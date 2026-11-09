-- Prove2me | Definitions.Def_RandomCNFDeficiency_LowerBound_RandomModel
-- name    : RandomCNFDeficiency_LowerBound_RandomModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:33:24.025278+00:00
-- url     : https://prove2.me/theorems/ecc6ed71-6687-4a5b-978e-17f4711de537
-- title:
--   The iid signed-clause law and logarithmic-width regime
-- statement:
--   Sample exactly $M=n2^k$ clauses independently and uniformly with replacement. The published proper-clause tuple type chooses each $k$-support and its $k$ signs uniformly. For any deterministic CNF predicate $E$, its probability is the fraction of ordered tuples whose clause image satisfies $E$.
--
--   $$s(n,k)=\frac n{\sqrt k},\qquad d(n,k)=\frac n2-\frac{4n}{\sqrt k},$$
--
--   $$\varepsilon(n,k)=e^{-(1-\ln2)n}+\frac{e^{-k^2}}{1-e^{-k}}+ne^{-(3/2-\ln2)n}.$$
--
--   An allowed sequence $k(n)$ tends to infinity and eventually obeys $1\le k(n)\le n$ and $k(n)\le C\log_2 n$ for some fixed $C>0$. The first two bounds are eventual consequences of the source regime, and exclude no allowed sequence. Define the criterion event as unsatisfiability together with the entire deterministic criterion at $s(n,k),d(n,k)$, and the hard event as unsatisfiability together with the strict degree lower bound simultaneously over all fields.
--
--   Finite exceptional parameters use total real arithmetic and a counting fraction of zero for an empty sample type. All probability conclusions concern the eventually valid domain. The common law is uniform on tuples, never uniform on the distinct clause sets obtained afterward.
-- source:
--   Jonas Conneryd, STOC 2027 submission #332 (October 2026), Section 3.3, Equations (21) and (32), printed p. 12, PDF p. 14; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/332.pdf; printed p. 14, PDF p. 16

import Definitions.Def_RandomCNFDeficiency_LowerBound_PolynomialCalculus
import Definitions.Def_RandomCNFDeficiency_LowerBound_DeficiencyClosure
set_option autoImplicit false
universe uRandom

namespace RandomCNFDeficiency.LowerBound

/-- Reuse the published exact-width clause product, with replacement. -/
abbrev Sample (n k : ℕ) := OAI.FixedClauseThreshold.Formula n k (n * 2 ^ k)

noncomputable def sampledCNF {n k : ℕ} (ω : Sample n k) : CNF n := by
  classical
  exact Finset.univ.image fun j => (ω j).val

/-- Uniform product mass on ordered tuples, NOT uniform on clause sets. -/
noncomputable def sampleProbability (n k : ℕ) (P : CNF n → Prop) : ℝ := by
  classical
  exact (Fintype.card {ω : Sample n k // P (sampledCNF ω)} : ℝ) /
    (Fintype.card (Sample n k) : ℝ)

noncomputable def smallThreshold (n k : ℕ) : ℝ := (n : ℝ) / Real.sqrt (k : ℝ)

noncomputable def degreeThreshold (n k : ℕ) : ℝ := (n : ℝ) / 2 - 4 * (n : ℝ) / Real.sqrt (k : ℝ)

/-- Equation (32), including the exponent -k². -/
noncomputable def failureBound (n k : ℕ) : ℝ :=
  Real.exp (-(1 - Real.log 2) * (n : ℝ)) +
    Real.exp (-((k : ℝ) ^ 2)) / (1 - Real.exp (-(k : ℝ))) +
    (n : ℝ) * Real.exp (-(3 / 2 - Real.log 2) * (n : ℝ))

/-- No prescribed growth speed: divergence plus ANY fixed logarithmic upper constant. -/
def LogarithmicRegime (k : ℕ → ℕ) : Prop :=
  Filter.Tendsto k Filter.atTop Filter.atTop ∧
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in Filter.atTop,
      1 ≤ k n ∧ k n ≤ n ∧ (k n : ℝ) ≤ C * (Real.log (n : ℝ) / Real.log 2)

def CriterionEvent (n k : ℕ) (F : CNF n) : Prop :=
  ¬ Satisfiable F ∧ Criterion F (smallThreshold n k) (degreeThreshold n k)

def HardEvent (n k : ℕ) (F : CNF n) : Prop :=
  ¬ Satisfiable F ∧ AllFieldsHard.{uRandom} F (degreeThreshold n k)

end RandomCNFDeficiency.LowerBound


