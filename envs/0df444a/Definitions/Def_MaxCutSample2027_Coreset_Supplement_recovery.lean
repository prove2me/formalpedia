-- Prove2me | Definitions.Def_MaxCutSample2027_Coreset_Supplement_recovery
-- name    : MaxCutSample2027_Coreset_Supplement_recovery
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T09:57:58.965193+00:00
-- url     : https://prove2.me/theorems/6482eb34-1e64-49fe-938f-571b8730c2c6
-- title:
--   Recovery objective, admissible LP choices, rounding and queried entries
-- statement:
--   Let $A$ be a symmetric nonnegative zero-diagonal matrix, $p$ a positive probability vector, $k\ge1$, and $x\in V^k$. Use the base kernel $K_{uv}=A_{uv}/(n^2p_up_v)$. For a sample cut $S\subseteq[k]$, define $a_v=|\{i\in S:x_i=v\}|/k$. For $b\in Z(p)=\{b:0\le b\le p\}$ define
--   $$e_x(a,b)=\frac1k\sum_i|(Ka)_{x_i}-(Kb)_{x_i}|.$$
--   An admissible recovery pair consists of an optimal cut $S$ of the actual sampled graph $\widehat A$ and a minimizer $b$ of this objective over $Z(p)$. This is exactly the set of $b$ components of optimal LP solutions in (3.6), after eliminating the slack variables.
--   Rounding includes each vertex independently with probability $b_v/p_v$; the weight of $U\subseteq V$ is the product of the inclusion and exclusion probabilities. The rounded loss is its weighted average of $(\operatorname{MaxCut}(A)-\operatorname{Cut}_A(U))/n^2$. The queried entries are $Q_x=\{(x_i,v):i\in[k],v\in V\}$.
--   This interface retains every optimal choice and both sources of randomness in cut recovery.
-- source:
--   Itamar Bender, Robert Krauthgamer, STOC 2027 submission #147 (October 2026), §3.1–§3.2, eqs. (3.4), (3.6), (3.7), p. 18–19. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/147.pdf (PDF SHA-256 54bb82836bdc80e7729d444c36f7299cb7d50838d4ee557decb3495e61236fa7; printed page = PDF page).

import Definitions.Def_MaxCutSample2027_Coreset_fractional
import Definitions.Def_MaxCutSample2027_Coreset_Supplement_sampling
open scoped BigOperators
noncomputable section

namespace MaxCutSample2027.Coreset.Supplement

def matVec {V : Type*} [Fintype V] (L : V → V → ℝ) (c : V → ℝ) (u : V) : ℝ :=
  ∑ v, L u v * c v

/-- The objective (3.4), equivalent to optimizing LP (3.6) after eliminating t. -/
def recoveryError {V : Type*} [Fintype V] {k : ℕ} (L : V → V → ℝ)
    (x : Fin k → V) (a b : V → ℝ) : ℝ :=
  (∑ i, |matVec L a (x i) - matVec L b (x i)|) / (k : ℝ)

/-- Step 1: the mass on the chosen side of the sample cut. -/
def inducedFraction {V : Type*} [DecidableEq V] {k : ℕ}
    (x : Fin k → V) (S : Finset (Fin k)) (v : V) : ℝ :=
  ((S.filter (fun i => x i = v)).card : ℝ) / (k : ℝ)

/-- Every admissible choice of optimal sample cut and optimal LP b. -/
def AdmissibleRecovery {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
    (A : V → V → ℝ) (p : V → ℝ) (x : Fin k → V)
    (S : Finset (Fin k)) (b : V → ℝ) : Prop :=
  cutValue (Ahat A p x) S = maxCut (Ahat A p x) ∧ b ∈ Z p ∧
    ∀ c ∈ Z p, recoveryError (K A p) x (inducedFraction x S) b ≤
      recoveryError (K A p) x (inducedFraction x S) c

/-- Independent rounding includes vertex v with probability b_v/p_v. -/
def roundingWeight {V : Type*} [Fintype V] [DecidableEq V]
    (p b : V → ℝ) (S : Finset V) : ℝ :=
  (∏ v ∈ S, b v / p v) * (∏ v ∈ Sᶜ, (1 - b v / p v))

def roundedLoss {V : Type*} [Fintype V] [DecidableEq V]
    (A : V → V → ℝ) (p b : V → ℝ) : ℝ :=
  ∑ S : Finset V, roundingWeight p b S *
    ((maxCut A - cutValue A S) / (Fintype.card V : ℝ) ^ 2)

/-- All ordered adjacency entries requested by the recovery algorithm. -/
def queryEntries {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
    (x : Fin k → V) : Finset (V × V) :=
  Finset.univ.biUnion (fun i => Finset.univ.image (fun v => (x i, v)))

end MaxCutSample2027.Coreset.Supplement


