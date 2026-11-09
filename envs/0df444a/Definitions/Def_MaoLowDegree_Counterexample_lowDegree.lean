-- Prove2me | Definitions.Def_MaoLowDegree_Counterexample_lowDegree
-- name    : MaoLowDegree_Counterexample_lowDegree
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:59:44.123895+00:00
-- url     : https://prove2.me/theorems/53fe2fb6-db1f-44e6-bcd1-e3d51807481d
-- title:
--   Real low-degree polynomial space, Fourier projection, and centered advantage
-- statement:
--   Let $P$ be any graph law on $\Omega_n$ and let $Q_n$ be uniform. The real degree-$d$ space is the span of the indicator monomials $\prod_{e\in S}x_e$ for $|S|\le d$, including the empty monomial. Write $\chi_S(x)=\prod_{e\in S}(-1)^{x_e}$. The likelihood ratio uses the referenced finite-space quotient, and the projection is its finite Fourier expansion:
--   $$\mathcal L^{\le d}(x)=\sum_{|S|\le d}\mathbb E_P[\chi_S(X)]\chi_S(x),\qquad \operatorname{Adv}_{\le d}(P,Q_n)=\|\mathcal L^{\le d}-1\|_{L^2(Q_n)}.$$
--
--   The norm uses the referenced squared $L^2$ sum. This specifies the full real polynomial space without a potentially unbounded real supremum; it is distinct from the binary polynomial space used in the construction. The degree-zero advantage and the advantage on an empty cube are zero. All logarithms are base two, and the goal threshold is $\lfloor c(\log_2 n)^{r-1}\rfloor$. The value at $n=0$ is only a total encoding convention, outside the limiting regime.
-- source:
--   Songtao Mao, STOC 2027 submission #509 (October 2026), equation (1), p.3; Theorem 1.2, p.5

import Definitions.Def_MaoLowDegree_Counterexample_graphModel
import Definitions.Def_PlantedSubgraphLD_l2NormSq

open Classical
noncomputable section
set_option autoImplicit false

namespace MaoLowDegree.Counterexample

/-- Real multilinear edge-indicator monomials, including the empty monomial. -/
def realMonomial {n : ℕ} (S : Finset (Edge n)) (x : Graph n) : ℝ :=
  ∏ e ∈ S, if x e then 1 else 0

def lowDegreeSpace (n d : ℕ) : Submodule ℝ (Graph n → ℝ) :=
  Submodule.span ℝ {f | ∃ S : Finset (Edge n), S.card ≤ d ∧ f = realMonomial S}

/-- The orthonormal Walsh characters for the full-support uniform null. -/
def character {n : ℕ} (S : Finset (Edge n)) (x : Graph n) : ℝ :=
  ∏ e ∈ S, if x e then -1 else 1

/-- dP/dQ is finite everywhere because Q is the full cube law. -/
def likelihoodRatio {n : ℕ} (P : GraphLaw n) (x : Graph n) : ℝ :=
  PlantedSubgraphLD.likelihoodRatio (fun y => (P y).toReal)
    (fun y => (nullLaw n y).toReal) x

/-- Finite Fourier formula for the real L²(Q) orthogonal projection onto degree ≤ d.
The Walsh span equals the real indicator-monomial span, with no F₂ reduction of coefficients. -/
def lowDegreeProjection {n : ℕ} (P : GraphLaw n) (d : ℕ) (x : Graph n) : ℝ :=
  ∑ S ∈ (Finset.univ : Finset (Edge n)).powerset.filter (fun S => S.card ≤ d),
    expect P (character S) * character S x

def l2Norm {n : ℕ} (f : Graph n → ℝ) : ℝ :=
  Real.sqrt (PlantedSubgraphLD.l2NormSq (fun y => (nullLaw n y).toReal) f)

/-- Centered low-degree advantage, defined by a finite norm rather than a real supremum. -/
def advantage {n : ℕ} (P : GraphLaw n) (d : ℕ) : ℝ :=
  l2Norm (fun x => lowDegreeProjection P d x - 1)

def log₂ (x : ℝ) : ℝ := Real.log x / Real.log 2

def degreeThreshold (r : ℕ) (c : ℝ) (n : ℕ) : ℕ :=
  ⌊c * (log₂ n) ^ (r - 1)⌋₊

end MaoLowDegree.Counterexample


