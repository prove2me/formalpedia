-- Prove2me | Definitions.Def_GaussPart_Supplement_TestableWellBehaved
-- name    : GaussPart_Supplement_TestableWellBehaved
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:05:20.279591+00:00
-- url     : https://prove2.me/theorems/65a05c01-2ffc-49ef-bee0-12fa2993d4c1
-- title:
--   $(\ell,K,A,\Lambda)$-testable well-behaved MIM classes (sandwiching on thin cells)
-- statement:
--   Let $\ell:(0,1]\to\mathbb Z_+$ be non-increasing, $K\in\mathbb Z_+$, $A>0$, $\Lambda\ge1$. A class $\mathcal F$ of Boolean $K$-MIMs on $\mathbb R^d$ is **$(\ell,K,A,\Lambda)$-testable well-behaved** if
--
--   1. it is closed under affine restrictions;
--   2. (**sandwiching on thin cells**) for every $f\in\mathcal F$, $\delta,\tau\in(0,1)$, every finite polyhedral partition $\mathcal P$ of $\mathbb R^d$ and every $\mathcal G\subseteq\mathcal P$ with $\operatorname{diam}(R)\le\delta$ for $R\in\mathcal G$, there are polynomials $p_R^-,p_R^+:V_R^\perp\to\mathbb R$, one pair per $R\in\mathcal G$, of degree at most $\ell(\tau)$, both depending on a common subspace of dimension at most $K$, with $p_R^-(x)\le f(x+y)\le p_R^+(x)$ for $x\in V_R^\perp$, $y\in\mathrm{proj}_{V_R}(R)$, and
--   $$
--   \sum_{R\in\mathcal G}Q(R)\,\mathbb E_{x\sim\mathcal N(0,I_{V_R^\perp})}[p_R^+(x)-p_R^-(x)]\le A\Lambda\delta+\tau
--   $$
--   for every probability $Q$ with $Q(R)\le\Lambda\Pr_{\mathcal N(0,I_d)}[R]$ for all $R\in\mathcal G$.
--
--   Here $V_R$ is the span of the normals of the constraints of $R$ and diameters are measured in $V_R$, as in the published Theorem 3.1. The class is the hypothesis of the testable learners (Theorems F.2, F.3).
--
--   **Formalization Note** A polynomial on $V_R^\perp$ is a polynomial on $\mathbb R^d$ read on $V_R^\perp$; the common subspace is chosen per cell (the page attaches it to the pair); $\mathcal N(0,I_{V_R^\perp})$ is the image of $\mathcal N(0,I_d)$ under the projection onto $V_R^\perp$; members of $\mathcal F$ are Borel measurable.
-- source:
--   Diakonikolas, Iakovidis, Kane, Ma, Gaussian Partitioning for Reliable Learning of Multi-Index Models, arXiv:2611.05264 (sha256 7e0ca6d4…), Definition F.1, p.79 (PDF p.81)

import Mathlib
import Definitions.Def_GaussPart_Cell
import Definitions.Def_GaussPart_IsGoodOutput
import Definitions.Def_GaussPart_Supplement_BoolFn
import Definitions.Def_GaussPart_Supplement_WellBehaved

open MeasureTheory ProbabilityTheory

namespace GaussPart

namespace Supplement

/-- **Sandwiching on thin cells** (Definition F.1 item 2, arXiv:2611.05264, sha256 7e0ca6d4…,
p.79, PDF p.81): for `f ∈ F`, `δ, τ ∈ (0, 1)`, every finite polyhedral partition `P` of `ℝᵈ` and
every `G ⊆ P` with `diam(R) ≤ δ` for `R ∈ G`, there are polynomials `p_R^−, p_R^+ : V_R^⊥ → ℝ`, one
pair for each `R ∈ G`, of degree at most `ℓ(τ)`, both depending on a common subspace of dimension at
most `K`, with `p_R^−(x) ≤ f(x + y) ≤ p_R^+(x)` for `x ∈ V_R^⊥`, `y ∈ proj_{V_R}(R)`, and
`Σ_{R∈G} Q(R) E_{x∼N(0, I_{V_R^⊥})}[p_R^+(x) − p_R^−(x)] ≤ AΛδ + τ` for every probability `Q` with
`Q(R) ≤ Λ · Pr_{x∼N(0,I_d)}[x ∈ R]` for all `R ∈ G`.

**Formalization Note.**
* The partition with `G` is a list of cells with flags (`true` means `R ∈ G`), a partition in the
  sense of the published `IsPartition`; diameters are the published `DiamLE` (measured in `V_R`,
  the published `constraintSpace`).
* A polynomial on `V_R^⊥` is a polynomial on `ℝᵈ` (`MvPolynomial (Fin d) ℝ`, total degree) read on
  `V_R^⊥`; "depending on a subspace `S`" is `p(x) = p(proj_S x)` for `x ∈ V_R^⊥`, with
  `S ⊆ V_R^⊥` and `dim S ≤ K`. The page attaches the common subspace to the pair; one `S` per
  cell is the reading taken.
* `N(0, I_{V_R^⊥})` is the image of `N(0, I_d)` under the orthogonal projection onto `V_R^⊥`.
* The polynomials are chosen before `Q`, as on the page. -/
def HasThinCellSandwiching {d : ℕ} (ℓ : ℝ → ℕ) (K : ℕ) (A Λ : ℝ) (F : Set (Vec d → ℝ)) :
    Prop :=
  ∀ f ∈ F, ∀ δ τ : ℝ, 0 < δ → δ < 1 → 0 < τ → τ < 1 →
  ∀ L : List (Cell d × Bool), IsPartition (L.map Prod.fst) →
    (∀ R : Cell d, (R, true) ∈ L → DiamLE R δ) →
    ∃ pm pp : Cell d → MvPolynomial (Fin d) ℝ,
      (∀ R : Cell d, (R, true) ∈ L →
        (pm R).totalDegree ≤ ℓ τ ∧ (pp R).totalDegree ≤ ℓ τ ∧
        (∃ S : Submodule ℝ (Vec d), S ≤ (constraintSpace R)ᗮ ∧ Module.finrank ℝ S ≤ K ∧
          ∀ x ∈ (constraintSpace R)ᗮ, evalPoly (pm R) x = evalPoly (pm R) (S.starProjection x) ∧
            evalPoly (pp R) x = evalPoly (pp R) (S.starProjection x)) ∧
        ∀ x ∈ (constraintSpace R)ᗮ, ∀ z ∈ cellSet R,
          evalPoly (pm R) x ≤ f (x + (constraintSpace R).starProjection z) ∧
            f (x + (constraintSpace R).starProjection z) ≤ evalPoly (pp R) x) ∧
      ∀ Q : Measure (Vec d), IsProbabilityMeasure Q →
        (∀ R : Cell d, (R, true) ∈ L →
          Q (cellSet R) ≤ ENNReal.ofReal Λ * stdGaussian (Vec d) (cellSet R)) →
        ((L.filter (fun e => e.2)).map (fun e =>
          (Q (cellSet e.1)).toReal *
            ∫ x, (evalPoly (pp e.1) x - evalPoly (pm e.1) x)
              ∂((stdGaussian (Vec d)).map (constraintSpace e.1)ᗮ.starProjection))).sum ≤
          A * Λ * δ + τ

/-- **Definition F.1** (testable well-behaved MIMs), p.79 (PDF p.81): `ℓ : (0, 1] → ℤ₊`
non-increasing, `K ∈ ℤ₊`, `A > 0`, `Λ ≥ 1`; `F` is a class of Boolean `K`-MIMs on `ℝᵈ` that is
(1) closed under affine restrictions and (2) has sandwiching on thin cells
(`HasThinCellSandwiching`).

**Formalization Note.** Members of `F` are Borel measurable (`IsBoolFn`), the paper's convention
for Boolean functions (Definition A.1). -/
def IsTestableWellBehaved {d : ℕ} (ℓ : ℝ → ℕ) (K : ℕ) (A Λ : ℝ) (F : Set (Vec d → ℝ)) : Prop :=
  IsDegreeFn ℓ ∧ 1 ≤ K ∧ 0 < A ∧ 1 ≤ Λ ∧ (∀ f ∈ F, IsBoolFn f ∧ IsKMIM K f) ∧
    ClosedUnderAffineRestr F ∧ HasThinCellSandwiching ℓ K A Λ F

end Supplement

end GaussPart


