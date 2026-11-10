-- Prove2me | Definitions.Def_TightCoreset2027_Euclidean_generalPowers
-- name    : TightCoreset2027_Euclidean_generalPowers
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T06:07:49.240436+00:00
-- url     : https://prove2.me/theorems/78b6507c-7089-45f2-9c85-b702fb471721
-- title:
--   The calibrated query construction for every real power
-- statement:
--   For a real exponent $z\ge1$ and positive $n,L$, define the calibration predicate on a real displacement $\delta$ at level $\ell$ by
--
--   $$0<\delta\le\frac1{16L^2},\qquad (D_\ell+2\sqrt n\,\delta)^{z/2}-(D_\ell-2\sqrt n\,\delta)^{z/2}=\frac{n^{(z-1)/2}}{32L^2}.$$
--
--   The level displacement selects a solution of this equation when one exists and otherwise returns zero. In the paper's parameter regime the equation has a unique solution, a fact which a subsequent proof must establish. The selected displacement depends only on $z,n,L,\ell$, never on weights, direction or signs. Let
--
--   $$B_z=\lceil n^{z/2}\rceil.$$
--
--   The general-power dataset uses $B_z$ separated copies of the same local points. Its query uses the preceding center formula with the calibrated displacement and $n(B_z-1)+m(L+1)$ unpadded centers. This records the precise general-power objects needed to prove the goal, without introducing another milestone or assuming the calibration's existence.
--
--   **Formalization Note** The fallback is explicitly exposed for inputs outside the proved regime. It does not turn existence into a theorem hypothesis. The theorem of the mission quantifies over every real $z\ge1$ independently of this selector, so proving only the squared-distance construction cannot close it.
-- source:
--   Junqiu Hu, Lingxiao Huang, Jian Li, Baoduo Xu, STOC 2027 submission #879 (October 2026), §2.5, Eq. (17)–(19), printed pp. 19–21 / PDF pp. 21–23; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/879.pdf

import Definitions.Def_TightCoreset2027_Euclidean_queryConstruction
set_option autoImplicit false

namespace TightCoreset2027.Euclidean

/-- Equation (17), including the source's displacement interval. -/
def CalibratesPower (z : ℝ) (n L : ℕ) (ℓ : Fin (L + 1)) (δ : ℝ) : Prop :=
  0 < δ ∧ δ ≤ 1 / (16 * (L : ℝ) ^ 2) ∧
    Real.rpow (baseline n L ℓ + 2 * Real.sqrt (n : ℝ) * δ) (z / 2) -
      Real.rpow (baseline n L ℓ - 2 * Real.sqrt (n : ℝ) * δ) (z / 2) =
        Real.rpow (n : ℝ) ((z - 1) / 2) / (32 * (L : ℝ) ^ 2)

/-- The root in (17), selected only from the source data, with a total fallback 0.
Existence and uniqueness in the source regime remain proof obligations, not assumptions. -/
noncomputable def displacementZ (z : ℝ) (n L : ℕ) (ℓ : Fin (L + 1)) : ℝ := by
  classical
  exact if h : ∃ δ : ℝ, CalibratesPower z n L ℓ δ then Classical.choose h else 0

noncomputable def copyCountZ (z : ℝ) (n : ℕ) : ℕ :=
  ⌈Real.rpow (n : ℝ) (z / 2)⌉₊

noncomputable def datasetZ (z : ℝ) (n m : ℕ) {L q : ℕ}
    (G : ProjectionFamily L q) : Finset (ConstructionSpace n m L) :=
  dataset (copyCountZ z n) n m G

noncomputable def queryCentersZ (z : ℝ) (n m L k : ℕ)
    (b : Fin (copyCountZ z n)) (v : ProjectionSpace L) (σ : SignArray n m) :
    Finset (ConstructionSpace n m L) :=
  queryCenters (copyCountZ z n) n m L k b (displacementZ z n L) v σ

end TightCoreset2027.Euclidean


