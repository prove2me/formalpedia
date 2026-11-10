-- Prove2me | Definitions.Def_KnownFidelity_Rank_wishartLaw
-- name    : KnownFidelity_Rank_wishartLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:48:33.817034+00:00
-- url     : https://prove2.me/theorems/ab8eaa15-865c-490e-9ad4-25dc81e64c86
-- title:
--   The law $Q_b$ of $G_b=UD_b^{1/2}ZD_b^{1/2}V^*$, Eq. (40)
-- statement:
--   Let $a\in\mathbb R^r_{\ge0}$, $D=\mathrm{diag}(a_1,\dots,a_r)$, let $Z$ be an $r\times r$ standard complex Ginibre matrix (independent entries with density $\pi^{-1}e^{-|z|^2}$), and let $U,V$ be independent Haar unitaries on $U(r)$, independent of $Z$. The law of
--
--   $$G=U\,D^{1/2}\,Z\,D^{1/2}\,V^*$$
--
--   is $Q(a)$; with $a=a^{(b)}$ it is $Q_b$.
--
--   **Formalization Note** Haar measure is the platform's `QAlgorithms.Schur.unitaryHaar` and the Ginibre matrix has law `ginibreLaw r` (entries with the platform's `BraneBrauer.Orthogonal.complexGaussian`); the law is the push-forward of the product measure under a continuous (hence measurable) map.
-- source:
--   Lee, Jo, Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank, arXiv:2608.01770, §5.4, Eq. (40), p. 17 (PDF p. 19)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_SchurUnitaryEnsembles
import Definitions.Def_KnownFidelity_Rank_ginibreLaw
import Definitions.Def_KnownFidelity_Rank_instMeasurableSpaceMatrix

open MeasureTheory
open scoped Matrix

namespace KnownFidelity.Rank

/-- **The doubly correlated Wishart factor law `Q_b`, Eq. (40).**
Lee, Jo, *Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank*,
arXiv:2608.01770, §5.4, Eq. (40), printed p. 17 (PDF p. 19): "Let Z be an r × r standard complex
Ginibre matrix: its entries are independent complex Gaussians with density π^{−1}e^{−|z|²}. Let
U, V be independent Haar unitaries, independent of Z, and define G_b = U D_b^{1/2} Z D_b^{1/2} V*,
R_b = ∥G_b∥²_F. (40) Let Q_b denote the law of G_b." Here D_b = diag(a^{(b)}_1, …, a^{(b)}_r).

`wishartLaw a` is the law of `G = U D^{1/2} Z D^{1/2} V*` with `D = diag(a)`, `U, V` independent
Haar unitaries on `U(r)` and `Z` an independent standard complex Ginibre matrix.

**Formalization Note.** Haar measure is the platform's `QAlgorithms.Schur.unitaryHaar r`
(normalized on the compact group `U(r)`, Borel σ-algebra). The Ginibre matrix `Z` has
law `ginibreLaw r`: independent entries whose real and imaginary parts are independent
`N(0, 1/2)` (density `π^{−1}e^{−|z|²}`).
`D^{1/2} = diag(√a_i)` (real square roots; the statements assume `a ≥ 0`). The law is the
push-forward of the product measure under the continuous map `(U, V, z) ↦ G`. -/
noncomputable def wishartLaw {r : ℕ} (a : Fin r → ℝ) : Measure (Matrix (Fin r) (Fin r) ℂ) :=
  let Dh : Matrix (Fin r) (Fin r) ℂ := Matrix.diagonal fun i => ((Real.sqrt (a i) : ℝ) : ℂ)
  Measure.map
    (fun w : (Matrix.unitaryGroup (Fin r) ℂ × Matrix.unitaryGroup (Fin r) ℂ) ×
        Matrix (Fin r) (Fin r) ℂ =>
      (w.1.1 : Matrix (Fin r) (Fin r) ℂ) * Dh * w.2 * Dh *
        (w.1.2 : Matrix (Fin r) (Fin r) ℂ)ᴴ)
    (((QAlgorithms.Schur.unitaryHaar r).prod (QAlgorithms.Schur.unitaryHaar r)).prod
      (ginibreLaw r))

end KnownFidelity.Rank


