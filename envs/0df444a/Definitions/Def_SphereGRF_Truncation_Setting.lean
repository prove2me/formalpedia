-- Prove2me | Definitions.Def_SphereGRF_Truncation_Setting
-- name    : SphereGRF_Truncation_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T04:35:45.235727+00:00
-- url     : https://prove2.me/theorems/523a0ee3-f580-4bf0-992b-b3cb5480eadc
-- title:
--   §§2, 5 — spherical harmonics, Gaussian KL series, truncations, and mixed norms
-- statement:
--   Let $S^2$ be the unit sphere in $\mathbb R^3$, equipped with its surface area measure $\sigma$ of total mass $4\pi$. Rodrigues' formula defines the Legendre polynomial $P_\ell$. The normalized complex spherical harmonics $Y_{\ell m}$ use the associated Legendre functions for $-\ell\le m\le\ell$. Their real and imaginary parts supply the real factors in the Karhunen–Loève expansion.
--
--   For a nonnegative angular power spectrum $(A_\ell)_{\ell\ge0}$ and independent standard normal coefficients $(X^1_{\ell m},X^2_{\ell m})$, the truncation $T^\kappa$ sums all degrees $0\le\ell\le\kappa$:
--
--   $$
--   T^\kappa(y)=\sum_{\ell=0}^{\kappa}\left(\sqrt{A_\ell}X^1_{\ell0}L_{\ell0}(\vartheta)+\sqrt{2A_\ell}\sum_{m=1}^{\ell}L_{\ell m}(\vartheta)(X^1_{\ell m}\cos(m\varphi)+X^2_{\ell m}\sin(m\varphi))\right).
--   $$
--
--   The field $T$ is the limit of these partial sums. The definitions also provide the squared spatial $L^2$ norm and the mixed $L^p(\Omega;L^2(S^2))$ norm used by the error results.
--
--   **Formalization Note** Coordinates $0,1,2$ correspond to the paper's $y_1,y_2,y_3$. The harmonic factors use the Cartesian identity $(y_1+i y_2)^m=\sin^m\vartheta\,e^{im\varphi}$, including at the poles. Surface measure is Mathlib's `volume.toSphere`. The field uses the limit of the ordered partial sums; its arbitrary value where that limit does not exist is ignored by the almost-sure claims. Extended nonnegative integrals keep nonintegrable inputs from silently acquiring zero norm. Only coefficients with $m\le\ell$ that enter the series are required to be independent standard normals; the unused $X^2_{\ell0}$ coordinates are zero as in Lemma 5.1.
-- source:
--   Lang, Schwab, Isotropic Gaussian random fields on the sphere, arXiv:1305.1170v3, §2 pp. 4–5; Lemma 5.1 pp. 23–24; §5 p. 25

import Mathlib
import Definitions.Def_SphereGRF_Holder_Setting
import Definitions.Def_SphereGRF_Spectral_Legendre

open MeasureTheory Filter

namespace SphereGRF.Truncation

noncomputable def sigma : MeasureTheory.Measure SphereGRF.Holder.S2 :=
  (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).toSphere

noncomputable def shNorm (ℓ m : ℕ) : ℝ :=
  Real.sqrt (((2 * ℓ + 1 : ℕ) : ℝ) / (4 * Real.pi) *
    ((ℓ - m).factorial : ℝ) / ((ℓ + m).factorial : ℝ))

private def y₀ (y : SphereGRF.Holder.S2) : ℝ := (y : EuclideanSpace ℝ (Fin 3)) 0
private def y₁ (y : SphereGRF.Holder.S2) : ℝ := (y : EuclideanSpace ℝ (Fin 3)) 1
private def y₂ (y : SphereGRF.Holder.S2) : ℝ := (y : EuclideanSpace ℝ (Fin 3)) 2

noncomputable def sphY (ℓ : ℕ) (m : ℤ) (y : SphereGRF.Holder.S2) : ℂ :=
  if 0 ≤ m ∧ m ≤ (ℓ : ℤ) then
    (shNorm ℓ m.toNat * (-1 : ℝ) ^ m.toNat *
      ((Polynomial.derivative^[m.toNat]) (SphereGRF.Spectral.legendreP ℓ)).eval (y₂ y) : ℝ) *
      ((y₀ y : ℂ) + Complex.I * (y₁ y : ℂ)) ^ m.toNat
  else if -(ℓ : ℤ) ≤ m ∧ m < 0 then
    ((-1 : ℤ) ^ m.natAbs : ℤ) *
      (star ((shNorm ℓ (-m).toNat * (-1 : ℝ) ^ (-m).toNat *
        ((Polynomial.derivative^[(-m).toNat]) (SphereGRF.Spectral.legendreP ℓ)).eval (y₂ y) : ℝ) *
        ((y₀ y : ℂ) + Complex.I * (y₁ y : ℂ)) ^ (-m).toNat))
  else 0

noncomputable def shC (ℓ m : ℕ) (y : SphereGRF.Holder.S2) : ℝ :=
  shNorm ℓ m * (-1 : ℝ) ^ m *
    ((Polynomial.derivative^[m]) (SphereGRF.Spectral.legendreP ℓ)).eval (y₂ y) *
    (((y₀ y : ℂ) + Complex.I * (y₁ y : ℂ)) ^ m).re

noncomputable def shS (ℓ m : ℕ) (y : SphereGRF.Holder.S2) : ℝ :=
  shNorm ℓ m * (-1 : ℝ) ^ m *
    ((Polynomial.derivative^[m]) (SphereGRF.Spectral.legendreP ℓ)).eval (y₂ y) *
    (((y₀ y : ℂ) + Complex.I * (y₁ y : ℂ)) ^ m).im

abbrev KLIndex :=
  {q : ℕ × ℕ × Fin 2 // q.2.1 ≤ q.1 ∧ (q.2.1 ≠ 0 ∨ q.2.2 = 0)}

def IsKLInput {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → ℕ → Fin 2 → Ω → ℝ) : Prop :=
  (∀ q : KLIndex, Measurable (X q.val.1 q.val.2.1 q.val.2.2)) ∧
  (∀ q : KLIndex, P.map (X q.val.1 q.val.2.1 q.val.2.2) =
    ProbabilityTheory.gaussianReal 0 1) ∧
  ProbabilityTheory.iIndepFun
    (fun q : KLIndex => X q.val.1 q.val.2.1 q.val.2.2) P ∧
  (∀ ℓ ω, X ℓ 0 1 ω = 0)

noncomputable def klTrunc {Ω : Type*} (A : ℕ → ℝ)
    (X : ℕ → ℕ → Fin 2 → Ω → ℝ) (κ : ℕ) (ω : Ω) (y : SphereGRF.Holder.S2) : ℝ :=
  ∑ ℓ ∈ Finset.range (κ + 1),
    (Real.sqrt (A ℓ) * X ℓ 0 0 ω * shC ℓ 0 y +
      Real.sqrt (2 * A ℓ) *
        ∑ m ∈ Finset.Icc 1 ℓ,
          (shC ℓ m y * X ℓ m 0 ω + shS ℓ m y * X ℓ m 1 ω))

noncomputable def klField {Ω : Type*} (A : ℕ → ℝ)
    (X : ℕ → ℕ → Fin 2 → Ω → ℝ) (ω : Ω) (y : SphereGRF.Holder.S2) : ℝ :=
  Filter.limUnder Filter.atTop (fun κ => klTrunc A X κ ω y)

noncomputable def l2S2Sq (f : SphereGRF.Holder.S2 → ℝ) : ENNReal :=
  ∫⁻ y, ‖f y‖ₑ ^ (2 : ℕ) ∂sigma

noncomputable def lpL2Norm {Ω : Type*} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) (p : ℝ) (Z : Ω → SphereGRF.Holder.S2 → ℝ) : ENNReal :=
  (∫⁻ ω, l2S2Sq (Z ω) ^ (p / 2) ∂P) ^ (1 / p)

end SphereGRF.Truncation


