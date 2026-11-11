-- Prove2me | Definitions.Def_MixedVolFPRAS_Main_MuMeasure
-- name    : MixedVolFPRAS_Main_MuMeasure
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T20:30:59.516446+00:00
-- url     : https://prove2.me/theorems/fe1c6cef-250b-4d55-b9a3-d7732dae1ed3
-- title:
--   The measure µ of Eq. (4) on Sⁿ⁻¹
-- statement:
--   Let $n\ge3$ and let $K_1,\dots,K_{n-3}\subseteq\mathbb{R}^n$ be smooth convex bodies with $D^2h_{K_i}\succ0$ on $S^{n-1}$. The measure $\mu$ on $S^{n-1}$ is defined by its density with respect to $\omega$ (Eq. (4)):
--
--   $$\frac{d\mu}{d\omega}(\theta)=\frac{1}{n}\cdot\frac{D_{n-1}\big(I,I,D^2h_{K_1}(\theta),\dots,D^2h_{K_{n-3}}(\theta)\big)}{V_n\big(B_2^n,B_2^n,B_2^n,K_1,\dots,K_{n-3}\big)} .$$
--
--   It is nonnegative, and by Proposition 2.9 it integrates to $1$, so $\mu$ is a probability measure.
--
--   **Formalization Note.** `muDensity K θ` with `K : Fin (n - 3) → Set (E n)` is the right-hand side (the first two matrices are the identity, the others `restrictedHessian (supportFunction (K i)) θ`; the mixed volume has $B_2^n$ in its first three slots). `muMeasure K` is `surfaceMeasure n` with density `ENNReal.ofReal (muDensity K θ)` (for the bodies of §3.1 the density is nonnegative, so this is the paper's $\mu$).
-- source:
--   Chen, Liu, An FPRAS for Mixed Volumes, STOC 2027 submission (manuscript sha256 0acf8d97…), p. 13, Eq. (4)

import Mathlib
import Definitions.Def_MixedVolFPRAS_Main_MixedVolume
import Definitions.Def_MixedVolFPRAS_Main_MixedDiscriminant
import Definitions.Def_MixedVolFPRAS_Main_Sphere

noncomputable section

namespace MixedVolFPRAS.Main

/-!
# The measure `µ` of Eq. (4)

Chen, Liu, *An FPRAS for Mixed Volumes*, p. 13, Eq. (4). For convex bodies `K₁, …, K_{n−3}` in
`ℝⁿ` (`n ≥ 3`), `µ` has density with respect to `ω`

`dµ/dω (θ) = (1/n) · D_{n−1}(I, I, D²h_{K₁}(θ), …, D²h_{K_{n−3}}(θ)) / Vₙ(B₂ⁿ, B₂ⁿ, B₂ⁿ, K₁, …, K_{n−3})`.

`muDensity K θ` is this density; `muMeasure K` is `ω` with this density (a negative value of the
density would be read as `0`; for the bodies of §3.1 it is nonnegative).
-/

/-- The density `dµ/dω` of Eq. (4); `K` lists `K₁, …, K_{n−3}`. -/
def muDensity {n : ℕ} (K : Fin (n - 3) → Set (E n)) (θ : E n) : ℝ :=
  (1 / (n : ℝ)) *
    mixedDiscriminant (fun j : Fin (n - 1) =>
      if h : j.val < 2 then (1 : Matrix (Fin (n - 1)) (Fin (n - 1)) ℝ)
      else restrictedHessian (supportFunction (K ⟨j.val - 2, by have := j.isLt; omega⟩)) θ) /
    mixedVolume (fun i : Fin n =>
      if h : i.val < 3 then unitBall n else K ⟨i.val - 3, by have := i.isLt; omega⟩)

/-- The measure `µ` of Eq. (4) on `Sⁿ⁻¹`. -/
def muMeasure {n : ℕ} (K : Fin (n - 3) → Set (E n)) : MeasureTheory.Measure (Sph n) :=
  (surfaceMeasure n).withDensity (fun θ => ENNReal.ofReal (muDensity K (θ : E n)))

end MixedVolFPRAS.Main


