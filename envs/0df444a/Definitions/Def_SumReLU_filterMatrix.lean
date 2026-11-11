-- Prove2me | Definitions.Def_SumReLU_filterMatrix
-- name    : SumReLU_filterMatrix
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T08:26:22.588601+00:00
-- url     : https://prove2.me/theorems/0b46fa24-07e5-4969-a2dd-a816911a32bf
-- title:
--   The moment tensor $\mathbb E[y\,\mathrm{He}_m(x)]$, the filter $u^{\otimes p}\otimes\bar u^{\otimes p}$ and the filtered matrix $M_{2p+2}(u)$
-- statement:
--   Let $\mathrm{He}_m(x)$ be the normalized order-$m$ Hermite tensor (Definition 2.5). For the target $f$, the Hermite moment tensor is $\mathbb E_{x\sim N(0,I_d)}[f(x)\,\mathrm{He}_m(x)]$. For $u\in\mathbb C^d$ and $p\in\mathbb N$, the filter is the order-$2p$ tensor $u^{\otimes p}\otimes\bar u^{\otimes p}$, and the partial contraction of an order-$(2p+2)$ tensor $W$ with an order-$2p$ tensor $T$ over the first $2p$ indices is the $d\times d$ array $(\langle W,T\rangle)_{ab}=\sum_{i_1,\dots,i_{2p}}\overline{W_{i_1\dots i_{2p}ab}}\,T_{i_1\dots i_{2p}}$. For $Z>0$ the filtered matrix is
--   $$
--   M_{2p+2}(u)=\frac1Z\sum_{i=1}^k\beta_i\,|w_i\cdot u|^{2p}\,w_iw_i^\top ,
--   $$
--   form (ii) of (M); $Z=Z_p(\mathcal U)$ is the normalizing parameter of the paper.
--
--   The top eigenvector of this matrix is the paper's estimate of a hidden weight vector.
--
--   **Formalization Note** $\mathrm{He}_m$ is the published `GaussPart.hermiteTensor`, whose entry at index $(i_1,\dots,i_m)$ is $(m!)^{-1/2}\prod_r\mathrm{He}_{\beta_r}(x_r)$ with $\beta_r$ the multiplicity of $r$; this equals (6), because the sum over partitions into singletons and pairs factors over coordinates.
-- source:
--   Diakonikolas, Diakonikolas, Wang, Zarifis, Learning Positive Linear Combinations of ReLUs in Fully Polynomial Time, arXiv:2610.32940 (PDF sha256 66803576…6c48), Eq. (M), p.24 (PDF p.26); Definition 2.5, (6), p.11 (PDF p.13); §2, p.10 (PDF p.12)

import Mathlib
import Definitions.Def_GaussPart_hermiteTensor
import Definitions.Def_SumReLU_reluSum
import Definitions.Def_SumReLU_CTensor

open MeasureTheory ProbabilityTheory

namespace SumReLU

/-- The Hermite moment tensor `E_{(x,y)∼D}[y He_m(x)]` of the example law, entrywise, with
`y = f(x) = reluSum β w x` and `He_m` the normalized Hermite tensor of Definition 2.5 (published
`GaussPart.hermiteTensor`).

Diakonikolas, Diakonikolas, Wang, Zarifis, *Learning Positive Linear Combinations of ReLUs in
Fully Polynomial Time*, arXiv:2610.32940 (PDF sha256 66803576…6c48), Eq. (M), p.24 (PDF p.26); Definition 2.5, (6), p.11 (PDF p.13).

**Formalization Note.** `GaussPart.hermiteTensor m x J = (1/√(m!)) ∏_r He_{β_r}(x_r)` with `β_r`
the number of occurrences of `r` in `J`; this is (6), because the sum over partitions of `[m]`
into singletons and pairs factors over the coordinates, and on one coordinate it is the
probabilists' `He_{β_r}`. -/
noncomputable def momentTensor {d k : ℕ} (β : Fin k → ℝ) (w : Fin k → EuclideanSpace ℝ (Fin d))
    (m : ℕ) (J : Fin m → Fin d) : ℝ :=
  ∫ x, reluSum β w x * GaussPart.hermiteTensor m x J ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))

/-- The filter `u^{⊗p} ⊗ ū^{⊗p} ∈ (ℂᵈ)^{⊗2p}`: entry `J` is
`∏_{m<p} u_{J_m} · ∏_{m<p} \overline{u_{J_{p+m}}}` (Eq. (M), p.24, PDF p.26). -/
noncomputable def filter {d : ℕ} (p : ℕ) (u : Fin d → ℂ) : CTensor d (2 * p) :=
  fun J => (∏ m : Fin p, u (J (Fin.cast (two_mul p).symm (Fin.castAdd p m)))) *
    ∏ m : Fin p, star (u (J (Fin.cast (two_mul p).symm (Fin.natAdd p m))))

/-- The partial contraction `⟨W, T⟩` of an order-`(2p+2)` tensor `W` with an order-`2p` tensor
`T` over the **first** `2p` indices, a `d × d` array:
`(⟨W, T⟩)_{a b} = ∑_{i₁…i_{2p}} \overline{(W)_{i₁…i_{2p} a b}} (T)_{i₁…i_{2p}}` (§2, p.10, PDF p.12). -/
noncomputable def contract {d p : ℕ} (W : (Fin (2 * p + 2) → Fin d) → ℝ) (T : CTensor d (2 * p))
    (a b : Fin d) : ℂ :=
  ∑ J : Fin (2 * p) → Fin d, star ((W (Fin.append J ![a, b]) : ℝ) : ℂ) * T J

/-- **The filtered matrix** `M_{2p+2}(u) = Z⁻¹ ∑_{i∈[k]} β_i |w_i · u|^{2p} w_i w_iᵀ`, form (ii) of
Eq. (M), with `Z = Z_p(U) > 0` the normalizing parameter.

Diakonikolas, Diakonikolas, Wang, Zarifis, *Learning Positive Linear Combinations of ReLUs in
Fully Polynomial Time*, arXiv:2610.32940 (PDF sha256 66803576…6c48), Eq. (M), p.24 (PDF p.26). Form (i) is `Z⁻¹ ⟨σ̂_{2p+2}⁻¹ E[y He_{2p+2}(x)], u^{⊗p} ⊗ ū^{⊗p}⟩`;
their equality is a milestone (`eq_M`). -/
noncomputable def filterMatrix {d k : ℕ} (β : Fin k → ℝ) (w : Fin k → EuclideanSpace ℝ (Fin d))
    (p : ℕ) (Z : ℝ) (u : Fin d → ℂ) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun a b => Z⁻¹ * ∑ i, β i * ‖dotC (w i) u‖ ^ (2 * p) * (w i a * w i b)

end SumReLU


