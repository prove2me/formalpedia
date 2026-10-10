-- Prove2me | Definitions.Def_SinkhornDRO_BSMD_Estimators
-- name    : SinkhornDRO_BSMD_Estimators
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T14:24:57.472357+00:00
-- url     : https://prove2.me/theorems/2d1ea0ea-7ce2-40c8-9e77-966eb6466616
-- title:
--   U, A^ℓ, g^ℓ, G^ℓ, the SG estimator (15), the RT-MLMC estimator (16)–(17), and the hyper-parameters of p. ec20
-- statement:
--   Fix $\lambda,\epsilon>0$, a loss $f_\theta(z)$ and a subgradient selector $\nabla_\theta f_\theta(z)$. For a sample $\zeta=(x,z_1,\dots,z_n)$ and a block $S$ of indices:
--
--   1. $U_S(\theta,\zeta)=\lambda\epsilon\log\big(\frac1{|S|}\sum_{j\in S}e^{f_\theta(z_j)/(\lambda\epsilon)}\big)$, and $U_\emptyset=0$.
--
--   2. $A^\ell=U_{1:2^\ell}-\tfrac12U_{1:2^{\ell-1}}-\tfrac12U_{2^{\ell-1}+1:2^\ell}$; for $\ell=0$ both halves are empty and $A^0=U_{1:1}$.
--
--   3. $g^\ell(\theta,\zeta^\ell)=\nabla_\theta U_{1:2^\ell}(\theta,\zeta^\ell)$ and $G^\ell(\theta,\zeta^\ell)=\nabla_\theta A^\ell(\theta,\zeta^\ell)$, computed by the chain rule from the same selected subgradients in all blocks:
--   $$\nabla_\theta U_S=\sum_{j\in S}w^S_j\,\nabla_\theta f_\theta(z_j),\qquad w^S_j=\frac{e^{f_\theta(z_j)/(\lambda\epsilon)}}{\sum_{k\in S}e^{f_\theta(z_k)/(\lambda\epsilon)}} .$$
--   In particular $G^0=g^0$.
--
--   4. **SG estimator (15).** $v^{SG}(\theta)=g^L(\theta,\zeta^L)$.
--
--   5. **RT-MLMC estimator (16)–(17).** Draw $\hat\ell\in\{0,\dots,L\}$ with $p_\ell=\Pr(\hat\ell=\ell)=\dfrac{2^{-\ell}}{2-2^{-L}}$, independently of $\zeta^L$, and set $v^{RT\text{-}MLMC}(\theta)=p_{\hat\ell}^{-1}G^{\hat\ell}(\theta,\zeta^{\hat\ell})$, where $\zeta^{\hat\ell}$ consists of $x$ and the first $2^{\hat\ell}$ draws.
--
--   6. **Hyper-parameters (p. ec20).** With $K=B/(\lambda\epsilon)$, $D=D_\omega(\theta_0,\bar\theta^*)$ and tolerance $\delta>0$:
--   $$L=\max\Big(1,\Big\lceil\frac{1}{\log2}\log\frac{2\lambda\epsilon e^{2K}}{\delta}\Big\rceil\Big),$$
--   SG: $T=\max\big(1,\lceil 8L_f^2D/(\kappa\mathfrak c^2\delta^2)\rceil\big)$, $h=\sqrt{2\kappa\mathfrak c^2D/(TL_f^2)}$;
--   RT-MLMC: $M^2=2(L+1)L_f^2e^{4K}/\mathfrak c^2$, $T=\max\big(1,\lceil16(L+1)L_f^2De^{4K}/(\kappa\mathfrak c^2\delta^2)\rceil\big)$, $h=\sqrt{2\kappa D/(TM^2)}$.
--
--   These are the two biased subgradient estimators of Algorithm 1 and the parameters with which Theorem 2 is proved.
--
--   **Formalization Note** The page writes $g^\ell=\nabla_\theta U$, $G^\ell=\nabla_\theta A^\ell$ for a nonsmooth loss; the explicit chain-rule form above is the subgradient obtained when "the same subgradient computation" is used across the three blocks, as the page prescribes. The RT-MLMC sample is $(\hat\ell,x,z_1,\dots,z_{2^L})$ and level $\hat\ell$ reads the first $2^{\hat\ell}$ draws, which has the paper's law of $\zeta^{\hat\ell}$ given $\hat\ell$. The `max 1` guards keep $L\in\mathbb N_+$ (as the paper requires) and $T\ge1$; they preserve $2^L\ge2\lambda\epsilon e^{2K}/\delta$. The paper's $(M_*^{RT\text{-}MLMC})^2=2(L+1)L_f^2e^{4K}$ omits the factor $\mathfrak c^{-2}$ that its own display derives and that its $T$ carries; $M^2$ here keeps it (the two agree when $\mathfrak c=1$). With $L_f=0$ the step sizes evaluate to $0$ (Lean's $x/0=0$); then every selected subgradient is $0$ and the step is immaterial.
-- source:
--   Wang, Gao, Xie, Sinkhorn Distributionally Robust Optimization, arXiv:2109.11926v5, p. 15 (U, A^ℓ, g^ℓ, G^ℓ, (15)), p. 16 ((16), (17)), p. ec20 (hyper-parameters)

import Mathlib
import Definitions.Def_SinkhornDRO_BSMD_MirrorSetup
import Definitions.Def_SinkhornDRO_BSMD_Objective

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace SinkhornDRO.BSMD

variable {d : ℕ} {Z : Type*} [MeasurableSpace Z]

/-- `U_S(θ, ζ) = λε log( |S|⁻¹ Σ_{j∈S} e^{f_θ(z_j)/(λε)} )` for a block `S` of sample indices,
and `U_∅ = 0` (p. 15, the paper's `U_{n1:n2}`). -/
noncomputable def blockU (lam eps : ℝ) (f : Param d → Z → ℝ) (θ : Param d) {n : ℕ}
    (zs : Fin n → Z) (S : Finset (Fin n)) : ℝ :=
  if S = ∅ then 0
  else lam * eps * Real.log (((S.card : ℝ))⁻¹ * ∑ j ∈ S, Real.exp (f θ (zs j) / (lam * eps)))

/-- The subgradient of `θ ↦ U_S(θ, ζ)` obtained from the subgradient selector `sg` by the chain
rule: `Σ_{j∈S} w_j ∇_θ f_θ(z_j)`, with softmax weights
`w_j = e^{f_θ(z_j)/(λε)} / Σ_{k∈S} e^{f_θ(z_k)/(λε)}` (and `0` for `S = ∅`). -/
noncomputable def blockGrad (lam eps : ℝ) (f : Param d → Z → ℝ) (sg : Param d → Z → Param d)
    (θ : Param d) {n : ℕ} (zs : Fin n → Z) (S : Finset (Fin n)) : Param d :=
  ∑ j ∈ S, (Real.exp (f θ (zs j) / (lam * eps)) /
      ∑ k ∈ S, Real.exp (f θ (zs k) / (lam * eps))) • sg θ (zs j)

/-- First half `[1 : 2^ℓ]` of the `2^{ℓ+1}` samples of level `ℓ + 1` (0-based indices `< 2^ℓ`). -/
def lowHalf (ℓ : ℕ) : Finset (Fin (2 ^ (ℓ + 1))) :=
  Finset.univ.filter (fun j => j.val < 2 ^ ℓ)

/-- Second half `[2^ℓ + 1 : 2^{ℓ+1}]` of the samples of level `ℓ + 1`. -/
def highHalf (ℓ : ℕ) : Finset (Fin (2 ^ (ℓ + 1))) :=
  Finset.univ.filter (fun j => 2 ^ ℓ ≤ j.val)

/-- `A^ℓ(θ, ζ^ℓ) = U_{1:2^ℓ} − ½ U_{1:2^{ℓ−1}} − ½ U_{2^{ℓ−1}+1:2^ℓ}` (p. 15). For `ℓ = 0` both
halves are empty, so `A⁰ = U_{1:1}`. -/
noncomputable def levelA (lam eps : ℝ) (f : Param d → Z → ℝ) :
    (ℓ : ℕ) → Param d → (Fin (2 ^ ℓ) → Z) → ℝ
  | 0, θ, zs => blockU lam eps f θ zs Finset.univ
  | ℓ + 1, θ, zs =>
    blockU lam eps f θ zs Finset.univ - (1 / 2 : ℝ) * blockU lam eps f θ zs (lowHalf ℓ)
      - (1 / 2 : ℝ) * blockU lam eps f θ zs (highHalf ℓ)

/-- `g^ℓ(θ, ζ^ℓ) = ∇_θ U_{1:2^ℓ}(θ, ζ^ℓ)` (p. 15), computed by the chain rule from `sg`. -/
noncomputable def levelg (lam eps : ℝ) (f : Param d → Z → ℝ) (sg : Param d → Z → Param d)
    (ℓ : ℕ) (θ : Param d) (zs : Fin (2 ^ ℓ) → Z) : Param d :=
  blockGrad lam eps f sg θ zs Finset.univ

/-- `G^ℓ(θ, ζ^ℓ) = ∇_θ A^ℓ(θ, ζ^ℓ)` (p. 15), with the same subgradients `sg θ z_j` in all three
blocks ("the same subgradient computation"). For `ℓ = 0`, `G⁰ = g⁰`. -/
noncomputable def levelG (lam eps : ℝ) (f : Param d → Z → ℝ) (sg : Param d → Z → Param d) :
    (ℓ : ℕ) → Param d → (Fin (2 ^ ℓ) → Z) → Param d
  | 0, θ, zs => blockGrad lam eps f sg θ zs Finset.univ
  | ℓ + 1, θ, zs =>
    blockGrad lam eps f sg θ zs Finset.univ - (1 / 2 : ℝ) • blockGrad lam eps f sg θ zs (lowHalf ℓ)
      - (1 / 2 : ℝ) • blockGrad lam eps f sg θ zs (highHalf ℓ)

/-- The SG estimator (15), p. 15: `v^SG(θ) = g^L(θ, ζ^L)`, `ζ^L = (x, z_1, …, z_{2^L})`. -/
noncomputable def vSG (lam eps : ℝ) (f : Param d → Z → ℝ) (sg : Param d → Z → Param d) (L : ℕ)
    (θ : Param d) (ζ : Z × (Fin (2 ^ L) → Z)) : Param d :=
  levelg lam eps f sg L θ ζ.2

/-- The truncated geometric level distribution (16), p. 16:
`p_ℓ = 2^{−ℓ} / (2 − 2^{−L})`, `ℓ = 0, …, L`. -/
noncomputable def levelProb (L ℓ : ℕ) : ℝ :=
  ((2 : ℝ) ^ ℓ)⁻¹ / (2 - ((2 : ℝ) ^ L)⁻¹)

/-- The first `2^ℓ` of `2^L` samples (`ℓ ≤ L`). -/
def truncSamples {L : ℕ} (ℓ : Fin (L + 1)) (zs : Fin (2 ^ L) → Z) : Fin (2 ^ (ℓ : ℕ)) → Z :=
  fun j => zs (Fin.castLE (Nat.pow_le_pow_right (by norm_num) (Nat.lt_succ_iff.mp ℓ.isLt)) j)

/-- The RT-MLMC estimator (17), p. 16: `v^{RT-MLMC}(θ) = p_ℓ̂⁻¹ · G^ℓ̂(θ, ζ^ℓ̂)`. The sample is
`(ℓ̂, x, z_1, …, z_{2^L})`; level `ℓ̂` uses `x` and the first `2^ℓ̂` draws, which is a sample of
`ζ^ℓ̂` given `ℓ̂`. -/
noncomputable def vRT (lam eps : ℝ) (f : Param d → Z → ℝ) (sg : Param d → Z → Param d) (L : ℕ)
    (θ : Param d) (ζ : Fin (L + 1) × Z × (Fin (2 ^ L) → Z)) : Param d :=
  (levelProb L ζ.1)⁻¹ • levelG lam eps f sg ζ.1 θ (truncSamples ζ.1 ζ.2.2)

/-- The sampling law of the RT-MLMC estimator: `ℓ̂ ∼ p` of (16), independent of
`(x, z_1, …, z_{2^L}) ∼ levelLaw P Q (2^L)`. -/
noncomputable def rtLaw (P : Measure Z) (Q : Kernel Z Z) [IsMarkovKernel Q] (L : ℕ) :
    Measure (Fin (L + 1) × Z × (Fin (2 ^ L) → Z)) :=
  ∑ ℓ : Fin (L + 1), ENNReal.ofReal (levelProb L ℓ) •
    (levelLaw P Q (2 ^ L)).map (fun ζ => (ℓ, ζ))

/-- The maximal level of p. ec20 for both estimators,
`L = ⌈ (1/log 2) · log( 2λε exp(2K) / δ ) ⌉` with `K = B/(λε)`, taken to be at least `1`
(the paper requires `L ∈ ℕ₊`). -/
noncomputable def levelL (lam eps B δ : ℝ) : ℕ :=
  max 1 ⌈Real.log (2 * lam * eps * Real.exp (2 * (B / (lam * eps))) / δ) / Real.log 2⌉₊

/-- The SG iteration count of p. ec20, `T = ⌈ 8 L_f² D / (κ 𝔠² δ²) ⌉`, at least `1`. -/
noncomputable def iterSG (Lf κ c Dstar δ : ℝ) : ℕ :=
  max 1 ⌈8 * Lf ^ 2 * Dstar / (κ * c ^ 2 * δ ^ 2)⌉₊

/-- The SG step size of p. ec20, `h = √( 2κ𝔠² D / (T L_f²) )`. -/
noncomputable def stepSG (Lf κ c Dstar : ℝ) (T : ℕ) : ℝ :=
  Real.sqrt (2 * κ * c ^ 2 * Dstar / (T * Lf ^ 2))

/-- The RT-MLMC second-moment bound `(M_*^{RT-MLMC})² = 2(L+1) L_f² exp(4K) / 𝔠²`
(p. ec20, with the factor `𝔠⁻²` of the first inequality of the display kept). -/
noncomputable def msqRT (L : ℕ) (Lf K c : ℝ) : ℝ :=
  2 * (L + 1) * Lf ^ 2 * Real.exp (4 * K) / c ^ 2

/-- The RT-MLMC iteration count of p. ec20,
`T = ⌈ 16 (L+1) L_f² D exp(4K) / (κ 𝔠² δ²) ⌉`, at least `1`. -/
noncomputable def iterRT (L : ℕ) (Lf K κ c Dstar δ : ℝ) : ℕ :=
  max 1 ⌈16 * (L + 1) * Lf ^ 2 * Dstar * Real.exp (4 * K) / (κ * c ^ 2 * δ ^ 2)⌉₊

/-- The RT-MLMC step size of p. ec20, `h = √( 2κD / (T (M_*^{RT-MLMC})²) )`. -/
noncomputable def stepRT (L : ℕ) (Lf K κ c Dstar : ℝ) (T : ℕ) : ℝ :=
  Real.sqrt (2 * κ * Dstar / (T * msqRT L Lf K c))

end SinkhornDRO.BSMD


