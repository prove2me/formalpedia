-- Prove2me | Definitions.Def_WassFSG_Conc_Setting
-- name    : WassFSG_Conc_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T09:48:54.279244+00:00
-- url     : https://prove2.me/theorems/71704a13-4fa3-4e5e-b56e-d29a2172f0eb
-- title:
--   Sec. 2, 3.1, Def. 1, App. B — 𝒫_p, T_p(τ), Wasserstein regularizer, I_p, dual objective (1), product distance d_p, 𝒥, ℛ
-- statement:
--   Let $\mathcal Z$ be a separable real Banach space with norm $\|\cdot\|$ and its Borel $\sigma$-algebra, and let $p\in[1,\infty)$. This module fixes the objects of Sections 2–3 and Appendix B of Gao's paper.
--
--   1. **Finite-moment class.** $\mathcal P_p(\mathcal Z)$ is the set of probability measures $\mathbb Q$ with $\mathbb E_{\mathbb Q}[\|z\|^p]<\infty$. More generally, for a moment function $m$, $\mathcal P_m$ is the set of probability measures with $\mathbb E_{\mathbb Q}[m]<\infty$.
--   2. **Wasserstein distance.** $\mathcal W_p(\mathbb P,\mathbb Q)^p=\inf_\pi \mathbb E_{(\tilde z,z)\sim\pi}[\|\tilde z-z\|^p]$, the infimum over couplings $\pi$ with marginals $\mathbb P,\mathbb Q$ (the published optimal transport cost with cost $c(u,w)=\|u-w\|^p$).
--   3. **Transportation-information inequality (Definition 1).** For a cost $c$ and a moment function $m$, a distribution $\mathbb P\in\mathcal P_m$ satisfies $T_p(\tau)$ if
--   $$\mathcal W_c(\mathbb Q,\mathbb P)\le\big(\tau\,H(\mathbb Q\|\mathbb P)\big)^{p/2}\qquad\forall\,\mathbb Q\in\mathcal P_m,$$
--   where $\mathcal W_c$ is the optimal transport cost and $H(\mathbb Q\|\mathbb P)$ the relative entropy ($+\infty$ unless $\mathbb Q\ll\mathbb P$). With $c=\|\cdot-\cdot\|^p$ this is $\mathcal W_p(\mathbb Q,\mathbb P)\le\sqrt{\tau H(\mathbb Q\|\mathbb P)}$; on $\mathcal Z^n$ the cost is $\mathsf d_p(z,\tilde z)^p=\sum_{i=1}^n\|z_i-\tilde z_i\|^p$ and the moment is $\sum_i\|z_i\|^p$.
--   4. **Wasserstein regularizer.** For a nominal $\mathbb Q$, a radius $\rho\ge0$ and a loss $f$,
--   $$\mathcal R_{\mathbb Q,p}(\rho;f)=\sup_{\mathbb P\in\mathcal P_p(\mathcal Z)}\{\mathbb E_{\mathbb P}[f]:\mathcal W_p(\mathbb P,\mathbb Q)\le\rho\}-\mathbb E_{\mathbb Q}[f],$$
--   valued in $[-\infty,+\infty]$.
--   5. **The rate function $\mathcal I_p$.** With $\Phi_g(t)=\mathbb E_{z\sim\mathbb P_{\rm true}}\big[\sup_{\tilde z\in\mathcal Z}\{t(g(\tilde z)-g(z))-\|\tilde z-z\|^p\}\big]\in[0,\infty]$,
--   $$\mathcal I_p(\varepsilon;g)^p=\max\Big(0,\ \sup_{t>0}\{\varepsilon t-\Phi_g(t)\}\Big)\in[0,\infty].$$
--   The bound $\exp(-n\,\mathcal I_p^2/\tau)$ is $\exp(-n(\mathcal I_p^p)^{2/p}/\tau)$, read as $0$ when $\mathcal I_p=+\infty$.
--   6. **Dual objective of (1).** $D(\lambda)=\lambda\rho^p+\mathbb E_{z\sim\mathbb Q}[\sup_{\tilde z}\{f(\tilde z)-\lambda\|\tilde z-z\|^p\}]$, and $\lambda_o$ is a dual minimizer if $\lambda_o\ge0$ minimizes $D$ over $\lambda\ge0$. The growth rate is $\underline\lambda=\limsup_{\|z\|\to\infty}f(z)/\|z\|^p\in[-\infty,\infty]$.
--   7. **Empirical mean and Lipschitz norm.** $\mathbb E_{\mathbb P_n}[f]=\frac1n\sum_{i=1}^n f(z_i)$ for a sample $z\in\mathcal Z^n$, and $\|f\|_{\rm Lip}=\sup_{z\ne z'}|f(z')-f(z)|/\|z'-z\|$.
--   8. **Lemma 5's functionals** for $F:\mathcal Z^n\to\mathbb R$, with $\mathbb E_\otimes$ the expectation under the $n$-fold product $\mathbb P_\otimes$ of $\mathbb P_{\rm true}$:
--   $$\mathcal J(\varepsilon;F)^p=\max\Big(0,\sup_{t>0}\Big\{\varepsilon t-\mathbb E_\otimes\Big[\sup_{\tilde z\in\mathcal Z^n}\Big\{t(F(\tilde z)-F(z))-\tfrac1n\mathsf d_p(\tilde z,z)^p\Big\}\Big]\Big\}\Big),$$
--   $$\mathcal R(\rho;F)=\inf_{\lambda\ge0}\Big\{\lambda\rho^p+\mathbb E_\otimes\Big[\sup_{\tilde z\in\mathcal Z^n}\Big\{F(\tilde z)-F(z)-\tfrac\lambda n\mathsf d_p(\tilde z,z)^p\Big\}\Big]\Big\}\in[0,\infty].$$
--
--   These are the shared objects of the variation-based concentration inequality (Theorem 1), its general form (Lemma 5), the tensorization of $T_p$ (Lemma 4) and the inverse of the regularizer (Proposition 1).
--
--   **Formalization Note** $\mathcal Z$ carries `[CompleteSpace]`, `[BorelSpace]` and `[SecondCountableTopology]` (Banach, Borel, separable: the cited duality results are for Polish spaces). Expectations of a loss inside the supremum are the extended integral $\int f^+-\int f^-$ in `EReal`; $\Phi$, $\mathcal J$ and $\mathcal R$ are lower Lebesgue integrals in $[0,\infty]$ of inner suprema that are $\ge0$ (take $\tilde z=z$), so truncation at $0$ changes nothing. The paper declares $\mathcal I_p,\mathcal J:\mathbb R_+\to\mathbb R_+\cup\{+\infty\}$, but the inner supremum over $t$ can be negative or $-\infty$; the $\max(0,\cdot)$ reading is the only one under which the declared codomain holds. Lemma 5's $\mathcal R$ is printed with "min"; it is an infimum here because the minimum need not be attained. $\underline\lambda$ is a $\limsup$ because the printed limit need not exist. The product distance is the $\ell_p$-sum, not the sup metric on `Fin n → Z`.
-- source:
--   Gao, Finite-Sample Guarantees for Wasserstein Distributionally Robust Optimization: Breaking the Curse of Dimensionality, arXiv:2009.04382, Sec. 2 Notation and eq. (1) (pp. 4–5), Sec. 3.1 display defining I_p and Definition 1 (p. 6), App. B.1 product distance d_p (p. 20), Lemma 5 displays defining 𝒥 and ℛ (p. 21)

import Mathlib
import Definitions.Def_RWPI_SqrtLasso_transportCost
import Definitions.Def_ModelRiskOT_Duality_extIntegral

namespace WassFSG.Conc

open MeasureTheory
open scoped ENNReal

/-! ### Generic objects on a measurable space `X` with a cost `c` and a moment function `m`

They are instantiated twice: on `Z` (cost `‖z̃ - z‖^p`, moment `‖z‖^p`) and on `Z^n = Fin n → Z`
(cost `d_p(z̃, z)^p = ∑ᵢ ‖z̃ᵢ - zᵢ‖^p`, moment `d_p(z, 0)^p = ∑ᵢ ‖zᵢ‖^p`), p. 4 and p. 20. -/

/-- `𝒫_p` (p. 4): `Q` is a probability measure with finite moment `E_Q[m] < ∞`. -/
def IsPp {X : Type*} [MeasurableSpace X] (m : X → ℝ≥0∞) (Q : Measure X) : Prop :=
  IsProbabilityMeasure Q ∧ ∫⁻ x, m x ∂Q < ∞

/-- Definition 1 (p. 6), for a general cost: `P ∈ 𝒫_p` satisfies the transportation-information
inequality `T_p(τ)`, i.e. `W_p(Q, P) ≤ √(τ H(Q‖P))` for every `Q ∈ 𝒫_p`, written with
`W_p(Q, P)^p = transportCost c Q P` as `W_p(Q, P)^p ≤ (τ H(Q‖P))^{p/2}`. -/
def TransportInfo {X : Type*} [MeasurableSpace X] (c : X → X → ℝ≥0∞) (m : X → ℝ≥0∞)
    (p τ : ℝ) (P : Measure X) : Prop :=
  IsPp m P ∧ ∀ Q : Measure X, IsPp m Q →
    RWPI.SqrtLasso.transportCost c Q P ≤ (ENNReal.ofReal τ * InformationTheory.klDiv Q P) ^ (p / 2)

/-- The bound `exp(-n I² / τ)` of Theorem 1 and Lemma 5, where `I^p = Ipow ∈ [0, ∞]`, so
`I² = Ipow^{2/p}`; an infinite rate gives the bound `0`. -/
noncomputable def expRate (n : ℕ) (τ p : ℝ) (Ipow : ℝ≥0∞) : ℝ≥0∞ :=
  if Ipow = ⊤ then 0 else ENNReal.ofReal (Real.exp (-((n : ℝ) * Ipow.toReal ^ (2 / p)) / τ))

/-! ### Objects on the Banach space `Z` -/

variable {Z : Type*} [NormedAddCommGroup Z] [MeasurableSpace Z]

/-- The transport cost `‖u - w‖^p` (p. 4). -/
noncomputable def costP (p : ℝ) (u w : Z) : ℝ≥0∞ := ‖u - w‖ₑ ^ p

/-- The `p`-th moment `‖z‖^p` defining `𝒫_p(Z)` (p. 4). -/
noncomputable def momentP (p : ℝ) (z : Z) : ℝ≥0∞ := ‖z‖ₑ ^ p

/-- `T_p(τ)` on `Z` (Definition 1, p. 6). -/
def Tp (p τ : ℝ) (P : Measure Z) : Prop :=
  TransportInfo (costP p) (momentP p) p τ P

/-- The Wasserstein robust loss `sup { E_P[f] : P ∈ 𝒫_p(Z), W_p(P, Q) ≤ ρ }` (p. 5), in `EReal`. -/
noncomputable def robustLoss (p ρ : ℝ) (Q : Measure Z) (f : Z → ℝ) : EReal :=
  ⨆ (P : Measure Z) (_ : IsPp (momentP p) P ∧
      RWPI.SqrtLasso.transportCost (costP p) P Q ≤ ENNReal.ofReal (ρ ^ p)),
    ModelRiskOT.Duality.extIntegral P (fun z => (f z : EReal))

/-- The Wasserstein regularizer `R_{Q,p}(ρ; f) = sup {E_P[f] : P ∈ 𝒫_p(Z), W_p(P, Q) ≤ ρ} - E_Q[f]`
(p. 5), in `EReal`. -/
noncomputable def regularizer (p ρ : ℝ) (Q : Measure Z) (f : Z → ℝ) : EReal :=
  robustLoss p ρ Q f - ModelRiskOT.Duality.extIntegral Q (fun z => (f z : EReal))

/-- `Φ_g(t) = E_{z∼P}[ sup_{z̃ ∈ Z} { t (g(z̃) - g(z)) - ‖z̃ - z‖^p } ] ∈ [0, ∞]` (Sec. 3.1, p. 6;
App. B, p. 20). The inner supremum is `≥ 0` (take `z̃ = z`), so truncating at `0` changes nothing. -/
noncomputable def Phi (p : ℝ) (P : Measure Z) (g : Z → ℝ) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ z, ⨆ zt : Z, ENNReal.ofReal (t * (g zt - g z) - ‖zt - z‖ ^ p) ∂P

/-- `I_p(ε; g)^p = max(0, sup_{t > 0} { ε t - Φ_g(t) })` (Sec. 3.1, p. 6), valued in `[0, ∞]`. -/
noncomputable def Ipow (p : ℝ) (P : Measure Z) (g : Z → ℝ) (ε : ℝ) : ℝ≥0∞ :=
  ⨆ (t : ℝ) (_ : 0 < t), (ENNReal.ofReal (ε * t) - Phi p P g t)

/-- The dual objective of (1) (p. 5): `λ ρ^p + E_{z∼Q}[ sup_{z̃} { f(z̃) - λ ‖z̃ - z‖^p } ]`, in `EReal`. -/
noncomputable def dualObj (p ρ : ℝ) (Q : Measure Z) (f : Z → ℝ) (lam : ℝ) : EReal :=
  ((lam * ρ ^ p : ℝ) : EReal) +
    ModelRiskOT.Duality.extIntegral Q
      (fun z => ⨆ zt : Z, ((f zt - lam * ‖zt - z‖ ^ p : ℝ) : EReal))

/-- `λ_o` is a minimizer of the dual problem (1) over `λ ≥ 0`. -/
def IsDualMinimizer (p ρ : ℝ) (Q : Measure Z) (f : Z → ℝ) (lamo : ℝ) : Prop :=
  0 ≤ lamo ∧ ∀ lam : ℝ, 0 ≤ lam → dualObj p ρ Q f lamo ≤ dualObj p ρ Q f lam

/-- The growth rate `λ̲ = limsup_{‖z‖ → ∞} f(z) / ‖z‖^p` of Proposition 1 (p. 6), in `EReal`. -/
noncomputable def growthRate (p : ℝ) (f : Z → ℝ) : EReal :=
  Filter.limsup (fun z => ((f z / ‖z‖ ^ p : ℝ) : EReal)) (Bornology.cobounded Z)

/-- The empirical mean `E_{P_n}[f] = (1/n) ∑ᵢ f(zᵢ)` of a sample `z : Fin n → Z`. -/
noncomputable def empMean {n : ℕ} (f : Z → ℝ) (z : Fin n → Z) : ℝ :=
  (1 / (n : ℝ)) * ∑ i, f (z i)

/-- The Lipschitz norm `‖f‖_Lip = sup_{z ≠ z'} |f(z') - f(z)| / ‖z' - z‖` (p. 4). -/
noncomputable def lipNorm (f : Z → ℝ) : ℝ :=
  ⨆ (z : Z) (z' : Z) (_ : z ≠ z'), |f z' - f z| / ‖z' - z‖

/-! ### Objects on the product space `Z^n` (App. B.1, pp. 20–21) -/

/-- `d_p(x, y)^p = ∑ᵢ ‖xᵢ - yᵢ‖^p` (p. 20), as a cost in `[0, ∞]`. -/
noncomputable def prodCost {n : ℕ} (p : ℝ) (x y : Fin n → Z) : ℝ≥0∞ :=
  ∑ i, ‖x i - y i‖ₑ ^ p

/-- `d_p(x, 0)^p = ∑ᵢ ‖xᵢ‖^p`, the moment defining `𝒫_p(Z^n)`. -/
noncomputable def prodMoment {n : ℕ} (p : ℝ) (x : Fin n → Z) : ℝ≥0∞ :=
  ∑ i, ‖x i‖ₑ ^ p

/-- `d_p(x, y)^p = ∑ᵢ ‖xᵢ - yᵢ‖^p` (p. 20), real-valued. -/
noncomputable def dpPow {n : ℕ} (p : ℝ) (x y : Fin n → Z) : ℝ :=
  ∑ i, ‖x i - y i‖ ^ p

/-- `T_p(τ)` on `(Z^n, d_p)` (Definition 1 with the product distance of p. 20). -/
def TpProd (n : ℕ) (p τ : ℝ) (P : Measure (Fin n → Z)) : Prop :=
  TransportInfo (prodCost (n := n) p) (prodMoment (n := n) p) p τ P

/-- `Φ(t; F) = E_⊗[ sup_{z̃ ∈ Z^n} { t (F(z̃) - F(z)) - (1/n) d_p(z̃, z)^p } ] ∈ [0, ∞]` (Lemma 5, p. 21);
the inner supremum is `≥ 0` (take `z̃ = z`). -/
noncomputable def PhiN (n : ℕ) (p : ℝ) (P : Measure Z) (F : (Fin n → Z) → ℝ) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ z, ⨆ zt : Fin n → Z,
      ENNReal.ofReal (t * (F zt - F z) - (1 / (n : ℝ)) * dpPow p zt z) ∂(Measure.pi fun _ : Fin n => P)

/-- `𝒥(ε; F)^p = max(0, sup_{t > 0} { ε t - Φ(t; F) })` (Lemma 5, p. 21), valued in `[0, ∞]`. -/
noncomputable def Jpow (n : ℕ) (p : ℝ) (P : Measure Z) (F : (Fin n → Z) → ℝ) (ε : ℝ) : ℝ≥0∞ :=
  ⨆ (t : ℝ) (_ : 0 < t), (ENNReal.ofReal (ε * t) - PhiN n p P F t)

/-- `ℛ(ρ; F) = inf_{λ ≥ 0} { λ ρ^p + E_⊗[ sup_{z̃ ∈ Z^n} { F(z̃) - F(z) - (λ/n) d_p(z̃, z)^p } ] }`
(Lemma 5, p. 21, with `inf` for the printed `min`), valued in `[0, ∞]`; the inner supremum is `≥ 0`. -/
noncomputable def calR (n : ℕ) (p : ℝ) (P : Measure Z) (F : (Fin n → Z) → ℝ) (ρ : ℝ) : ℝ≥0∞ :=
  ⨅ (lam : ℝ) (_ : 0 ≤ lam), (ENNReal.ofReal (lam * ρ ^ p) +
    ∫⁻ z, ⨆ zt : Fin n → Z,
        ENNReal.ofReal (F zt - F z - (lam / (n : ℝ)) * dpPow p zt z) ∂(Measure.pi fun _ : Fin n => P))

end WassFSG.Conc


