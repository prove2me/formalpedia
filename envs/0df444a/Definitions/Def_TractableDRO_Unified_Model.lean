-- Prove2me | Definitions.Def_TractableDRO_Unified_Model
-- name    : TractableDRO_Unified_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T03:12:56.971985+00:00
-- url     : https://prove2.me/theorems/30e832d6-10f1-44a6-af46-68f208ed6f45
-- title:
--   §3, §5 (pp. 905, 909–911) — the families 𝔽₁, 𝔽₂, 𝔽₃, the bounds π¹, π², ψ, π³ and their infimal convolution π (25)
-- statement:
--   This file sets up the objects of §5 of Goh and Sim (2010): three families of distributions of an uncertain vector, the bound each family gives on an expected positive part, and the unified bound obtained by infimal convolution.
--
--   **The random vector and the objective.** The uncertainty is a random vector $\tilde\zeta\in\mathbb R^{N_E}$ (the segregated uncertainty of §4.4). A distribution $\mathbb P$ is a probability measure on $\mathbb R^{N_E}$, with mean $\hat\zeta=E_{\mathbb P}(\tilde\zeta)$. For $r^0\in\mathbb R$ and $r\in\mathbb R^{N_E}$ the objective is $E_{\mathbb P}((r^0+r'\tilde\zeta)^+)$, and for a family $\mathbb F$ of distributions its worst case is
--   $$\sup_{\mathbb P\in\mathbb F}E_{\mathbb P}\big((r^0+r'\tilde\zeta)^+\big)\in[-\infty,+\infty],$$
--   with the paper's convention (p. 909) that a supremum over an empty family is $-\infty$ and an infimum over an empty set is $+\infty$.
--
--   **Data.** Sets $\mathcal V,\hat{\mathcal V}\subseteq\mathbb R^{N_E}$ (support and mean support); a matrix $F\in\mathbb R^{N\times N_E}$ and a covariance matrix $\Sigma\in\mathbb R^{N\times N}$ of the primitive uncertainty $\tilde z=F\tilde\zeta+g$; a matrix $F_\sigma\in\mathbb R^{N_\sigma\times N_E}$, a vector $g_\sigma\in\mathbb R^{N_\sigma}$, a set $\hat{\mathcal W}_\sigma\subseteq\mathbb R^{N_\sigma}$ and deviation bounds $\sigma_f,\sigma_b\in\mathbb R^{N_\sigma}$.
--
--   **The three families** (Theorems 1–3, pp. 909–910):
--   1. $\mathbb F_1=\{\mathbb P:\ \hat\zeta\in\hat{\mathcal V},\ \mathbb P(\tilde\zeta\in\mathcal V)=1\}$;
--   2. $\mathbb F_2=\{\mathbb P:\ \hat\zeta\in\hat{\mathcal V},\ E_{\mathbb P}(F(\tilde\zeta-\hat\zeta)(\tilde\zeta-\hat\zeta)'F')=\Sigma\}$;
--   3. $\mathbb F_3=\{\mathbb P:\ \hat\zeta\in\hat{\mathcal V},\ \sigma_{f\mathbb P}(\tilde z_\sigma)\le\sigma_f,\ \sigma_{b\mathbb P}(\tilde z_\sigma)\le\sigma_b\}$, where $\tilde z_\sigma=F_\sigma\tilde\zeta+g_\sigma$ has independent components, and the forward and backward deviations of p. 905 are
--   $$\sigma_{f\mathbb P}(\tilde z_{\sigma,j})=\sup_{\theta>0}\sqrt{\frac{2\ln E_{\mathbb P}\exp(\theta(\tilde z_{\sigma,j}-\hat z_{\sigma,j}))}{\theta^2}},\qquad \sigma_{b\mathbb P}(\tilde z_{\sigma,j})=\sup_{\theta>0}\sqrt{\frac{2\ln E_{\mathbb P}\exp(-\theta(\tilde z_{\sigma,j}-\hat z_{\sigma,j}))}{\theta^2}}.$$
--
--   **The three bounds.**
--   $$\pi^1(r^0,r)=\inf_{s\in\mathbb R^{N_E}}\Big(\sup_{\hat\zeta\in\hat{\mathcal V}}s'\hat\zeta+\sup_{\zeta\in\mathcal V}\max\{r^0+r'\zeta-s'\zeta,\,-s'\zeta\}\Big)\quad(21)$$
--   $$\pi^2(r^0,r)=\inf_{y:\,F'y=r}\ \sup_{\hat\zeta\in\hat{\mathcal V}}\Big\{\tfrac12(r^0+r'\hat\zeta)+\tfrac12\sqrt{(r^0+r'\hat\zeta)^2+y'\Sigma y}\Big\}\quad(22)$$
--   $$\pi^3(r^0,r)=\inf_{\substack{s^0,s,x^0,x:\\ x^0+x'g_\sigma=r^0,\ F_\sigma'x=r}}\Big\{(r^0-s^0-s'g_\sigma)+\sup_{\hat\zeta\in\hat{\mathcal V}}(r'-s'F_\sigma)\hat\zeta+\psi(s^0-x^0,s-x)+\psi(s^0,s)\Big\}\quad(24)$$
--   where, with $u_j=\max\{x_j\sigma_{f,j},-x_j\sigma_{b,j}\}$,
--   $$\psi(x^0,x)=\inf_{\lambda>0}\Big\{\frac{\lambda}{e}\exp\Big(\frac1\lambda\sup_{\hat z_\sigma\in\hat{\mathcal W}_\sigma}\{x^0+x'\hat z_\sigma\}+\frac{\|u\|_2^2}{2\lambda^2}\Big)\Big\}.$$
--
--   **The unified bound** (Theorem 4, p. 911). For an index set $S\subseteq\{1,2,3\}$, $\mathbb F=\bigcap_{s\in S}\mathbb F_s$ and
--   $$\pi(r^0,r)=\min\Big\{\sum_{s\in S}\pi^s(r^{0,s},r^s):\ r^0=\sum_{s\in S}r^{0,s},\ r=\sum_{s\in S}r^s\Big\}.\quad(25)$$
--
--   These objects are the statements' common vocabulary: Theorems 1–3 bound the worst case over each $\mathbb F_s$ by $\pi^s$, and Theorem 4 combines them.
--
--   **Formalization Note** A distribution is a `Measure` on `Fin N_E → ℝ` with `IsProbabilityMeasure`; $\tilde\zeta$ is the identity. The mean is the published `MomentDRO.Conf.meanVec`; $\mathbb F_1$ and $\mathbb F_3$ require integrable coordinates and $\mathbb F_2$ requires finite second moments (`HasSecondMoments`), so the mean and covariance are genuine; the covariance condition is `F * covMat P * Fᵀ = Σ`, which is $E_{\mathbb P}(F(\tilde\zeta-\hat\zeta)(\tilde\zeta-\hat\zeta)'F')$ by linearity. $\mathbb P(\tilde\zeta\in\mathcal V)=1$ is `∀ᵐ ζ ∂P, ζ ∈ V`. $(\cdot)^+$ is `max · 0`. In $\mathbb F_3$, independence is `iIndepFun` of the coordinates of $\tilde z_\sigma$, every $\exp(\theta\tilde z_{\sigma,j})$ is required integrable (otherwise the Lean integral is $0$ and $\log 0=0$, and heavy-tailed laws would pass), and "$\sigma_{f\mathbb P}(\tilde z_{\sigma,j})\le\sigma_{f,j}$" is the published `DataDrivenRO.FwdBwd.FwdDevLe` of the law of $\tilde z_{\sigma,j}$, i.e. $-2\mu/\theta+(2/\theta^2)\ln E e^{\theta t}\le\sigma_{f,j}^2$ for all $\theta>0$; for $\sigma_{f,j}\ge0$ and finite exponential moments this is exactly the bound on the square root of p. 905 (likewise `BwdDevLe`). Worst cases and all bounds take values in `EReal`; `⨅` over an empty set is $+\infty$ and `⨆` over an empty set is $-\infty$, the paper's convention; Mathlib's `EReal` has $\bot+\top=\bot$. The printed "min" of (25) and the "inf" of (21), (22), (24) are read as `⨅` (attainment is not claimed). In $\psi$ the supremum over $\hat{\mathcal W}_\sigma$ is taken outside the increasing continuous map $t\mapsto(\lambda/e)\exp(t/\lambda+\|u\|^2/(2\lambda^2))$, which gives the same value whenever $\hat{\mathcal W}_\sigma\ne\emptyset$. The data are bundled in a structure `Data`; $S$ is a `Finset (Fin 3)` with index $0,1,2$ standing for the paper's $1,2,3$. Indices of vectors are 0-based (`Fin`).
-- source:
--   Goh & Sim, Distributionally Robust Optimization and Its Tractable Approximations, Oper. Res. 58(4), 2010, DOI 10.1287/opre.1090.0795: p. 905 (§3, Directional Deviations), p. 909 (§5 convention, Theorem 1, (21)), p. 910 (Theorem 2, (22); Theorem 3, (24), ψ, u), p. 911 (Theorem 4, (25))

import Mathlib
import Definitions.Def_MomentDRO_Conf_Setting
import Definitions.Def_DataDrivenRO_FwdBwd_Setting
import Definitions.Def_TractableDRO_MeanCov_Model
import Definitions.Def_TractableDRO_MeanSupport_Model

namespace TractableDRO.Unified

open MeasureTheory ProbabilityTheory Matrix

/-! Goh & Sim (2010), §3 (p. 905) and §5 (pp. 909–911). The segregated uncertainty `ζ̃` is the
identity on `Fin n → ℝ` (`n = N_E`); a distribution `ℙ` is a probability measure `P` on it. -/

/-- The bound `π¹(r⁰, r)` of (21), p. 909. -/
noncomputable def pi1 {n : ℕ} (V Vhat : Set (Fin n → ℝ)) (r0 : ℝ) (r : Fin n → ℝ) : EReal :=
  ⨅ s : Fin n → ℝ, ((⨆ ζh ∈ Vhat, ((s ⬝ᵥ ζh : ℝ) : EReal)) +
    ⨆ ζ ∈ V, ((max (r0 + r ⬝ᵥ ζ - s ⬝ᵥ ζ) (-(s ⬝ᵥ ζ)) : ℝ) : EReal))

/-- The projected uncertainty vector `z̃_σ = F_σ ζ̃ + g_σ` (Theorem 3, p. 910). -/
def zσ {n Nσ : ℕ} (Fσ : Matrix (Fin Nσ) (Fin n) ℝ) (gσ : Fin Nσ → ℝ) (ζ : Fin n → ℝ) :
    Fin Nσ → ℝ :=
  Fσ *ᵥ ζ + gσ

/-- The family `𝔽₃ = {ℙ : ζ̂ = E_ℙ(ζ̃) ∈ 𝒱̂, σ_{fℙ}(z̃_σ) ⩽ σ_f, σ_{bℙ}(z̃_σ) ⩽ σ_b}` of
Theorem 3 (p. 910), with `z̃_σ` having independent components and finite exponential moments.
The deviation bounds are the published `FwdDevLe`/`BwdDevLe` of the law of each `z̃_{σ,j}`. -/
def family3 {n Nσ : ℕ} (Fσ : Matrix (Fin Nσ) (Fin n) ℝ) (gσ : Fin Nσ → ℝ)
    (Vhat : Set (Fin n → ℝ)) (σf σb : Fin Nσ → ℝ) : Set (Measure (Fin n → ℝ)) :=
  {P | IsProbabilityMeasure P ∧ (∀ i, Integrable (fun ζ : Fin n → ℝ => ζ i) P) ∧
    MomentDRO.Conf.meanVec P ∈ Vhat ∧
    iIndepFun (fun j (ζ : Fin n → ℝ) => zσ Fσ gσ ζ j) P ∧
    (∀ (j : Fin Nσ) (θ : ℝ), Integrable (fun ζ => Real.exp (θ * zσ Fσ gσ ζ j)) P) ∧
    (∀ j, DataDrivenRO.FwdBwd.FwdDevLe (P.map (fun ζ => zσ Fσ gσ ζ j)) (σf j)) ∧
    (∀ j, DataDrivenRO.FwdBwd.BwdDevLe (P.map (fun ζ => zσ Fσ gσ ζ j)) (σb j))}

/-- `u_j = max{x_j σ_{f,j}, −x_j σ_{b,j}}` (Theorem 3, p. 910). -/
noncomputable def uvec {Nσ : ℕ} (σf σb x : Fin Nσ → ℝ) : Fin Nσ → ℝ :=
  fun j => max (x j * σf j) (-(x j * σb j))

/-- `ψ(x⁰, x) = inf_{λ>0} (λ/e) exp((1/λ) sup_{ẑ_σ∈𝒲̂_σ}{x⁰ + x′ẑ_σ} + ‖u‖₂²/(2λ²))`
(Theorem 3, p. 910), with the supremum taken outside the increasing map `exp`. -/
noncomputable def psi {Nσ : ℕ} (Wσhat : Set (Fin Nσ → ℝ)) (σf σb : Fin Nσ → ℝ) (x0 : ℝ)
    (x : Fin Nσ → ℝ) : EReal :=
  ⨅ (lam : ℝ) (_ : 0 < lam), ⨆ zh ∈ Wσhat,
    (((lam / Real.exp 1) * Real.exp ((x0 + x ⬝ᵥ zh) / lam +
      (∑ j, uvec σf σb x j ^ 2) / (2 * lam ^ 2)) : ℝ) : EReal)

/-- The bound `π³(r⁰, r)` of (24), p. 910. -/
noncomputable def pi3 {n Nσ : ℕ} (Fσ : Matrix (Fin Nσ) (Fin n) ℝ) (gσ : Fin Nσ → ℝ)
    (Vhat : Set (Fin n → ℝ)) (Wσhat : Set (Fin Nσ → ℝ)) (σf σb : Fin Nσ → ℝ) (r0 : ℝ)
    (r : Fin n → ℝ) : EReal :=
  ⨅ (s0 : ℝ) (s : Fin Nσ → ℝ) (x0 : ℝ) (x : Fin Nσ → ℝ) (_ : x0 + x ⬝ᵥ gσ = r0)
    (_ : Fσᵀ *ᵥ x = r),
    ((((r0 - s0 - s ⬝ᵥ gσ : ℝ)) : EReal) +
      (⨆ ζh ∈ Vhat, (((r - Fσᵀ *ᵥ s) ⬝ᵥ ζh : ℝ) : EReal)) +
      psi Wσhat σf σb (s0 - x0) (s - x) + psi Wσhat σf σb s0 s)

/-- The data of the model of uncertainty shared by the three families (§3, p. 905; p. 908;
Theorem 3, p. 910). -/
structure Data (n N Nσ : ℕ) where
  /-- support set `𝒱` -/
  V : Set (Fin n → ℝ)
  /-- mean support set `𝒱̂` -/
  Vhat : Set (Fin n → ℝ)
  /-- the segregation matrix `F` in `z̃ = F ζ̃ + g` -/
  F : Matrix (Fin N) (Fin n) ℝ
  /-- the covariance `Σ` of the primitive uncertainty -/
  Sig : Matrix (Fin N) (Fin N) ℝ
  /-- `F_σ` -/
  Fσ : Matrix (Fin Nσ) (Fin n) ℝ
  /-- `g_σ` -/
  gσ : Fin Nσ → ℝ
  /-- `𝒲̂_σ` -/
  Wσhat : Set (Fin Nσ → ℝ)
  /-- forward deviation bounds `σ_f` -/
  σf : Fin Nσ → ℝ
  /-- backward deviation bounds `σ_b` -/
  σb : Fin Nσ → ℝ

/-- `𝔽_s` for `s ∈ {1, 2, 3}`, indexed by `Fin 3` (index `0, 1, 2` is the paper's `1, 2, 3`). -/
def familyOf {n N Nσ : ℕ} (D : Data n N Nσ) (s : Fin 3) : Set (Measure (Fin n → ℝ)) :=
  match s.val with
  | 0 => TractableDRO.MeanSupport.family1 D.V D.Vhat
  | 1 => TractableDRO.MeanCov.family2 D.F D.Sig D.Vhat
  | _ => family3 D.Fσ D.gσ D.Vhat D.σf D.σb

/-- `π^s` for `s ∈ {1, 2, 3}`, indexed by `Fin 3` as in `familyOf`. -/
noncomputable def piOf {n N Nσ : ℕ} (D : Data n N Nσ) (s : Fin 3) (r0 : ℝ) (r : Fin n → ℝ) :
    EReal :=
  match s.val with
  | 0 => pi1 D.V D.Vhat r0 r
  | 1 => TractableDRO.MeanCov.pi2 D.F D.Sig D.Vhat r0 r
  | _ => pi3 D.Fσ D.gσ D.Vhat D.Wσhat D.σf D.σb r0 r

/-- `𝔽 = ⋂_{s∈S} 𝔽_s` (Theorem 4, p. 911). -/
def familyU {n N Nσ : ℕ} (D : Data n N Nσ) (S : Finset (Fin 3)) : Set (Measure (Fin n → ℝ)) :=
  ⋂ s ∈ S, familyOf D s

/-- The unified bound `π(r⁰, r)` of (25), p. 911: the infimal convolution of the `π^s`, `s ∈ S`. -/
noncomputable def piU {n N Nσ : ℕ} (D : Data n N Nσ) (S : Finset (Fin 3)) (r0 : ℝ)
    (r : Fin n → ℝ) : EReal :=
  ⨅ (r0s : Fin 3 → ℝ) (rs : Fin 3 → Fin n → ℝ) (_ : r0 = ∑ s ∈ S, r0s s)
    (_ : r = ∑ s ∈ S, rs s), ∑ s ∈ S, piOf D s (r0s s) (rs s)

end TractableDRO.Unified


