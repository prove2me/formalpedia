-- Prove2me | Definitions.Def_WassFSG_Grad_Rademacher
-- name    : WassFSG_Grad_Rademacher
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T11:28:25.680861+00:00
-- url     : https://prove2.me/theorems/7276dc51-5d03-4bd0-b405-84fd875a5c8e
-- title:
--   Sec. 4.2, App. C.2.1 — Rademacher complexity 𝔑_n, normalized gradient class G, localized class, sub-root ψ, Assumption 5, R_{⊗,2}, ε_n, ρ_n, ρ̃_n
-- statement:
--   Fix a sample size $n\ge1$ and a distribution $\mathbb P_{\mathrm{true}}$ on $\mathcal Z$, and write $\mathbb E_\otimes$ for expectation over an i.i.d. sample $z = (z_1,\dots,z_n)\sim\mathbb P_{\mathrm{true}}^{\otimes n}$.
--
--   1. **Rademacher complexity.** For a class $\mathcal H$ of functions $\mathcal Z\to\mathbb R$,
--   $$
--   \mathfrak R_n(\mathcal H) = \mathbb E_\sigma\Big[\sup_{h\in\mathcal H}\frac1n\sum_{i=1}^n\sigma_i h(z_i)\Big],
--   $$
--   with $\sigma_1,\dots,\sigma_n$ i.i.d. signs, $\mathbb P\{\sigma_i=\pm1\}=\tfrac12$; its expectation $\mathbb E_\otimes[\mathfrak R_n(\mathcal H)]$ is the Rademacher complexity with respect to $\mathbb P_{\mathrm{true}}$.
--   2. **Normalized gradient class.** $\mathcal G = \big\{\, \|\nabla f\|_*^2 / \|\|\nabla f\|_*\|_{\mathbb P_{\mathrm{true}},2}^2 : f\in\mathcal F \,\big\}$.
--   3. **Localized class** at level $r$: $\{cf : f\in\mathcal F,\ 0\le c\le1,\ T(cf)\le r\}$ with $T(f) = \|\|\nabla f\|_*\|_{\mathbb P_{\mathrm{true}},2}^2$.
--   4. **Sub-root functions.** $\psi:\mathbb R_+\to\mathbb R_+$ is sub-root if it is non-constant, non-negative, non-decreasing, and $r\mapsto\psi(r)/\sqrt r$ is non-increasing on $r>0$.
--   5. **Assumption 5.** $\psi_n$ is sub-root and $\psi_n(r)\ge\mathbb E_\otimes[\mathfrak R_n(\{cf : f\in\mathcal F, 0\le c\le1, T(cf)\le r\})]$ for every level $r>0$ (the page defines the localized complexity at levels $r>0$).
--   6. **The class $-\mathcal F$** $=\{-f : f\in\mathcal F\}$, and the product regularizer
--   $$
--   \mathcal R_{\otimes,2}(\rho;\mathcal F) = \inf_{\lambda\ge0}\Big\{\lambda\rho^2 + \mathbb E_\otimes\Big[\sup_{f\in\mathcal F,\ \tilde z\in\mathcal Z^n}\frac1n\sum_{i=1}^n\big(f(\tilde z_i) - f(z_i) - \lambda\|\tilde z_i - z_i\|^2\big)\Big]\Big\}.
--   $$
--   7. **Radii and remainders of Theorem 3 and Corollary 6.** With $R_{\mathcal G} = \mathbb E_\otimes[\mathfrak R_n(\mathcal G)]$ and $r_{n\star}$ the fixed point of $\psi_n$,
--   $$
--   \epsilon_n = \frac{\hbar\tau t + 1 + R_{\mathcal G}}{n},\qquad \rho_n = 2\sqrt{\frac{\tau t}{n}}\,(1 + R_{\mathcal G}) + \sqrt{4r_{n\star} + 2\epsilon_n},\qquad \tilde\rho_n = \rho_n\Big(1 + 2R_{\mathcal G} + \kappa_g^2\sqrt{\frac{t}{2n}}\Big),
--   $$
--   and the number of peeling events $N_2 = \max\big(0, \lceil\log_2(\gamma_2\sqrt{\tau t n})\rceil\big) + 1$.
--
--   These are the objects of the local Rademacher analysis of Section 4.2 for the gradient-regularized ($p=2$) case.
--
--   **Formalization Note** Signs are encoded by Booleans and $\mathbb E_\sigma$ is the average over the $2^n$ sign vectors; the supremum is taken in the extended reals ($-\infty$ for an empty class). $\mathbb E_\otimes[\mathfrak R_n]$ and the expectation inside $\mathcal R_{\otimes,2}$ are extended integrals $\int\varphi^+-\int\varphi^-$ (`ModelRiskOT.Duality.extIntegral`). The page writes $\min_{\lambda\ge0}$ in $\mathcal R_{\otimes,2}$; the minimum need not be attained, so the infimum is used. $\epsilon_n$, $\rho_n$, $\tilde\rho_n$ take $R_{\mathcal G}$ as a real argument; the theorems tie it to $\mathbb E_\otimes[\mathfrak R_n(\mathcal G)]$ by a hypothesis. $N_2$ is the **corrected** count: the paper prints $\lceil\log_2(\sqrt{\gamma_2\tau tn})\rceil$, which is negative when $\gamma_2\sqrt{\tau t n}$ is small and puts $\gamma_2$ under the root, against the paper's own Lemma 14. The class $\mathcal G$ divides by $\|\|\nabla f\|_*\|_{\mathbb P_{\mathrm{true}},2}^2$; every theorem using it assumes this is positive. Mission-local duplicates of the $p=1$ objects of the sibling mission (drafts cannot import drafts).
-- source:
--   Gao, Finite-Sample Guarantees for Wasserstein Distributionally Robust Optimization: Breaking the Curse of Dimensionality, arXiv:2009.04382, Sec. 4.2 (pp. 9–11: Rademacher complexity, localized complexity, sub-root, Assumption 5, the class G, Theorem 3 and Corollary 6 radii), App. C.2.1 (p. 26: R_{⊗,p} and −F)

import Mathlib
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_WassFSG_Grad_Setting
import Definitions.Def_WassFSG_Lip_Rademacher

open MeasureTheory

namespace WassFSG.Grad

variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [MeasurableSpace Z]

/-- The family of normalized gradient norm functions
`G = { ‖∇f‖_*² / ‖‖∇f‖_*‖²_{P_true,2} : f ∈ F }` (Gao, Sec. 4.2, p. 11). Every statement using it
assumes `‖‖∇f‖_*‖_{P_true,2} > 0` for `f ∈ F`, so the division is a genuine one. -/
noncomputable def gradClass (Ptrue : Measure Z) (F : Set (Z → ℝ)) : Set (Z → ℝ) :=
  {g | ∃ f ∈ F, g = fun z => ‖fderiv ℝ f z‖ ^ 2 / gradNorm Ptrue f ^ 2}

/-- The localized class `{c f : f ∈ F, 0 ≤ c ≤ 1, T(c f) ≤ r}` with
`T(f) = ‖‖∇f‖_*‖²_{P_true,2}` (Gao, Sec. 4.2, p. 10, case `p = 2`). -/
def localized (Ptrue : Measure Z) (F : Set (Z → ℝ)) (r : ℝ) : Set (Z → ℝ) :=
  {h | ∃ f ∈ F, ∃ c : ℝ, 0 ≤ c ∧ c ≤ 1 ∧ h = c • f ∧ gradNorm Ptrue (c • f) ^ 2 ≤ r}

/-- Assumption 5 (Gao, p. 10) with `T(f) = ‖‖∇f‖_*‖²_{P_true,2}`: `ψ` is sub-root and
`ψ(r) ≥ E_⊗[𝔑_n({c f : f ∈ F, 0 ≤ c ≤ 1, T(c f) ≤ r})]` for every level `r > 0` (the page
defines the localized complexity at levels `r > 0`). -/
def SubRootLocalComplexity (Ptrue : Measure Z) (n : ℕ) (F : Set (Z → ℝ)) (ψ : ℝ → ℝ) : Prop :=
  WassFSG.Lip.IsSubRoot ψ ∧ ∀ r : ℝ, 0 < r → WassFSG.Lip.expectedRad Ptrue n (localized Ptrue F r) ≤ (ψ r : EReal)

/-- `R_{⊗,2}(ρ; G)` (Gao, App. C.2.1, p. 26, with `p = 2`; the page's `min` is read as an
infimum): `inf_{λ ≥ 0} { λρ² + E_⊗[ sup_{g ∈ G, z̃ ∈ Zⁿ} (1/n) ∑ᵢ (g(z̃ᵢ) − g(zᵢ) − λ‖z̃ᵢ − zᵢ‖²) ] }`,
in `EReal`, the expectation under the `n`-fold product `P_true^{⊗n}`. -/
noncomputable def productRegularizer (Ptrue : Measure Z) (n : ℕ) (ρ : ℝ) (G : Set (Z → ℝ)) :
    EReal :=
  ⨅ (lam : ℝ) (_ : 0 ≤ lam), (((lam * ρ ^ 2 : ℝ) : EReal) +
    ModelRiskOT.Duality.extIntegral (Measure.pi fun _ : Fin n => Ptrue)
      (fun z => ⨆ g ∈ G, ⨆ z' : Fin n → Z,
        (((1 / (n : ℝ)) * ∑ i, (g (z' i) - g (z i) - lam * ‖z' i - z i‖ ^ 2) : ℝ) : EReal)))

/-- `ε_n = (ħ τ t + 1 + E_⊗[𝔑_n(G)]) / n` (Gao, Theorem 3, p. 11), with the Rademacher complexity
`E_⊗[𝔑_n(G)]` of the normalized gradient class passed as the real number `RG`. -/
noncomputable def epsN (ħ τ t RG : ℝ) (n : ℕ) : ℝ :=
  (ħ * τ * t + 1 + RG) / n

/-- `ρ_n = 2 √(τ t / n) (1 + E_⊗[𝔑_n(G)]) + √(4 r_{n⋆} + 2 ε_n)` (Gao, Theorem 3, p. 11), with
`E_⊗[𝔑_n(G)] = RG` and `r_{n⋆} = rstar`. -/
noncomputable def rhoN (ħ τ t RG rstar : ℝ) (n : ℕ) : ℝ :=
  2 * Real.sqrt (τ * t / n) * (1 + RG) + Real.sqrt (4 * rstar + 2 * epsN ħ τ t RG n)

/-- `ρ̃_n = ρ_n (1 + 2 E_⊗[𝔑_n(G)] + κ_g² √(t / (2n)))` (Gao, Corollary 6, p. 11). -/
noncomputable def rhoTilde (ħ τ t RG rstar κg : ℝ) (n : ℕ) : ℝ :=
  rhoN ħ τ t RG rstar n * (1 + 2 * RG + κg ^ 2 * Real.sqrt (t / (2 * n)))

end WassFSG.Grad


