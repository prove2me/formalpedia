-- Prove2me | Definitions.Def_WassFSG_Lip_Rademacher
-- name    : WassFSG_Lip_Rademacher
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T10:38:50.951991+00:00
-- url     : https://prove2.me/theorems/bc0f2335-82c5-4902-a2e7-8087a3d46e07
-- title:
--   Sec. 4.2, App. C.2.1 — Rademacher complexity 𝔑_n, localized class, sub-root functions, Assumption 5, R_{⊗,1}, the peeling count N₁
-- statement:
--   Let $\mathcal Z$ be as in `WassFSG.Lip.Setting`, let $\mathbb P_{\mathrm{true}}$ be a probability measure on $\mathcal Z$, and let $n \ge 1$. Write $\mathbb E_\otimes$ for the expectation under the $n$-fold product $\mathbb P_{\mathrm{true}}^{\otimes n}$ of a sample $z = (z_1,\dots,z_n)$.
--
--   1. **Rademacher complexity.** For a class $\mathcal G$ of real functions on $\mathcal Z$,
--   $$
--   \mathfrak R_n(\mathcal G) = \mathbb E_{\sigma}\Big[\sup_{g\in\mathcal G}\frac1n\sum_{i=1}^n \sigma_i\, g(z_i)\Big],
--   $$
--   where $\sigma_1,\dots,\sigma_n$ are i.i.d. signs with $\mathbb P\{\sigma_i = \pm1\} = \tfrac12$; the expectation over $\sigma$ is the average over the $2^n$ sign vectors. The Rademacher complexity of $\mathcal G$ with respect to $\mathbb P_{\mathrm{true}}$ is $\mathbb E_\otimes[\mathfrak R_n(\mathcal G)]$.
--   2. **Localized class.** For $\mathcal F$ and a level $r \ge 0$, $\{cf : f\in\mathcal F,\ 0\le c\le1,\ \|cf\|_{\mathrm{Lip}}^2 \le r\}$, i.e. $T(cf)\le r$ with $T(f) = \|f\|^2_{\mathrm{Lip}}$.
--   3. **Sub-root function.** $\psi:\mathbb R_+\to\mathbb R_+$ is sub-root if it is non-constant, non-negative and non-decreasing, and $r\mapsto\psi(r)/\sqrt r$ is non-increasing on $(0,\infty)$.
--   4. **Assumption 5.** $\psi$ is sub-root and, for every level $r>0$,
--   $$
--   \psi(r) \ge \mathbb E_\otimes\Big[\mathfrak R_n\big(\{cf : f\in\mathcal F,\ 0\le c\le 1,\ \|cf\|^2_{\mathrm{Lip}}\le r\}\big)\Big].
--   $$
--   5. **The class $-\mathcal F$** is $\{-f : f\in\mathcal F\}$.
--   6. **The product regularizer.** For a radius $\rho$ and a class $\mathcal G$,
--   $$
--   \mathcal R_{\otimes,1}(\rho;\mathcal G) = \inf_{\lambda\ge0}\Big\{\lambda\rho + \mathbb E_\otimes\Big[\sup_{g\in\mathcal G,\ \tilde z\in\mathcal Z^n}\frac1n\sum_{i=1}^n\big(g(\tilde z_i) - g(z_i) - \lambda\|\tilde z_i - z_i\|\big)\Big]\Big\}.
--   $$
--   7. **The peeling count.** $N_1(t,n) = \max\big(0, \lceil \log_2(\gamma_1\sqrt{\tau t n})\rceil\big) + 1$.
--
--   These are the complexity objects of the paper's local Rademacher analysis for $p = 1$.
--
--   **Formalization Note** Signs are Booleans (`true ↦ 1`, `false ↦ −1`). Suprema over classes are taken in the extended reals (an empty class gives $-\infty$), and the expectations $\mathbb E_\otimes$ are the extended integrals $\int\varphi^+ - \int\varphi^-$ of `ModelRiskOT.Duality.extIntegral` under `Measure.pi`. The page writes $\min_{\lambda\ge0}$ in $\mathcal R_{\otimes,p}$; the minimum need not be attained, so the definition takes the infimum. The page's printed count in Lemma 12, Theorem 2 and Corollary 4 is $\lceil\log_2(\sqrt{\gamma_1\tau t n})\rceil$, which is negative for small $\gamma_1\sqrt{\tau t n}$ and does not match the proof's peeling; $N_1$ is the corrected count (see the theorems' notes). A sub-root function is a function on $\mathbb R$ whose properties are required on $[0,\infty)$ only. The localized complexity is defined on the page at levels $r>0$, so Assumption 5's domination is required for $r>0$; the localized class uses the Lipschitz norm `WassFSG.Conc.lipNorm`.
-- source:
--   Gao, Finite-Sample Guarantees for Wasserstein Distributionally Robust Optimization: Breaking the Curse of Dimensionality, arXiv:2009.04382, Sec. 4.2 (pp. 9–10: Rademacher complexity, localized Rademacher complexity, sub-root functions, Assumption 5), App. C.2.1 (p. 26: R_{⊗,p} and −F), proof of Lemma 12 (p. 27: K)

import Mathlib
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_WassFSG_Lip_Setting

open MeasureTheory

namespace WassFSG.Lip

variable {Z : Type*} [NormedAddCommGroup Z] [MeasurableSpace Z]

/-- The value `±1` of a Rademacher sign, encoded by a Boolean: `true ↦ 1`, `false ↦ −1`. -/
def signVal (b : Bool) : ℝ := if b then 1 else -1

/-- The empirical Rademacher complexity `𝔑_n(G) = E_σ[ sup_{g ∈ G} (1/n) ∑ᵢ σᵢ g(zᵢ) ]`
(Gao, Sec. 4.2, p. 9) of a class `G` on the sample `z = (z₁, …, zₙ)`: the average over the `2ⁿ`
equally likely sign vectors `σ ∈ {±1}ⁿ`, with factor `1/n` and no absolute value. The supremum is
taken in `EReal` (it may be `+∞`; it is `−∞` for the empty class). -/
noncomputable def radComp {n : ℕ} (G : Set (Z → ℝ)) (z : Fin n → Z) : EReal :=
  ((1 / 2 ^ n : ℝ) : EReal) * ∑ σ : Fin n → Bool,
    ⨆ g ∈ G, (((1 / (n : ℝ)) * ∑ i, signVal (σ i) * g (z i) : ℝ) : EReal)

/-- The Rademacher complexity of `G` with respect to `P_true` for sample size `n`:
`E_⊗[𝔑_n(G)]`, the expectation of `𝔑_n(G)` under the `n`-fold product `P_true^{⊗n}` (Gao,
Sec. 4.2, p. 10), as an extended integral `∫ φ⁺ − ∫ φ⁻` in `EReal`. -/
noncomputable def expectedRad (Ptrue : Measure Z) (n : ℕ) (G : Set (Z → ℝ)) : EReal :=
  ModelRiskOT.Duality.extIntegral (Measure.pi fun _ : Fin n => Ptrue) (radComp G)

/-- The localized class `{c f : f ∈ F, 0 ≤ c ≤ 1, T(c f) ≤ r}` with `T(f) = ‖f‖²_Lip`
(Gao, Sec. 4.2, p. 10, case `p = 1`). -/
def localized (F : Set (Z → ℝ)) (r : ℝ) : Set (Z → ℝ) :=
  {h | ∃ f ∈ F, ∃ c : ℝ, 0 ≤ c ∧ c ≤ 1 ∧ h = c • f ∧ WassFSG.Conc.lipNorm (c • f) ^ 2 ≤ r}

/-- A sub-root function `ψ : ℝ₊ → ℝ₊` (Gao, Sec. 4.2, p. 10): on `[0, ∞)` it is non-negative,
non-decreasing and non-constant, and `r ↦ ψ(r)/√r` is non-increasing on `(0, ∞)`. Values of `ψ`
at negative arguments are irrelevant. -/
def IsSubRoot (ψ : ℝ → ℝ) : Prop :=
  (∀ r, 0 ≤ r → 0 ≤ ψ r) ∧ MonotoneOn ψ (Set.Ici 0) ∧
    AntitoneOn (fun r => ψ r / Real.sqrt r) (Set.Ioi 0) ∧
    ∃ r₁ r₂ : ℝ, 0 ≤ r₁ ∧ 0 ≤ r₂ ∧ ψ r₁ ≠ ψ r₂

/-- Assumption 5 (Gao, p. 10) with `T(f) = ‖f‖²_Lip`: `ψ` is sub-root and
`ψ(r) ≥ E_⊗[𝔑_n({c f : f ∈ F, 0 ≤ c ≤ 1, T(c f) ≤ r})]` for every level `r > 0` (the page
defines the localized complexity at levels `r > 0`). -/
def SubRootLocalComplexity (Ptrue : Measure Z) (n : ℕ) (F : Set (Z → ℝ)) (ψ : ℝ → ℝ) : Prop :=
  IsSubRoot ψ ∧ ∀ r : ℝ, 0 < r → expectedRad Ptrue n (localized F r) ≤ (ψ r : EReal)

/-- The class `−F = {−f : f ∈ F}` (Gao, App. C.2.1, p. 26). -/
def negClass (F : Set (Z → ℝ)) : Set (Z → ℝ) :=
  {g | ∃ f ∈ F, g = -f}

/-- `R_{⊗,1}(ρ; G)` (Gao, App. C.2.1, p. 26, with `p = 1`; the page's `min` is read as an infimum):
`inf_{λ ≥ 0} { λρ + E_⊗[ sup_{g ∈ G, z̃ ∈ Zⁿ} (1/n) ∑ᵢ (g(z̃ᵢ) − g(zᵢ) − λ‖z̃ᵢ − zᵢ‖) ] }`,
in `EReal`, the expectation under the `n`-fold product `P_true^{⊗n}`. -/
noncomputable def productRegularizer (Ptrue : Measure Z) (n : ℕ) (ρ : ℝ) (G : Set (Z → ℝ)) :
    EReal :=
  ⨅ (lam : ℝ) (_ : 0 ≤ lam), (((lam * ρ : ℝ) : EReal) +
    ModelRiskOT.Duality.extIntegral (Measure.pi fun _ : Fin n => Ptrue)
      (fun z => ⨆ g ∈ G, ⨆ z' : Fin n → Z,
        (((1 / (n : ℝ)) * ∑ i, (g (z' i) - g (z i) - lam * ‖z' i - z i‖) : ℝ) : EReal)))

/-- The corrected number of peeling events `N₁(t, n) = max(0, ⌈log₂(γ₁ √(τ t n))⌉) + 1` in the
failure probability of Lemma 12, Theorem 2 and Corollary 4 (the printed count is
`⌈log₂(√(γ₁ τ t n))⌉`, which can be negative). -/
noncomputable def peelCount (γ₁ τ t : ℝ) (n : ℕ) : ℕ :=
  (max 0 ⌈Real.logb 2 (γ₁ * Real.sqrt (τ * t * n))⌉).toNat + 1

end WassFSG.Lip


