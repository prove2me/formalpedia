-- Prove2me | Definitions.Def_MinimaxATE_Learnability_FatDims
-- name    : MinimaxATE_Learnability_FatDims
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T05:00:35.381398+00:00
-- url     : https://prove2.me/theorems/ac3b20f0-c18d-4d13-b200-dd6ebc2cc9fa
-- title:
--   Projected classes, mutual, symmetric and approximately symmetric fat-shattering, and $N_{\mathrm{DR}}$ (Definitions 5–7)
-- statement:
--   Let $\mathcal P,\mathcal M$ be classes of real functions on $\mathcal X$ and $\lambda\in\{-1,+1\}^k$ a labeling. Throughout, $\mathrm{fat}_\gamma$ is the fat-shattering dimension of Definition 3 (the published definition `BartlettNN_Margin_FatShattering`).
--
--   **Projected class.** For points $x_1,\dots,x_n$ and an index set $I$, $H[x_I]=\{i\mapsto h(x_i):h\in H\}$, a class of functions on $I$.
--
--   **Definition 5.** For $\kappa,\gamma>0$, points $x_1,\dots,x_k$ are **mutually $(\kappa,\gamma)$-fat-shattered** by $(\mathcal P,\mathcal M)$ if there are thresholds $a_i,r_i$ such that for every labeling $\lambda$ there are $p^{(\lambda)}\in\mathcal P$, $m^{(\lambda)}\in\mathcal M$ with
--   $$\lambda_i\,(p^{(\lambda)}(x_i)-a_i)\ge\kappa\quad\text{and}\quad\lambda_i\,(m^{(\lambda)}(x_i)-r_i)\ge\gamma\qquad\text{for all }i.$$
--   $\mathrm{fat}^{\mathrm{mut}}_{\kappa,\gamma}(\mathcal P,\mathcal M)$ is the largest such $k$ (over distinct points), $\infty$ if unbounded.
--
--   **Definition 6.** Points are **symmetrically** mutually $(\kappa,\gamma)$-fat-shattered if there are thresholds $a_i,r_i$ and gaps $d_i\ge\kappa$, $e_i\ge\gamma$ such that every $\lambda$ has $p^{(\lambda)}\in\mathcal P$, $m^{(\lambda)}\in\mathcal M$ with $p^{(\lambda)}(x_i)=a_i+\lambda_i d_i$ and $m^{(\lambda)}(x_i)=r_i+\lambda_i e_i$; the largest such $k$ is $\mathrm{fat}^{\mathrm{sym\text{-}mut}}_{\kappa,\gamma}(\mathcal P,\mathcal M)$.
--
--   **Definition 7.** For $\alpha,\beta\ge0$, the $(\alpha,\beta)$-**approximately symmetric** version asks instead $|p^{(\lambda)}(x_i)-(a_i+\lambda_i d_i)|\le\alpha$ and $|m^{(\lambda)}(x_i)-(r_i+\lambda_i e_i)|\le\beta$; the largest such $k$ is $(\alpha,\beta)\text{-}\mathrm{fat}^{\mathrm{sym\text{-}mut}}_{\kappa,\gamma}(\mathcal P,\mathcal M)$.
--
--   **Doubly robust sample complexity** (p. 8):
--   $$N_{\mathrm{DR}}(\varepsilon,c,\mathcal P,\mathcal M)=\inf_{\substack{0<\varepsilon_1,\varepsilon_2\le1\\ \varepsilon_1\varepsilon_2\le\varepsilon}}\Big\{\frac{\mathrm{fat}_{c\varepsilon_1}(\mathcal P)}{\varepsilon_1^2}+\frac{\mathrm{fat}_{c\varepsilon_2}(\mathcal M)}{\varepsilon_2^2}\Big\}\in[0,\infty].$$
--
--   **Formalization Note.** Labelings are `Bool`-valued and read through `pm` ($\pm1$) of `BartlettNN_Margin_Classification`. Points are sequences `Fin k → X`; the three dimensions count injective sequences ("$k$ points"); for Definitions 5 and 6 at positive scales a repeated point can never be shattered, so this changes nothing there. Dimensions are `ℕ∞` suprema (`⊤` when unbounded, `0` for empty classes); $N_{\mathrm{DR}}$ is an `ℝ≥0∞` infimum with `ℕ∞` dimensions cast to `ℝ≥0∞`.
-- source:
--   Cai, Kalavasis, Mamali, Mehrotra, Zampetakis, Minimax Rates for Estimation of Average Treatment Effects in Observational Studies, STOC 2027 submission (manuscript sha256 89998c39…), p. 11 (PDF 13), Definition 5; p. 14 (PDF 16), Definition 6; p. 15 (PDF 17), Definition 7; p. 19 (PDF 21), H[X_I]; p. 8 (PDF 10), N_DR

import Mathlib
import Definitions.Def_BartlettNN_Margin_FatShattering

namespace MinimaxATE.Learnability

open BartlettNN.Margin

/-- The projected class `H[x] = {i ↦ h(x_i) : h ∈ H}` on an index type `ι` (§3, p. 19); for a
sample `X_1, …, X_n` and `R ⊆ [n]`, `H[X_R]` is `proj H (fun i : R => X i)`. -/
def proj {X ι : Type*} (H : Set (X → ℝ)) (x : ι → X) : Set (ι → ℝ) :=
  (fun h => h ∘ x) '' H

/-- Points `x_i` are mutually `(κ, γ)`-fat-shattered by `(P, M)` (Definition 5, p. 11): there are
propensity thresholds `a_i` and outcome thresholds `r_i` such that for every labeling
`λ ∈ {−1, +1}^ι` (encoded by `Bool`, read through `pm`) some `p ∈ P` and `m ∈ M` satisfy
`λ_i (p(x_i) − a_i) ≥ κ` and `λ_i (m(x_i) − r_i) ≥ γ` for all `i`. -/
def MutShatters {X ι : Type*} (P M : Set (X → ℝ)) (κ γ : ℝ) (x : ι → X) : Prop :=
  ∃ a r : ι → ℝ, ∀ b : ι → Bool, ∃ p ∈ P, ∃ m ∈ M, ∀ i,
    κ ≤ pm (b i) * (p (x i) - a i) ∧ γ ≤ pm (b i) * (m (x i) - r i)

/-- The mutual fat-shattering dimension `fat^mut_{κ,γ}(P, M)` (Definition 5, p. 11): the largest
number of distinct points mutually `(κ, γ)`-fat-shattered by `(P, M)`, `⊤` if unbounded. -/
noncomputable def mutFat {X : Type*} (P M : Set (X → ℝ)) (κ γ : ℝ) : ℕ∞ :=
  ⨆ (k : ℕ) (x : Fin k → X) (_ : Function.Injective x ∧ MutShatters P M κ γ x), (k : ℕ∞)

/-- Points `x_i` are `(α, β)`-approximately symmetrically mutually `(κ, γ)`-fat-shattered
(Definition 7, p. 15): there are thresholds `a_i, r_i` and gaps `d_i ≥ κ`, `e_i ≥ γ` such that for
every labeling `λ` some `p ∈ P`, `m ∈ M` satisfy `|p(x_i) − (a_i + λ_i d_i)| ≤ α` and
`|m(x_i) − (r_i + λ_i e_i)| ≤ β` for all `i`. With `α = β = 0` this is Definition 6. -/
def ApproxSymShatters {X ι : Type*} (P M : Set (X → ℝ)) (κ γ α β : ℝ) (x : ι → X) : Prop :=
  ∃ a r d e : ι → ℝ, (∀ i, κ ≤ d i ∧ γ ≤ e i) ∧ ∀ b : ι → Bool, ∃ p ∈ P, ∃ m ∈ M, ∀ i,
    |p (x i) - (a i + pm (b i) * d i)| ≤ α ∧ |m (x i) - (r i + pm (b i) * e i)| ≤ β

/-- Points `x_i` are symmetrically mutually `(κ, γ)`-fat-shattered (Definition 6, p. 14): there are
thresholds `a_i, r_i` and gaps `d_i ≥ κ`, `e_i ≥ γ` such that for every labeling `λ` some `p ∈ P`,
`m ∈ M` satisfy `p(x_i) = a_i + λ_i d_i` and `m(x_i) = r_i + λ_i e_i` for all `i`. -/
def SymShatters {X ι : Type*} (P M : Set (X → ℝ)) (κ γ : ℝ) (x : ι → X) : Prop :=
  ∃ a r d e : ι → ℝ, (∀ i, κ ≤ d i ∧ γ ≤ e i) ∧ ∀ b : ι → Bool, ∃ p ∈ P, ∃ m ∈ M, ∀ i,
    p (x i) = a i + pm (b i) * d i ∧ m (x i) = r i + pm (b i) * e i

/-- The symmetric mutual fat-shattering dimension `fat^{sym-mut}_{κ,γ}(P, M)` (Definition 6). -/
noncomputable def symFat {X : Type*} (P M : Set (X → ℝ)) (κ γ : ℝ) : ℕ∞ :=
  ⨆ (k : ℕ) (x : Fin k → X) (_ : Function.Injective x ∧ SymShatters P M κ γ x), (k : ℕ∞)

/-- The `(α, β)`-approximately symmetric mutual fat-shattering dimension
`(α, β)-fat^{sym-mut}_{κ,γ}(P, M)` (Definition 7). -/
noncomputable def approxSymFat {X : Type*} (P M : Set (X → ℝ)) (κ γ α β : ℝ) : ℕ∞ :=
  ⨆ (k : ℕ) (x : Fin k → X) (_ : Function.Injective x ∧ ApproxSymShatters P M κ γ α β x),
    (k : ℕ∞)

/-- The doubly robust sample complexity (p. 8):
`N_DR(ε, c, P, M) = inf_{0 < ε₁, ε₂ ≤ 1, ε₁ε₂ ≤ ε} fat_{cε₁}(P)/ε₁² + fat_{cε₂}(M)/ε₂²`, in `[0, ∞]`. -/
noncomputable def NDR {X : Type*} (ε c : ℝ) (P M : Set (X → ℝ)) : ENNReal :=
  ⨅ (ε₁ : ℝ) (ε₂ : ℝ) (_ : 0 < ε₁ ∧ ε₁ ≤ 1 ∧ 0 < ε₂ ∧ ε₂ ≤ 1 ∧ ε₁ * ε₂ ≤ ε),
    ((fat P (c * ε₁) : ENNReal) / ENNReal.ofReal (ε₁ ^ 2) +
      (fat M (c * ε₂) : ENNReal) / ENNReal.ofReal (ε₂ ^ 2))

end MinimaxATE.Learnability


