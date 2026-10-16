-- Prove2me | Definitions.Def_ContextualAuctions_Existence_Setting
-- name    : ContextualAuctions_Existence_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T19:28:10.159823+00:00
-- url     : https://prove2.me/theorems/5c6b28de-6a31-4f17-a246-41f450e32404
-- title:
--   §2–§3.2, pp. 4–7 — contextual budget-constrained first price auctions: Θ, A, F, G, r, ω, pacing, H^µ_α, σ^µ_α, β^µ (Definition 2), SFPE (Definition 1), q^µ
-- statement:
--   This module fixes the model of §2 and the objects of §3.1–§3.2 of Balseiro, Kroer and Kumar.
--
--   **Primitives (§2, §2.2).** An item has a **context** $\alpha\in A\subset\mathbb R^d_{+}$ (strictly positive coordinates), drawn from a law $F$ with a density, $F(A)=1$. There are $n$ buyers; each has a **type** $\theta=(w,B)$, a weight vector $w$ and a budget $B$, drawn i.i.d. from a law $G$ with a density supported on
--   $$
--   \Theta=(0,U)^d\times(B_{\min},U),\qquad U,B_{\min}>0 .
--   $$
--   The value of type $(w,B)$ for item $\alpha$ is $w^T\alpha$, and $\omega:=\sup_{(w,B)\in\Theta,\alpha\in A}w^T\alpha$. A public reserve price $r(\alpha)$ is charged; the item goes to the highest bidder at or above the reserve, who pays the bid (first price). We assume $d\ge2$.
--
--   **Pacing (§3.1).** A **pacing function** is $\mu:\Theta\to\mathbb R_{\ge0}$; the **paced value** of $(w,B)$ for $\alpha$ is $w^T\alpha/(1+\mu(w,B))$. Let $\lambda^\mu_\alpha$ be the law of the paced value when $(w,B)\sim G$, and $H^\mu_\alpha(x)=\lambda^\mu_\alpha((-\infty,x])^{n-1}$ the distribution function of the highest of $n-1$ i.i.d. paced values. For $x\ge r(\alpha)$,
--   $$
--   \sigma^\mu_\alpha(x)=x-\int_{r(\alpha)}^x\frac{H^\mu_\alpha(s)}{H^\mu_\alpha(x)}\,ds ,
--   $$
--   with $\sigma^\mu_\alpha(x)=0$ if $H^\mu_\alpha(x)=0$, and $\sigma^\mu_\alpha(x)=x$ for $x<r(\alpha)$. The **value pacing–based strategy** (Definition 2) is $\beta^\mu(w,B,\alpha)=\sigma^\mu_\alpha\big(w^T\alpha/(1+\mu(w,B))\big)$.
--
--   **The buyer's problem and SFPE (Definition 1).** Fix a strategy $\beta$ used by the $n-1$ competitors, with types $\theta_1,\dots,\theta_{n-1}\sim G$ i.i.d., independent of $\alpha\sim F$. A bid function $b:A\to\mathbb R_{\ge0}$ wins when $b(\alpha)\ge\max(r(\alpha),\{\beta(\theta_i,\alpha)\}_i)$. Type $(w,B)$ solves
--   $$
--   \max_{b}\ \mathbb E\big[(w^T\alpha-b(\alpha))\mathbb 1\{b(\alpha)\ge\max(r(\alpha),\{\beta(\theta_i,\alpha)\}_i)\}\big]\quad\text{s.t.}\quad \mathbb E\big[b(\alpha)\mathbb 1\{\cdots\}\big]\le B .
--   $$
--   A strategy $\beta^*$ is a **symmetric first price equilibrium** (SFPE) if, for $G$-almost every type $(w,B)$, $\beta^*(w,B,\cdot)$ is an optimal solution of this problem against $\beta^*$. With $\beta=\beta^\mu$ this problem is $Q^\mu(w,B)$.
--
--   **Dual function (§3.2).** For $t\ge0$,
--   $$
--   q^\mu(w,B,t)=\sup_{b}\ \mathbb E\big[(w^T\alpha-(1+t)b(\alpha))\mathbb 1\{b(\alpha)\ge\max(r(\alpha),\{\beta^\mu(\theta_i,\alpha)\}_i)\}\big]+tB,
--   $$
--   and the Lagrangian objective of Lemma 1 is $\mathbb E\big[(w^T\alpha/(1+t)-b(\alpha))\mathbb 1\{\cdots\}\big]$.
--
--   **Formalization Note** Contexts are `Fin d → ℝ`, types are pairs `(w, B)`, and $w^T\alpha$ is the explicit sum $\sum_i w_i\alpha_i$. Pacing functions are defined on all of $\mathbb R^{d}\times\mathbb R$, measurable and nonnegative on $\Theta$; their values off $\Theta$ do not matter because $G(\Theta^c)=0$. Ties win, as in the paper's tie-breaking rule that allocates the good to every highest bidder. An admissible bid function is measurable, nonnegative on $A$, and has an integrable payment integrand; the max in Definition 1, $Q^\mu$, $q^\mu$ and the Lagrangian all range over this class. An SFPE is required to be jointly measurable in $(\theta,\alpha)$. $q^\mu$ is the supremum over bids, not its closed form. The $H^\mu_\alpha(x)=0$ case of $\sigma^\mu_\alpha$ is an explicit branch, since Lean's division by zero would return $x$ instead of $0$. The `Standing` predicate collects the paper's assumptions together with four that the paper uses but does not state: $n\ge2$ (there are $n-1$ competitors), $B_{\min}<U$ (otherwise $\Theta$ is empty), $A$ nonempty and bounded (so that $\omega$ is finite), and measurability of $A$ and $r$. Measures are on the Borel $\sigma$-algebra; since $F$ and $G$ have densities, this changes no expectation.
-- source:
--   Balseiro, Kroer, Kumar, Contextual Standard Auctions with Budgets: Revenue Equivalence and Efficiency Guarantees, Management Science, Articles in Advance (2023), doi:10.1287/mnsc.2023.4719, pp. 4–7, §2, §2.2, Definition 1, §3.1, Definition 2, §3.2

import Mathlib

namespace ContextualAuctions.Existence

open MeasureTheory

/-- The primitives of §2: the context dimension `d`, the number of buyers `n`, the bounds `U`
and `B_min`, the set of item types (contexts) `A ⊆ ℝᵈ`, the law `F` of the context, the law `G`
of a buyer type `θ = (w, B) ∈ ℝᵈ × ℝ`, and the reserve price `r : ℝᵈ → ℝ`. -/
structure Model where
  d : ℕ
  n : ℕ
  U : ℝ
  Bmin : ℝ
  A : Set (Fin d → ℝ)
  F : Measure (Fin d → ℝ)
  G : Measure ((Fin d → ℝ) × ℝ)
  r : (Fin d → ℝ) → ℝ

/-- The set of buyer types `Θ = (0,U)ᵈ × (B_min, U)` (§2.2). A type is `θ = (w, B)` with
`θ.1 = w` the weight vector and `θ.2 = B` the budget. -/
def Theta (M : Model) : Set ((Fin M.d → ℝ) × ℝ) :=
  {θ | (∀ i, 0 < θ.1 i ∧ θ.1 i < M.U) ∧ M.Bmin < θ.2 ∧ θ.2 < M.U}

/-- The value `wᵀα` of buyer type `θ = (w, B)` for item `α`. -/
def val {d : ℕ} (θ : (Fin d → ℝ) × ℝ) (α : Fin d → ℝ) : ℝ :=
  ∑ i, θ.1 i * α i

/-- `ω = sup_{(w,B) ∈ Θ, α ∈ A} wᵀα`, the largest value a buyer can have for an item (§2). -/
noncomputable def omega (M : Model) : ℝ :=
  sSup {v | ∃ θ ∈ Theta M, ∃ α ∈ M.A, v = val θ α}

/-- Standing assumptions of §2–§2.2, with the disclosed additions `2 ≤ n`, `B_min < U`, and
`A` nonempty, bounded and measurable. -/
structure Model.Standing (M : Model) : Prop where
  two_le_d : 2 ≤ M.d
  two_le_n : 2 ≤ M.n
  Bmin_pos : 0 < M.Bmin
  Bmin_lt_U : M.Bmin < M.U
  U_pos : 0 < M.U
  measurableSet_A : MeasurableSet M.A
  A_pos : M.A ⊆ {α | ∀ i, 0 < α i}
  A_nonempty : M.A.Nonempty
  A_bounded : Bornology.IsBounded M.A
  probF : IsProbabilityMeasure M.F
  F_ac : M.F ≪ volume
  F_A : M.F M.Aᶜ = 0
  probG : IsProbabilityMeasure M.G
  G_ac : M.G ≪ volume
  G_Theta : M.G (Theta M)ᶜ = 0
  measurable_r : Measurable M.r

/-- A pacing function `μ : Θ → ℝ≥0` (§3.1), extended arbitrarily off `Θ`: measurable, with
nonnegative values on `Θ`. -/
def IsPacing (M : Model) (μ : (Fin M.d → ℝ) × ℝ → ℝ) : Prop :=
  Measurable μ ∧ ∀ θ ∈ Theta M, 0 ≤ μ θ

/-- The paced value `wᵀα / (1 + μ(w,B))`. -/
noncomputable def paced {d : ℕ} (μ : (Fin d → ℝ) × ℝ → ℝ) (θ : (Fin d → ℝ) × ℝ)
    (α : Fin d → ℝ) : ℝ :=
  val θ α / (1 + μ θ)

/-- `H^μ_α((−∞, x]) = λ^μ_α((−∞, x])^{n−1}`: the distribution function of the highest of `n − 1`
i.i.d. paced values, where `λ^μ_α` is the law of the paced value of a type `(w,B) ∼ G`. -/
noncomputable def H (M : Model) (μ : (Fin M.d → ℝ) × ℝ → ℝ) (α : Fin M.d → ℝ) (x : ℝ) : ℝ :=
  ((M.G {θ | paced μ θ α ≤ x}).toReal) ^ (M.n - 1)

open Classical in
/-- The bidding function `σ^μ_α` of §3.1: `σ^μ_α(x) = x` if `x < r(α)`; otherwise `0` if
`H^μ_α(x) = 0`, and `x − ∫_{r(α)}^x H^μ_α(s) ds / H^μ_α(x)` if `H^μ_α(x) ≠ 0`. -/
noncomputable def sigma (M : Model) (μ : (Fin M.d → ℝ) × ℝ → ℝ) (α : Fin M.d → ℝ) (x : ℝ) : ℝ :=
  if x < M.r α then x
  else if H M μ α x = 0 then 0
  else x - (∫ s in (M.r α)..x, H M μ α s) / H M μ α x

/-- The value pacing–based strategy (Definition 2): `β^μ(w,B,α) = σ^μ_α(wᵀα / (1 + μ(w,B)))`. -/
noncomputable def beta (M : Model) (μ : (Fin M.d → ℝ) × ℝ → ℝ) (θ : (Fin M.d → ℝ) × ℝ)
    (α : Fin M.d → ℝ) : ℝ :=
  sigma M μ α (paced μ θ α)

/-- The joint law of the context `α ∼ F` and the `n − 1` competitor types `θᵢ ∼ G`, all
independent. -/
noncomputable def P (M : Model) : Measure ((Fin M.d → ℝ) × (Fin (M.n - 1) → (Fin M.d → ℝ) × ℝ)) :=
  M.F.prod (Measure.pi fun _ : Fin (M.n - 1) => M.G)

/-- The bid `b(α)` wins against reserve `r(α)` and competitors bidding `β(θᵢ, α)`, i.e.
`b(α) ≥ max(r(α), {β(θᵢ, α)}ᵢ)` (ties win, as in Definition 1). -/
def wins (M : Model) (β : (Fin M.d → ℝ) × ℝ → (Fin M.d → ℝ) → ℝ) (b : (Fin M.d → ℝ) → ℝ)
    (ω : (Fin M.d → ℝ) × (Fin (M.n - 1) → (Fin M.d → ℝ) × ℝ)) : Prop :=
  M.r ω.1 ≤ b ω.1 ∧ ∀ i, β (ω.2 i) ω.1 ≤ b ω.1

open Classical in
/-- Expected payment `E[b(α) 1{b(α) ≥ max(r(α), {β(θᵢ,α)}ᵢ)}]` of bid function `b`. -/
noncomputable def payment (M : Model) (β : (Fin M.d → ℝ) × ℝ → (Fin M.d → ℝ) → ℝ)
    (b : (Fin M.d → ℝ) → ℝ) : ℝ :=
  ∫ ω, (if wins M β b ω then b ω.1 else 0) ∂P M

open Classical in
/-- Expected utility `E[(wᵀα − b(α)) 1{b(α) ≥ max(r(α), {β(θᵢ,α)}ᵢ)}]` of type `θ = (w,B)`. -/
noncomputable def utility (M : Model) (β : (Fin M.d → ℝ) × ℝ → (Fin M.d → ℝ) → ℝ)
    (θ : (Fin M.d → ℝ) × ℝ) (b : (Fin M.d → ℝ) → ℝ) : ℝ :=
  ∫ ω, (if wins M β b ω then val θ ω.1 - b ω.1 else 0) ∂P M

open Classical in
/-- Admissible bid functions `b : A → ℝ≥0`: measurable, nonnegative on `A`, with an integrable
payment integrand. -/
def Admissible (M : Model) (β : (Fin M.d → ℝ) × ℝ → (Fin M.d → ℝ) → ℝ)
    (b : (Fin M.d → ℝ) → ℝ) : Prop :=
  Measurable b ∧ (∀ α ∈ M.A, 0 ≤ b α) ∧
    Integrable (fun ω => if wins M β b ω then b ω.1 else 0) (P M)

/-- `b` is an optimal solution of the budget-constrained problem of type `θ = (w, B)` against
competitors using `β` (the problem of Definition 1; `Q^μ(w,B)` when `β = β^μ`). -/
def IsOptimal (M : Model) (β : (Fin M.d → ℝ) × ℝ → (Fin M.d → ℝ) → ℝ)
    (θ : (Fin M.d → ℝ) × ℝ) (b : (Fin M.d → ℝ) → ℝ) : Prop :=
  Admissible M β b ∧ payment M β b ≤ θ.2 ∧
    ∀ b', Admissible M β b' → payment M β b' ≤ θ.2 → utility M β θ b' ≤ utility M β θ b

/-- Symmetric first price equilibrium (Definition 1): a jointly measurable strategy `β` such that,
for `G`-almost every type `θ`, the bid function `β(θ, ·)` is optimal for `θ` against `β`. -/
def IsSFPE (M : Model) (β : (Fin M.d → ℝ) × ℝ → (Fin M.d → ℝ) → ℝ) : Prop :=
  Measurable (Function.uncurry β) ∧ ∀ᵐ θ ∂M.G, IsOptimal M β θ (β θ)

open Classical in
/-- The dual function of §3.2:
`q^μ(w,B,t) = sup_b E[(wᵀα − (1+t) b(α)) 1{b(α) ≥ max(r(α), {β^μ(θᵢ,α)}ᵢ)}] + tB`,
the supremum over admissible bid functions. -/
noncomputable def qDual (M : Model) (μ : (Fin M.d → ℝ) × ℝ → ℝ) (θ : (Fin M.d → ℝ) × ℝ)
    (t : ℝ) : ℝ :=
  sSup {v | ∃ b, Admissible M (beta M μ) b ∧
    v = ∫ ω, (if wins M (beta M μ) b ω then val θ ω.1 - (1 + t) * b ω.1 else 0) ∂P M}
  + t * θ.2

open Classical in
/-- The Lagrangian objective of Lemma 1:
`E[(wᵀα/(1+t) − b(α)) 1{b(α) ≥ max(r(α), {β^μ(θᵢ,α)}ᵢ)}]`. -/
noncomputable def lagr (M : Model) (μ : (Fin M.d → ℝ) × ℝ → ℝ) (θ : (Fin M.d → ℝ) × ℝ)
    (t : ℝ) (b : (Fin M.d → ℝ) → ℝ) : ℝ :=
  ∫ ω, (if wins M (beta M μ) b ω then val θ ω.1 / (1 + t) - b ω.1 else 0) ∂P M

end ContextualAuctions.Existence


