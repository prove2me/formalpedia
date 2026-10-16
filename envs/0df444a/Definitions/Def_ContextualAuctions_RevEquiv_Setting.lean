-- Prove2me | Definitions.Def_ContextualAuctions_RevEquiv_Setting
-- name    : ContextualAuctions_RevEquiv_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T19:28:08.481601+00:00
-- url     : https://prove2.me/theorems/9eafa007-5d70-4aa1-85ec-dcb8d83ce2f7
-- title:
--   §2–§3.2 — contextual budget-constrained first price auctions: Θ, A, F, G, r, ω, pacing, H^µ_α, σ^µ_α, β^µ (Definition 2), admissible bids, the dual function q^µ
-- statement:
--   This file fixes the model of §2 and the first-price objects of §3.1–§3.2.
--
--   **Primitives.** An instance consists of a feature dimension $d$, a number of buyers $n$, constants $U$ and $B_{\min}$, a set of item types (contexts) $A\subset\mathbb R^d$, a law $F$ of the context, a law $G$ of a buyer type, and a reserve price $r:\mathbb R^d\to\mathbb R$. A buyer type is $\theta=(w,B)$ with weights $w\in\mathbb R^d$ and budget $B$, and its value for item $\alpha$ is $w^T\alpha=\sum_i w_i\alpha_i$. The type set is $\Theta=(0,U)^d\times(B_{\min},U)$ and $\omega=\sup\{w^T\alpha : (w,B)\in\Theta,\ \alpha\in A\}$ is the supremal possible value.
--
--   **Standing assumptions** (§2, §2.2): $d\ge2$; $n\ge2$; $0<B_{\min}<U$; $A$ is a measurable, nonempty, bounded subset of the open positive orthant; $F$ and $G$ are probability measures with densities, concentrated on $A$ and $\Theta$ respectively; $r$ is measurable.
--
--   **Pacing.** A pacing function is a measurable $\mu$ with $\mu(w,B)\ge0$ on $\Theta$. The paced value is $w^T\alpha/(1+\mu(w,B))$, and
--   $$H^\mu_\alpha(x)=\lambda^\mu_\alpha((-\infty,x])^{n-1}=G\Big(\Big\{(w,B):\tfrac{w^T\alpha}{1+\mu(w,B)}\le x\Big\}\Big)^{n-1}$$
--   is the c.d.f. of the highest of $n-1$ i.i.d. paced values. The first-price bid is
--   $$\sigma^\mu_\alpha(x)=\begin{cases}x, & x<r(\alpha),\\ 0, & x\ge r(\alpha),\ H^\mu_\alpha(x)=0,\\ x-\displaystyle\int_{r(\alpha)}^{x}\frac{H^\mu_\alpha(s)}{H^\mu_\alpha(x)}\,ds, & \text{otherwise,}\end{cases}$$
--   and the value pacing–based strategy (Definition 2) is $\beta^\mu(w,B,\alpha)=\sigma^\mu_\alpha\big(w^T\alpha/(1+\mu(w,B))\big)$.
--
--   **The buyer's problem.** Contexts and the $n-1$ competitor types $\theta_1,\dots,\theta_{n-1}$ are drawn independently from $F\otimes G^{\otimes(n-1)}$. A bid $b(\alpha)$ wins against competitors using a strategy $\beta$ when $b(\alpha)\ge\max(r(\alpha),\{\beta(\theta_i,\alpha)\}_i)$ (ties win). A bid function $b$ is admissible if it is measurable, nonnegative on every context in $A$, and its first-price payment $b(\alpha)\mathbb 1\{\text{win}\}$ is integrable. The dual function is the supremum of the Lagrangian over admissible bids,
--   $$q^\mu(w,B,t)=\sup_{b}\ \mathbb E_{\alpha,\{\theta_i\}_{i=1}^{n-1}}\Big[(w^T\alpha-(1+t)b(\alpha))\,\mathbb 1\{b(\alpha)\ge\max(r(\alpha),\{\beta^\mu(\theta_i,\alpha)\}_i)\}\Big]+tB .$$
--
--   These objects are shared by every statement of the mission: the dual function $q^\mu$ is the first-price benchmark against which every standard auction is compared.
--
--   **Formalization Note** The additions $n\ge2$, $B_{\min}<U$ and $A$ bounded and nonempty are implicit in the paper ($H^\mu_\alpha$ needs a competitor, $\Theta$ must be nonempty, $\omega$ must be finite). The special case $H^\mu_\alpha(x)=0$ is an explicit branch, because Lean's division by zero would otherwise return $x$. The dual function is defined as the supremum of p. 7, never by its closed form, which is a theorem of the mission. Bids are functions on all of $\mathbb R^d$ with the paper's nonnegativity condition imposed on $A$; values off $A$ do not enter the expectations.
-- source:
--   Balseiro, Kroer, Kumar, Contextual Standard Auctions with Budgets: Revenue Equivalence and Efficiency Guarantees, Management Science, Articles in Advance (2023), doi:10.1287/mnsc.2023.4719, pp. 4–7, §2, §2.2, Definition 1, §3.1 (Definition 2), §3.2 (dual function q^µ, p. 7)

import Mathlib

namespace ContextualAuctions.RevEquiv

open MeasureTheory

open Classical

noncomputable section
open scoped BigOperators

/-- The primitives of §2: feature dimension `d`, number of buyers `n`, the constants `U` and
`Bmin`, the item-type set `A`, the context law `F`, the buyer-type law `G`, the reserve price `r`. -/
structure Model where
  d : ℕ
  n : ℕ
  U : ℝ
  Bmin : ℝ
  A : Set (Fin d → ℝ)
  F : Measure (Fin d → ℝ)
  G : Measure ((Fin d → ℝ) × ℝ)
  r : (Fin d → ℝ) → ℝ

/-- A buyer type `θ = (w, B)`: weights `θ.1 = w` and budget `θ.2 = B`. -/
abbrev Buyer (M : Model) := (Fin M.d → ℝ) × ℝ
/-- An item type (context) `α`. -/
abbrev Context (M : Model) := Fin M.d → ℝ

/-- The value `w^T α` of buyer type `θ = (w, B)` for item `α`. -/
def val (M : Model) (θ : Buyer M) (α : Context M) : ℝ :=
  ∑ i, θ.1 i * α i

/-- The type set `Θ = (0,U)^d × (Bmin, U)` of §2.2. -/
def Theta (M : Model) : Set (Buyer M) :=
  {θ | (∀ i, 0 < θ.1 i ∧ θ.1 i < M.U) ∧ M.Bmin < θ.2 ∧ θ.2 < M.U}

/-- The maximum value `ω`, a supremum since `Θ` is open. -/
def omega (M : Model) : ℝ :=
  sSup {v : ℝ | ∃ θ ∈ Theta M, ∃ α ∈ M.A, v = val M θ α}

/-- The standing assumptions of §2 and §2.2, with the disclosed additions `2 ≤ n`,
`Bmin < U`, and `A` measurable, nonempty and bounded. -/
structure Model.Standing (M : Model) : Prop where
  dim : 2 ≤ M.d
  buyers : 2 ≤ M.n
  budget_pos : 0 < M.Bmin
  budget_lt : M.Bmin < M.U
  measurableA : MeasurableSet M.A
  positiveA : M.A ⊆ {α | ∀ i, 0 < α i}
  nonemptyA : M.A.Nonempty
  boundedA : Bornology.IsBounded M.A
  probF : IsProbabilityMeasure M.F
  densityF : M.F ≪ volume
  supportedF : M.F M.Aᶜ = 0
  probG : IsProbabilityMeasure M.G
  densityG : M.G ≪ volume
  supportedG : M.G (Theta M)ᶜ = 0
  measurableR : Measurable M.r

/-- A pacing function `μ : Θ → ℝ≥0`: measurable, nonnegative on `Θ`. -/
def IsPacing (M : Model) (μ : Buyer M → ℝ) : Prop :=
  Measurable μ ∧ ∀ θ ∈ Theta M, 0 ≤ μ θ

/-- The paced value `w^T α / (1 + μ(w, B))`. -/
def paced (M : Model) (μ : Buyer M → ℝ) (θ : Buyer M) (α : Context M) : ℝ :=
  val M θ α / (1 + μ θ)

/-- `H^μ_α(x) = λ^μ_α((-∞, x])^{n-1}`, the c.d.f. of the highest of `n - 1` i.i.d. paced values. -/
def H (M : Model) (μ : Buyer M → ℝ) (α : Context M) (x : ℝ) : ℝ :=
  ((M.G {θ | paced M μ θ α ≤ x}).toReal) ^ (M.n - 1)

/-- The first-price bidding function `σ^μ_α` of §3.1, with both special cases. -/
def sigma (M : Model) (μ : Buyer M → ℝ) (α : Context M) (x : ℝ) : ℝ :=
  if x < M.r α then x else if H M μ α x = 0 then 0 else
    x - (∫ s in (M.r α)..x, H M μ α s) / H M μ α x

/-- The value pacing-based strategy `β^μ` of Definition 2. -/
def beta (M : Model) (μ : Buyer M → ℝ) (θ : Buyer M) (α : Context M) : ℝ :=
  sigma M μ α (paced M μ θ α)

/-- The joint law of the context and the `n - 1` competitor types. -/
def P (M : Model) : Measure (Context M × (Fin (M.n - 1) → Buyer M)) :=
  M.F.prod (Measure.pi fun _ : Fin (M.n - 1) => M.G)

/-- The bid `b(α)` wins against competitors using `β`: it meets the reserve and every competing
bid (ties win). -/
def wins (M : Model) (β : Buyer M → Context M → ℝ) (b : Context M → ℝ)
    (ω : Context M × (Fin (M.n - 1) → Buyer M)) : Prop :=
  M.r ω.1 ≤ b ω.1 ∧ ∀ i, β (ω.2 i) ω.1 ≤ b ω.1

/-- An admissible first-price bid `b : A → ℝ≥0`: measurable, nonnegative on `A`,
with an integrable payment. -/
def Admissible (M : Model) (β : Buyer M → Context M → ℝ) (b : Context M → ℝ) : Prop :=
  Measurable b ∧ (∀ α ∈ M.A, 0 ≤ b α) ∧
    Integrable (fun ω : Context M × (Fin (M.n - 1) → Buyer M) =>
      if wins M β b ω then b ω.1 else 0) (P M)

/-- The first-price dual function `q^μ(w, B, t)` of §3.2 (p. 7, first line): a supremum over
admissible bids of the Lagrangian, plus `t B`. -/
def qDual (M : Model) (μ : Buyer M → ℝ) (θ : Buyer M) (t : ℝ) : ℝ :=
  sSup {v : ℝ | ∃ b : Context M → ℝ, Admissible M (beta M μ) b ∧
    v = ∫ ω, (if wins M (beta M μ) b ω then
      val M θ ω.1 - (1 + t) * b ω.1 else 0) ∂P M} + t * θ.2

end

end ContextualAuctions.RevEquiv


