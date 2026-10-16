-- Prove2me | Definitions.Def_ContextualAuctions_PoA_Setting
-- name    : ContextualAuctions_PoA_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T19:28:07.806124+00:00
-- url     : https://prove2.me/theorems/367b78b9-17f2-45d8-8463-3688929b7b5a
-- title:
--   §2–§3.2 — contextual first-price auction model, pacing strategy, and buyer dual
-- statement:
--   A **contextual first-price auction** has $n$ buyers and a context $\alpha\in A\subset\mathbb R^d$. A buyer has a private weight vector $w\in(0,U)^d$ and budget $B\in(B_{\min},U)$, with value $w^\top\alpha$. Contexts have law $F$ and independent buyer types have law $G$. The reserve is $r(\alpha)$, and $\omega$ is the supremum of possible values.
--
--   A **pacing function** $\mu$ scales the buyer's value to $w^\top\alpha/(1+\mu(w,B))$. The largest of $n-1$ independently drawn paced competitor values has distribution function $H^\mu_\alpha$. The bid function $\sigma^\mu_\alpha$ equals $x$ below the reserve, equals zero when $H^\mu_\alpha(x)=0$ at or above the reserve, and otherwise equals
--   $$
--   \sigma^\mu_\alpha(x)=x-\frac{\int_{r(\alpha)}^x H^\mu_\alpha(s)\,ds}{H^\mu_\alpha(x)}.
--   $$
--   The **value pacing-based bid** is $\beta^\mu(w,B,\alpha)=\sigma^\mu_\alpha(w^\top\alpha/(1+\mu(w,B)))$.
--
--   The module also specifies the first-price buyer problem, expected payment and utility, and its **dual function** $q^\mu(w,B,t)$ as the supremum of the Lagrangian over admissible bids. These definitions are the model layer used by the efficiency mission.
--
--   **Formalization Note** The bounded nonempty context set, $n\ge2$, $0<B_{\min}<U$, and measurability and integrability conditions make the paper's implicit domain requirements explicit. The paper's utility problem lets all highest bidders win when bids tie; its tie convention is used here for this buyer problem. The dual is defined by its bid supremum, not by its later closed form.
-- source:
--   Balseiro, Kroer, Kumar, Contextual Standard Auctions with Budgets: Revenue Equivalence and Efficiency Guarantees, Management Science, Articles in Advance (2023), doi:10.1287/mnsc.2023.4719, pp. 4–8, §2, Definitions 1–2, §3.1–§3.2

import Mathlib

namespace ContextualAuctions.PoA

open MeasureTheory

open Classical

noncomputable section
open scoped BigOperators

/-- The contextual first-price auction primitives from §2. -/
structure Model where
  d : ℕ
  n : ℕ
  U : ℝ
  Bmin : ℝ
  A : Set (Fin d → ℝ)
  F : Measure (Fin d → ℝ)
  G : Measure ((Fin d → ℝ) × ℝ)
  r : (Fin d → ℝ) → ℝ

abbrev Buyer (M : Model) := (Fin M.d → ℝ) × ℝ
abbrev Context (M : Model) := Fin M.d → ℝ

/-- The buyer's value for a context. -/
def val (M : Model) (θ : Buyer M) (α : Context M) : ℝ :=
  ∑ i, θ.1 i * α i

/-- The open type rectangle in §2.2. -/
def Theta (M : Model) : Set (Buyer M) :=
  {θ | (∀ i, 0 < θ.1 i ∧ θ.1 i < M.U) ∧ M.Bmin < θ.2 ∧ θ.2 < M.U}

/-- The maximum possible value, written as a supremum because Θ is open. -/
noncomputable def omega (M : Model) : ℝ :=
  sSup {v : ℝ | ∃ θ ∈ Theta M, ∃ α ∈ M.A, v = val M θ α}

/-- Assumptions of §2 and §2.2, with the disclosed boundedness and nonempty hypotheses. -/
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

/-- A measurable nonnegative pacing multiplier on the type space. -/
def IsPacing (M : Model) (μ : Buyer M → ℝ) : Prop :=
  Measurable μ ∧ ∀ θ ∈ Theta M, 0 ≤ μ θ

def paced (M : Model) (μ : Buyer M → ℝ) (θ : Buyer M) (α : Context M) : ℝ :=
  val M θ α / (1 + μ θ)

/-- Distribution function of the largest of `n-1` independent paced values. -/
noncomputable def H (M : Model) (μ : Buyer M → ℝ) (α : Context M) (x : ℝ) : ℝ :=
  ((M.G {θ | paced M μ θ α ≤ x}).toReal) ^ (M.n - 1)

/-- The first-price bidding map, including both special cases of §3.1. -/
noncomputable def sigma (M : Model) (μ : Buyer M → ℝ) (α : Context M) (x : ℝ) : ℝ :=
  if x < M.r α then x else if H M μ α x = 0 then 0 else
    x - (∫ s in (M.r α)..x, H M μ α s) / H M μ α x

/-- The value pacing-based strategy of Definition 2. -/
noncomputable def beta (M : Model) (μ : Buyer M → ℝ) (θ : Buyer M)
    (α : Context M) : ℝ := sigma M μ α (paced M μ θ α)

/-- Joint law of the context and `n-1` competitors. -/
noncomputable def P (M : Model) : Measure (Context M × (Fin (M.n - 1) → Buyer M)) :=
  M.F.prod (Measure.pi fun _ : Fin (M.n - 1) => M.G)

/-- The paper's tie convention for a deviating buyer. -/
def wins (M : Model) (β : Buyer M → Context M → ℝ) (b : Context M → ℝ)
    (ω : Context M × (Fin (M.n - 1) → Buyer M)) : Prop :=
  M.r ω.1 ≤ b ω.1 ∧ ∀ i, β (ω.2 i) ω.1 ≤ b ω.1

/-- A bid over the measurable contexts, with a genuine expected payment. -/
def Admissible (M : Model) (β : Buyer M → Context M → ℝ)
    (b : Context M → ℝ) : Prop :=
  Measurable b ∧ (∀ α ∈ M.A, 0 ≤ b α) ∧
    Integrable (fun ω : Context M × (Fin (M.n - 1) → Buyer M) =>
      if wins M β b ω then b ω.1 else 0) (P M)

noncomputable def payment (M : Model) (β : Buyer M → Context M → ℝ)
    (b : Context M → ℝ) : ℝ :=
  ∫ ω, (if wins M β b ω then b ω.1 else 0) ∂P M

noncomputable def utility (M : Model) (β : Buyer M → Context M → ℝ)
    (θ : Buyer M) (b : Context M → ℝ) : ℝ :=
  ∫ ω, (if wins M β b ω then val M θ ω.1 - b ω.1 else 0) ∂P M

def IsOptimal (M : Model) (β : Buyer M → Context M → ℝ)
    (θ : Buyer M) (b : Context M → ℝ) : Prop :=
  Admissible M β b ∧ payment M β b ≤ θ.2 ∧
  ∀ b', Admissible M β b' → payment M β b' ≤ θ.2 →
    utility M β θ b' ≤ utility M β θ b

/-- The symmetric first-price equilibrium in Definition 1. -/
def IsSFPE (M : Model) (β : Buyer M → Context M → ℝ) : Prop :=
  Measurable (Function.uncurry β) ∧ ∀ᵐ θ ∂M.G, IsOptimal M β θ (β θ)

/-- The dual function from the first line of the p. 7 display. -/
noncomputable def qDual (M : Model) (μ : Buyer M → ℝ) (θ : Buyer M) (t : ℝ) : ℝ :=
  sSup {v : ℝ | ∃ b : Context M → ℝ, Admissible M (beta M μ) b ∧
    v = ∫ ω, (if wins M (beta M μ) b ω then
      val M θ ω.1 - (1 + t) * b ω.1 else 0) ∂P M} + t * θ.2

/-- The Lagrangian-optimal bid candidate in Lemma 1. -/
noncomputable def bidAt (M : Model) (μ : Buyer M → ℝ) (θ : Buyer M)
    (t : ℝ) : Context M → ℝ :=
  fun α => sigma M μ α (val M θ α / (1 + t))

end

end ContextualAuctions.PoA


