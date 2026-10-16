-- Prove2me | Definitions.Def_ContextualAuctions_Structure_Setting
-- name    : ContextualAuctions_Structure_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T19:28:07.18509+00:00
-- url     : https://prove2.me/theorems/402fd29a-270c-46fd-9634-140de2e0d300
-- title:
--   §2–§3.2 — contextual budget-constrained first price auctions: Θ, A, F, G, r, ω, pacing, H^µ_α, σ^µ_α, β^µ (Definition 2), the buyer's bids and the dual function q^µ
-- statement:
--   This file sets up the model of Balseiro, Kroer and Kumar for a single item sold by first price auction to $n$ budget-constrained buyers whose values depend on the item's features.
--
--   **Primitives (§2, §2.2).** There are $d$ features and $n$ buyers. An item has a context $\alpha \in A \subset \mathbb{R}^d_+$, drawn from a law $F$. A buyer type is $\theta = (w, B)$, with weight vector $w \in \mathbb{R}^d$ and budget $B$, drawn independently for every buyer from a law $G$ on the type space
--   $$\Theta = (0, U)^d \times (B_{\min}, U).$$
--   The value of type $(w, B)$ for item $\alpha$ is $w^{\top}\alpha = \sum_i w_i \alpha_i$, and $\omega = \sup_{(w,B)\in\Theta,\ \alpha\in A} w^{\top}\alpha$ is the largest value a buyer can have. The reserve price for item $\alpha$ is $r(\alpha)$.
--
--   The standing assumptions are: $d \ge 2$; $U > 0$, $B_{\min} > 0$; $A$ is a measurable subset of the strictly positive orthant; $F$ and $G$ are probability measures with densities (absolutely continuous with respect to Lebesgue measure) and $F(A^{c}) = 0$, $G(\Theta^{c}) = 0$; $r$ is measurable.
--
--   **Pacing (§3.1).** A pacing function $\mu : \Theta \to \mathbb{R}_{\ge 0}$ is measurable. It scales values down to the paced values $w^{\top}\alpha/(1+\mu(w,B))$. Let $\lambda^\mu_\alpha$ be the law of the paced value of a type drawn from $G$, and
--   $$H^\mu_\alpha(x) = \lambda^\mu_\alpha\big((-\infty, x]\big)^{n-1},$$
--   the distribution function of the highest of $n-1$ independent paced values. The bidding function is
--   $$\sigma^\mu_\alpha(x) = \begin{cases} x, & x < r(\alpha),\\ 0, & x \ge r(\alpha),\ H^\mu_\alpha(x) = 0,\\ x - \displaystyle\int_{r(\alpha)}^{x} \frac{H^\mu_\alpha(s)}{H^\mu_\alpha(x)}\,ds, & \text{otherwise,}\end{cases}$$
--   and the value pacing–based strategy (Definition 2) is $\beta^\mu(w,B,\alpha) = \sigma^\mu_\alpha\big(w^{\top}\alpha/(1+\mu(w,B))\big)$.
--
--   **The buyer's problem (Definition 1, §3.2).** A buyer facing $n-1$ competitors who bid by a strategy $\beta$ chooses a bid $b(\alpha) \ge 0$ for every context. The bid wins when $b(\alpha) \ge \max(r(\alpha), \{\beta(\theta_i, \alpha)\}_i)$, where $\alpha \sim F$ and $\theta_1, \dots, \theta_{n-1} \sim G$ are independent; ties count as wins, as in the paper's tie-breaking rule. An admissible bid is measurable, nonnegative and has an integrable expected payment. The dual function of a type $(w, B)$ facing $\beta^\mu$ is
--   $$q^\mu(w,B,t) = \sup_{b} \ \mathbb{E}_{\alpha,\{\theta_i\}}\Big[\big(w^{\top}\alpha - (1+t)\,b(\alpha)\big)\,\mathbf 1\{b(\alpha) \ge \max(r(\alpha), \{\beta^\mu(\theta_i,\alpha)\}_i)\}\Big] + tB,$$
--   the supremum taken over admissible bids.
--
--   These objects are used by every statement of the mission; the §6 objects (support of $G$, unique best response) are in a separate file.
--
--   **Formalization Note.** Types are pairs `(w, B) : (Fin d → ℝ) × ℝ`; values are explicit sums. Three hypotheses are added to the paper's: $n \ge 2$ (the paper's $H^\mu_\alpha$ is the law of a maximum over $n-1$ buyers), $B_{\min} < U$ (otherwise $\Theta$ is empty), and $A$ nonempty and bounded (otherwise $\omega$, written as a maximum on p. 4, is infinite). Because $\Theta$ is open, $\omega$ is a supremum, not an attained maximum. The paper's Lebesgue σ-algebra is replaced by the Borel σ-algebra; since $F$ and $G$ have densities, the expectations agree. $\sigma^\mu_\alpha$ uses an explicit case split, so the $H^\mu_\alpha(x) = 0$ case returns $0$ as the paper prescribes rather than Lean's $x/0 = 0$. The dual function is the supremum over bids of p. 7, first line, not the closed form of p. 8. A pacing function is a real function nonnegative on $\Theta$; its values off $\Theta$ are $G$-null and irrelevant.
-- source:
--   Balseiro, Kroer, Kumar, Contextual Standard Auctions with Budgets: Revenue Equivalence and Efficiency Guarantees, Management Science, Articles in Advance (2023), doi:10.1287/mnsc.2023.4719, pp. 4–7, §2, §2.2, Definition 1, §3.1 (Definition 2), §3.2 (dual function q^µ, p. 7)

import Mathlib

namespace ContextualAuctions.Structure

open MeasureTheory

/-- The primitives of the contextual auction model (§2, p. 4): `d` features, `n` buyers, the bounds
`U`, `B_min` of the type space, the set of contexts `A`, the context law `F`, the type law `G` and the
context-dependent reserve price `r`. A buyer type is `θ = (w, B) : (Fin d → ℝ) × ℝ`. -/
structure Model where
  d : ℕ
  n : ℕ
  U : ℝ
  Bmin : ℝ
  A : Set (Fin d → ℝ)
  F : Measure (Fin d → ℝ)
  G : Measure ((Fin d → ℝ) × ℝ)
  r : (Fin d → ℝ) → ℝ

/-- The value `w^T α` of buyer type `θ = (w, B)` for an item with context `α`. -/
def val {d : ℕ} (θ : (Fin d → ℝ) × ℝ) (α : Fin d → ℝ) : ℝ := ∑ i, θ.1 i * α i

/-- The type space `Θ = (0, U)^d × (B_min, U)` (§2.2, p. 5). -/
def Theta (M : Model) : Set ((Fin M.d → ℝ) × ℝ) :=
  {θ | (∀ i, 0 < θ.1 i ∧ θ.1 i < M.U) ∧ M.Bmin < θ.2 ∧ θ.2 < M.U}

/-- `ω`, the largest value a buyer can have for an item (§2, p. 4), as a supremum over `Θ × A`. -/
noncomputable def omega (M : Model) : ℝ :=
  sSup {v | ∃ θ ∈ Theta M, ∃ α ∈ M.A, v = val θ α}

/-- The standing assumptions of §2 and §2.2. `2 ≤ n`, `B_min < U` and the boundedness and
nonemptiness of `A` are disclosed additions (see the natural-language statement). -/
structure Model.Standing (M : Model) : Prop where
  two_le_d : 2 ≤ M.d
  two_le_n : 2 ≤ M.n
  U_pos : 0 < M.U
  Bmin_pos : 0 < M.Bmin
  Bmin_lt_U : M.Bmin < M.U
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

/-- A pacing function `µ : Θ → ℝ≥0` (§3.1), measurable, nonnegative on `Θ`. -/
def IsPacing (M : Model) (mu : (Fin M.d → ℝ) × ℝ → ℝ) : Prop :=
  Measurable mu ∧ ∀ θ ∈ Theta M, 0 ≤ mu θ

/-- The paced value `w^T α / (1 + µ(w, B))` (§3.1). -/
noncomputable def paced {d : ℕ} (mu : (Fin d → ℝ) × ℝ → ℝ) (θ : (Fin d → ℝ) × ℝ)
    (α : Fin d → ℝ) : ℝ :=
  val θ α / (1 + mu θ)

/-- `H^µ_α(x) = λ^µ_α((−∞, x])^{n−1}`, the c.d.f. of the highest of `n − 1` i.i.d. paced values. -/
noncomputable def H (M : Model) (mu : (Fin M.d → ℝ) × ℝ → ℝ) (α : Fin M.d → ℝ) (x : ℝ) : ℝ :=
  ((M.G {θ | paced mu θ α ≤ x}).toReal) ^ (M.n - 1)

/-- The bidding function `σ^µ_α` (§3.1, p. 6): `x` below the reserve, `0` where `H^µ_α(x) = 0`, and
`x − ∫_{r(α)}^x H^µ_α(s)/H^µ_α(x) ds` otherwise. -/
noncomputable def sigma (M : Model) (mu : (Fin M.d → ℝ) × ℝ → ℝ) (α : Fin M.d → ℝ) (x : ℝ) : ℝ :=
  if x < M.r α then x
  else if H M mu α x = 0 then 0
  else x - (∫ s in (M.r α)..x, H M mu α s) / H M mu α x

/-- The value pacing–based strategy `β^µ(w, B, α) = σ^µ_α(w^T α / (1 + µ(w, B)))` (Definition 2). -/
noncomputable def beta (M : Model) (mu : (Fin M.d → ℝ) × ℝ → ℝ) (θ : (Fin M.d → ℝ) × ℝ)
    (α : Fin M.d → ℝ) : ℝ :=
  sigma M mu α (paced mu θ α)

/-- The joint law of the context `α ~ F` and the `n − 1` competitor types `θ_i ~ G`, independent. -/
noncomputable def P (M : Model) : Measure ((Fin M.d → ℝ) × (Fin (M.n - 1) → (Fin M.d → ℝ) × ℝ)) :=
  M.F.prod (Measure.pi fun _ : Fin (M.n - 1) => M.G)

/-- The bid `b(α)` wins against competitors bidding `β(θ_i, α)`: it clears the reserve and is at least
every competing bid (ties win, p. 5). -/
def wins (M : Model) (β : (Fin M.d → ℝ) × ℝ → (Fin M.d → ℝ) → ℝ) (b : (Fin M.d → ℝ) → ℝ)
    (ω : (Fin M.d → ℝ) × (Fin (M.n - 1) → (Fin M.d → ℝ) × ℝ)) : Prop :=
  M.r ω.1 ≤ b ω.1 ∧ ∀ i, β (ω.2 i) ω.1 ≤ b ω.1

open Classical in
/-- Admissible bids `b : A → ℝ≥0`: measurable, nonnegative, with an integrable payment. -/
def Admissible (M : Model) (β : (Fin M.d → ℝ) × ℝ → (Fin M.d → ℝ) → ℝ)
    (b : (Fin M.d → ℝ) → ℝ) : Prop :=
  Measurable b ∧ (∀ α, 0 ≤ b α) ∧
    Integrable (fun ω => if wins M β b ω then b ω.1 else 0) (P M)

open Classical in
/-- The dual function `q^µ(w, B, t)` (§3.2, p. 7, first line): the supremum over admissible bids of
`E[(w^T α − (1 + t) b(α)) 1{b wins}]`, plus `t B`. -/
noncomputable def qDual (M : Model) (mu : (Fin M.d → ℝ) × ℝ → ℝ) (θ : (Fin M.d → ℝ) × ℝ)
    (t : ℝ) : ℝ :=
  sSup {v | ∃ b, Admissible M (beta M mu) b ∧
      v = ∫ ω, (if wins M (beta M mu) b ω then val θ ω.1 - (1 + t) * b ω.1 else 0) ∂P M} +
    t * θ.2

end ContextualAuctions.Structure


