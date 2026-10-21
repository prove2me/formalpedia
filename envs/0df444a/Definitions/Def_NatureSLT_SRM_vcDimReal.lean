-- Prove2me | Definitions.Def_NatureSLT_SRM_vcDimReal
-- name    : NatureSLT_SRM_vcDimReal
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:50:54.415336+00:00
-- url     : https://prove2.me/theorems/c04975d0-003b-45cf-a148-4223cdfa7409
-- title:
--   VC dimension of a set of real functions $A \le Q(z,\alpha) \le B$ via the indicators $\theta\{Q(z,\alpha) - \beta\}$, $\beta \in (A, B)$
-- statement:
--   Let $Q(z, \alpha)$, $\alpha \in \Lambda$, be a set of functions on a set $Z$ indexed by an arbitrary parameter set $\Lambda$. For indicator functions (values in $\{0, 1\}$), points $z_1, \dots, z_h$ are **shattered** if they can be separated into two classes in all $2^h$ possible ways by functions of the set: for every $\delta \in \{0,1\}^h$ some $\alpha$ has $Q(z_i, \alpha) = \delta_i$ for all $i$. The **VC dimension** of a set of indicator functions is the maximum number $h$ of points that can be shattered, and is infinite if arbitrarily many points can be shattered.
--
--   For a set of real functions bounded by constants, $A \le Q(z, \alpha) \le B$ ($A$ may be $-\infty$, $B$ may be $+\infty$), consider the indicators
--   $$I(z, \alpha, \beta) = \theta\{Q(z, \alpha) - \beta\}, \qquad \alpha \in \Lambda,\ \beta \in (A, B),$$
--   where $\theta(u) = 0$ for $u < 0$ and $\theta(u) = 1$ for $u \ge 0$. The **VC dimension of the set of real functions** is the VC dimension of this set of indicators, with parameters $\alpha \in \Lambda$ and $\beta \in (A, B)$.
--
--   This is the capacity $h_k$ attached to each element $S_k$ of a structure in structural risk minimization, and the $h$ in the confidence terms of the bounds (4.1) and (4.2).
--
--   **Formalization Note** Indicator values are Booleans (`true` for $1$); the VC dimension takes values in $\mathbb N \cup \{\infty\}$ (`ℕ∞`), the supremum of the sizes of shattered samples. The bounds $A, B$ are extended reals and enter only through the range of $\beta$; a statement about a particular set of functions states $A \le Q \le B$ as a hypothesis. For an empty parameter set nothing is shattered and the value is $0$. The file also defines the step function $\theta$ (with $\theta(0) = 1$), shattering and the VC dimension of indicator functions, on which this definition is built.
-- source:
--   Vapnik, The Nature of Statistical Learning Theory, 2nd ed., Springer 2000, p. 80, Section 3.6, (3.22)

import Mathlib

namespace NatureSLT.SRM

/-- The **step function** of (3.22) (Vapnik, *The Nature of Statistical Learning Theory*, 2nd ed.,
§3.6, p. 80): `θ(z) = 0` if `z < 0` and `θ(z) = 1` if `z ≥ 0`, as a `Bool` (`true` = `1`). -/
noncomputable def stepFunction (z : ℝ) : Bool := decide (0 ≤ z)

/-- The points `z₁, …, z_h` are **shattered** by the indicator functions `Q(z, α)`, `α ∈ Λ`
(§3.6, p. 80): for every assignment `δ₁, …, δ_h ∈ {0, 1}` some `α ∈ Λ` has `Q(zᵢ, α) = δᵢ`
for every `i`. `Q α z` is the book's `Q(z, α)`. -/
def Shatters {Z Λ : Type*} (Q : Λ → Z → Bool) {h : ℕ} (z : Fin h → Z) : Prop :=
  ∀ δ : Fin h → Bool, ∃ α : Λ, ∀ i : Fin h, Q α (z i) = δ i

/-- The **VC dimension of a set of indicator functions** (§3.6, p. 80): the maximum number `h`
of points that can be shattered, `⊤` (infinity) if arbitrarily many points can be shattered. -/
noncomputable def vcDim {Z Λ : Type*} (Q : Λ → Z → Bool) : ℕ∞ :=
  ⨆ (h : ℕ) (_ : ∃ z : Fin h → Z, Shatters Q z), (h : ℕ∞)

/-- The indicators (3.22) of a set of real functions `A ≤ Q(z, α) ≤ B` (§3.6, p. 80):
`I(z, α, β) = θ{Q(z, α) − β}`, indexed by the pairs `(α, β)` with `α ∈ Λ` and `β ∈ (A, B)`.
`A`, `B` are extended reals (the book allows `A = −∞`, `B = ∞`). -/
noncomputable def realIndicators {Z Λ : Type*} (Q : Λ → Z → ℝ) (A B : EReal) :
    {p : Λ × ℝ // A < (p.2 : EReal) ∧ (p.2 : EReal) < B} → Z → Bool :=
  fun p z => stepFunction (Q p.1.1 z - p.1.2)

/-- The **VC dimension of a set of real functions** `A ≤ Q(z, α) ≤ B`, `α ∈ Λ` (Vapnik, 1979;
§3.6, p. 80): the VC dimension of the set of indicators (3.22) `θ{Q(z, α) − β}` with
parameters `α ∈ Λ` and `β ∈ (A, B)`. -/
noncomputable def vcDimReal {Z Λ : Type*} (Q : Λ → Z → ℝ) (A B : EReal) : ℕ∞ :=
  vcDim (realIndicators Q A B)

end NatureSLT.SRM


