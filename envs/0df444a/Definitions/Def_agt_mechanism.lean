-- Prove2me | Definitions.Def_agt_mechanism
-- name    : agt_mechanism
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-13T03:08:02.316635+00:00
-- url     : https://prove2.me/theorems/b66e0657-4443-43ec-a444-c3f3eed47766
-- title:
--   Mechanisms, VCG, weak monotonicity, and single-parameter domains
-- statement:
--   This bundle fixes the quasilinear mechanism-design vocabulary of §§9.3 and 9.5 of *Algorithmic Game Theory* (Nisan). There is a set $A$ of alternatives and a finite set $\iota$ of players; player $i$ holds a valuation $v_i : A \to \mathbb{R}$ from a publicly known domain $V_i$, and utility is quasilinear, $v_i(a) - p_i$.
--
--   1. **`IsValProfile`** — a profile of valuations drawn from the players' domains (§9.3.1).
--   2. **`MechIncentiveCompatible`** — Definition 9.15: no unilateral misreport from the domain ever gives higher quasilinear utility than the truth.
--   3. **`MaximizesWelfare`** — the chosen alternative maximizes $\sum_i v_i(a)$ at every profile of the domain (the first VCG condition).
--   4. **`IsVCG`** — Definition 9.16: welfare maximization plus Groves payments $p_i = h_i(v_{-i}) - \sum_{j\ne i} v_j(f(v))$, where "$h_i$ does not depend on $v_i$" is rendered as invariance of $h_i$ under updating coordinate $i$.
--   5. **`IndividuallyRational`**, **`NoPositiveTransfers`** — Definition 9.18: utilities always nonnegative; payments always nonnegative.
--   6. **`clarkePayment`** — Definition 9.19: $h_i(v_{-i}) = \max_b \sum_{j\ne i} v_j(b)$, the externality payment; the maximum is a `Finset.sup'` over a finite nonempty $A$, so it is attained and no junk supremum arises.
--   7. **`WeakMonotone`** — Definition 9.28: an outcome change from $a$ to $b$ caused by player $i$'s change of valuation satisfies $v_i'(b)-v_i'(a) \ge v_i(b)-v_i(a)$.
--   8. **`spValue`** — Definition 9.33: the single-parameter valuation worth $t$ on the win set $W_i$ and $0$ elsewhere (a `Set.indicator`).
--   9. **`SPIncentiveCompatible`**, **`SPNormalized`** — truthfulness for scalar bids in $[t_0,t_1]$, and the normalization "losing bids pay $0$" (§9.5.4).
--   10. **`SPMonotone`** — Definition 9.34: raising a winning bid keeps it winning.
--   11. **`SPCriticalPayments`** — Definitions 9.35/Theorem 9.36(ii): every winning bid pays a value $c$ fixed by the others' bids, and whenever some bid loses, $c$ is the least upper bound of the losing bids.
--
--   *A note on conventions.* Mechanisms are total functions on all valuation profiles, but every property quantifies only over profiles from the domain $V$, so behavior on invalid inputs carries no content. The critical value is characterized by `IsLUB` guarded by nonemptiness of the losing set — the book's "the critical value is undefined if the set is empty" caveat made precise without a junk `sSup`.
-- source:
--   N. Nisan, T. Roughgarden, E. Tardos, V. V. Vazirani (eds.), Algorithmic Game Theory, Cambridge University Press 2007, https://doi.org/10.1017/CBO9780511800481, Ch. 9, Sections 9.3 and 9.5, Definitions 9.14-9.19, 9.28, 9.33-9.35, pp. 216-230

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Order.Bounds.Basic
import Mathlib.Algebra.Group.Indicator

/-!
Mechanisms with money, following Chapter 9 (Nisan, "Introduction to
Mechanism Design (for Computer Scientists)") of
Nisan–Roughgarden–Tardos–Vazirani (eds.), *Algorithmic Game Theory* (2007),
§§9.3 and 9.5.

There is a set `A` of alternatives and a finite set `ι` of players.  Player
`i` holds a private **valuation** `vᵢ : A → ℝ` from a publicly known domain
`V i ⊆ (A → ℝ)`; utilities are quasilinear, `vᵢ(a) − pᵢ`.  A **(direct
revelation) mechanism** is a social choice function
`f : (ι → A → ℝ) → A` together with payment functions
`p i : (ι → A → ℝ) → ℝ` (Definition 9.14).  Mechanisms are total functions
on all valuation profiles; every property below quantifies only over
profiles from the domain `V`, so behavior on invalid inputs is irrelevant.

The single-parameter setting of §9.5.4 is presented by a win set
`W i ⊆ A` per player and a scalar bid in `[t₀, t₁]`: the valuation
determined by the scalar `t` is `t` on `W i` and `0` elsewhere
(Definition 9.33).
-/

namespace AGT

open Finset

variable {A ι : Type*}

/-- A valuation profile drawn from the players' domains: `v i ∈ V i` for
every player (§9.3.1). -/
def IsValProfile (V : ι → Set (A → ℝ)) (v : ι → A → ℝ) : Prop :=
  ∀ i, v i ∈ V i

variable [Fintype ι] [DecidableEq ι]

/-- **Incentive compatibility** of a mechanism `(f, p)` on the domain `V`
(Definition 9.15): for every player and every unilateral misreport from the
domain, the quasilinear utility of truth-telling is at least that of the
misreport. -/
def MechIncentiveCompatible (V : ι → Set (A → ℝ)) (f : (ι → A → ℝ) → A)
    (p : ι → (ι → A → ℝ) → ℝ) : Prop :=
  ∀ v, IsValProfile V v → ∀ i, ∀ v' ∈ V i,
    v i (f (Function.update v i v')) - p i (Function.update v i v') ≤
      v i (f v) - p i v

/-- `f` **maximizes social welfare** on the domain `V`: at every profile the
chosen alternative maximizes `∑ i, vᵢ(a)` (the first VCG condition,
Definition 9.16). -/
def MaximizesWelfare (V : ι → Set (A → ℝ)) (f : (ι → A → ℝ) → A) : Prop :=
  ∀ v, IsValProfile V v → ∀ a : A, ∑ i, v i a ≤ ∑ i, v i (f v)

/-- `(f, p)` is a **Vickrey–Clarke–Groves mechanism** (Definition 9.16):
`f` maximizes social welfare, and each payment has the Groves form
`pᵢ = hᵢ(v₋ᵢ) − ∑_{j ≠ i} vⱼ(f(v))` where `hᵢ` does not depend on `vᵢ`
(expressed by invariance under updating coordinate `i`). -/
def IsVCG (V : ι → Set (A → ℝ)) (f : (ι → A → ℝ) → A)
    (p : ι → (ι → A → ℝ) → ℝ) : Prop :=
  MaximizesWelfare V f ∧
    ∃ h : ι → (ι → A → ℝ) → ℝ,
      (∀ i v (v' : A → ℝ), h i (Function.update v i v') = h i v) ∧
      ∀ v, IsValProfile V v → ∀ i,
        p i v = h i v - ∑ j ∈ Finset.univ.erase i, v j (f v)

/-- The mechanism is **(ex-post) individually rational** (Definition 9.18):
players always get nonnegative utility. -/
def IndividuallyRational (V : ι → Set (A → ℝ)) (f : (ι → A → ℝ) → A)
    (p : ι → (ι → A → ℝ) → ℝ) : Prop :=
  ∀ v, IsValProfile V v → ∀ i, 0 ≤ v i (f v) - p i v

/-- The mechanism makes **no positive transfers** (Definition 9.18): no
player is ever paid money. -/
def NoPositiveTransfers (V : ι → Set (A → ℝ)) (_f : (ι → A → ℝ) → A)
    (p : ι → (ι → A → ℝ) → ℝ) : Prop :=
  ∀ v, IsValProfile V v → ∀ i, 0 ≤ p i v

/-- The **Clarke pivot payment** (Definition 9.19):
`hᵢ(v₋ᵢ) = max_b ∑_{j ≠ i} vⱼ(b)`, so player `i` pays the externality they
impose on the others.  Requires a finite nonempty alternative set so the
maximum is attained. -/
noncomputable def clarkePayment [Fintype A] [Nonempty A]
    (f : (ι → A → ℝ) → A) : ι → (ι → A → ℝ) → ℝ :=
  fun i v =>
    (Finset.univ.sup' Finset.univ_nonempty fun b =>
        ∑ j ∈ Finset.univ.erase i, v j b) -
      ∑ j ∈ Finset.univ.erase i, v j (f v)

/-- **Weak monotonicity** (Definition 9.28): if the outcome changes from
`a` to `b` when player `i` alone changes their valuation from `vᵢ` to
`vᵢ'`, then `vᵢ'(b) − vᵢ'(a) ≥ vᵢ(b) − vᵢ(a)` — the player raised the value
of the new choice relative to the old one. -/
def WeakMonotone (V : ι → Set (A → ℝ)) (f : (ι → A → ℝ) → A) : Prop :=
  ∀ v, IsValProfile V v → ∀ i, ∀ v' ∈ V i,
    f v ≠ f (Function.update v i v') →
      v i (f (Function.update v i v')) - v i (f v) ≤
        v' (f (Function.update v i v')) - v' (f v)

/-- The valuation of a single-parameter player with win set `W i` and
scalar value `t` (Definition 9.33): worth `t` on every winning alternative
and `0` elsewhere. -/
noncomputable def spValue (W : ι → Set A) (i : ι) (t : ℝ) : A → ℝ :=
  (W i).indicator fun _ => t

/-- **Incentive compatibility on a single-parameter domain**: players bid
scalars in `[t₀, t₁]`, and no unilateral scalar misreport beats the truth in
quasilinear utility (Definition 9.15 specialized via Definition 9.33). -/
def SPIncentiveCompatible (W : ι → Set A) (t0 t1 : ℝ) (f : (ι → ℝ) → A)
    (p : ι → (ι → ℝ) → ℝ) : Prop :=
  ∀ t : ι → ℝ, (∀ j, t j ∈ Set.Icc t0 t1) → ∀ i, ∀ s ∈ Set.Icc t0 t1,
    spValue W i (t i) (f (Function.update t i s)) -
        p i (Function.update t i s) ≤
      spValue W i (t i) (f t) - p i t

/-- The mechanism is **normalized**: losing bids pay `0` (§9.5.4). -/
def SPNormalized (W : ι → Set A) (t0 t1 : ℝ) (f : (ι → ℝ) → A)
    (p : ι → (ι → ℝ) → ℝ) : Prop :=
  ∀ t : ι → ℝ, (∀ j, t j ∈ Set.Icc t0 t1) → ∀ i, f t ∉ W i → p i t = 0

/-- `f` is **monotone** on a single-parameter domain (Definition 9.34):
raising a winning bid, the others fixed, keeps it winning. -/
def SPMonotone (W : ι → Set A) (t0 t1 : ℝ) (f : (ι → ℝ) → A) : Prop :=
  ∀ t : ι → ℝ, (∀ j, t j ∈ Set.Icc t0 t1) → ∀ i,
    ∀ s ∈ Set.Icc t0 t1, ∀ s' ∈ Set.Icc t0 t1, s ≤ s' →
      f (Function.update t i s) ∈ W i → f (Function.update t i s') ∈ W i

/-- **Payments are the critical value** (Definitions 9.35 and Theorem
9.36(ii)): for every player and every profile of others' bids there is a
value `c` that every winning bid pays; and whenever some bid in `[t₀,t₁]`
loses, `c` is the least upper bound of the losing bids — the critical value
below which the player loses and above which they win.  Phrasing the
critical value through `IsLUB`, guarded by nonemptiness of the losing set,
renders the book's "undefined if the set is empty" caveat without appeal to
a junk supremum. -/
def SPCriticalPayments (W : ι → Set A) (t0 t1 : ℝ) (f : (ι → ℝ) → A)
    (p : ι → (ι → ℝ) → ℝ) : Prop :=
  ∀ t : ι → ℝ, (∀ j, t j ∈ Set.Icc t0 t1) → ∀ i, ∃ c : ℝ,
    (∀ s ∈ Set.Icc t0 t1, f (Function.update t i s) ∈ W i →
      p i (Function.update t i s) = c) ∧
    ((∃ s ∈ Set.Icc t0 t1, f (Function.update t i s) ∉ W i) →
      IsLUB {s | s ∈ Set.Icc t0 t1 ∧ f (Function.update t i s) ∉ W i} c)

end AGT


