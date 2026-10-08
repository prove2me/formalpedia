-- Prove2me | Definitions.Def_LittleLaw50_FiniteWindow_Window
-- name    : LittleLaw50_FiniteWindow_Window
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T07:52:16.771972+00:00
-- url     : https://prove2.me/theorems/3bec3534-e950-4ed1-abf3-cfacc9fea0b7
-- title:
--   §2.2.2, p. 539 — S(T), the time in system during [0, T], and L(T), λ(T), W(T) of Theorem LL.2, for all items or one class
-- statement:
--   These are the quantities of Theorem LL.2 (Little's Law over $[0, T]$) and of its class-wise Corollary (3), in Little's *Little's Law as Viewed on Its 50th Anniversary*. The object is one deterministic **sample path** observed over a finite window $[0, T]$; unlike in Theorem LL.1, items may already be in the system at time $0$ and may still be there at time $T$.
--
--   The sample path consists of finitely many items $i = 1, \dots, M$. Item $i$ arrives at time $a_i$ and leaves at time $d_i$, and is in the system at time $t$ exactly when $a_i \le t < d_i$. An item that has not left by $T$ is given any departure time $d_i > T$; its time after $T$ never enters a quantity below. All quantities are computed from a set $s$ of **recorded items**: $s$ is all items for Theorem LL.2, and the items of one class for Corollary (3) ("we only record data about ... type $k$ items").
--
--   1. The number of recorded items in the system at time $t$:
--   $$n_s(t) = \#\{\, i \in s : a_i \le t < d_i \,\}.$$
--   For $s$ the set of all items this is the published `KellyStochasticNetworks.occupancy`, i.e. $n(t)$.
--   2. $S(T)$, the cumulative number of items in the system over $[0, T]$: the recorded items that were in the system at $t = 0$ having arrived before $0$ ($a_i < 0 < d_i$), plus the recorded items arriving in $[0, T]$ ($0 \le a_i \le T$).
--   3. The time item $i$ spends in the system during $[0, T]$, the length of $[a_i, d_i) \cap [0, T]$:
--   $$w_i(T) = \max\bigl(0,\ \min(d_i, T) - \max(a_i, 0)\bigr).$$
--   4. The area $A = \int_0^T n_s(t)\,dt$.
--   5. $L(T) = A/T$, $\lambda(T) = S(T)/T$, and
--   $$W(T) = \frac{1}{S(T)} \sum_{i \text{ counted in } S(T)} w_i(T),$$
--   the average time in system over $[0, T]$ of the $S(T)$ counted items.
--   6. For a class assignment $c$ of the items to classes $1, \dots, K$ (mutually exclusive and exhaustive), the items of class $k$, $\{\, i : c(i) = k \,\}$.
--
--   $W(T)$ is the paper's "average incremental age being added to the wines in the cellar during the interval": an item present at $0$ starts accumulating time at $0$, and an item present at $T$ stops at $T$.
--
--   **Formalization Note** Items are indexed by `Fin M`, a finite family; the family may also contain items never present during $[0, T]$ (they leave by $0$ or arrive after $T$), which are not counted in $S(T)$ and have $w_i(T) = 0$. With half-open presence, an item arriving exactly at $0$ is counted once, as an arrival in $[0, T]$, so $S(T)$ reduces to Theorem LL.1's $N$ when every item lies in $[0, T]$. The paper's remark $S(0) = n(0)$ then holds except for an item arriving and leaving at the same instant $0$. $W(T)$ is the average of the individual times in window, never defined as $A/S(T)$. When $S(T) = 0$ the paper's $W(T)$ is undefined and Lean's division gives $0$. A trivial `rfl` lemma `numIn_univ` records that $n_s$ for all items is Kelly's `occupancy`.
-- source:
--   Little, Little's Law as Viewed on Its 50th Anniversary, Oper. Res. 59(3) (2011), DOI 10.1287/opre.1110.0940, p. 539, §2.2.1 (W(T)), §2.2.2 (proof of Theorem LL.2: S(t), A), §2.2.3 Corollary (3) (classes); p. 538, §2.1.4 (sample path)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Migration

namespace LittleLaw50.FiniteWindow

open KellyStochasticNetworks

/-! # The LL parameters of Theorem LL.2 (Little 2011, §2.2.2, p. 539)

A sample path has `M` items; item `i` arrives at `a i` and leaves at `d i` (an item still present
at `T` has any `d i > T`), and is in the system at time `t` iff `a i ≤ t < d i`.  Every quantity
is computed from the items of a set `s` of *recorded* items: `s = Finset.univ` is the whole path
(Theorem LL.2), and `s = classItems c k` is class `k` (§2.2.3, Corollary (3)). -/

/-- `n_s(t)`, the number of recorded items in the system at time `t`. -/
noncomputable def numIn {M : ℕ} (s : Finset (Fin M)) (a d : Fin M → ℝ) (t : ℝ) : ℝ :=
  ∑ i ∈ s, Set.indicator (Set.Ico (a i) (d i)) (fun _ => (1 : ℝ)) t

/-- For the whole path, `n(t)` is Kelly's `occupancy`. -/
theorem numIn_univ {M : ℕ} (a d : Fin M → ℝ) : numIn Finset.univ a d = occupancy a d := rfl

/-- The items counted by `S(T)`: the recorded items that were in the system at `t = 0` having
arrived before `0` (`a i < 0 < d i`), together with the recorded arrivals in `[0, T]`
(`0 ≤ a i ≤ T`). -/
noncomputable def countedItems {M : ℕ} (s : Finset (Fin M)) (a d : Fin M → ℝ) (T : ℝ) : Finset (Fin M) :=
  s.filter fun i => (a i < 0 ∧ 0 < d i) ∨ (0 ≤ a i ∧ a i ≤ T)

/-- `S(T)`, the cumulative number of items in the system over `[0, T]`. -/
noncomputable def cumCount {M : ℕ} (s : Finset (Fin M)) (a d : Fin M → ℝ) (T : ℝ) : ℝ :=
  ((countedItems s a d T).card : ℝ)

/-- The time item `i` spends in the system during `[0, T]`: the length of `[aᵢ, dᵢ) ∩ [0, T]`,
i.e. `max 0 (min dᵢ T − max aᵢ 0)`. -/
noncomputable def timeInWindow {M : ℕ} (a d : Fin M → ℝ) (T : ℝ) (i : Fin M) : ℝ :=
  max 0 (min (d i) T - max (a i) 0)

/-- `A = ∫₀ᵀ n_s(t) dt`, the area under `n_s(t)` over `[0, T]`. -/
noncomputable def area {M : ℕ} (s : Finset (Fin M)) (a d : Fin M → ℝ) (T : ℝ) : ℝ :=
  ∫ t in (0:ℝ)..T, numIn s a d t

/-- `L(T) = A / T`, the time average of the number of recorded items in the system during
`[0, T]`. -/
noncomputable def Lw {M : ℕ} (s : Finset (Fin M)) (a d : Fin M → ℝ) (T : ℝ) : ℝ :=
  area s a d T / T

/-- `λ(T) = S(T) / T`. -/
noncomputable def lamw {M : ℕ} (s : Finset (Fin M)) (a d : Fin M → ℝ) (T : ℝ) : ℝ :=
  cumCount s a d T / T

/-- `W(T)`, the average over the `S(T)` counted items of the time each spends in the system
during `[0, T]`. -/
noncomputable def Ww {M : ℕ} (s : Finset (Fin M)) (a d : Fin M → ℝ) (T : ℝ) : ℝ :=
  (∑ i ∈ countedItems s a d T, timeInWindow a d T i) / cumCount s a d T

/-- The items of class `k`, for a class assignment `c : Fin M → Fin K` (the classes are
mutually exclusive and cover every item). -/
def classItems {M K : ℕ} (c : Fin M → Fin K) (k : Fin K) : Finset (Fin M) :=
  Finset.univ.filter fun i => c i = k

end LittleLaw50.FiniteWindow


