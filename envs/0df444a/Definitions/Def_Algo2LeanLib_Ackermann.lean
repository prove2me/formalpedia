-- Prove2me | Definitions.Def_Algo2LeanLib_Ackermann
-- name    : Algo2LeanLib_Ackermann
-- status  : Definition
-- author  : @lunjia
-- created : 2026-10-10T23:39:02.99515+00:00
-- url     : https://prove2.me/theorems/3a3c8483-4a01-4929-88f7-8409df0a5043
-- title:
--   Ackermann hierarchy and the inverse-Ackermann function
-- statement:
--   This is the definition bundle for the exact inverse used in every displayed union-find and Kruskal bound. The names to inspect are `Algo2Lean.Ackermann.ack`, `Algo2Lean.Ackermann.iterate`, and **`Algo2Lean.Ackermann.alpha`**.
--   $$
--   A_0(r)=r+1,\qquad A_{k+1}(r)=A_k^{(r+1)}(r),\qquad
--   \alpha(n)=\min\{k\in\mathbb N:0<k\ \text{and}\ n<A_k(1)\}.
--   $$
--   The superscript means repeated function composition, not exponentiation. The minimum is over positive hierarchy levels and uses a strict threshold; in particular the convention includes $n=0$. The Lean `alpha` definition chooses the least witness from the proved `inverse_exists`, making it noncomputable but mathematically specified. Its supporting existence facts are retained in the bundle because the definition itself requires them.
--
--   This arithmetic library does not depend on a heap, graph, generated algorithm or execution trace. Other inverse-Ackermann conventions may differ by small constants; this bundle is the authoritative convention for the submitted inequalities.
--
--   <!-- algo2lean-provenance-v0.1.4 -->
--   **[Algo2Lean](https://www.algo2lean.com/) provenance and reproduction.** These definitions target [Algo2Lean](https://www.algo2lean.com/) v0.1.4, using the compiler source at [public commit `0f79d5e4242e6477531c9ee4410409f5b1c92f76`](https://github.com/lunjiah/algo2lean/tree/0f79d5e4242e6477531c9ee4410409f5b1c92f76), and Lean 4.33.1. The versioned compiler location is [Algo2Lean v0.1.4](https://www.algo2lean.com/versions/v0.1.4/). Compile all supplied `.algo` files and imports to reproduce the raw generated definitions. Release publication and exact website parity require their separately recorded checks; this metadata alone does not assert them. Prove2Me imports and declaration packaging are mechanically adapted, with original hashes, compiler-reported source ranges, and adaptations recorded in transplant provenance. Exact reproduction does not prove the compiler correct.
-- source:
--   https://github.com/lunjiah/algo2lean/blob/0f79d5e4242e6477531c9ee4410409f5b1c92f76/Algo2LeanLib/Ackermann.lean

import Std

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
The Ackermann hierarchy used in the union-find amortized analysis.
`ack 0 r = r + 1` and `ack (k + 1) r` applies `ack k` exactly `r + 1`
times to `r`. The inverse `alpha n` is the least positive hierarchy index
whose value at one exceeds `n`. All arithmetic facts are independent of
program execution and of the union-find representation.
-/

namespace Algo2Lean.Ackermann

/-- Apply a natural-number function a fixed number of times. -/
def iterate (f : Nat → Nat) : Nat → Nat → Nat
  | 0, value => value
  | count + 1, value => f (iterate f count value)

@[simp] theorem iterate_zero (f : Nat → Nat) (value : Nat) :
    iterate f 0 value = value := rfl

@[simp] theorem iterate_succ (f : Nat → Nat) (count value : Nat) :
    iterate f (count + 1) value = f (iterate f count value) := rfl









theorem iterate_mono_count {f : Nat → Nat}
    (grow : ∀ value, value ≤ f value) {first second : Nat} (ordered : first ≤ second)
    (value : Nat) : iterate f first value ≤ iterate f second value := by
  induction second generalizing first with
  | zero =>
    have zero : first = 0 := by omega
    simp [zero]
  | succ second ih =>
    by_cases same : first = second + 1
    · subst first; exact Nat.le_refl _
    · exact Nat.le_trans (ih (by omega)) (grow _)

theorem iterate_strict_count {f : Nat → Nat}
    (grow : ∀ value, value < f value) {first second : Nat} (ordered : first < second)
    (value : Nat) : iterate f first value < iterate f second value := by
  have step := grow (iterate f first value)
  have rest := iterate_mono_count (fun x => Nat.le_of_lt (grow x)) ordered value
  exact Nat.lt_of_lt_of_le step rest



/-- The increasing hierarchy obtained by repeated iteration. -/
def ack : Nat → Nat → Nat
  | 0, value => value + 1
  | level + 1, value => iterate (ack level) (value + 1) value

@[simp] theorem ack_zero (value : Nat) : ack 0 value = value + 1 := rfl



theorem ack_gt (level value : Nat) : value < ack level value := by
  induction level generalizing value with
  | zero => simp
  | succ level ih =>
    have start := ih value
    have rest := iterate_mono_count (fun x => Nat.le_of_lt (ih x))
      (Nat.succ_le_succ (Nat.zero_le value)) value
    exact Nat.lt_of_lt_of_le start rest









theorem ack_lt_succ (level : Nat) {value : Nat} (positive : 0 < value) :
    ack level value < ack (level + 1) value := by
  exact iterate_strict_count (ack_gt level) (by omega : 1 < value + 1) value

theorem index_bound (level : Nat) : level + 2 ≤ ack level 1 := by
  induction level with
  | zero => simp
  | succ level ih =>
    have growing := ack_lt_succ level (by decide : 0 < 1)
    omega

/-- Every inhabited natural-number predicate has a least witness. -/
 theorem least_exists (property : Nat → Prop) (inhabited : ∃ value, property value) :
    ∃ value, property value ∧ ∀ other, other < value → ¬ property other := by
  classical
  obtain ⟨bound, holds⟩ := inhabited
  induction bound using Nat.strongRecOn with
  | ind bound ih =>
    by_cases earlier : ∃ other, other < bound ∧ property other
    · obtain ⟨other, smaller, valid⟩ := earlier
      exact ih other smaller valid
    · exact ⟨bound, holds, fun other smaller valid => earlier ⟨other, smaller, valid⟩⟩

 theorem inverse_exists (n : Nat) :
    ∃ level, (0 < level ∧ n < ack level 1) ∧
      ∀ other, other < level → ¬ (0 < other ∧ n < ack other 1) := by
  apply least_exists
  refine ⟨n + 1, by omega, ?_⟩
  have := index_bound (n + 1)
  omega

/-- Least positive level whose Ackermann value at one exceeds the input. -/
noncomputable def alpha (n : Nat) : Nat := Classical.choose (inverse_exists n)





















end Algo2Lean.Ackermann


