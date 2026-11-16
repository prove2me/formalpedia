-- Prove2me | Definitions.Def_SublinearChoresMMS_Disposal_Supplement_TailRounding
-- name    : SublinearChoresMMS_Disposal_Supplement_TailRounding
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:00:08.508332+00:00
-- url     : https://prove2.me/theorems/05f249e3-86af-46ce-83de-6ea951c50fe0
-- title:
--   Tail slots and fixed-bundle preservation
-- statement:
--   Only the fractional shares of $V$ are placed, in their common cost order, into consecutive unit slots. For agent $i$ the fractional row is $t_i\mathbf1_V$; its slot masses are the published interval-intersection formula.
--
--   A tail rounding assigns every tail chore to a positive-mass slot, uses each tail slot at most once, and fills each full tail slot. Every fixed bundle remains with its Algorithm 1 owner. This is a structural matching interface; it contains no MMS or proportionality conclusion. Slots assigned to fixed chores serve only to record their owner and do not consume tail-slot capacity.
--
--   **Formalization Note** The finite slot carrier has $m+1$ slots per agent; surplus empty slots have zero marginal and receive no tail chore.
-- source:
--   Zehan Lin, Xiaowei Wu, Shengwei Zhou, STOC 2027 submission #845 (October 2026), Section 4 tail rounding, printed p. 16 / PDF p. 17. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/845.pdf General slot formula: Section 3.3, printed p. 11 / PDF p. 12.

import Mathlib
import Definitions.Def_SublinearChoresMMS_Disposal_Supplement_FixedBundles
import Definitions.Def_SublinearChoresMMS_Disposal_Slots

noncomputable section

namespace SublinearChoresMMS.Disposal.Supplement

attribute [local instance] Classical.propDecidable

/-- Section 4, printed 16 / PDF 17: only fractions of V are sorted into unit slots.
Fixed bundles are kept intact, outside these tail slots. -/
def tailSlot {n m : ℕ} (V : Finset (Fin m)) (z : Completion n)
    (s : Slots n m) (e : Fin m) : ℝ :=
  generalSlot (fun g => if g ∈ V then z.tail s.1 else 0) e s.2.val

/-- An integral tail matching together with preservation of the assigned fixed bundles.
No MMS or proportionality bound is included here. -/
def RoundsTail {n m : ℕ} (Q : Fin n → Finset (Fin m))
    (V : Finset (Fin m)) (z : Completion n) (A : SlotAssignment n m) : Prop :=
  Complete z ∧
  (∀ i, assignedBundle Q z i ⊆ bundle (fun e => (A e).1) i) ∧
  (∀ e ∈ V, 0 < tailSlot V z (A e) e) ∧
  Set.InjOn A (↑V : Set (Fin m)) ∧
  (∀ s : Slots n m, slotLoad (tailSlot V z) s = 1 → ∃ e ∈ V, A e = s)

end SublinearChoresMMS.Disposal.Supplement


