-- Prove2me | Definitions.Def_TIESharp_SlotFeasible
-- name    : TIESharp_SlotFeasible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:39:58.985449+00:00
-- url     : https://prove2.me/theorems/b061114e-1054-41d4-8584-36bea5ca6975
-- title:
--   Slot-feasible assignment (induced by a perfect matching of the slot matrix)
-- statement:
--   An assignment $A$ is **slot-feasible** if it is induced by a perfect matching of the slot matrix supported on positive entries, after unit dummy rows have filled the slot deficits: at every machine $i$ the jobs $A$ sends to $i$ can be matched to distinct slots of $i$,
--   1. each job to a slot it overlaps with positive length,
--   2. distinct jobs to distinct slots,
--   3. so that every **full** slot of $i$ (total job overlap one) receives a job.
--
--   Each real job goes to the machine that owns its matched slot. Every assignment in the support of any decomposition of the slot matrix into perfect matchings (Sec. 5.2) is slot-feasible.
--
--   **Formalization Note.** Dummy rows have entries only in slots with a deficit, so full slots are matched to real jobs while a deficit slot may be matched to a dummy.
-- source:
--   Li, Sharp Bounds for Truthful-in-Expectation Scheduling, arXiv:2611.05134 (held version, sha256 e611c390…b70e5481), §3.2, p.10; §5.2, p.23

import Mathlib
import Definitions.Def_TIESharp_overlap

set_option autoImplicit false

namespace TIESharp

/-- An assignment is **slot-feasible** (Li, *Sharp Bounds for Truthful-in-Expectation
Scheduling*, arXiv:2611.05134, §3.2, p.10, and §5.2, p.23): it is induced by a perfect matching of
the slot matrix supported on its positive entries, after `K − m` unit dummy rows have filled the
deficits. At every machine `i` there is a choice of slots `σ` for the jobs `A` sends to `i` such
that
1. each such job overlaps its slot with positive length,
2. distinct such jobs get distinct slots,
3. every full slot of `i` (total job overlap one, hence no dummy entry) is taken by such a job.
"Each real job goes to the machine that owns its matched slot."

**Formalization Note.** Dummy rows have entries only in slots with a deficit, so a full slot is
matched to a real job; a slot with a deficit (only a machine's last slot) may be matched to a
dummy. Every assignment drawn from any Hall/Birkhoff decomposition of Sec. 5.2 is slot-feasible. -/
def SlotFeasible {n m : ℕ} (t : Fin n → Fin m → ℝ) (A : Fin m → Fin n) : Prop :=
  ∀ i : Fin n, ∃ σ : Fin m → ℕ,
    (∀ j, A j = i → 0 < overlap t i j (σ j)) ∧
    Set.InjOn σ {j | A j = i} ∧
    (∀ k : ℕ, ∑ j, overlap t i j k = 1 → ∃ j, A j = i ∧ σ j = k)

end TIESharp


