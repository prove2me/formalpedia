-- Prove2me | Definitions.Def_DetDLP_S8M_AtomBasePortFits
-- name    : DetDLP_S8M_AtomBasePortFits
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-25T03:02:59.073231+00:00
-- url     : https://prove2.me/theorems/02ddc4d9-e191-4680-b746-15302b8ca01b
-- title:
--   Tag 6 base atom port fit
-- statement:
--   The base atom port evaluator satisfies the required local port-fit properties for the Tag 6 construction.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8M_PortPoly
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace DetDLP.S8M.PortEval
open S8H0 S8H.PortCombinators S8J S8J.CircuitRealizes NamedBlocks RegisterMap GateRoutes LocalGateEq PortPoly
variable {s : Shape} {d : ℕ}
theorem tile_one {k : ℕ} {g : GC} {A : B k} (h : FitsG g A.core) : FitsG (tile 1 g) A.core := by
  refine ⟨by simp [tile,tab,h.1],fun i w => ?_⟩; simpa only [tile,tab,Nat.mod_eq_of_lt (show i.val < g.1 by rw [h.1]; exact i.isLt)] using h.2 i w
theorem tiles_join {k n m : ℕ} {g : GC} {A B : NamedBlocks.B k} (ha : FitsG (tile n g) A.core) (hb : FitsG (tile m g) B.core) : FitsG (tile (n+m) g) (joinB A B).core := by
  have H := catB ha hb; refine ⟨by simpa only [tile,tab,catG,Nat.add_mul] using H.1,fun i w => ?_⟩
  rw [← H.2]; simp only [catG,tile,tab]; split_ifs with h
  · simp [h]
  · obtain ⟨j,hj⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt h); rw [hj]; simp [Nat.add_mod]
theorem tile_many {k n t : ℕ} {g : GC} (b : Fin (n+1) → B k) (h : ∀ i, FitsG (tile t g) (b i).core) : FitsG (tile ((n+1)*t) g) (RangeRows.many n b).core := by
  induction n with
  | zero => simpa [RangeRows.many] using h 0
  | succ n ih => rw [Nat.succ_mul,Nat.add_comm]; exact tiles_join (h 0) (ih (fun i => b i.succ) (fun i => h i.succ))
end DetDLP.S8M.PortEval


