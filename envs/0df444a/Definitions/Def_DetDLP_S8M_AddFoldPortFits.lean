-- Prove2me | Definitions.Def_DetDLP_S8M_AddFoldPortFits
-- name    : DetDLP_S8M_AddFoldPortFits
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-25T05:15:06.506335+00:00
-- url     : https://prove2.me/theorems/de72dea9-33b4-5dab-a46b-70fd1695a5f5

import Definitions.Def_DetDLP_S8M_AtomMapPortFits
import Definitions.Def_DetDLP_S8N_ECAddRoutes
import Definitions.Def_DetDLP_S8M_ECFoldRoutes
import Definitions.Def_DetDLP_S8M_Routes
set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace DetDLP.S8M.PortEval
open S8H0 S8H.PortCombinators S8J S8J.CircuitRealizes NamedBlocks RegisterMap GateRoutes LocalGateEq PortPoly S8N
open private ECAddRoutes.gw ECAddRoutes.invRows ECAddRoutes.selectRows ECAddRoutes.rwrd from Definitions.Def_DetDLP_S8N_ECAddRoutes
variable {s : Shape} {d : ℕ}
private theorem splitTile (n m : ℕ) (g : GC) : tile (n+m) g = catG (tile n g) (tile m g) := by
  apply Prod.ext (Nat.add_mul ..); funext i w; simp only [tile,tab,catG]; split_ifs with h
  · rfl
  · obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt h); simp [Nat.add_mod]
private theorem assocG (a b c : GC) : catG (catG a b) c = catG a (catG b c) := by
  apply Prod.ext (Nat.add_assoc ..); funext i w; simp only [catG]; by_cases ha : i < a.1
  · simp [ha,show i<a.1+b.1 by omega]
  · by_cases hb : i < a.1+b.1
    · simp [ha,hb,show i-a.1<b.1 by omega]
    · simp [ha,hb,show ¬i-a.1<b.1 by omega,Nat.sub_sub]
private theorem pinReads (k : ℕ) : Reads (rd d (k+1)) (HashRows.pub (s:=s) k) := fun _ _ => rfl
private theorem readIn {w : HashRows.Word s} (hw : Reads (regR d) w) (i : Fin d) (b : Bool) : (w i).read b = b := by rw [←hw]; simp [regR,i.isLt]
theorem addStepFits (hd : 1 ≤ d) (p c : ℕ) (f g : Ref s) (x y X Y : HashRows.Word s) (q : Path (ECAddRoutes.addShape d (edges hd)) s) (hf : ∀ z, f.read z = z) (hg : ∀ z, g.read z = z) (hx : Reads (regR d) x) (hy : Reads (regR d) y) (hX : Reads (regR d) X) (hY : Reads (regR d) Y) : FitsG (addStepG (List.replicate d ()) d p c) (ECAddRoutes.addBlock hd p (p-1) (3%p) c f x y g X Y q).core := by
  unfold addStepG ECAddRoutes.addBlock; dsimp only
  rw [show 34=4+30 by decide,splitTile,assocG]; refine catB (tile_many (n:=3) (t:=1) _ fun _ => tile_one (range_spec ..)) (catB (tile_many (n:=14) (t:=2) _ fun _ => tiles_join (n:=1) (m:=1) (tile_one (range_spec ..)) (tile_one (range_spec ..))) (catB (many_spec fun i => ?_) ?_))
  · apply hashFits hd <;> fin_cases i <;> first | apply pinReads | exact hx | exact hy | exact hX | exact hY | apply wordReads
  · rw [splitTile 1 1,assocG]; refine catB (tile_one ?_) (catB (tile_one ?_) (catB ?_ (catB ?_ (tiles_join (n:=1) (m:=1) (tile_one ?_) (tile_one ?_)))))
    all_goals refine ⟨rfl,fun i w => ?_⟩; simp only [ECAddRoutes.invRows,ECAddRoutes.selectRows,rows_local]; have hi : i.val < d := by first | exact i.isLt | have := i.isLt; change i.val < 1 at this; omega
    all_goals simp [ECAddRoutes.rwrd,ECAddRoutes.mux,ECAddRoutes.dest,GateRoutes.word,HashRows.padded,hi,bit,hf,hg,readIn hx,readIn hy,readIn hX,readIn hY] <;> rfl
theorem tile_all {n : ℕ} {g : GC} (a : Fin n → B (s.size+1)) (h : ∀ i, FitsG g (a i).core) : FitsG (tile n g) (S8G.SeedAndAtomBank.allRows (s:=s) n a).core := by
  cases n with
  | zero => exact ⟨Nat.zero_mul _,fun i => i.elim0⟩
  | succ n => unfold S8G.SeedAndAtomBank.allRows; simpa only [Nat.mul_one] using tile_many (t:=1) a (fun i => tile_one (h i))
open private foldStep outputFlag outputX outputY outX outY from Definitions.Def_DetDLP_S8M_ECFoldRoutes
theorem foldFits {m : ℕ} (hd : 1 ≤ d) (hm : 1 ≤ m) (p c : ℕ) (t : Routes.Target) : FitsG (foldG (2*m-1) d t.1 t.2.1 t.2.2 (addStepG (List.replicate d ()) d p c)) (Routes.foldRows hd hm p (p-1) (3%p) c t).core := by
  unfold foldG Routes.foldRows ECFoldRoutes.foldBlock; dsimp only; refine catB ?_ (catB ?_ (catB ?_ (tile_all _ fun i => ?_)))
  · refine ⟨rfl,fun i w => ?_⟩; rw [rows_local]; simp [outputFlag,show 2*m-1 ≠ 0 by omega,Ref.read,bit] <;> rfl
  · refine ⟨rfl,fun i w => ?_⟩; rw [rows_local]; have hi : i.val<d := i.isLt; simp [outputX,outX,show 2*m-1 ≠ 0 by omega,GateRoutes.word,HashRows.padded,hi,Ref.read,HashRows.pub,bit] <;> rfl
  · refine ⟨rfl,fun i w => ?_⟩; rw [rows_local]; have hi : i.val<d := i.isLt; simp [outputY,outY,show 2*m-1 ≠ 0 by omega,GateRoutes.word,HashRows.padded,hi,Ref.read,HashRows.pub,bit] <;> rfl
  · unfold foldStep; dsimp only; split <;> apply addStepFits <;> first | apply wordReads | intro z; rfl
end DetDLP.S8M.PortEval


