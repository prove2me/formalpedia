-- Prove2me | Definitions.Def_DetDLP_S8M_PortBankRows
-- name    : DetDLP_S8M_PortBankRows
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-25T05:56:59.650976+00:00
-- url     : https://prove2.me/theorems/b73b80c4-f139-5d6c-9880-0b04b6339b9b
-- title:
--   Tag 6 atom and map bank rows
-- statement:
--   Proves that the tabulated atom gates and tiled map gates fit the corresponding rows of the Tag 6 bank.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8M_SubPortFits
import Definitions.Def_DetDLP_S8M_MapPortFits
import Definitions.Def_DetDLP_S8M_PortFields
set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace DetDLP.S8M.PortEval
open S8H0 S8H.PortCombinators S8J S8J.CircuitRealizes NamedBlocks RegisterMap GateRoutes RangeRows PortPoly M89S1
variable {p m : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) (T : ℕ) (S : ECSeed p m) (η : List Bool)
local notation "d" => GateSemantics.d p
local notation "hd" => GateSemantics.hd p
local notation "atom" => atomFixed (List.replicate d ()) d p T (GateSemantics.coeff E)
include η in
theorem atomBankFits : FitsG (tab (2*m) (fun j => atomG atom (bitLen p) d m j (List.ofFn (ecBits S))))
    (S8G.SeedAndAtomBank.allRows (2*m) (Routes.atomRows hd p T (GateSemantics.coeff E) (Semantics.seed S))).core := by
  apply tabAll (c:=atom.1+d) (Nat.add_pos_right _ hd) _ _ (fun _ => rfl)
  intro i
  have h := atomFits hd p T (bitLen p) m i.val (GateSemantics.coeff E) (List.ofFn (ecBits S)) (Routes.A i)
  dsimp only at h
  have co (k : Fin 4) : coord (List.ofFn (ecBits S)) (bitLen p) ((i.val%m)*4+k.val) = ecWords S (Routes.idx i) k :=
    coord_eq E T S η (Routes.idx i) k
  rw [co ⟨0,by decide⟩,co ⟨1,by decide⟩,co ⟨2,by decide⟩,co ⟨3,by decide⟩] at h
  exact h

theorem mapBankFits : FitsG (tile (2*m) (mapG (List.replicate d ()) d p E.b₂.val E.a₁.val E.a₃.val))
    (S8G.SeedAndAtomBank.allRows (2*m) (Routes.mapRows hd p E.b₂.val E.a₁.val E.a₃.val)).core := by
  apply tile_all
  intro i
  exact mapFits hd p E.b₂.val E.a₁.val E.a₃.val (Routes.atomW i).1 (Routes.atomW i).2.1 (Routes.atomW i).2.2 (Routes.M i) (fun _ => rfl) (wordReads (fun j => Routes.A i (.fst (xa (.fst j))))) (wordReads (fun j => Routes.A i (.fst (ya (.fst j)))))
end DetDLP.S8M.PortEval


