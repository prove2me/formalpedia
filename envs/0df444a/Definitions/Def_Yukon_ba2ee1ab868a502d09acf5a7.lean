-- Prove2me | Definitions.Def_Yukon_ba2ee1ab868a502d09acf5a7
-- name    : Yukon_ba2ee1ab868a502d09acf5a7
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-03T03:15:53.996128+00:00
-- url     : https://prove2.me/theorems/9ca7edff-d412-4ef4-b7df-8548962b45ee
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.MovingSourcePacket6814.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.MovingSourcePacket6814.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/MovingSourcePacket6814.lean
--
--   yukon-proof-operation:certificate-b56-4f8668d5520d4e72c9cdbdbf58b7a22d593e0d42e2c1a011b9417fef1ba0b75c
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiYWRlNGM1MTZmZDZjM2E2OTY3MWVkN2NiMTEwNDE3YjgzMTcyNzZjMTVjZTM4NjYzMjI2YzQxMDQyZDFiZDJhNCIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLWI1Ni00Zjg2NjhkNTUyMGQ0ZTcyYzljZGJkYmY1OGI3YTIyZDU5M2UwZDQyZTJjMWEwMTFiOTQxN2ZlZjFiYTBiNzVjIiwidGFnIjoiYmV0dGVyLWNvZGVzIiwidGFyZ2V0IjoiWXVrb25fYmEyZWUxYWI4NjhhNTAyZDA5YWNmNWE3IiwidiI6Mn0]

import Definitions.Def_Yukon_470e6b3ad95913c90c8c44d8













































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-! Assemble the actual source alternative and the standard small-degree
projection suppliers into the regular moving-family endpoint. -/
namespace ProximityPrize.SubmissionLower.MovingSourcePacket6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2500000
open MvPolynomial RCN002 RCN003 RCN037 RCN042 RCN046 RCN084 RCN095 RCN135 RCN136 RCN234 RCN156 RCN264 RCN341
open WholeSpaceCube6814 WholeSpaceCubeUniform6814 WholeSpaceSourceAlternative6814
open MovingSourceCarrierField6814 MovingSourceGeometricBudget6814

theorem exists_projection_data
    {E : Type} [Field E] [IsAlgClosed E]
    (G H R : MvPolynomial (Fin 3) E) (hG : Irreducible G) (hproper : ¬G∣H)
    (p q : FlagDegree) (hp : PolynomialInFlag p G) (hq : PolynomialInFlag q H)
    (c : ℕ) [CharP E c] (hdeg : p.zOnly+p.yz+p.all<c)
    (hmix : 2*(p.zOnly+p.yz+p.all)*(q.zOnly+q.yz+q.all)<c) :
    ∃ base : ∀ C : RegularComponent E G H R, SeparableLiteralCoordinate C.1,
      (∀ C : RegularComponent E G H R, LiteralProjectionGate C 0) ∧
      (∀ C : RegularComponent E G H R, LiteralProjectionGate C 2) := by
  have hgate (C : RegularComponent E G H R) (i : Fin 3)
      (hi : Transcendental E (coordinate E C.1 i)) := by
    have hgdeg (j : Fin 3) : G.degreeOf j≤p.zOnly+p.yz+p.all := degreeOf_le_flag_total G p hp j
    have hhdeg (j : Fin 3) : H.degreeOf j≤q.zOnly+q.yz+q.all := degreeOf_le_flag_total H q hq j
    have hprod (u v : Fin 3) : H.degreeOf u*G.degreeOf v+G.degreeOf u*H.degreeOf v < c := by
      calc
        _ ≤ (q.zOnly+q.yz+q.all)*(p.zOnly+p.yz+p.all)+
            (p.zOnly+p.yz+p.all)*(q.zOnly+q.yz+q.all) :=
          Nat.add_le_add (Nat.mul_le_mul (hhdeg u) (hgdeg v))
            (Nat.mul_le_mul (hgdeg u) (hhdeg v))
        _ = 2*(p.zOnly+p.yz+p.all)*(q.zOnly+q.yz+q.all) := by ring
        _ < c := hmix
    apply finite_separable_at_of_original_coordinate_gate E C.1 i hi c G H hG
      (regularComponent_G_mem E G H R C) (regularComponent_T_mem E G H R C)
      hproper (fun j => (hgdeg j).trans_lt hdeg)
    have hi3 : i=0 ∨ i=1 ∨ i=2 := by omega
    rcases hi3 with rfl | rfl | rfl
    · rw [RCN001.coordinateMixedDegree_zero]; exact hprod 1 2
    · rw [RCN001.coordinateMixedDegree_one]; exact hprod 0 2
    · rw [RCN001.coordinateMixedDegree_two]; exact hprod 0 1
  refine ⟨fun C => Classical.choice (exists_separableLiteralCoordinate_of_YZ_gates C.1
    (regularComponent_ne_point E G H R C) (hgate C 0) (hgate C 2)),?_,?_⟩
  · exact fun C => hgate C 0
  · exact fun C => hgate C 2

variable {K N : Type} [Field K] [CharP K 2130706433] [Fintype N]
local notation "Omega" => GenericField K
local notation "OmegaT" => GenericField (GenericField K)
local notation "phi" => RingHom.comp (coefficientEmbedding (GenericField K)) (polynomialEmbedding K)








end
end ProximityPrize.SubmissionLower.MovingSourcePacket6814


