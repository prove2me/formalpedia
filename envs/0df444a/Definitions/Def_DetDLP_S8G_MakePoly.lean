-- Prove2me | Definitions.Def_DetDLP_S8G_MakePoly
-- name    : DetDLP_S8G_MakePoly
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-25T03:20:41.103399+00:00
-- url     : https://prove2.me/theorems/a90c0bde-7c79-4ace-9898-d24a1f6cb4c0

import Definitions.Def_DetDLP_S8G_SubEff
import Definitions.Def_DetDLP_S8G_PacketModel
import Definitions.Def_DetDLP_S8G_Bounds

set_option autoImplicit false
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace DetDLP.S8G.MakePacketV2
open S8H S8H0 RegisterMap NamedBlocks RangeRows GateRoutes HashRows SeedAndAtomBank Routes
open S8H.MakeCombinators FpMoment.Code M89S1 S8C Groundwork FpAtomRows ResidueWires

private def jOf (i : ℕ) : Fin 4 := if i = 0 then 0 else if i = 1 then 1 else if i = 3 then 3 else 2
private theorem copies_jOf (i : ℕ) : copies (jOf i) = min i 2 := by
  unfold jOf copies; split_ifs <;> simp [Fin.val_zero, Fin.val_one] <;> omega
private theorem outputs_jOf (i : ℕ) : outputs (jOf i) = (if i = 3 then 1 else 0) := by
  by_cases h0 : i = 0; · simp [jOf, h0, outputs]
  by_cases h1 : i = 1; · simp [jOf, h1, outputs]
  by_cases h3 : i = 3; · simp [jOf, h3, outputs]
  simp [jOf, h0, h1, h3, outputs]

private theorem tree_L_dims (m d e c v L : ℕ) :
    (tree m d e c v L).1.ng = (tree m d e c v 0).1.ng + L ∧
    (tree m d e c v L).1.ne = (tree m d e c v 0).1.ne + L := by
  simp only [tree, seedN, catN, PointAddresses.sum, rowN, BaseCode.rowsCode, Nat.mul_one, Nat.zero_mul, Nat.add_zero]
  omega

private def padBits (w : PacketWord) := (prime w - 1).bits ++ [false, false]
private def sqBits (w : PacketWord) := (padBits w).flatMap fun _ => padBits w
private def bigBound (w : PacketWord) := (sqBits w ++ pfx w).flatMap fun _ => List.replicate 1048576 ()

private theorem bigBound_poly : PolyT bigBound := by
  have hp : PolyT padBits := PolyT.append (PolyT.bits (PolyT.sub prime_poly (PolyT.const 1))) (PolyT.const _)
  have hs : PolyT sqBits := PolyT.flatMap (PolyT.comp hp (PolyT.fst PolyT.id')) hp
  exact PolyT.flatMap (PolyT.const _) (PolyT.append hs prefix_poly)

private theorem networkCode_bound (w : PacketWord) :
    let c := cycle (networkCode w)
    c.ng + c.nb + c.ne ≤ (bigBound w).length ∧ c.ne + c.ne ≤ (bigBound w).length := by
  dsimp only
  let p := prime w; let j := jOf (idx w); let l := (pfx w).length
  let m := blockCount (bitLen p)
  have hm : 0 < m := lt_of_lt_of_le (by decide : 0 < 2) (le_max_left ..)
  have hM := DetDLP.S8G.MakePacket.packet_models p m hm j 0 []
  have he := DetDLP.S8G.Bounds.edgeBudget p j 0 [] (Nat.zero_le _)
  have hg := DetDLP.S8G.Bounds.gateBudget p j 0 [] (Nat.zero_le _)
  rw [← hM.ng] at hg; rw [← hM.ne] at he
  have hnet : networkCode w = tree m (bitLen p + 1) (edges (Nat.succ_pos (bitLen p))) (copies j) (outputs j) l := by
    simp only [networkCode, p, m, j, l, width_eq, slots_eq, copies_jOf, outputs_jOf,
      PointAddresses.wires_eq (Nat.succ_pos (bitLen p)), edges]
  obtain ⟨hng, hne⟩ := tree_L_dims m (bitLen p + 1) (edges (Nat.succ_pos (bitLen p))) (copies j) (outputs j) l
  have hpkt : (DetDLP.S8G.MakePacket.packetCode p m j 0 []).1 =
      cycle (tree m (bitLen p + 1) (edges (Nat.succ_pos (bitLen p))) (copies j) (outputs j) 0) := rfl
  rw [hpkt] at hg he
  have hs : FpMoment.scale m (bitLen p) ≤ 65536 * ((bitLen p + 2) * (bitLen p + 2)) := by
    unfold FpMoment.scale; rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (FpMoment.blockUpper (bitLen p)))
  have hlen : (bigBound w).length = ((bitLen p + 2) * (bitLen p + 2) + l) * 1048576 := by
    have hpad : (padBits w).length = bitLen p + 2 := by
      have hw' := width_eq p; simp only [width] at hw'
      simp [padBits, p, ← hw']
    simp only [bigBound, sqBits, List.length_flatMap, List.length_replicate, List.map_const',
      List.sum_replicate_nat, List.length_append, Function.comp_def, hpad, l]
  rw [hnet, hlen, Nat.add_mul]
  dsimp only [m, p, l] at *
  simp only [cycle, CycleCode.code] at hg he ⊢
  rw [hng, hne]; constructor <;> omega

theorem make_poly : PolyT make :=
  fullMake_poly networkCode_eff networkCode_idx_eff sizeField_poly bigBound_poly networkCode_bound

theorem make_word (p : ℕ) (j : Fin 4) (T : ℕ) (η : List Bool) (hm : 0 < blockCount (bitLen p)) :
    make (FpMoment.word p j T η) = encodeBTNInstance (FpMoment.word p j T η)
      (w3_factorGraph (Semantics.layout p (blockCount (bitLen p)) j T η)).subdivision
      (FpMoment.scale (blockCount (bitLen p)) (bitLen p))
      (FpMoment.scale (blockCount (bitLen p)) (bitLen p)) 1 := by
  let w := FpMoment.word p j T η
  let n := Semantics.net p (blockCount (bitLen p)) j T η
  obtain ⟨hp, hj, _, hη⟩ := FpMoment.Code.fields p j T η
  have hcode : networkCode w =
      tree (blockCount (bitLen p)) (bitLen p + 1) (edges (Nat.succ_pos (bitLen p))) (copies j) (outputs j) η.length := by
    have hj' : jOf (idx w) = j := by
      rw [hj]; fin_cases j <;> decide
    have hc : min (idx w) 2 = copies j := by rw [← copies_jOf, hj']
    have ho : (if idx w = 3 then 1 else 0) = outputs j := by rw [← outputs_jOf, hj']
    simp only [networkCode, w, hp, hη, width_eq, slots_eq, hc, ho,
      PointAddresses.wires_eq (Nat.succ_pos (bitLen p)), edges]
  have hf : Fits (networkCode w) (anchored n) := by
    rw [hcode]; exact DetDLP.S8G.MakePacket.tree_fit p (blockCount (bitLen p)) hm j T η
  have hspec := fullMake_spec (F := networkCode) (s := sizeField) (w := w) (u := anchored n) hf
  rw [FpMoment.Code.sizeField_word p j T η] at hspec
  exact hspec

end DetDLP.S8G.MakePacketV2


