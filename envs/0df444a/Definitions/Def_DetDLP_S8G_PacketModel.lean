-- Prove2me | Definitions.Def_DetDLP_S8G_PacketModel
-- name    : DetDLP_S8G_PacketModel
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-25T00:18:55.000806+00:00
-- url     : https://prove2.me/theorems/19143042-f36c-40d6-ab88-d5311058698e
-- title:
--   S8G Packet Model
-- statement:
--   Packet model and correctness theorem
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8G_PacketCode_v2
import Definitions.Def_DetDLP_S8G_ChainSpec
import Definitions.Def_DetDLP_S8G_AnchoredBank
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 300000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace DetDLP.S8G.MakePacket
open DetDLP.S8G.MakePacketV2
open S8H S8H0 RegisterMap NamedBlocks RangeRows GateRoutes HashRows SeedAndAtomBank Routes
open S8H.PointAddresses S8J.CircuitRealizes S8H.MakeCombinators FpMoment.Code M89S1 S8C Groundwork FpAtomRows ResidueWires

/-- Abstract offset lemmas keep the expensive graph edge count opaque. -/
theorem atoms_at {j : Fin 4} {m d e : ℕ} (k : Fin (copies j)) (i : Fin m)
    (b : Addr (atomSlot d e)) :
    (atoms k (.vec i b)).index.val = m*(seedSlot d).size + k.val*(m*(atomSlot d e).size) +
      i.val*(atomSlot d e).size + b.index.val := by
  change (Addr.snd (Addr.fst (Addr.vec k (Addr.vec i b)))).index.val = _
  rw [idxR, idxL, idxV, idxV]
  simp [Shape.size, seedShape, seedSlot, atomBankShape, atomSlot, triple, run, auxShape, RegisterMap.mul]
  ring_nf

theorem coeffA_names {j : Fin 4} {m d e : ℕ} (i : Fin m) :
    Names (s:=Routes.bank j m d e)
      (bus d (Routes.bank j m d e).size (i.val*(seedSlot d).size+2*(triple d).size))
      (Routes.coeffA (j:=j) (m:=m) (d:=d) (e:=e) i) := by
  unfold Names; intro b
  by_cases hb : b < d
  · simp only [bus,hb,if_true,coeffA,seedA,word,padded,dif_pos,seeds]
    rw [srcR, idxL, idxV, idxR, idxR, idxL, idxW]
    simp only [seedSlot,triple,Shape.size]; ring
  · simp [bus,hb,coeffA,seedA,word,padded,srcP]

theorem coeffB_names {j : Fin 4} {m d e : ℕ} (i : Fin m) :
    Names (s:=Routes.bank j m d e)
      (bus d (Routes.bank j m d e).size (i.val*(seedSlot d).size+(triple d).size))
      (Routes.coeffB (j:=j) (m:=m) (d:=d) (e:=e) i) := by
  unfold Names; intro b
  by_cases hb : b < d
  · simp only [bus,hb,if_true,coeffB,seedB,word,padded,dif_pos,seeds]
    rw [srcR, idxL, idxV, idxR, idxL, idxL, idxW]
    simp only [seedSlot,triple,Shape.size]; ring
  · simp [bus,hb,coeffB,seedB,word,padded,srcP]

theorem result_at {j : Fin 4} {m d e : ℕ} (l : Fin (outputs j)) (a : Addr (triple d)) :
    (Routes.result (j:=j) (m:=m) (d:=d) (e:=e) l a).index.val = m*(seedSlot d).size + copies j*(m*(atomSlot d e).size) +
      l.val*((triple d).size+copies j*(chainShape (m-1) d e).size) + a.index.val := by
  change (Addr.snd (Addr.snd (Addr.vec l (Addr.fst a)))).index.val = _
  rw [idxR, idxR, idxV, idxL]
  simp only [productShape, seedShape, atomBankShape, Shape.size]
  ring

theorem stages_at {j : Fin 4} {m d e : ℕ} (l : Fin (outputs j)) (k : Fin (copies j))
    (a : Addr (chainShape (m-1) d e)) :
    (stages l k a).index.val = m*(seedSlot d).size + copies j*(m*(atomSlot d e).size) +
      l.val*((triple d).size+copies j*(chainShape (m-1) d e).size) + (triple d).size +
      k.val*(chainShape (m-1) d e).size + a.index.val := by
  change (Addr.snd (Addr.snd (Addr.vec l (Addr.snd (Addr.vec k a))))).index.val = _
  rw [idxR, idxR, idxV, idxR, idxV]
  simp only [productShape, seedShape, atomBankShape, Shape.size]
  ring

theorem result_names {j : Fin 4} {m d e : ℕ} (l : Fin (outputs j)) :
    Names (s:=Routes.bank j m d e)
      (bus d (Routes.bank j m d e).size
        (m*(seedSlot d).size+copies j*(m*(atomSlot d e).size)+l.val*((triple d).size+copies j*(chainShape (m-1) d e).size)))
      (residueWord (Routes.result (j:=j) (m:=m) (d:=d) (e:=e) l)) := by
  unfold Names; intro b
  by_cases hb : b < d
  · have h := result_at (j:=j) (m:=m) (d:=d) (e:=e) l (.fst (.word ⟨b,hb⟩))
    simp only [bus,hb,if_true,residueWord,word,padded,dif_pos]; rw [srcR]
    exact h.symm
  · simp [bus,hb,residueWord,word,padded,srcP]

theorem atom_names {j : Fin 4} {m d e : ℕ} (k : Fin (copies j)) (i : Fin m) :
    Names (s:=Routes.bank j m d e)
      (bus d (Routes.bank j m d e).size
        (m*(seedSlot d).size+k.val*(m*(atomSlot d e).size)+i.val*(atomSlot d e).size))
      (Routes.atom (j:=j) (m:=m) (d:=d) (e:=e) k i) := by
  unfold Names; intro b
  by_cases hb : b < d
  · have h := atoms_at (j:=j) (m:=m) (d:=d) (e:=e) k i (.fst (.fst (.word ⟨b,hb⟩)))
    simp only [bus,hb,if_true,atom,residueWord,word,padded,dif_pos]; rw [srcR]
    exact h.symm
  · simp [bus,hb,atom,residueWord,word,padded,srcP]

theorem initial_names {j : Fin 4} {m d e : ℕ} (hm : 0 < m) (k : Fin (copies j)) :
    Names (s:=Routes.bank j m d e)
      (bus d (Routes.bank j m d e).size
        (m*(seedSlot d).size+k.val*(m*(atomSlot d e).size)))
      (Routes.initial (j:=j) (m:=m) (d:=d) (e:=e) k) := by
  simp only [initial,hm,dif_pos]
  simpa using atom_names (j:=j) (m:=m) (d:=d) (e:=e) k ⟨0,hm⟩

theorem tail_names {j : Fin 4} {m d e : ℕ} (k : Fin (copies j)) (i : Fin (m-1)) :
    Names (s:=Routes.bank j m d e)
      (bus d (Routes.bank j m d e).size
        (m*(seedSlot d).size+k.val*(m*(atomSlot d e).size)+(i.val+1)*(atomSlot d e).size))
      (Routes.tail (j:=j) (m:=m) (d:=d) (e:=e) k i) := by
  simpa [tail] using atom_names (j:=j) (m:=m) (d:=d) (e:=e) k ⟨i.val+1, by omega⟩

theorem result_check_spec {j : Fin 4} {m d e : ℕ} (p : ℕ) (l : Fin (outputs j)) :
    let z := m*(seedSlot d).size + copies j*(m*(atomSlot d e).size) +
      l.val*((triple d).size + copies j*(chainShape (m-1) d e).size)
    Fits (checkN d (Routes.bank j m d e).size z (z+d) (z+2*d))
      (checker p (Routes.result (j:=j) (m:=m) (d:=d) (e:=e) l)) := by
  dsimp only; apply col_spec
  · intro b; by_cases hb : b.val < d
    · simp only [bus,pad,hb,if_true,dif_pos]; rw [srcR, result_at]; rfl
    · simp [bus,pad,hb,srcP]
  · intro b; by_cases hb : b.val < d
    · simp only [bus,pad,hb,if_true,dif_pos]; rw [srcR, result_at, idxR, idxL, idxW]; simp only [triple,Shape.size]; omega
    · simp [bus,pad,hb,srcP]
  · intro b; simp [srcP]
  · intro b; rw [srcR, result_at, idxR, idxR, idxW]; simp only [triple,Shape.size]; omega

theorem tree_fit (p m : ℕ) (hm : 0 < m) (j : Fin 4) (T : ℕ) (η : List Bool) :
    Fits (MakePacketV2.tree m (bitLen p+1) (edges (Nat.succ_pos (bitLen p))) (copies j) (outputs j) η.length) (anchored (Semantics.net p m j T η)) := by
  let d := bitLen p+1
  let hd : 1 ≤ d := Nat.succ_pos _
  let e := edges hd
  let s := Routes.bank j m d e
  let t := (triple d).size
  let u := (seedSlot d).size
  let v := (atomSlot d e).size
  let w := (chainShape (m-1) d e).size
  let o := m*u
  let r := o+copies j*(m*v)
  unfold MakePacketV2.tree Semantics.net Routes.network atomBankBlock
  dsimp only
  apply anchors_fit
  apply cat_spec
  · exact ⟨⟨rfl,rfl,rfl,fun _ => rfl,fun _ => rfl⟩,fun _ => rfl⟩
  · apply cat_spec
    · apply seed_spec (s:=s) (m:=m) p η Routes.seeds
      intro a
      change (Addr.fst a).index.val = (0 : ℕ) + a.index.val
      rw [idxL]
      omega
    · apply cat_spec
      · apply (all_spec (s:=s) (n:=copies j)); intro k
        apply (all_spec (s:=s) (n:=m)); intro i
        refine atom_spec (s:=s) (d:=d) hd p T (o+k*(m*v)+i*v) (i*u+2*t) (i*u+t)
          (coeffA i) (coeffB i) (fun a => atoms k (.vec i a)) ?_ ?_ ?_
        · intro b
          dsimp only [At,o,u,v,t,e]
          simpa only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
            (atoms_at (e:=edges hd) k i b)
        · exact coeffA_names (e:=edges hd) i
        · exact coeffB_names (e:=edges hd) i
      · apply (all_spec (s:=s) (n:=outputs j)); intro l; apply cat_spec
        · exact result_check_spec (e:=edges hd) p l
        · apply (all_spec (s:=s) (n:=copies j)); intro k
          refine chain_spec (s:=s) (d:=d) hd p m (r+l*(t+copies j*w)+t+k*w) (o+k*(m*v)) (r+l*(t+copies j*w)) (stages l k) (initial k) (residueWord (result l)) (tail k) ?_ ?_ ?_ ?_
          · intro b
            dsimp only [At,r,o,t,w,u,v,e]
            exact stages_at (e:=edges hd) l k b
          · exact initial_names (e:=edges hd) hm k
          · exact result_names (e:=edges hd) l
          · intro i
            exact tail_names (e:=edges hd) k i

def packetCode (p m : ℕ) (j : Fin 4) (T : ℕ) (η : List Bool) : NC :=
  let b := tree m (bitLen p+1) (edges (Nat.succ_pos (bitLen p))) (copies j) (outputs j) η.length
  (CycleCode.code b.1 b.2, b.2)

theorem packet_models (p m : ℕ) (hm : 0 < m) (j : Fin 4) (T : ℕ) (η : List Bool) :
    Models (packetCode p m j T η).1 (Semantics.layout p m j T η) := by
  let b := tree m (bitLen p+1) (edges (Nat.succ_pos (bitLen p))) (copies j) (outputs j) η.length
  let n := Semantics.net p m j T η
  have F := tree_fit p m hm j T η
  have N (i : Fin (anchored n).core.A.ne) : b.2 i = (AnchoredLayout.signal n.core n.name i).val := F.2 i
  have M := CycleCode.models F.1 b.2
  have k := AnchoredLayout.next_congr (fun i : Fin (anchored n).core.A.ne => b.2 i) (AnchoredLayout.signal n.core n.name) (by intro i j; rw [N,N]; exact Fin.val_inj)
  rw [k] at M; exact M

theorem signal_agrees (p m : ℕ) (hm : 0 < m) (j : Fin 4) (T : ℕ) (η : List Bool)
    (i : Fin (Semantics.layout p m j T η).nb) : (packetCode p m j T η).2 i =
      (AnchoredLayout.signal (Semantics.net p m j T η).core (Semantics.net p m j T η).name i).val :=
  (tree_fit p m hm j T η).2 i

end DetDLP.S8G.MakePacket


