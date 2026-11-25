-- Prove2me | Definitions.Def_DetDLP_S8H0_ResidueWires
-- name    : DetDLP_S8H0_ResidueWires
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T06:56:08.866273+00:00
-- url     : https://prove2.me/theorems/6388d617-9625-458d-b89b-c1967a87a2d4
-- title:
--   Canonical residue wires with a unique comparison certificate
-- statement:
--   A triple of little-endian Boolean words stores a field representative, the difference to the modulus minus one, and the carries of a fixed addition layout. Its accepted assignments correspond bijectively to residues below the modulus. The value word retains its little-endian bit ordering under the equivalence.
-- source:
--   DetDLP S8H0 seven-check compiler, companion to f0e81f0e-6143-4672-a126-0c2b5aa2d552.

import Definitions.Def_DetDLP_S8H0_SevenChecks

set_option autoImplicit false
namespace DetDLP.S8H0.ResidueWires
open S8J S8J.HashGateLayout S8H.ECPointArithmetic S8H.ECPointSlots SevenChecks

abbrev Bits (d : ℕ) := Fin d → Bool

def value {d : ℕ} (w : Bits d) : Fin (2^d) :=
  ⟨(BitVec.ofBoolListLE (List.ofFn w)).toNat,by simpa using (BitVec.ofBoolListLE (List.ofFn w)).isLt⟩

@[simp] theorem value_bit {d : ℕ} (w : Bits d) (i : Fin d) : (value w).val.testBit i.val = w i := by
  change (BitVec.ofBoolListLE (List.ofFn w)).toNat.testBit _ = _
  rw [BitVec.testBit_toNat,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD]
  simp [i.isLt]

def numBits (d : ℕ) : Bits d ≃ Fin (2^d) where
  toFun := value
  invFun n := fun i => n.val.testBit i.val
  left_inv w := funext (value_bit w)
  right_inv n := by
    apply Fin.ext; apply Nat.eq_of_testBit_eq; intro k
    by_cases hk : k < d
    · exact value_bit _ ⟨k,hk⟩
    · have hp : 2^d ≤ 2^k := Nat.pow_le_pow_right (by decide) (by omega)
      rw [Nat.testBit_lt_two_pow ((value _).isLt.trans_le hp),Nat.testBit_lt_two_pow (n.isLt.trans_le hp)]

abbrev Triple (d : ℕ) := Bits d × Bits d × Bits (d+1)

def below {d : ℕ} (p : ℕ) (w : Triple d) :=
  Accept (S8C.AddLayout.layout (d+1)) (S8C.AddLayout.test true)
    (addBits (value w.1).val (value w.2.1).val p w.2.2)

theorem below_iff {d : ℕ} (p : ℕ) (w : Triple d) :
    below p w ↔ w3_slotLt d (value w.1).val p (value w.2.1,w.2.2) := addBits_iff (by omega) ..

noncomputable def finEquiv {d p : ℕ} (hp : p ≤ 2^d) : {w : Triple d // below p w} ≃ Fin p := by
  let lift (w : Bits d) := w3_slotLt_spec (value w).isLt hp
  let f (u : {w : Triple d // below p w}) : Fin p :=
    ⟨(value u.val.1).val,(lift u.val.1).1 _ ((below_iff p u.val).mp u.property)⟩
  apply Equiv.ofBijective f
  constructor
  · rintro ⟨⟨a,b,c⟩,hu⟩ ⟨⟨a',b',c'⟩,hv⟩ he
    have hev := congrArg (Fin.val (n := p)) he
    have ha : a = a' := (numBits d).injective (Fin.ext hev)
    subst a'
    have h1 := (below_iff p (a,b,c)).mp hu
    have h2 := (below_iff p (a,b',c')).mp hv
    have h := ((lift a).2 ((lift a).1 _ h1)).unique h1 h2
    have hb : value b = value b' := congrArg Prod.fst h
    have hcc : c = c' := congrArg (fun x : w3_slotDiff d => x.2) h
    exact Subtype.ext (Prod.ext rfl (Prod.ext ((numBits d).injective hb) hcc))
  · intro r
    let v : Fin (2^d) := ⟨r.val,r.isLt.trans_le hp⟩
    let a := (numBits d).symm v
    have hv : value a = v := (numBits d).apply_symm_apply v
    obtain ⟨⟨b,c⟩,hc,_⟩ := (lift a).2 (by rw [hv]; exact r.isLt)
    let z := (numBits d).symm b
    have hz : value z = b := (numBits d).apply_symm_apply b
    refine ⟨⟨(a,z,c),(below_iff ..).mpr (by simpa only [hz] using hc)⟩,Fin.ext ?_⟩
    change (value a).val = r.val
    rw [hv]

theorem finEquiv_val {d p : ℕ} (hp : p ≤ 2^d) (w : {u : Triple d // below p u}) :
    (finEquiv hp w).val = (value w.val.1).val := rfl

def zmodFin (p : ℕ) [NeZero p] : Fin p ≃ ZMod p where
  toFun u := u.val
  invFun r := ⟨r.val,r.val_lt⟩
  left_inv u := Fin.ext (ZMod.val_natCast_of_lt u.isLt)
  right_inv r := ZMod.natCast_zmod_val r

noncomputable abbrev zmodEquiv {d p : ℕ} [NeZero p] (hp : p ≤ 2^d) := (finEquiv hp).trans (zmodFin p)

end DetDLP.S8H0.ResidueWires


