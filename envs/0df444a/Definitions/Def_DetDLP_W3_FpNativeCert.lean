-- Prove2me | Definitions.Def_DetDLP_W3_FpNativeCert
-- name    : DetDLP_W3_FpNativeCert
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T02:02:44.672782+00:00
-- url     : https://prove2.me/theorems/7afdc73b-120d-4ffb-a2a2-da223308fb0c
-- title:
--   Parsimony of prime-field hash and product certificates
-- statement:
--   A checked slot carries its nonzero residue, a bounded address, and an affine multiplication certificate. For each block, such slots are in bijection with its list positions. Taking the product of these bijections and adjoining the two modular product chains gives a bijection between combined certificates and tuple pairs satisfying the prescribed group equation and prefix predicate.

import Definitions.Def_DetDLP_W3_FpHashPins

set_option autoImplicit false
namespace DetDLP

abbrev w3_fpRawSlot (d p k : ℕ) (hd : 1 ≤ d) := Fin p × Fin (2^k) × w3_fpHashCert d p hd

def w3_fpSlotCheck {d p m k : ℕ} (hd : 1 ≤ d) (seed : FpSeed p m) (i : Fin m) (T : ℕ)
    (s : w3_fpRawSlot d p k hd) : Prop :=
  s.1.val ≠ 0 ∧ s.2.1.val < T ∧ s.2.1.val < p ∧
  w3_fpHashCheck hd ((seed i).1.val+1) (seed i).2.val s.1.val s.2.1.val s.2.2

noncomputable def w3_fpCheckedSlotEquiv {p d m k : ℕ} [Fact p.Prime] (hd : 1 ≤ d) (hp : 2 ≤ p)
    (hfit : p < 2^d) (mul : w3_modMulInterface) (seed : FpSeed p m) (F : Fin m → List (ZMod p)ˣ)
    (i : Fin m) (T : ℕ) (hk : T ≤ 2^k) (hF : (F i).Nodup ∧ (F i).toFinset = fpFactorBlock T seed i) :
    {s : w3_fpRawSlot d p k hd // w3_fpSlotCheck hd seed i T s} ≃ Fin ((w3_fpFB F).blocks i).length := by
  let a : Fin p := ⟨(seed i).1.val+1,by have := (seed i).1.isLt; omega⟩
  let b := (seed i).2
  let R := {s : w3_fpRawSlot d p k hd // w3_fpSlotCheck hd seed i T s}
  have sound (s : R) : s.1.2.1.val = w3_fpHashWord seed i s.1.1.val :=
    w3_fpHash_sound hd hp hfit mul a b s.1.1 ⟨s.1.2.1.val,s.2.2.2.1⟩ s.1.2.2 s.2.2.2.2
  let f (s : R) : w3_fpBlockResidues seed i T := ⟨s.1.1,s.2.1,(sound s) ▸ s.2.2.1⟩
  apply Equiv.trans (Equiv.ofBijective f ?_) (w3_fpBlockResidueEquiv seed F i T hF).symm
  constructor
  · rintro ⟨⟨x,z,c⟩,hs⟩ ⟨⟨y,t,e⟩,hu⟩ h
    have hxy : x = y := congrArg Subtype.val h
    subst y
    have hz := sound ⟨(x,z,c),hs⟩
    have ht := sound ⟨(x,t,e),hu⟩
    change z.val = w3_fpHashWord seed i x.val at hz
    change t.val = w3_fpHashWord seed i x.val at ht
    have hzt : z = t := Fin.ext (hz.trans ht.symm)
    subst t
    have uniq := w3_fpHash_unique hd hp hfit mul a b x ⟨z.val,hs.2.2.1⟩ hz
    have hce : c = e := uniq.unique hs.2.2.2 hu.2.2.2
    subst e; rfl
  · rintro ⟨x,hx,hy⟩
    let z := w3_fpHashWord seed i x.val
    have hz : z < p := Nat.mod_lt _ (by omega)
    obtain ⟨c,hc,_⟩ := w3_fpHash_unique hd hp hfit mul a b x ⟨z,hz⟩ rfl
    exact ⟨⟨(x,⟨z,hy.trans_le hk⟩,c),hx,hy,hz,hc⟩,rfl⟩

abbrev w3_fpSlotTable {p m : ℕ} (F : Fin m → List (ZMod p)ˣ) :=
  (i : Fin m) → Fin 2 → Bool → Fin ((w3_fpFB F).blocks i).length

def w3_fpSlotTableEquiv {p m : ℕ} (F : Fin m → List (ZMod p)ˣ) :
    w3_fpSlotTable F ≃ (w3_fpFB F).BlockTuple × (w3_fpFB F).BlockTuple where
  toFun s := (fun i j => s i j false,fun i j => s i j true)
  invFun t := fun i j b => if b then t.2 i j else t.1 i j
  left_inv s := by funext i j b; cases b <;> rfl
  right_inv _ := rfl

noncomputable def w3_fpCheckedTableEquiv {p d m k : ℕ} [Fact p.Prime] (hd : 1 ≤ d) (hp : 2 ≤ p)
    (hfit : p < 2^d) (mul : w3_modMulInterface) (seed : FpSeed p m) (F : Fin m → List (ZMod p)ˣ)
    (T : ℕ) (hk : T ≤ 2^k) (hF : ∀ i, (F i).Nodup ∧ (F i).toFinset = fpFactorBlock T seed i) :
    ((i : Fin m) → Fin 2 → Bool → {s : w3_fpRawSlot d p k hd // w3_fpSlotCheck hd seed i T s}) ≃
      (w3_fpFB F).BlockTuple × (w3_fpFB F).BlockTuple :=
  (Equiv.piCongrRight fun i => Equiv.piCongrRight fun _ => Equiv.piCongrRight fun _ =>
    w3_fpCheckedSlotEquiv hd hp hfit mul seed F i T hk (hF i)).trans (w3_fpSlotTableEquiv F)

noncomputable def w3_fpNativeCertEquiv {p d m k : ℕ} [Fact p.Prime] (hd : 1 ≤ d) (hp : 2 ≤ p)
    (hfit : p < 2^d) (mul : w3_modMulInterface) (seed : FpSeed p m) (F : Fin m → List (ZMod p)ˣ)
    (T : ℕ) (hk : T ≤ 2^k) (hF : ∀ i, (F i).Nodup ∧ (F i).toFinset = fpFactorBlock T seed i)
    (P : (ZMod p)ˣ) (pin : (w3_fpFB F).BlockTuple × (w3_fpFB F).BlockTuple → Prop) :
    let E := w3_fpCheckedTableEquiv hd hp hfit mul seed F T hk hF
    {a : ((i : Fin m) → Fin 2 → Bool → {s : w3_fpRawSlot d p k hd // w3_fpSlotCheck hd seed i T s}) ×
      w3_fpJoinedRun p d hd // pin (E a.1) ∧ w3_fpJoinedOK hd (w3_fpFB F) P (E a.1).1 (E a.1).2 a.2} ≃
    {t : (w3_fpFB F).BlockTuple × (w3_fpFB F).BlockTuple //
      (w3_fpFB F).tupleVal t.2 = (w3_fpFB F).tupleVal t.1 + Additive.ofMul P ∧ pin t} := by
  let E := w3_fpCheckedTableEquiv hd hp hfit mul seed F T hk hF
  apply Equiv.trans _ (w3_fpJoinedEquiv hd hp hfit mul (w3_fpFB F) P pin)
  exact (Equiv.prodCongr E (Equiv.refl _)).subtypeEquiv (fun _ => Iff.rfl)

end DetDLP


