-- Prove2me | Definitions.Def_DetDLP_W3_FpWire2
-- name    : DetDLP_W3_FpWire2
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T01:33:33.131421+00:00
-- url     : https://prove2.me/theorems/b08e884b-c959-4c61-89b8-8e43aee84b6f
-- title:
--   Joined modular product certificates for prime-field block tuples
-- statement:
--   Associate to each block tuple a list of twice the block count many canonical residues. For a prime-field unit P, start the first modular product chain at P and the second at the identity. The pair of chains admits a common residue precisely when the second tuple product is the first tuple product multiplied by P. In this case the common residue and both sequences of M5 multiplication certificates are unique. Consequently forgetting the certificates is a bijection, also after restricting the tuple pair by an arbitrary prefix predicate.

import Definitions.Def_DetDLP_W3_ModMulChain
import Definitions.Def_DetDLP_W3_Separator

set_option autoImplicit false
namespace DetDLP

theorem w3_fpPrimeFits {p : ℕ} (hp : p.Prime) (h : 2 < p) :
    1 ≤ bitLen p ∧ p < 2^(bitLen p) := by
  have hle : p ≤ 2^(bitLen p) := Nat.le_pow_clog (by decide) p
  refine ⟨Nat.clog_pos (by decide) (by omega),lt_of_le_of_ne hle ?_⟩
  intro he
  have hd := Nat.Prime.eq_one_of_pow (he ▸ hp : (2^(bitLen p)).Prime)
  rw [hd,pow_one] at he; omega

def w3_fpResidue {p : ℕ} [NeZero p] (u : (ZMod p)ˣ) : Fin p :=
  ⟨(u : ZMod p).val,(u : ZMod p).val_lt⟩

def w3_fpFactors {p m : ℕ} [NeZero p] (FB : IndexedFactorBase (Additive (ZMod p)ˣ) m)
    (X : FB.BlockTuple) : List (Fin p) :=
  (List.ofFn fun i => w3_fpResidue ((FB.blocks i).get (X i 0)).toMul) ++
  (List.ofFn fun i => w3_fpResidue ((FB.blocks i).get (X i 1)).toMul)

theorem w3_fpFactors_length {p m : ℕ} [NeZero p] (FB : IndexedFactorBase (Additive (ZMod p)ˣ) m)
    (X : FB.BlockTuple) : (w3_fpFactors FB X).length = 2*m := by
  simp [w3_fpFactors]; omega

theorem w3_fpFactors_cast {p m : ℕ} [NeZero p] (FB : IndexedFactorBase (Additive (ZMod p)ˣ) m)
    (X : FB.BlockTuple) : ((((w3_fpFactors FB X).map Fin.val).prod : ℕ) : ZMod p) =
      ((FB.tupleVal X).toMul : ZMod p) := by
  simp [w3_fpFactors,IndexedFactorBase.tupleVal,w3_fpResidue,List.map_ofFn,
    Function.comp_def,List.prod_ofFn,Finset.prod_mul_distrib,Units.coe_prod]

/-- The chains start at the public unit and the identity and meet at one remainder. -/
abbrev w3_fpJoinedRun (p d : ℕ) (hd : 1 ≤ d) :=
  Fin p × List (w3_mulStage d hd p) × List (w3_mulStage d hd p)

def w3_fpJoinedOK {p d m : ℕ} [NeZero p] (hd : 1 ≤ d)
    (FB : IndexedFactorBase (Additive (ZMod p)ˣ) m) (P : (ZMod p)ˣ)
    (X Y : FB.BlockTuple) (r : w3_fpJoinedRun p d hd) : Prop :=
  w3_checkStages hd (w3_fpResidue P) (w3_fpFactors FB X) r.2.1 r.1 ∧
  w3_checkStages hd (w3_fpResidue 1) (w3_fpFactors FB Y) r.2.2 r.1

theorem w3_fpChainValue {p m : ℕ} [NeZero p] (FB : IndexedFactorBase (Additive (ZMod p)ˣ) m)
    (P : (ZMod p)ˣ) (X : FB.BlockTuple) :
    ((w3_fpResidue P).val*((w3_fpFactors FB X).map Fin.val).prod)%p =
      (w3_fpResidue ((FB.tupleVal X).toMul * P)).val := by
  rw [← ZMod.val_natCast,Nat.cast_mul,w3_fpFactors_cast]
  simp [w3_fpResidue,mul_comm]

theorem w3_fpJoined_sound {p d m : ℕ} [NeZero p] (hd : 1 ≤ d) (hp : 2 ≤ p) (hfit : p < 2^d)
    (mul : w3_modMulInterface) (FB : IndexedFactorBase (Additive (ZMod p)ˣ) m) (P : (ZMod p)ˣ)
    (X Y : FB.BlockTuple) (r : w3_fpJoinedRun p d hd) (hr : w3_fpJoinedOK hd FB P X Y r) :
    FB.tupleVal Y = FB.tupleVal X + Additive.ofMul P := by
  have hx := w3_checkStages_output hd hp hfit mul _ _ _ _ hr.1
  have hy := w3_checkStages_output hd hp hfit mul _ _ _ _ hr.2
  rw [w3_fpChainValue] at hx hy
  rw [mul_one] at hy
  exact Additive.toMul.injective (Units.ext (ZMod.val_injective p (hy.symm.trans hx)))

theorem w3_fpJoined_iff {p d m : ℕ} [NeZero p] (hd : 1 ≤ d) (hp : 2 ≤ p) (hfit : p < 2^d)
    (mul : w3_modMulInterface) (FB : IndexedFactorBase (Additive (ZMod p)ˣ) m) (P : (ZMod p)ˣ)
    (X Y : FB.BlockTuple) : (∃! r, w3_fpJoinedOK hd FB P X Y r) ↔
      FB.tupleVal Y = FB.tupleVal X + Additive.ofMul P := by
  constructor
  · rintro ⟨r,hr,_⟩; exact w3_fpJoined_sound hd hp hfit mul FB P X Y r hr
  · intro hv
    let z := w3_fpResidue (FB.tupleVal Y).toMul
    have hx : z.val = ((w3_fpResidue P).val*((w3_fpFactors FB X).map Fin.val).prod)%p := by
      rw [w3_fpChainValue]; exact congrArg (fun u => (w3_fpResidue u.toMul).val) hv
    have hy : z.val = ((w3_fpResidue (p := p) 1).val*((w3_fpFactors FB Y).map Fin.val).prod)%p := by
      rw [w3_fpChainValue,mul_one]
    obtain ⟨s,hs,us⟩ := w3_checkStages_existsUnique hd hp hfit mul _ _ z hx
    obtain ⟨t,ht,ut⟩ := w3_checkStages_existsUnique hd hp hfit mul _ _ z hy
    refine ⟨(z,s,t),⟨hs,ht⟩,?_⟩
    rintro ⟨z',s',t'⟩ ⟨hs',ht'⟩
    have hz : z' = z := Fin.ext ((w3_checkStages_output hd hp hfit mul _ _ s' z' hs').trans hx.symm)
    subst z'; rw [us s' hs',ut t' ht']

noncomputable def w3_fpJoinedEquiv {p d m : ℕ} [NeZero p] (hd : 1 ≤ d) (hp : 2 ≤ p) (hfit : p < 2^d)
    (mul : w3_modMulInterface) (FB : IndexedFactorBase (Additive (ZMod p)ˣ) m) (P : (ZMod p)ˣ)
    (pin : FB.BlockTuple × FB.BlockTuple → Prop) :
    {a : (FB.BlockTuple × FB.BlockTuple) × w3_fpJoinedRun p d hd //
      pin a.1 ∧ w3_fpJoinedOK hd FB P a.1.1 a.1.2 a.2} ≃
    {t : FB.BlockTuple × FB.BlockTuple // FB.tupleVal t.2 = FB.tupleVal t.1 + Additive.ofMul P ∧ pin t} := by
  classical
  refine Equiv.ofBijective (fun a => ⟨a.val.1,
    w3_fpJoined_sound hd hp hfit mul FB P _ _ _ a.prop.2,a.prop.1⟩) ⟨?_,?_⟩
  · rintro ⟨⟨t,r⟩,ht,hr⟩ ⟨⟨t',s⟩,hs',hs⟩ h
    have h' : t = t' := congrArg Subtype.val h
    subst t'
    have hu := (w3_fpJoined_iff hd hp hfit mul FB P t.1 t.2).2
      (w3_fpJoined_sound hd hp hfit mul FB P t.1 t.2 r hr)
    exact Subtype.ext (congrArg (Prod.mk t) (hu.unique hr hs))
  · rintro ⟨t,he,ht⟩
    obtain ⟨r,hr,_⟩ := (w3_fpJoined_iff hd hp hfit mul FB P t.1 t.2).2 he
    exact ⟨⟨(t,r),ht,hr⟩,rfl⟩

end DetDLP


