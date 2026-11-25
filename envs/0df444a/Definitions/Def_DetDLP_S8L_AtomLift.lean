-- Prove2me | Definitions.Def_DetDLP_S8L_AtomLift
-- name    : DetDLP_S8L_AtomLift
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T08:34:53.811967+00:00
-- url     : https://prove2.me/theorems/a1dddfe6-0a45-414f-95ca-62c0f1056e2f
-- title:
--   Canonical extension of a Tag 5 factor
-- statement:
--   Projection onto the input residue gives a bijection between accepted atom banks and the nonzero inputs whose affine hash is below the threshold. The carry chains, range witnesses and multiplication certificates are uniquely determined.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8L_RowSound

set_option autoImplicit false
namespace DetDLP.S8L.AtomLift
open S8H0 S8H0.RegisterMap S8H0.ResidueWires S8H0.SignalBank RowSound S8C M89S1
variable {p m d T : ℕ} {hd : 1 ≤ d}
abbrev Checked (p T d : ℕ) (hd : 1 ≤ d) := Bounded (d:=d) p × (Bits d × Bits d) × Bounded (d:=d) (min T p) × CheckedRun d p hd × AuxBank d

def unpack : {v : Atom d hd // bounds p T v} ≃ Checked p T d hd where
  toFun a := let v := a.val; let r := slot v
             (⟨v.1,a.2.1⟩,v.2.1,⟨v.2.2.1,a.2.2.1⟩,(⟨r.1,a.2.2.2.1⟩,(⟨r.2.1.1,a.2.2.2.2⟩,r.2.1.2),r.2.2),v.2.2.2.2)
  invFun a := let r := a.2.2.2.1
              ⟨(a.1.val,a.2.1,a.2.2.1.val,(r.1.val,(r.2.1.1.val,r.2.1.2),r.2.2),a.2.2.2.2),a.1.2,a.2.2.1.2,r.1.2,r.2.1.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

abbrev Typed (p T d : ℕ) (hd : 1 ≤ d) := Fin p × (Fin (2^d) × Bits d) × Fin (min T p) × (Fin p × w3_fpHashCert d p hd) × w3_slotHashAux d
noncomputable def decode (hp : p ≤ 2^d) : {v : Atom d hd // bounds p T v} ≃ Typed p T d hd :=
  unpack.trans <| (finEquiv hp).prodCongr (((numBits d).prodCongr (Equiv.refl _)).prodCongr
    ((finEquiv ((min_le_right T p).trans hp)).prodCongr (((finEquiv hp).prodCongr
    (((finEquiv hp).prodCongr ((numBits d).prodCongr ((mulEquiv hd).prodCongr (mulEquiv hd)))).prodCongr (Equiv.refl _))).prodCongr (auxEquiv d))))

abbrev Good (c : ℕ × ℕ) (a : Typed p T d hd) :=
  w3_addColumns d a.2.1.1.val 0 a.1.val true a.2.1.2 ∧ a.2.2.2.1.1.val = a.2.2.1.val ∧
  w3_slotHashBits hd c.1 c.2 a.1.val a.2.2.2.1.1.val a.2.2.2.1.2 a.2.2.2.2
noncomputable def typedEquiv (hp : p ≤ 2^d) (c : ℕ × ℕ) : {v : Atom d hd // constraint hp T c v} ≃ {a : Typed p T d hd // Good c a} := by
  let e := decode (T:=T) (hd:=hd) hp
  refine (Equiv.subtypeEquivRight (q := fun v => ∃ h : bounds p T v, Good c (e ⟨v,h⟩)) ?_).trans ?_
  · intro v; apply exists_congr; intro h
    apply and_congr_right; intro _; apply and_congr_left; intro _
    exact ⟨fun h => congrArg num h,fun h => (numBits d).injective (Fin.ext h)⟩
  exact ((Equiv.subtypeSubtypeEquivSubtypeExists _ _).symm).trans (Equiv.subtypeEquiv e fun _ => Iff.rfl)

variable [Fact p.Prime] (S : FpSeed p m) (i : Fin m) (T : ℕ)
abbrev coeff := ((S i).1.val+1,(S i).2.val)
abbrev posD (p : ℕ) : 1 ≤ atomWidth p := Nat.succ_pos _
abbrev Accepted := {v : Atom (atomWidth p) (posD p) // constraint (primeFitsAtom p).le T (coeff S i) v}
noncomputable def residue (a : Accepted S i T) : Fin p := finEquiv (primeFitsAtom p).le ⟨a.val.1,a.2.choose.1⟩

/-- Each canonical input has exactly one extension precisely when it is a nonzero member of the hash block. -/
noncomputable def atomEquiv : Accepted S i T ≃ {x : Fin p // x.val ≠ 0 ∧ w3_fpHashWord S i x.val < T} := by
  let e := typedEquiv (hd:=posD p) (T:=T) (primeFitsAtom p).le (coeff S i)
  apply e.trans
  let fit := primeFitsAtom p
  let check := fun (x : Fin p) => atom_iff w3_m5_modmul_r2 S i T x
  have nzLift (x : Fin p) : w3_slotLift (x.val ≠ 0) (fun b : Fin (2^atomWidth p) × Bits (atomWidth p) => w3_addColumns _ b.1.val 0 x.val true b.2) := by
    have L (b : Fin (2^atomWidth p) × Bits (atomWidth p)) (h : w3_addColumns _ b.1.val 0 x.val true b.2) : b.1.val+1 = x.val := by
      simpa using w3_addColumns_sound b.1.isLt (Nat.two_pow_pos _) (x.isLt.trans fit) h
    refine ⟨fun b h => by have := L b h; omega,?_⟩
    intro hx; let k : Fin (2^atomWidth p) := ⟨x.val-1,by have := x.isLt.trans fit; omega⟩
    obtain ⟨t,ht,ut⟩ := w3_addColumns_unique k.isLt (Nat.two_pow_pos _) (x.isLt.trans fit) (cin:=true) (by simp [k]; omega)
    exact ⟨(k,t),ht,fun ⟨j,u⟩ hu => by obtain rfl : j = k := Fin.ext (by have hj : j.val+1=x.val := L (j,u) hu; dsimp [k]; omega); exact Prod.ext rfl (ut _ hu)⟩
  have hashLift (x : Fin p) (r : AtomRun p) := w3_slotHash_spec (a:=(coeff S i).1) (x:=x.val) (posD p) fit (S i).2.isLt r.1.isLt r.2
  have sound (a : Typed p T _ (posD p)) (h : Good (coeff S i) a) : atomOK S i T a.1 a.2.2.2.1 :=
    ⟨(nzLift _).1 _ h.1, h.2.1 ▸ a.2.2.1.isLt.trans_le (min_le_left ..),(hashLift _ _).1 _ h.2.2⟩
  have wordOK (a : Typed p T _ (posD p)) (h : Good (coeff S i) a) : a.1.val ≠ 0 ∧ w3_fpHashWord S i a.1.val < T := by
    have ok := sound a h; have H := w3_fpHash_sound (posD p) (Fact.out : p.Prime).two_le fit w3_m5_modmul_r2
      (⟨(coeff S i).1, by have := (S i).1.isLt; dsimp [coeff]; omega⟩ : Fin p) (S i).2 a.1 _ _ ok.2.2
    change a.2.2.2.1.1.val = w3_fpHashWord S i a.1.val at H
    exact ⟨ok.1,H ▸ ok.2.1⟩
  apply Equiv.ofBijective (fun a => ⟨a.1.1,wordOK _ a.2⟩)
  constructor
  · rintro ⟨⟨x,b,z,r,u⟩,h⟩ ⟨⟨y,b',z',r',u'⟩,h'⟩ he
    obtain rfl : x = y := congrArg Subtype.val he
    have ok := sound _ h; have ok' := sound _ h'
    obtain rfl : r = r' := ((check x).mpr (wordOK _ h)).unique ok ok'
    obtain rfl : b = b' := ((nzLift x).2 ok.1).unique h.1 h'.1
    obtain rfl : z = z' := Fin.ext (h.2.1.symm.trans h'.2.1)
    obtain rfl : u = u' := ((hashLift x r).2 ok.2.2).unique h.2.2 h'.2.2
    rfl
  · rintro ⟨x,hx⟩; obtain ⟨r,hr,_⟩ := (check x).mpr hx
    obtain ⟨b,hb,_⟩ := (nzLift x).2 hx.1; obtain ⟨u,hu,_⟩ := (hashLift x r).2 hr.2.2
    exact ⟨⟨(x,b,⟨r.1.val,lt_min hr.2.1 r.1.isLt⟩,r,u),hb,rfl,hu⟩,rfl⟩

end DetDLP.S8L.AtomLift


