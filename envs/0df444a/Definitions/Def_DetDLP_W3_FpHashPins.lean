-- Prove2me | Definitions.Def_DetDLP_W3_FpHashPins
-- name    : DetDLP_W3_FpHashPins
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T01:57:26.040751+00:00
-- url     : https://prove2.me/theorems/30c88731-27d3-48d8-a781-a3a0e2fabc69
-- title:
--   Unique certificates for affine prime-field lookup addresses
-- statement:
--   For each block, its list positions are in bijection with the nonzero canonical residues whose affine address is below the threshold. For a modulus strictly smaller than the word capacity, a multiplication certificate and one carry bit determine the reduced affine address. Every correct address has exactly one such certificate.

import Definitions.Def_DetDLP_W3_FpWire2

set_option autoImplicit false
namespace DetDLP

def w3_fpHashWord {p m : ℕ} (seed : FpSeed p m) (i : Fin m) (x : ℕ) : ℕ :=
  (((seed i).1.val+1)*x+(seed i).2.val)%p

def w3_fpBlockResidues {p m : ℕ} (seed : FpSeed p m) (i : Fin m) (T : ℕ) :=
  {x : Fin p // x.val ≠ 0 ∧ w3_fpHashWord seed i x.val < T}

noncomputable def w3_fpBlockResidueEquiv {p m : ℕ} [Fact p.Prime] (seed : FpSeed p m)
    (F : Fin m → List (ZMod p)ˣ) (i : Fin m) (T : ℕ)
    (hF : (F i).Nodup ∧ (F i).toFinset = fpFactorBlock T seed i) :
    Fin ((w3_fpFB F).blocks i).length ≃ w3_fpBlockResidues seed i T := by
  classical
  let l := (F i).map Additive.ofMul
  have mem (r : Fin l.length) : (l.get r).toMul ∈ fpFactorBlock T seed i := by
    rw [←hF.2, List.mem_toFinset]; simpa [l] using List.get_mem l r
  let f (r : Fin l.length) : w3_fpBlockResidues seed i T :=
    ⟨w3_fpResidue (l.get r).toMul,by
      apply And.intro
      · exact fun h => (l.get r).toMul.ne_zero (ZMod.val_injective p (h.trans ZMod.val_zero.symm))
      · exact of_decide_eq_true (Finset.mem_filter.mp (mem r)).2⟩
  apply Equiv.ofBijective f
  constructor
  · intro r t h
    have hv := congrArg (fun a : w3_fpBlockResidues seed i T => a.val.val) h
    have hu := Units.ext (ZMod.val_injective p hv)
    exact ((hF.1.map Additive.ofMul.injective).get_inj_iff).mp (congrArg Additive.ofMul hu)
  · rintro ⟨x,hx,ha⟩
    have hv : ((x.val : ZMod p)).val = x.val := ZMod.val_natCast_of_lt x.isLt
    have hn : (x.val : ZMod p) ≠ 0 := by intro hz; exact hx (hv.symm.trans ((congrArg ZMod.val hz).trans ZMod.val_zero))
    let u := Units.mk0 (x.val : ZMod p) hn
    have hu : ((u : ZMod p)).val = x.val := hv
    have hm : u ∈ fpFactorBlock T seed i := by
      apply Finset.mem_filter.mpr; refine ⟨Finset.mem_univ _,?_⟩
      change decide (w3_fpHashWord seed i ((u : ZMod p)).val < T) = true
      rw [hu]; exact decide_eq_true ha
    rw [←hF.2, List.mem_toFinset] at hm
    have hmem : Additive.ofMul u ∈ l := List.mem_map_of_mem hm
    obtain ⟨r,hr⟩ := List.mem_iff_get.mp hmem
    refine ⟨r, Subtype.ext (Fin.ext ?_)⟩
    change (((l.get r).toMul : (ZMod p)ˣ) : ZMod p).val = x.val
    rw [hr]; exact hu

abbrev w3_fpHashCert (d p : ℕ) (hd : 1 ≤ d) := w3_mulStage d hd p × Bool

def w3_fpHashCheck {d p : ℕ} (hd : 1 ≤ d) (a b x z : ℕ) (r : w3_fpHashCert d p hd) :=
  w3_modTwo hd p a x r.1.1.val r.1.2 ∧ r.1.1.val+b = z + (if r.2 then p else 0)

theorem w3_fpHash_sound {d p : ℕ} (hd : 1 ≤ d) (hp : 2 ≤ p) (hfit : p < 2^d)
    (mul : w3_modMulInterface) (a b x z : Fin p) (r : w3_fpHashCert d p hd)
    (h : w3_fpHashCheck hd a.val b.val x.val z.val r) : z.val = (a.val*x.val+b.val)%p := by
  have hu := ((mul d hd p a.val x.val r.1.1.val hp hfit.le a.isLt x.isLt r.1.1.isLt).2 hfit).2 _ h.1
  rw [←Nat.mod_add_mod,←hu,h.2]
  cases r.2 <;> simp [Nat.mod_eq_of_lt z.isLt]

theorem w3_fpHash_unique {d p : ℕ} (hd : 1 ≤ d) (hp : 2 ≤ p) (hfit : p < 2^d)
    (mul : w3_modMulInterface) (a b x z : Fin p) (hz : z.val = (a.val*x.val+b.val)%p) :
    ∃! r : w3_fpHashCert d p hd, w3_fpHashCheck hd a.val b.val x.val z.val r := by
  let u : Fin p := ⟨(a.val*x.val)%p,Nat.mod_lt _ (by omega)⟩
  obtain ⟨t,ht,ut⟩ := ((mul d hd p a.val x.val u.val hp hfit.le a.isLt x.isLt u.isLt).2 hfit).1 rfl
  let c := decide (p ≤ u.val+b.val)
  have he : z.val = (u.val+b.val)%p := hz.trans (Nat.mod_add_mod ..).symm
  have hs : u.val+b.val = z.val + (if c then p else 0) := by
    by_cases h : p ≤ u.val+b.val
    · have hv : u.val+b.val-p < p := by have := u.isLt; have := b.isLt; omega
      rw [Nat.mod_eq_sub_mod h,Nat.mod_eq_of_lt hv] at he
      simp [c,h]; omega
    · rw [Nat.mod_eq_of_lt (by omega)] at he; simp [c,h,he]
  refine ⟨((u,t),c),⟨ht,hs⟩,?_⟩
  rintro ⟨⟨v,s⟩,e⟩ ⟨hv,he'⟩
  have hvu : v = u := Fin.ext (((mul d hd p a.val x.val v.val hp hfit.le a.isLt x.isLt v.isLt).2 hfit).2 _ hv)
  subst v; rw [ut s hv]
  have ec : e = c := by
    change u.val+b.val = z.val + (if e then p else 0) at he'
    cases hc : c <;> rw [hc] at hs <;> cases e <;> first | rfl | (simp only [Bool.false_eq_true,if_false,if_true] at hs he'; omega)
  rw [ec]

end DetDLP


