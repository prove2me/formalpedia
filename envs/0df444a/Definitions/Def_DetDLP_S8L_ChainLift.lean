-- Prove2me | Definitions.Def_DetDLP_S8L_ChainLift
-- name    : DetDLP_S8L_ChainLift
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T08:42:37.088498+00:00
-- url     : https://prove2.me/theorems/91a225a1-f1b6-42d5-a56d-08586682c3ff
-- title:
--   Unique extension along the shortened modular product chain
-- statement:
--   For a sequence of $n\ge2$ field elements the $n-1$ routed product stages and $n-2$ intermediate residue registers admit exactly one accepting assignment when the product equals the public endpoint, and none otherwise. Each intermediate word is the corresponding partial product.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8L_AtomLift

set_option autoImplicit false
namespace DetDLP.S8L.ChainLift
open S8H0.ResidueWires S8H0.SignalBank RowSound S8C AtomLift
variable {p n : ℕ} [Fact p.Prime]
abbrev D (p : ℕ) := Stage (atomWidth p) (posD p)
abbrev Bank (p n : ℕ) := (Fin (n-1) → D p) × (Fin (n-2) → Triple (atomWidth p))
private def parts {d : ℕ} (hd : 1 ≤ d) : Stage d hd ≃ (Fin (2^d) × w3_mulRun d hd × w3_mulRun d hd) × Bits (2*d) :=
  { toFun := fun v => (stepCert v,v.2.2.2)
    invFun := fun ⟨⟨q,a,b⟩,c⟩ => ((numBits d).symm q,(mulEquiv hd).symm a,(mulEquiv hd).symm b,c)
    left_inv := fun v => Prod.ext ((numBits d).symm_apply_apply _) (Prod.ext ((mulEquiv hd).symm_apply_apply _) (Prod.ext ((mulEquiv hd).symm_apply_apply _) rfl))
    right_inv := fun ⟨⟨q,a,b⟩,c⟩ => by simp only [stepCert,← show (numBits d).toFun = value from rfl]; simp }

theorem stepLift (x y z : ZMod p) : w3_slotLift (z = x*y) (step (hd:=posD p) p x.val y.val z.val) := by
  let fit := primeFitsAtom p
  let hd := posD p
  have H := (w3_m5_modmul_r2 _ hd p x.val y.val z.val (Fact.out : p.Prime).two_le fit.le x.val_lt y.val_lt z.val_lt).2 fit
  have hwide := z.val_lt.trans_le (fit.le.trans (Nat.pow_le_pow_right (by decide) (by omega : atomWidth p ≤ 2*atomWidth p)))
  have R (v : D p) : step p x.val y.val z.val v → w3_modTwo hd p x.val y.val z.val (stepCert v) := by
    rintro ⟨a,b,c⟩; exact ⟨(w3_fpMulPins_inc ..).2 a,(w3_fpMulPins_inc ..).2 b,by change num v.2.2.1.1 + z.val = num v.2.1.1; simpa only [Bool.toNat_false,Nat.add_zero] using w3_addColumns_sound (value v.2.2.1.1).isLt hwide (value v.2.1.1).isLt c⟩
  refine ⟨fun v h => ZMod.val_injective p ((H.2 _ (R v h)).trans (ZMod.val_mul x y).symm),?_⟩
  intro he; obtain ⟨r,hr,ur⟩ := H.1 (he ▸ ZMod.val_mul x y)
  obtain ⟨c,hc,uc⟩ := w3_addColumns_unique r.2.2.1.isLt hwide r.2.1.1.isLt (cin:=false) (by simpa using hr.2.2)
  let v := (parts hd).symm (r,c)
  have ev : (stepCert v,v.2.2.2) = (r,c) := (parts hd).apply_symm_apply (r,c)
  have hv := congrArg Prod.fst ev; have hv' := congrArg Prod.snd ev
  change stepCert v = r at hv; change v.2.2.2 = c at hv'
  refine ⟨v,?_,?_⟩
  · change w3_slotMulInc _ _ _ (stepCert v).2.1 ∧ w3_slotMulInc _ _ _ (stepCert v).2.2 ∧ w3_addColumns _ (stepCert v).2.2.1.val _ (stepCert v).2.1.1.val false v.2.2.2
    rw [hv,hv']; exact ⟨(w3_fpMulPins_inc ..).1 hr.1,(w3_fpMulPins_inc ..).1 hr.2.1,hc⟩
  · intro v' h; have hr' := ur _ (R v' h)
    have hc' := h.2.2; change w3_addColumns _ (stepCert v').2.2.1.val _ (stepCert v').2.1.1.val false _ at hc'
    rw [hr'] at hc'; exact (parts hd).injective ((Prod.ext hr' (uc _ hc')).trans ev.symm)

variable (f : ℕ → ZMod p) (X : ZMod p)
def partialProd (k : ℕ) := ∏ j ∈ Finset.range (k+1), f j
abbrev acc (v : Bank p n) (k : ℕ) : ZMod p :=
  if h : k = 0 then f 0 else if h : k < n-1 then (num (v.2 ⟨k-1,by omega⟩).1 : ℕ) else X
abbrev OK (v : Bank p n) := (∀ j, below p (v.2 j)) ∧ ∀ i : Fin (n-1),
  step p (acc f X v i).val (f (i+1)).val (acc f X v (i+1)).val (v.1 i)

theorem chainLift (hn : 2 ≤ n) : w3_slotLift (X = partialProd f (n-1)) (OK (n:=n) f X) := by
  have next (k : ℕ) : partialProd f (k+1) = partialProd f k * f (k+1) := Finset.prod_range_succ ..
  have out (v : Bank p n) (hv : OK f X v) (k : ℕ) (hk : k < n) : acc f X v k = partialProd f k := by
    induction k with
    | zero => simp [acc,partialProd]
    | succ k ih => exact ((stepLift ..).1 _ (hv.2 ⟨k,by omega⟩)).trans (by rw [next,ih (by omega)])
  let E := @zmodEquiv (atomWidth p) p _ (primeFitsAtom p).le
  have read (b : {v : Triple (atomWidth p) // below p v}) : E b = (num b.val.1 : ZMod p) := rfl
  refine ⟨fun v h => by simpa [acc,show n-1 ≠ 0 by omega] using out v h (n-1) (by omega),?_⟩
  intro hX
  let t := fun i : Fin (n-2) => E.symm (partialProd f (i+1))
  have bits (v : Bank p n) (hv : OK f X v) (j : Fin (n-2)) : v.2 j = (t j).val := by
    apply congrArg Subtype.val (a₁:=⟨v.2 j,hv.1 j⟩)
    apply E.injective; rw [Equiv.apply_symm_apply]; have := out v hv (j+1) (by have := j.isLt; omega)
    simpa [acc,show j.val+1<n-1 by have := j.isLt; omega,read] using this
  choose s hs us using fun i : Fin (n-1) => (stepLift (partialProd f i) (f (i+1)) (partialProd f (i+1))).2 (next i)
  let w : Bank p n := (s,fun j => (t j).val)
  have aw (k : ℕ) (hk : k < n) : acc f X w k = partialProd f k := by
    unfold acc; split_ifs with h h'
    · simp [h,partialProd]
    · have ht := E.apply_symm_apply (partialProd f ((k-1)+1)); rw [read] at ht
      simpa [w,t,show k-1+1 = k by omega] using ht
    · rwa [show k=n-1 by omega]
  refine ⟨w,⟨fun j => (t j).property,fun i => by rw [aw _ (by have := i.isLt; omega),aw _ (by have := i.isLt; omega)]; exact hs i⟩,?_⟩
  intro v hv; apply Prod.ext _ (funext (bits v hv)); funext i
  apply us i; have h := hv.2 i; rwa [out v hv _ (by have := i.isLt; omega),out v hv _ (by have := i.isLt; omega)] at h

end DetDLP.S8L.ChainLift


