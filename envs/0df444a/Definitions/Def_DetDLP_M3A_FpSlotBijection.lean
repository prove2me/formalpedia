-- Prove2me | Definitions.Def_DetDLP_M3A_FpSlotBijection
-- name    : DetDLP_M3A_FpSlotBijection
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T20:25:47.005772+00:00
-- url     : https://prove2.me/theorems/805cc9a1-0153-4f23-94ba-74ded8fa4e72
-- title:
--   Fp slot physical bijection
-- statement:
--   Exact witness bijection between accepted physical Fp hash-slot tiles and factor-block indices, with residue and address bus readouts.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 4.2 (pp. 14-15)

import Definitions.Def_DetDLP_M3A_FpSlotRowLift

set_option autoImplicit false
namespace DetDLP.M3A.FpSlotBijection

export FpSlotRowLift (Accepted toResidue index residue_eq read_x read_z Table Specs rowsLift
  forget physical_iff rowPart residue_read hash_read hash_pad multiplier_input hash_bits hash_value)

open FpSlotRows FpSlotTile S8J S8G.FpPhysicalAtom S8L.FpPair.Stage S8L.FpPair.Stage.Links w4_M5PortTensor
attribute [-simp] Fin.natAdd_eq_addNat

def tableOf (p B a b x z u : ℕ) (f : Bool) (j : Fin 7) (l : Fin 3) : ℕ :=
  if j = 0 then (if l = 0 then a else if l = 1 then 0 else a + 1)
  else if j = 1 then (if l = 0 then x - 1 else if l = 1 then 0 else x)
  else if j = 2 then (if l = 0 then x else if l = 1 then p - 1 - x else p)
  else if j = 3 then (if l = 0 then z else if l = 1 then B - 1 - z else B)
  else if j = 4 then (if l = 0 then u else if l = 1 then p - 1 - u else p)
  else if j = 5 then (if l = 0 then u else if l = 1 then b else u + b)
  else (if l = 0 then z else if l = 1 then (if f then p else 0) else u + b)

private theorem num_of_bits {d : ℕ} {w : Rows d} {j : Fin 8} {l : Fin 4} {n : ℕ}
    (hn : n < 2^(d+1)) (h : ∀ i, get w j l i = n.testBit i.val) : number w j l = n :=
  congrArg Fin.val ((congrArg readWord (funext h)).trans (read_word (⟨n,hn⟩ : Fin (2^(d+1)))))

private theorem padded {d : ℕ} {w : Rows d} {j : Fin 8} {l : Fin 4} {n : ℕ} (hn : n < 2^d)
    (h : ∀ i : Fin d, get w j l i.castSucc = n.testBit i.val)
    (ht : get w j l (Fin.last d) = false) : number w j l = n := by
  apply num_of_bits (hn.trans_le (Nat.pow_le_pow_right (by decide) (by omega)))
  intro i; induction i using Fin.lastCases with
  | last => exact ht.trans (Nat.testBit_lt_two_pow hn).symm
  | cast i => exact h i

private theorem roweq {d : ℕ} {w : Rows d} {j j' : Fin 8} {l l' : Fin 4}
    (h : ∀ i, get w j l i = get w j' l' i) : number w j l = number w j' l' :=
  congrArg (fun v => (readWord v).val) (funext h)

private theorem premainder {d n : ℕ} (hn : n < 2^d) (i : Fin (2*d)) (h : d ≤ i.val) : n.testBit i.val = false :=
  Nat.testBit_lt_two_pow (hn.trans_le (Nat.pow_le_pow_right (by decide) h))

section Bijection
variable {d k m p T : ℕ} (hd : 1 ≤ d) (mul : w3_modMulInterface) (hp : 2 ≤ p) (hf : p < 2^d)
variable (seed : FpSeed p m) (i : Fin m)

private theorem extract (x : Accepted hd seed i T k) :
    let a := (seed i).1.val; let b := (seed i).2.val
    let x0 := (toResidue hd mul hp hf seed i x).1
    let z0 := w3_fpHashWord seed i x0.val
    let v := (forget hd x).1
    let s : StageBits hd := v ∘ Fin.castAdd _
    let w : Rows d := rowPart hd x.1
    ∃ u0 : Fin p,
      (Accept _ (tests hd) s ∧ buses hd p (a+1) x0.val u0.val s) ∧
      w3_fpHashCheck hd (a+1) b x0.val z0 ((u0, certificate hd s), get w 7 0 0) ∧
      Specs (tableOf p (min T p) a b x0.val z0 u0.val (get w 7 0 0)) (get w 7 0 0) w ∧
      Accept _ (S8G.FpPhysicalAtom.rowTest d p (min T p)) w := by
  dsimp only
  let a := (seed i).1.val; let b := (seed i).2.val
  let v := (forget hd x).1
  let s : StageBits hd := v ∘ Fin.castAdd _
  let w : Rows d := rowPart hd x.1
  have ha1 : a + 1 < p := by have := (seed i).1.isLt; omega
  have hb : b < p := (seed i).2.isLt
  have hpb : p < 2^(d+1) := hf.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have H := (physical_iff hd v).mp ((forget hd x).2)
  have W : wordsOK p (min T p) w := FpSlotRows.sound hpb ((min_le_right T p).trans_lt hpb) H.1.2
  obtain ⟨eqs, z01, z11, _, _, t00, zp, zp', zt, _, topb, flag⟩ := W
  have ts := H.2.1
  have short (j : Fin 3) (q : Fin d) := ts (Fin.castAdd (5*(d+1)) (finProdFinEquiv (j,q)))
  have long (j : Fin 5) (q : Fin (d+1)) := ts (Fin.natAdd (3*d) (finProdFinEquiv (j,q)))
  simp only [ties,Fin.addCases_left,Fin.addCases_right,Equiv.symm_apply_apply] at short long
  have e12 : number w 1 2 = number w 2 0 := roweq (long 0)
  have e36 : number w 3 0 = number w 6 0 := roweq (long 1)
  have e45 : number w 4 0 = number w 5 0 := roweq (long 2)
  have e56 : number w 5 2 = number w 6 2 := roweq (long 3)
  have e76 : number w 7 1 = number w 6 1 := roweq (long 4)
  have e0 := eqs 0; have e1 := eqs 1; have e2 := eqs 2; have e3 := eqs 3
  have e4 := eqs 4; have e5 := eqs 5; have e6 := eqs 6
  change number w 0 0 + number w 0 1 + 1 = number w 0 2 at e0
  change number w 1 0 + number w 1 1 + 1 = number w 1 2 at e1
  change number w 2 0 + number w 2 1 + 1 = number w 2 2 at e2
  change number w 3 0 + number w 3 1 + 1 = number w 3 2 at e3
  change number w 4 0 + number w 4 1 + 1 = number w 4 2 at e4
  change number w 5 0 + number w 5 1 + 0 = number w 5 2 at e5
  change number w 6 0 + number w 6 1 + 0 = number w 6 2 at e6
  have hn0 : number w 0 0 = a := padded (by omega) (fun q => (H.2.2 q).1) t00
  have hn5 : number w 5 1 = b := padded (hb.trans hf) (fun q => (H.2.2 q).2) topb
  have hu : number w 5 0 < p := by omega
  have hzval : number w 3 0 = w3_fpHashWord seed i (number w 1 2) :=
    hash_value hd mul hp hf ha1 hb x.2
  have hx0 : (toResidue hd mul hp hf seed i x).1.val = number w 1 2 := rfl
  let f := get w 7 0 0
  have fl : number w 7 1 = (if f then p else 0) := by
    cases he : f
    · apply num_of_bits (Nat.two_pow_pos _); intro q; simpa [←show f = get w 7 0 0 from rfl,he] using (flag q).2.2.2
    · apply num_of_bits hpb; intro q; simpa [←show f = get w 7 0 0 from rfl,he] using (flag q).2.2.2
  have hs := H.1.1
  change Accept _ (S8G.FpPhysicalAtom.stageTest hd p) s at hs
  unfold S8G.FpPhysicalAtom.stageTest at hs
  erw [atPins_iff,atPins_iff] at hs
  have bound : Boundary hd p (a+1) (number w 1 2) (number w 5 0) s := by
    refine ⟨multiplier_input hd (by omega) hf x.2, fun q => ?_, hs.1.2, fun q => ?_⟩
    · exact (short 1 q).symm.trans (read_bit (get w 1 2) q.castSucc).symm
    · by_cases hq : q.val < d
      · let t : Fin d := ⟨q.val,hq⟩
        exact (short 2 t).symm.trans (read_bit (get w 5 0) t.castSucc).symm
      · let t : Fin d := ⟨q.val-d,by have := q.isLt; omega⟩
        have et : (⟨d+t.val,by omega⟩ : Fin (2*d)) = q := Fin.ext (by dsimp [t]; omega)
        rw [premainder (hu.trans hf) q (by omega),←et]; exact hs.2 t
  have HH := (linked_iff ..).mp (And.intro hs.1.1 bound)
  have hwide : number w 5 0 < 2^(2*d) :=
    (hu.trans hf).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have hm := decode hd hwide s HH.1 HH.2
  refine ⟨⟨number w 5 0, hu⟩, ?_, ?_, ?_, H.1.2⟩
  · simpa only [hx0] using HH
  · refine ⟨?_, ?_⟩
    · simpa only [hx0] using hm
    · change number w 5 0 + b = w3_fpHashWord seed i (toResidue hd mul hp hf seed i x).1.val + (if f then p else 0)
      rw [hx0, ← hzval]; omega
  · refine ⟨fun j l => ?_, rfl⟩
    have fold_num (jj : Fin 7) (ll : Fin 3) :
        number (rowPart hd x.1) jj.castSucc ll.castSucc =
          match jj.val, ll.val with
          | 0,0 => number w 0 0 | 0,1 => number w 0 1 | 0,_ => number w 0 2
          | 1,0 => number w 1 0 | 1,1 => number w 1 1 | 1,_ => number w 1 2
          | 2,0 => number w 2 0 | 2,1 => number w 2 1 | 2,_ => number w 2 2
          | 3,0 => number w 3 0 | 3,1 => number w 3 1 | 3,_ => number w 3 2
          | 4,0 => number w 4 0 | 4,1 => number w 4 1 | 4,_ => number w 4 2
          | 5,0 => number w 5 0 | 5,1 => number w 5 1 | 5,_ => number w 5 2
          | _,0 => number w 6 0 | _,1 => number w 6 1 | _,_ => number w 6 2 := by
      fin_cases jj <;> fin_cases ll <;> rfl
    have hf_eq : get (rowPart hd x.1) 7 0 0 = f := rfl
    rw [fold_num, hf_eq]
    fin_cases j <;> fin_cases l <;>
      simp (config := {decide := true}) only [tableOf, ↓reduceIte, hx0, ← hzval] <;>
      omega

theorem toResidue_bijective [Fact p.Prime] :
    Function.Bijective (toResidue hd mul hp hf seed i (T:=T) (k:=k)) := by
  let a := (seed i).1.val; let b := (seed i).2.val
  have ha1 : a + 1 < p := by have := (seed i).1.isLt; omega
  have hb : b < p := (seed i).2.isLt
  have hpb : p < 2^(d+1) := hf.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have hB : min T p < 2^(d+1) := (min_le_right T p).trans_lt hpb
  have tbl_props (x0 : Fin p) (hx0 : x0.val ≠ 0) (hzT : w3_fpHashWord seed i x0.val < T)
      (r : w3_fpHashCert d p hd) (hr : w3_fpHashCheck hd (a+1) b x0.val (w3_fpHashWord seed i x0.val) r) :
      let z0 := w3_fpHashWord seed i x0.val
      let N := tableOf p (min T p) a b x0.val z0 r.1.1.val r.2
      (∀ j l, N j l < 2^(d+1)) ∧
      (∀ j : Fin 7, N j 0 + N j 1 + (decide (j.val<5)).toNat = N j 2) ∧
      (N 0 1 = 0 ∧ N 1 1 = 0) ∧
      (N 0 2 < 2^d ∧ N 1 2 < 2^d ∧ N 0 0 < 2^d ∧ N 5 0 < 2^d ∧ N 5 1 < 2^d) ∧
      (N 2 2 = p ∧ N 4 2 = p ∧ N 3 2 = min T p) := by
    dsimp only
    have hxlt : x0.val < p := x0.isLt
    have hzlt : w3_fpHashWord seed i x0.val < p := Nat.mod_lt _ (by omega)
    have hzm : w3_fpHashWord seed i x0.val < min T p := lt_min hzT hzlt
    have hu : r.1.1.val < p := r.1.1.isLt
    have heq : r.1.1.val + b = w3_fpHashWord seed i x0.val + (if r.2 then p else 0) := hr.2
    have h2d : 2 * p ≤ 2^(d+1) := by rw [pow_succ]; omega
    refine ⟨fun j l => ?_, fun j => ?_, ⟨rfl, rfl⟩, ?_, ⟨rfl, rfl, rfl⟩⟩
    · cases hr2 : r.2 <;> rw [hr2] at heq <;> simp only [Bool.false_eq_true, ↓reduceIte] at heq <;>
        fin_cases j <;> fin_cases l <;>
        simp (config := {decide := true}) only [tableOf, ↓reduceIte] <;> omega
    · have hj5 (j : Fin 7) : (decide (j.val < 5)).toNat = if j = 5 ∨ j = 6 then 0 else 1 := by
        fin_cases j <;> decide
      simp only [hj5]
      cases hr2 : r.2 <;> rw [hr2] at heq <;> simp only [Bool.false_eq_true, ↓reduceIte] at heq <;>
        fin_cases j <;>
        simp (config := {decide := true}) only [tableOf, ↓reduceIte] <;> omega
    · simp (config := {decide := true}) only [tableOf, ↓reduceIte]; omega
  constructor
  · intro x y hxy
    let u := toResidue hd mul hp hf seed i y
    have hxu : toResidue hd mul hp hf seed i x = u := hxy
    obtain ⟨ux, hsx, hcx, hwx, hrx⟩ := extract hd mul hp hf seed i x
    obtain ⟨uy, hsy, hcy, hwy, hry⟩ := extract hd mul hp hf seed i y
    rw [hxu] at hsx hcx hwx
    let z0 : Fin p := ⟨w3_fpHashWord seed i u.1.val, Nat.mod_lt _ (by omega)⟩
    have hun := w3_fpHash_unique hd hp hf mul ⟨a+1, ha1⟩ (seed i).2 u.1 z0 rfl
    have hcert : ((ux, certificate hd ((forget hd x).1 ∘ Fin.castAdd _)), get (rowPart hd x.1) 7 0 0) =
        ((uy, certificate hd ((forget hd y).1 ∘ Fin.castAdd _)), get (rowPart hd y.1) 7 0 0) :=
      hun.unique hcx hcy
    have hux : ux = uy := congrArg (fun r => r.1.1) hcert
    have hfx : get (rowPart hd x.1) 7 0 0 = get (rowPart hd y.1) 7 0 0 := congrArg Prod.snd hcert
    have hcs : certificate hd ((forget hd x).1 ∘ Fin.castAdd _) =
        certificate hd ((forget hd y).1 ∘ Fin.castAdd _) := congrArg (fun r => r.1.2) hcert
    subst hux
    have hwide : ux.val < 2^(2*d) :=
      (ux.isLt.trans hf).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
    have hs_eq := inject hd hwide hsx hsy hcs
    have tp := tbl_props u.1 u.2.1 u.2.2 _ hcy
    have hrl := rowsLift (d:=d) (p:=p) (tableOf p (min T p) a b u.1.val z0.val ux.val (get (rowPart hd y.1) 7 0 0))
      (get (rowPart hd y.1) 7 0 0) (min T p) tp.1 tp.2.1 tp.2.2.1 tp.2.2.2.1 tp.2.2.2.2 hpb hB
    rw [hfx] at hwx
    have hw_eq : rowPart hd x.1 = rowPart hd y.1 := hrl.unique ⟨hrx, hwx⟩ ⟨hry, hwy⟩
    apply (forget hd).injective; apply Subtype.ext; funext q
    induction q using Fin.addCases with
    | left q => exact congrFun hs_eq q
    | right q => exact congrFun hw_eq q
  · intro u
    let z0 : Fin p := ⟨w3_fpHashWord seed i u.1.val, Nat.mod_lt _ (by omega)⟩
    obtain ⟨r, hr, _⟩ := w3_fpHash_unique hd hp hf mul ⟨a+1, ha1⟩ (seed i).2 u.1 z0 rfl
    have hwide : r.1.1.val < 2^(2*d) :=
      (r.1.1.isLt.trans hf).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
    obtain ⟨s, hs, _⟩ := lift hd hwide hr.1
    have hlink := (linked_iff hd p (a+1) u.1.val r.1.1.val s).mpr hs
    have tp := tbl_props u.1 u.2.1 u.2.2 r hr
    obtain ⟨w, ⟨hw, hspec⟩, _⟩ := rowsLift (d:=d) (p:=p)
      (tableOf p (min T p) a b u.1.val z0.val r.1.1.val r.2) r.2 (min T p)
      tp.1 tp.2.1 tp.2.2.1 tp.2.2.2.1 tp.2.2.2.2 hpb hB
    let v : Fin (S8G.FpPhysicalAtom.layout d hd).nb → Bool := Fin.append s w
    have hv_left : v ∘ Fin.castAdd _ = s := funext fun q => Fin.append_left s w q
    have hv_right : v ∘ Fin.natAdd _ = w := funext fun q => Fin.append_right s w q
    have rd (j : Fin 7) (l : Fin 3) (q : Fin (d+1)) :
        get w j.castSucc l.castSucc q = (tableOf p (min T p) a b u.1.val z0.val r.1.1.val r.2 j l).testBit q.val := by
      rw [← hspec.1 j l]; exact (read_bit (get w j.castSucc l.castSucc) q).symm
    have hv_ok : Accept _ (seedTest hd p T a b) v := by
      have vp (jj : Fin 8) (ll : Fin 4) (tt : Fin (d+1)) : v (port hd jj ll tt) = get w jj ll tt :=
        Fin.append_right s w _
      have vs (bb : Bit hd) : v (st hd bb) = s bb := Fin.append_left s w bb
      rw [physical_iff, hv_left, hv_right]
      refine ⟨⟨?_, hw⟩, ?_, ?_⟩
      · unfold S8G.FpPhysicalAtom.stageTest
        erw [atPins_iff, atPins_iff]
        refine ⟨⟨hlink.1, hlink.2.2.2.1⟩, fun q => ?_⟩
        rw [hlink.2.2.2.2 ⟨d+q.val, by omega⟩]
        exact premainder (r.1.1.isLt.trans hf) ⟨d+q.val, by omega⟩ (by dsimp; omega)
      · intro q; induction q using Fin.addCases with
        | left q =>
          obtain ⟨⟨j, t⟩, rfl⟩ := finProdFinEquiv.surjective q
          simp only [ties, Fin.addCases_left, Equiv.symm_apply_apply]
          fin_cases j
          · change v (port hd 0 2 t.castSucc) = v (st hd (mul1 hd (inPos false t)))
            rw [vp, vs]; exact (rd 0 2 t.castSucc).trans (hlink.2.1 t).symm
          · change v (port hd 1 2 t.castSucc) = v (st hd (mul1 hd (inPos true t)))
            rw [vp, vs]; exact (rd 1 2 t.castSucc).trans (hlink.2.2.1 t).symm
          · change v (port hd 5 0 t.castSucc) = v (st hd (addr hd ⟨t.val, by omega⟩ 1))
            rw [vp, vs]; exact (rd 5 0 t.castSucc).trans (hlink.2.2.2.2 ⟨t.val, by omega⟩).symm
        | right q =>
          obtain ⟨⟨j, t⟩, rfl⟩ := finProdFinEquiv.surjective q
          simp only [ties, Fin.addCases_right, Equiv.symm_apply_apply]
          have W7 := (FpSlotRows.sound hpb hB hw).2.2.2.2.2.2.2.2.2.2.2 t
          rw [hspec.2] at W7
          fin_cases j
          · change v (port hd 1 2 t) = v (port hd 2 0 t)
            rw [vp, vp]; exact (rd 1 2 t).trans (rd 2 0 t).symm
          · change v (port hd 3 0 t) = v (port hd 6 0 t)
            rw [vp, vp]; exact (rd 3 0 t).trans (rd 6 0 t).symm
          · change v (port hd 4 0 t) = v (port hd 5 0 t)
            rw [vp, vp]; exact (rd 4 0 t).trans (rd 5 0 t).symm
          · change v (port hd 5 2 t) = v (port hd 6 2 t)
            rw [vp, vp]; exact (rd 5 2 t).trans (rd 6 2 t).symm
          · change v (port hd 7 1 t) = v (port hd 6 1 t)
            rw [vp, vp, W7.2.2.2]
            change _ = get w (Fin.castSucc 6) (Fin.castSucc 1) t
            rw [rd 6 1 t]
            simp (config := {decide := true}) only [tableOf, ↓reduceIte]
            cases r.2 <;> simp
      · intro q
        change v (port hd 0 0 q.castSucc) = a.testBit q.val ∧ v (port hd 5 1 q.castSucc) = b.testBit q.val
        rw [vp, vp]
        exact ⟨(rd 0 0 q.castSucc).trans (by simp [tableOf]),
               (rd 5 1 q.castSucc).trans (by simp (config := {decide := true}) [tableOf])⟩
    let x : Accepted hd seed i T k := (forget (k:=k) hd).symm ⟨v, hv_ok⟩
    have hfx : (forget (k:=k) hd x).1 = v := congrArg Subtype.val ((forget (k:=k) hd).apply_symm_apply ⟨v, hv_ok⟩)
    have hwx : rowPart hd x.1 = w := by
      change ((forget hd x).1 ∘ Fin.natAdd _) = w; rw [hfx, hv_right]
    refine ⟨x, Subtype.ext (Fin.ext ?_)⟩
    change number (rowPart hd x.1) 1 2 = u.1.val
    rw [hwx]; exact hspec.1 1 2

noncomputable def slotEquiv [Fact p.Prime] (F : Fin m → List (ZMod p)ˣ)
    (hF : (F i).Nodup ∧ (F i).toFinset = fpFactorBlock T seed i) :
    Accepted hd seed i T k ≃ Fin ((w3_fpFB F).blocks i).length :=
  (Equiv.ofBijective _ (toResidue_bijective hd mul hp hf seed i)).trans (w3_fpBlockResidueEquiv seed F i T hF).symm

theorem slotEquiv_eq_index [Fact p.Prime] (F : Fin m → List (ZMod p)ˣ)
    (hF : (F i).Nodup ∧ (F i).toFinset = fpFactorBlock T seed i) (x : Accepted hd seed i T k) :
    slotEquiv hd mul hp hf seed i F hF x = index hd mul hp hf seed i F hF x := rfl

end Bijection
end DetDLP.M3A.FpSlotBijection
noncomputable abbrev DetDLP_M3A_FpSlotBijection := @DetDLP.M3A.FpSlotBijection.slotEquiv


