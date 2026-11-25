-- Prove2me | Definitions.Def_DetDLP_S8M_AtomMapNat
-- name    : DetDLP_S8M_AtomMapNat
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-25T01:10:32.060801+00:00
-- url     : https://prove2.me/theorems/d3d4b66d-f107-4765-aa78-a7fa17e0def1
-- title:
--   Tag 6 pure-ℕ atomN and mapN NC combinators and Eff bounds
-- statement:
--   **Register layout.** For width $d$ and edge count $e$, an atom slot occupies $122d+14e+46$ registers and a conversion map occupies $70d+8e+27$. The bank contains $2m$ slots of each kind and $2m\mathbin{\dot-}1$ addition slots. Its size is the common address for public pins.
--
--   **Uniformity.** `atomN` and `mapN` compute the code and register names of a single slot from $(m,d,e,i)$. The theorems `atomN_eff` and `mapN_eff` establish `Eff` whenever the four parameters are polynomial-time functions of the input. The proof composes the hash, range, column, and row bounds and uses fixed-length concatenation for the gate families.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8M_EffCombinators
import Definitions.Def_DetDLP_S8M_Routes

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace DetDLP.S8M.AtomMapNat
open S8H0 RegisterMap S8H.MakeCombinators EffCombinators Groundwork

theorem slot_size (d e : ℕ) : (ECAtomSlot.slotShape d e).size = 122*d+14*e+46 := by
  simp only [ECAtomSlot.slotShape,S8H4.Routes.bank,GateRoutes.S,RegisterMap.bank,run,mul,triple,Shape.size]; omega
theorem map_size (d e : ℕ) : (ECMapRows.mapShape d e).size = 70*d+8*e+27 := by
  simp only [ECMapRows.mapShape,ECMapRows.slot,run,mul,triple,GateRoutes.auxShape,Shape.size]; omega
theorem bank_size (m d e : ℕ) : (Routes.bank m d e).size =
    2*m*(122*d+14*e+46)+(2*m*(70*d+8*e+27)+(2*m-1)*(253*d+30*e+97)) := by
  have h : (S8N.ECAddRoutes.addShape d e).size = 253*d+30*e+97 := by
    simp only [S8N.ECAddRoutes.addShape,ECMapRows.slot,run,mul,triple,GateRoutes.auxShape,Shape.size]; omega
  simp only [Routes.bank,Shape.size,slot_size,map_size,h]

/-- A hash run and its auxiliary words may occupy separate banks. -/
private def hashN (d e pin z aux : ℕ) (a x b : ℕ → ℕ) : NC :=
  let w := fun o n => wd o n pin; let r := z+3*d+1; let q := r+3*d+1
  let p := q+d; let t := p+2*d+e
  genHashN d e (p+2*d) (t+2*d) pin a x b (w z d) (w r d) (w q d) (w p (2*d)) (w t (2*d))
    (w (aux+2*d) (d+1)) (fun _ => t+2*d+e) (aux+·) (aux+3*d+1+·) (aux+4*d+2+·)

/-- Flatten one atom slot, including the threshold and seven-input seed rows. -/
def atomN (m d e i : ℕ) : NC :=
  let pin := (Routes.bank m d e).size; let w := fun o => wd o d pin
  let o := i*(ECAtomSlot.slotShape d e).size; let x := o+1; let tr := 3*d+1; let y := x+tr
  let stride := 11*d+2*e+3; let z := fun g => y+tr+g*stride
  let aux := fun g => z 7+g*(5*d+3); let seed := aux 7; let P := fun (_ : ℕ) => pin
  let rng := rangeN d pin; let ranges := catN (catN (rng x) (rng y)) (manyN 6 fun g => catN (rng (z g)) (rng (z g+tr)))
  let h := fun g => hashN d e pin (z g) (aux g)
    (fun j => if g=2 then w (z 1) j else if g=4 then w (z 3) j else if g=5 then w (z 4) j else pin)
    (fun j => if g=1 then w (z 0) j else if g=2 then w y j else w x j) (fun j => if g=0 then w y j else pin)
  let curve := rowN d 5 fun j k => if k=0 then o else if k=1 then x+j else if k=2 then y+j else if k=3 then z 2+j else z 5+j
  let ltT := colN (d+1) (w (z 6)) (w (seed+2*d)) P (seed+3*d+·)
  let fixed := catN (catN ranges (catN (manyN 5 h) curve)) (catN (hashN d e pin (z 6) (aux 6) (w seed) (w x) (w (seed+d))) (catN (rowN 1 1 fun _ _ => o) ltT))
  catN fixed (rowN d 7 fun j k => if k=0 then w y 0 else if k=1 then seed+j else if k=2 then seed+d+j else pin)

/-- Four interleaved run/auxiliary slots for conversion to short Weierstrass form. -/
def mapN (m d e i : ℕ) : NC :=
  let pin := (Routes.bank m d e).size; let w := fun o => wd o d pin
  let slot := (ECAtomSlot.slotShape d e).size; let a := i*slot
  let o := 2*m*slot+i*(ECMapRows.mapShape d e).size; let tr := 3*d+1
  let x := o+1; let y := x+tr; let z := fun g => y+tr+g*(16*d+2*e+6)
  let rng := rangeN d pin; let ranges := catN (catN (rng x) (rng y)) (manyN 3 fun g => catN (rng (z g)) (rng (z g+tr)))
  let h := fun g => hashN d e pin (z g) (z g+11*d+2*e+3) (fun _ => pin)
    (fun j => if g=3 then w (z 2) j else if g=2 then w (a+1+tr) j else w (a+1) j) (fun j => if g=2 then w (z 1) j else pin)
  let mask := fun u v => rowN d 3 fun j k => if k=0 then a else if k=1 then u+j else v+j
  catN ranges (catN (manyN 3 h) (catN (rowN 1 2 fun _ k => if k=0 then o else a) (catN (mask x (z 0)) (mask y (z 3)))))

attribute [local fun_prop] PolyT.const PolyT.add PolyT.sub PolyT.mul PolyT.decide_eq wdP P2M_Groundwork_PolyT_ite__226169acf219
variable {α : Type} [Enc α] {M D E I : α → ℕ}
private theorem hashP {P Z U : α → ℕ} {A X B : α → ℕ → ℕ} (hd : PolyT D) (he : PolyT E)
    (hp : PolyT P) (hz : PolyT Z) (hu : PolyT U) (ha : FP A) (hx : FP X) (hb : FP B) :
    Eff fun x => hashN (D x) (E x) (P x) (Z x) (U x) (A x) (X x) (B x) := by
  unfold hashN; apply genHashP <;> first | assumption | (intro J hj; fun_prop) | fun_prop

attribute [local irreducible] catN rangeN manyN hashN rowN colN Eff
theorem atomN_eff (hm : PolyT M) (hd : PolyT D) (he : PolyT E) (hi : PolyT I) :
    Eff fun x => atomN (M x) (D x) (E x) (I x) := by
  simp only [atomN, bank_size, slot_size]
  repeat' first | apply catP | (apply manyN_const_poly; intro g) | apply rangeP | apply hashP | apply rowP | apply colP
  all_goals first | (intro J K hj hk; fun_prop) | (intro J hj; fun_prop) | fun_prop

theorem mapN_eff (hm : PolyT M) (hd : PolyT D) (he : PolyT E) (hi : PolyT I) :
    Eff fun x => mapN (M x) (D x) (E x) (I x) := by
  simp only [mapN, bank_size, slot_size, map_size]
  repeat' first | apply catP | (apply manyN_const_poly; intro g) | apply rangeP | apply hashP | apply rowP
  all_goals first | (intro J K hj hk; fun_prop) | (intro J hj; fun_prop) | fun_prop

end DetDLP.S8M.AtomMapNat


