-- Prove2me | Definitions.Def_DetDLP_S8H0_CoreCheck
-- name    : DetDLP_S8H0_CoreCheck
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T08:41:22.102867+00:00
-- url     : https://prove2.me/theorems/901d5864-f253-490d-8445-42c9b7cc274c
-- title:
--   Tag 0 polynomial-time arithmetic gate evaluator
-- statement:
--   For a decoded coefficient list, a vertex index, and a local Boolean word, `CoreCheck.gate` computes a Boolean in polynomial time. Multiplication rows reorder the input word from the source-half/destination-half partition into the W4 port order before applying `evalNat`. The remaining numeric branches handle the carry, pin, and curve rows. The theorem `gate_poly` proves closure under polynomial-time input maps.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8J_HashGatePoly
import Definitions.Def_DetDLP_S8H0_GraphBudget
import Definitions.Def_DetDLP_S8G_FpMomentPoly

set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace DetDLP.S8H0.CoreCheck
open Groundwork w4_M5GateOps w4_M5GraphBounds
abbrev W := List Bool
attribute [local fun_prop] PolyT.fst PolyT.snd PolyT.comp PolyT.const PolyT.prodMk PolyT.id' PolyT.mul
  PolyT.div PolyT.mod PolyT.length PolyT.getD PolyT.testBit PolyT.idxOf PolyT.append PolyT.filter
  P2M_Groundwork_PolyT_id__1c5d0f44cc8f P2M_Groundwork_PolyT_ite__226169acf219
  P2M_Groundwork_PolyT_cond__4c673073da15 P2M_Groundwork_PolyT_cons__3a60f43a3b86
  w4_M5Dispatch.evalNat_poly w4_M5Evaluator.vertexCount_poly RegisterMap.regs_poly w4_M5GateOps.portList_poly w4_M5EdgeNat.srcNat_poly

def pad (p : ℕ) := () :: (p-1).bits.map (fun _ => ())
@[local fun_prop] theorem pad_poly {α} [Enc α] {p : α → ℕ} (hp : PolyT p) : PolyT (fun x => pad (p x)) := by
  unfold pad; apply P2M_Groundwork_PolyT_cons__3a60f43a3b86 (PolyT.const ()); apply PolyT.map (f := fun _ (_ : Bool) => ()) (PolyT.const ()); fun_prop

/-- Incidences in the multiplication layout list source half-edges before destination half-edges. -/
def reorder (q : Pad) (g : ℕ) (a : W) :=
  let ps := portList q g
  let ls := ps.filter (fun e => decide (w4_M5EdgeNat.srcNat q.length e = g))
  let rs := ps.filter (fun e => decide (w4_M5EdgeNat.srcNat q.length e ≠ g))
  ps.map fun e => a.getD ((ls++rs).idxOf e) false

@[local fun_prop] theorem reorder_poly {α} [Enc α] {q : α → Pad} {g : α → ℕ} {a : α → W}
    (hq : PolyT q) (hg : PolyT g) (ha : PolyT a) : PolyT fun x => reorder (q x) (g x) (a x) := by
  let ps := fun x => portList (q x) (g x)
  have hl : PolyT ps := portList_poly hq hg
  have hq' := PolyT.comp hq (PolyT.fst (PolyT.id' (α := α × ℕ)))
  have hg' := PolyT.comp hg (PolyT.fst (PolyT.id' (α := α × ℕ)))
  have L := PolyT.filter (f := fun x e => decide (w4_M5EdgeNat.srcNat (q x).length e = g x)) (by fun_prop) hl
  have R := PolyT.filter (f := fun x e => decide (w4_M5EdgeNat.srcNat (q x).length e ≠ g x)) (by fun_prop) hl
  have P := PolyT.comp (PolyT.append L R) (PolyT.fst (PolyT.id' (α := α × ℕ)))
  have ha' := PolyT.comp ha (PolyT.fst (PolyT.id' (α := α × ℕ)))
  unfold reorder; apply PolyT.map (hl := hl); apply PolyT.getD ha' (PolyT.idxOf (by fun_prop) P) (PolyT.const _)

def column (n i : ℕ) (x y z c last : Bool) := decide
  (x.toNat+y.toNat+c.toNat = z.toNat+2*last.toNat ∧ (i+1 ≠ n ∨ last = false))

def opA (ns : List ℕ) (g i : ℕ) (b : Bool) :=
  if g=0 then (ns.getD 1 0).testBit i else if g=1 ∨ g=3 then decide (i=0) else if g=6 then false else b

def opB (ns : List ℕ) (g i d : ℕ) (b : Bool) :=
  if g=0 then decide (i<d) && b else if g=1 then (ns.getD 3 0).testBit i else
  if g=3 then (ns.getD 2 0).testBit i else if g=4 then (ns.getD 4 0).testBit i else
  if g=5 then (ns.getD 5 0).testBit i else false

/-- A product gate or a constraint linking an external product pin to its signal. -/
def product (q : Pad) (ns : List ℕ) (g p t : ℕ) (a : W) :=
  let d := q.length; let nv := vertexCount d; let k := t % (nv+4*d)
  if k < nv then w4_M5Dispatch.evalNat q k (reorder q k a) else
  let i := k-nv; let b := a.getD 1 false
  let pin := if i < d ∧ t < nv+4*d then opA ns g i b else
    if d ≤ i ∧ i < 2*d ∧ nv+4*d ≤ t then p.testBit (i-d) else b
  a.getD 0 false == pin

/-- Seven slots, each consisting of two pinned products and three carry chains. -/
def hash (q : Pad) (ns : List ℕ) (p g k : ℕ) (a : W) :=
  let d := q.length; let m := 2*(vertexCount d+4*d)
  if k < m then product q ns g p k a else
  let j := k-m; let n := if j<2*d then 2*d else d+1
  let i := if j<2*d then j else (j-2*d)%(d+1)
  let y := if j<2*d then decide (i<d) && a.getD 1 false else
    if j<3*d+1 then opB ns g i d (a.getD 1 false) else p.testBit i && a.getD 1 false
  column n i (decide (j<2*d ∨ i<d) && a.getD 0 false) y (a.getD 2 false)
    (decide (i≠0) && a.getD 4 false) (a.getD 3 false)

def gate (ns : List ℕ) (v : ℕ) (a : W) :=
  let p := ns.getD 0 0; let q := pad p; let d := q.length; let n := d+1
  let anchors := RegisterMap.regs d+1; let j := v-(anchors+1); let i := j%n
  let h := 2*(vertexCount d+4*d) + 2*d + 2*n; let k := j-16*n
  if v<anchors then true else if v=anchors then !a.getD 0 false else
  if j<16*n then column n i (decide (i<d) && a.getD 0 false) (decide (i<d) && a.getD 1 false)
    (p.testBit i) (decide (i=0) || a.getD 4 false) (a.getD 3 false) else
  if k<7*h then hash q ns p (k/h) (k%h) a else if k<7*h+d then
    CurveRows.test (a.getD 0 false) (a.getD 1 false) (a.getD 2 false) (a.getD 3 false) (a.getD 4 false)
  else a.getD 0 false == a.getD 1 false

attribute [local irreducible] w4_M5Dispatch.evalNat w4_M5GraphBounds.vertexCount RegisterMap.regs reorder pad Nat.testBit
section Uniform
variable {α : Type} [Enc α] {q : α → Pad} {ns : α → List ℕ} {p g k : α → ℕ} {a : α → W}
@[local fun_prop] theorem column_poly {n i : α → ℕ} {x y z c l : α → Bool} (hn : PolyT n) (hi : PolyT i)
    (hx : PolyT x) (hy : PolyT y) (hz : PolyT z) (hc : PolyT c) (hl : PolyT l) :
    PolyT fun t => column (n t) (i t) (x t) (y t) (z t) (c t) (l t) := by unfold column; fun_prop
@[local fun_prop] theorem product_poly (hq : PolyT q) (hs : PolyT ns) (hg : PolyT g) (hp : PolyT p)
    (hk : PolyT k) (ha : PolyT a) : PolyT fun x => product (q x) (ns x) (g x) (p x) (k x) (a x) := by
  let d := fun x => (q x).length; let n := fun x => vertexCount (d x); let m := fun x => n x+4*d x
  let t := fun x => k x % m x; let i := fun x => t x - n x
  have hd : PolyT d := PolyT.length hq; have hn : PolyT n := w4_M5Evaluator.vertexCount_poly hd
  have hm : PolyT m := PolyT.add hn (PolyT.mul (PolyT.const _) hd)
  have ht : PolyT t := PolyT.mod hk hm; have hi : PolyT i := PolyT.sub ht hn
  unfold product; dsimp only
  apply PolyT.ite' (c := fun x => t x < n x) (by fun_prop) (w4_M5Dispatch.evalNat_poly hq ht (reorder_poly hq ht ha))
  change PolyT fun x => (a x).getD 0 false == (if i x < d x ∧ k x < m x then opA (ns x) (g x) (i x) ((a x).getD 1 false) else if d x ≤ i x ∧ i x < 2*d x ∧ m x ≤ k x then (p x).testBit (i x-d x) else (a x).getD 1 false)
  unfold opA; fun_prop
@[local fun_prop] theorem hash_poly (hq : PolyT q) (hs : PolyT ns) (hp : PolyT p) (hg : PolyT g)
    (hk : PolyT k) (ha : PolyT a) : PolyT fun x => hash (q x) (ns x) (p x) (g x) (k x) (a x) := by
  simp only [hash,opB]; fun_prop (disch := assumption)
theorem gate_poly (hs : PolyT ns) (hk : PolyT k) (ha : PolyT a) : PolyT fun x => gate (ns x) (k x) (a x) := by
  let pp := fun x => (ns x).getD 0 0; let d := fun x => (pad (pp x)).length
  have hp : PolyT pp := PolyT.getD hs (PolyT.const _) (PolyT.const _)
  have hd : PolyT d := PolyT.length (pad_poly hp)
  have hr := RegisterMap.regs_poly hd
  have hv := w4_M5Evaluator.vertexCount_poly hd
  let n := fun x => d x+1; let j := fun x => k x-(RegisterMap.regs (d x)+1+1)
  let h := fun x => 2*(vertexCount (d x)+4*d x)+2*d x+2*n x; let t := fun x => j x-16*n x
  have hn : PolyT n := PolyT.add hd (PolyT.const _)
  have hj : PolyT j := PolyT.sub hk (PolyT.add (PolyT.add hr (PolyT.const _)) (PolyT.const _))
  have hh : PolyT h := by unfold h; fun_prop
  have ht : PolyT t := by unfold t; fun_prop
  let i := fun x => j x%n x; have hi : PolyT i := PolyT.mod hj hn
  have hc := hash_poly (pad_poly hp) hs hp (PolyT.div ht hh) (PolyT.mod ht hh) ha
  unfold gate; dsimp only
  apply PolyT.ite' (c := fun x => k x < RegisterMap.regs (d x)+1) (by fun_prop) (PolyT.const _)
  apply PolyT.ite' (c := fun x => k x = RegisterMap.regs (d x)+1) (by fun_prop) (by fun_prop)
  apply PolyT.ite' (c := fun x => j x < 16*n x) (by fun_prop)
  · change PolyT fun x => column (n x) (i x) (decide (i x<d x) && (a x).getD 0 false) (decide (i x<d x) && (a x).getD 1 false) ((pp x).testBit (i x)) (decide (i x=0) || (a x).getD 4 false) ((a x).getD 3 false)
    fun_prop
  · apply PolyT.ite' (c := fun x => t x < 7*h x) (by fun_prop) hc
    apply PolyT.ite' (c := fun x => t x < 7*h x+d x) (by fun_prop)
    · unfold CurveRows.test; fun_prop
    · fun_prop
end Uniform
end DetDLP.S8H0.CoreCheck


