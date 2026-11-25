-- Prove2me | Definitions.Def_DetDLP_S8C3_Semantics
-- name    : DetDLP_S8C3_Semantics
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T08:29:54.81775+00:00
-- url     : https://prove2.me/theorems/cc074cad-0d57-4c5b-8b45-595e38ddda00
-- title:
--   Tag 3 anchored layout, element bijection, and graph bounds
-- statement:
--   For a prime $p$ and $T\le p$, the satisfying bit assignments of the anchored tag 3 layout are in bijection with the elements of `S8C.elemSet S i T η`. Fixing the last bit to zero removes the padding coordinate; the OR scan certifies that the decoded residue is a unit. The remaining registers give precisely the witnesses consumed by `S8C3.checkedEquiv`.
--
--   **Graph bounds.** Write $b=\operatorname{bitLen}(p)$ and $A$ for the layout. Every gate has an incident edge. If $|\eta|\le b$, then $2A.\mathrm{ne}<\operatorname{scale}(\operatorname{blockCount}(b),b)$. Independently of the prefix length, every vertex has degree at most $\max\{12,\lceil136(b+2)^{3/4}\rceil\}$.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8C3_Routes
import Definitions.Def_DetDLP_S8H0_GraphDegree
import Theorems.Thm_DetDLP_w3_m5_modmul_r2

set_option autoImplicit false
namespace DetDLP.S8C3.Semantics
open S8H0 RegisterMap NamedBlocks GateSemantics S8J.CircuitRealizes
open S8J S8C M89S1
private abbrev bank (p : ℕ) := Routes.bank (d p) (e p)
def net (p T a b : ℕ) (η : List Bool) := joinB (PointGraph.zeroLast (bank p).size) (Routes.network (hd p) p T a b η)
private abbrev C (p T a b : ℕ) (η : List Bool) := AnchoredLayout.block (net p T a b η).core ((bank p).size+1)
private abbrev W (p T a b : ℕ) (η : List Bool) := AnchoredLayout.wiring (net p T a b η).core (net p T a b η).name
def layout (p T a b : ℕ) (η : List Bool) : w3_FactorLayout := circuit (C p T a b η) (W p T a b η)
def tests (p T a b : ℕ) (η : List Bool) : w3_factorTest (layout p T a b η) := test (C p T a b η) (W p T a b η)
open ResidueWires SignalBank GraphDegree S8H
private abbrev raw {p : ℕ} (u : Bits ((bank p).size+1)) := (bank p).decode (u ∘ Fin.castSucc)
private abbrev valid {p : ℕ} (v : (bank p).Data) :=
  below p v.1 ∧ (value v.1.1).val ≠ 0 ∧ below p v.2.1.1 ∧ below p v.2.1.2.1.1
noncomputable section
private def unitEq {p : ℕ} [Fact p.Prime] : {v : Triple (d p) // below p v ∧ (value v.1).val ≠ 0} ≃ (ZMod p)ˣ := by
  let f := zmodEquiv (d:=d p) (primeFitsAtom p).le
  refine (Equiv.subtypeEquivRight (q := fun v => ∃ _ : below p v, (value v.1).val ≠ 0) (fun _ => by simp)).trans ?_
  refine (Equiv.subtypeSubtypeEquivSubtypeExists (below p) (fun v => (value v.val.1).val ≠ 0)).symm.trans ((Equiv.subtypeEquiv f ?_).trans unitsEquivNeZero.symm)
  intro v; change (value v.val.1).val ≠ 0 ↔ f v ≠ 0
  have h : (f v).val = (value v.val.1).val := by change (↑((finEquiv _ v).val) : ZMod p).val = _; rw [ZMod.val_natCast_of_lt (finEquiv _ v).isLt]; apply finEquiv_val
  rw [← h, ZMod.val_ne_zero]
/-- Regroup the three range certificates into a unit, a hash run and its auxiliary registers. -/
private def typedEq {p : ℕ} [Fact p.Prime] : {v : (bank p).Data // valid v} ≃ (ZMod p)ˣ × (AtomRun p × Aux p) := by
  let split : {v : (bank p).Data // valid v} ≃ {x : Triple (d p) // below p x ∧ (value x.1).val ≠ 0} × (CheckedRun (d p) p (hd p) × _) :=
    { toFun := fun w => (⟨w.val.1,w.prop.1,w.prop.2.1⟩,(⟨w.val.2.1.1,w.prop.2.2.1⟩,(⟨w.val.2.1.2.1.1,w.prop.2.2.2⟩,w.val.2.1.2.1.2),w.val.2.1.2.2),w.val.2.2)
      invFun := fun ⟨x,⟨⟨z,⟨⟨r,q⟩,c⟩⟩,t⟩⟩ => ⟨(x.val,(z.val,(r.val,q),c),t),x.prop.1,x.prop.2,z.prop,r.prop⟩
      left_inv := by rintro ⟨⟨_,⟨⟨_,⟨⟨_,_⟩,_⟩⟩,_⟩⟩,_,_,_,_⟩; rfl, right_inv := fun _ => rfl }
  let runE := (runEquiv (hd p) (primeFitsAtom p).le).trans ((zmodFin p).symm.prodCongr (Equiv.refl _))
  exact split.trans (unitEq.prodCongr (runE.prodCongr ((auxEquiv _).prodCongr (((numBits _).prodCongr (Equiv.refl _)).prodCongr (Equiv.refl _)))))
private theorem decoded {p m : ℕ} [Fact p.Prime] (T : ℕ) (S : FpSeed p m) (i : Fin m) (η : List Bool) (u : Bits ((bank p).size+1)) :
    (Routes.network (hd p) p T ((S i).1.val+1) (S i).2.val η).OK u ↔ ∃ h : valid (raw u),
      let t := typedEq ⟨raw u,h⟩; checked T S i η t.1 t.2.1 t.2.2 := by
  classical
  refine (Routes.network_iff ..).trans ?_; let v := raw u
  have H (h : valid v) : let t := typedEq ⟨v,h⟩; ((HashRows.block p (Routes.wires (hd p) p ((S i).1.val+1) (S i).2.val)).OK u ↔ w3_slotHashBits (hd p) ((S i).1.val+1) (S i).2.val (value v.1.1) (value v.2.1.1.1) t.2.1.2 t.2.2.1) ∧ (w3_fpResidue t.1).val = (value v.1.1).val ∧ t.2.1.1.val = (value v.2.1.1.1).val := by
    let t := typedEq ⟨v,h⟩
    have X : (w3_fpResidue t.1).val = (value v.1.1).val := by
      change ((zmodFin p) (finEquiv _ ⟨v.1,h.1⟩)).val = _
      simpa [zmodFin,Nat.mod_eq_of_lt (finEquiv (primeFitsAtom p).le ⟨v.1,h.1⟩).isLt] using finEquiv_val (primeFitsAtom p).le ⟨v.1,h.1⟩
    have Z : t.2.1.1.val = (value v.2.1.1.1).val := by
      change ((zmodFin p).symm ((zmodFin p) _)).val = _; rw [Equiv.symm_apply_apply]; apply finEquiv_val
    have R : t.2.1.2.1.1.val = (value v.2.1.2.1.1.1).val := finEquiv_val _ _
    refine ⟨HashRows.block_spec (hd p) _ u _ _ _ _ _ _ (fun _ => rfl) ?_ (fun _ => rfl) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_,X,Z⟩
    all_goals dsimp only [Routes.wires,Routes.rw]
    all_goals first | rw [R]; apply GateRoutes.word_eval; intro; rfl | apply GateRoutes.word_eval; intro; rfl | (funext j; exact (Ref.correct _ _).symm) | (intro j; rw [← Ref.correct]; change (p.testBit j && v.2.1.2.2) = (@ite ℕ (v.2.1.2.2 = true) (instDecidableEqBool v.2.1.2.2 true) p 0).testBit j; cases v.2.1.2.2 <;> simp; rfl)
  constructor
  · rintro ⟨hx,hz,hr,hh,hl,ho,hη⟩; have hn := ((w3_slotOr_spec false (value v.1.1).isLt).1 _ ho).resolve_left (by decide)
    let h : valid v := ⟨hx,hn,hz,hr⟩; obtain ⟨B,X,Z⟩ := H h
    refine ⟨h,(by rw [X,Z]; exact B.mp hh),⟨(by rwa [Z]),(by rwa [X])⟩,?_⟩
    change (digitWord (bitLen p) (w3_fpResidue _).val).take _ = _; rwa [X]
  · rintro ⟨h,hh,⟨hl,ho⟩,hη⟩; obtain ⟨B,X,Z⟩ := H h
    rw [X,Z] at hh; rw [Z] at hl; rw [X] at ho
    change (digitWord (bitLen p) (w3_fpResidue _).val).take _ = _ at hη; rw [X] at hη
    exact ⟨h.1,h.2.2.1,h.2.2.2,B.mpr hh,hl,ho,hη⟩
noncomputable def points {p m : ℕ} [Fact p.Prime] {T : ℕ} (hT : T ≤ p) (S : FpSeed p m) (i : Fin m) (η : List Bool) :
    {x : Fin (layout p T ((S i).1.val + 1) (S i).2.val η).nb → Bool // ∀ g, tests p T ((S i).1.val + 1) (S i).2.val η g
      (fun e => x ((layout p T ((S i).1.val + 1) (S i).2.val η).bit e.1)) = true} ≃ ↥(S8C.elemSet S i T η) := by
  let dec := PointGraph.dropLast.trans (bank p).decode
  refine (w3_factorEquiv _ _).symm.trans ((S8J.CircuitRealizes.decode _ _).trans ((AnchoredLayout.assignments _ _).trans ?_))
  refine (Equiv.subtypeEquivRight (q := fun u => ∃ h : u (Fin.last _) = false, ∃ hv : valid (dec ⟨u,h⟩), _) ?_).trans
    ((Equiv.subtypeSubtypeEquivSubtypeExists _ _).symm.trans ((Equiv.subtypeEquivOfSubtype dec).trans
    ((Equiv.subtypeSubtypeEquivSubtypeExists _ _).symm.trans ((Equiv.subtypeEquivOfSubtype typedEq).trans (checkedEquiv hT w3_m5_modmul_r2 S i η)))))
  intro u; change (net ..).OK u ↔ _; rw [net,joinB_iff,PointGraph.zeroLast_iff,decoded]; exact ⟨fun h => ⟨h.1,h.2⟩,fun ⟨h,k⟩ => ⟨h,k⟩⟩
open w4_M5GraphBounds w4_MulParams
/-- Each multiplier vertex occurs as a source or destination of an explicit edge. -/
private theorem mulHits {n : ℕ} (hn : 1 ≤ n) : Function.Surjective (w3_fpMulLayout n hn).gate := by
  intro i; obtain ⟨v,rfl⟩ := (vertexIndex n).surjective i
  let L (e : Edge n (w4_M5GraphBounds.W n)) := Fin.castAdd (graph n hn).nE (edgeIndex _ _ e)
  let R (e : Edge n (w4_M5GraphBounds.W n)) := Fin.natAdd (graph n hn).nE (edgeIndex _ _ e)
  have l (e) : (w3_fpMulLayout n hn).gate (L e) = vertexIndex n (src hn e) := by simp [L,w3_fpMulLayout,w3_m5Layout,w3_m5HalfGate,w3_forgetSides,graph]
  have r (e) : (w3_fpMulLayout n hn).gate (R e) = vertexIndex n (dst hn e) := by simp only [R,w3_fpMulLayout,w3_m5Layout,w3_m5HalfGate,w3_forgetSides,graph,Fin.addCases_right,Equiv.symm_apply_apply]
  let j : Fin (L1 n) := ⟨0,L1_pos n⟩; let k : Fin (L2 n) := ⟨0,L2_pos n⟩
  cases v with
  | inputBit a i => exact ⟨_,l (.input a i)⟩
  | pack a i => exact ⟨_,l (.packForward a i 0)⟩
  | forward1 a b => exact ⟨_,l (.forwardMiddle a b j 0)⟩
  | forward2 a i => exact ⟨_,l (.forwardPoint a k i 0)⟩
  | pointwise b i => exact ⟨_,l (.pointInverse b i 0)⟩
  | inverse1 i => exact ⟨_,l (.inverseMiddle k i 0)⟩
  | inverse2 b => exact ⟨_,r (.inverseMiddle b j 0)⟩
  | carry i => exact ⟨_,r (.coefficient i 0)⟩
  | carrySpacer i => exact ⟨_,l (.carryRight i 0)⟩
  | outputBit i => exact ⟨_,r (.output i)⟩
private abbrev OK (p : ℕ) (A : w3_FactorLayout) := Function.Surjective A.gate ∧ bounded A (cap p)
private theorem joinOK {p : ℕ} {A B : w3_FactorLayout} (h : OK p A) (k : OK p B) : OK p (join A B) := by
  constructor <;> intro i <;> induction i using Fin.addCases with
  | left i => first | obtain ⟨e,he⟩ := h.1 i; exact ⟨Fin.castAdd _ e,by simp [join,splitMap,he]⟩ | simpa [join] using h.2 i
  | right i => first | obtain ⟨e,he⟩ := k.1 i; exact ⟨Fin.natAdd _ e,by simp [join,splitMap,he]⟩ | simpa [join] using k.2 i
private theorem rowsOK {s : Shape} {p n m : ℕ} (hm : 0 < m) (h : m ≤ 12) (r : Fin n → Fin m → Ref s) (t : Fin n → (Fin m → Bool) → Bool) : OK p (rows n m r t).core.A :=
  ⟨fun i => ⟨finProdFinEquiv (i,⟨0,hm⟩),congrArg Prod.fst (finProdFinEquiv.symm_apply_apply _)⟩,mono (row_ok n m r t) (small p _ h)⟩
private theorem scanOK {s : Shape} (p n : ℕ) (x : Fin n → Ref s) (c : Ref s) (t : Fin n → Ref s) : OK p (Routes.scan n x c t).core.A := by
  induction n generalizing c with | zero => exact rowsOK (by decide) (by decide) .. | succ n ih => exact joinOK (rowsOK (by decide) (by decide) ..) (ih ..)
private theorem coreOK (p T a b : ℕ) (η : List Bool) : OK p (C p T a b η).A := by
  have anc (k) : OK p (AnchoredLayout.anchors k) := ⟨Function.surjective_id,anchors_ok k _ (small p 1 (by decide))⟩
  have add (n) : OK p (AddLayout.layout n) := ⟨fun i => ⟨_,AddLayout.col_pos i 0⟩,fun i => (w3_gateDegree _ i).symm.le.trans ((AddLayout.gateDegree i).trans (small p 5 (by decide)))⟩
  have M : OK p (w3_fpMulLayout (d p) (hd p)) := ⟨mulHits _,mul_ok p (s:=bank p) (fun _ => .pin false)⟩
  have H (w : HashRows.Wires (d p) (hd p) (bank p)) : OK p (HashRows.block p w).core.A := by
    unfold HashRows.block HashRows.product
    refine joinOK (joinOK (joinOK M ?_) (joinOK M ?_)) (joinOK (add _) (joinOK (add _) (add _)))
    all_goals exact rowsOK (m:=2) (by decide) (by decide) _ _
  exact joinOK (anc _) (joinOK (anc _) (joinOK (add _) (joinOK (add _) (joinOK (add _) (joinOK (H _) (joinOK (add _) (joinOK (scanOK ..) (rowsOK (m:=1) (by decide) (by decide) _ _))))))))
theorem gate_surj (p T a b : ℕ) (η : List Bool) : Function.Surjective (layout p T a b η).gate := by
  let A := (C p T a b η).A
  intro i; induction i using Fin.addCases with
  | left i => obtain ⟨e,he⟩ := (coreOK p T a b η).1 i; exact ⟨Fin.castAdd _ e,by simp [layout,circuit,CopyCycle.layout,he]⟩
  | right i => exact ⟨Fin.natAdd A.ne (Fin.castAdd _ i),by simp [layout,circuit,CopyCycle.layout,A]⟩
theorem degree (p T a b : ℕ) (η : List Bool) (v : Fin (w3_factorGraph (layout p T a b η)).nV) :
    (w3_factorGraph (layout p T a b η)).deg v ≤ max 12 (Nat.ceil (136 * ((bitLen p : ℝ) + 2) ^ ((3 : ℝ) / 4))) := by
  let A := (C p T a b η).A; let f := AnchoredLayout.signal (net p T a b η).core (net p T a b η).name
  induction v using Fin.addCases with
  | left i => induction i using Fin.addCases with
              | left i => exact (NamedWires.oldDegree f A.gate i).le.trans ((coreOK p T a b η).2 i)
              | right i => exact (NamedWires.eqDegree f A.gate i).le.trans (small p 2 (by decide))
  | right i => exact (CopyCycle.bitDegree A.gate (NamedWires.next f) i).le.trans (small p 3 (by decide))
private theorem scanE {s : Shape} (n : ℕ) (x : Fin n → Ref s) (c : Ref s) (t : Fin n → Ref s) :
    (Routes.scan n x c t).core.A.ne = 3*n+1 := by
  induction n generalizing c with | zero => rfl | succ n ih => simp only [Routes.scan,joinB,join,rows,mapped,ih]; omega
theorem edgeBudget (p T a b : ℕ) [Fact p.Prime] (η : List Bool) (hη : η.length ≤ bitLen p) :
    2 * (layout p T a b η).ne < S8G.FpMoment.scale (blockCount (bitLen p)) (bitLen p) := by
  have h : (net p T a b η).core.A.ne = 4*e p + 59*d p + 32 + η.length := by
    simp only [net,Routes.network,joinB,join,RangeRows.checker,HashRows.block,HashRows.product,eqs,HashRows.sumRows,Routes.ltRows,NamedBlocks.add,scanE,Routes.pref,rows,mapped,AddLayout.layout,PointGraph.zeroLast,AnchoredLayout.anchors,w3_fpMulLayout,w3_m5Layout,w3_forgetSides,e]; omega
  have k : (bank p).size = 22*d p + 8 + 2*e p := by simp [bank,Routes.bank,triple,run,mul,GateRoutes.auxShape,Shape.size]; omega
  have g := graph_edge_bound (hd p)
  have low := Nat.mul_le_mul_right (bitLen p+2) (Nat.mul_le_mul_left 65536 (le_max_left 2 _ : 2 ≤ blockCount (bitLen p)))
  change 2*((((bank p).size+1)+(net p T a b η).core.A.ne) + ((((bank p).size+1)+(net p T a b η).core.A.ne)+(((bank p).size+1)+(net p T a b η).core.A.ne))) < _
  rw [h,k]; apply lt_of_lt_of_le _ low; simp only [e,d,ECPointArithmetic.width] at *; omega
end
end DetDLP.S8C3.Semantics


