-- Prove2me | Definitions.Def_DetDLP_S8H0_BaseCode
-- name    : DetDLP_S8H0_BaseCode
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T08:20:45.430128+00:00
-- url     : https://prove2.me/theorems/e0acb1cd-ee70-4ffd-a0ba-35c24d50e91b
-- title:
--   Tag 0 base layout code and register-name addresses
-- statement:
--   Let $A_{p,c}$ denote the anchored point-network layout. The natural-number code `baseCode` models $A_{p,c}$: its gate, bit, and incidence counts agree with those of the layout, and both address functions agree on every valid incidence. The layout code is uniform in $p$, including the equality rows that connect multiplier ports. The total register-name function `sigName` agrees with the anchored signal map on valid incidences and returns zero otherwise. For fixed $p,c$, finite-table lookup gives polynomial-time register names and copy-cycle endpoints. For a varying family, `sigName_poly_of_table` gives the corresponding lookup bound assuming polynomial-time construction of its name table.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8H0_PointGraph
import Definitions.Def_DetDLP_S8H0_CycleCode

set_option autoImplicit false
namespace DetDLP.S8H0.BaseCode
open S8H.PointAddresses Groundwork GateSemantics GateRoutes RegisterMap NamedBlocks PointGraph

/-- A row has one gate and `m` distinct input ports. -/
def rowsCode (n m : ℕ) : Code := ⟨n,n*m,n*m,(·/m),id⟩
private theorem rows_spec {s : Shape} (n m : ℕ) (r : Fin n → Fin m → Ref s) (t) :
    Models (rowsCode n m) (rows n m r t).core.A := ⟨rfl,rfl,rfl,fun _ => rfl,fun _ => rfl⟩

private def rangeCode (d : ℕ) := let a := S8H.PointAddresses.add (d+1); sum (sum a a) (copiesCode (sum a a) 6)
private def hashCode (d : ℕ) := let m := sum (S8H.PointAddresses.mul d) (rowsCode (4*d) 2)
  sum (sum m m) (sum (add (2*d)) (sum (add (d+1)) (add (d+1))))
private def body (d : ℕ) := sum (AnchoredLayout.anchorCode 1)
  (sum (rangeCode d) (sum (copiesCode (hashCode d) 6) (rowsCode d 5)))

def baseCode (p : ℕ) := AnchoredLayout.withAnchors (regs (d p)+1) (body (d p))

private theorem many_spec {k : ℕ} (n : ℕ) (f : Fin (n+1) → B k) (a : Code)
    (hf : ∀ i, Models a (f i).core.A) : Models (copiesCode a n) (RangeRows.many n f).core.A := by
  induction n with
  | zero => exact hf 0
  | succ n ih => exact sum_spec (hf 0) (ih (fun i => f i.succ) (fun i => hf _))

private theorem range_spec (d e p : ℕ) : Models (rangeCode d) (RangeRows.block d e p).core.A :=
  sum_spec (sum_spec (add_spec _) (add_spec _)) (many_spec _ _ _ fun _ => sum_spec (add_spec _) (add_spec _))
private theorem hash_spec' {d : ℕ} {hd : 1 ≤ d} {s : Shape} (p : ℕ) (w : HashRows.Wires d hd s) :
    Models (hashCode d) (HashRows.block p w).core.A :=
  sum_spec (sum_spec (sum_spec (mul_spec hd) (rows_spec _ _ _ _)) (sum_spec (mul_spec hd) (rows_spec _ _ _ _)))
    (sum_spec (add_spec _) (sum_spec (add_spec _) (add_spec _)))

theorem models (p : ℕ) (c : Coeff) : Models (baseCode p) (C p c).A := by
  have hk : regs (d p) = (S (d p) (e p)).size := by unfold regs; rw [wires_eq (hd p)]
  unfold baseCode; rw [hk]
  exact sum_spec (AnchoredLayout.anchorModels _) (sum_spec (AnchoredLayout.anchorModels 1)
    (sum_spec (range_spec ..) (sum_spec (many_spec _ _ _ fun i => hash_spec' _ (wires (hd p) p c i)) (rows_spec _ _ _ _))))

attribute [local fun_prop] PolyT.mul PolyT.div PolyT.const PolyT.comp PolyT.id' regs_poly w4_M5Evaluator.clog2_poly
private theorem rows_poly (n : ℕ → ℕ) (m : ℕ) (hn : ∀ {α : Type} [Enc α] {g : α → ℕ}, PolyT g → PolyT fun x => n (g x)) :
    Uniform fun g => rowsCode (n g) m := by constructor <;> intros <;> simp only [rowsCode,id_eq] <;> fun_prop (disch := solve_by_elim)
private theorem anchors_poly (n : ℕ → ℕ) (hn : ∀ {α : Type} [Enc α] {g : α → ℕ}, PolyT g → PolyT fun x => n (g x)) :
    Uniform fun g => AnchoredLayout.anchorCode (n g) := by
  constructor <;> intros <;> simp only [AnchoredLayout.anchorCode,id_eq] <;> first | assumption | apply hn; assumption
private theorem baseWidth_poly : Uniform (fun d => AnchoredLayout.withAnchors (regs d+1) (body d)) := by
  have a := add_poly (fun d => d+1) (by intros; fun_prop)
  have b := add_poly (fun d => 2*d) (by intros; fun_prop)
  have m := sum_poly mul_poly (rows_poly (fun d => 4*d) 2 (by intros; fun_prop))
  have r := sum_poly (sum_poly a a) (copies_poly (sum_poly a a) 6)
  have h := sum_poly (sum_poly m m) (sum_poly b (sum_poly a a))
  exact sum_poly (anchors_poly (fun d => regs d+1) (by intros; fun_prop)) (sum_poly (anchors_poly (fun _ => 1) (by intros; fun_prop))
    (sum_poly r (sum_poly (copies_poly h 6) (rows_poly id 5 (by intros; assumption)))))

theorem uniform : Uniform baseCode := by
  have H {α : Type} [Enc α] {p : α → ℕ} (hp : PolyT p) : PolyT fun x => d (p x) := by
    unfold d S8H.ECPointArithmetic.width bitLen; fun_prop
  constructor
  · intros; exact baseWidth_poly.ng (H ‹_›)
  · intros; exact baseWidth_poly.nb (H ‹_›)
  · intros; exact baseWidth_poly.ne (H ‹_›)
  · intros; exact baseWidth_poly.gate (H ‹_›) ‹_›
  · intros; exact baseWidth_poly.bit (H ‹_›) ‹_›

/-- Out-of-range port queries return zero. -/
def sigName (p : ℕ) (c : Coeff) (i : ℕ) : ℕ := if h : i < (C p c).A.ne then
  (AnchoredLayout.signal (net p c).core (net p c).name ⟨i,h⟩).val else 0

theorem sigName_spec (p : ℕ) (c : Coeff) (i : Fin (C p c).A.ne) : sigName p c i.val =
    (AnchoredLayout.signal (net p c).core (net p c).name i).val := by simp [sigName,i.isLt]

/-- A fixed layout's register names form a finite table, extended by zero. -/
def nameTable (p : ℕ) (c : Coeff) : List ℕ := List.ofFn fun i : Fin (C p c).A.ne =>
  (AnchoredLayout.signal (net p c).core (net p c).name i).val

theorem table_spec (p : ℕ) (c : Coeff) (i : ℕ) : (nameTable p c).getD i 0 = sigName p c i := by
  unfold nameTable sigName; split <;> rename_i h
  · rw [List.getD_eq_getElem _ _ (by simpa using h),List.getElem_ofFn]
  · exact List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt h)

theorem sigName_poly (p : ℕ) (c : Coeff) : PolyT (sigName p c) :=
  (PolyT.getD (PolyT.const (nameTable p c)) PolyT.id' (PolyT.const 0)).congr (table_spec p c)

/-- For a varying family, table construction and address lookup are separate operations. -/
theorem sigName_poly_of_table {α : Type} [Enc α] {p : α → ℕ} {c : α → Coeff} {i : α → ℕ}
    (ht : PolyT fun x => nameTable (p x) (c x)) (hi : PolyT i) :
    PolyT fun x => sigName (p x) (c x) (i x) :=
  (PolyT.getD ht hi (PolyT.const 0)).congr fun x => table_spec (p x) (c x) (i x)

theorem cycle_models (p : ℕ) (c : Coeff) :
    Models (CycleCode.code (baseCode p) (sigName p c)) (layout p c) := by
  have h := CycleCode.models (models p c) (sigName p c)
  have hn := AnchoredLayout.next_congr (fun i : Fin (C p c).A.ne => sigName p c i.val)
    (AnchoredLayout.signal (net p c).core (net p c).name) (by intro i j; rw [sigName_spec,sigName_spec]; exact Fin.val_inj)
  rw [hn] at h; exact h

theorem cycle_endpoints_poly (p : ℕ) (c : Coeff) :
    PolyT (CycleCode.code (baseCode p) (sigName p c)).gate ∧
    PolyT (CycleCode.code (baseCode p) (sigName p c)).bit := by
  let a := baseCode p
  have H := CycleCode.endpoints_poly (α := Unit) (c := fun _ => a) (name := fun _ => sigName p c)
    (PolyT.const _) (PolyT.const _) (PolyT.const _) (PolyT.comp (uniform.gate (PolyT.const p) PolyT.id') (PolyT.snd PolyT.id'))
    (PolyT.comp (sigName_poly p c) (PolyT.snd PolyT.id'))
  have h : PolyT fun i : ℕ => ((),i) := PolyT.prodMk (PolyT.const ()) PolyT.id'
  have hg := PolyT.comp H.1 h
  have hb := PolyT.comp H.2 h
  exact ⟨hg,hb⟩

end DetDLP.S8H0.BaseCode


