-- Prove2me | Definitions.Def_DetDLP_S8H4_BaseCode
-- name    : DetDLP_S8H4_BaseCode
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T14:23:49.975351+00:00
-- url     : https://prove2.me/theorems/ecf07582-54ef-497c-a59e-6f8dac942658
-- title:
--   Tag 4 pure Code layout, Models, and Uniformity
-- statement:
--   ## S8H4 element query code layout\n\nWe define the natural-number code for the anchored S8H4 element query circuit. For input parameter p and query word length l, the code is the outer anchored layout around the zero-last network and its component codes. The construction includes range checks, repeated hash blocks, seed-selection rows, the threshold comparison, and the query-bit rows.\n\nThe model theorem proves that this code describes the anchored network layout. The uniformity theorem establishes polynomial dependence on both p and l, including the final rowsCode l 1 block. This gives a pure Code-level account of the complete S8H4 layout and its size, gate, and bit-index functions.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8H0_BaseCode
import Definitions.Def_DetDLP_S8H4_Semantics

set_option autoImplicit false
namespace DetDLP.S8H4.BaseCode
open S8H0 S8H.PointAddresses Groundwork GateSemantics GateRoutes RegisterMap NamedBlocks PointGraph
open DetDLP.S8H0.BaseCode DetDLP.S8H4.Routes DetDLP.S8H4.Semantics

private def rangeCode (d : ℕ) := let a := S8H.PointAddresses.add (d+1); sum (sum a a) (copiesCode (sum a a) 6)
private def hashCode (d : ℕ) := let m := sum (S8H.PointAddresses.mul d) (rowsCode (4*d) 2)
  sum (sum m m) (sum (add (2*d)) (sum (add (d+1)) (add (d+1))))
private def body (d l : ℕ) := sum (AnchoredLayout.anchorCode 1)
  (sum (sum (rangeCode d) (sum (copiesCode (hashCode d) 5) (rowsCode d 5)))
    (sum (hashCode d) (sum (rowsCode d 3) (sum (rowsCode 1 1) (sum (add (d+1)) (rowsCode l 1))))) )

def elemCode (p l : ℕ) : Code := AnchoredLayout.withAnchors (regs (d p)+4*(d p)+2) (body (d p) l)

private theorem rows_spec {s : Shape} (n m : ℕ) (r : Fin n → Fin m → Ref s) (t) :
    Models (rowsCode n m) (rows n m r t).core.A := ⟨rfl,rfl,rfl,fun _ => rfl,fun _ => rfl⟩

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

theorem models (p T a0 b0 a1 b1 : ℕ) (c : Coeff) (η : List Bool) :
    Models (elemCode p η.length)
      (AnchoredLayout.block
        (joinB (PointGraph.zeroLast (Routes.bank (d p) (e p)).size)
          (network (hd p) p T a0 b0 a1 b1 c η)).core
        ((Routes.bank (d p) (e p)).size+1)).A := by
  have hk : (Routes.bank (d p) (e p)).size + 1 = regs (d p) + 4*(d p)+2 := by
    change (GateRoutes.S (d p) (e p)).size + (d p + (d p + (d p + (d p+1)))) + 1 = _
    rw [GraphBudget.anchorSize]; omega
  unfold elemCode; rw [← hk]
  simp only [AnchoredLayout.block, joinB]
  exact sum_spec (AnchoredLayout.anchorModels ((Routes.bank (d p) (e p)).size+1))
    (sum_spec (AnchoredLayout.anchorModels 1)
      (sum_spec
        (sum_spec (range_spec ..)
          (sum_spec (many_spec _ _ _ fun i => hash_spec' _ (GateRoutes.wires (hd p) p c i.castSucc)) (rows_spec _ _ _ _)))
        (sum_spec (hash_spec' _ (network.six (hd p) p c))
          (sum_spec (rows_spec _ _ _ _)
            (sum_spec (rows_spec _ _ _ _)
              (sum_spec (add_spec _) (rows_spec _ _ _ _)))))))

attribute [local fun_prop] PolyT.add PolyT.sub PolyT.mul PolyT.div PolyT.const PolyT.comp PolyT.id' PolyT.fst PolyT.snd PolyT.ite' PolyT.decide_lt regs_poly w4_M5Evaluator.clog2_poly
private theorem rows_poly (n : ℕ → ℕ) (m : ℕ) (hn : ∀ {α : Type} [Enc α] {p : α → ℕ}, PolyT p → PolyT fun x => n (p x)) : Uniform (fun p => rowsCode (n p) m) := by
  constructor <;> intros <;> simp only [rowsCode,id_eq] <;> fun_prop (disch := solve_by_elim [hn])

structure Uniform2 (c : ℕ → ℕ → Code) : Prop where
  ng : ∀ {α : Type} [Enc α] {p l : α → ℕ}, PolyT p → PolyT l → PolyT fun x => (c (p x) (l x)).ng
  nb : ∀ {α : Type} [Enc α] {p l : α → ℕ}, PolyT p → PolyT l → PolyT fun x => (c (p x) (l x)).nb
  ne : ∀ {α : Type} [Enc α] {p l : α → ℕ}, PolyT p → PolyT l → PolyT fun x => (c (p x) (l x)).ne
  gate : ∀ {α : Type} [Enc α] {p l i : α → ℕ}, PolyT p → PolyT l → PolyT i → PolyT fun x => (c (p x) (l x)).gate (i x)
  bit : ∀ {α : Type} [Enc α] {p l i : α → ℕ}, PolyT p → PolyT l → PolyT i → PolyT fun x => (c (p x) (l x)).bit (i x)

private theorem liftUniformD {c : ℕ → Code} (h : Uniform c) : Uniform2 (fun p _ => c (d p)) := by
  have hd {α : Type} [Enc α] {p : α → ℕ} (hp : PolyT p) : PolyT fun x => d (p x) := by
    unfold d S8H.ECPointArithmetic.width bitLen; fun_prop
  constructor
  · intro _ _ _ _ hp _; exact h.ng (hd hp)
  · intro _ _ _ _ hp _; exact h.nb (hd hp)
  · intro _ _ _ _ hp _; exact h.ne (hd hp)
  · intro _ _ _ _ _ hp _ hi; exact h.gate (hd hp) hi
  · intro _ _ _ _ _ hp _ hi; exact h.bit (hd hp) hi

private theorem sum_poly2 {a b : ℕ → ℕ → Code} (h : Uniform2 a) (k : Uniform2 b) : Uniform2 (fun p l => sum (a p l) (b p l)) := by
  constructor
  · intro _ _ p l hp hl; exact PolyT.add (h.ng hp hl) (k.ng hp hl)
  · intro _ _ p l hp hl; exact PolyT.add (h.nb hp hl) (k.nb hp hl)
  · intro _ _ p l hp hl; exact PolyT.add (h.ne hp hl) (k.ne hp hl)
  · intro _ _ p l i hp hl hi
    exact PolyT.ite' (PolyT.decide_lt hi (h.ne hp hl)) (h.gate hp hl hi)
      (PolyT.add (h.ng hp hl) (k.gate hp hl (PolyT.sub hi (h.ne hp hl))))
  · intro _ _ p l i hp hl hi
    exact PolyT.ite' (PolyT.decide_lt hi (h.ne hp hl)) (h.bit hp hl hi)
      (PolyT.add (h.nb hp hl) (k.bit hp hl (PolyT.sub hi (h.ne hp hl))))

private theorem rowL_poly2 : Uniform2 (fun _ l => rowsCode l 1) := by
  constructor
  · intro _ _ _ l _ hl; simpa [rowsCode] using hl
  · intro _ _ _ l _ hl; simpa [rowsCode] using hl
  · intro _ _ _ l _ hl; simpa [rowsCode] using hl
  · intro _ _ _ _ i _ _ hi; simpa [rowsCode] using hi
  · intro _ _ _ _ i _ _ hi; simpa [rowsCode] using hi

private theorem anchors_poly2 (n : ℕ → ℕ → ℕ)
    (hn : ∀ {α : Type} [Enc α] {p l : α → ℕ}, PolyT p → PolyT l → PolyT fun x => n (p x) (l x)) : Uniform2 (fun p l => AnchoredLayout.anchorCode (n p l)) := by
  constructor
  · intro _ _ _ _ hp hl; exact hn hp hl
  · intro _ _ _ _ hp hl; exact hn hp hl
  · intro _ _ _ _ hp hl; exact hn hp hl
  · intro _ _ _ _ _ _ _ hi; exact hi
  · intro _ _ _ _ _ _ _ hi; exact hi

private theorem elemWidth_poly : Uniform2 elemCode := by
  have ad := add_poly (fun k => k+1) (by intros; fun_prop)
  have bd := add_poly (fun k => 2*k) (by intros; fun_prop)
  have md := sum_poly mul_poly (rows_poly (fun k => 4*k) 2 (by intros; fun_prop))
  have rd := sum_poly (sum_poly ad ad) (copies_poly (sum_poly ad ad) 6)
  have hd := sum_poly (sum_poly md md) (sum_poly bd (sum_poly ad ad))
  have r := liftUniformD rd
  have h := liftUniformD hd
  have rowD5 := liftUniformD (rows_poly id 5 (by intros; assumption))
  have rowD3 := liftUniformD (rows_poly id 3 (by intros; assumption))
  have rowL := rowL_poly2
  have q := sum_poly2 (sum_poly2 r (sum_poly2 (liftUniformD (copies_poly hd 5)) rowD5))
    (sum_poly2 h (sum_poly2 rowD3 (sum_poly2 (liftUniformD (rows_poly (fun _ => 1) 1 (by intros; fun_prop)))
      (sum_poly2 (liftUniformD ad) rowL))))
  have hAnc {α : Type} [Enc α] {p l : α → ℕ} (hp : PolyT p) (_ : PolyT l) : PolyT fun x => regs (d (p x))+4*d (p x)+2 := by
    have hdp : PolyT fun x => d (p x) := by unfold d S8H.ECPointArithmetic.width bitLen; fun_prop
    fun_prop
  exact sum_poly2 (anchors_poly2 (fun p _ => regs (d p)+4*d p+2) hAnc)
    (sum_poly2 (anchors_poly2 (fun _ _ => 1) (by intros; fun_prop)) q)

theorem uniform : Uniform2 elemCode := elemWidth_poly

end DetDLP.S8H4.BaseCode


