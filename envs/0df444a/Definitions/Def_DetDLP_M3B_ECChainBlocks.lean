-- Prove2me | Definitions.Def_DetDLP_M3B_ECChainBlocks
-- name    : DetDLP_M3B_ECChainBlocks
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T20:09:32.334037+00:00
-- url     : https://prove2.me/theorems/195c3850-6850-4057-8e5b-1053da125f4e
-- title:
--   Physical elliptic-curve map and addition fold
-- statement:
--   Named map and addition rows for a running short-Weierstrass sum, with a full terminal register copy, row characterization, and explicit edge bound.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_M3B_ECAddRows

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace DetDLP.M3B.ECChainBlocks
open S8H0 RegisterMap NamedBlocks GateRoutes HashRows ECMapRows S8H.ECPointArithmetic

variable {p n d e k : ℕ} {s : Shape}

def emptyB : B k := ⟨S8J.CircuitRealizes.empty,Fin.elim0⟩
theorem emptyB_iff (x : Fin k → Bool) : emptyB.OK x ↔ True := ⟨fun _ => trivial,fun _ i => i.elim0⟩
def manyB : (n : ℕ) → (Fin n → B k) → B k
  | 0, _ => emptyB
  | n+1,f => joinB (f 0) (manyB n (fun i => f i.succ))
theorem manyB_iff (f : Fin n → B k) (x : Fin k → Bool) : (manyB n f).OK x ↔ ∀ i, (f i).OK x := by
  induction n with
  | zero => exact ⟨fun _ i => i.elim0, fun _ => (emptyB_iff x).2 trivial⟩
  | succ n ih => rw [manyB,joinB_iff,ih,Fin.forall_fin_succ]
theorem manyB_edges (f : Fin n → B k) (C : ℕ) (h : ∀ i, (f i).core.A.ne ≤ C) :
    (manyB n f).core.A.ne ≤ n*C := by
  induction n with
  | zero => rw [Nat.zero_mul]; exact Nat.le_refl 0
  | succ n ih =>
    change (f 0).core.A.ne + (manyB n (fun i => f i.succ)).core.A.ne ≤ _
    rw [Nat.succ_mul]; exact (Nat.add_le_add (h 0) (ih _ (fun i => h i.succ))).trans_eq (Nat.add_comm ..)

abbrev PointCell (d : ℕ) := Shape.pair .bit (.pair (triple d) (triple d))
abbrev Cells (d e n : ℕ) := Shape.pair (.vec (n+1) (mapShape d e)) (.vec n (ECAddRows.addShape d e))
abbrev Wires (s : Shape) := Ref s × Word s × Word s
def pointWires (f : Path (PointCell d) s) : Wires s :=
  (.reg (fstP f .bit),rwrd (fstP (sndP f)),rwrd (sndP (sndP f)))
def publicPoint [Fact p.Prime] (q : S8K.ECAddArithmetic.Coords p) : Wires s := (.pin q.1,pub q.2.1.val,pub q.2.2.val)

def mapPath (f : Path (Cells d e n) s) (i : Fin (n+1)) : Path (mapShape d e) s := fun a => f (.fst (.vec i a))
def addPath (f : Path (Cells d e n) s) (i : Fin n) : Path (ECAddRows.addShape d e) s := fun a => f (.snd (.vec i a))
/-- Accumulator zero is map zero; accumulator i+1 is addition i. -/
def acc (f : Path (Cells d e n) s) : Fin (n+1) → Path (PointCell d) s :=
  Fin.cases (fstP (mapPath f 0)) (fun i => fstP (addPath f i))

def wordEqB {w : ℕ} (f g : Path (.word w) s) := eqs w (refw f) (refw g)
def tripleEq (f g : Path (triple d) s) := joinB (wordEqB (fstP f) (fstP g))
  (joinB (wordEqB (fstP (sndP f)) (fstP (sndP g))) (wordEqB (sndP (sndP f)) (sndP (sndP g))))
/-- Copy the range-certificate bits too: no terminal witness bits are left free. -/
def pointEq (f g : Path (PointCell d) s) := joinB (eqs 1 (fun _ => .reg (fstP f .bit)) (fun _ => .reg (fstP g .bit)))
  (joinB (tripleEq (fstP (sndP f)) (fstP (sndP g))) (tripleEq (sndP (sndP f)) (sndP (sndP g))))
theorem pointEq_edges (f g : Path (PointCell d) s) : (pointEq f g).core.A.ne = 12*d+6 := by
  simp only [pointEq,tripleEq,wordEqB,joinB,eqs,rows,mapped,S8J.join]; omega

variable [Fact p.Prime] (E : WeierstrassCurve (ZMod p))
abbrev Chain (p n : ℕ) := Cells (width p) (GateSemantics.e p) n
variable (f : Path (Chain p n) s) (input : Fin (n+1) → Wires s) (term : Path (PointCell (width p)) s)
noncomputable def mapAt (i : Fin (n+1)) := let q := input i
  mapBlock (GateSemantics.hd p) p E.b₂.val E.a₁.val E.a₃.val q.1 q.2.1 q.2.2 (mapPath f i)
noncomputable def addAt (i : Fin n) :=
  let a := pointWires (acc f i.castSucc); let b := pointWires (fstP (mapPath f i.succ))
  ECAddRows.addBlock (GateSemantics.hd p) p (-1 : ZMod p).val (1 : ZMod p).val (3 : ZMod p).val
    (-27*E.c₄).val a.1 b.1 a.2.1 a.2.2 b.2.1 b.2.2 (addPath f i)
noncomputable def chainBlock := joinB (manyB (n+1) (mapAt E f input))
  (joinB (manyB n (addAt E f)) (pointEq (acc f (Fin.last n)) term))
theorem chainBlock_iff (x : Fin (s.size+1) → Bool) : (chainBlock E f input term).OK x ↔
    (∀ i, (mapAt E f input i).OK x) ∧ (∀ i, (addAt E f i).OK x) ∧ (pointEq (acc f (Fin.last n)) term).OK x := by
  simp only [chainBlock,joinB_iff,manyB_iff]
def edgeBound (d e n : ℕ) := (n+1)*(16*e+400*(d+2)) + (n*(60*e+1600*(d+2)) + (12*d+6))
theorem chainBlock_edges : (chainBlock E f input term).core.A.ne ≤ edgeBound (width p) (GateSemantics.e p) n := by
  apply Nat.add_le_add (manyB_edges _ _ (fun i => mapBlock_edges ..))
  exact Nat.add_le_add (manyB_edges _ _ (fun i => ECAddRows.addBlock_edges ..)) (pointEq_edges ..).le

end DetDLP.M3B.ECChainBlocks


