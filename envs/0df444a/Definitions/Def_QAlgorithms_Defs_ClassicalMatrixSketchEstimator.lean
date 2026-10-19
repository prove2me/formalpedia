-- Prove2me | Definitions.Def_QAlgorithms_Defs_ClassicalMatrixSketchEstimator
-- name    : QAlgorithms_Defs_ClassicalMatrixSketchEstimator
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:21:06.964977+00:00
-- url     : https://prove2.me/theorems/12db7145-b91f-44c7-a229-57343d6f6ad0
-- title:
--   ClassicalMatrixSketchEstimator
-- statement:
--   ClassicalMatrixSketchEstimator
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\ClassicalMatrixSketchEstimator.lean

import Definitions.Def_QAlgorithms_Defs_ApproximateMatrixCircuitFamilies
import Definitions.Def_QAlgorithms_Defs_MultipleMatrixSketches
import Definitions.Def_QAlgorithms_Defs_SamplingUtilities
import Definitions.Def_QAlgorithms_Defs_ApproximateMatrixMultiplicationContracts
noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.MatrixApprox

variable {n k c : ℕ}

/-- Mathematical law of the independent multirow sign sketch. This is not a charged circuit implementation. Source: arxiv-2510.08509v1 PDF pp.19–23. -/
def classicalSketchLaw (A : Fin (k+1) → Matrix (Fin n) (Fin n) ℝ)
    (hc : 0 < c) : PMF (Matrix (Fin n) (Fin n) ℝ) :=
  (PMF.uniformOfFintype (Fin k → Fin c → Fin n → Bool)).map (MatrixSketch.matrixProduct A hc)

/-- Select the estimate whose median squared Frobenius distance to the other estimates is
smallest, with fixed tie ordering. If a majority are within e of the target, this selection
is within 3e; use e=eps/3 in confidence amplification. This is a selector, not the complete
sample-size/confidence wrapper. Source: arxiv-2510.08509v1 PDF pp.22–23. -/
def frobeniusAmplification (t : ℕ) (_ht : 0 < t)
    (estimates : Fin t → Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  let distanceMedian := fun i : Fin t =>
    realMedian (List.ofFn fun j => ∑ a : Fin n, ∑ b : Fin n, (estimates i a b-estimates j a b)^2)
  let selected := (List.finRange t).mergeSort fun i j => decide (distanceMedian i ≤ distanceMedian j)
  estimates ((selected.head?).getD ⟨0,_ht⟩)


/-- Expand a supplied multiplication circuit into the parent circuit's fixed memory addresses.
Initialize the embedded scratch registers to zero before each invocation; the supplied multiplication contract is stated from zero memory. Every reset, read, arithmetic operation and output copy is retained and charged.
Source: arxiv-2510.08509v1 PDF pp.13–14,22–23. -/
def multiplyInstructions {input registers rows inner cols work : ℕ}
    (C : ExactArithmetic.ClassicalCircuit (rows*inner+inner*cols) work (rows*cols))
    (embed : Fin work ↪ Fin registers) (left : Fin rows → Fin inner → Fin registers)
    (right : Fin inner → Fin cols → Fin registers) (out : Fin rows → Fin cols → Fin registers) :
    List (ExactArithmetic.ClassicalInstruction input registers) :=
  let lookup : Fin (rows*inner+inner*cols) → Fin registers := Fin.addCases
    (fun i => left (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2)
    (fun i => right (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2)
  (List.finRange work).map (fun i =>
    ExactArithmetic.ClassicalInstruction.constant (input := input) (embed i) 0) ++
  C.instructions.map (fun op => match op with
    | .constant dst v => .constant (embed dst) v
    | .read dst src => .copy (embed dst) (lookup src)
    | .copy dst src => .copy (embed dst) (embed src)
    | .add dst a b => .add (embed dst) (embed a) (embed b)
    | .sub dst a b => .sub (embed dst) (embed a) (embed b)
    | .mul dst a b => .mul (embed dst) (embed a) (embed b)
    | .div dst a b => .div (embed dst) (embed a) (embed b)
    | .coin dst => .coin (embed dst)) ++
      (List.finRange (rows*cols)).map (fun i =>
        .copy (out (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2) (embed (C.output i)))

/-- The actual sign-sketch circuit: read the full matrix input, generate independent signs,
multiply in low-rank rectangular order, and divide by c^k. When n≤c use exact sequential multiplication instead. All multiplication routines are
expanded into their instructions, preserving the chosen achievable multiplication exponent.
For zero interfaces return the one input matrix by copies.
Source: arxiv-2510.08509v1 PDF pp.19–23. -/
def classicalSketchCircuit (n k c : ℕ) (_hc : 0 < c) (I : MultiplicationImplementation) := by
  classical
  let dims : Fin 6 → ℕ × (ℕ × ℕ) := ![(n,(n,c)),(c,(n,n)),(c,(n,c)),(n,(c,c)),(n,(c,n)),(n,(n,n))]
  let work := (Finset.univ : Finset (Fin 6)).sup fun t =>
    I.registers (dims t).1 (dims t).2.1 (dims t).2.2
  let Slot := (Fin (k+1) × (Fin n × Fin n)) ⊕
    ((Fin k × (Fin c × Fin n)) ⊕ ((Bool × (Fin n × Fin c)) ⊕
      ((Fin c × Fin n) ⊕ ((Fin c × Fin c) ⊕ ((Fin n × Fin n) ⊕ (Fin work ⊕ Unit))))))
  let r := Fintype.card Slot
  let address := Fintype.equivFin Slot
  let dataAddr := fun (t : Fin (k+1)) (i j : Fin n) => address (Sum.inl (t,(i,j)))
  let signAddr := fun (t : Fin k) (i : Fin c) (j : Fin n) => address (Sum.inr (Sum.inl (t,(i,j))))
  let vecAddr := fun (b : Bool) (i : Fin n) (j : Fin c) =>
    address (Sum.inr (Sum.inr (Sum.inl (b,(i,j)))))
  let rowAddr := fun (i : Fin c) (j : Fin n) =>
    address (Sum.inr (Sum.inr (Sum.inr (Sum.inl (i,j)))))
  let midAddr := fun (i j : Fin c) =>
    address (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (i,j))))))
  let outAddr := fun (i j : Fin n) =>
    address (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (i,j)))))))
  let denominator := address (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr ())))))))
  let scratchAddress : Fin work ↪ Fin r :=
    ⟨fun j => address (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl j))))))),
      by intro a b h; have he := address.injective h; exact Sum.inl.inj (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj he))))))⟩
  let scratch : (t : Fin 6) → Fin (I.registers (dims t).1 (dims t).2.1 (dims t).2.2) ↪ Fin r :=
    fun t => (Fin.castLEEmb (Finset.le_sup (Finset.mem_univ t))).trans scratchAddress
  let call := fun (t : Fin 6) => multiplyInstructions (input := (k+1)*(n*n))
    (I.circuit (dims t).1 (dims t).2.1 (dims t).2.2) (scratch t)
  let reads := (List.finRange (k+1)).flatMap fun t => (List.finRange n).flatMap fun i =>
    (List.finRange n).map fun j =>
      ExactArithmetic.ClassicalInstruction.read (dataAddr t i j) (finProdFinEquiv (t,finProdFinEquiv (i,j)))
  let coins := (List.finRange k).flatMap fun t => (List.finRange c).flatMap fun i =>
    (List.finRange n).map fun j => ExactArithmetic.ClassicalInstruction.coin (input := (k+1)*(n*n)) (signAddr t i j)
  let output := fun z : Fin (n*n) => outAddr (finProdFinEquiv.symm z).1 (finProdFinEquiv.symm z).2
  let copies := fun (source target : Fin n → Fin c → Fin r) =>
    (show List (ExactArithmetic.ClassicalInstruction ((k+1)*(n*n)) r) from
    (List.finRange n).flatMap fun i => (List.finRange c).map fun j =>
      ExactArithmetic.ClassicalInstruction.copy (target i j) (source i j))
  let ops := if hk : k = 0 then reads ++ (List.finRange (n*n)).map fun z =>
      ExactArithmetic.ClassicalInstruction.copy (output z)
        (dataAddr ⟨0,by omega⟩ (finProdFinEquiv.symm z).1 (finProdFinEquiv.symm z).2)
    else if hExact : n ≤ c then
      let buffer := fun i j : Fin n => vecAddr false i (Fin.castLE hExact j)
      reads ++
      ((List.finRange n).flatMap fun i => (List.finRange n).map fun j =>
        ExactArithmetic.ClassicalInstruction.copy (buffer i j) (dataAddr ⟨0,by omega⟩ i j)) ++
      ((List.finRange k).flatMap fun t =>
        call 5 buffer (dataAddr t.succ) outAddr ++
        ((List.finRange n).flatMap fun i => (List.finRange n).map fun j =>
          ExactArithmetic.ClassicalInstruction.copy (buffer i j) (outAddr i j)))
    else
      reads ++ coins ++ call 0 (dataAddr ⟨0,by omega⟩) (fun j i => signAddr ⟨0,by omega⟩ i j) (vecAddr false) ++
      ((List.finRange (k-1)).flatMap fun t =>
        let a : Fin k := ⟨t.val,by have := t.isLt; omega⟩
        let b : Fin k := ⟨t.val+1,by have := t.isLt; omega⟩
        call 1 (signAddr a) (dataAddr a.succ) rowAddr ++
        call 2 rowAddr (fun j i => signAddr b i j) midAddr ++
        call 3 (vecAddr false) midAddr (vecAddr true) ++ copies (vecAddr true) (vecAddr false)) ++
      call 1 (signAddr ⟨k-1,by omega⟩) (dataAddr (Fin.last k)) rowAddr ++
      call 4 (vecAddr false) rowAddr outAddr ++
      [ExactArithmetic.ClassicalInstruction.constant denominator ((c : ℝ)^k)] ++
      (List.finRange (n*n)).map fun z => ExactArithmetic.ClassicalInstruction.div (output z) (output z) denominator
  exact (⟨ops,output⟩ : ExactArithmetic.ClassicalCircuit ((k+1)*(n*n)) r (n*n))

example (A : Fin 1 → Matrix (Fin n) (Fin n) ℝ) (hc : 0 < c) :
    classicalSketchLaw A hc = PMF.pure (A 0) := by
  unfold classicalSketchLaw
  have h : MatrixSketch.matrixProduct A hc = fun _ => A 0 := by
    funext s
    simp [MatrixSketch.matrixProduct]
  rw [h]
  change (PMF.uniformOfFintype _).bind (fun _ => PMF.pure (A 0)) = PMF.pure (A 0)
  exact PMF.bind_const _ _

end QAlgorithms.MatrixApprox


