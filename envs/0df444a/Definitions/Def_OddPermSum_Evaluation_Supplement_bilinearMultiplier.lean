-- Prove2me | Definitions.Def_OddPermSum_Evaluation_Supplement_bilinearMultiplier
-- name    : OddPermSum_Evaluation_Supplement_bilinearMultiplier
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:36:32.878517+00:00
-- url     : https://prove2.me/theorems/8db8e4fc-87ec-4bb9-bb08-f27110b79833
-- title:
--   Uniform prime-field bilinear matrix multiplication
-- statement:
--   A bilinear multiplication circuit first computes $\mathbb F_2$-linear forms separately in the entries of two matrices, multiplies selected pairs of these forms, then combines the products by another $\mathbb F_2$-linear circuit. Formal correctness is equality with matrix multiplication in the polynomial ring of independent input entries over $\mathbb F_2$, rather than equality only as functions on a finite field. Circuit cost counts all linear gates and pair products.
--
--   An exponent $2<\omega\le3$ is uniformly bilinear admissible if one deterministic finite bit-RAM program, without advice, generates such circuits at every size $s\ge1$, their costs are at most $C_Ms^\omega$, and construction takes at most $C_Ms^\omega(\log_2(s+1)+1)^k$ steps. Constants and the generator precede $s$.
--
--   This implements the brief's field-uniform reading of admissibility in §§5–6: fixed prime-field coefficients lift to every characteristic-two algebra, while circuit generation is charged in time bounds. It supplies no multiplication primitive.
-- source:
--   Boxuan Chen, Bin Cui, Hanqing Li, Xupeng Miao, Haoze Wang, STOC 2027 submission #716 (October 2026), p. 5, linear algebra; 14, proof of Lemma 5.3

import Definitions.Def_OddPermSum_Evaluation_Supplement_bitModel
import Definitions.Def_OddPermSum_Evaluation_matrixEncoding

set_option autoImplicit false

namespace OddPermSum.Evaluation.Supplement

/-- F₂-linear straight-line circuits: addition, zero, input only. -/
inductive LinearGate where
  | zero
  | input (i : ℕ)
  | add (i j : ℕ)

def LinearGate.eval {R : Type*} [AddMonoid R] (input regs : List R) : LinearGate → R
  | .zero => 0
  | .input i => input.getD i 0
  | .add i j => regs.getD i 0 + regs.getD j 0

def linearEval {R : Type*} [AddMonoid R] (input : List R) (gates : List LinearGate) : List R :=
  gates.foldl (fun regs g => regs ++ [g.eval input regs]) []

def LinearGate.encode : LinearGate → List ℕ
  | .zero => [0]
  | .input i => [1,i]
  | .add i j => [2,i,j]

/-- Two F₂-linear input circuits, paired products, and an F₂-linear output circuit. -/
structure BilinearCircuit where
  left : List LinearGate
  right : List LinearGate
  products : List (ℕ × ℕ)
  combine : List LinearGate
  outputs : List ℕ

def BilinearCircuit.cost (c : BilinearCircuit) : ℕ :=
  c.left.length + c.right.length + c.products.length + c.combine.length

def BilinearCircuit.encode (c : BilinearCircuit) : List Bool :=
  encodeNats (c.left.length :: c.left.flatMap LinearGate.encode) ++
  encodeNats (c.right.length :: c.right.flatMap LinearGate.encode) ++
  encodeNats (c.products.flatMap (fun ij => [ij.1,ij.2])) ++
  encodeNats (c.combine.length :: c.combine.flatMap LinearGate.encode) ++ encodeNats c.outputs

def BilinearCircuit.eval {R : Type*} [CommRing R] (c : BilinearCircuit) (a b : List R) : List R :=
  let l := linearEval a c.left
  let r := linearEval b c.right
  let p := c.products.map fun ij => l.getD ij.1 0 * r.getD ij.2 0
  let o := linearEval p c.combine
  c.outputs.map fun i => o.getD i 0

/-- Formal multiplication identity in independent matrix-entry indeterminates. -/
noncomputable def BilinearCircuit.Multiplies (s : ℕ) (c : BilinearCircuit) : Prop :=
  let A : Matrix (Fin s) (Fin s) (MvPolynomial (Bool × Fin s × Fin s) (ZMod 2)) :=
    fun i j => MvPolynomial.X (false,i,j)
  let B : Matrix (Fin s) (Fin s) (MvPolynomial (Bool × Fin s × Fin s) (ZMod 2)) :=
    fun i j => MvPolynomial.X (true,i,j)
  c.eval (matrixEncoding A) (matrixEncoding B) = matrixEncoding (A * B)

/-- Uniform, prime-field bilinear admissibility. Circuit construction is effective and charged,
not an arbitrary nonuniform family or a multiplication oracle. The generator has no advice. -/
noncomputable def UniformBilinearExponent (ω : ℝ) : Prop :=
  2 < ω ∧ ω ≤ 3 ∧ ∃ (gen : BitProgram) (C : ℝ) (k : ℕ), 0 < C ∧
    MaoLowDegree.Counterexample.HasNoCoins gen ∧
    ∀ s : ℕ, 1 ≤ s → ∃ (c : BilinearCircuit) (t : ℕ),
      c.Multiplies s ∧ (c.cost : ℝ) ≤ C * (s : ℝ)^ω ∧
      (t : ℝ) ≤ C * (s : ℝ)^ω * logFactor s k ∧
      let st := runBits gen s (encodeNats [s]) [] (fun _ => false) t
      st.halted = true ∧ st.output = c.encode

end OddPermSum.Evaluation.Supplement


