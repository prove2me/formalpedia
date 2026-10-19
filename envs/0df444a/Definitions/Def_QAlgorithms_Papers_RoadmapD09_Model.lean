-- Prove2me | Definitions.Def_QAlgorithms_Papers_RoadmapD09_Model
-- name    : QAlgorithms_Papers_RoadmapD09_Model
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:33:46.25241+00:00
-- url     : https://prove2.me/theorems/52021bf5-befe-4b31-9061-e45ebf4e1993
-- title:
--   Worst-Case Quantum Algorithm for Optimal Polynomial Intersection Beyond Decoded Quantum Interferometry: supporting definitions
-- statement:
--   Supporting mathematical objects and conventions for the selected original paper results. Exact source hypotheses and labels are documented in the Lean declarations.
-- source:
--   Worst-Case Quantum Algorithm for Optimal Polynomial Intersection Beyond Decoded Quantum Interferometry, arXiv:2607.14650v1, https://arxiv.org/abs/2607.14650v1. Exact locators in declaration docstrings.

import Definitions.Def_QAlgorithms_Defs_BalancedOPIRegimes
import Definitions.Def_QAlgorithms_Defs_FiniteRegisters
noncomputable section

attribute [local instance] Classical.propDecidable

open scoped Matrix

namespace QAlgorithms.Papers.RoadmapD09

open QAlgorithms OPI

/-- Public inputs for Theorem 1.1, arXiv:2607.14650v1, PDF pp.3–5.
The family index is bookkeeping; the serialized input contains field data, n, k,
evaluation points and an integer satisfaction target, and contains no hidden subsets. -/
structure PublicInput (F : ℕ → Type) (n : ℕ → ℕ) where
  index : ℕ
  alpha : Fin (n index) → F index
  target : ℕ

/-- The public binary input of Problem 1 (PDF p.3), using the finite-field convention
of §2.1 (PDF p.16). The index itself is not an input to the constructor. -/
def publicEncoding {F : ℕ → Type} [∀ j, Field (F j)] [∀ j, Fintype (F j)]
    {n : ℕ → ℕ} (k : ℕ → ℕ) (E : (j : ℕ) → publicFieldEncoding (F j))
    (Q : PublicInput F n) : Complexity.Str :=
  publicInputEncoding (E Q.index) (n Q.index) (k Q.index) Q.target Q.alpha

/-- Size parameters of the public input; q-sized membership tables are absent
(Problem 1, PDF p.3, footnote 1). -/
def publicScale {F : ℕ → Type} [∀ j, Field (F j)] [∀ j, Fintype (F j)]
    {n : ℕ → ℕ} (E : (j : ℕ) → publicFieldEncoding (F j)) (Q : PublicInput F n) : ℕ :=
  n Q.index + (E Q.index).e * Nat.clog 2 (E Q.index).p + 1

/-- Binary embedding of a field element and a membership-answer bit. Each coordinate
has its own XOR membership oracle, as in Problem 1, PDF p.3. -/
def membershipEmbedding {F : Type} [Field F] [Fintype F] (E : publicFieldEncoding F) :
    Matrix (Qubits (E.e * Nat.clog 2 E.p + 1)) (F × Bool) ℂ :=
  Matrix.of fun z ab => if z =
    Fin.snoc (fun i : Fin (E.e * Nat.clog 2 E.p) => (fieldBits E ab.1).getD i.val false) ab.2
    then 1 else 0

/-- A fixed uniform solver with one uncontrolled membership oracle per subset.
Quantum and classical operations use the frozen standard circuit/program model;
the output consists of k field coefficients. Source: PDF pp.3, 17, 29–30, 38–39. -/
structure UniformSolver (F : ℕ → Type) [∀ j, Field (F j)] [∀ j, Fintype (F j)]
    (n k : ℕ → ℕ) (E : (j : ℕ) → publicFieldEncoding (F j)) where
  family : UniformResourceFamily (PublicInput F n) (publicEncoding k E) (publicScale E)
  oracleCount : ∀ Q, (family.construct Q).oracles = n Q.index
  oracleArity : ∀ Q i, (family.construct Q).arity i =
    (E Q.index).e * Nat.clog 2 (E Q.index).p + 1
  uncontrolled : ∀ Q i, (family.construct Q).control i = false
  outputSize : ∀ Q, (family.construct Q).outputBits =
    k Q.index * ((E Q.index).e * Nat.clog 2 (E Q.index).p)

/-- The hidden sets enter execution only through their XOR membership oracles;
on unused binary encodings the oracle is the identity (Problem 1, PDF p.3). -/
def solverOracles {F : ℕ → Type} [∀ j, Field (F j)] [∀ j, Fintype (F j)]
    [∀ j, DecidableEq (F j)] {n k : ℕ → ℕ} {E : (j : ℕ) → publicFieldEncoding (F j)}
    (A : UniformSolver F n k E) (Q : PublicInput F n)
    (sets : Fin (n Q.index) → Finset (F Q.index)) :
    (i : Fin (A.family.construct Q).oracles) →
      Matrix (Qubits ((A.family.construct Q).arity i))
        (Qubits ((A.family.construct Q).arity i)) ℂ :=
  fun i =>
    (extendEncodedUnitary (membershipEmbedding (E Q.index))
      (xorOracle fun a : F Q.index => decide (a ∈ sets (Fin.cast (A.oracleCount Q) i)))).submatrix
      (fun z => z ∘ Fin.cast (A.oracleArity Q i).symm)
      (fun z => z ∘ Fin.cast (A.oracleArity Q i).symm)

/-- Successful polynomial output, with degree strictly below k and at least the
public integer target satisfied. A failure leaf never counts. Source: Problem 1,
PDF p.3; the inverse-polynomial success of Corollary 5.2, PDF pp.29–30, is amplified. -/
def solverSuccess {F : ℕ → Type} [∀ j, Field (F j)] [∀ j, Fintype (F j)]
    [∀ j, DecidableEq (F j)] {n k : ℕ → ℕ} {E : (j : ℕ) → publicFieldEncoding (F j)}
    (A : UniformSolver F n k E) (Q : PublicInput F n)
    (sets : Fin (n Q.index) → Finset (F Q.index)) : ℝ :=
  membershipOutputLaw (A.family.construct Q).program (solverOracles A Q sets)
    (fun result => match result with
      | none => False
      | some bits =>
          IsSolution (k Q.index) Q.target Q.alpha sets
            (coefficientPolynomial (coefficientOutput (E Q.index) (k Q.index) (List.ofFn bits))))

/-- All executable resources, including queries, Clifford+T gates, classical control,
measurements, preparations, workspace and coefficient decoding. Source: PDF pp.3,
17, 19, 36–39. The bound includes density estimation and success amplification. -/
def solverWork {F : ℕ → Type} [∀ j, Field (F j)] [∀ j, Fintype (F j)]
    [∀ j, DecidableEq (F j)] {n k : ℕ → ℕ} {E : (j : ℕ) → publicFieldEncoding (F j)}
    (A : UniformSolver F n k E) (Q : PublicInput F n)
    (sets : Fin (n Q.index) → Finset (F Q.index)) : ℕ :=
  membershipResources (A.family.construct Q).program (solverOracles A Q sets) +
    k Q.index * ((E Q.index).e * Nat.clog 2 (E Q.index).p + 1) ^ 2


end QAlgorithms.Papers.RoadmapD09


