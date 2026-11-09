-- Prove2me | Definitions.Def_IQPForrelation832_SingleQuery_Circuits
-- name    : IQPForrelation832_SingleQuery_Circuits
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T03:05:26.612006+00:00
-- url     : https://prove2.me/theorems/ad21e226-a771-4d33-864d-70eb0158bfe5
-- title:
--   Joint phase oracle, IQP middle blocks and Born acceptance
-- statement:
--   For arbitrary real sign functions $f,g:V_n\to\{-1,1\}$, define the joint oracle by
--   $$
--   O_{f,g}|b,x\rangle=\begin{cases}f(x)|b,x\rangle&b=0,\\g(x)|b,x\rangle&b=1.\end{cases}
--   $$
--   An IQP middle block is a finite list of actual embedded diagonal unitary gates and plain oracle calls. The full circuit applies a tensor Hadamard layer, that list, and a second tensor Hadamard layer to the all-zero state. For an accepting predicate $F$, its acceptance probability is
--   $$
--   P_{\rm acc}(C,F;f,g)=\sum_{z\in F}|\langle z|H^{\otimes m}D^{f,g}H^{\otimes m}|0^m\rangle|^2.
--   $$
--   The list semantics, wire embeddings, Hadamards, initial state and Born sums are reused from the published circuit substrate. The IQP predicate separately requires diagonal gates to be unitary. Polynomial supplied implementations have absolute polynomial length and an absolute locality bound, without a generator requirement. Exact efficient computation of a sign-valued Fourier transform means one polynomial-time finite string transducer returning its sign bit for every dimension and address.
--
--   These objects give Proposition 1 an operational meaning independent of its desired acceptance identity. The accepting input is a fixed self-delimiting encoding of dimension, branch and measured output; it contains no truth tables.
-- source:
--   Quentin Buzet, André Chailloux, IQP circuits for 2-Forrelation, STOC 2027 submission #832 (October 2026), pp. 2, 3–4, 13 (Definitions 3–4), 14–15 (Proposition 1 and its proof). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/832.pdf

import Definitions.Def_IQPForrelation832_SingleQuery_Analysis
import Definitions.Def_QAlgorithms_ClassicalStringComputability

set_option autoImplicit false

namespace IQPForrelation832.SingleQuery

open QAlgorithms QAlgorithms.Complexity

abbrev Middle (n m : ℕ) := OracleCircuit Set.univ (fun _ : Fin 1 => n+1) m

/-- The joint phase oracle; it is one black-box gate. -/
noncomputable def jointOracle {n : ℕ} (f g : Cube n → ℝ) :
    Matrix (Qubits (n+1)) (Qubits (n+1)) ℂ :=
  Matrix.diagonal (fun z => ((if z 0 then g else f) (cubeEquiv n (Fin.tail z)) : ℂ))

def DiagonalUnitary (g : Gate) : Prop :=
  g.IsUnitary ∧ ∀ x y, x ≠ y → g.mat x y = 0

/-- An IQP middle block can contain arbitrary diagonal unitaries and plain phase queries.
No acceptance identity or efficiency assertion is part of this predicate. -/
def IsIQP {n m : ℕ} (c : Middle n m) : Prop :=
  ∀ s ∈ c, match s with
    | .gate g => DiagonalUnitary g.gate
    | .query _ adj control _ _ => adj = false ∧ control = none

noncomputable def run {n m : ℕ} (c : Middle n m) (f g : Cube n → ℝ) :
    EuclideanSpace ℂ (Qubits m) :=
  act (hadamardN m * OracleCircuit.unitary c (fun _ => jointOracle f g) * hadamardN m)
    (zeroKet m)

/-- Born probability, summed over accepted outcomes without postselection. -/
noncomputable def born {n m : ℕ} (c : Middle n m) (F : Qubits m → Prop)
    (f g : Cube n → ℝ) : ℝ := by
  classical
  exact probEvent (run c f g) F

/-- A fixed encoding, with a unary dimension, a branch, and a counted output string. -/
def decisionInput {m : ℕ} (n : ℕ) (b : Bool) (z : Qubits m) : Str :=
  encNat n ++ [b] ++ encNat m ++ List.ofFn z

def accepts {m : ℕ} (a : Str → Str) (n : ℕ) (b : Bool) (z : Qubits m) : Prop :=
  a (decisionInput n b z) = [true]

/-- Supplied implementations are retained, with one oracle query before their gates. -/
def withQuery {n : ℕ} (c : Circuit Set.univ (n+1)) : Middle n (n+1) :=
  .query 0 false none (Function.Embedding.refl _) (by simp) :: c.map OracleStep.gate

noncomputable def phaseDiagonal {n : ℕ} (r0 r1 : Cube n → ℝ) :
    Matrix (Qubits (n+1)) (Qubits (n+1)) ℂ :=
  Matrix.diagonal (fun z => ((if z 0 then r1 else r0) (cubeEquiv n (Fin.tail z)) : ℂ))

/-- Standard bounded-locality gate cost. k is absolute; no generator is required of supplied
implementations. In particular the library is not restricted to Z/CZ gates. -/
def PolynomialImplementation (c : ∀ n, Circuit Set.univ (n+1)) : Prop :=
  ∃ C d k : ℕ, ∀ n,
    (c n).length ≤ C * (n+1)^d ∧
    ∀ g ∈ c n, g.gate.arity ≤ k ∧ DiagonalUnitary g.gate

/-- Efficient exact computation of a sign-valued transform, as one bit. -/
def ComputableTransform (s : ∀ n, Cube n → ℝ) : Prop :=
  ∃ t : Str → Str, PolyTimeComputable t ∧
    ∀ n x, t (encNat n ++ cubeBits x) =
      (if realFourier (s n) x = 1 then [true] else [false])

end IQPForrelation832.SingleQuery


