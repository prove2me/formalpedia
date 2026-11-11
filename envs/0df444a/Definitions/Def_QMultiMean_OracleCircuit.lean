-- Prove2me | Definitions.Def_QMultiMean_OracleCircuit
-- name    : QMultiMean_OracleCircuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T04:10:01.214918+00:00
-- url     : https://prove2.me/theorems/a94dfc17-ca50-4af1-a8e2-9899669cdb04
-- title:
--   Oracle circuits and quantum estimators in the binary-oracle model
-- statement:
--   The paper does not define its model of computation. The mission uses the standard query model. An **oracle circuit** with input register $\mathcal H_I$ consists of:
--
--   1. $r$ copies of the register pair $\mathcal H_\Omega\otimes\mathcal H_E$ and an ancilla $\mathbb C^{A+1}$;
--   2. a number $T$ of oracle calls, each of one kind ($U_P$, $U_P^{-1}$, $\mathcal B_X$ or $\mathcal B_X^{-1}$) and acting on one chosen copy;
--   3. unitary gates $G_0,\dots,G_T$ on the whole space.
--
--   With oracles $U_P,\mathcal B_X$ the circuit implements
--   $$W=G_T\,O_T\cdots G_1\,O_1\,G_0 ,$$
--   where $O_t$ is the $t$-th oracle call. A **quantum estimator** is an oracle circuit with no input register followed by a measurement of all registers in the computational basis and a classical map from the measured label to an output. Started in the all-zero state $|0\rangle|\vec0\rangle$, it outputs a point of a set $S$ with probability
--   $$\sum_{\ell:\ \mathrm{out}(\ell)\in S}\big|\langle\ell|W|0\rangle|\vec 0\rangle\big|^2 .$$
--   The number of quantum experiments and binary oracle queries an estimator uses is $T$.
--
--   This is the model in which the theorems of the mission state that an estimator "uses $\tilde O(n)$ quantum experiments and binary oracle queries".
--
--   **Formalization Note** The gates and the output map are fields of the structure. They do not mention $P$, $X$ or the oracles, which enter only when the circuit is run. A theorem chooses the circuit from its parameters, $N$ and $E$, before the instance. Gates are arbitrary unitaries: no gate count is claimed. Controlled oracle calls are not provided, and intermediate measurements and classical control are absorbed by deferred measurement into fresh registers. The module also defines the Euclidean norm of a complex vector.
-- source:
--   Cornelissen, Hamoudi, Jerbi, Near-Optimal Quantum Algorithms for Multivariate Mean Estimation, arXiv:2111.09787v2, §2.2, p.7 (Definitions 2.4–2.6); model read from §3, pp.9–13

import Mathlib
import Definitions.Def_QMultiMean_IsBinaryOracle

set_option autoImplicit false

namespace QMultiMean

/-- The four kinds of oracle call of the binary-oracle model (Cornelissen, Hamoudi, Jerbi,
arXiv:2111.09787v2, §2.2, Definitions 2.5–2.6, p.7): a quantum experiment `U_P` or `U_P⁻¹`, and a
binary oracle query `B_X` or `B_X⁻¹`. -/
inductive CallKind where
  | U
  | Uinv
  | B
  | Binv
  deriving DecidableEq

/-- The workspace register of a circuit, apart from its input register: `r` copies of the pair
`H_Ω ⊗ H_E` (each a sample register and a value register) and an ancilla `ℂ^{A+1}`. -/
abbrev AuxLabel (N : ℕ) {V : Type} (E : Finset V) (r A : ℕ) : Type :=
  (Fin r → Fin (N + 1) × E) × Fin (A + 1)

/-- The computational-basis labels of a circuit with input register `I`. -/
abbrev Label (I : Type) (N : ℕ) {V : Type} (E : Finset V) (r A : ℕ) : Type :=
  I × AuxLabel N E r A

/-- The all-zero workspace label `|0⃗⟩`: every sample register at `0 ∈ Ω`, every value register at
`0⃗ ∈ E`, the ancilla at `0`. -/
def initAux {N : ℕ} {V : Type} [Zero V] {E : Finset V} (h0 : (0 : V) ∈ E) (r A : ℕ) :
    AuxLabel N E r A :=
  (fun _ => (0, ⟨0, h0⟩), 0)

open Classical in
/-- An **oracle circuit** in the binary-oracle model of arXiv:2111.09787v2, §2.2 (Definitions 2.5,
2.6, p.7), with input register `I`, for samples in `Ω = Fin (N+1)` and values in the finite set `E`.
It consists of `r` copies of the register pair `H_Ω ⊗ H_E`, an ancilla of dimension `A + 1`, a
number `T` of oracle calls, unitary gates `G₀, …, G_T` on the whole space, and for each call `t < T`
its kind (`U_P`, `U_P⁻¹`, `B_X`, `B_X⁻¹`) and the copy it acts on.

**Formalization Note.** The fields do not mention the probability mass function, the random
variable or the oracles: gates may depend only on what the structure is built from (in the theorems:
`d`, the parameters, `N` and `E`). Free gates are arbitrary unitaries (the query model; no gate count
is claimed). `T` counts every application of `U_P`, `U_P⁻¹`, `B_X`, `B_X⁻¹`; no controlled oracle
calls are provided. Adaptive classical control and intermediate measurements are absorbed by
deferred measurement into fresh registers. -/
structure OracleCircuit (I : Type) [Fintype I] (N : ℕ) {V : Type} (E : Finset V) where
  /-- Number of copies of the register pair `H_Ω ⊗ H_E`. -/
  r : ℕ
  /-- The ancilla is `ℂ^{A+1}`. -/
  A : ℕ
  /-- Number of oracle calls. -/
  T : ℕ
  /-- The gates `G₀, …, G_T`. -/
  gate : Fin (T + 1) → Matrix (Label I N E r A) (Label I N E r A) ℂ
  /-- Every gate is unitary. -/
  gate_unitary : ∀ t, gate t ∈ Matrix.unitaryGroup (Label I N E r A) ℂ
  /-- The kind of the `t`-th oracle call. -/
  kind : Fin T → CallKind
  /-- The copy of `H_Ω ⊗ H_E` the `t`-th oracle call acts on. -/
  copy : Fin T → Fin r

open Classical in
/-- A matrix `M` on one register pair `H_Ω ⊗ H_E`, acting on copy `i` of a circuit's space and as the
identity on the input register, the other copies and the ancilla. -/
noncomputable def onCopy {I : Type} {N : ℕ} {V : Type} {E : Finset V} {r A : ℕ} (i : Fin r)
    (M : Matrix (Fin (N + 1) × E) (Fin (N + 1) × E) ℂ) :
    Matrix (Label I N E r A) (Label I N E r A) ℂ :=
  fun p q =>
    if p.1 = q.1 ∧ p.2.2 = q.2.2 ∧ (∀ j, j ≠ i → p.2.1 j = q.2.1 j) then M (p.2.1 i) (q.2.1 i)
    else 0

open Classical in
/-- A matrix on `H_Ω`, acting on the sample register of a pair `H_Ω ⊗ H_E` (identity on `H_E`). -/
noncomputable def onSample {N : ℕ} {V : Type} {E : Finset V}
    (U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) : Matrix (Fin (N + 1) × E) (Fin (N + 1) × E) ℂ :=
  fun p q => if p.2 = q.2 then U p.1 q.1 else 0

/-- The matrix of the `t`-th oracle call of a circuit, given the oracles `U` (on `H_Ω`) and `B` (on
`H_Ω ⊗ H_E`): `U_P`, `U_P⁻¹ = U_P†`, `B_X` or `B_X⁻¹ = B_X†` on the chosen copy. -/
noncomputable def OracleCircuit.call {I : Type} [Fintype I] {N : ℕ} {V : Type} {E : Finset V}
    (C : OracleCircuit I N E) (U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (B : Matrix (Fin (N + 1) × E) (Fin (N + 1) × E) ℂ) (t : Fin C.T) :
    Matrix (Label I N E C.r C.A) (Label I N E C.r C.A) ℂ :=
  match C.kind t with
  | .U => onCopy (C.copy t) (onSample U)
  | .Uinv => onCopy (C.copy t) (onSample (star U))
  | .B => onCopy (C.copy t) B
  | .Binv => onCopy (C.copy t) (star B)

open Classical in
/-- The operator a circuit implements with the oracles `U` and `B`:
`G_T · O_T ⋯ G_1 · O_1 · G_0`, where `O_t` is the `t`-th oracle call. -/
noncomputable def OracleCircuit.implemented {I : Type} [Fintype I] {N : ℕ} {V : Type}
    {E : Finset V} (C : OracleCircuit I N E) (U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (B : Matrix (Fin (N + 1) × E) (Fin (N + 1) × E) ℂ) :
    Matrix (Label I N E C.r C.A) (Label I N E C.r C.A) ℂ :=
  ((List.finRange C.T).map (fun t => C.gate t.succ * C.call U B t)).reverse.prod * C.gate 0

/-- A **quantum estimator** with outputs in `Out`: an oracle circuit without input register,
followed by a measurement of every register in the computational basis and a classical output map
from the measured label to `Out`.

**Formalization Note.** This is the reading of the paper's informal "quantum estimator" /
"algorithm" (arXiv:2111.09787v2, §2.2, §3): the paper gives no formal model. The output map, like the
gates, does not see the probability mass function, the random variable or the oracles. -/
structure Estimator (N : ℕ) {V : Type} (E : Finset V) (Out : Type) extends
    OracleCircuit Unit N E where
  /-- The classical output computed from the measured label. -/
  out : Label Unit N E r A → Out

open Classical in
/-- The probability that an estimator, run with the oracles `U`, `B` from the all-zero state
`|0⟩|0⃗⟩`, outputs an element of `S`: the sum of `|⟨ℓ| W |0⟩|0⃗⟩|²` over the labels `ℓ` whose output
lies in `S`, where `W` is the implemented operator. -/
noncomputable def Estimator.successProb {N : ℕ} {V : Type} [Zero V] {E : Finset V} {Out : Type}
    (M : Estimator N E Out) (h0 : (0 : V) ∈ E) (U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (B : Matrix (Fin (N + 1) × E) (Fin (N + 1) × E) ℂ) (S : Set Out) : ℝ :=
  ∑ ℓ : Label Unit N E M.r M.A,
    if M.out ℓ ∈ S then
      Complex.normSq (M.toOracleCircuit.implemented U B ℓ ((), initAux h0 M.r M.A))
    else 0

/-- The Euclidean norm `‖v‖ = (Σ_i |v_i|²)^{1/2}` of a vector of a finite-dimensional Hilbert space
`ℂ^ι`. -/
noncomputable def cnorm {ι : Type} [Fintype ι] (v : ι → ℂ) : ℝ :=
  Real.sqrt (∑ i, Complex.normSq (v i))

end QMultiMean


