-- Prove2me | Definitions.Def_ConstDepthUnitary_Synth
-- name    : ConstDepthUnitary_Synth
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:48:14.417644+00:00
-- url     : https://prove2.me/theorems/72f9e7ae-5190-46d2-8e1e-9fa84c73dc92
-- title:
--   Unitary synthesis statements, plain and oracle
-- statement:
--   For $q$ qubits, four classes of targets on $\mathbb C^{2^q}$: all unitaries, real unitaries, real symmetric involutions, and traceless real symmetric involutions.
--
--   For a class $\mathcal G$, the plain statement `Synth std G s d w ε` says: every $U\in\mathcal G$ has a circuit on $q$ target qubits and some number $m$ of ancillas with size at most $s$, depth at most $d$, width $q+m\le w$, implementing $U$ up to operator norm distance $\varepsilon$. With `std = true` the circuit has only one- and two-qubit gates, otherwise fan-out is allowed.
--
--   The oracle statement `SynthOracle std G Ω qq s d w ε` says: there is **one** query algorithm $A$, with exactly $qq$ queries and the same resource bounds, such that for every $U\in\mathcal G$ some oracle $O\in\Omega$ makes $A^O$ implement $U$ up to $\varepsilon$.
-- source:
--   Nehoran, Slote, Yuen, All Unitaries Have Constant Depth Quantum Circuits, arXiv:2609.40351 (version of 2026-11-03, sha256 45cfb6a7…), Lemma 3.1 and footnotes 9–10, pp.14–15

import Mathlib
import Definitions.Def_ConstDepthUnitary_Circuit
import Definitions.Def_ConstDepthUnitary_OGate
import Definitions.Def_ConstDepthUnitary_ancEmbed
import Definitions.Def_ConstDepthUnitary_ImplementsWithin
import Definitions.Def_ConstDepthUnitary_IsTRS
open scoped Matrix.Norms.L2Operator

namespace ConstDepthUnitary

/-- All `q`-qubit unitaries, the class `U(N)`, `N = 2^q`, of Lemma 3.1, item 1.

Nehoran, Slote, Yuen, *All Unitaries Have Constant Depth Quantum Circuits*, arXiv:2609.40351 (version of 2026-11-03, sha256 45cfb6a7…), Lemma 3.1, pp.14–15. -/
def unitaryClass (q : ℕ) : Set (Matrix (Fin q → Bool) (Fin q → Bool) ℂ) :=
  {U | U ∈ Matrix.unitaryGroup (Fin q → Bool) ℂ}

/-- The real unitaries `O(N)`, Lemma 3.1, item 2. -/
def orthogonalClass (q : ℕ) : Set (Matrix (Fin q → Bool) (Fin q → Bool) ℂ) :=
  {U | ∃ R : Matrix (Fin q → Bool) (Fin q → Bool) ℝ, R * R.transpose = 1 ∧ U = R.map Complex.ofReal}

/-- The real symmetric involutions, Lemma 3.1, item 3 and footnote 10 (`U⁻¹ = U† = Uᵀ = U`). -/
def symInvolutionClass (q : ℕ) : Set (Matrix (Fin q → Bool) (Fin q → Bool) ℂ) :=
  {U | ∃ R : Matrix (Fin q → Bool) (Fin q → Bool) ℝ, R.IsSymm ∧ R * R = 1 ∧ U = R.map Complex.ofReal}

/-- The traceless real symmetric involutions, Lemma 3.1, item 4. -/
def tracelessClass (q : ℕ) : Set (Matrix (Fin q → Bool) (Fin q → Bool) ℂ) :=
  {U | ∃ R : Matrix (Fin q → Bool) (Fin q → Bool) ℝ, IsTRS R ∧ U = R.map Complex.ofReal}

/-- The plain-model synthesis statement of Lemma 3.1: for every `U` in the class `𝒢` there is a circuit
`A(U)` of size at most `s`, depth at most `d`, width at most `w`, implementing `U` up to operator norm
distance `ε`. The width counts the target and the ancilla qubits. If `std = true` the circuit has only
one- and two-qubit gates; if `std = false` fan-out gates are allowed too. -/
def Synth (std : Bool) {q : ℕ} (𝒢 : Set (Matrix (Fin q → Bool) (Fin q → Bool) ℂ))
    (s d w : ℕ) (ε : ℝ) : Prop :=
  ∀ U ∈ 𝒢, ∃ (m : ℕ) (C : Circuit (Fin q ⊕ Fin m)),
    (std = true → C.IsStandard) ∧ C.size ≤ s ∧ C.depth ≤ d ∧ q + m ≤ w ∧ ImplementsWithin C U ε

/-- The oracle-model synthesis statement of Lemma 3.1 and footnote 9: one fixed query algorithm `A` of the
stated size, depth, width and number `qq` of queries, such that for every `U` in the class `𝒢` some oracle
`O ∈ Ω` makes `A^O` implement `U` up to operator norm distance `ε`. -/
def SynthOracle (std : Bool) {q t : ℕ} (𝒢 : Set (Matrix (Fin q → Bool) (Fin q → Bool) ℂ))
    (Ω : Set (Matrix (Fin t → Bool) (Fin t → Bool) ℂ)) (qq s d w : ℕ) (ε : ℝ) : Prop :=
  ∃ (m : ℕ) (A : OCircuit (Fin q ⊕ Fin m) t),
    (std = true → A.IsStandard) ∧ A.queries = qq ∧ A.size ≤ s ∧ A.depth ≤ d ∧ q + m ≤ w ∧
      ∀ U ∈ 𝒢, ∃ O ∈ Ω,
        ‖A.matrix O * ancEmbed (Fin q) (Fin m) - ancEmbed (Fin q) (Fin m) * U‖ ≤ ε

end ConstDepthUnitary


