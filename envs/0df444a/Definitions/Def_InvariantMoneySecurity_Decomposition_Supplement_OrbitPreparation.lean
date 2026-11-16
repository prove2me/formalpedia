-- Prove2me | Definitions.Def_InvariantMoneySecurity_Decomposition_Supplement_OrbitPreparation
-- name    : InvariantMoneySecurity_Decomposition_Supplement_OrbitPreparation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T12:29:35.884553+00:00
-- url     : https://prove2.me/theorems/9d57e533-cca6-4262-8bbd-13aba8a7faef
-- title:
--   Definition 3.10 — orbit state preparation solvable on a family of seeds
-- statement:
--   A **family of seeds** is $G=(G_n)$ with $G_n\subseteq X_n$, an arbitrary subset of the ground set; no decidability or efficiency is assumed.
--
--   A family of states $|\phi_x\rangle$ on $o(n)$ qubits, indexed by seeds, **can be prepared from $x$** on $G$ if there are a uniform family of polynomial-size circuits $\mathrm{Prep}=(\mathrm{Prep}_n)$ acting on an $n$-qubit input register and $m=m(n)$ ancilla qubits, with every wire kept as output, and a negligible function $\mu$, such that for every $n$ and every $x\in G_n$ there is a unit ancilla vector $|a_x\rangle$ (which may depend on $x$) with
--   $$\big\|\,\mathrm{Prep}_n|x\rangle|0^m\rangle-|\phi_x\rangle\otimes|a_x\rangle\,\big\|\le\mu(n)$$
--   in the Euclidean norm of the pure output. The target state must therefore come out unentangled from the ancilla.
--
--   **Orbit state preparation is solvable on $G$** if this holds for the orbit states $|\phi_x\rangle=|\psi_{k(x)}\rangle$, the uniform superposition over the orbit of $x$. Such a family is a solver for orbit state preparation on $G$.
--
--   **Formalization Note** The circuit is the published uniform QPT model with all of its wires designated as outputs (the output map onto the wires is surjective): the first $o(n)$ output wires carry $|\phi_x\rangle$, the last $m(n)$ carry the ancilla. The pure output is the circuit unitary applied to the clean initialization of $|x\rangle$; nothing is traced out. This is not the published mixed-output fidelity notion `Prepares`, which discards garbage.
-- source:
--   Hans Schmiedel, Jiangshan Yu, STOC 2027 submission #164 (October 2026), pp. 13–14, Definition 3.10, equation (9)

import Definitions.Def_InvariantMoneySecurity_Decomposition_Scheme
set_option autoImplicit false
noncomputable section

namespace InvariantMoneySecurity.Decomposition.Supplement

open InvariantMoneySecurity.Decomposition

/-- A family of seeds: an arbitrary set `G n` of objects of the ground set, for every `n`.
No decidability or efficiency is assumed. -/
abbrev SeedFamily (D : Scheme) := ∀ n, Set (D.data n).Object

/-- The pure output of a circuit on a computational-basis input, on all of its wires:
`U V |input⟩`, with no wire discarded. -/
def pureOutput {i o : ℕ} (C : Circuit i o) (input : Bits i) : Bits C.width → ℂ :=
  (C.operator * C.initializer).mulVec (basisVector input)

/-- Definition 3.10, general form ("a family of states can be prepared from `x`").
A uniform QPT family `Prep` with an `n`-qubit input register and `m(n)` ancilla qubits, whose
retained outputs are *all* its wires (the first `o(n)` the target register, the last `m(n)` the
ancilla), and a negligible `μ`, such that for every `n` and every seed `x ∈ G n` there is a unit
ancilla vector `a_x` with `‖Prep|x⟩|0^m⟩ − |ϕ_x⟩ ⊗ |a_x⟩‖ ≤ μ(n)` in the Euclidean norm. -/
def PreparableFrom (D : Scheme) (G : SeedFamily D) (o : ℕ → ℕ)
    (target : ∀ n, (D.data n).Object → Bits (o n) → ℂ) : Prop :=
  ∃ m : ℕ → ℕ, ∃ P : QPT (fun n => n) (fun n => o n + m n),
    (∀ n, Function.Surjective (P.circuit n).outputWire) ∧
    ∃ μ : ℕ → ℝ, Negligible μ ∧
      ∀ n, ∀ x ∈ G n, ∃ a : Bits (m n) → ℂ, (∑ b, ‖a b‖ ^ 2 = 1) ∧
        Real.sqrt (∑ c : Bits (P.circuit n).width,
          ‖pureOutput (P.circuit n) x.val c -
            target n x (fun j => c ((P.circuit n).outputWire (Fin.castAdd (m n) j))) *
            a (fun j => c ((P.circuit n).outputWire (Fin.natAdd (o n) j)))‖ ^ 2) ≤ μ n

/-- Definition 3.10: orbit state preparation is solvable on `G` — the orbit state
`|ψ_{k(x)}⟩` (the published `orbitVector`) can be prepared from every seed `x ∈ G n`. -/
def OrbitPrepSolvable (D : Scheme) (G : SeedFamily D) : Prop :=
  PreparableFrom D G (fun n => n) (fun n x => (D.data n).orbitVector x)

end InvariantMoneySecurity.Decomposition.Supplement


