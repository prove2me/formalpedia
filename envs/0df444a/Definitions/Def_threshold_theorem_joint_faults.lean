-- Prove2me | Definitions.Def_threshold_theorem_joint_faults
-- name    : threshold_theorem_joint_faults
-- status  : Definition
-- author  : @shivm
-- created : 2026-10-25T21:21:35.663995+00:00
-- url     : https://prove2.me/theorems/7b8ef218-4ade-455d-93a6-ce3414fd783d
-- title:
--   Layer-wise joint faults, bad qubits and predecessor locations for layered circuits
-- statement:
--   Auxiliary notions for the level reduction in the proof of the quantum threshold theorem, built on the layered circuit model `threshold_theorem_noise_model` and the fault semantics of `threshold_theorem_local_stochastic`.
--
--   A *location* of a layered circuit $C$ is a pair $(t,j)$: location number $j$ of layer number $t$ (both counted from $0$). `locAt C (t, j)` is that location, if it exists.
--
--   **Bad qubits.** For a set $B$ of locations and a layer index $t$, $\mathrm{bad}_t(B)\subseteq Q$ is the set of qubits acted on by the locations $(t,j)\in B$ that exist in $C$.
--
--   **Predecessors.** $\mathrm{pred}_C(B)$ is the finite set of locations $(t-1,j')$ of $C$ that share a qubit with some location $(t,j)\in B$ with $t\ge 1$. Since every layer acts on every qubit exactly once, every qubit of a location $(t,j)$, $t\ge1$, is the output qubit of exactly one location of layer $t-1$, and that location lies in $\mathrm{pred}_C(\{(t,j)\})$.
--
--   **Joint faults.** In `faultyState` the faulty locations of a layer act one after another, each by its own channel on its qubits and the $m$-qubit environment. A *joint fault* $J=(k,s,\mathcal E)$ is instead a channel $\mathcal E$ on $k$ distinct data qubits $s(0),\dots,s(k-1)$ together with the whole environment. Given a set $B$ of faulty locations and a joint fault $J_t$ for every layer $t$, the execution `jointFaultyState B J C` starts in $|0\cdots0\rangle$ on data and environment and runs the layers in order. In layer $t$, every location $(t,j)\notin B$ acts ideally on its qubits, the locations $(t,j)\in B$ do not act, and then $J_t$ acts:
--   $$\rho\;\longmapsto\;\mathcal E_t\Big(\prod_{(t,j)\notin B}\mathcal U_{(t,j)}(\rho)\Big).$$
--   Usually one requires $s_t$ to take values in $\mathrm{bad}_t(B)$. Then all faulty locations of one layer are replaced by one channel that acts jointly on all their qubits and the environment, with no fixed order among them. This is the fault model of the level reduction of Aliferis, Gottesman and Preskill, where the bad extended rectangles of one time step are replaced by one arbitrary, possibly correlated, fault.
-- source:
--   P. Aliferis, D. Gottesman, J. Preskill, Quantum accuracy threshold for concatenated distance-3 codes, Quantum Inf. Comput. 6 (2006) 97-165, arXiv:quant-ph/0504218, Sec. 5 (level reduction: bad extended rectangles replaced by faulty, possibly correlated, level-0 locations); D. Gottesman, An introduction to quantum error correction and fault-tolerant quantum computation, arXiv:0904.2557, Sec. 5. Built on Prove2Me definitions threshold_theorem_noise_model and threshold_theorem_local_stochastic.

import Mathlib
import Definitions.Def_threshold_theorem_local_stochastic

/-!
# Layer-wise joint faults, bad qubits and predecessor locations

Auxiliary notions for the level reduction of the threshold theorem, built on
`Definitions.Def_threshold_theorem_local_stochastic`. In `faultyState` the faulty locations of a
layer act one after another (each jointly with the environment). Here all faulty locations of a
layer are instead replaced by **one** channel acting jointly on all their qubits and on the
environment.
-/

open Matrix

namespace ThresholdTheorem

/-- The location number `ℓ.2` of layer number `ℓ.1` of `C`, if it exists. -/
def locAt {Q : Type*} [DecidableEq Q] (C : Circuit Q) (ℓ : ℕ × ℕ) : Option (Location Q) :=
  (C[ℓ.1]?).bind fun L => L.locs[ℓ.2]?

/-- The qubits acted on by those locations of layer `t` of `C` that belong to `B`. -/
def badQubits {Q : Type*} [DecidableEq Q] (C : Circuit Q) (B : Finset (ℕ × ℕ)) (t : ℕ) :
    Set Q :=
  {q | ∃ (j : ℕ) (l : Location Q), (t, j) ∈ B ∧ locAt C (t, j) = some l ∧ q ∈ Set.range l.support}

open Classical in
/-- The predecessor locations of `B`: the locations `(t - 1, j')` of `C` that share a qubit with
some location `(t, j) ∈ B` with `t ≥ 1`. -/
noncomputable def predLocs {Q : Type*} [DecidableEq Q] (C : Circuit Q) (B : Finset (ℕ × ℕ)) :
    Finset (ℕ × ℕ) :=
  B.biUnion fun ℓ =>
    ((Finset.range C.size).filter fun j =>
      0 < ℓ.1 ∧ ∃ l l' : Location Q, locAt C (ℓ.1 - 1, j) = some l ∧ locAt C ℓ = some l' ∧
        ∃ i i', l.support i = l'.support i').image fun j => (ℓ.1 - 1, j)

/-- A joint fault of one layer: a channel acting jointly on `k` distinct data qubits `supp` and on
the whole `m`-qubit environment. -/
structure JointFault (Q : Type*) (m : ℕ) where
  /-- Number of data qubits acted on. -/
  k : ℕ
  /-- The data qubits acted on. -/
  supp : Fin k ↪ Q
  /-- The channel, on the `k` data qubits followed by the `m` environment qubits. -/
  chan : Channel (k + m)

/-- Execution of layer number `t` with joint faults: every location `(t, j) ∉ B` acts ideally on
its qubits, the locations `(t, j) ∈ B` do not act, and then the joint channel `J` acts on its data
qubits and the environment. -/
noncomputable def jointLayer {Q : Type*} [Fintype Q] [DecidableEq Q] {m : ℕ}
    (B : Finset (ℕ × ℕ)) (J : JointFault Q m) (t : ℕ) (L : Layer Q)
    (ρ : Op (Q ⊕ Fin m)) : Op (Q ⊕ Fin m) :=
  applyKraus (envEmbed m J.supp) J.chan.kraus
    (L.locs.zipIdx.foldl
      (fun σ ℓj => if (t, ℓj.2) ∈ B then σ else
        applyKraus (ℓj.1.support.trans Function.Embedding.inl) ℓj.1.op.idealKraus σ) ρ)

/-- Final state of the execution of `C`, started in `|0…0⟩` on data and environment, in which the
locations of `B` are faulty and the faults of layer `t` act through the single joint fault
`J t`. -/
noncomputable def jointFaultyState {Q : Type*} [Fintype Q] [DecidableEq Q] {m : ℕ}
    (B : Finset (ℕ × ℕ)) (J : ℕ → JointFault Q m) (C : Circuit Q) : Op (Q ⊕ Fin m) :=
  C.zipIdx.foldl (fun σ Lt => jointLayer B (J Lt.2) Lt.2 Lt.1 σ) (initState (Q ⊕ Fin m))

end ThresholdTheorem


