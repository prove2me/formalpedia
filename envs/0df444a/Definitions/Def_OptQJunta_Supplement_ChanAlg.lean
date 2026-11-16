-- Prove2me | Definitions.Def_OptQJunta_Supplement_ChanAlg
-- name    : OptQJunta_Supplement_ChanAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:13:52.252216+00:00
-- url     : https://prove2.me/theorems/515e622c-bfbb-45e5-b932-7b9d218bf03e
-- title:
--   Query algorithms with channel access $\mathcal O_\Phi=\Phi\otimes I_W$
-- statement:
--   With **channel access** to an unknown $n$-qubit channel $\Phi$ (§2.5.3), one query applies $\mathcal O_\Phi=\Phi\otimes I_W$ to the joint state of the query register $Q$ and the workspace $W$, so its input may be entangled with $W$; the oracle gives no access to an environment or a Kraus label. A $T$-query algorithm starts from an oracle-independent state $|\psi\rangle$ of $Q\otimes W$ and evolves it as
--
--   $$
--   \rho_0=U_0|\psi\rangle\langle\psi|U_0^\dagger,\qquad \rho_{i+1}=U_{i+1}\,(\Phi\otimes I_W)(\rho_i)\,U_{i+1}^\dagger\quad(0\le i<T),
--   $$
--
--   with oracle-independent unitaries $U_0,\dots,U_T$; the output is a function of a computational-basis measurement of $\rho_T$.
--
--   This is the access model of the channel lower bound (Theorem 6.3). For a unitary channel $\Phi_U$, one channel query is one forward query to $U$.
--
--   **Formalization Note** $(\Phi\otimes I_W)(\rho)$ applies $\Phi$ to every $Q$-block $\rho_{w,w'}$ of $\rho$. The paper's algorithms may use mixed initial states, interleaving channels, randomness, intermediate measurements and an accepting POVM; Stinespring and Naimark dilation into a larger finite workspace and padding with dummy queries turn every such algorithm into one of this form with the same acceptance probability on every channel.
-- source:
--   Bao, Gao, Yao, Optimal Quantum Junta Testing, preprint (version of November 3, 2026, sha256 a97d09a4…), §2.5, p.22; §2.5.3, p.23; §5.4.2, p.67

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Channel

namespace OptQJunta.Supplement

open QAlgorithms

/-- The channel query `𝒪_Φ = Φ ⊗ I_W` on the joint state of the query register `Q` (`n` qubits) and
the workspace `W` (Bao, Gao, Yao, *Optimal Quantum Junta Testing*, preprint, version of November 3,
2026, sha256 a97d09a4…, §2.5.3, p.23): `Φ` is applied to every `Q`-block
`ρ_{w,w'} = (ρ_{(a,w),(b,w')})_{a,b}` of `ρ`, so the query input may be entangled with `W`.

**Formalization Note** For a linear `Φ` this is `Φ ⊗ id_W` (expand `ρ = Σ_{w,w'} ρ_{w,w'} ⊗ |w⟩⟨w'|`).
The oracle gives no access to an environment or a Kraus label of `Φ`. -/
def tensorIdW {n : ℕ} {W : Type} (Φ : Superop (Qubits n) (Qubits n)) :
    Superop (Qubits n × W) (Qubits n × W) :=
  fun ρ => Matrix.of fun p p' => Φ (Matrix.of fun a b => ρ (a, p.2) (b, p'.2)) p.1 p'.1

/-- A `T`-query algorithm with channel access to an `n`-qubit channel (Bao–Gao–Yao preprint, version
of November 3, 2026, sha256 a97d09a4…, §2.5, p.22, and §2.5.3, p.23): an oracle-independent unit start
vector on `Q × W` and oracle-independent unitaries `U_0, …, U_T` on `Q × W`, `W` a finite workspace.
The state evolves as `ρ ↦ U_0 ρ U_0†`, then `T` times `ρ ↦ U_{i+1} (Φ ⊗ I_W)(ρ) U_{i+1}†`, and the
output is a function of the final computational-basis measurement.

**Formalization Note** The paper's algorithms may use a mixed initial state, interleaving channels,
private randomness, intermediate measurements, adaptivity and an arbitrary accepting POVM, and make
at most `T` queries in every execution. By Stinespring and Naimark dilation into a larger finite
workspace (purification of the initial state and the randomness, deferred measurement) and padding
with dummy queries, every such algorithm has the same acceptance probability on every channel as an
algorithm of this form. -/
structure ChanAlg (n : ℕ) (W : Type) [Fintype W] [DecidableEq W] (T : ℕ) where
  /-- The oracle-independent unitaries `U_0, …, U_T`. -/
  U : Fin (T + 1) → Matrix.unitaryGroup (Qubits n × W) ℂ
  /-- The oracle-independent start state. -/
  start : EuclideanSpace ℂ (Qubits n × W)
  /-- It is a unit vector. -/
  start_unit : ‖start‖ = 1

namespace ChanAlg

variable {n : ℕ} {W : Type} [Fintype W] [DecidableEq W] {T : ℕ}

/-- The final density matrix `U_T 𝒪_Φ(⋯ U_1 𝒪_Φ(U_0 |ψ⟩⟨ψ| U_0†) U_1† ⋯) U_T†`. -/
noncomputable def finalState (A : ChanAlg n W T) (Φ : Superop (Qubits n) (Qubits n)) :
    Matrix (Qubits n × W) (Qubits n × W) ℂ :=
  Fin.induction (motive := fun _ => Matrix (Qubits n × W) (Qubits n × W) ℂ)
    ((A.U 0 : Matrix _ _ ℂ) *
        Matrix.vecMulVec (WithLp.ofLp A.start) (star (WithLp.ofLp A.start)) *
      (A.U 0 : Matrix _ _ ℂ).conjTranspose)
    (fun i ρ => (A.U i.succ : Matrix _ _ ℂ) * tensorIdW Φ ρ * (A.U i.succ : Matrix _ _ ℂ).conjTranspose)
    (Fin.last T)

/-- The probability that the algorithm outputs `b` on the channel `Φ`: the final
computational-basis measurement gives an outcome `z` with `out z = b`. -/
noncomputable def outputProb {β : Type} [DecidableEq β] (A : ChanAlg n W T)
    (Φ : Superop (Qubits n) (Qubits n)) (out : Qubits n × W → β) (b : β) : ℝ :=
  ∑ z ∈ Finset.univ.filter (fun z => out z = b), (A.finalState Φ z z).re

end ChanAlg

end OptQJunta.Supplement


