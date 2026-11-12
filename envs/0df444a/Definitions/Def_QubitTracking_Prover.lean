-- Prove2me | Definitions.Def_QubitTracking_Prover
-- name    : QubitTracking_Prover
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:29:06.350885+00:00
-- url     : https://prove2.me/theorems/5bd51d23-ad8f-4ae0-8a02-e3e9bda1dc15
-- title:
--   Provers in spacetime: cells, trajectories, located gates, validity and QPT families
-- statement:
--   Space is $[-1,1]$ with verifiers $\mathcal V_L$ at $-1$ and $\mathcal V_R$ at $1$; time is a real number and light travels at speed $1$. A **schedule** lists, for rounds $i=0,\dots,N$, the broadcast times and response deadlines of both verifiers.
--
--   A **prover** consists of a finite set of one-qubit **cells**, each with a trajectory $t\mapsto\mathrm{traj}_c(t)$, and a time-sorted list of gates, each placed at a spacetime point $(p,t)$. Some cells are designated: the input cells holding the register $\mathbf B$, the challenge cells carrying the bits of each verifier's round-$i$ challenge, and the response cells holding the bits of each round-$i$ response. A prover is **valid** if:
--
--   1. every cell stays in $[-1,1]$ and is $1$-Lipschitz (moves at most at the speed of light);
--   2. the designated cells are pairwise distinct;
--   3. challenge cells follow the light rays of their broadcasts (dormant at the verifier before the broadcast, lingering at the far end), and response cells are at the receiving verifier at the deadline;
--   4. every cell a gate acts on is at the gate's point;
--   5. a gate touches a challenge cell only at or after its broadcast and a response cell only at or before its deadline.
--
--   A family $(P_\lambda)$ is **QPT** if every member is valid and has at most $p(\lambda)$ gates for a polynomially bounded $p$. The state at time $t$ is the initial state after all gates with time $\le t$.
--
--   This pins down the spacetime model of §3.2, in which every positional statement of the paper is phrased.
--
--   **Formalization Note** A multi-qubit cell of the paper is a bundle of one-qubit cells with one trajectory. A circuit at an intersection point is the run, in list order, of the located gates at that point. The oracle answering a gate may depend on the gate's point, which Lemma 3.1 needs.
-- source:
--   Bartusek, Huang, Orshansky, Yuen, How To Track Qubits Through Space and Time (Or: Sailing in a Quantum Boat), arXiv:2605.30732 (held version, sha256 bf98e5b5…), §3.2, pp.21–23

import Definitions.Def_QubitTracking_Gate
import Definitions.Def_PPADSIS_SubexpSIS_Negligible

set_option autoImplicit false

open Matrix

namespace QubitTracking

/-- The verifiers' message schedule of a two-verifier positional protocol with rounds
`i = 0, …, N` (Bartusek, Huang, Orshansky, Yuen, *How To Track Qubits Through Space and Time*,
arXiv:2605.30732 (held version, sha256 bf98e5b5…), §3.2 pp.22–23 and Construction 9.5, p.66): in
round `i`, `𝒱_L` (at position `−1`) broadcasts its challenge at time `sendL i` and expects a
response at time `deadL i`; `𝒱_R` (at position `1`) broadcasts at `sendR i` and expects a
response at `deadR i`. Time is a real number. -/
structure Sched where
  N : ℕ
  sendL : Fin (N + 1) → ℝ
  sendR : Fin (N + 1) → ℝ
  deadL : Fin (N + 1) → ℝ
  deadR : Fin (N + 1) → ℝ

/-- A gate placed at a spacetime point: position `pos ∈ [−1, 1]` and time `time` (§3.2, p.22:
"the computational units of an algorithm are contained at the intersection points between its
cells"). -/
structure LocatedGate (ι : Type) (κ : Type) (inLen outLen : κ → ℕ) where
  pos : ℝ
  time : ℝ
  gate : Gate ι κ inLen outLen

/-- The light ray of a message broadcast rightwards by `𝒱_L` from position `−1` at time `s₀`:
dormant at `−1` before `s₀`, then moving at speed `1`, lingering at `1` once it reaches it
(§3.2, p.22). -/
noncomputable def lightL (s₀ s : ℝ) : ℝ := max (-1) (min 1 (-1 + (s - s₀)))

/-- The light ray of a message broadcast leftwards by `𝒱_R` from position `1` at time `s₀`. -/
noncomputable def lightR (s₀ s : ℝ) : ℝ := max (-1) (min 1 (1 - (s - s₀)))

/-- **A prover in spacetime** (the model of §3.2, pp.21–23, pinned down): a finite set of
one-qubit **cells**, each with a trajectory `traj c : ℝ → ℝ` (its position at every time), and a
time-sorted list of located gates. Some cells are designated:
* `input j` (`j < inLen`): the cells that hold the prover's input register `𝐁` from the start;
* `chalL i j`, `chalR i j` (`j < lam`): the message cells carrying the `j`-th bit of the round-`i`
  challenges of `𝒱_L` and `𝒱_R` ("for each message that could possibly be sent or received by the
  algorithm, we add a cell which travels along the same path as this message", p.22);
* `respL i j`, `respR i j` (`j < respLen`): the cells holding the `j`-th bit of the round-`i`
  responses received by `𝒱_L` and `𝒱_R`.

**Formalization Note** A multi-qubit cell of the paper is a bundle of one-qubit cells with a
common trajectory; a circuit at an intersection point is the run of the located gates at that
point, in list order. -/
structure Prover (σ : Sched) (lam inLen respLen : ℕ) (κ : Type) (inL outL : κ → ℕ) where
  Cell : Type
  [cellFintype : Fintype Cell]
  [cellDecEq : DecidableEq Cell]
  traj : Cell → ℝ → ℝ
  input : Fin inLen → Cell
  chalL : Fin (σ.N + 1) → Fin lam → Cell
  chalR : Fin (σ.N + 1) → Fin lam → Cell
  respL : Fin (σ.N + 1) → Fin respLen → Cell
  respR : Fin (σ.N + 1) → Fin respLen → Cell
  gates : List (LocatedGate Cell κ inL outL)

attribute [instance] Prover.cellFintype Prover.cellDecEq

namespace Prover

variable {σ : Sched} {lam inLen respLen : ℕ} {κ : Type} {inL outL : κ → ℕ}

/-- All designated cells of a prover, as one family. -/
def desig (P : Prover σ lam inLen respLen κ inL outL) :
    Fin inLen ⊕ (Fin (σ.N + 1) × Fin lam) ⊕ (Fin (σ.N + 1) × Fin lam) ⊕
      (Fin (σ.N + 1) × Fin respLen) ⊕ (Fin (σ.N + 1) × Fin respLen) → P.Cell :=
  Sum.elim P.input <| Sum.elim (fun p => P.chalL p.1 p.2) <| Sum.elim (fun p => P.chalR p.1 p.2) <|
    Sum.elim (fun p => P.respL p.1 p.2) (fun p => P.respR p.1 p.2)

/-- **Validity of a spacetime prover** (§3.2, pp.21–23):
1. every cell stays in `[−1, 1]` and moves at most at the speed of light (`1`-Lipschitz);
2. the designated cells are pairwise distinct;
3. the challenge cells follow the light rays of their broadcasts; the response cells are at the
   receiving verifier's position at the response deadline;
4. the gate list is sorted by time, every gate is well formed, and every cell a gate acts on is at
   the gate's position at the gate's time;
5. a gate acts on a challenge cell only at or after its broadcast time (before it, the message is
   the verifier's), and on a response cell only at or before its deadline (after it, the message is
   the verifier's). -/
structure Valid (P : Prover σ lam inLen respLen κ inL outL) : Prop where
  traj_mem : ∀ c s, P.traj c s ∈ Set.Icc (-1 : ℝ) 1
  traj_lip : ∀ c, LipschitzWith 1 (P.traj c)
  desig_inj : Function.Injective P.desig
  chalL_traj : ∀ i j s, P.traj (P.chalL i j) s = lightL (σ.sendL i) s
  chalR_traj : ∀ i j s, P.traj (P.chalR i j) s = lightR (σ.sendR i) s
  respL_at : ∀ i j, P.traj (P.respL i j) (σ.deadL i) = -1
  respR_at : ∀ i j, P.traj (P.respR i j) (σ.deadR i) = 1
  sorted : P.gates.Pairwise (fun g h => g.time ≤ h.time)
  wellFormed : ∀ g ∈ P.gates, g.gate.WellFormed
  colocated : ∀ g ∈ P.gates, ∀ c, g.gate.Touches c → P.traj c g.time = g.pos
  chalL_after : ∀ g ∈ P.gates, ∀ i j, g.gate.Touches (P.chalL i j) → σ.sendL i ≤ g.time
  chalR_after : ∀ g ∈ P.gates, ∀ i j, g.gate.Touches (P.chalR i j) → σ.sendR i ≤ g.time
  respL_before : ∀ g ∈ P.gates, ∀ i j, g.gate.Touches (P.respL i j) → g.time ≤ σ.deadL i
  respR_before : ∀ g ∈ P.gates, ∀ i j, g.gate.Touches (P.respR i j) → g.time ≤ σ.deadR i

/-- The matrix of a located gate on the global register `𝐀 ⊗ (cells)` (the extra register `A`,
e.g. the anchor, is never acted on), with the oracle assignment in force at the gate's point. -/
noncomputable def lgMat (P : Prover σ lam inLen respLen κ inL outL) (A : Type) [Fintype A]
    [DecidableEq A] (orcAt : ℝ → ℝ → OracleAssign κ inL outL)
    (g : LocatedGate P.Cell κ inL outL) : Matrix (Bits (A ⊕ P.Cell)) (Bits (A ⊕ P.Cell)) ℂ :=
  (g.gate.map Sum.inr).mat (orcAt g.pos g.time)

open Classical in
/-- The global state at time `t`: the initial state `ψ₀` on `A ⊗ (cells)` after all gates with
time `≤ t`, in list order (circuits are instantaneous, p.22). The oracle answering a gate may
depend on the gate's point (`orcAt pos time`); in the protocol it is constant. -/
noncomputable def stateAt (P : Prover σ lam inLen respLen κ inL outL) (A : Type) [Fintype A]
    [DecidableEq A] (orcAt : ℝ → ℝ → OracleAssign κ inL outL) (ψ₀ : Bits (A ⊕ P.Cell) → ℂ)
    (t : ℝ) : Bits (A ⊕ P.Cell) → ℂ :=
  ((P.gates.filter (fun g => decide (g.time ≤ t))).foldl
    (fun acc g => P.lgMat A orcAt g * acc) 1) *ᵥ ψ₀

/-- The global state after all gates (the prover has terminated). -/
noncomputable def finalState (P : Prover σ lam inLen respLen κ inL outL) (A : Type) [Fintype A]
    [DecidableEq A] (orcAt : ℝ → ℝ → OracleAssign κ inL outL) (ψ₀ : Bits (A ⊕ P.Cell) → ℂ) :
    Bits (A ⊕ P.Cell) → ℂ :=
  (P.gates.foldl (fun acc g => P.lgMat A orcAt g * acc) 1) *ᵥ ψ₀

end Prover

/-- **QPT prover families** (§3.2, p.22: "there exists some polynomial `p(λ)` such that for all
`λ ∈ ℕ`, `𝒜_λ` terminates, and `∑ |C^{L,t}_λ| ≤ p(λ)`"): every member is a valid prover and the
number of gates of the `λ`-th member is at most `p(λ)` for a polynomially bounded `p`.

**Formalization Note** Every one-qubit unitary, two-qubit unitary and oracle query counts as one
gate; a finite gate list always terminates. Families are non-uniform, as in the paper. -/
def IsQPT {σ : ℕ → Sched} {lam inLen respLen : ℕ → ℕ} {κ : Type} {inL outL : ℕ → κ → ℕ}
    (P : (l : ℕ) → Prover (σ l) (lam l) (inLen l) (respLen l) κ (inL l) (outL l)) : Prop :=
  ∃ p : ℕ → ℕ, PPADSIS.SubexpSIS.PolyBounded p ∧ ∀ l, (P l).Valid ∧ (P l).gates.length ≤ p l

end QubitTracking


