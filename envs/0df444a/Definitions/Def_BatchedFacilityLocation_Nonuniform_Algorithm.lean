-- Prove2me | Definitions.Def_BatchedFacilityLocation_Nonuniform_Algorithm
-- name    : BatchedFacilityLocation_Nonuniform_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:11:52.575131+00:00
-- url     : https://prove2.me/theorems/74d828da-8276-4cb0-8578-3bee6ddd7156
-- title:
--   The marginal Meyerson rule and its execution under batched random order
-- statement:
--   This file defines the algorithm of §4.1 and its execution.
--
--   **One step.** A client at site $v$ arrives facing the open set $F_v$ and draws $U_v^{(1)},\dots,U_v^{(m)}$. The level-$j$ lottery succeeds iff, as in (4.2),
--   $$d_v^{(j)}+f_jU_v^{(j)}\le\min\{d(v,F_v),\,d_v^{(j-1)}\},$$
--   all levels using the same pre-client set $F_v$. Each successful level selects a closest point of $F_v\cup M_j$ (with a fixed tie-breaking rule, a parameter); every selected facility not already open is opened, paying its *original* cost $f(y)$, and $v$ is connected to a closest facility of the resulting set $F_v^+$. Thus
--   $$\mathrm{cost}(v)=\sum_{y\in F_v^+\setminus F_v}f(y)+d(v,F_v^+).$$
--   When $F_v=\emptyset$ the first lottery succeeds surely. The lottery probability of (4.1) is $p_v^{(j)}=\min\{1,(\Delta_v^{(j-1)}-\Delta_v^{(j)})/f_j\}$ with $\Delta_v^{(j)}=\min\{d(v,F_v),d_v^{(j)}\}$ and $\Delta_v^{(0)}=d(v,F_v)$.
--
--   **Execution.** Clients are processed one at a time from the empty open set. Under batched random order the batch order is a uniformly random permutation $\sigma$ of the $B$ batches, and inside each batch the algorithm processes the clients in a uniformly random order, independently across batches. This is realized by a uniform permutation $\tau$ of all clients: client $i$ is processed at lexicographic position $(\sigma(\mathrm{batch}(i)),\tau(i))$. The execution records $F_v$ and $\mathrm{cost}(v)$ for every client; $\mathrm{ALG}(C)=\sum_{v\in C}\mathrm{cost}(v)$ and $\mathrm{ALG}=\sum_v\mathrm{cost}(v)$.
--
--   **Expectation.** $\mathbb E[X]$ averages over the $B!$ batch orders, the $n!$ permutations $\tau$, and integrates over the lottery array.
--
--   **Formalization Note** The algorithm is online: the step uses only $F_v$, the client's site, the known sites and costs, and its own lotteries.
-- source:
--   Fabrizio Grandoni, Stefano Leonardi, Matteo Russo, Metric Facility Location under Batched Random Order, STOC 2027 submission #212 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/212.pdf (source.pdf sha256 2e976c4133df9baa0c32b4cd22b6e370c2c4611dfe4d4dec02ceb01bd7a0dc94), §4.1 p. 13–14, eqs. (4.1)–(4.2); §2 p. 7 (batched random order, in-batch shuffle); §3.1 p. 9 (lotteries independent of both orders)

import Mathlib
import Definitions.Def_BatchedFacilityLocation_Nonuniform_Model

open MeasureTheory
open scoped ENNReal

namespace BatchedFacilityLocation.Nonuniform

noncomputable section

open Classical

/-! # The marginal Meyerson algorithm and its batched random-order execution

§4.1, p. 13–14, eqs. (4.1)–(4.2); §2, p. 7 (batched random order, in-batch shuffle);
§3.1, p. 9 (lotteries independent across clients and of both random orders). -/

variable {S : Type*} [Fintype S] [MetricSpace S]

/-- A fixed distance tie-breaking rule: `pick A x` is a closest point of `A` to `x` whenever
`A` is nonempty ("fixed distance tie breaking", p. 13–14). Every theorem of the mission is
stated for an arbitrary such rule. -/
structure TieBreak (S : Type*) [MetricSpace S] where
  pick : Finset S → S → S
  pick_mem : ∀ (A : Finset S) (x : S), A.Nonempty → pick A x ∈ A
  pick_min : ∀ (A : Finset S) (x : S), A.Nonempty → ∀ z ∈ A, dist x (pick A x) ≤ dist x z

/-! ## One step of the marginal rule (processing one client) -/

/-- The level-`j` lottery of a client at site `x`, facing the pre-client open set `F`, with
lottery vector `u`, succeeds iff (4.2):
`d_v^{(j)} + f_j U_v^{(j)} ≤ min {d(v, F_v), d_v^{(j-1)}}`. -/
def succeeds (f : S → ℝ) (F : Finset S) (x : S) (u : Lev f → ℝ) (t : Lev f) : Prop :=
  dset x (Mset f t) + ENNReal.ofReal ((t : ℝ) * u t) ≤ min (dset x F) (dset x (MsetLt f t))

/-- The facilities selected by the successful lotteries: for each successful level `j`, the
closest point of `F ∪ M_j` to `x` (tie-breaking by `tb`). -/
def selected (tb : TieBreak S) (f : S → ℝ) (F : Finset S) (x : S) (u : Lev f → ℝ) :
    Finset S :=
  (Finset.univ.filter (succeeds f F x u)).image (fun t => tb.pick (F ∪ Mset f t) x)

/-- `F_v^+`: the open set after processing the client (every selected facility not already
open is opened). -/
def Fplus (tb : TieBreak S) (f : S → ℝ) (F : Finset S) (x : S) (u : Lev f → ℝ) : Finset S :=
  F ∪ selected tb f F x u

/-- `cost(v)`: the original opening costs `f(y)` of the newly opened facilities plus the
connection distance `d(v, F_v^+)` to a closest open facility. -/
def stepCost (tb : TieBreak S) (f : S → ℝ) (F : Finset S) (x : S) (u : Lev f → ℝ) : ℝ≥0∞ :=
  (∑ y ∈ Fplus tb f F x u \ F, ENNReal.ofReal (f y)) + dset x (Fplus tb f F x u)

/-- `Δ_v^{(j-1)} = min {d(v, F_v), d_v^{(j-1)}}` (with `d_v^{(0)} = ∞`, so `Δ_v^{(0)} = d(v,F_v)`). -/
def DeltaPrev (f : S → ℝ) (F : Finset S) (x : S) (t : Lev f) : ℝ≥0∞ :=
  min (dset x F) (dset x (MsetLt f t))

/-- `Δ_v^{(j)} = min {d(v, F_v), d_v^{(j)}}`. -/
def Delta (f : S → ℝ) (F : Finset S) (x : S) (t : Lev f) : ℝ≥0∞ :=
  min (dset x F) (dset x (Mset f t))

/-- The lottery probability (4.1): `p_v^{(j)} = min {1, (Δ_v^{(j-1)} - Δ_v^{(j)}) / f_j}`. -/
def pLottery (f : S → ℝ) (F : Finset S) (x : S) (t : Lev f) : ℝ≥0∞ :=
  min 1 ((DeltaPrev f F x t - Delta f F x t) / ENNReal.ofReal (t : ℝ))

/-! ## Sequential execution -/

/-- State of an execution: the current open set, and for each processed client the open set
`F_v` just before it and its cost `cost(v)`. -/
structure RunState (ι : Type*) (S : Type*) where
  F : Finset S
  pre : ι → Finset S
  cost : ι → ℝ≥0∞

/-- Process the clients of a list one at a time, in list order; client `i` is at site `site i`
and uses lottery vector `lot i`. -/
def runFrom {ι : Type*} [DecidableEq ι] (tb : TieBreak S) (f : S → ℝ) (site : ι → S)
    (lot : ι → Lev f → ℝ) : List ι → RunState ι S → RunState ι S
  | [], st => st
  | i :: rest, st =>
      runFrom tb f site lot rest
        { F := Fplus tb f st.F (site i) (lot i)
          pre := Function.update st.pre i st.F
          cost := Function.update st.cost i (stepCost tb f st.F (site i) (lot i)) }

/-- The execution of the marginal Meyerson algorithm from the empty open set. -/
def run {ι : Type*} [DecidableEq ι] (tb : TieBreak S) (f : S → ℝ) (site : ι → S)
    (lot : ι → Lev f → ℝ) (order : List ι) : RunState ι S :=
  runFrom tb f site lot order ⟨∅, fun _ => ∅, fun _ => 0⟩

/-! ## Batched random order on an indexed instance

The batch order is a uniform `σ : Equiv.Perm (Fin B)` (`σ b` is the arrival position of batch
`b`); the in-batch shuffle is realized by a uniform `τ : Equiv.Perm (Fin n)`: inside a batch,
client `i` is processed before `i'` iff `τ i < τ i'`. Since `τ` restricted to each batch induces
independent uniform orders of the batches, independent of `σ`, this is the paper's arrival law.
Client `i` is processed at lexicographic key `(σ (batch i), τ i)`. -/

/-- The processing key `(σ(batch i), τ(i))`, encoded lexicographically in `ℕ`. -/
def arrivalKey (I : Instance S) (σ : Equiv.Perm (Fin I.B)) (τ : Equiv.Perm (Fin I.n))
    (i : Fin I.n) : ℕ :=
  (σ (I.batch i)).val * I.n + (τ i).val

/-- The processing order: all clients sorted by their arrival key (keys are distinct). -/
def order (I : Instance S) (σ : Equiv.Perm (Fin I.B)) (τ : Equiv.Perm (Fin I.n)) :
    List (Fin I.n) :=
  (List.finRange I.n).mergeSort (fun i j => decide (arrivalKey I σ τ i ≤ arrivalKey I σ τ j))

/-- The single-copy execution on instance `I` (all clients processed by one copy). -/
def runI (tb : TieBreak S) (f : S → ℝ) (I : Instance S) (σ : Equiv.Perm (Fin I.B))
    (τ : Equiv.Perm (Fin I.n)) (U : Fin I.n → Lev f → ℝ) : RunState (Fin I.n) S :=
  run tb f I.loc U (order I σ τ)

/-- `F_v`: the open set just before client `i` is processed. -/
def Fpre (tb : TieBreak S) (f : S → ℝ) (I : Instance S) (σ : Equiv.Perm (Fin I.B))
    (τ : Equiv.Perm (Fin I.n)) (U : Fin I.n → Lev f → ℝ) (i : Fin I.n) : Finset S :=
  (runI tb f I σ τ U).pre i

/-- `cost(v)` of client `i` in the single-copy execution. -/
def cost (tb : TieBreak S) (f : S → ℝ) (I : Instance S) (σ : Equiv.Perm (Fin I.B))
    (τ : Equiv.Perm (Fin I.n)) (U : Fin I.n → Lev f → ℝ) (i : Fin I.n) : ℝ≥0∞ :=
  (runI tb f I σ τ U).cost i

/-- `ALG(C) = Σ_{v ∈ C} cost(v)`. -/
def ALGC (tb : TieBreak S) (f : S → ℝ) (I : Instance S) (C : Finset (Fin I.n))
    (σ : Equiv.Perm (Fin I.B)) (τ : Equiv.Perm (Fin I.n)) (U : Fin I.n → Lev f → ℝ) : ℝ≥0∞ :=
  ∑ i ∈ C, cost tb f I σ τ U i

/-- `ALG = Σ_v cost(v)`, the total cost of the single-copy algorithm. -/
def ALG (tb : TieBreak S) (f : S → ℝ) (I : Instance S)
    (σ : Equiv.Perm (Fin I.B)) (τ : Equiv.Perm (Fin I.n)) (U : Fin I.n → Lev f → ℝ) : ℝ≥0∞ :=
  ∑ i, cost tb f I σ τ U i

/-- Expectation over the arrival law and the lotteries: `σ` uniform on the `B!` batch orders,
`τ` uniform on the `n!` client permutations, and the lottery array i.i.d. uniform on `[0,1]`,
all independent. -/
def Ex (f : S → ℝ) (I : Instance S)
    (X : Equiv.Perm (Fin I.B) → Equiv.Perm (Fin I.n) → (Fin I.n → Lev f → ℝ) → ℝ≥0∞) :
    ℝ≥0∞ :=
  ((I.B.factorial : ℝ≥0∞) * (I.n.factorial : ℝ≥0∞))⁻¹ *
    ∑ σ : Equiv.Perm (Fin I.B), ∑ τ : Equiv.Perm (Fin I.n),
      ∫⁻ U, X σ τ U ∂(lotteryLaw f (Fin I.n))

end

end BatchedFacilityLocation.Nonuniform


