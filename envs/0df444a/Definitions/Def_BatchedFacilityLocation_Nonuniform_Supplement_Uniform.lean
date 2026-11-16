-- Prove2me | Definitions.Def_BatchedFacilityLocation_Nonuniform_Supplement_Uniform
-- name    : BatchedFacilityLocation_Nonuniform_Supplement_Uniform
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T15:42:53.711798+00:00
-- url     : https://prove2.me/theorems/4e1c7f38-bff3-4f29-87b8-e3b95a404729
-- title:
--   Meyerson's algorithm with a uniform opening cost, its batched execution, and the uniform certificates
-- statement:
--   This file fixes the algorithm and the certificates of §3 (uniform opening costs).
--
--   **Meyerson's rule.** All sites have the same opening cost $f>0$. A client $v$ at site $x$, arriving when the open set is $F_v$, draws a lottery value $U_v\in[0,1]$ and opens a facility at $x$ exactly when
--
--   $$
--   f\,U_v\le d(x,F_v),
--   $$
--
--   with $d(x,\emptyset)=\infty$; so it opens with probability $p_v=\min\{1,d(v,F_v)/f\}$ and the first client opens surely. The new open set is $F_v^+=F_v\cup\{x\}$ if it opens and $F_v^+=F_v$ otherwise, and $\mathrm{cost}(v)$ is $f$ (if a new facility was opened) plus the connection distance $d(x,F_v^+)$.
--
--   **Execution and expectation.** On a batched instance, the clients are processed one at a time in the published batched random order (a uniform order of the $B$ batches and an independent uniform shuffle inside each batch), starting from no open facility. $F_v$ and $\mathrm{cost}(v)$ are read off this run, and $\mathrm{ALG}(C)=\sum_{v\in C}\mathrm{cost}(v)$. Expectations average over the $B!$ batch orders, the $n!$ client permutations, and i.i.d. uniform lotteries, all independent.
--
--   **Certificates (3.1).** For a center $c$ and a set $C$ of clients, client $v$ has key $Z_v=d(c,v)+fU_v$ and is *certified* when
--
--   $$
--   Z_v\le\min\{f,d(c,F_v)\}.
--   $$
--
--   $Y_v=f\,\mathbf 1\{v\text{ certified}\}$, $C_b=C\cap b$, $W_b=f\,\mathbf 1\{\exists v\in C_b\text{ certified}\}$, and $K_C$ is the number of batches containing a certified client of $C$.
--
--   **The two-copy algorithm.** On a batch sequence, the single-copy algorithm shuffles each arriving batch uniformly and processes its clients by Meyerson's rule; the algorithm of Theorem 3.1 runs one copy on the singleton batches and an independent copy on the nonsingleton batches, and its cost is the sum of the two copies' costs.
--
--   These objects are shared by Lemmas 3.2–3.6 and Theorem 3.1.
--
--   **Formalization Note** Distances to sets and costs take values in $[0,\infty]$; the lottery law is Lebesgue measure on $[0,1]$; the batch order, in-batch shuffle and two-copy combination are the published definitions of the base mission.
-- source:
--   Fabrizio Grandoni, Stefano Leonardi, Matteo Russo, Metric Facility Location under Batched Random Order, STOC 2027 submission #212 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/212.pdf (source.pdf sha256 2e976c4133df9baa0c32b4cd22b6e370c2c4611dfe4d4dec02ceb01bd7a0dc94), §2 p. 7 (notation, batched random order), §3.1 p. 9 (Meyerson's rule, coupling f U_v ≤ d(v,F_v), certificate (3.1), Y_v, W_b, W_C, K_C), Observation 2.2 p. 8 (two copies)

import Mathlib
import Definitions.Def_BatchedFacilityLocation_Nonuniform_Batched

open MeasureTheory
open scoped ENNReal

namespace BatchedFacilityLocation.Nonuniform.Supplement

noncomputable section

open Classical

/-! # Meyerson's algorithm with a uniform opening cost, and its certificates

Grandoni–Leonardi–Russo, *Metric Facility Location under Batched Random Order*,
STOC 2027 submission #212, §2 (p. 7) and §3.1 (p. 9).

All sites have the same opening cost `f > 0`. On the arrival of a client `v` at site `x`,
Meyerson's algorithm opens a facility at `x` with probability `p_v = min {1, d(v, F_v)/f}`,
realized by a lottery `U_v ~ Unif[0,1]`: it opens exactly when `f U_v ≤ d(v, F_v)`. The
first client opens surely (`d(v, ∅) = ∞`). The client is connected to a closest facility of
the resulting open set `F_v^+`. -/

variable {S : Type*} [Fintype S] [MetricSpace S]

/-! ## One step of Meyerson's rule with common cost `f` -/

/-- The opening test of Meyerson's algorithm (p. 9): a client at site `x`, facing the pre-client
open set `F`, with lottery value `u`, opens a facility at `x` exactly when `f u ≤ d(x, F)`
(with `d(x, ∅) = ∞`). -/
def uOpens (f : ℝ) (F : Finset S) (x : S) (u : ℝ) : Prop :=
  ENNReal.ofReal (f * u) ≤ dset x F

/-- `F_v^+`: the open set after processing the client. -/
def uFplus (f : ℝ) (F : Finset S) (x : S) (u : ℝ) : Finset S :=
  if uOpens f F x u then insert x F else F

/-- `cost(v)`: the opening cost `f` if a new facility is opened at `x`, plus the connection
distance `d(x, F_v^+)` to a closest open facility. -/
def uStepCost (f : ℝ) (F : Finset S) (x : S) (u : ℝ) : ℝ≥0∞ :=
  (if uOpens f F x u ∧ x ∉ F then ENNReal.ofReal f else 0) + dset x (uFplus f F x u)

/-! ## Sequential execution -/

/-- Process the clients of a list one at a time, in list order; client `i` is at site `site i`
and uses lottery value `lot i`. The state records, for every processed client, the open set
`F_v` just before it and its cost. -/
def runFromU {ι : Type*} [DecidableEq ι] (f : ℝ) (site : ι → S) (lot : ι → ℝ) :
    List ι → RunState ι S → RunState ι S
  | [], st => st
  | i :: rest, st =>
      runFromU f site lot rest
        { F := uFplus f st.F (site i) (lot i)
          pre := Function.update st.pre i st.F
          cost := Function.update st.cost i (uStepCost f st.F (site i) (lot i)) }

/-- The execution of Meyerson's uniform-cost algorithm from the empty open set. -/
def runU {ι : Type*} [DecidableEq ι] (f : ℝ) (site : ι → S) (lot : ι → ℝ) (ord : List ι) :
    RunState ι S :=
  runFromU f site lot ord ⟨∅, fun _ => ∅, fun _ => 0⟩

/-! ## The single-copy execution on an indexed instance

The processing order is the published `order I σ τ`: batches in the order given by the uniform
batch permutation `σ`, and inside each batch the uniform in-batch shuffle induced by `τ`. Client
`i` uses lottery `U i`. -/

/-- The single-copy execution of the uniform algorithm on instance `I`. -/
def runIU (f : ℝ) (I : Instance S) (σ : Equiv.Perm (Fin I.B)) (τ : Equiv.Perm (Fin I.n))
    (U : Fin I.n → ℝ) : RunState (Fin I.n) S :=
  runU f I.loc U (order I σ τ)

/-- `F_v`: the open set just before client `i` is processed. -/
def FpreU (f : ℝ) (I : Instance S) (σ : Equiv.Perm (Fin I.B)) (τ : Equiv.Perm (Fin I.n))
    (U : Fin I.n → ℝ) (i : Fin I.n) : Finset S :=
  (runIU f I σ τ U).pre i

/-- `cost(v)` of client `i` in the single-copy execution. -/
def costU (f : ℝ) (I : Instance S) (σ : Equiv.Perm (Fin I.B)) (τ : Equiv.Perm (Fin I.n))
    (U : Fin I.n → ℝ) (i : Fin I.n) : ℝ≥0∞ :=
  (runIU f I σ τ U).cost i

/-- `ALG(C) = Σ_{v ∈ C} cost(v)` for the single-copy uniform algorithm. -/
def ALGCU (f : ℝ) (I : Instance S) (C : Finset (Fin I.n)) (σ : Equiv.Perm (Fin I.B))
    (τ : Equiv.Perm (Fin I.n)) (U : Fin I.n → ℝ) : ℝ≥0∞ :=
  ∑ i ∈ C, costU f I σ τ U i

/-- Expectation over the arrival law and the lotteries: `σ` uniform on the `B!` batch orders,
`τ` uniform on the `n!` client permutations (inducing independent uniform in-batch shuffles),
and the lotteries `U_v` i.i.d. uniform on `[0,1]`, all independent (p. 7, p. 9). -/
def ExU (I : Instance S)
    (X : Equiv.Perm (Fin I.B) → Equiv.Perm (Fin I.n) → (Fin I.n → ℝ) → ℝ≥0∞) : ℝ≥0∞ :=
  ((I.B.factorial : ℝ≥0∞) * (I.n.factorial : ℝ≥0∞))⁻¹ *
    ∑ σ : Equiv.Perm (Fin I.B), ∑ τ : Equiv.Perm (Fin I.n),
      ∫⁻ U, X σ τ U ∂(Measure.pi fun _ : Fin I.n => unif01)

/-! ## Certificates (§3.1, p. 9, eq. (3.1))

Fix a center `c` and a set `C` of clients. Client `v` gets the key `Z_v = d(c, v) + f U_v` and is
*certified* when `Z_v ≤ min {f, d(c, F_v)}`. -/

/-- The key `Z_v = d(c, v) + f U_v` of client `i`. -/
def keyU (f : ℝ) (I : Instance S) (c : S) (U : Fin I.n → ℝ) (i : Fin I.n) : ℝ≥0∞ :=
  ENNReal.ofReal (dist c (I.loc i)) + ENNReal.ofReal (f * U i)

/-- Client `i` is certified (3.1): `Z_v ≤ min {f, d(c, F_v)}` (threshold `f` when `F_v = ∅`). -/
def certifiedU (f : ℝ) (I : Instance S) (c : S) (σ : Equiv.Perm (Fin I.B))
    (τ : Equiv.Perm (Fin I.n)) (U : Fin I.n → ℝ) (i : Fin I.n) : Prop :=
  keyU f I c U i ≤ min (ENNReal.ofReal f) (dset c (FpreU f I σ τ U i))

/-- `Y_v = f · 1{v is certified}`. -/
def YU (f : ℝ) (I : Instance S) (c : S) (σ : Equiv.Perm (Fin I.B))
    (τ : Equiv.Perm (Fin I.n)) (U : Fin I.n → ℝ) (i : Fin I.n) : ℝ≥0∞ :=
  if certifiedU f I c σ τ U i then ENNReal.ofReal f else 0

/-- `C_b = C ∩ b`: the clients of `C` in batch `b`. -/
def Cbatch (I : Instance S) (C : Finset (Fin I.n)) (b : Fin I.B) : Finset (Fin I.n) :=
  C.filter (fun i => I.batch i = b)

/-- `W_b = f · 1{∃ v ∈ C_b, v is certified}`. -/
def WbU (f : ℝ) (I : Instance S) (c : S) (C : Finset (Fin I.n)) (b : Fin I.B)
    (σ : Equiv.Perm (Fin I.B)) (τ : Equiv.Perm (Fin I.n)) (U : Fin I.n → ℝ) : ℝ≥0∞ :=
  if ∃ i ∈ Cbatch I C b, certifiedU f I c σ τ U i then ENNReal.ofReal f else 0

/-- `K_C = W_C / f`: the number of batches containing a certified client of `C`. -/
def KCU (f : ℝ) (I : Instance S) (c : S) (C : Finset (Fin I.n))
    (σ : Equiv.Perm (Fin I.B)) (τ : Equiv.Perm (Fin I.n)) (U : Fin I.n → ℝ) : ℝ≥0∞ :=
  ((Finset.univ.filter (fun b : Fin I.B =>
      ∃ i ∈ Cbatch I C b, certifiedU f I c σ τ U i)).card : ℝ≥0∞)

/-! ## The uniform algorithm on a batch sequence, and the two-copy algorithm (§3.1, p. 9) -/

/-- Expected cost of Meyerson's uniform algorithm processing the client sites `seq` one at a
time, in this order, from the empty open set, with i.i.d. uniform lotteries on `[0,1]`. -/
def meySeqCost (f : ℝ) (seq : List S) : ℝ≥0∞ :=
  ∫⁻ U, ∑ k : Fin seq.length,
      (runU f (fun k : Fin seq.length => seq.get k) U (List.finRange seq.length)).cost k
    ∂(Measure.pi fun _ : Fin seq.length => unif01)

/-- The single-copy batched uniform algorithm: each arriving batch is shuffled uniformly at
random and its clients are processed one at a time by Meyerson's rule. `meyAlg f L` is its
expected cost given the batch sequence `L`. -/
def meyAlg (f : ℝ) (L : List (List S)) : ℝ≥0∞ :=
  shuffleAvg L (meySeqCost f)

/-- The algorithm of Theorem 3.1: two parallel copies of Meyerson's uniform algorithm, one on
the singleton batches and one on the nonsingleton batches (published `combine`, cost = sum of
the copies' costs). -/
def meyComb (f : ℝ) (L : List (List S)) : ℝ≥0∞ :=
  combine (meyAlg f) (meyAlg f) L

end

end BatchedFacilityLocation.Nonuniform.Supplement


