-- Prove2me | Definitions.Def_DynOracleConn_PPHP
-- name    : DynOracleConn_PPHP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:48:11.680208+00:00
-- url     : https://prove2.me/theorems/7aab4764-0bb1-4bd4-b6cb-fef1358b03e8
-- title:
--   Prefix Parity with Hidden Permutation: instances, oracle, hits, stream algorithms
-- statement:
--   An instance of **Prefix Parity with Hidden Permutation** is $X=(\pi,z)$ with $\pi$ a bijection of $[d]$ (from items to slots) and $z\in\{0,1\}^d$ (the switch bits). The oracle $P_X(i,j)$ returns $z_j$ if $\pi(i)=j$ and $\bot$ otherwise. A probe with $\pi(i)=j$ is a **hit**. The query for item $i$ must be answered by
--
--   $$y_i=\bigoplus_{k\le\pi(i)} z_k.$$
--
--   A **stream algorithm** has a state set $S$, a preprocessing map $X\mapsto\mathcal M(\pi,z)\in S$, and for each epoch a probe tree against $P_X$ returning the new state and an output bit. The event $\mathrm{correct}_{\mathrm{total}}$ says that every output is right, and $L_{\mathrm{total}}$ is the total number of probes. A **randomized** stream algorithm is a probability space of stream algorithms with measurable runs.
--
--   **Formalization Note** Items, slots and epochs are 0-based, so the paper's $k\in[\pi(i)]$ becomes $k\le\pi(i)$. $\bot$ is `none`. `numHits` counts distinct hit pairs, which are distinct items and distinct slots.
-- source:
--   Aryanfard, Henzinger, Kuszmaul, Nogler, Vassilevska Williams, Connectivity in a New Bounded-Space Dynamic Model, STOC 2027 submission (manuscript sha256 e9b19480…), §3, box on p.19

import Mathlib
import Definitions.Def_DynOracleConn_ProbeTree

namespace DynOracleConn

/-!
# Prefix Parity with Hidden Permutation (PPHP)

Aryanfard, Henzinger, Kuszmaul, Nogler, Vassilevska Williams, *Connectivity in a New Bounded-Space
Dynamic Model*, STOC 2027 submission (manuscript sha256 e9b19480…), §3, box on p.19:

"Instance. A bijection π: [d] → [d] and a vector z ∈ {0, 1}^d, both uniformly random and
independent. … Preprocessing. The algorithm sees X := (π, z) once and stores a B-bit string
𝓜(π, z). Queries. In the i-th query (called epoch), where i ∈ [N], the algorithm receives
Iᵢ ∼ Unif([d]) and must output y_{Iᵢ} = ⊕_{k=1}^{π(Iᵢ)} z_k. While processing queries, we have B bits
of space and access to the following oracle: given i, j ∈ [d], return P_X(i, j), which is zⱼ if
π(i) = j and ⊥ otherwise. A probe P_X(i, j) with π(i) = j is called a hit. The cost of an algorithm
is the number of oracle probes it makes. The algorithm succeeds if it answers all N queries
correctly."

**Formalization Note.**
1. Items, slots and epochs are 0-based: `[d]` is `Fin d`, and `y_i = ⊕_{k ≤ π i} z_k`. Bits are
   `Bool` (`true` = 1); `⊥` is `none`.
2. `hits t X` is the set of distinct hit pairs `(i, π i)` probed along the run of `t`; distinct hits
   are distinct items and distinct slots. `hitSlots` lists their slots as natural numbers.
3. A stream algorithm has a state type `S` (the B bits, as `Fintype.card S ≤ 2 ^ B` where used),
   a preprocessing map `pre : PPHPInst d → S`, and for the `k`-th epoch a probe tree with unlimited
   temporary memory whose leaf gives the new state and the output bit.
4. A randomized PPHP algorithm is a probability space of stream algorithms with a common state
   type; `PPHPMeasurableRuns` asks every transcript preimage to be measurable.
-/

open MeasureTheory

/-- A PPHP instance `X = (π, z)`: the bijection from items to slots and the switch bits. -/
abbrev PPHPInst (d : ℕ) : Type := Equiv.Perm (Fin d) × (Fin d → Bool)

/-- The PPHP oracle `P_X(i, j)`: `some z_j` if `π i = j`, and `none` (⊥) otherwise. -/
def pOracle {d : ℕ} (X : PPHPInst d) : Fin d × Fin d → Option Bool :=
  fun p => if X.1 p.1 = p.2 then some (X.2 p.2) else none

/-- The parity (xor) of the bits `z j` over the slots `j ∈ P`. -/
def parity {d : ℕ} (z : Fin d → Bool) (P : Finset (Fin d)) : Bool :=
  decide (Odd (P.filter (fun j => z j = true)).card)

/-- The correct answer to a query of item `i`: `y_i = ⊕_{k ≤ π i} z_k` (0-based). -/
def yval {d : ℕ} (X : PPHPInst d) (i : Fin d) : Bool :=
  parity X.2 (Finset.univ.filter (fun k => k ≤ X.1 i))

/-- Probe trees against the PPHP oracle. -/
abbrev PPHPTree (d : ℕ) (R : Type) : Type := ProbeTree (Fin d × Fin d) (Option Bool) R

/-- The distinct hit pairs `(i, j)` (with `π i = j`) probed along the run of `t` on instance `X`. -/
def hits {d : ℕ} {R : Type} (t : PPHPTree d R) (X : PPHPInst d) : Finset (Fin d × Fin d) :=
  (((t.transcript (pOracle X)).filter (fun p => p.2.isSome)).map Prod.fst).toFinset

/-- The number `H` of distinct hits of the run of `t` on `X`. -/
def numHits {d : ℕ} {R : Type} (t : PPHPTree d R) (X : PPHPInst d) : ℕ := (hits t X).card

/-- The slots (as natural numbers) hit along the run of `t` on `X`. -/
def hitSlots {d : ℕ} {R : Type} (t : PPHPTree d R) (X : PPHPInst d) : Finset ℕ :=
  (hits t X).image (fun p => p.2.val)

/-- A deterministic PPHP stream algorithm with state type `S`. -/
structure PPHPAlg (d : ℕ) (S : Type) : Type where
  /-- Preprocessing: the stored state `𝓜(π, z)`. -/
  pre : PPHPInst d → S
  /-- The probe tree answering the `k`-th epoch (0-based) for queried item `i` from state `st`;
  its leaf gives the new state and the output bit. -/
  step : ℕ → S → Fin d → PPHPTree d (S × Bool)

namespace PPHPAlg

variable {d : ℕ} {S : Type}

/-- The run from epoch index `k` and state `st` on the remaining queries: per epoch, the probes
with their replies and the output bit. -/
def runFrom (A : PPHPAlg d S) (X : PPHPInst d) :
    ℕ → S → List (Fin d) → List (List ((Fin d × Fin d) × Option Bool) × Bool)
  | _, _, [] => []
  | k, st, i :: rest =>
      ((A.step k st i).transcript (pOracle X), ((A.step k st i).run (pOracle X)).2) ::
        runFrom A X (k + 1) ((A.step k st i).run (pOracle X)).1 rest

/-- The run of `A` on instance `X` and query sequence `ℐ`, starting from `A.pre X`. -/
def transcript (A : PPHPAlg d S) (X : PPHPInst d) (ℐ : List (Fin d)) :
    List (List ((Fin d × Fin d) × Option Bool) × Bool) :=
  A.runFrom X 0 (A.pre X) ℐ

/-- `correct_total`: every output equals `y_{I_i}`. -/
def correctTotal (A : PPHPAlg d S) (X : PPHPInst d) (ℐ : List (Fin d)) : Prop :=
  (A.transcript X ℐ).map Prod.snd = ℐ.map (yval X)

/-- `L_total`: the total number of oracle probes over all epochs. -/
def Ltotal (A : PPHPAlg d S) (X : PPHPInst d) (ℐ : List (Fin d)) : ℕ :=
  ((A.transcript X ℐ).map (fun p => p.1.length)).sum

end PPHPAlg

/-- A randomized PPHP algorithm: a probability space of stream algorithms with state type `S`. -/
structure RandPPHPAlg (d : ℕ) (S : Type) : Type 1 where
  /-- The randomness (e.g. the random tape `R`). -/
  Ω : Type
  [measΩ : MeasurableSpace Ω]
  /-- Its law. -/
  μ : Measure Ω
  [isProb : IsProbabilityMeasure μ]
  /-- The deterministic algorithm given the outcome `ω`. -/
  alg : Ω → PPHPAlg d S

attribute [instance] RandPPHPAlg.measΩ RandPPHPAlg.isProb

/-- For every instance and query sequence, the transcript is a measurable function of the
randomness: every set of transcripts has a measurable preimage. -/
def PPHPMeasurableRuns {d : ℕ} {S : Type} (A : RandPPHPAlg d S) : Prop :=
  ∀ (X : PPHPInst d) (ℐ : List (Fin d))
    (P : Set (List (List ((Fin d × Fin d) × Option Bool) × Bool))),
    MeasurableSet ((fun ω => (A.alg ω).transcript X ℐ) ⁻¹' P)

end DynOracleConn


