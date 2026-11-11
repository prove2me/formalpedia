-- Prove2me | Definitions.Def_MaxCutMatrix2027_Upper_Algorithm
-- name    : MaxCutMatrix2027_Upper_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T12:48:00.91243+00:00
-- url     : https://prove2.me/theorems/6eb2f64e-93c0-40d5-a14f-039e58953c9c
-- title:
--   Algorithm 1 with bounded geometric sampling and explicit cut enumeration
-- statement:
--   Given $n$, $\varepsilon>0$, and one absolute coefficient $C$, set $s=\lceil C/\varepsilon^2\rceil$. The fixed RAM program first computes this integer. If $n\le s$, it records all vertices, queries every increasing pair, enumerates every cut, and returns the exact MAX-CUT value. Otherwise it generates selected vertices in increasing order from independent geometric gaps with parameter $s/n$. It stops at the first out-of-range position or the $(2s+1)$st selection. On overflow it halts with zero before any query.
--
--   For a retained sample $Q$ its output is
--   $$\widehat M=\frac{n^2}{s^2}\operatorname{MAXCUT}(G[Q]).$$
--   The denominator is the squared expected sample size. Every pair in $Q$ is queried once and stored in a random-access table. A binary array enumerates all assignments by carry propagation; each cut is counted from the table and compared with the best value. Even the empty sample enumerates its unique empty assignment. Finally the program computes the real rescaling through individual arithmetic instructions.
--
--   The finite random tape has $2s+1$ independent geometric entries, with the standard law of the number of failures before a success. The decoding of this tape, the graph-independent planned pair set, the exact mathematical output, the capped Bernoulli output, the initial RAM state, the executed state after $t$ transitions, and the actual termination-and-accuracy event are defined separately. Outside the sampled branch the geometric parameter is clipped only to totalize the unused law. Equivalence with Bernoulli sampling is a conclusion of the goal, not an assumption in these definitions.
--
--   This identifies both probability and resources with the same program under the paper's unit-cost geometric and real-arithmetic RAM convention. No bit-complexity guarantee is asserted.
-- source:
--   Songhua He, STOC 2027 submission #351 (October 2026), Algorithm 1, p.17; proof of Theorem 4.1, pp.27–28, p.17 (PDF p.17); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/351.pdf; PDF SHA-256 b38cd84079663d9e2eb7375d7bf1572d5dc7c2157cfaf90e175fd371a9503631

import Definitions.Def_MaxCutMatrix2027_Upper_MatrixModel
import Definitions.Def_MaxCutMatrix2027_Upper_RAM
import Mathlib.Probability.Distributions.Geometric

set_option autoImplicit false
open scoped BigOperators
open MeasureTheory

namespace MaxCutMatrix2027.Upper

/-! Algorithm 1 (p.17), geometric-gap implementation (p.28).
Nat registers: 0=n, 1=s, 2=k, 3=next, 4=candidate, 5=gap,
6=i,7=j,8=u,9=v,10=table address,11=temporary,12=cut mask,
13=enumeration finished flag,14=best,15=current,16=carry,17=temporary,18/19=bits,
20=table entry,21=constant 1,22=constant 2,23=2s,24=constant 0.
Real registers: 0=epsilon,1=C,2=epsilon² (then n²),3=C/epsilon²,
4=s (then s²),5=p,6=n,7=best,8=output (initially zero).
Memory banks: 0=selected vertices in increasing order, 1=queried adjacency
at address i*k+j for i<j, 2=binary cut labels. The binary increment uses
O(k) small-word operations rather than arithmetic on a 2^k-sized word.
-/

/-- A fixed finite program; it contains no input-dependent code or uncharged optimization. -/
noncomputable def canonicalProgram : List Command :=
  [.natConst 21 1, .natConst 22 2, .natConst 24 0,
   .realOp 2 .mul 0 0, .realOp 3 .div 1 2, .ceil 1 3,
   .natOp 23 .add 1 1,
   .branch (.le 0 1)
     [.natOp 2 .add 0 24, .natConst 6 0,
      .loop (.lt 6 2) [.store 0 6 6, .natOp 6 .add 6 21]]
     [.cast 4 1, .cast 6 0, .realOp 5 .div 4 6,
      .natConst 2 0, .natConst 3 0,
      .loop (.both (.lt 3 0) (.le 2 23))
        [.gap 5 5, .natOp 4 .add 3 5,
         .branch (.lt 4 0)
           [.store 0 2 4, .natOp 2 .add 2 21, .natOp 3 .add 4 21]
           [.natOp 3 .add 0 24]],
      .branch (.lt 23 2) [.halt 8] []],
   .natConst 6 0,
   .loop (.lt 6 2)
     [.natOp 7 .add 6 21,
      .loop (.lt 7 2)
        [.load 8 0 6, .load 9 0 7, .query 20 8 9,
         .natOp 10 .mul 6 2, .natOp 10 .add 10 7, .store 1 10 20,
         .natOp 7 .add 7 21],
      .natOp 6 .add 6 21],
   .natConst 13 0, .natConst 14 0,
   .loop (.ne 13 21)
     [.natConst 15 0, .natConst 6 0,
      .loop (.lt 6 2)
        [.load 18 2 6, .natOp 7 .add 6 21,
         .loop (.lt 7 2)
           [.load 19 2 7,
            .branch (.ne 18 19)
              [.natOp 10 .mul 6 2, .natOp 10 .add 10 7,
               .load 20 1 10, .natOp 15 .add 15 20] [],
            .natOp 7 .add 7 21],
         .natOp 6 .add 6 21],
      .natOp 14 .max 14 15,
      .natConst 6 0, .natConst 16 1,
      .loop (.both (.lt 6 2) (.ne 16 24))
        [.load 18 2 6,
         .branch (.ne 18 24)
           [.store 2 6 24, .natOp 6 .add 6 21]
           [.store 2 6 21, .natConst 16 0]],
      .branch (.ne 16 24) [.natConst 13 1] []],
   .cast 7 14,
   .branch (.le 0 1) [.halt 7]
     [.cast 6 0, .cast 4 1, .realOp 2 .mul 6 6, .realOp 4 .mul 4 4,
      .realOp 8 .mul 2 7, .realOp 8 .div 8 4, .halt 8]]

noncomputable def initialState (n : ℕ) (ε C : ℝ) : RAMState where
  control := canonicalProgram
  natReg := fun r => if r = 0 then n else 0
  realReg := fun r => if r = 0 then ε else if r = 1 then C else 0
  memory := fun _ _ => 0
  randomCursor := 0
  randomParameters := []
  queries := []
  output := none

noncomputable def sampleSize (C ε : ℝ) : ℕ := ⌈C / ε ^ 2⌉₊

/-- A pair query returns an adjacency bit. Invalid addresses are totalized, but the
resource/correctness specification requires every actual query to be a valid increasing pair. -/
noncomputable def graphOracle {n : ℕ} (G : SimpleGraph (Fin n)) (u v : ℕ) : Bool := by
  classical
  exact if hu : u < n then if hv : v < n then decide (G.Adj ⟨u, hu⟩ ⟨v, hv⟩) else false else false

/-- The geometric measure has parameter s/n only in the sampled branch. Clipping outside
[0,1] merely totalizes unused inputs. n≥2, s≥1 and n>s give exactly 0<s/n<1. -/
noncomputable def gapParameter (n s : ℕ) : unitInterval :=
  ⟨min 1 (max 0 ((s : ℝ) / n)), by constructor <;> simp⟩

/-- At most 2s+1 independent geometric gaps are ever needed. -/
noncomputable def gapLaw (n s : ℕ) : Measure (RandomTape (2 * s + 1)) :=
  Measure.pi (fun _ : Fin (2 * s + 1) => ProbabilityTheory.geometricMeasure (gapParameter n s))

/-- The first 2s+1 selected positions. This is a mathematical decoding of the tape,
not an instruction charged as a single RAM operation. The implementation generates them
incrementally, stopping at the first out-of-range position or at the (2s+1)st selection. -/
noncomputable def gapSet (n s : ℕ) (ω : RandomTape (2 * s + 1)) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => ∃ k : Fin (2 * s + 1),
    i.val + 1 = ∑ j : Fin (2 * s + 1), if j ≤ k then ω j + 1 else 0)

noncomputable def queryVertices (n s : ℕ) (ω : RandomTape (2 * s + 1)) : Finset (Fin n) :=
  if n ≤ s then Finset.univ else if (gapSet n s ω).card ≤ 2 * s then gapSet n s ω else ∅

/-- The query set is determined before any graph answers are available. -/
noncomputable def plannedPairs (n s : ℕ) (ω : RandomTape (2 * s + 1)) : Finset (ℕ × ℕ) := by
  classical
  exact ((queryVertices n s ω).product (queryVertices n s ω)).filter
    (fun e => e.1 < e.2) |>.image (fun e => (e.1.val, e.2.val))

noncomputable def algorithmEstimate {n : ℕ} (G : SimpleGraph (Fin n)) (s : ℕ)
    (ω : RandomTape (2 * s + 1)) : ℝ :=
  if n ≤ s then IIDMatchHard.maxCut G else
    if (gapSet n s ω).card > 2 * s then 0 else
      (n : ℝ) ^ 2 * inducedMaxCut G (gapSet n s ω) / (s : ℝ) ^ 2

/-- Returned value under the uncapped Bernoulli set, with the actual abort branch. -/
noncomputable def bernoulliEstimate {n : ℕ} (G : SimpleGraph (Fin n)) (s : ℕ)
    (Q : Finset (Fin n)) : ℝ :=
  if n ≤ s then IIDMatchHard.maxCut G else if Q.card > 2 * s then 0 else
    (n : ℝ) ^ 2 * inducedMaxCut G Q / (s : ℝ) ^ 2

/-- A genuine finite run of Algorithm 1, with transition-derived time and oracle trace. -/
noncomputable def execution {n : ℕ} (G : SimpleGraph (Fin n)) (ε C : ℝ)
    (ω : RandomTape (2 * sampleSize C ε + 1)) (t : ℕ) : RAMState :=
  ramRun (graphOracle G) ω (initialState n ε C) t

/-- Accuracy is an event of the actual RAM run, including termination. -/
noncomputable def successEvent {n : ℕ} (G : SimpleGraph (Fin n)) (ε C : ℝ) :
    Set (RandomTape (2 * sampleSize C ε + 1)) :=
  {ω | ∃ t z, (execution G ε C ω t).output = some z ∧
    |z - (IIDMatchHard.maxCut G : ℝ)| ≤ ε * (n : ℝ) ^ 2}

end MaxCutMatrix2027.Upper


