-- Prove2me | Definitions.Def_SubmodMDP_Policies_Supplement_Pipeline
-- name    : SubmodMDP_Policies_Supplement_Pipeline
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:29:54.225756+00:00
-- url     : https://prove2.me/theorems/8ad19848-f5c5-4a9a-83cd-68f197396105
-- title:
--   LP preprocessing contract and independent rounding pipeline
-- statement:
--   For the reduced graph, use the published constrained round-or-cut interface of Lemma 7 with fixed accuracy $\delta=1/2$, one singleton length row, and the clipped budget. The preprocessing contract requires an actual word-charged RAM program to halt within its stated cost, return a feasible point on every outcome, and satisfy Lemma 7's comparison guarantee with probability at least $1-N^{-2}$, where $N$ is the reduced vertex count.
--
--   The full output law is the preprocessing law followed by an independent RRR sample and reconstruction:
--
--   $$\mathcal L(W)=\mathbb E_{x\sim\mathrm{Pre}}\bigl[\mathcal L(\operatorname{reconstruct}(P)),\ P\sim\mathrm{RRR}(x)\bigr].$$
--
--   There is no conditioning on reward success and no rejection of a long sample. Theorem 1 requires a RAM implementation of this entire law on the original oracle, charges all stages to its runtime, and states both the exact transfer factor and the advertised asymptotic reward guarantee. Failure and malformed outputs are represented explicitly, and are excluded from the output support by that theorem.
-- source:
--   Lars Rohwedder, Rico Zenklusen, STOC 2027 submission #658 (October 2026), §2.4, Lemma 7 and proof of Theorem 1, pp. 13–14 (PDF pp. 14–15)

import Mathlib
import Definitions.Def_SubmodMDP_Policies_Supplement_Reduction

namespace SubmodMDP.Policies.Supplement

noncomputable section
open Classical

/-- Input to the published constrained round-or-cut interface, with the singleton length row.
The full oracle is not input data: it is accessed only through query instructions. -/
def preInput {n : ℕ} (I : Ori n) (d r : ℕ) (w : Fin n → Fin n → ℕ) (C : ℕ) : List ℤ :=
  let H := d ^ r
  encGraph (reduced I H) ++ [(d : ℤ), (r : ℤ)] ++
    encDb (reduced I H).N r 1 (lengthRow I H w) (fun _ => (cappedBudget I H w C : ℤ))

def preTime {n : ℕ} (I : Ori n) (d r c : ℕ) (w : Fin n → Fin n → ℕ) (C : ℕ) : ℕ :=
  let H := d ^ r
  ((reduced I H).N + 1) ^ (c * (r + 1)) *
    (sizeDb (reduced I H).N r 1 (lengthRow I H w)
      (fun _ => (cappedBudget I H w C : ℤ)) + 1) ^ c

def preLaw {n : ℕ} (A : Program) (c : ℕ) (I : Ori n) (d r : ℕ)
    (w : Fin n → Fin n → ℕ) (C : ℕ) (f : Finset (Fin n) → ℚ) : PMF (Option (List ℤ)) :=
  let O : Oracle := ⟨(reduced I (d ^ r)).N, redReward I (d ^ r) f⟩
  outLaw A O (wordLen (preInput I d r w C) O) (preInput I d r w C) (preTime I d r c w C)

/-- The contract of the existing Lemma 7 at the fixed accuracy δ=1/2, on the reduced instance.
Every preprocessing outcome is feasible, including outcomes where the reward test fails.
The success event compares against every feasible comparison distribution, as in Lemma 7.
This is a property of an actual RAM program, not a supplied free running-time predicate. -/
def Preprocesses {n : ℕ} (A : Program) (c : ℕ) (I : Ori n) (d r : ℕ)
    (w : Fin n → Fin n → ℕ) (C : ℕ) (f : Finset (Fin n) → ℚ) : Prop :=
  let H := d ^ r
  let G := reduced I H
  let D := lengthRow I H w
  let b := fun (_ : Fin 1) => (cappedBudget I H w C : ℤ)
  let O : Oracle := ⟨G.N, redReward I H f⟩
  let inp := preInput I d r w C
  let μ := preLaw A c I d r w C f
  HaltsWithin A O (wordLen inp O) inp (preTime I d r c w C) ∧
  (∀ σ, some σ ∈ μ.support → ∃ x, decodePoint G.N (r + 1) σ = some x ∧
    InQ G r (fun X => (x X : ℝ)) ∧ SatDb r 1 D b (fun X => (x X : ℝ))) ∧
  ENNReal.ofReal (1 - (G.N : ℝ) ^ (-2 : ℝ)) ≤
    μ.toOuterMeasure {o | ∃ σ x, o = some σ ∧ decodePoint G.N (r + 1) σ = some x ∧
      ∀ Od : PMF (List (Fin G.N)), FeasibleDist G r 1 D b Od →
        (1 / 2 : ℝ) / (((d : ℝ) - 1) * ((r : ℝ) + 1)) *
          pmfExp Od (fun P => (redReward I H f P.toFinset : ℝ)) ≤
            pmfExp (RRR G d r (fun X => (x X : ℝ))) (fOpt (redReward I H f))}

/-- The complete LP-based sampling pipeline, with an independent RRR draw after preprocessing.
There is no conditioning on high reward and no rejection of long walks. -/
def pipelineLaw {n : ℕ} (A : Program) (c : ℕ) (I : Ori n) (d r : ℕ)
    (w : Fin n → Fin n → ℕ) (C : ℕ) (f : Finset (Fin n) → ℚ) :
    PMF (Option (List (Fin n))) :=
  let H := d ^ r
  let G := reduced I H
  (preLaw A c I d r w C f).bind (fun o =>
    match o.bind (decodePoint G.N (r + 1)) with
    | none => PMF.pure none
    | some x => (RRR G d r (fun X => (x X : ℝ))).map
      (fun p => p.bind (reconstruct I H w)))

/-- Decode a RAM output law into optional walks. Malformed output is failure, never a walk. -/
def walkLaw (n : ℕ) (μ : PMF (Option (List ℤ))) : PMF (Option (List (Fin n))) :=
  μ.map (fun o => o.bind (decodeWalk n))

/-- Full finite-output specification for an LP pipeline on a general graph. Both the exact
proof transfer factor and the advertised ratio are retained. All preprocessing, construction,
oracle simulation, final RRR sampling, and reconstruction are charged to the final RAM run. -/
def LPGuarantee {n : ℕ} (Alg Pre : Program) (cPre : ℕ) (I : Ori n) (d r : ℕ)
    (w : Fin n → Fin n → ℕ) (C B : ℕ) (f : Finset (Fin n) → ℚ) (ratio : ℝ) : Prop :=
  let O : Oracle := ⟨n, f⟩
  let inp := encWeighted I w C
  let ν := walkLaw n (outLaw Alg O (wordLen inp O) inp B)
  let N := (reduced I (d ^ r)).N
  let OPT := (optimum I f (fun W => walkLength w W ≤ C) : ℝ)
  HaltsWithin Alg O (wordLen inp O) inp B ∧
  Preprocesses Pre cPre I d r w C f ∧
  ν = pipelineLaw Pre cPre I d r w C f ∧
  (∀ o ∈ ν.support, ∃ W, o = some W ∧ Walk I.graph I.s I.t W) ∧
  pmfExp ν (fun o => match o with | none => 0 | some W => (walkLength w W : ℝ)) ≤ (C : ℝ) ∧
  (1 - (N : ℝ) ^ (-2 : ℝ)) * (1 / 2 : ℝ) /
    (((d : ℝ) - 1) * ((r : ℝ) + 1)) * OPT ≤ pmfExp ν (fOpt f) ∧
  OPT / ratio ≤ pmfExp ν (fOpt f)

end
end SubmodMDP.Policies.Supplement


