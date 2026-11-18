-- Prove2me | Definitions.Def_KoanaKPaths_TapeSampling
-- name    : KoanaKPaths_TapeSampling
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T01:45:04.702557+00:00
-- url     : https://prove2.me/theorems/0c6767a1-ea36-4498-98cb-b0582953c5e8
-- title:
--   Explicit independent sign blocks on a finite random tape
-- statement:
--   One trial uses independent bits indexed by vertex-label coordinates, the first sketch matrix, and the later sketch matrices. Its number of bits at width $k$ is
--
--   $$r=nk+kn+(k-1)k^2n.$$
--
--   Explicit bijections between finite sums and products of index sets identify a block of $r$ bits with all of these signs. Consecutive blocks form the trials and groups of the amplified estimate. The prescribed prefix length is
--
--   $$S=(2b+1)\,1024k^3 4^a\,r.$$
--
--   The decoder reads this prefix of the supplied tape and never takes its total length as an input. The graph input is encoded with the discrete controls $a,b$ directly. The intended output is the amplified written fraction, with the empty graph returning $0/1$.
--
--   These data specify deterministic bit indexing and the intended rational output. Correct uniform marginals and efficient machine evaluation are separate proof obligations.
-- source:
--   Tomohiro Koana, Approximate Counting of k-Paths in O*(2^k) Time, STOC 2027 submission #953, printed pp. 8–9 / PDF pp. 9–10, Section 3.2 (sampling the estimator, integer-size bound and amplification), and Section 4.1 (directed walks). Explicit fair-bit refinement uses the mission computation model in Definitions.Def_HypergraphUnreliability_FPRAS_Machine and the declared timeBudget in Definitions.Def_KoanaKPaths_Main_Inputs. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/953.pdf

import Definitions.Def_KoanaKPaths_GraphEstimator
import Definitions.Def_KoanaKPaths_Main_Inputs

set_option synthInstance.maxSize 4096
namespace KoanaKPaths.Main

/-- Coordinate positions of all independent fair signs in one width-k trial. -/
abbrev TrialIndex (n k : ℕ) :=
  (Fin n × Fin k) ⊕ ((Fin k × Fin n) ⊕ (Fin (k-1) × Fin k × (Fin k × Fin n)))

def trialBits (n k : ℕ) : ℕ := n*k+(k*n+(k-1)*(k*(k*n)))

/-- Explicit row-major indexing, using only sums and products of finite ordinals. -/
def trialIndexEquiv (n k : ℕ) : TrialIndex n k ≃ Fin (trialBits n k) :=
  (Equiv.sumCongr finProdFinEquiv
    ((Equiv.sumCongr finProdFinEquiv
      ((Equiv.prodCongr (Equiv.refl (Fin (k-1)))
        ((Equiv.prodCongr (Equiv.refl (Fin k)) finProdFinEquiv).trans finProdFinEquiv)).trans
          finProdFinEquiv)).trans finSumFinEquiv)).trans finSumFinEquiv

/-- Decode one block of fair bits into its labels and sketch matrices. -/
def trialEquiv (n k : ℕ) :
    (Fin (trialBits n k) → Bool) ≃ Labels n k × SketchSigns n k k :=
  (Equiv.arrowCongr (trialIndexEquiv n k).symm (Equiv.refl Bool)).trans
    ((Equiv.sumArrowEquivProdArrow _ _ Bool).trans
      (Equiv.prodCongr (Equiv.curry (Fin n) (Fin k) Bool)
        ((Equiv.sumArrowEquivProdArrow _ _ Bool).trans
          (Equiv.prodCongr (Equiv.curry (Fin k) (Fin n) Bool)
            ((Equiv.curry (Fin (k-1)) (Fin k × (Fin k × Fin n)) Bool).trans
              (Equiv.piCongrRight (fun _ => Equiv.curry (Fin k) (Fin k × Fin n) Bool)))))))

def sampleBits (n k a b : ℕ) : ℕ := (2*b+1)*groupTrials k a*trialBits n k

/-- Decode consecutive, nonoverlapping trial blocks into independent groups. -/
def samplesEquiv (n k a b : ℕ) :
    (Fin (sampleBits n k a b) → Bool) ≃
      (Fin (2*b+1) → Fin (groupTrials k a) → Labels n k × SketchSigns n k k) :=
  (Equiv.arrowCongr (finProdFinEquiv (m := (2*b+1)*groupTrials k a) (n := trialBits n k)).symm
      (Equiv.refl Bool)).trans
    ((Equiv.curry _ _ Bool).trans
      ((Equiv.piCongrRight (fun _ => trialEquiv n k)).trans
        ((Equiv.arrowCongr (finProdFinEquiv (m := 2*b+1) (n := groupTrials k a)).symm
          (Equiv.refl _)).trans (Equiv.curry _ _ _))))

/-- Only this fixed prefix of the tape is used; its total length is never an input parameter. -/
def tapeSamples (n k a b : ℕ) (tape : List Bool) :=
  samplesEquiv n k a b (fun j => tape.getD j.val false)

/-- Graph input with the two finite controls written explicitly. -/
def graphInputControls (n : ℕ) (arcs : List (Fin n × Fin n)) (k a b : ℕ) : List Bool :=
  HypergraphUnreliability.FPRAS.natCode n ++ HypergraphUnreliability.FPRAS.natCode k ++
    HypergraphUnreliability.FPRAS.natCode a ++ HypergraphUnreliability.FPRAS.natCode b ++
    HypergraphUnreliability.FPRAS.listCode
      (fun p : Fin n × Fin n => HypergraphUnreliability.FPRAS.natCode p.1.val ++
        HypergraphUnreliability.FPRAS.natCode p.2.val) arcs

/-- Intended written output on the supplied random tape. Empty graphs return zero directly. -/
noncomputable def tapeEstimate (n : ℕ) (arcs : List (Fin n × Fin n)) (k a b : ℕ) (tape : List Bool) :
    HypergraphUnreliability.FPRAS.Frac :=
  if n=0 then ⟨0,1⟩ else estimateFraction (walkTensor n arcs k) a b (tapeSamples n k a b tape)

end KoanaKPaths.Main


