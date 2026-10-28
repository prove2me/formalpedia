-- Prove2me | Definitions.Def_OAIQ085D011
-- name    : OAIQ085D011
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T16:02:20.147606+00:00
-- url     : https://prove2.me/theorems/603778d1-6770-4098-913e-493a2e4563ae
-- title:
--   Definitions bundle OAIQ085D011 of the split of OpenAI, Constant-factor hardness of directed feedback vertex set (result family 102)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DirectedFeedback.main`, carved from OpenAI's openai/math development (OpenAI, *Constant-factor hardness of directed feedback vertex set (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 102 declarations of OpenAI's Lean: 72 definitions, 2 inductive types or structures, 9 instances and 19 theorems. The definitions and types are `OAI.DirectedFeedback.GraphPrinter.Family`, `OAI.DirectedFeedback.GraphPrinter.Family.bits`, `OAI.DirectedFeedback.GraphPrinter.Family.count`, `OAI.DirectedFeedback.GraphPrinter.Family.edgeBits`, `OAI.DirectedFeedback.GraphPrinter.Family.graph`, `OAI.DirectedFeedback.GraphPrinter.Family.inst`, `OAI.DirectedFeedback.GraphPrinter.Family.pairs`, `OAI.DirectedFeedback.Junta.IsBoolean`, `OAI.DirectedFeedback.Junta.OnCoordinates`, `OAI.DirectedFeedback.Junta.biasedInfluence`, `OAI.DirectedFeedback.Junta.error`, `OAI.DirectedFeedback.Junta.highInfluences`, `OAI.DirectedFeedback.Junta.influence`, `OAI.DirectedFeedback.Junta.lowDiff`, `OAI.DirectedFeedback.Junta.lowDiffCoeff`, `OAI.DirectedFeedback.Junta.pivotal`, `OAI.DirectedFeedback.Junta.project`, `OAI.DirectedFeedback.Junta.projectCoeff`, `OAI.DirectedFeedback.Junta.roundBoolean`, `OAI.DirectedFeedback.Junta.support`, `OAI.DirectedFeedback.Junta.totalInfluence`, `OAI.DirectedFeedback.JuntaSupport.coefficient`, `OAI.DirectedFeedback.LivePackets.Live`, `OAI.DirectedFeedback.LivePackets.project`, `OAI.DirectedFeedback.LocalPrinter.Family`, `OAI.DirectedFeedback.LocalPrinter.Family.Arc`, `OAI.DirectedFeedback.LocalPrinter.Family.deleted`, `OAI.DirectedFeedback.LocalPrinter.Family.value`, `OAI.DirectedFeedback.PacketLocality.localGame`, `OAI.DirectedFeedback.PacketSeeds.BigSeed`, `OAI.DirectedFeedback.PacketSeeds.CommonSeed`, `OAI.DirectedFeedback.PacketSeeds.CompareSeed`, `OAI.DirectedFeedback.PacketSeeds.FullSeed`, `OAI.DirectedFeedback.PacketSeeds.Seed`, `OAI.DirectedFeedback.PacketSeeds.SmallSeed`, `OAI.DirectedFeedback.PacketSeeds.bigLaw`, `OAI.DirectedFeedback.PacketSeeds.commonLaw`, `OAI.DirectedFeedback.PacketSeeds.compareLaw`, `OAI.DirectedFeedback.PacketSeeds.fill`, `OAI.DirectedFeedback.PacketSeeds.fillBig` and 34 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: [`DirectedFeedback_Main`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DirectedFeedback/Main.lean), [`DirectedFeedback_RankGraph_AllGraph`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DirectedFeedback/RankGraph/AllGraph.lean), [`DirectedFeedback_RankGraph_CellCount`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DirectedFeedback/RankGraph/CellCount.lean), [`DirectedFeedback_RankGraph_FailureEvent`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DirectedFeedback/RankGraph/FailureEvent.lean), [`DirectedFeedback_RankGraph_PacketLocality`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DirectedFeedback/RankGraph/PacketLocality.lean), [`DirectedFeedback_RankGraph_PrefixBit`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DirectedFeedback/RankGraph/PrefixBit.lean), [`DirectedFeedback_RankGraph_Rational`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DirectedFeedback/RankGraph/Rational.lean), [`DirectedFeedback_RankGraph_RoundBoolean`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DirectedFeedback/RankGraph/RoundBoolean.lean), [`DirectedFeedback_RankGraph_UnweightedIntegrated`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DirectedFeedback/RankGraph/UnweightedIntegrated.lean).
--
--   **Imports.** It imports the published bundle `Def_DirectedFeedback`; the bundles `OAIQ085D000`, `OAIQ085D004` and `OAIQ085D005` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ085D016` and `OAIQ085D017`.
-- source:
--   OpenAI, Constant-factor hardness of directed feedback vertex set (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Constant-factor-hardness-of-directed-feedback-vertex-set-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit adc7f12

import Mathlib
import Definitions.Def_DirectedFeedback
import Definitions.Def_OAIQ085D000
import Definitions.Def_OAIQ085D004
import Definitions.Def_OAIQ085D005

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_RankGraph_UnweightedIntegrated
attribute [-instance] _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace DirectedFeedback.RankGraph

variable (U V X Y : Type) (T N : ℕ)

instance instNonemptyDomain [Nonempty X] [Nonempty Y] (d : Tuple U V T) : Nonempty (Domain U V X Y T d) := by
  cases d with
  | inl d => rcases d with ⟨t, s⟩; exact inferInstanceAs (Nonempty (Fin t.val → X))
  | inr d => rcases d with ⟨t, s⟩; exact inferInstanceAs (Nonempty ((Fin t.val → X) × Y))

variable {U V X Y T N}

theorem arc_irrefl [Nonempty X] [Nonempty Y] (a : Rank U V X Y T N) : ¬Arc a a := by
  intro h
  exact (lt_irrefl _) (eval_arc (fun _ => Classical.choice ‹Nonempty X›)
    (fun _ => Classical.choice ‹Nonempty Y›) h)

end DirectedFeedback.RankGraph

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.TestGraph
open RankGraph
variable {U V X Y W C : Type} {T N : ℕ}

variable (wild : W → Wildcard (U := U) (V := V) (X := X) (Y := Y) (T := T) (N := N))
    (comp : C → Comparison (U := U) (V := V) (X := X) (Y := Y) (T := T) (N := N))

theorem arc_irrefl [Nonempty X] [Nonempty Y] (a : Vertex U V X Y W C T N) :
    ¬Arc wild comp a a := by
  intro h
  cases h with
  | rank h => exact RankGraph.arc_irrefl _ h

end DirectedFeedback.TestGraph

end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_RankGraph_CellCount
attribute [-instance] _root_.OAI.DFVSGames.Reduction.ActualGame.dualFintype _root_.OAI.DFVSGames.Reduction.ActualGame.mapFintype _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder _root_.OAI.DirectedFeedback.RankPackets.shapeFintype _root_.OAI.DirectedFeedback.RawFamily.eNonempty _root_.OAI.DirectedFeedback.RawFamily.wNonempty _root_.OAI.DirectedFeedback.StackDSL.Code.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical

noncomputable section
open scoped Classical

noncomputable section
open scoped Classical BigOperators

noncomputable section
open scoped BigOperators

namespace DirectedFeedback.Probability
open DirectedFeedback.SourceProbability FiniteDistribution

def andCoin (k : ℕ) : FiniteDistribution Bool :=
  (uniform (Fin k → Bool)).pushforward andBit

def dyadicLaw (I : Type*) [Fintype I] [DecidableEq I] (k : ℕ) :
    FiniteDistribution (I → Bool) := table (fun _ : I => andCoin k)

end DirectedFeedback.Probability

end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_RankGraph_FailureEvent
attribute [-instance] _root_.OAI.DFVSGames.Reduction.ActualGame.dualFintype _root_.OAI.DFVSGames.Reduction.ActualGame.mapFintype _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.RankPackets.shapeFintype _root_.OAI.DirectedFeedback.StackDSL.Code.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
open DirectedFeedback.SourceProbability
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators

noncomputable section
open scoped Classical BigOperators

noncomputable section
namespace DirectedFeedback.JuntaSupport

open scoped BigOperators
open Finset

def coefficient {I : Type*} [Fintype I] [DecidableEq I] (f : Cube I → ℝ) (s : Cube I) : ℝ :=
  𝔼 x, f x * walsh s x

end DirectedFeedback.JuntaSupport

namespace DirectedFeedback.Junta
open scoped BigOperators
open Finset DirectedFeedback.JuntaSupport DFVSMaxCut.BooleanFourthMoment
open DFVSMaxCut.Analytic

def influence {n : ℕ} (f : Cube (Fin n) → ℝ) (i : Fin n) : ℝ :=
  𝔼 x, (f x - f (Function.update x i (!x i))) ^ 2

def totalInfluence {n : ℕ} (f : Cube (Fin n) → ℝ) : ℝ := ∑ i, influence f i

def IsBoolean {n : ℕ} (f : Cube (Fin n) → ℝ) : Prop := ∀ x, f x = 0 ∨ f x = 1

def OnCoordinates {n : ℕ} (J : Finset (Fin n)) (f : Cube (Fin n) → ℝ) : Prop :=
  ∀ x y, (∀ i ∈ J, x i = y i) → f x = f y

def error {n : ℕ} (f g : Cube (Fin n) → ℝ) : ℝ :=
  𝔼 x, if f x = g x then 0 else 1

def pivotal {n : ℕ} (f : Cube (Fin n) → ℝ) (i : Fin n)
    (x : Cube (Fin n)) : ℝ := if f x = f (Function.update x i (!x i)) then 0 else 1

def lowDiffCoeff {n : ℕ} (f : Cube (Fin n) → ℝ) (K : ℕ) (i : Fin n)
    (s : Cube (Fin n)) : ℝ := if s i = true ∧ degree s ≤ K then coefficient f s else 0

def lowDiff {n : ℕ} (f : Cube (Fin n) → ℝ) (K : ℕ) (i : Fin n) :=
  polynomial (lowDiffCoeff f K i)

def support {n : ℕ} (s : Cube (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (fun i => s i = true)

def projectCoeff {n : ℕ} (J : Finset (Fin n)) (f : Cube (Fin n) → ℝ)
    (s : Cube (Fin n)) : ℝ := if support s ⊆ J then coefficient f s else 0

def project {n : ℕ} (J : Finset (Fin n)) (f : Cube (Fin n) → ℝ) :=
  polynomial (projectCoeff J f)

def highInfluences {n : ℕ} (f : Cube (Fin n) → ℝ) (τ : ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => τ ^ 2 < influence f i)

end DirectedFeedback.Junta
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_RankGraph_RoundBoolean
attribute [-instance] _root_.OAI.DFVSGames.Reduction.ActualGame.dualFintype _root_.OAI.DFVSGames.Reduction.ActualGame.mapFintype _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.RankPackets.shapeFintype _root_.OAI.DirectedFeedback.StackDSL.Code.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
open DirectedFeedback.SourceProbability
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
namespace DirectedFeedback.Junta
open scoped BigOperators
open Finset DirectedFeedback.JuntaSupport DFVSMaxCut.BooleanFourthMoment
open DFVSMaxCut.Analytic

def roundBoolean {n : ℕ} (p : Cube (Fin n) → ℝ) (x : Cube (Fin n)) : ℝ :=
  if (1 : ℝ) / 2 ≤ p x then 1 else 0

end DirectedFeedback.Junta

namespace DirectedFeedback.Junta
open DirectedFeedback.SourceProbability FiniteDistribution
open DirectedFeedback.Probability
variable {I : Type} [Fintype I] [DecidableEq I]

def biasedInfluence (k : ℕ) (f : (I → Bool) → ℝ) (i : I) : ℝ :=
  (dyadicLaw I k).expectation (fun x => (f x - f (Function.update x i (!x i))) ^ 2)

end DirectedFeedback.Junta

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_RankGraph_PrefixBit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
open DirectedFeedback.SourceProbability
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators

noncomputable section
open scoped Classical BigOperators

noncomputable section
open scoped BigOperators

noncomputable section
open scoped BigOperators

noncomputable section
open scoped BigOperators
namespace DirectedFeedback.Ranks

abbrev RankTest (L N : ℕ) := (Triple L × Triple L) × Finset (Finset (Fin N))

def rankPayoff {L N : ℕ} (ψ : Increasing L N) (t : RankTest L N) : ℝ :=
  (if t.1.1.val.image ψ.val ∈ t.2 then 1 else 0) -
  (if t.1.2.val.image ψ.val ∈ t.2 then 1 else 0)

end DirectedFeedback.Ranks
open scoped Classical
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_RankGraph_Rational
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open scoped Classical BigOperators
open scoped Classical
open scoped Classical
open scoped Classical BigOperators
open scoped BigOperators
open scoped BigOperators
open DirectedFeedback.SourceProbability
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators

open scoped Classical BigOperators

namespace DirectedFeedback.SourceProbability.FiniteDistribution
open DirectedFeedback
variable {I J : Type*} [Fintype I] [Fintype J]
def RationalMass (μ : FiniteDistribution I) : Prop := ∀ i, Rational (μ.weight i)

end DirectedFeedback.SourceProbability.FiniteDistribution

open scoped Classical BigOperators

open scoped Classical BigOperators

end

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback
open SourceProbability SourceProbability.FiniteDistribution
open Games Construction
open DFVSGames.Explicit DFVSGames.Explicit.MachineOutputContract

namespace UGBridge
variable {U V E Q : Type} [Fintype U] [Fintype V] [Fintype E] [Fintype Q]
  [Nonempty E] [Nonempty Q]

def game (G : BipartiteGame U V E Q) : Game U V E (Q × Bool) Q where
  edgeLaw := uniform E
  left := G.left
  right := G.right
  project := fun e a => G.permutation e a.1

end UGBridge

end DirectedFeedback

end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_RankGraph_AllGraph
attribute [-instance] _root_.OAI.DirectedFeedback.CookLevin.NPTableau.codec_width_nonempty _root_.OAI.DirectedFeedback.RawFamily.eNonempty _root_.OAI.DirectedFeedback.RawFamily.wNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.GraphPrinter
open BoundedExpr

structure Family where
  n : List Bool → Nat
  k : List Bool → Nat
  arc : List Bool → Nat → Nat → Prop
  n_def : Def (r:=0) (fun x _ => n x)
  k_def : Def (r:=0) (fun x _ => k x)
  arc_def : PDef (r:=2) (fun x a => arc x (a 0) (a 1))
  k_pos : ∀ x, 0 < k x
  irrefl : ∀ x i, ¬arc x i i

namespace Family
variable (F : Family)

def pairs (x : List Bool) : List (Fin (F.n x) × Fin (F.n x)) :=
  ((List.finRange (F.n x)).product (List.finRange (F.n x))).filter
    (fun p => decide (F.arc x p.1.val p.2.val))

@[simp] theorem mem_pairs (x : List Bool) (a b : Fin (F.n x)) :
    (a,b) ∈ F.pairs x ↔ F.arc x a.val b.val := by simp [pairs]

def graph (x : List Bool) : Digraph where
  n := F.n x
  arcs := F.pairs x
  loopless := by
    rintro ⟨a,b⟩ hab he
    have h := (F.mem_pairs x a b).mp hab
    change a=b at he
    subst b
    exact F.irrefl x a.val h
  nodup := (List.nodup_finRange _).product (List.nodup_finRange _) |> fun h => h.filter _

def inst (x : List Bool) : GapInstance := ⟨F.graph x,F.k x,F.k_pos x⟩

def count (x : List Bool) : Nat :=
  ∑ i ∈ Finset.range (F.n x), ∑ j ∈ Finset.range (F.n x), if F.arc x i j then 1 else 0

theorem count_eq (x : List Bool) : F.count x=(F.pairs x).length := by
  have he : (F.pairs x).toFinset = Finset.univ.filter
      (fun p : Fin (F.n x) × Fin (F.n x) => F.arc x p.1.val p.2.val) := by
    ext ⟨a,b⟩
    simp [pairs]
  have hnd : (F.pairs x).Nodup := (F.graph x).nodup
  rw [← List.toFinset_card_of_nodup hnd,he,Finset.card_filter]
  simp only [count,Finset.sum_range,Fintype.sum_prod_type]

def edgeBits (x : List Bool) : List Bool :=
  (List.range (F.n x)).flatMap (fun i => (List.range (F.n x)).flatMap
    (fun j => if F.arc x i j then natBits i++natBits j else []))

theorem edgeBits_eq (x : List Bool) : F.edgeBits x=
    (F.pairs x).flatMap (fun e => natBits e.1.val++natBits e.2.val) := by
  rw [edgeBits,pairs,flatMap_filter]
  change _ = (List.flatMap (fun i => (List.finRange (F.n x)).map (fun j => (i,j)))
    (List.finRange (F.n x))).flatMap _
  rw [List.flatMap_assoc]
  simp only [List.flatMap_map]
  rw [← map_fin_values (F.n x),List.flatMap_map]
  congr 1
  funext i
  simp only [List.flatMap_map,decide_eq_true_eq]

def bits (x : List Bool) : List Bool := natBits (F.k x)++natBits (F.n x)++
  (List.range (F.n x)).flatMap natBits++natBits (F.count x)++F.edgeBits x

theorem bits_correct (x : List Bool) : F.bits x=(F.inst x).bits := by
  simp only [bits,GapInstance.bits,inst,Digraph.bits,graph]
  rw [count_eq,edgeBits_eq]
  simp only [List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,
    List.flatMap_assoc,List.append_assoc]

end Family
end DirectedFeedback.GraphPrinter

end
end

section

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.LocalPrinter
open BoundedExpr LocalAssignments

theorem ordered_iff {H : Nat} (a b : Option (Fin H)) :
    Ordered a b ↔ (a ≠ none → b ≠ none → potential a < potential b) := by
  cases a <;> cases b <;> simp [Ordered,potential]

structure Family (S T X Y : Type) [Fintype S] [Fintype T] [Fintype X] [Fintype Y]
    (H : Nat) where
  n : List Bool → Nat
  k : List Bool → Nat
  valid : List Bool → Nat → Prop
  u : List Bool → Nat → S → Nat
  v : List Bool → Nat → T → Nat
  rule : List Bool → Nat → Rule S T X Y H
  n_def : Def (r:=0) (fun x _ => n x)
  k_def : Def (r:=0) (fun x _ => k x)
  valid_def : PDef (r:=1) (fun x a => valid x (a 0))
  u_def : ∀ s, Def (r:=1) (fun x a => u x (a 0) s)
  v_def : ∀ t, Def (r:=1) (fun x a => v x (a 0) t)
  rule_def : FDef (r:=1) (fun x a => rule x (a 0))
  k_pos : ∀ x, 0 < k x

namespace Family
variable {S T X Y : Type} [Fintype S] [Fintype T] [Fintype X] [Fintype Y]
  [Nonempty X] [Nonempty Y] {H : Nat} (F : Family S T X Y H)

def Arc (x : List Bool) (i j : Nat) : Prop :=
  i ≠ j ∧ F.valid x i ∧ F.valid x j ∧
    ∀ a : S ⊕ S → X, ∀ b : T ⊕ T → Y,
      Consistent (Sum.elim (F.u x i) (F.u x j)) a →
      Consistent (Sum.elim (F.v x i) (F.v x j)) b →
      Ordered (F.rule x i (a ∘ Sum.inl) (b ∘ Sum.inl))
        (F.rule x j (a ∘ Sum.inr) (b ∘ Sum.inr))

def value (x : List Bool) (i : Nat) (a : Nat → X) (b : Nat → Y) : Option (Fin H) :=
  F.rule x i (a ∘ F.u x i) (b ∘ F.v x i)

theorem arc_global (x : List Bool) (i j : Nat) : F.Arc x i j ↔
    i ≠ j ∧ F.valid x i ∧ F.valid x j ∧
    ∀ a : Nat → X, ∀ b : Nat → Y, Ordered (F.value x i a b) (F.value x j a b) := by
  unfold Arc value
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  exact (forall_iff (Sum.elim (F.u x i) (F.u x j)) (Sum.elim (F.v x i) (F.v x j))
    (fun a b => Ordered (F.rule x i (a ∘ Sum.inl) (b ∘ Sum.inl))
      (F.rule x j (a ∘ Sum.inr) (b ∘ Sum.inr)))).symm

def deleted (x : List Bool) (a : Nat → X) (b : Nat → Y) : Finset (Fin (F.n x)) :=
  Finset.univ.filter (fun i => F.valid x i.val ∧ F.value x i.val a b=none)

theorem deleted_feedback (x : List Bool) (a : Nat → X) (b : Nat → Y) :
    FeedbackR (fun i j : Fin (F.n x) => F.Arc x i.val j.val) (F.deleted x a b) := by
  intro n f _ ha
  by_contra hn
  have hv (j) : F.valid x (f j).val := (ha j).2.1
  have hs (j) : F.value x (f j).val a b ≠ none := by
    intro h
    exact hn ⟨j,by simp [deleted,h,hv]⟩
  have hi (j) : potential (F.value x (f j).val a b) < potential (F.value x (f (j+1)).val a b) :=
    (ordered_iff _ _).mp (((F.arc_global x _ _).mp (ha j)).2.2.2 a b) (hs j) (hs (j+1))
  have hsum := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun j _ => hi j)
  have he : (∑ j : Fin (n+1), potential (F.value x (f (j+1)).val a b)) =
      ∑ j : Fin (n+1), potential (F.value x (f j).val a b) :=
    Fintype.sum_equiv (Equiv.addRight (1 : Fin (n+1))) _ _ (fun _ => rfl)
  rw [he] at hsum
  exact (lt_irrefl _ hsum)

end Family
end DirectedFeedback.LocalPrinter

end
end

section

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.PacketSeeds
open SourceProbability FiniteDistribution Construction PrefixExperiment Games
variable {U V E X Y : Type} [Fintype U] [Fintype V] [Fintype E]
  [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
variable {M T N : Nat} [NeZero M] [NeZero T]

abbrev FullSeed (X : Type) [Fintype X] (M T N : Nat) :=
  Emb (rankLength X T) N × PrefixSeed X M T
abbrev CommonSeed (X : Type) [Fintype X] (M T N : Nat) :=
  Emb (rankLength X T) N × (Σ t : Fin T, PrefixSeed X M t.val)
abbrev BigSeed (X : Type) [Fintype X] (M T N : Nat) :=
  CommonSeed X M T N × Pivotal.LabelOrder X
abbrev SmallSeed (X Y : Type) [Fintype X] [Fintype Y] (M T N : Nat) :=
  CommonSeed X M T N × Pivotal.LabelOrder Y
abbrev CompareSeed (X Y : Type) [Fintype X] (M T N : Nat) :=
  Σ d : CommonSeed X M T N, Σ _ : Fin M, Fin (Prefix.cellCount d.2.1.val) × (Y → Coupling.Block)

abbrev Seed (X Y : Type) [Fintype X] [Fintype Y] (M T N : Nat) :=
  FullSeed X M T N ⊕ (BigSeed X M T N ⊕ (SmallSeed X Y M T N ⊕ CompareSeed X Y M T N))
instance seedFullFintype : Fintype (FullSeed X M T N) := inferInstance
instance seedCommonFintype : Fintype (CommonSeed X M T N) := inferInstance
instance seedBigFintype : Fintype (BigSeed X M T N) := inferInstance
instance seedSmallFintype : Fintype (SmallSeed X Y M T N) := inferInstance
instance seedCompareFintype : Fintype (CompareSeed X Y M T N) := inferInstance
instance seedFintype : Fintype (Seed X Y M T N) := by unfold Seed; infer_instance

def slotLaw : FiniteDistribution (SlotSeed X M) := (uniform (Fin M)).sigma subsetLaw
variable (ψLaw : FiniteDistribution (Emb (rankLength X T) N))

def fullLaw : FiniteDistribution (FullSeed X M T N) := ψLaw.product (slotLaw.iid T)
def commonLaw : FiniteDistribution (CommonSeed X M T N) :=
  ψLaw.product ((uniform (Fin T)).sigma (fun t => slotLaw.iid t.val))
def bigLaw : FiniteDistribution (BigSeed X M T N) := (commonLaw ψLaw).product Pivotal.labelOrderLaw
def smallLaw : FiniteDistribution (SmallSeed X Y M T N) := (commonLaw ψLaw).product Pivotal.labelOrderLaw

def localCompareLaw (t : Nat) : FiniteDistribution (Σ _ : Fin M, Fin (Prefix.cellCount t) × (Y → Coupling.Block)) :=
  (uniform (Fin M)).sigma (fun i => (uniform (Fin (Prefix.cellCount t))).product
    (Coupling.law (bias i) (bias_pos i).le (by linarith [bias_le_quarter i])))
def compareLaw : FiniteDistribution (CompareSeed X Y M T N) :=
  (commonLaw ψLaw).sigma (fun d => localCompareLaw d.2.1.val)

variable (G : Game U V E X Y)

def fillPrefix {t : Nat} (ht : t≤T+1) (a : PrefixSeed X M t) (e : Fin (T+1) → E) :
    PrefixData U X M t := fun j => (G.left (e (Fin.castLE ht j)),a j)
def fillFull (a : FullSeed X M T N) (e : Fin (T+1) → E) : Full U X M T N :=
  (a.1,fillPrefix G (Nat.le_succ T) a.2 e)
def fillCommon (a : CommonSeed X M T N) (e : Fin (T+1) → E) : Common U X M T N :=
  (a.1,⟨a.2.1,fillPrefix G (by have := a.2.1.isLt; omega) a.2.2 e⟩)
def fresh (a : CommonSeed X M T N) (e : Fin (T+1) → E) : E :=
  e ⟨a.2.1.val,by have := a.2.1.isLt; omega⟩
def fillBig (a : BigSeed X M T N) (e : Fin (T+1) → E) : Big U X M T N :=
  (fillCommon G a.1 e,(G.left (fresh a.1 e),a.2))
def fillSmall (a : SmallSeed X Y M T N) (e : Fin (T+1) → E) : Small U V X Y M T N :=
  (fillCommon G a.1 e,(G.right (fresh a.1 e),a.2))
def fillCompare (a : CompareSeed X Y M T N) (e : Fin (T+1) → E) : Compare U E X Y M T N :=
  ⟨fillCommon G a.1 e,fresh a.1 e,a.2⟩

def fill : Seed X Y M T N → (Fin (T+1) → E) → AllVertex U V E X Y M T N
  | .inl a,e => .inr (.inl (.inl (fillFull G a e)))
  | .inr (.inl a),e => .inr (.inl (.inr (.inl (fillBig G a e))))
  | .inr (.inr (.inl a)),e => .inr (.inl (.inr (.inr (fillSmall G a e))))
  | .inr (.inr (.inr a)),e => .inr (.inr (fillCompare G a e))

end DirectedFeedback.PacketSeeds

end
end

section

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.RankPackets
open RankGraph

variable {W X Y : Type} {T N : Nat}

def fill (s : Shape X Y T N) (a : Fin (T+1) → W) : Rank W W X Y T N :=
  match s with
  | .inl ⟨t,f⟩ => vertex (.inl ⟨t,fun i => a (Fin.castLE (Nat.le_of_lt t.isLt) i)⟩) f
  | .inr ⟨t,f⟩ => vertex (.inr ⟨t,(fun i => a (Fin.castLE (by have := t.isLt; omega) i)),
      a ⟨t.val,by have := t.isLt; omega⟩⟩) f

theorem fill_surjective [Nonempty W] : Function.Surjective
    (fun z : Shape X Y T N × (Fin (T+1) → W) => fill z.1 z.2) := by
  intro r
  induction r using Quot.inductionOn with
  | h d =>
    rcases d with ⟨⟨t,s⟩ | ⟨t,s,v⟩,f⟩
    · let a : Fin (T+1) → W := fun i => if h : i.val<t.val then s ⟨i.val,h⟩
          else Classical.choice inferInstance
      refine ⟨(.inl ⟨t,f⟩,a),?_⟩
      have he : (fun i : Fin t.val => a (Fin.castLE (Nat.le_of_lt t.isLt) i))=s := by
        funext i
        simp only [a,Fin.castLE,dite_eq_left i.isLt]
      exact congrArg (fun s' : Fin t.val → W => vertex (.inl ⟨t,s'⟩) f) he
    · let a : Fin (T+1) → W := fun i => if h : i.val<t.val then s ⟨i.val,h⟩ else v
      refine ⟨(.inr ⟨t,f⟩,a),?_⟩
      have he : (fun i : Fin t.val => a (Fin.castLE (by have := t.isLt; omega) i))=s := by
        funext i
        simp only [a,Fin.castLE,dite_eq_left i.isLt]
      have hv : a ⟨t.val,by have := t.isLt; omega⟩=v := by simp [a]
      have hp : ((fun i : Fin t.val => a (Fin.castLE (by have := t.isLt; omega) i)),
          a ⟨t.val,by have := t.isLt; omega⟩)=(s,v) := Prod.ext he hv
      exact congrArg (fun p : (Fin t.val → W) × W => vertex (.inr ⟨t,p⟩) f) hp

theorem eval_fill (s : Shape X Y T N) (a : Fin (T+1) → W)
    (lu : W → X) (lv : W → Y) :
    eval lu lv (fill s a) = eval (lu ∘ a) (lv ∘ a) (fill s id) := by
  rcases s with ⟨t,f⟩ | ⟨t,f⟩ <;> rfl

end DirectedFeedback.RankPackets

end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_RankGraph_PacketLocality
attribute [-instance] _root_.OAI.DirectedFeedback.CookLevin.NPTableau.codec_width_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.PacketLocality
open Construction SourceProbability FiniteDistribution Games RankGraph PacketSeeds
variable {U V E X Y : Type} [Fintype U] [Fintype V] [Fintype E]
  [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
variable {M T N : Nat} [NeZero M] [NeZero T]

def localGame (f : Slots T → X ≃ Y × Bool) : Game (Slots T) (Slots T) (Slots T) X Y where
  edgeLaw := uniform _
  left := id
  right := id
  project e x := (f e x).1

variable (G : Game U V E X Y) (hYX : Fintype.card Y≤Fintype.card X) (fiber : E → X ≃ Y × Bool)
variable (s : Seed X Y M T N) (e : Slots T → E) (a : U → X) (b : V → Y)

omit [Fintype U] [Fintype V] [Nonempty Y] [NeZero M] [NeZero T] in
lemma deleted_fill :
    AllLabels.deleted G hYX fiber a b (fill G s e) ↔
    AllLabels.deleted (localGame (fiber ∘ e)) hYX (fiber ∘ e)
      (a ∘ G.left ∘ e) (b ∘ G.right ∘ e) (fill (localGame (fiber ∘ e)) s id) := by
  rcases s with s | (s | (s | s))
  · rfl
  · simp +unfoldPartialApp only [AllLabels.deleted,TestGraph.LabelDeleted,fill,fillBig,fillCommon,fillPrefix,fresh,
      wildcard,bigWildcard,labels,vertices,localGame,map_snoc_apply,Function.comp_def,id_eq]
    rfl
  · rfl
  · simp +unfoldPartialApp only [AllLabels.deleted,TestGraph.LabelDeleted,fill,fillCompare,comparison,
      fillCommon,fillPrefix,fresh,localGame,twoLevel,eval_vertex,labels,vertices,
      map_snoc_apply,Function.comp_def,id_eq]
    rfl

omit [Fintype U] [Fintype V] [Nonempty Y] [NeZero M] [NeZero T] in
lemma height_fill :
    AllLabels.height G hYX fiber a b (fill G s e) =
    AllLabels.height (localGame (fiber ∘ e)) hYX (fiber ∘ e)
      (a ∘ G.left ∘ e) (b ∘ G.right ∘ e) (fill (localGame (fiber ∘ e)) s id) := by
  rcases s with s | (s | (s | s))
  · rfl
  · simp +unfoldPartialApp only [AllLabels.height,fill,fillBig,fillCommon,fillPrefix,fresh,
      wildcard,bigWildcard,labels,vertices,localGame,map_snoc_apply,Function.comp_def,id_eq]
    rfl
  · rfl
  · simp +unfoldPartialApp only [AllLabels.height,fill,fillCompare,comparison,
      fillCommon,fillPrefix,fresh,localGame,twoLevel,eval_vertex,labels,vertices,
      map_snoc_apply,Function.comp_def,id_eq]
    rfl

omit [Fintype U] [Fintype V] [Nonempty Y] [NeZero M] [NeZero T] in
lemma code_fill :
    AllLabels.code G hYX fiber a b (fill G s e) =
    AllLabels.code (localGame (fiber ∘ e)) hYX (fiber ∘ e)
      (a ∘ G.left ∘ e) (b ∘ G.right ∘ e) (fill (localGame (fiber ∘ e)) s id) := by
  unfold AllLabels.code
  rw [deleted_fill G hYX fiber s e a b]
  split_ifs
  · rfl
  · congr 2
    exact height_fill G hYX fiber s e a b

end DirectedFeedback.PacketLocality

end
end

section

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.RawFamily
open BoundedExpr Construction PacketSeeds Games RankGraph
variable (q M T N : Nat) [NeZero q] [NeZero M] [NeZero T] [NeZero N]
abbrev Seed := PacketSeeds.Seed (X q) (Y q) M T N
abbrev Tag := Shape q T N ⊕ Seed q M T N
instance tagNonempty : Nonempty (Tag q M T N) := ⟨.inl (.inl ⟨0,fun _ => 0⟩)⟩
variable (D C : Nat) (c : Seed q M T N → Nat)
def copies (x : List Bool) := SumBox.copies (r T D C x) c

def size (x : List Bool) := SumBox.size (Shape q T N) (Seed q M T N)
  (GameRead.n x) (GameRead.m x) (T+1) (r T D C x) c
def tag (x : List Bool) (i : Nat) := SumBox.tag (Shape q T N) (Seed q M T N)
  (GameRead.n x) (GameRead.m x) (T+1) (r T D C x) c i
def digit (x : List Bool) (i : Nat) (j : Fin (T+1)) := SumBox.digits (Seed q M T N)
  (GameRead.n x) (GameRead.m x) (T+1) (r T D C x) c i j
def copy (x : List Bool) (i : Nat) := SumBox.copy (Seed q M T N)
  (GameRead.n x) (GameRead.m x) (T+1) (r T D C x) c i
def valid (x : List Bool) (i : Nat) := SumBox.valid (Shape q T N) (Seed q M T N)
  (GameRead.n x) (GameRead.m x) (T+1) (r T D C x) c i

def isRank : Tag q M T N → Prop | .inl _ => True | .inr _ => False
def u (x : List Bool) (i : Nat) (j : Fin (T+1)) : Nat :=
  if isRank q M T N (tag q M T N D C c x i) then digit q M T N D C c x i j
  else GameRead.left q x (digit q M T N D C c x i j)
def v (x : List Bool) (i : Nat) (j : Fin (T+1)) : Nat :=
  if isRank q M T N (tag q M T N D C c x i) then digit q M T N D C c x i j
  else GameRead.right q x (digit q M T N D C c x i j)

def tagRule (s : Tag q M T N) (f : Fin (T+1) → X q ≃ Y q × Bool) :
    LocalPrinter.Rule (Fin (T+1)) (Fin (T+1)) (X q) (Y q) (2*N+1) := fun a b =>
  AllLabels.code (PacketLocality.localGame f) (hYX q) f a b
    (match s with
    | .inl r => .inl (RankPackets.fill r id)
    | .inr s => PacketSeeds.fill (PacketLocality.localGame f) s id)
def rule (x : List Bool) (i : Nat) := tagRule q M T N (tag q M T N D C c x i)
  (fun j => GameRead.fiber q x (digit q M T N D C c x i j))

end DirectedFeedback.RawFamily

end
end

section

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.PacketSeeds
open SourceProbability FiniteDistribution Construction PrefixExperiment Games
variable {U V E X Y : Type} [Fintype U] [Fintype V] [Fintype E]
  [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
variable {M T N : Nat} [NeZero M] [NeZero T]
variable (ψLaw : FiniteDistribution (Emb (rankLength X T) N))

def mass (H K : Nat) : Seed X Y M T N → ℝ
  | .inl s => H*(fullLaw ψLaw).weight s
  | .inr (.inl s) => Fintype.card X*(bigLaw ψLaw).weight s
  | .inr (.inr (.inl s)) => Fintype.card Y*(smallLaw ψLaw).weight s
  | .inr (.inr (.inr s)) => K*(compareLaw ψLaw).weight s

variable (G : Game U V E X Y)

theorem iid_uniform_expectation {A : Type} [Fintype A] [Nonempty A] (L : Nat) (f : (Fin L → A) → ℝ) :
    ((uniform A).iid L).expectation f = (∑ a, f a)/(Fintype.card A:ℝ)^L := by
  simp only [expectation,iid,uniform,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  simp only [div_eq_mul_inv,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  ring

end DirectedFeedback.PacketSeeds

end
end

section

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.LivePackets
open Construction SourceProbability FiniteDistribution Games RankGraph PacketSeeds
variable {W E X Y : Type} [Fintype W] [Fintype E] [Fintype X] [Fintype Y]
  [Nonempty W] [Nonempty E] [Nonempty X] [Nonempty Y]
variable {M T N : Nat} [NeZero M] [NeZero T]

abbrev Live (r : Nat) (c : Seed X Y M T N → Nat) :=
  ((RankPackets.Shape X Y T N × (Fin (T+1) → W)) × Fin r) ⊕
    (Σ s : Seed X Y M T N, (Fin (T+1) → E) × Fin (c s))
instance liveFintype (r : Nat) (c : Seed X Y M T N → Nat) : Fintype (Live (W:=W) (E:=E) r c) := by
  unfold Live
  infer_instance

variable (G : Game W W E X Y) (ψLaw : FiniteDistribution (Emb (rankLength X T) N))
variable (r : Nat) (c : Seed X Y M T N → Nat)
def project : Live (W:=W) (E:=E) r c → AllVertex W W E X Y M T N
  | .inl a => .inl (RankPackets.fill a.1.1 a.1.2)
  | .inr a => PacketSeeds.fill G a.1 a.2.1

omit [Nonempty W] [Nonempty E] [Nonempty X] [Nonempty Y] [NeZero M] [NeZero T] in
theorem sum_project (f : AllVertex W W E X Y M T N → ℝ) (hf : ∀ z, f (.inl z)=0) :
    (∑ a : Live (W:=W) (E:=E) r c, f (project G r c a)) =
      ∑ s, (c s:ℝ)*∑ e : Fin (T+1) → E, f (PacketSeeds.fill G s e) := by
  simp only [Fintype.sum_sum_type,project,hf,Finset.sum_const_zero,zero_add,Fintype.sum_sigma,
    Fintype.sum_prod_type,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  simp only [Finset.mul_sum]

omit [Nonempty E] [Nonempty X] [Nonempty Y] [NeZero M] [NeZero T] in
theorem rank_fiber_bound (z : Rank W W X Y T N) :
    r ≤ PotentialCover.fiberCount (project G r c) (.inl z) := by
  obtain ⟨⟨s,a⟩,ha⟩ := RankPackets.fill_surjective (W:=W) (X:=X) (Y:=Y) (T:=T) (N:=N) z
  change RankPackets.fill s a=z at ha
  let f : Fin r → {v : Live (W:=W) (E:=E) r c // project G r c v=.inl z} :=
    fun j => ⟨.inl ((s,a),j),by change Sum.inl (RankPackets.fill s a)=Sum.inl z; rw [ha]⟩
  have hf : Function.Injective f := by
    intro i j h
    have := congrArg Subtype.val h
    simpa [f] using this
  have hcard := Fintype.card_le_of_injective f hf
  rw [Fintype.card_fin] at hcard
  convert hcard using 1
  all_goals try with_reducible_and_instances rfl
  rw [Fintype.card_subtype]
  unfold PotentialCover.fiberCount
  congr 1
  ext v
  simp

end DirectedFeedback.LivePackets

end
end

section

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.RawFamily
open Construction Games PacketSeeds SourceProbability FiniteDistribution RankGraph
variable {q M T N : Nat} [NeZero q] [NeZero M] [NeZero T] [NeZero N]
variable (D C : Nat) (c : Seed q M T N → Nat) (hC : 0<C) (x : List Bool)
abbrev Live := LivePackets.Live (W:=W x) (E:=E x) (r T D C x) c

variable (G : Game (W x) (W x) (E x) (X q) (Y q))
variable (fiber : E x → X q ≃ Y q × Bool)
variable (hl : ∀e : E x, GameRead.left q x e.val=(G.left e).val)
variable (hr : ∀e : E x, GameRead.right q x e.val=(G.right e).val)
variable (hf : ∀e : E x, GameRead.fiber q x e.val=fiber e)
include hl hr hf

def liveDeleted (a : W x → X q) (b : W x → Y q) : Finset (Live D C c x) :=
  Finset.univ.filter (fun z => AllLabels.deleted G (hYX q) fiber a b (LivePackets.project G (r T D C x) c z))

end DirectedFeedback.RawFamily

end
end

section

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.RawFamily
open Construction Games PacketSeeds SourceProbability FiniteDistribution RankGraph
variable {q D : Nat} [NeZero q] (P : Parameters D) (R : RankParameters P (X q)) [NeZero R.N]
variable (C : Nat) (c : Seed q P.M P.T R.N → Nat) (hC : 0<C)
variable (hc : ∀s, (C:ℝ)*mass R.law (8*(D+1)) P.K s=c s)
variable (x : List Bool)
variable (G : Game (W x) (W x) (E x) (X q) (Y q))
variable (fiber : E x → X q ≃ Y q × Bool)
variable (hl : ∀e : E x, GameRead.left q x e.val=(G.left e).val)
variable (hr : ∀e : E x, GameRead.right q x e.val=(G.right e).val)
variable (hf : ∀e : E x, GameRead.fiber q x e.val=fiber e)
variable (hE : G.edgeLaw=uniform (E x))
variable (hproj : ∀e a, (fiber e a).1=G.project e a)

def extend {n : Nat} {A : Type} [Nonempty A] (a : Fin n → A) (i : Nat) : A :=
  if h : i<n then a ⟨i,h⟩ else Classical.choice inferInstance
@[simp] theorem extend_restrict {n : Nat} {A : Type} [Nonempty A] (a : Fin n → A) :
    extend a ∘ Fin.val=a := by funext i; simp [extend]

end DirectedFeedback.RawFamily

end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped Classical
namespace DirectedFeedback.CookLevin

namespace NPTableau
open Turing DFVSGames.Foundations DFVSGames.Foundations.PCP
attribute [local instance] FinTM2.ΛFin

theorem decodeEvent_surjective (H S : Nat) : Function.Surjective (decodeEvent H S) := by
  intro e
  rcases e with j | (tj | u)
  · refine ⟨⟨j.val,by dsimp [eventCount]; omega⟩,?_⟩
    simp [decodeEvent,j.isLt]
  · let i := finProdFinEquiv tj
    refine ⟨⟨S+1+i.val,by have := i.isLt; dsimp [eventCount]; omega⟩,?_⟩
    simp only [decodeEvent,show ¬ S+1+i.val<S+1 by omega,Nat.add_sub_cancel_left,
      dite_eq_left i.isLt]
    exact congrArg (fun t => Sum.inr (Sum.inl t)) (finProdFinEquiv.symm_apply_apply tj)
  · cases u
    refine ⟨⟨S+1+H*(S+1),by dsimp [eventCount]; omega⟩,?_⟩
    simp [decodeEvent,show ¬ S+1+H*(S+1)<S+1 by omega]

end NPTableau
end DirectedFeedback.CookLevin

end
end

end OAI
end


