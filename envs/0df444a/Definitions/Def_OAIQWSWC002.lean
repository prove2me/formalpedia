-- Prove2me | Definitions.Def_OAIQWSWC002
-- name    : OAIQWSWC002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-23T16:12:24.771967+00:00
-- url     : https://prove2.me/theorems/81ade4bf-e8dc-4ebe-aaf0-0939104e4bb2
-- title:
--   OpenAI switch-chain split: definitions bundle OAIQWSWC002
-- statement:
--   One of the definitions bundles of the split of OpenAI's proof of `OAI.Problem315.switch_chain_main`: the lazy switch chain on simple graphs with a prescribed graphical degree sequence mixes in at most $2n^8$ steps, and has spectral gap at least $1/(24 n^2 \binom n4)$ when there is more than one realization. The bundle holds OpenAI's Lean definitions from the modules listed below of `lean/OAI/Probability/SwitchChain` (OpenAI, *Polynomial mixing of the switch chain for every graphical degree sequence*, OpenAI Math Release, September 25, 2026, result family 131, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a. It also holds the lemmas these definitions use in their bodies, and OpenAI's `@[simp]` lemmas about them.
--
--   This bundle carries the operators the later statements are phrased with: the triple operator $H_T = \sum_{a \subseteq T} h_a$ (`PairResampling.tripleGenerator`), the reindexed equality vectors and moves on a slice (`SliceNormalized.reindexedRaw`, `SliceNormalized.reindexedMove`), the pair-fiber moves used for connectivity (`FiberMove`), and the law of the block counts and the cell models used for the three-row variance bound on a vertex triple.
--
--   The definitions of the published goal (`GraphState`, `SwitchStep`, `switchKernel`, `mixingTime`, `hasSpectralGapAtLeast` and the rest) come from the published bundle `Def_SwitchChain`. It also imports the bundles `OAIQWSWC000`, `OAIQWSWC001` of this split.
--
--   Modules: `FourVertexSwitch`, `OrthogonalPairResampling`, `PairEqualityBudget`, `PairEqualityLocalization`, `PairEqualityOrientation`, `PairEqualityRestriction`, `PairEqualityUnordered`, `PairFiberConnectivity`, `PairFiberEqualityTransport`, `PairFiberSliceComparison`, `PairGeneratorSquare`, `PairProjectionCell`, `PairSquaredEnergy`, `ProposalLaplacian`, `SliceCardEncoding`, `SliceCoefficientAlgebra`, `SliceEuclideanGenerator`, `SliceGeneratorEquality`, `SliceGeneratorSampling`, `SliceGramOrbit`, `SliceGramProfile`, `SliceImageNorm`, `SlicePermutationAction`, `SliceReindexedComparison`, `SwitchMultiplicity`, `TripleActualRowBound`, `TripleCellTransport`, `TripleCellVarianceGluing`, `TripleCountEigenvalue`, `TripleCountGram`, `TripleCountLaw`, `TripleMatrixFinEquiv`, `VariableBlockVariance`.
-- source:
--   OpenAI, Polynomial mixing of the switch chain for every graphical degree sequence, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 131; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-Mixing-of-the-Switch-Chain-for-Every-Graphical-Degree-Sequence-September-25-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability/SwitchChain at commit adc7f12

import Mathlib
import Definitions.Def_SwitchChain
import Definitions.Def_OAIQWSWC000
import Definitions.Def_OAIQWSWC001

section
-- module Solutions.OAIQW_Problem315.FourVertexSwitch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem315

def fourVertexState {n : Nat} {d : Fin n → Nat} (G : GraphState n d)
    (a b c e : Fin n) (h : FourDistinct a b c e) : GraphState n d :=
  ⟨proposalResult G.val (fourVertexProposal a b c e h),
    proposalResult_realizes G.property (fourVertexProposal a b c e h)⟩

end Problem315

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.OrthogonalPairResampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators RealInnerProductSpace

namespace Problem315
namespace PairResampling

attribute [local instance] Classical.propDecidable

variable {n : ℕ} {d : Fin n → ℕ} (a : Finset (Fin n))

def generator (n : ℕ) (d : Fin n → ℕ) : StateSpace n d →L[ℝ] StateSpace n d :=
  ∑ a ∈ pairs n, fluctuation n d a

def fiberIndicator (a : Finset (Fin n)) (G : GraphState n d) : StateSpace n d :=
  WithLp.toLp 2 (fun H => if SameFiber a G.val H.val then 1 else 0)

end PairResampling
end Problem315

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.PairProjectionCell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.PairResampling

attribute [local instance] Classical.propDecidable

variable {n : ℕ} {d : Fin n → ℕ}

def CellInvariant (a : Finset (Fin n)) (C : GraphState n d → Prop) : Prop :=
  ∀ G H, SameFiber a G.val H.val → (C G ↔ C H)

end Problem315.PairResampling

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.PairEqualityLocalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Problem315.PairEquality
open PairResampling PairFiber
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {d : Fin n → ℕ}

def gatedCentered (i j k l : Fin n) : StateSpace n d :=
  WithLp.toLp 2 (fun G => if active i j k l G then centered i j k l G else 0)

def localizedVector (i j k l : Fin n) (G : GraphState n d) : StateSpace n d :=
  restrictCell (fun H => SameFiber {i,j} G.val H.val) (gatedCentered i j k l)

end Problem315.PairEquality

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.PairEqualityRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Problem315.PairEquality
open PairResampling PairFiber
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {d : Fin n → ℕ}

def assignmentVector (G : GraphState n d) (i j k l : Fin n) : AssignmentSpace G i j :=
  WithLp.toLp 2 (fun T => if active i j k l G then
    SliceMoments.centeredEqual (singletonSet G.val i j) (leftSet G.val i j).card
      k l T.val else 0)

end Problem315.PairEquality

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.SlicePermutationAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.SlicePermutationAction

variable {α : Type*} [sectionFintypeα : Fintype α] [sectionDecidableEqα : DecidableEq α]

def relabelHom (q : ℕ) : Equiv.Perm α →* Equiv.Perm (Slice α q) where
  toFun := relabelEquiv
  map_one' := by apply Equiv.ext; intro s; exact relabel_one s
  map_mul' σ τ := by apply Equiv.ext; intro s; exact relabel_mul σ τ s

end Problem315.SlicePermutationAction

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.PairFiberSliceComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.PairFiber

open SlicePermutationAction
attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

def assignmentRelabel (G : SimpleGraph V) (i j : V)
    (σ : Equiv.Perm (singletonSet G i j)) (T : Assignment G i j) :
    Assignment G i j :=
  (assignmentSliceEquiv G i j).symm
    (relabel σ (assignmentSliceEquiv G i j T))

def assignmentRelabelEquiv (G : SimpleGraph V) (i j : V)
    (σ : Equiv.Perm (singletonSet G i j)) : Equiv.Perm (Assignment G i j) :=
  ((assignmentSliceEquiv G i j).trans (relabelEquiv σ)).trans
    (assignmentSliceEquiv G i j).symm

end Problem315.PairFiber

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.PairFiberEqualityTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.PairFiber

attribute [local instance] Classical.propDecidable

def stateFiberNormalizedEquiv {n : ℕ} {d : Fin n → ℕ}
    (G : GraphState n d) (i j : Fin n) (hij : i ≠ j) :
    StateFiber G i j ≃
      SliceNormalized.State (singletonSet G.val i j) (leftSet G.val i j).card :=
  ((stateFiberEquiv G i j hij).trans (assignmentSliceEquiv G.val i j)).trans
    (cardSliceEquivPowerset _)

end Problem315.PairFiber

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.SwitchMultiplicity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem315.SwitchPairFiber

attribute [local instance] Classical.propDecidable

def Crosses {n : ℕ} (p : SwitchProposal n) (A : Finset (Fin n)) : Prop :=
  ∀ u v, ((removedMatching p).Adj u v ∨ (addedMatching p).Adj u v) →
    (u ∈ A ↔ v ∉ A)

def crossingPairs {n : ℕ} (p : SwitchProposal n) : Finset (Finset (Fin n)) :=
  (p.1.val.powersetCard 2).filter (Crosses p)

end Problem315.SwitchPairFiber

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.ProposalLaplacian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

namespace Problem315

def pairSwitchLaplacian (n : Nat) (d : Fin n → Nat) (a : Finset (Fin n))
    (f : GraphState n d → ℝ) (G : GraphState n d) : ℝ :=
  ∑ p ∈ allProposals n,
    if a ∈ SwitchPairFiber.crossingPairs p then f G - f (proposalState G p) else 0

end Problem315

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.PairSquaredEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace Problem315.PairSquaredEnergy
attribute [local instance] Classical.propDecidable

def reverseMove {n : ℕ} {d : Fin n → ℕ}
    (x : GraphState n d × SwitchProposal n) : GraphState n d × SwitchProposal n :=
  if validSwitch x.1.val x.2 then (proposalState x.1 x.2, reverseProposal x.2) else x

lemma reverseMove_involutive {n : ℕ} {d : Fin n → ℕ} :
    Function.Involutive (@reverseMove n d) := by
  intro x
  rcases x with ⟨G,p⟩
  by_cases h : validSwitch G.val p
  · have hr : validSwitch (proposalState G p).val (reverseProposal p) := by
      change validSwitch (proposalResult G.val p) (reverseProposal p)
      rw [proposalResult_of_valid h]
      exact validSwitch_reverse_replace h
    have hb : proposalState (proposalState G p) (reverseProposal p) = G := by
      apply Subtype.ext
      exact proposalResult_reverse h
    simp [reverseMove, h, hr, hb]
  · simp [reverseMove, h]

def reverseMoveEquiv {n : ℕ} {d : Fin n → ℕ} :
    Equiv.Perm (GraphState n d × SwitchProposal n) :=
  ⟨reverseMove, reverseMove, reverseMove_involutive, reverseMove_involutive⟩

end Problem315.PairSquaredEnergy

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.SliceCoefficientAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.SliceCoefficients

variable {V : Type*} [sectionFintypeV : Fintype V] [DecidableEq V]

include sectionFintypeV in
@[simp] theorem constantPair_diag (a : ℝ) (i : V) : constantPair a i i = 0 := by
  have retainedsectionFintypeV := sectionFintypeV
  simp [constantPair]

end Problem315.SliceCoefficients

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.SliceEuclideanGenerator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Problem315.SliceEuclideanGenerator

variable {α : Type*} [Fintype α] [DecidableEq α]

@[simp] theorem moveOperator_twice (q : ℕ) (a b : α)
    (f : EuclideanSpace ℝ (State α q)) :
    moveOperator q a b (moveOperator q a b f) = f := by
  ext S
  simp

def generator (q : ℕ) :
    EuclideanSpace ℝ (State α q) →ₗ[ℝ] EuclideanSpace ℝ (State α q) :=
  (1 / 4 : ℝ) • ∑ a : α, ∑ b : α, (LinearMap.id - moveOperator q a b)

@[simp] theorem generator_apply (q : ℕ) (f : EuclideanSpace ℝ (State α q))
    (S : State α q) :
    generator q f S = (∑ a : α, ∑ b : α, (f S - f (swapState q a b S))) / 4 := by
  simp only [generator, LinearMap.smul_apply, LinearMap.sum_apply,
    LinearMap.sub_apply, LinearMap.id_apply, PiLp.smul_apply, smul_eq_mul,
    WithLp.ofLp_sum, Finset.sum_apply, PiLp.sub_apply, moveOperator_apply]
  ring

end Problem315.SliceEuclideanGenerator

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.SliceGeneratorSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace Problem315.SliceEuclideanGenerator

variable {α : Type*} [Fintype α] [DecidableEq α]

def coordinates {q : ℕ} (S : State α q) (i : α) : ℝ :=
  if i ∈ S.val then 1 else 0

def sample (q : ℕ) (f : (α → ℝ) → ℝ) : EuclideanSpace ℝ (State α q) :=
  WithLp.toLp 2 (fun S => f (coordinates S))

@[simp] theorem sample_apply (q : ℕ) (f : (α → ℝ) → ℝ) (S : State α q) :
    sample q f S = f (coordinates S) := rfl

end Problem315.SliceEuclideanGenerator

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.SliceGeneratorEquality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace Problem315.SliceEuclideanGenerator

variable {α : Type*} [Fintype α] [DecidableEq α]

def equalityVector (q : ℕ) (p : ℝ) (i j : α) : EuclideanSpace ℝ (State α q) :=
  sample q (fun x => SliceEquality.offDiagonal (SliceEquality.centeredEquality x p) i j)

end Problem315.SliceEuclideanGenerator

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.SliceImageNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.SliceImageNorm

variable {α : Type*} [Fintype α] [sectionDecidableEqα : DecidableEq α]

def equalityImage (q : ℕ) (c : α → α → ℝ) (S : Finset α) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, ∑ j, c i j * SliceMoments.centeredEqual Finset.univ q i j S

def linearGramScalar (q : ℕ) : ℝ :=
  (2 * (q : ℝ) - (Fintype.card α : ℝ))^2 /
    (2 * ((Fintype.card α : ℝ) - 2) *
      SliceMoments.equalMean (Finset.univ : Finset α) q)

end Problem315.SliceImageNorm

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.SliceGramOrbit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.SliceGramOrbit

variable {α : Type*} [Fintype α] [DecidableEq α]

def centeredPair (q : ℕ) (P S : Finset α) : ℝ :=
  pairEquality P S - SliceMoments.equalMean (Finset.univ : Finset α) q

def gram (q : ℕ) (P Q : Finset α) : ℝ :=
  SliceMoments.average Finset.univ q (fun S => centeredPair q P S * centeredPair q Q S)

end Problem315.SliceGramOrbit

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.SliceGramProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.SliceGramProfile

variable {V : Type*} [Fintype V] [DecidableEq V]

def profile (q t : ℕ) : ℝ :=
  if h : ∃ p : Finset V × Finset V,
      p.1.card = 2 ∧ p.2.card = 2 ∧ (p.1 ∩ p.2).card = t then
    SliceGramOrbit.gram q h.choose.1 h.choose.2
  else 0

end Problem315.SliceGramProfile

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.SliceReindexedComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.SliceNormalized

variable {V Ω : Type*} [Fintype V] [sectionDecidableEqV : DecidableEq V] [sectionFintypeΩ : Fintype Ω]

def reindexedRaw {q : ℕ} (e : Ω ≃ State V q) (i j : V) :
    EuclideanSpace ℝ Ω := pullback e (raw q i j)

@[simp] theorem reindexedRaw_apply {q : ℕ} (e : Ω ≃ State V q)
    (i j : V) (ω : Ω) :
    reindexedRaw e i j ω = if i = j then 0 else
      SliceMoments.centeredEqual Finset.univ q i j (e ω).val := rfl

def reindexedMove {q : ℕ} (e : Ω ≃ State V q) (i j : V)
    (f : EuclideanSpace ℝ Ω) : EuclideanSpace ℝ Ω :=
  WithLp.toLp 2 (fun ω => f (e.symm (SliceEuclideanGenerator.swapState q i j (e ω))))

include sectionFintypeΩ in
@[simp] theorem reindexedMove_apply {q : ℕ} (e : Ω ≃ State V q)
    (i j : V) (f : EuclideanSpace ℝ Ω) (ω : Ω) :
    reindexedMove e i j f ω =
      f (e.symm (SliceEuclideanGenerator.swapState q i j (e ω))) := by
  have retainedsectionFintypeΩ := sectionFintypeΩ
  exact rfl

end Problem315.SliceNormalized

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.SliceCardEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem315.SliceNormalized

variable {V Ω : Type*} [Fintype V] [sectionDecidableEqV : DecidableEq V] [sectionFintypeΩ : Fintype Ω]

def cardSliceEquiv (q : ℕ) : State V q ≃ SlicePermutationAction.Slice V q where
  toFun S := ⟨S.val, (Finset.mem_powersetCard.mp S.property).2⟩
  invFun S := ⟨S.val, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, S.property⟩⟩
  left_inv S := by apply Subtype.ext; rfl
  right_inv S := by apply Subtype.ext; rfl

include sectionDecidableEqV in
@[simp] theorem cardSliceEquiv_val (q : ℕ) (S : State V q) :
    (cardSliceEquiv q S).val = S.val := by
  have retainedsectionDecidableEqV := sectionDecidableEqV
  exact rfl

include sectionDecidableEqV in
@[simp] theorem cardSliceEquiv_symm_val (q : ℕ) (S : SlicePermutationAction.Slice V q) :
    ((cardSliceEquiv q).symm S).val = S.val := by
  have retainedsectionDecidableEqV := sectionDecidableEqV
  exact rfl

end Problem315.SliceNormalized

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.PairEqualityBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.PairEquality
open PairResampling PairFiber
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {d : Fin n → ℕ}

def assignmentNormalizedEquiv (G : GraphState n d) (i j : Fin n) :
    Assignment G.val i j ≃
      SliceNormalized.State (singletonSet G.val i j) (leftSet G.val i j).card :=
  (assignmentSliceEquiv G.val i j).trans (cardSliceEquivPowerset _)

def orderedGain (i j k l : Fin n) : StateSpace n d →L[ℝ] StateSpace n d :=
  if h : FourDistinct i k l j then
    SwitchFlip.projection (fourVertexProposal i k l j h) else 0

end Problem315.PairEquality

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.PairEqualityOrientation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.PairEquality
open PairResampling PairFiber
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {d : Fin n → ℕ}

@[simp] theorem observable_swap_right (i k l : Fin n) :
    observable (d := d) i l k = observable i k l := by
  ext G
  change (if G.val.Adj i l ↔ G.val.Adj i k then (1 : ℝ) else 0) =
    if G.val.Adj i k ↔ G.val.Adj i l then 1 else 0
  simp only [iff_comm]

@[simp] theorem centered_swap_right (i j k l : Fin n) :
    centered (d := d) i j l k = centered i j k l := by
  simp only [centered, observable_swap_right]

end Problem315.PairEquality

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.PairEqualityUnordered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.PairEquality
open PairResampling PairFiber
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {d : Fin n → ℕ}

def pairProjection (a b : Finset (Fin n)) : StateSpace n d →L[ℝ] StateSpace n d :=
  if ha : a.card = 2 then
    if hb : b.card = 2 then
      projection (endpoints a ha).1 (endpoints a ha).2
        (endpoints b hb).1 (endpoints b hb).2
    else 0
  else 0

@[simp] theorem pairProjection_eq_zero_right (a b : Finset (Fin n))
    (hb : b.card ≠ 2) : pairProjection (d := d) a b = 0 := by
  unfold pairProjection
  split_ifs <;> rfl

end Problem315.PairEquality

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.PairFiberConnectivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem315.PairResampling

attribute [local instance] Classical.propDecidable

def FiberMove (n : Nat) (d : Fin n → Nat) (G H : GraphState n d) : Prop :=
  ∃ a ∈ pairs n, SameFiber a G.val H.val

end Problem315.PairResampling

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.PairGeneratorSquare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.PairResampling

attribute [local instance] Classical.propDecidable

def tripleGenerator (n : Nat) (d : Fin n → Nat) (T : Finset (Fin n)) :
    StateSpace n d →L[ℝ] StateSpace n d :=
  ∑ a ∈ T.powersetCard 2, fluctuation n d a

end Problem315.PairResampling

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.TripleCountLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.TripleCountLaw

def weight (a : Fin 3 → ℕ) {m : ℕ} (x : Triple m) : ℝ :=
  ∏ i : Fin 3, CountCoupling.countWeight (a i) (x.val i).val

def conditionalAverage (a : Fin 3 → ℕ) {m : ℕ} (f : Triple m → ℝ)
    (σ : Equiv.Perm (Fin 3)) (t : ℕ) : ℝ :=
  (∑ x : Fiber m σ t, weight a x.val * f x.val) /
    (∑ x : Fiber m σ t, weight a x.val)

def rowSum {m : ℕ} (b : Fin 3 → ℕ → ℝ) (x : Triple m) : ℝ :=
  ∑ i : Fin 3, b i (x.val i).val

def totalWeight (a : Fin 3 → ℕ) (m : ℕ) : ℝ := ∑ x : Triple m, weight a x

def probability (a : Fin 3 → ℕ) {m : ℕ} (x : Triple m) : ℝ :=
  weight a x / totalWeight a m

end Problem315.TripleCountLaw

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.TripleCountEigenvalue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.TripleCountLaw

def marginal (a : Fin 3 → ℕ) (m : ℕ) (i : Fin 3) (t : Fin (m + 1)) : ℝ :=
  ∑ x : Triple m, if x.val i = t then probability a x else 0

end Problem315.TripleCountLaw

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.TripleCountGram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.TripleCountLaw

def countKey (m : ℕ) (i : Fin 3) (x : Triple m) : Fin (m + 1) := x.val i

end Problem315.TripleCountLaw

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.VariableBlockVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.VariableBlockVariance
open FixedBlockMarginal (average)
open TripleCountLaw (Triple)

variable (U W : Type*) [Fintype U] [DecidableEq U] [Fintype W] [DecidableEq W]

variable {U W}

def rowFunction (m : ℕ) (u w : Fin 3 → ℕ)
    (g : Fin 3 → Finset U → Finset W → ℝ) (i : Fin 3)
    (x : Triple m) (z : Fiber U W m u w x) : ℝ :=
  g i (FixedBlock.row z.1.val i) (FixedBlock.row z.2.val i)

def rowMean (m : ℕ) (u w : Fin 3 → ℕ)
    (g : Fin 3 → Finset U → Finset W → ℝ) (i : Fin 3) (t : Fin (m + 1)) : ℝ :=
  average (fun z : FixedBlockMarginal.Subsets (α := U) (t.val + u i) ×
      FixedBlockMarginal.Subsets (α := W) (t.val + w i) => g i z.1.val z.2.val)

end Problem315.VariableBlockVariance

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.TripleCellTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.TripleCellTransport

open TripleStateReindex TripleInternalEncoding
attribute [local instance] Classical.propDecidable

variable {n : ℕ} {d : Fin n → ℕ}
variable (T : Finset (Fin n)) (hT : T.card = 3)

def splitGraph (G : GraphState n d) : SimpleGraph (Fin 3 ⊕ Outside T) :=
  G.val.comap (splitEquiv T hT)

theorem splitGraph_degree (G : GraphState n d) (v : Fin 3 ⊕ Outside T) :
    (splitGraph T hT G).degree v = d (splitEquiv T hT v) := by
  rw [← degreeCount_eq_degree]
  change degreeCount (G.val.comap (splitEquiv T hT)) v = _
  rw [degreeCount_comap]
  exact G.property _

abbrev Cell (G : GraphState n d) :=
  {H : GraphState n d //
    outsideGraph (splitGraph T hT H) = outsideGraph (splitGraph T hT G) ∧
    internalEdgeCount (internalGraph (splitGraph T hT H)) =
      internalEdgeCount (internalGraph (splitGraph T hT G)) ∧
    ∀ w, crossColumn (splitGraph T hT H) w = crossColumn (splitGraph T hT G) w}

abbrev Model (G : GraphState n d) :=
  GraphTripleCell (outsideGraph (splitGraph T hT G))
    (internalEdgeCount (internalGraph (splitGraph T hT G)))
    (leftDegree (splitGraph T hT G)) (crossColumn (splitGraph T hT G))

def referenceModel (G : GraphState n d) : Model T hT G :=
  ⟨splitGraph T hT G, rfl, rfl, (fun _ => rfl), (fun _ => rfl)⟩

def toModel (G : GraphState n d) (H : Cell T hT G) : Model T hT G :=
  ⟨splitGraph T hT H.val, H.property.1, H.property.2.1, by
    intro v
    rw [leftDegree_eq_degree, leftDegree_eq_degree, splitGraph_degree,
      splitGraph_degree], H.property.2.2⟩

def modelState (G : GraphState n d) (H : Model T hT G) : GraphState n d :=
  (stateEquiv T hT d).symm ⟨H.val, by
    intro v
    rw [degreeCount_eq_degree,
      graphCell_degrees_eq H (referenceModel T hT G) v]
    exact splitGraph_degree T hT G v⟩

@[simp] theorem splitGraph_modelState (G : GraphState n d) (H : Model T hT G) :
    splitGraph T hT (modelState T hT G H) = H.val := by
  change ((stateEquiv T hT d) ((stateEquiv T hT d).symm _)).val = H.val
  simp only [Equiv.apply_symm_apply]

def fromModel (G : GraphState n d) (H : Model T hT G) : Cell T hT G :=
  ⟨modelState T hT G H, by
    rw [splitGraph_modelState]
    exact ⟨H.property.1, H.property.2.1, H.property.2.2.2⟩⟩

def cellEquiv (G : GraphState n d) : Cell T hT G ≃ Model T hT G where
  toFun := toModel T hT G
  invFun := fromModel T hT G
  left_inv H := by
    apply Subtype.ext
    apply (stateEquiv T hT d).injective
    apply Subtype.ext
    exact splitGraph_modelState T hT G (toModel T hT G H)
  right_inv H := by
    apply Subtype.ext
    exact splitGraph_modelState T hT G H

def referenceCell (G : GraphState n d) : Cell T hT G :=
  ⟨G, rfl, rfl, fun _ => rfl⟩

def matrixEquiv (G : GraphState n d) : Cell T hT G ≃
    AugmentedMatrix (Outside T)
      (internalEdgeCount (internalGraph (splitGraph T hT G)))
      (leftDegree (splitGraph T hT G)) (crossColumn (splitGraph T hT G)) :=
  (cellEquiv T hT G).trans (graphTripleMatrixEquiv _ _
    (internalEdgeCount_le_three _) _ _
    (rowOffset_le_of_nonempty ⟨graphToCell (referenceModel T hT G)⟩))

def pair (i : Fin 3) : Finset (Fin n) :=
  (complementaryPair (W := Outside T) i).map (splitEquiv T hT).toEmbedding

@[simp] theorem split_mem_pair (i : Fin 3) (v : Fin 3 ⊕ Outside T) :
    splitEquiv T hT v ∈ pair T hT i ↔ v ∈ complementaryPair i := by
  classical
  simp [pair]

theorem pair_eq_erase (i : Fin 3) :
    pair T hT i = T.erase (splitEquiv T hT (Sum.inl i)) := by
  classical
  ext v
  obtain ⟨x, rfl⟩ := (splitEquiv T hT).surjective v
  rw [split_mem_pair]
  cases x with
  | inl j =>
      simp only [inl_mem_complementaryPair, Finset.mem_erase,
        splitEquiv_inl_mem, and_true]
      constructor
      · intro h heq
        exact h (Sum.inl.inj ((splitEquiv T hT).injective heq))
      · intro h heq
        exact h (congrArg (fun j => splitEquiv T hT (Sum.inl j)) heq)
  | inr w =>
      simp only [inr_notMem_complementaryPair, Finset.mem_erase,
        splitEquiv_inr_not_mem, and_false]

theorem pair_card (i : Fin 3) : (pair T hT i).card = 2 := by
  rw [pair_eq_erase, Finset.card_erase_of_mem (splitEquiv_inl_mem T hT i), hT]

theorem pair_mem_powersetCard (i : Fin 3) : pair T hT i ∈ T.powersetCard 2 := by
  rw [Finset.mem_powersetCard]
  exact ⟨by rw [pair_eq_erase]; exact Finset.erase_subset _ _, pair_card T hT i⟩

theorem pair_injective : Function.Injective (pair T hT) := by
  intro i j heq
  by_contra hij
  have hi : splitEquiv T hT (Sum.inl i) ∈ pair T hT j := by
    rw [split_mem_pair]
    exact (inl_mem_complementaryPair j i).mpr hij
  rw [← heq, split_mem_pair] at hi
  simp at hi

def pairEquiv : Fin 3 ≃ T.powersetCard 2 := by
  let f : Fin 3 → T.powersetCard 2 := fun i => ⟨pair T hT i, pair_mem_powersetCard T hT i⟩
  apply Equiv.ofBijective f
  have hinj : Function.Injective f := by
    intro i j h
    exact pair_injective T hT (congrArg Subtype.val h)
  refine ⟨hinj, ?_⟩
  have hc : Fintype.card (Fin 3) = Fintype.card (T.powersetCard 2) := by
    rw [Fintype.card_coe, Finset.card_powersetCard, hT]
    rfl
  exact (Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, hc⟩ |>.2

theorem sum_leftDegree_decompose {W : Type*} [Fintype W]
    (G : SimpleGraph (Fin 3 ⊕ W)) :
    (∑ i, leftDegree G i) = 2 * internalEdgeCount (internalGraph G) +
      ∑ w, crossColumn G w := by
  simp_rw [leftDegree_decompose]
  rw [Finset.sum_add_distrib, sum_degrees, Finset.sum_comm]
  rfl

theorem cellData_iff_outsideGraph (G H : GraphState n d) :
    (outsideGraph (splitGraph T hT H) = outsideGraph (splitGraph T hT G) ∧
      internalEdgeCount (internalGraph (splitGraph T hT H)) =
        internalEdgeCount (internalGraph (splitGraph T hT G)) ∧
      ∀ w, crossColumn (splitGraph T hT H) w = crossColumn (splitGraph T hT G) w) ↔
    outsideGraph (splitGraph T hT H) = outsideGraph (splitGraph T hT G) := by
  refine ⟨And.left, fun ho => ?_⟩
  have hc : ∀ w, crossColumn (splitGraph T hT H) w =
      crossColumn (splitGraph T hT G) w := by
    intro w
    have hd := (splitGraph_degree T hT H (Sum.inr w)).trans
      (splitGraph_degree T hT G (Sum.inr w)).symm
    rw [rightDegree_decompose, rightDegree_decompose, ho] at hd
    exact Nat.add_right_cancel hd
  have hl : ∀ i, leftDegree (splitGraph T hT H) i =
      leftDegree (splitGraph T hT G) i := by
    intro i
    rw [leftDegree_eq_degree, leftDegree_eq_degree,
      splitGraph_degree, splitGraph_degree]
  have hs : (∑ i, leftDegree (splitGraph T hT H) i) =
      ∑ i, leftDegree (splitGraph T hT G) i := Finset.sum_congr rfl (fun i _ => hl i)
  rw [sum_leftDegree_decompose, sum_leftDegree_decompose] at hs
  simp_rw [hc] at hs
  exact ⟨ho, by omega, hc⟩

def outsideCellEquiv (G : GraphState n d) :
    {H : GraphState n d //
      outsideGraph (splitGraph T hT H) = outsideGraph (splitGraph T hT G)} ≃
      Cell T hT G where
  toFun H := ⟨H.val, (cellData_iff_outsideGraph T hT G H.val).mpr H.property⟩
  invFun H := ⟨H.val, H.property.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

end Problem315.TripleCellTransport

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.TripleCellVarianceGluing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace
attribute [local instance] Classical.propDecidable

namespace Problem315.PairResampling
open CellVarianceGluing

def tripleExteriorKey {n : ℕ} {d : Fin n → ℕ} (T : Finset (Fin n))
    (G : GraphState n d) : SimpleGraph {v : Fin n // v ∉ T} :=
  G.val.comap Subtype.val

end Problem315.PairResampling

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.TripleMatrixFinEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.TripleMatrixFinEquiv
open TripleInternalEncoding
attribute [local instance] Classical.propDecidable

variable {W : Type*} [Fintype W]

def augmentedEquiv (e : ℕ) (d : Fin 3 → ℕ) (c : W → ℕ) :
    AugmentedMatrix W e d c ≃
      ForcedColumns.FullMargins (margins e c) (fun i => d i - rowOffset e) where
  toFun M := ⟨fun i w => ⟨M.matrix i w, by have := M.binary i w; omega⟩,
    M.rows, M.columns⟩
  invFun M :=
    { matrix := fun i w => (M.val i w : ℕ)
      binary := fun i w => by have := (M.val i w).isLt; omega
      columns := M.property.2
      rows := M.property.1 }
  left_inv M := by apply AugmentedMatrix.ext; rfl
  right_inv M := by apply Subtype.ext; rfl

@[simp] theorem augmentedEquiv_apply_val (e : ℕ) (d : Fin 3 → ℕ) (c : W → ℕ)
    (M : AugmentedMatrix W e d c) (i : Fin 3) (w : Option W) :
    ((augmentedEquiv e d c M).val i w : ℕ) = M.matrix i w := rfl

end Problem315.TripleMatrixFinEquiv

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.TripleActualRowBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.TripleActualRowBound

open TripleCellTransport TripleInternalEncoding
attribute [local instance] Classical.propDecidable

variable {n : ℕ} {d : Fin n → ℕ}
variable (T : Finset (Fin n)) (hT : T.card = 3)

def finiteCellEquiv (G : GraphState n d) : Cell T hT G ≃
    ForcedColumns.FullMargins
      (TripleMatrixFinEquiv.margins
        (internalEdgeCount (internalGraph (splitGraph T hT G)))
        (crossColumn (splitGraph T hT G)))
      (fun i => leftDegree (splitGraph T hT G) i -
        rowOffset (internalEdgeCount (internalGraph (splitGraph T hT G)))) :=
   (matrixEquiv T hT G).trans
    (TripleMatrixFinEquiv.augmentedEquiv
      (internalEdgeCount (internalGraph (splitGraph T hT G)))
      (leftDegree (splitGraph T hT G)) (crossColumn (splitGraph T hT G)))

def exteriorCellEquiv (G : GraphState n d) :
    {H : GraphState n d // PairResampling.tripleExteriorKey T H =
      PairResampling.tripleExteriorKey T G} ≃ Cell T hT G :=
  outsideCellEquiv T hT G

end Problem315.TripleActualRowBound

end

end OAI
end


