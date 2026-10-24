-- Prove2me | Definitions.Def_OAIQWSWC001
-- name    : OAIQWSWC001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-23T16:09:59.186169+00:00
-- url     : https://prove2.me/theorems/db3b0257-9432-4bbb-9f13-8b490e68d2de
-- title:
--   OpenAI switch-chain split: definitions bundle OAIQWSWC001
-- statement:
--   One of the definitions bundles of the split of OpenAI's proof of `OAI.Problem315.switch_chain_main`: the lazy switch chain on simple graphs with a prescribed graphical degree sequence mixes in at most $2n^8$ steps, and has spectral gap at least $1/(24 n^2 \binom n4)$ when there is more than one realization. The bundle holds OpenAI's Lean definitions from the modules listed below of `lean/OAI/Probability/SwitchChain` (OpenAI, *Polynomial mixing of the switch chain for every graphical degree sequence*, OpenAI Math Release, September 25, 2026, result family 131, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a. It also holds the lemmas these definitions use in their bodies, and OpenAI's `@[simp]` lemmas about them.
--
--   This bundle carries the set of vertex pairs (`PairResampling.pairs`), total variation from the uniform law, the transposition generators and moments on uniform subset slices used in Section 6 of the paper, the unnormalized switch Laplacian of Section 7.3, and the encodings of a vertex triple's cell as a three-row binary matrix with prescribed margins (Section 4, including the extra column for the triple's internal edges).
--
--   The definitions of the published goal (`GraphState`, `SwitchStep`, `switchKernel`, `mixingTime`, `hasSpectralGapAtLeast` and the rest) come from the published bundle `Def_SwitchChain`. It imports no other bundle of this split.
--
--   Modules: `InitialTV`, `OrthogonalPairResampling`, `PairEqualityUnordered`, `PairFibers`, `PermutationGenerator`, `SliceBounds`, `SliceCoefficientAlgebra`, `SliceEquality`, `SliceGenerator`, `SliceGramAction`, `SliceGramOrbit`, `SliceMoments`, `SlicePathComparison`, `SliceSynthesis`, `SwitchLaplacian`, `TripleCellTransport`, `TripleGraphEncoding`, `TripleInternalEncoding`, `TripleMatrixEncoding`, `TripleMatrixFinEquiv`, `TriplePairFiber`, `TripleStateReindex`, `WeightedConditionalVariance`.
-- source:
--   OpenAI, Polynomial mixing of the switch chain for every graphical degree sequence, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 131; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-Mixing-of-the-Switch-Chain-for-Every-Graphical-Degree-Sequence-September-25-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability/SwitchChain at commit adc7f12

import Mathlib
import Definitions.Def_SwitchChain

section
-- module Solutions.OAIQW_Problem315.InitialTV
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315Aux

def deltaUniformTV {α : Type*} [Fintype α] (x : α) : ℝ := by
  classical
  exact (1 / 2 : ℝ) * ∑ y : α,
    |(if x = y then (1 : ℝ) else 0) - 1 / (Fintype.card α : ℝ)|

end Problem315Aux

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

def pairs (n : ℕ) : Finset (Finset (Fin n)) := Finset.univ.powersetCard 2

end PairResampling
end Problem315

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
open PairResampling
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {d : Fin n → ℕ}

theorem exists_pair_endpoints (a : Finset (Fin n)) (ha : a.card = 2) :
    ∃ p : Fin n × Fin n, p.1 ≠ p.2 ∧ a = {p.1,p.2} := by
  obtain ⟨i,j,hij,hpair⟩ := Finset.card_eq_two.mp ha
  exact ⟨(i,j),hij,hpair⟩

def endpoints (a : Finset (Fin n)) (ha : a.card = 2) : Fin n × Fin n :=
  Classical.choose (exists_pair_endpoints a ha)

end Problem315.PairEquality

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.PairFibers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Problem315.PairFibers

section Partition

variable {α : Type*} [Fintype α]

def constantSubspace (R : Setoid α) : Submodule ℝ (EuclideanSpace ℝ α) where
  carrier := {f | ∀ x y, R.r x y → f x = f y}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg x y hxy
    change f x + g x = f y + g y
    rw [hf x y hxy, hg x y hxy]
  smul_mem' := by
    intro c f hf x y hxy
    change c * f x = c * f y
    rw [hf x y hxy]

omit [Fintype α] in
@[simp] theorem mem_constantSubspace (R : Setoid α) (f : EuclideanSpace ℝ α) :
    f ∈ constantSubspace R ↔ ∀ x y, R.r x y → f x = f y := Iff.rfl

def expectation (R : Setoid α) : EuclideanSpace ℝ α →L[ℝ] EuclideanSpace ℝ α :=
  (constantSubspace R).starProjection

def cellIndicator (R : Setoid α) (x : α) : EuclideanSpace ℝ α :=
  WithLp.toLp 2 (fun y => if R.r x y then 1 else 0)

end Partition

end Problem315.PairFibers

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.PermutationGenerator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.PermutationGenerator

variable {Ω S : Type*} [Fintype Ω] [Fintype S]

def apply (τ : S → Equiv.Perm Ω) (f : Ω → ℝ) (x : Ω) : ℝ :=
  ∑ s, (f x - f (τ s x))

def operator (τ : S → Equiv.Perm Ω) :
    EuclideanSpace ℝ Ω →ₗ[ℝ] EuclideanSpace ℝ Ω where
  toFun f := WithLp.toLp 2 (apply τ f)
  map_add' f g := by
    ext x
    change (∑ s, ((f x + g x) - (f (τ s x) + g (τ s x)))) =
      (∑ s, (f x - f (τ s x))) + ∑ s, (g x - g (τ s x))
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s hs
    ring
  map_smul' c f := by
    ext x
    change (∑ s, (c * f x - c * f (τ s x))) = c * ∑ s, (f x - f (τ s x))
    simp only [mul_sub, Finset.mul_sum]

omit [Fintype Ω] in
@[simp] theorem operator_apply (τ : S → Equiv.Perm Ω)
    (f : EuclideanSpace ℝ Ω) (x : Ω) : operator τ f x = apply τ f x := rfl

end Problem315.PermutationGenerator

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.SliceBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem315.SliceBounds

def equalityProbability (N q r : ℝ) : ℝ :=
  (q * (q - 1) + r * (r - 1)) / (N * (N - 1))

end Problem315.SliceBounds

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

def linearPair (u : V → ℝ) (i j : V) : ℝ :=
  if i = j then 0 else u i + u j

def rowSum (c : V → V → ℝ) (i : V) : ℝ := ∑ j, c i j

def outside (i j : V) : Finset V := (Finset.univ.erase i).erase j

def meetingSum (c : V → V → ℝ) (i j : V) : ℝ :=
  ∑ k ∈ outside i j, (c i k + c j k)

def disjointSum (c : V → V → ℝ) (i j : V) : ℝ :=
  (∑ k ∈ outside i j, ∑ l ∈ outside i j, c k l) / 2

include sectionFintypeV in
@[simp] theorem linearPair_diag (u : V → ℝ) (i : V) : linearPair u i i = 0 := by
  have retainedsectionFintypeV := sectionFintypeV
  simp [linearPair]

def intersectionAction (a b d : ℝ) (c : V → V → ℝ) (i j : V) : ℝ :=
  if i = j then 0 else a * c i j + b * meetingSum c i j + d * disjointSum c i j

end Problem315.SliceCoefficients

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.SliceEquality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.SliceEquality

def equalityIndicator {α : Type*} (x : α → ℝ) (i j : α) : ℝ := by
  classical
  exact if x i = x j then 1 else 0

def centeredEquality {α : Type*} (x : α → ℝ) (p : ℝ) (i j : α) : ℝ :=
  equalityIndicator x i j - p

def offDiagonal {α : Type*} [DecidableEq α] (z : α → α → ℝ) (i j : α) : ℝ :=
  if i = j then 0 else z i j

end Problem315.SliceEquality

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.SliceGenerator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.SliceGenerator

def generator {α : Type*} [Fintype α] [DecidableEq α]
    (f : (α → ℝ) → ℝ) (x : α → ℝ) : ℝ :=
  (1 / 4 : ℝ) * ∑ i, ∑ j, (f x - f (x ∘ Equiv.swap i j))

def generatorLinearMap {α : Type*} [Fintype α] [DecidableEq α] :
    ((α → ℝ) → ℝ) →ₗ[ℝ] ((α → ℝ) → ℝ) where
  toFun := generator
  map_add' f g := by
    ext x
    simp only [generator, Pi.add_apply]
    simp_rw [show ∀ a b c d : ℝ, a + b - (c + d) = (a-c) + (b-d) by intros; ring]
    simp [Finset.sum_add_distrib, mul_add]
  map_smul' c f := by
    ext x
    simp only [generator, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    simp_rw [← mul_sub, ← Finset.mul_sum]
    ring

end Problem315.SliceGenerator

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.SliceGramAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.SliceCoefficients

variable {V : Type*} [Fintype V] [DecidableEq V]

def orbitKernel (a b d : ℝ) (i j k l : V) : ℝ :=
  if (k = i ∧ l = j) ∨ (k = j ∧ l = i) then a
  else if k = i ∨ k = j ∨ l = i ∨ l = j then b else d

end Problem315.SliceCoefficients

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.SliceMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Problem315.SliceMoments

variable {V : Type*} [sectionDecidableEqV : DecidableEq V]

def average (U : Finset V) (q : ℕ) (f : Finset V → ℝ) : ℝ :=
  (∑ S ∈ U.powersetCard q, f S) / (U.card.choose q : ℝ)

def coord (i : V) (S : Finset V) : ℝ := if i ∈ S then 1 else 0

@[simp] theorem coord_sq (i : V) (S : Finset V) : (coord i S)^2 = coord i S := by
  by_cases hi : i ∈ S <;> simp [coord, hi]

include sectionDecidableEqV in
@[simp] theorem average_add (U : Finset V) (q : ℕ) (f g : Finset V → ℝ) :
    average U q (fun S => f S + g S) = average U q f + average U q g := by
  have retainedsectionDecidableEqV := sectionDecidableEqV
  simp [average, Finset.sum_add_distrib, add_div]

include sectionDecidableEqV in
@[simp] theorem average_mul_left (U : Finset V) (q : ℕ) (c : ℝ) (f : Finset V → ℝ) :
    average U q (fun S => c * f S) = c * average U q f := by
  have retainedsectionDecidableEqV := sectionDecidableEqV
  simp [average, ← Finset.mul_sum, mul_div_assoc]

include sectionDecidableEqV in
@[simp] theorem average_const (U : Finset V) (q : ℕ) (hq : q ≤ U.card) (c : ℝ) :
    average U q (fun _ => c) = c := by
  have retainedsectionDecidableEqV := sectionDecidableEqV
  have hden : (U.card.choose q : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hq).ne'
  simp [average, Finset.card_powersetCard, hden]

include sectionDecidableEqV in
@[simp] theorem average_sub (U : Finset V) (q : ℕ) (f g : Finset V → ℝ) :
    average U q (fun S => f S - g S) = average U q f - average U q g := by
  have retainedsectionDecidableEqV := sectionDecidableEqV
  simp [average, Finset.sum_sub_distrib, sub_div]

@[simp] theorem coord_map_embedding {W : Type*} [DecidableEq W]
    (e : V ↪ W) (i : V) (S : Finset V) :
    coord (e i) (S.map e) = coord i S := by
  simp [coord]

abbrev State (U : Finset V) (q : ℕ) := ↥(U.powersetCard q)

def vector (U : Finset V) (q : ℕ) (f : Finset V → ℝ) : EuclideanSpace ℝ (State U q) :=
  WithLp.toLp 2 (fun S => f S.val)

end Problem315.SliceMoments

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

def pairEquality (P S : Finset α) : ℝ :=
  if (P ∩ S).card = 0 ∨ (P ∩ S).card = 2 then 1 else 0

end Problem315.SliceGramOrbit

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.SlicePathComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.SlicePathComparison

variable {α : Type*} [Fintype α] [DecidableEq α]

def swaps : Finset (Equiv.Perm α) := by
  classical
  exact Finset.univ.filter Equiv.Perm.IsSwap

@[simp] theorem mem_swaps (σ : Equiv.Perm α) : σ ∈ swaps ↔ Equiv.Perm.IsSwap σ := by
  classical
  simp [swaps]

end Problem315.SlicePathComparison

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.SliceSynthesis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.SliceSynthesis
open SliceCoefficients

variable {V E : Type*} [Fintype V] [sectionDecidableEqV : DecidableEq V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

abbrev Coeff (V : Type*) [Fintype V] := EuclideanSpace ℝ (V × V)

def ofMatrix (c : V → V → ℝ) : Coeff V :=
  WithLp.toLp 2 (fun p => c p.1 p.2)

include sectionDecidableEqV in
@[simp] theorem ofMatrix_apply (c : V → V → ℝ) (i j : V) :
    ofMatrix c (i,j) = c i j := by
  have retainedsectionDecidableEqV := sectionDecidableEqV
  exact rfl

def synthesis (z : V → V → E) : Coeff V →ₗ[ℝ] E where
  toFun c := ∑ i, ∑ j, c (i,j) • z i j
  map_add' c d := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a c := by simp [mul_smul, Finset.smul_sum]

include sectionDecidableEqV in
@[simp] theorem synthesis_ofMatrix (z : V → V → E) (c : V → V → ℝ) :
    synthesis z (ofMatrix c) = ∑ i, ∑ j, c i j • z i j := by
  have retainedsectionDecidableEqV := sectionDecidableEqV
  exact rfl

def symMatrix (c : Coeff V) (i j : V) : ℝ :=
  if i = j then 0 else (c (i,j) + c (j,i)) / 2

@[simp] theorem symMatrix_diag (c : Coeff V) (i : V) : symMatrix c i i = 0 := by
  simp [symMatrix]

end Problem315.SliceSynthesis

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.SwitchLaplacian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace Problem315

def switchLaplacian (n : Nat) (d : Fin n → Nat)
    (f : GraphState n d → ℝ) (G : GraphState n d) : ℝ :=
  ∑ H ∈ allGraphStates n d, if SwitchStep n d G H then f G - f H else 0

end Problem315

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.TripleInternalEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Problem315.TripleInternalEncoding
attribute [local instance] Classical.propDecidable

def edgeBit (G : SimpleGraph (Fin 3)) (u v : Fin 3) : ℕ :=
  if G.Adj u v then 1 else 0

def internalEdgeCount (G : SimpleGraph (Fin 3)) : ℕ :=
  edgeBit G 0 1 + edgeBit G 0 2 + edgeBit G 1 2

theorem degree_zero (G : SimpleGraph (Fin 3)) :
    graphDegree G 0 = edgeBit G 0 1 + edgeBit G 0 2 := by
  classical
  simp only [graphDegree, Finset.card_eq_sum_ones, Finset.sum_filter, Fin.sum_univ_three]
  simp [edgeBit]

theorem degree_one (G : SimpleGraph (Fin 3)) :
    graphDegree G 1 = edgeBit G 0 1 + edgeBit G 1 2 := by
  classical
  simp only [graphDegree, Finset.card_eq_sum_ones, Finset.sum_filter, Fin.sum_univ_three]
  simp [edgeBit, G.adj_comm]

theorem degree_two (G : SimpleGraph (Fin 3)) :
    graphDegree G 2 = edgeBit G 0 2 + edgeBit G 1 2 := by
  classical
  simp only [graphDegree, Finset.card_eq_sum_ones, Finset.sum_filter, Fin.sum_univ_three]
  simp [edgeBit, G.adj_comm]

theorem edgeBit_le_one (G : SimpleGraph (Fin 3)) (u v : Fin 3) :
    edgeBit G u v ≤ 1 := by
  unfold edgeBit
  split <;> omega

theorem edgeBit_eq_iff (G H : SimpleGraph (Fin 3)) (u v : Fin 3) :
    edgeBit G u v = edgeBit H u v ↔ (G.Adj u v ↔ H.Adj u v) := by
  by_cases hg : G.Adj u v <;> by_cases hh : H.Adj u v <;> simp [edgeBit, hg, hh]

theorem degree_injective : Function.Injective
    (fun G : SimpleGraph (Fin 3) => graphDegree G) := by
  intro G H h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  change graphDegree G 0 = graphDegree H 0 at h0
  change graphDegree G 1 = graphDegree H 1 at h1
  change graphDegree G 2 = graphDegree H 2 at h2
  rw [degree_zero, degree_zero] at h0
  rw [degree_one, degree_one] at h1
  rw [degree_two, degree_two] at h2
  have h01 : G.Adj 0 1 ↔ H.Adj 0 1 :=
    (edgeBit_eq_iff G H 0 1).mp (by omega)
  have h02 : G.Adj 0 2 ↔ H.Adj 0 2 :=
    (edgeBit_eq_iff G H 0 2).mp (by omega)
  have h12 : G.Adj 1 2 ↔ H.Adj 1 2 :=
    (edgeBit_eq_iff G H 1 2).mp (by omega)
  have h10 : G.Adj 1 0 ↔ H.Adj 1 0 :=
    (G.adj_comm 1 0).trans (h01.trans (H.adj_comm 0 1))
  have h20 : G.Adj 2 0 ↔ H.Adj 2 0 :=
    (G.adj_comm 2 0).trans (h02.trans (H.adj_comm 0 2))
  have h21 : G.Adj 2 1 ↔ H.Adj 2 1 :=
    (G.adj_comm 2 1).trans (h12.trans (H.adj_comm 1 2))
  ext u v
  fin_cases u <;> fin_cases v <;> simp_all

theorem internalEdgeCount_le_three (G : SimpleGraph (Fin 3)) :
    internalEdgeCount G ≤ 3 := by
  have h01 := edgeBit_le_one G 0 1
  have h02 := edgeBit_le_one G 0 2
  have h12 := edgeBit_le_one G 1 2
  unfold internalEdgeCount
  omega

theorem sum_degrees (G : SimpleGraph (Fin 3)) :
    ∑ v, graphDegree G v = 2 * internalEdgeCount G := by
  rw [Fin.sum_univ_three, degree_zero, degree_one, degree_two]
  unfold internalEdgeCount
  omega

theorem degree_le_internalEdgeCount (G : SimpleGraph (Fin 3)) (v : Fin 3) :
    graphDegree G v ≤ internalEdgeCount G := by
  fin_cases v
  · change graphDegree G 0 ≤ _
    rw [degree_zero]
    unfold internalEdgeCount
    omega
  · change graphDegree G 1 ≤ _
    rw [degree_one]
    unfold internalEdgeCount
    omega
  · change graphDegree G 2 ≤ _
    rw [degree_two]
    unfold internalEdgeCount
    omega

theorem degree_le_two (G : SimpleGraph (Fin 3)) (v : Fin 3) :
    graphDegree G v ≤ 2 := by
  have h01 := edgeBit_le_one G 0 1
  have h02 := edgeBit_le_one G 0 2
  have h12 := edgeBit_le_one G 1 2
  fin_cases v
  · change graphDegree G 0 ≤ 2
    rw [degree_zero]
    omega
  · change graphDegree G 1 ≤ 2
    rw [degree_one]
    omega
  · change graphDegree G 2 ≤ 2
    rw [degree_two]
    omega

theorem one_le_degree_of_two_edges (G : SimpleGraph (Fin 3))
    (he : internalEdgeCount G = 2) (v : Fin 3) :
    1 ≤ graphDegree G v := by
  have h01 := edgeBit_le_one G 0 1
  have h02 := edgeBit_le_one G 0 2
  have h12 := edgeBit_le_one G 1 2
  unfold internalEdgeCount at he
  fin_cases v
  · change 1 ≤ graphDegree G 0
    rw [degree_zero]
    omega
  · change 1 ≤ graphDegree G 1
    rw [degree_one]
    omega
  · change 1 ≤ graphDegree G 2
    rw [degree_two]
    omega

theorem degree_eq_zero_of_no_edges (G : SimpleGraph (Fin 3))
    (he : internalEdgeCount G = 0) (v : Fin 3) : graphDegree G v = 0 := by
  have h := degree_le_internalEdgeCount G v
  omega

theorem degree_eq_two_of_three_edges (G : SimpleGraph (Fin 3))
    (he : internalEdgeCount G = 3) (v : Fin 3) : graphDegree G v = 2 := by
  have h01 := edgeBit_le_one G 0 1
  have h02 := edgeBit_le_one G 0 2
  have h12 := edgeBit_le_one G 1 2
  unfold internalEdgeCount at he
  fin_cases v
  · change graphDegree G 0 = 2
    rw [degree_zero]
    omega
  · change graphDegree G 1 = 2
    rw [degree_one]
    omega
  · change graphDegree G 2 = 2
    rw [degree_two]
    omega

def extraColumn (G : SimpleGraph (Fin 3)) (v : Fin 3) : ℕ :=
  if internalEdgeCount G = 1 then graphDegree G v
  else if internalEdgeCount G = 2 then graphDegree G v - 1 else 0

theorem extraColumn_le_one (G : SimpleGraph (Fin 3)) (v : Fin 3) :
    extraColumn G v ≤ 1 := by
  unfold extraColumn
  split
  · have h := degree_le_internalEdgeCount G v
    omega
  · split
    · have h := degree_le_two G v
      omega
    · omega

theorem sum_extraColumn (G : SimpleGraph (Fin 3)) :
    ∑ v, extraColumn G v =
      if internalEdgeCount G = 1 then 2 else if internalEdgeCount G = 2 then 1 else 0 := by
  by_cases h1 : internalEdgeCount G = 1
  · simp only [extraColumn, h1, ite_true]
    rw [sum_degrees, h1]
  · by_cases h2 : internalEdgeCount G = 2
    · simp only [extraColumn, h2, show (2 : ℕ) ≠ 1 by decide, ite_false, ite_true, Fin.sum_univ_three]
      have hsum := sum_degrees G
      rw [Fin.sum_univ_three, h2] at hsum
      have h0 := one_le_degree_of_two_edges G h2 0
      have h1 := one_le_degree_of_two_edges G h2 1
      have h2 := one_le_degree_of_two_edges G h2 2
      omega
    · simp [extraColumn, h1, h2]

theorem degree_from_extraColumn (G : SimpleGraph (Fin 3)) (v : Fin 3) :
    graphDegree G v =
      if internalEdgeCount G = 0 then 0
      else if internalEdgeCount G = 1 then extraColumn G v
      else if internalEdgeCount G = 2 then extraColumn G v + 1 else 2 := by
  have he := internalEdgeCount_le_three G
  have hcases : internalEdgeCount G = 0 ∨ internalEdgeCount G = 1 ∨
      internalEdgeCount G = 2 ∨ internalEdgeCount G = 3 := by omega
  rcases hcases with h | h | h | h
  · simp [h, degree_eq_zero_of_no_edges G h v]
  · simp [h, extraColumn]
  · have hd := one_le_degree_of_two_edges G h v
    simp [h, extraColumn]
    omega
  · simp [h, degree_eq_two_of_three_edges G h v]

theorem encoded_graph_injective : Function.Injective
    (fun G : SimpleGraph (Fin 3) => (internalEdgeCount G, extraColumn G)) := by
  intro G H h
  have he : internalEdgeCount G = internalEdgeCount H := congrArg Prod.fst h
  have hx : extraColumn G = extraColumn H := congrArg Prod.snd h
  apply degree_injective
  funext v
  change graphDegree G v = graphDegree H v
  rw [degree_from_extraColumn, degree_from_extraColumn, he, hx]

def oneEdgeGraph (x : Fin 3 → ℕ) : SimpleGraph (Fin 3) :=
  SimpleGraph.fromRel (fun u v => x u = 1 ∧ x v = 1)

def twoEdgeGraph (x : Fin 3 → ℕ) : SimpleGraph (Fin 3) :=
  SimpleGraph.fromRel (fun u v => x u = 1 ∨ x v = 1)

theorem oneEdgeGraph_spec (x : Fin 3 → ℕ) (hx : ∀ v, x v ≤ 1)
    (hs : ∑ v, x v = 2) :
    internalEdgeCount (oneEdgeGraph x) = 1 ∧ graphDegree (oneEdgeGraph x) = x := by
  have h0 := hx 0
  have h1 := hx 1
  have h2 := hx 2
  rw [Fin.sum_univ_three] at hs
  have hcases : (x 0 = 0 ∧ x 1 = 1 ∧ x 2 = 1) ∨
      (x 0 = 1 ∧ x 1 = 0 ∧ x 2 = 1) ∨
      (x 0 = 1 ∧ x 1 = 1 ∧ x 2 = 0) := by omega
  rcases hcases with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
  all_goals
    have hd0 : graphDegree (oneEdgeGraph x) 0 = x 0 := by
      rw [degree_zero]
      simp [edgeBit, oneEdgeGraph, SimpleGraph.fromRel_adj, h0, h1, h2]
    have hd1 : graphDegree (oneEdgeGraph x) 1 = x 1 := by
      rw [degree_one]
      simp [edgeBit, oneEdgeGraph, SimpleGraph.fromRel_adj, h0, h1, h2]
    have hd2 : graphDegree (oneEdgeGraph x) 2 = x 2 := by
      rw [degree_two]
      simp [edgeBit, oneEdgeGraph, SimpleGraph.fromRel_adj, h0, h1, h2]
    refine ⟨?_, ?_⟩
    · simp [internalEdgeCount, edgeBit, oneEdgeGraph, SimpleGraph.fromRel_adj, h0, h1, h2]
    · funext v
      fin_cases v
      · exact hd0
      · exact hd1
      · exact hd2

theorem twoEdgeGraph_spec (x : Fin 3 → ℕ) (hx : ∀ v, x v ≤ 1)
    (hs : ∑ v, x v = 1) :
    internalEdgeCount (twoEdgeGraph x) = 2 ∧
      graphDegree (twoEdgeGraph x) = fun v => x v + 1 := by
  have h0 := hx 0
  have h1 := hx 1
  have h2 := hx 2
  rw [Fin.sum_univ_three] at hs
  have hcases : (x 0 = 1 ∧ x 1 = 0 ∧ x 2 = 0) ∨
      (x 0 = 0 ∧ x 1 = 1 ∧ x 2 = 0) ∨
      (x 0 = 0 ∧ x 1 = 0 ∧ x 2 = 1) := by omega
  rcases hcases with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
  all_goals
    have hd0 : graphDegree (twoEdgeGraph x) 0 = x 0 + 1 := by
      rw [degree_zero]
      simp [edgeBit, twoEdgeGraph, SimpleGraph.fromRel_adj, h0, h1, h2]
    have hd1 : graphDegree (twoEdgeGraph x) 1 = x 1 + 1 := by
      rw [degree_one]
      simp [edgeBit, twoEdgeGraph, SimpleGraph.fromRel_adj, h0, h1, h2]
    have hd2 : graphDegree (twoEdgeGraph x) 2 = x 2 + 1 := by
      rw [degree_two]
      simp [edgeBit, twoEdgeGraph, SimpleGraph.fromRel_adj, h0, h1, h2]
    refine ⟨?_, ?_⟩
    · simp [internalEdgeCount, edgeBit, twoEdgeGraph, SimpleGraph.fromRel_adj, h0, h1, h2]
    · funext v
      fin_cases v
      · exact hd0
      · exact hd1
      · exact hd2

def columnSum (e : ℕ) : ℕ := if e = 1 then 2 else if e = 2 then 1 else 0

theorem exists_graph_of_column (e : ℕ) (he : e ≤ 3) (x : Fin 3 → ℕ)
    (hx : ∀ v, x v ≤ 1) (hs : ∑ v, x v = columnSum e) :
    ∃ G : SimpleGraph (Fin 3), internalEdgeCount G = e ∧ extraColumn G = x := by
  have hcases : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 := by omega
  rcases hcases with rfl | rfl | rfl | rfl
  · have hx0 : ∀ v, x v = 0 := by
      have hs0 : ∑ v, x v = 0 := by simpa [columnSum] using hs
      intro v
      exact Finset.sum_eq_zero_iff.mp hs0 v (Finset.mem_univ v)
    refine ⟨⊥, ?_, ?_⟩
    · simp [internalEdgeCount, edgeBit]
    · funext v
      simp [extraColumn, internalEdgeCount, edgeBit, hx0]
  · have hs2 : ∑ v, x v = 2 := by simpa [columnSum] using hs
    obtain ⟨he, hd⟩ := oneEdgeGraph_spec x hx hs2
    refine ⟨oneEdgeGraph x, he, ?_⟩
    funext v
    simp only [extraColumn, he, ite_true, hd]
  · have hs1 : ∑ v, x v = 1 := by simpa [columnSum] using hs
    obtain ⟨he, hd⟩ := twoEdgeGraph_spec x hx hs1
    refine ⟨twoEdgeGraph x, he, ?_⟩
    funext v
    simp [extraColumn, he, hd]
  · have hx0 : ∀ v, x v = 0 := by
      have hs0 : ∑ v, x v = 0 := by simpa [columnSum] using hs
      intro v
      exact Finset.sum_eq_zero_iff.mp hs0 v (Finset.mem_univ v)
    refine ⟨⊤, ?_, ?_⟩
    · simp [internalEdgeCount, edgeBit]
    · funext v
      simp [extraColumn, internalEdgeCount, edgeBit, hx0]

abbrev Column (e : ℕ) :=
  {x : Fin 3 → ℕ // (∀ v, x v ≤ 1) ∧ ∑ v, x v = columnSum e}

def fixedEdgeEncodingEquiv (e : ℕ) (he : e ≤ 3) :
    {G : SimpleGraph (Fin 3) // internalEdgeCount G = e} ≃ Column e := by
  let F : {G : SimpleGraph (Fin 3) // internalEdgeCount G = e} → Column e :=
    fun G => ⟨extraColumn G.val, extraColumn_le_one G.val, by
      simpa only [columnSum, G.property] using sum_extraColumn G.val⟩
  apply Equiv.ofBijective F
  constructor
  · intro G H h
    apply Subtype.ext
    apply encoded_graph_injective
    apply Prod.ext
    · exact G.property.trans H.property.symm
    · exact congrArg Subtype.val h
  · intro x
    obtain ⟨G, hG, hx⟩ := exists_graph_of_column e he x.val x.property.1 x.property.2
    refine ⟨⟨G, hG⟩, ?_⟩
    apply Subtype.ext
    exact hx

end Problem315.TripleInternalEncoding

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.TripleMatrixEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace Problem315.TripleInternalEncoding

def rowOffset (e : ℕ) : ℕ := if e = 2 then 1 else if e = 3 then 2 else 0

theorem degree_eq_extra_add_offset (G : SimpleGraph (Fin 3)) (v : Fin 3) :
    graphDegree G v = extraColumn G v + rowOffset (internalEdgeCount G) := by
  have he := internalEdgeCount_le_three G
  have hcases : internalEdgeCount G = 0 ∨ internalEdgeCount G = 1 ∨
      internalEdgeCount G = 2 ∨ internalEdgeCount G = 3 := by omega
  rcases hcases with h | h | h | h
  · simp [extraColumn, rowOffset, h, degree_eq_zero_of_no_edges G h v]
  · simp [extraColumn, rowOffset, h]
  · have hd := one_le_degree_of_two_edges G h v
    simp [extraColumn, rowOffset, h]
    omega
  · simp [extraColumn, rowOffset, h, degree_eq_two_of_three_edges G h v]

variable (W : Type*) [Fintype W]

@[ext]
structure TripleCell (e : ℕ) (d : Fin 3 → ℕ) (c : W → ℕ) where
  outside : Fin 3 → W → ℕ
  inside : SimpleGraph (Fin 3)
  edge_count : internalEdgeCount inside = e
  binary : ∀ v w, outside v w ≤ 1
  columns : ∀ w, ∑ v, outside v w = c w
  rows : ∀ v, (∑ w, outside v w) + graphDegree inside v = d v

@[ext]
structure AugmentedMatrix (e : ℕ) (d : Fin 3 → ℕ) (c : W → ℕ) where
  matrix : Fin 3 → Option W → ℕ
  binary : ∀ v w, matrix v w ≤ 1
  columns : ∀ w, ∑ v, matrix v w = w.elim (columnSum e) c
  rows : ∀ v, (∑ w, matrix v w) = d v - rowOffset e

variable {W}

def encodeCell {e : ℕ} {d : Fin 3 → ℕ} {c : W → ℕ}
    (A : TripleCell W e d c) : AugmentedMatrix W e d c where
  matrix v w := w.elim (extraColumn A.inside v) (A.outside v)
  binary v w := by
    cases w with
    | none => exact extraColumn_le_one A.inside v
    | some w => exact A.binary v w
  columns w := by
    cases w with
    | none =>
        simpa only [Option.elim_none, A.edge_count, columnSum] using sum_extraColumn A.inside
    | some w => exact A.columns w
  rows v := by
    rw [Fintype.sum_option]
    dsimp only [Option.elim_none, Option.elim_some]
    have hrow := A.rows v
    rw [degree_eq_extra_add_offset, A.edge_count] at hrow
    omega

def internalOfAugmented {e : ℕ} {d : Fin 3 → ℕ} {c : W → ℕ}
    (he : e ≤ 3) (A : AugmentedMatrix W e d c) :
    {G : SimpleGraph (Fin 3) // internalEdgeCount G = e} :=
  (fixedEdgeEncodingEquiv e he).symm
    ⟨fun v => A.matrix v none, (fun v => A.binary v none), A.columns none⟩

theorem extraColumn_internalOfAugmented {e : ℕ} {d : Fin 3 → ℕ} {c : W → ℕ}
    (he : e ≤ 3) (A : AugmentedMatrix W e d c) :
    extraColumn (internalOfAugmented he A).val = fun v => A.matrix v none := by
  exact congrArg Subtype.val ((fixedEdgeEncodingEquiv e he).apply_symm_apply
    ⟨fun v => A.matrix v none, (fun v => A.binary v none), A.columns none⟩)

def decodeMatrix {e : ℕ} {d : Fin 3 → ℕ} {c : W → ℕ}
    (he : e ≤ 3) (hd : ∀ v, rowOffset e ≤ d v)
    (A : AugmentedMatrix W e d c) : TripleCell W e d c where
  outside v w := A.matrix v (some w)
  inside := (internalOfAugmented he A).val
  edge_count := (internalOfAugmented he A).property
  binary v w := A.binary v (some w)
  columns w := A.columns (some w)
  rows v := by
    rw [degree_eq_extra_add_offset, (internalOfAugmented he A).property,
      extraColumn_internalOfAugmented]
    have hrow := A.rows v
    rw [Fintype.sum_option] at hrow
    dsimp
    have hmargin := hd v
    omega

@[simp] theorem decode_encode {e : ℕ} {d : Fin 3 → ℕ} {c : W → ℕ}
    (he : e ≤ 3) (hd : ∀ v, rowOffset e ≤ d v) (A : TripleCell W e d c) :
    decodeMatrix he hd (encodeCell A) = A := by
  apply TripleCell.ext
  · rfl
  · apply encoded_graph_injective
    apply Prod.ext
    · exact (internalOfAugmented he (encodeCell A)).property.trans A.edge_count.symm
    · exact extraColumn_internalOfAugmented he (encodeCell A)

@[simp] theorem encode_decode {e : ℕ} {d : Fin 3 → ℕ} {c : W → ℕ}
    (he : e ≤ 3) (hd : ∀ v, rowOffset e ≤ d v) (A : AugmentedMatrix W e d c) :
    encodeCell (decodeMatrix he hd A) = A := by
  apply AugmentedMatrix.ext
  funext v w
  cases w with
  | none => exact congrFun (extraColumn_internalOfAugmented he A) v
  | some w => rfl

def tripleMatrixEquiv (e : ℕ) (he : e ≤ 3) (d : Fin 3 → ℕ) (c : W → ℕ)
    (hd : ∀ v, rowOffset e ≤ d v) :
    TripleCell W e d c ≃ AugmentedMatrix W e d c where
  toFun := encodeCell
  invFun := decodeMatrix he hd
  left_inv := decode_encode he hd
  right_inv := encode_decode he hd

theorem rowOffset_le_of_nonempty {e : ℕ} {d : Fin 3 → ℕ} {c : W → ℕ}
    (h : Nonempty (TripleCell W e d c)) : ∀ v, rowOffset e ≤ d v := by
  obtain ⟨A⟩ := h
  intro v
  have hrow := A.rows v
  rw [degree_eq_extra_add_offset, A.edge_count] at hrow
  omega

end Problem315.TripleInternalEncoding

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.TripleGraphEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace Problem315.TripleInternalEncoding
attribute [local instance] Classical.propDecidable

variable {W : Type*} [Fintype W]

def adjacencyBit {V : Type*} (G : SimpleGraph V) (u v : V) : ℕ :=
  if G.Adj u v then 1 else 0

def leftDegree (G : SimpleGraph (Fin 3 ⊕ W)) (v : Fin 3) : ℕ :=
  ∑ w, adjacencyBit G (Sum.inl v) w

def crossColumn (G : SimpleGraph (Fin 3 ⊕ W)) (w : W) : ℕ :=
  ∑ v : Fin 3, adjacencyBit G (Sum.inl v) (Sum.inr w)

def internalGraph (G : SimpleGraph (Fin 3 ⊕ W)) : SimpleGraph (Fin 3) :=
  G.comap Sum.inl

def outsideGraph (G : SimpleGraph (Fin 3 ⊕ W)) : SimpleGraph W :=
  G.comap Sum.inr

theorem leftDegree_eq_degree (G : SimpleGraph (Fin 3 ⊕ W)) (v : Fin 3) :
    leftDegree G v = G.degree (Sum.inl v) := by
  simpa only [leftDegree, adjacencyBit, Nat.cast_id] using
    (G.degree_eq_sum_if_adj (R := ℕ) (Sum.inl v)).symm

theorem leftDegree_decompose (G : SimpleGraph (Fin 3 ⊕ W)) (v : Fin 3) :
    leftDegree G v = graphDegree (internalGraph G) v +
      ∑ w, adjacencyBit G (Sum.inl v) (Sum.inr w) := by
  simp only [leftDegree, Fintype.sum_sum_type, graphDegree, Finset.card_eq_sum_ones,
    Finset.sum_filter, internalGraph, SimpleGraph.comap_adj, adjacencyBit]

abbrev GraphTripleCell (O : SimpleGraph W) (e : ℕ) (d : Fin 3 → ℕ) (c : W → ℕ) :=
  {G : SimpleGraph (Fin 3 ⊕ W) // outsideGraph G = O ∧
    internalEdgeCount (internalGraph G) = e ∧
    (∀ v, leftDegree G v = d v) ∧ ∀ w, crossColumn G w = c w}

variable {O : SimpleGraph W} {e : ℕ} {d : Fin 3 → ℕ} {c : W → ℕ}

def graphToCell (G : GraphTripleCell O e d c) : TripleCell W e d c where
  outside v w := adjacencyBit G.val (Sum.inl v) (Sum.inr w)
  inside := internalGraph G.val
  edge_count := G.property.2.1
  binary v w := by unfold adjacencyBit; split <;> omega
  columns w := G.property.2.2.2 w
  rows v := by
    have h := G.property.2.2.1 v
    rw [leftDegree_decompose] at h
    omega

def assembleGraph (O : SimpleGraph W) (A : TripleCell W e d c) :
    SimpleGraph (Fin 3 ⊕ W) where
  Adj x y := match x, y with
    | Sum.inl v, Sum.inl u => A.inside.Adj v u
    | Sum.inl v, Sum.inr w => A.outside v w = 1
    | Sum.inr w, Sum.inl v => A.outside v w = 1
    | Sum.inr w, Sum.inr z => O.Adj w z
  symm := by
    constructor
    intro x y h
    cases x with
    | inl v =>
        cases y with
        | inl u => exact A.inside.symm.symm v u h
        | inr w => exact h
    | inr w =>
        cases y with
        | inl v => exact h
        | inr z => exact O.symm.symm w z h
  loopless := by
    constructor
    intro x h
    cases x with
    | inl v => exact A.inside.loopless.irrefl v h
    | inr w => exact O.loopless.irrefl w h

@[simp] theorem internalGraph_assemble (O : SimpleGraph W) (A : TripleCell W e d c) :
    internalGraph (assembleGraph O A) = A.inside := by
  ext v u
  rfl

@[simp] theorem outsideGraph_assemble (O : SimpleGraph W) (A : TripleCell W e d c) :
    outsideGraph (assembleGraph O A) = O := by
  ext w z
  rfl

@[simp] theorem adjacencyBit_assemble_cross (O : SimpleGraph W)
    (A : TripleCell W e d c) (v : Fin 3) (w : W) :
    adjacencyBit (assembleGraph O A) (Sum.inl v) (Sum.inr w) = A.outside v w := by
  unfold adjacencyBit
  have h := A.binary v w
  split_ifs with hedge
  · exact (show A.outside v w = 1 from hedge).symm
  · have hne : A.outside v w ≠ 1 := hedge
    omega

def cellToGraph (O : SimpleGraph W) (A : TripleCell W e d c) :
    GraphTripleCell O e d c :=
  ⟨assembleGraph O A, outsideGraph_assemble O A, by
    rw [internalGraph_assemble]; exact A.edge_count, by
    intro v
    rw [leftDegree_decompose, internalGraph_assemble]
    simp only [adjacencyBit_assemble_cross]
    have h := A.rows v
    omega, by
    intro w
    simpa only [crossColumn, adjacencyBit_assemble_cross] using A.columns w⟩

@[simp] theorem graphToCell_cellToGraph (O : SimpleGraph W) (A : TripleCell W e d c) :
    graphToCell (cellToGraph O A) = A := by
  apply TripleCell.ext
  · funext v w
    exact adjacencyBit_assemble_cross O A v w
  · exact internalGraph_assemble O A

@[simp] theorem cellToGraph_graphToCell (G : GraphTripleCell O e d c) :
    cellToGraph O (graphToCell G) = G := by
  apply Subtype.ext
  ext x y
  cases x with
  | inl v =>
      cases y with
      | inl u => rfl
      | inr w => simp [cellToGraph, assembleGraph, graphToCell, adjacencyBit]
  | inr w =>
      cases y with
      | inl v =>
          simpa [cellToGraph, assembleGraph, graphToCell, adjacencyBit] using
            G.val.adj_comm (Sum.inl v) (Sum.inr w)
      | inr z =>
          change O.Adj w z ↔ G.val.Adj (Sum.inr w) (Sum.inr z)
          exact Iff.of_eq (congrArg (fun K : SimpleGraph W => K.Adj w z) G.property.1).symm

def graphTripleCellEquiv (O : SimpleGraph W) (e : ℕ) (d : Fin 3 → ℕ) (c : W → ℕ) :
    GraphTripleCell O e d c ≃ TripleCell W e d c where
  toFun := graphToCell
  invFun := cellToGraph O
  left_inv := cellToGraph_graphToCell
  right_inv := graphToCell_cellToGraph O

def graphTripleMatrixEquiv (O : SimpleGraph W) (e : ℕ) (he : e ≤ 3)
    (d : Fin 3 → ℕ) (c : W → ℕ) (hd : ∀ v, rowOffset e ≤ d v) :
    GraphTripleCell O e d c ≃ AugmentedMatrix W e d c :=
  (graphTripleCellEquiv O e d c).trans (tripleMatrixEquiv e he d c hd)

end Problem315.TripleInternalEncoding

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.TriplePairFiber
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace Problem315.TripleInternalEncoding
attribute [local instance] Classical.propDecidable

variable {W : Type*} [Fintype W]

def complementaryPair (i : Fin 3) : Finset (Fin 3 ⊕ W) := by
  classical
  exact (Finset.univ.image Sum.inl).erase (Sum.inl i)

omit [Fintype W] in
@[simp] theorem inl_mem_complementaryPair (i v : Fin 3) :
    (Sum.inl v : Fin 3 ⊕ W) ∈ complementaryPair i ↔ v ≠ i := by
  classical
  simp [complementaryPair]

omit [Fintype W] in
@[simp] theorem inr_notMem_complementaryPair (i : Fin 3) (w : W) :
    (Sum.inr w : Fin 3 ⊕ W) ∉ complementaryPair i := by
  classical
  simp [complementaryPair]

def SamePairRestrictions {V : Type*} (a : Finset V) (G H : SimpleGraph V) : Prop :=
  (∀ u ∉ a, ∀ v ∉ a, G.Adj u v ↔ H.Adj u v) ∧
  (∀ u ∈ a, ∀ v ∈ a, G.Adj u v ↔ H.Adj u v)

variable {O : SimpleGraph W} {e : ℕ} {d : Fin 3 → ℕ} {c : W → ℕ}

theorem rightDegree_eq (G : GraphTripleCell O e d c) (w : W) :
    G.val.degree (Sum.inr w) = c w + O.degree w := by
  have hsum := G.val.degree_eq_sum_if_adj (R := ℕ) (Sum.inr w)
  simp only [Nat.cast_id, Fintype.sum_sum_type] at hsum
  rw [hsum]
  have hleft : (∑ v : Fin 3, if G.val.Adj (Sum.inr w) (Sum.inl v) then 1 else 0) =
      crossColumn G.val w := by
    unfold crossColumn adjacencyBit
    apply Finset.sum_congr rfl
    intro v hv
    rw [G.val.adj_comm (Sum.inr w) (Sum.inl v)]
  have hright : (∑ z : W, if G.val.Adj (Sum.inr w) (Sum.inr z) then 1 else 0) =
      O.degree w := by
    have ho := O.degree_eq_sum_if_adj (R := ℕ) w
    simp only [Nat.cast_id] at ho
    rw [ho]
    apply Finset.sum_congr rfl
    intro z hz
    have ha : G.val.Adj (Sum.inr w) (Sum.inr z) ↔ O.Adj w z :=
      Iff.of_eq (congrArg (fun K : SimpleGraph W => K.Adj w z) G.property.1)
    simp only [ha]
  rw [hleft, hright, G.property.2.2.2]

theorem graphCell_degrees_eq (G H : GraphTripleCell O e d c) :
    ∀ v, G.val.degree v = H.val.degree v := by
  intro v
  cases v with
  | inl i =>
      rw [← leftDegree_eq_degree, ← leftDegree_eq_degree]
      exact (G.property.2.2.1 i).trans (H.property.2.2.1 i).symm
  | inr w => rw [rightDegree_eq, rightDegree_eq]

def SamePairData {V : Type*} (a : Finset V) (G H : SimpleGraph V) : Prop :=
  (∀ u ∉ a, ∀ v ∉ a, G.Adj u v ↔ H.Adj u v) ∧
  (∀ u ∈ a, ∀ v ∈ a, G.Adj u v ↔ H.Adj u v) ∧
  (∀ w ∉ a, (a.filter (G.Adj w)).card = (a.filter (H.Adj w)).card)

theorem rightDegree_decompose (G : SimpleGraph (Fin 3 ⊕ W)) (w : W) :
    G.degree (Sum.inr w) = crossColumn G w + (outsideGraph G).degree w := by
  let A : GraphTripleCell (outsideGraph G) (internalEdgeCount (internalGraph G))
      (leftDegree G) (crossColumn G) := ⟨G, rfl, rfl, (fun _ => rfl), (fun _ => rfl)⟩
  exact rightDegree_eq A w

end Problem315.TripleInternalEncoding

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.TripleStateReindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem315.TripleStateReindex

open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {V W : Type*} [sectionFintypeV : Fintype V] [sectionFintypeW : Fintype W]

def degreeCount (G : SimpleGraph V) (v : V) : ℕ := by
  classical
  exact (Finset.univ.filter (G.Adj v)).card

theorem degreeCount_comap (e : V ≃ W) (G : SimpleGraph W) (v : V) :
    degreeCount (G.comap e) v = degreeCount G (e v) := by
  classical
  unfold degreeCount
  apply Finset.card_bij (fun w _ => e w)
  · intro w hw
    simpa using hw
  · intro u hu w hw he
    exact e.injective he
  · intro w hw
    refine ⟨e.symm w, ?_, e.apply_symm_apply w⟩
    simpa using hw

def graphEquiv (e : V ≃ W) : SimpleGraph W ≃ SimpleGraph V where
  toFun G := G.comap e
  invFun G := G.comap e.symm
  left_inv G := by ext u v; simp
  right_inv G := by ext u v; simp

include sectionFintypeV sectionFintypeW in
@[simp] theorem graphEquiv_adj (e : V ≃ W) (G : SimpleGraph W) (u v : V) :
    (graphEquiv e G).Adj u v ↔ G.Adj (e u) (e v) := by
  have retainedsectionFintypeV := sectionFintypeV
  have retainedsectionFintypeW := sectionFintypeW
  exact Iff.rfl

def fixedDegreeEquiv (e : V ≃ W) (d : W → ℕ) :
    {G : SimpleGraph W // ∀ v, degreeCount G v = d v} ≃
      {G : SimpleGraph V // ∀ v, degreeCount G v = d (e v)} where
  toFun G := ⟨graphEquiv e G.val, fun v => by
    rw [show graphEquiv e G.val = G.val.comap e from rfl, degreeCount_comap]
    exact G.property (e v)⟩
  invFun G := ⟨(graphEquiv e).symm G.val, fun v => by
    change degreeCount (G.val.comap e.symm) v = d v
    rw [degreeCount_comap, G.property, e.apply_symm_apply]⟩
  left_inv G := by apply Subtype.ext; exact (graphEquiv e).left_inv G.val
  right_inv G := by apply Subtype.ext; exact (graphEquiv e).right_inv G.val

variable {n : ℕ} (s : Finset (Fin n)) (hs : s.card = 3)

abbrev Outside := {v : Fin n // v ∉ s}

def tripleEnum : Fin 3 ≃ ↥s :=
  (Fintype.equivFinOfCardEq (by simpa using hs)).symm

def splitEquiv : (Fin 3 ⊕ Outside s) ≃ Fin n :=
  (Equiv.sumCongr (tripleEnum s hs) (Equiv.refl _)).trans
    (Equiv.sumCompl (fun v : Fin n => v ∈ s))

@[simp] theorem splitEquiv_inl (i : Fin 3) :
    splitEquiv s hs (Sum.inl i) = (tripleEnum s hs i).val := rfl

@[simp] theorem splitEquiv_inr (v : Outside s) :
    splitEquiv s hs (Sum.inr v) = v.val := rfl

@[simp] theorem splitEquiv_inl_mem (i : Fin 3) :
    splitEquiv s hs (Sum.inl i) ∈ s := (tripleEnum s hs i).property

@[simp] theorem splitEquiv_inr_not_mem (v : Outside s) :
    splitEquiv s hs (Sum.inr v) ∉ s := v.property

def stateEquiv (d : Fin n → ℕ) : GraphState n d ≃
    {G : SimpleGraph (Fin 3 ⊕ Outside s) //
      ∀ v, degreeCount G v = d (splitEquiv s hs v)} :=
  fixedDegreeEquiv (splitEquiv s hs) d

@[simp] theorem stateEquiv_adj (d : Fin n → ℕ) (G : GraphState n d)
    (u v : Fin 3 ⊕ Outside s) :
    (stateEquiv s hs d G).val.Adj u v ↔
      G.val.Adj (splitEquiv s hs u) (splitEquiv s hs v) := Iff.rfl

@[simp] theorem stateEquiv_outside_adj (d : Fin n → ℕ) (G : GraphState n d)
    (u v : Outside s) :
    (stateEquiv s hs d G).val.Adj (Sum.inr u) (Sum.inr v) ↔
      G.val.Adj u.val v.val := Iff.rfl

end Problem315.TripleStateReindex

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

theorem degreeCount_eq_degree {V : Type*} [Fintype V]
    (G : SimpleGraph V) (v : V) : degreeCount G v = G.degree v := by
  classical
  simp only [degreeCount, Finset.card_eq_sum_ones, Finset.sum_filter]
  exact (G.degree_eq_sum_if_adj (R := ℕ) v).symm

end Problem315.TripleCellTransport

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

def margins (e : ℕ) (c : W → ℕ) : Option W → ℕ :=
  fun w => w.elim (columnSum e) c

end Problem315.TripleMatrixFinEquiv

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.WeightedConditionalVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.WeightedConditional

variable {Ω ι β : Type*} [Fintype Ω] [sectionFintypeι : Fintype ι] [sectionFintypeβ : Fintype β]
  [sectionDecidableEqβ : DecidableEq β]

def conditionalSum (w : Ω → ℝ) (key : ι → Ω → β)
    (i : ι) (t : β) (f : Ω → ℝ) : ℝ :=
  ∑ x, if key i x = t then w x * f x else 0

include sectionFintypeι sectionFintypeβ in
theorem conditionalSum_add (w : Ω → ℝ) (key : ι → Ω → β)
    (i : ι) (t : β) (f g : Ω → ℝ) :
    conditionalSum w key i t (fun x => f x + g x) =
      conditionalSum w key i t f + conditionalSum w key i t g := by
  have retainedsectionFintypeι := sectionFintypeι
  have retainedsectionFintypeβ := sectionFintypeβ
  unfold conditionalSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  split <;> simp_all [mul_add]

include sectionFintypeι sectionFintypeβ in
theorem conditionalSum_smul (w : Ω → ℝ) (key : ι → Ω → β)
    (i : ι) (t : β) (c : ℝ) (f : Ω → ℝ) :
    conditionalSum w key i t (fun x => c * f x) =
      c * conditionalSum w key i t f := by
  have retainedsectionFintypeι := sectionFintypeι
  have retainedsectionFintypeβ := sectionFintypeβ
  unfold conditionalSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  split <;> simp_all [mul_left_comm]

abbrev Space (ι β : Type*) [Fintype ι] [Fintype β] :=
  EuclideanSpace ℝ (ι × β)

def decode (p : ι → β → ℝ) (z : Space ι β) (i : ι) (t : β) : ℝ :=
  z (i, t) / Real.sqrt (p i t)

def rowSum (p : ι → β → ℝ) (key : ι → Ω → β) (z : Space ι β) (x : Ω) : ℝ :=
  ∑ i, decode p z i (key i x)

def gram (w : Ω → ℝ) (p : ι → β → ℝ) (key : ι → Ω → β) :
    Space ι β →ₗ[ℝ] Space ι β where
  toFun z := WithLp.toLp 2 (fun it =>
    conditionalSum w key it.1 it.2 (rowSum p key z) / Real.sqrt (p it.1 it.2))
  map_add' z z' := by
    ext it
    change conditionalSum w key it.1 it.2 (rowSum p key (z + z')) /
      Real.sqrt (p it.1 it.2) = _
    have hs : rowSum p key (z + z') = fun x => rowSum p key z x + rowSum p key z' x := by
      funext x
      simp [rowSum, decode, add_div, Finset.sum_add_distrib]
    rw [hs, conditionalSum_add, add_div]
    rfl
  map_smul' c z := by
    ext it
    change conditionalSum w key it.1 it.2 (rowSum p key (c • z)) /
      Real.sqrt (p it.1 it.2) = c * _
    have hs : rowSum p key (c • z) = fun x => c * rowSum p key z x := by
      funext x
      simp [rowSum, decode, mul_div_assoc, Finset.mul_sum]
    rw [hs, conditionalSum_smul]
    change (c * _) / _ = c * (_ / _)
    ring

@[simp] theorem gram_apply (w : Ω → ℝ) (p : ι → β → ℝ)
    (key : ι → Ω → β) (z : Space ι β) (i : ι) (t : β) :
    gram w p key z (i,t) =
      conditionalSum w key i t (rowSum p key z) / Real.sqrt (p i t) := rfl

def centered (p : ι → β → ℝ) : Submodule ℝ (Space ι β) where
  carrier := {z | ∀ i, ∑ t, Real.sqrt (p i t) * z (i,t) = 0}
  zero_mem' := by simp
  add_mem' := by
    intro z z' hz hz' i
    simp only [Set.mem_ofPred_eq] at hz hz'
    simp only [PiLp.add_apply, mul_add, Finset.sum_add_distrib, hz i, hz' i, add_zero]
  smul_mem' := by
    intro c z hz i
    simp only [Set.mem_ofPred_eq] at hz
    simp only [PiLp.smul_apply, smul_eq_mul]
    simp_rw [mul_left_comm (Real.sqrt _) c]
    rw [← Finset.mul_sum, hz i, mul_zero]

include sectionDecidableEqβ in
@[simp] theorem mem_centered (p : ι → β → ℝ) (z : Space ι β) :
    z ∈ centered p ↔ ∀ i, ∑ t, Real.sqrt (p i t) * z (i,t) = 0 := by
  have retainedsectionDecidableEqβ := sectionDecidableEqβ
  exact Iff.rfl

def encode (p : ι → β → ℝ) (b : ι → β → ℝ) : Space ι β :=
  WithLp.toLp 2 (fun it => Real.sqrt (p it.1 it.2) * b it.1 it.2)

include sectionDecidableEqβ in
@[simp] theorem decode_encode (p : ι → β → ℝ) (hp : ∀ i t, 0 < p i t)
    (b : ι → β → ℝ) (i : ι) (t : β) : decode p (encode p b) i t = b i t := by
  have retainedsectionDecidableEqβ := sectionDecidableEqβ
  unfold decode encode
  change Real.sqrt (p i t) * b i t / Real.sqrt (p i t) = b i t
  exact mul_div_cancel_left₀ _ (Real.sqrt_pos.2 (hp i t)).ne'

end Problem315.WeightedConditional

end

end OAI
end


