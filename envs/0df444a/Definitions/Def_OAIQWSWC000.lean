-- Prove2me | Definitions.Def_OAIQWSWC000
-- name    : OAIQWSWC000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-23T16:10:49.906977+00:00
-- url     : https://prove2.me/theorems/48359fb6-df53-4863-836b-19a7867cc109
-- title:
--   OpenAI switch-chain split: definitions bundle OAIQWSWC000
-- statement:
--   One of the definitions bundles of the split of OpenAI's proof of `OAI.Problem315.switch_chain_main`: the lazy switch chain on simple graphs with a prescribed graphical degree sequence mixes in at most $2n^8$ steps, and has spectral gap at least $1/(24 n^2 \binom n4)$ when there is more than one realization. The bundle holds OpenAI's Lean definitions from the modules listed below of `lean/OAI/Probability/SwitchChain` (OpenAI, *Polynomial mixing of the switch chain for every graphical degree sequence*, OpenAI Math Release, September 25, 2026, result family 131, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a. It also holds the lemmas these definitions use in their bodies, and OpenAI's `@[simp]` lemmas about them.
--
--   This bundle carries the basic objects of the proof: the three-row matrix model of the paper's Section 3 (ordered block partitions and their counts), the pair fibers and the pair-resampling projections of Section 2 (`PairResampling.StateSpace`, the Euclidean space of real functions on the realizations, and `PairResampling.fluctuation n d a` $= h_a = I - E_a$), the four-vertex switches and their involutive flips (`fourVertexProposal`, `SwitchFlip.projection`, the projection $g_{a,b} = (I - T_{a,b})/2$, `CrossToggle.crossProposal`), the encoding of a cell for two disjoint pairs used in Section 5, the equality-indicator projections $R_{a,b}$ (`PairEquality.projection`), and the uniform subset slices of Section 6 (`SliceEuclideanGenerator.swapState`, `SliceNormalized.raw`).
--
--   The definitions of the published goal (`GraphState`, `SwitchStep`, `switchKernel`, `mixingTime`, `hasSpectralGapAtLeast` and the rest) come from the published bundle `Def_SwitchChain`. It imports no other bundle of this split.
--
--   Modules: `BalancedBlockVariance`, `BinaryAssignments`, `BinaryColumnPartitions`, `CellProjectionTransport`, `CountCoupling`, `CountCovering`, `CrossCellConditionalExpectation`, `CrossCellMoments`, `CrossCovariance`, `CrossIndependent`, `CrossMatrix`, `CrossToggleGain`, `CrossTogglePairs`, `DisjointBoundary`, `DisjointCellCounting`, `DisjointCoordinateFeasibility`, `DisjointCrossCellEquiv`, `DisjointEncoding`, `DisjointGraphAffine`, `DisjointInternal`, `DisjointProjectionCell`, `DisjointRealization`, `DisjointReconstruct`, `DisjointStateCell`, `DisjointStateLaw`, `FiberLabelCounting`, `FiniteKernelTV`, `FiniteVarianceDecomposition`, `FixedBlockCount`, `FixedBlockMarginal`, `FixedBlockPartitions`, `FixedBlockVariance`, `ForcedColumns`, `FourVertexSwitch`, `FrameSynthesis`, `FrozenRows`, `HavelInduction`, `KernelNormalization`, `MatchingCount`, `MatrixRowVariance`, `OrthogonalPairResampling`, `PairAffineInteraction`, `PairEqualityOrientation`, `PairEqualityProjection`, `PairEqualityRestriction`, `PairFiber`, `PairFiberBridge`, `PairFiberDegree`, `PairFiberEqualityTransport`, `PairFiberEquiv`, `PairFiberOrientation`, `PairFiberSliceComparison`, `PairFibers`, `PairOrbit`, `PairProjectionCell`, `SliceCoefficientAlgebra`, `SliceEuclideanGenerator`, `SliceMoments`, `SliceNormalizedFamily`, `SlicePermutationAction`, `SliceReindexedComparison`, `SwitchFlip`, `SwitchFoundations`, `TripleCellVarianceGluing`, `TripleCountLaw`, `VariableBlockVariance`.
-- source:
--   OpenAI, Polynomial mixing of the switch chain for every graphical degree sequence, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 131; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-Mixing-of-the-Switch-Chain-for-Every-Graphical-Degree-Sequence-September-25-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability/SwitchChain at commit adc7f12

import Mathlib
import Definitions.Def_SwitchChain

section
-- module Solutions.OAIQW_Problem315.FixedBlockPartitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.FixedBlock

variable {α : Type*} [Fintype α] [sectionDecidableEqα : DecidableEq α]

def row (c : α → Fin 3) (i : Fin 3) : Finset α :=
  Finset.univ.filter (fun a => c a = i)

include sectionDecidableEqα in
@[simp] lemma mem_row (c : α → Fin 3) (i : Fin 3) (a : α) :
    a ∈ row c i ↔ c a = i := by
  have retainedsectionDecidableEqα := sectionDecidableEqα
  simp [row]

lemma row_relabel (σ : Equiv.Perm α) (c : α → Fin 3) (i : Fin 3) :
    row (fun a => c (σ.symm a)) i = (row c i).map σ.toEmbedding := by
  ext a
  simp []

abbrev Partition (sizes : Fin 3 → ℕ) :=
  {c : α → Fin 3 // ∀ i, (row c i).card = sizes i}

def relabel {sizes : Fin 3 → ℕ} (σ : Equiv.Perm α) (c : Partition (α := α) sizes) :
    Partition (α := α) sizes :=
  ⟨fun a => c.val (σ.symm a), by
    intro i
    rw [row_relabel, Finset.card_map]
    exact c.property i⟩

@[simp] lemma relabel_val {sizes : Fin 3 → ℕ} (σ : Equiv.Perm α)
    (c : Partition (α := α) sizes) (a : α) :
    (relabel σ c).val a = c.val (σ.symm a) := rfl

@[simp] lemma relabel_one {sizes : Fin 3 → ℕ} (c : Partition (α := α) sizes) :
    relabel 1 c = c := by apply Subtype.ext; rfl

end Problem315.FixedBlock

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.FixedBlockVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.FixedBlockVariance
open FixedBlock

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
variable (p q : Fin 3 → ℕ)

abbrev State := Partition (α := α) p × Partition (α := β) q

def relabelPerm (σ : Equiv.Perm α) : Equiv.Perm (Partition (α := α) p) where
  toFun := relabel σ
  invFun := relabel σ.symm
  left_inv c := by
    apply Subtype.ext
    funext a
    simp [relabel]
  right_inv c := by
    apply Subtype.ext
    funext a
    simp [relabel]

def move : (α × α) ⊕ (β × β) → Equiv.Perm (State (α := α) (β := β) p q)
  | Sum.inl ab => Equiv.prodCongr (relabelPerm p (Equiv.swap ab.1 ab.2)) (Equiv.refl _)
  | Sum.inr ab => Equiv.prodCongr (Equiv.refl _) (relabelPerm q (Equiv.swap ab.1 ab.2))

def key (i : Fin 3) (x : State (α := α) (β := β) p q) : Finset α × Finset β :=
  (row x.1.val i, row x.2.val i)

def rowSpace (i : Fin 3) : Submodule ℝ (EuclideanSpace ℝ (State (α := α) (β := β) p q)) where
  carrier := {f | (∑ x, f x = 0) ∧ ∀ x y, key p q i x = key p q i y → f x = f y}
  zero_mem' := by simp
  add_mem' := by
    rintro f g ⟨hfc, hfk⟩ ⟨hgc, hgk⟩
    constructor
    · simp only [PiLp.add_apply, Finset.sum_add_distrib, hfc, hgc, zero_add]
    · intro x y h
      simp only [PiLp.add_apply, hfk x y h, hgk x y h]
  smul_mem' := by
    rintro c f ⟨hfc, hfk⟩
    constructor
    · simp only [PiLp.smul_apply, smul_eq_mul, ← Finset.mul_sum, hfc, mul_zero]
    · intro x y h
      simp only [PiLp.smul_apply, hfk x y h]

def average (f : State (α := α) (β := β) p q → ℝ) : ℝ :=
  (∑ x, f x) / (Fintype.card (State (α := α) (β := β) p q) : ℝ)

def variance (f : State (α := α) (β := β) p q → ℝ) : ℝ :=
  (∑ x, (f x - average p q f) ^ 2) /
    (Fintype.card (State (α := α) (β := β) p q) : ℝ)

end Problem315.FixedBlockVariance

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.FixedBlockMarginal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.FixedBlockMarginal
open FixedBlock

def average {X : Type*} [Fintype X] (f : X → ℝ) : ℝ :=
  (∑ x, f x) / (Fintype.card X : ℝ)

variable {α : Type*} [sectionFintypeα : Fintype α] [sectionDecidableEqα : DecidableEq α]

variable {β : Type*} [Fintype β] [DecidableEq β]

abbrev Subsets (k : ℕ) := {s : Finset α // s.card = k}

def subsetPerm (k : ℕ) (σ : Equiv.Perm α) : Equiv.Perm (Subsets (α := α) k) where
  toFun s := ⟨s.val.map σ.toEmbedding, by simpa using s.property⟩
  invFun s := ⟨s.val.map σ.symm.toEmbedding, by simpa using s.property⟩
  left_inv s := by
    apply Subtype.ext
    ext a
    simp
  right_inv s := by
    apply Subtype.ext
    ext a
    simp

end Problem315.FixedBlockMarginal

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.FiniteVarianceDecomposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.FiniteVariance

open FixedBlockMarginal (average)

variable {X I : Type*} [Fintype X] [Fintype I]

def variance (f : X → ℝ) : ℝ := average (fun x => (f x - average f) ^ 2)

end Problem315.FiniteVariance

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.FiberLabelCounting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace Problem315.FiberLabelCounting

variable {V C : Type*} [sectionFintypeV : Fintype V] [sectionFintypeC : Fintype C]

abbrev PrescribedFiberColorings (k : C → ℕ) :=
  {g : V → C // ∀ c, Fintype.card {v // g v = c} = k c}

abbrev EqualFiberColorings (f₀ : V → C) :=
  {g : V → C // ∀ c, Fintype.card {v // g v = c} = Fintype.card {v // f₀ v = c}}

abbrev LabeledFibers (f₀ : V → C) :=
  Σ g : EqualFiberColorings f₀, ∀ c, {v // f₀ v = c} ≃ {v // g.val v = c}

include sectionFintypeV sectionFintypeC in
theorem ofFiberEquiv_apply_subtype {f g : V → C}
    (e : ∀ c, {v // f v = c} ≃ {v // g v = c}) (c : C) (v : {v // f v = c}) :
    Equiv.ofFiberEquiv e v.val = (e c v).val := by
  have retainedsectionFintypeV := sectionFintypeV
  have retainedsectionFintypeC := sectionFintypeC
  rcases v with ⟨v, hv⟩
  subst c
  rfl

def labeledFibersEquivPerm (f₀ : V → C) : LabeledFibers f₀ ≃ Equiv.Perm V := by
  let F : LabeledFibers f₀ → Equiv.Perm V := fun a => Equiv.ofFiberEquiv a.2
  apply Equiv.ofBijective F
  constructor
  · rintro ⟨⟨g, hg⟩, e⟩ ⟨⟨h, hh⟩, f⟩ hp
    change Equiv.ofFiberEquiv e = Equiv.ofFiberEquiv f at hp
    have hgh : g = h := by
      funext y
      obtain ⟨x, rfl⟩ := (Equiv.ofFiberEquiv e).surjective y
      have hx := Equiv.ofFiberEquiv_map e x
      have hy := Equiv.ofFiberEquiv_map f x
      rw [← hp] at hy
      exact hx.trans hy.symm
    subst h
    have hef : e = f := by
      funext c
      apply Equiv.ext
      intro v
      apply Subtype.ext
      rw [← ofFiberEquiv_apply_subtype e c v, ← ofFiberEquiv_apply_subtype f c v]
      exact congrArg (fun p : Equiv.Perm V => p v.val) hp
    subst f
    rfl
  · intro p
    let g : V → C := fun v => f₀ (p.symm v)
    let e (c : C) : {v // f₀ v = c} ≃ {v // g v = c} :=
      { toFun := fun v => ⟨p v.val, by simpa [g] using v.property⟩
        invFun := fun v => ⟨p.symm v.val, v.property⟩
        left_inv := by intro v; apply Subtype.ext; simp
        right_inv := by intro v; apply Subtype.ext; simp }
    have hg : ∀ c, Fintype.card {v // g v = c} = Fintype.card {v // f₀ v = c} :=
      fun c => (Fintype.card_congr (e c)).symm
    refine ⟨⟨⟨g, hg⟩, e⟩, ?_⟩
    apply Equiv.ext
    intro v
    rfl

end Problem315.FiberLabelCounting

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.FixedBlockCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace Problem315.FixedBlock

variable {α β : Type*} [Fintype α] [sectionDecidableEqα : DecidableEq α] [Fintype β] [DecidableEq β]

def partitionEquivColorings (sizes : Fin 3 → ℕ) :
    Partition (α := α) sizes ≃
    FiberLabelCounting.PrescribedFiberColorings (V := α) sizes :=
  Equiv.subtypeEquivRight (fun g => by simp [Fintype.card_subtype, row])

def pairSizeWeight (sizesU sizesW : Fin 3 → ℕ) : ℝ :=
  (∏ i, (((sizesU i).factorial : ℝ) * ((sizesW i).factorial : ℝ)))⁻¹

end Problem315.FixedBlock

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.CountCoupling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.CountCoupling

def countWeight (α t : ℕ) : ℝ :=
  1 / ((t.factorial : ℝ) * ((t + α).factorial : ℝ))

def pairWeight (α β s y : ℕ) : ℝ :=
  countWeight α y * countWeight β (s - y)

def pairExpectation (α β s : ℕ) (b : ℕ → ℝ) : ℝ :=
  (∑ y ∈ Finset.range (s + 1), pairWeight α β s y * b y) /
    (∑ y ∈ Finset.range (s + 1), pairWeight α β s y)

end Problem315.CountCoupling

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.CountCovering
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.CountCoupling

def prefixMass (p : ℕ → ℝ) (k : ℕ) : ℝ := ∑ i ∈ Finset.range k, p i

def coveredPairProbability (α β s y : ℕ) : ℝ :=
  if y ≤ s then pairWeight α β s y /
    (∑ z ∈ Finset.range (s + 1), pairWeight α β s z) else 0

end Problem315.CountCoupling

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

abbrev Triple (m : ℕ) :=
  {x : Fin 3 → Fin (m + 1) // ∑ i : Fin 3, (x i).val = m}

abbrev Fiber (m : ℕ) (σ : Equiv.Perm (Fin 3)) (t : ℕ) :=
  {x : Triple m // (x.val (σ 0)).val = t}

def fiberEquiv (m : ℕ) (σ : Equiv.Perm (Fin 3)) (t : ℕ) (ht : t ≤ m) :
    Fin (m - t + 1) ≃ Fiber m σ t where
  toFun y :=
    ⟨⟨fun i => (![⟨t, by omega⟩, ⟨y.val, by omega⟩,
      ⟨m - t - y.val, by omega⟩] : Fin 3 → Fin (m + 1)) (σ.symm i), by
      rw [← Equiv.sum_comp σ]
      simp only [Equiv.symm_apply_apply]
      simp only [Fin.sum_univ_three]
      dsimp
      omega⟩, by simp⟩
  invFun x := ⟨(x.val.val (σ 1)).val, by
    have hs := x.val.property
    rw [← Equiv.sum_comp σ] at hs
    simp only [Fin.sum_univ_three] at hs
    have hx := x.property
    omega⟩
  left_inv y := by simp
  right_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    obtain ⟨j, rfl⟩ := σ.surjective i
    apply Fin.ext
    have hs := x.val.property
    rw [← Equiv.sum_comp σ] at hs
    simp only [Fin.sum_univ_three] at hs
    have hx := x.property
    fin_cases j <;> simp at * <;> omega

@[simp] theorem fiberEquiv_coordinate_zero (m : ℕ) (σ : Equiv.Perm (Fin 3))
    (t : ℕ) (ht : t ≤ m) (y : Fin (m - t + 1)) :
    (((fiberEquiv m σ t ht y).val.val (σ 0)).val) = t := by
  simp [fiberEquiv]

@[simp] theorem fiberEquiv_coordinate_one (m : ℕ) (σ : Equiv.Perm (Fin 3))
    (t : ℕ) (ht : t ≤ m) (y : Fin (m - t + 1)) :
    (((fiberEquiv m σ t ht y).val.val (σ 1)).val) = y.val := by
  simp [fiberEquiv]

@[simp] theorem fiberEquiv_coordinate_two (m : ℕ) (σ : Equiv.Perm (Fin 3))
    (t : ℕ) (ht : t ≤ m) (y : Fin (m - t + 1)) :
    (((fiberEquiv m σ t ht y).val.val (σ 2)).val) = m - t - y.val := by
  simp [fiberEquiv]

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

def sizes (o : Fin 3 → ℕ) {m : ℕ} (x : Triple m) (i : Fin 3) : ℕ :=
  (x.val i).val + o i

abbrev Fiber (m : ℕ) (u w : Fin 3 → ℕ) (x : Triple m) :=
  FixedBlockVariance.State (α := U) (β := W) (sizes u x) (sizes w x)

abbrev Family (m : ℕ) (u w : Fin 3 → ℕ) :=
  Σ x : Triple m, Fiber U W m u w x

end Problem315.VariableBlockVariance

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.BalancedBlockVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.BalancedBlockVariance
open FixedBlockMarginal (average)
open VariableBlockVariance (Family sizes )

variable (U W : Type*) [Fintype U] [sectionDecidableEqU : DecidableEq U] [Fintype W] [sectionDecidableEqW : DecidableEq W]

abbrev Balanced (u w : Fin 3 → ℕ) :=
  {c : (U → Fin 3) × (W → Fin 3) // ∀ i,
    (FixedBlock.row c.1 i).card + w i = (FixedBlock.row c.2 i).card + u i}

variable {U W}

theorem sum_row_card {A : Type*} [Fintype A] [DecidableEq A] (c : A → Fin 3) :
    (∑ i, (FixedBlock.row c i).card) = Fintype.card A := by
  simp only [FixedBlock.row, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

include sectionDecidableEqU sectionDecidableEqW in
theorem lower_le {u w : Fin 3 → ℕ} (hsep : ∀ i, u i = 0 ∨ w i = 0)
    (c : Balanced U W u w) (i : Fin 3) : w i ≤ (FixedBlock.row c.val.2 i).card := by
  have retainedsectionDecidableEqU := sectionDecidableEqU
  have retainedsectionDecidableEqW := sectionDecidableEqW
  have h := c.property i
  rcases hsep i with h | h <;> omega

def countVector {u w : Fin 3 → ℕ} (hsep : ∀ i, u i = 0 ∨ w i = 0)
    (c : Balanced U W u w) : TripleCountLaw.Triple (Fintype.card W - ∑ i, w i) := by
  let m := Fintype.card W - ∑ i, w i
  have hs : (∑ i, ((FixedBlock.row c.val.2 i).card - w i)) = m := by
    rw [Finset.sum_tsub_distrib]
    · simp only [sum_row_card, m]
    · intro i hi
      exact lower_le hsep c i
  refine ⟨fun i => ⟨(FixedBlock.row c.val.2 i).card - w i, ?_⟩, hs⟩
  have hi : (FixedBlock.row c.val.2 i).card - w i ≤
      ∑ j, ((FixedBlock.row c.val.2 j).card - w j) :=
    Finset.single_le_sum (f := fun j => (FixedBlock.row c.val.2 j).card - w j)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  rw [hs] at hi
  omega

def forgetCounts (u w : Fin 3 → ℕ)
    (z : Family U W (Fintype.card W - ∑ i, w i) u w) : Balanced U W u w :=
  ⟨(z.2.1.val, z.2.2.val), by
    intro i
    rw [z.2.1.property i, z.2.2.property i]
    simp only [sizes]
    omega⟩

def familyEquiv (u w : Fin 3 → ℕ) (hsep : ∀ i, u i = 0 ∨ w i = 0) :
    Balanced U W u w ≃ Family U W (Fintype.card W - ∑ i, w i) u w := by
  apply Equiv.symm
  apply Equiv.ofBijective (forgetCounts (U := U) (W := W) u w)
  constructor
  · rintro ⟨x, c, d⟩ ⟨y, e, f⟩ h
    have hc : c.val = e.val := congrArg (fun z : Balanced U W u w => z.val.1) h
    have hd : d.val = f.val := congrArg (fun z : Balanced U W u w => z.val.2) h
    have hxy : x = y := by
      apply Subtype.ext
      funext i
      apply Fin.ext
      have hi := congrArg (fun v : W → Fin 3 => (FixedBlock.row v i).card) hd
      rw [d.property i, f.property i] at hi
      simp only [sizes] at hi
      omega
    subst y
    have hce : c = e := Subtype.ext hc
    have hdf : d = f := Subtype.ext hd
    subst e
    subst f
    rfl
  · intro c
    refine ⟨⟨countVector hsep c, ⟨⟨c.val.1, ?_⟩, ⟨c.val.2, ?_⟩⟩⟩, rfl⟩
    · intro i
      have he := c.property i
      have hl := lower_le hsep c i
      change (FixedBlock.row c.val.1 i).card =
        (FixedBlock.row c.val.2 i).card - w i + u i
      omega
    · intro i
      change (FixedBlock.row c.val.2 i).card =
        (FixedBlock.row c.val.2 i).card - w i + w i
      exact (Nat.sub_add_cancel (lower_le hsep c i)).symm

end Problem315.BalancedBlockVariance

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.BinaryAssignments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical

namespace Problem315.BinaryAssignments

variable {α : Type*} [Fintype α]

def singletons (c : α → Nat) : Finset α := Finset.univ.filter (fun w => c w = 1)
def common (c : α → Nat) : Finset α := Finset.univ.filter (fun w => c w = 2)

def first (c : α → Nat) (U : Finset α) (w : α) : Prop := c w = 2 ∨ w ∈ U
def second (c : α → Nat) (U : Finset α) (w : α) : Prop :=
  c w = 2 ∨ (c w = 1 ∧ w ∉ U)

theorem indicator_sum (c : α → Nat) (hc : ∀ w, c w ≤ 2)
    (U : Finset α) (hU : U ⊆ singletons c) (w : α) :
    (if first c U w then 1 else 0) + (if second c U w then 1 else 0) = c w := by
  have hw := hc w
  have hmem : w ∈ U → c w = 1 := fun h => (Finset.mem_filter.mp (hU h)).2
  by_cases hu : w ∈ U
  · have hc1 := hmem hu
    simp [first, second, hu, hc1]
  · rcases (show c w = 0 ∨ c w = 1 ∨ c w = 2 by omega) with h | h | h <;>
      simp [first, second, hu, h]

theorem first_on_singletons (c : α → Nat) (U : Finset α) (w : α)
    (hw : w ∈ singletons c) : first c U w ↔ w ∈ U := by
  have hc := (Finset.mem_filter.mp hw).2
  simp [first, hc]

theorem first_filter (c : α → Nat) (U : Finset α) :
    Finset.univ.filter (first c U) = common c ∪ U := by
  ext w
  simp [first, common]

theorem second_filter (c : α → Nat) (U : Finset α) :
    Finset.univ.filter (second c U) = common c ∪ (singletons c \ U) := by
  ext w
  simp [second, common, singletons]

theorem first_card (c : α → Nat) (U : Finset α) (hU : U ⊆ singletons c) :
    (Finset.univ.filter (first c U)).card = (common c).card + U.card := by
  rw [first_filter, Finset.card_union_of_disjoint]
  apply Finset.disjoint_left.mpr
  intro w hw hwu
  have h2 := (Finset.mem_filter.mp hw).2
  have h1 := (Finset.mem_filter.mp (hU hwu)).2
  omega

theorem second_card_add (c : α → Nat) (U : Finset α) (hU : U ⊆ singletons c) :
    (Finset.univ.filter (second c U)).card + U.card =
      (common c).card + (singletons c).card := by
  have hdis : Disjoint (common c) (singletons c \ U) := by
    apply Finset.disjoint_left.mpr
    intro w hw hws
    have h2 := (Finset.mem_filter.mp hw).2
    have h1 := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hws).1).2
    omega
  rw [second_filter, Finset.card_union_of_disjoint hdis, Nat.add_assoc,
    Finset.card_sdiff_add_card_eq_card hU]

end Problem315.BinaryAssignments

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.BinaryColumnPartitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.BinaryColumnPartitions

abbrev Column (q : ℕ) := {c : Fin 3 → Fin 2 // ∑ i, (c i : ℕ) = q}

def unitColumn (i : Fin 3) : Column 1 :=
  ⟨fun j => if j = i then 1 else 0, by
    simp only [Fin.sum_univ_three]
    fin_cases i <;> decide⟩

def complementColumn (c : Fin 3 → Fin 2) : Fin 3 → Fin 2 :=
  fun i => if c i = 0 then 1 else 0

lemma column_one_surjective : Function.Surjective unitColumn := by
  decide

lemma column_one_injective : Function.Injective unitColumn := by
  decide

noncomputable def oneColumnEquiv : Fin 3 ≃ Column 1 :=
  Equiv.ofBijective unitColumn ⟨column_one_injective, column_one_surjective⟩

noncomputable def complementEquiv : Column 1 ≃ Column 2 where
  toFun c := ⟨complementColumn c.val, by
    have h : ∀ c : Column 1, ∑ i, (complementColumn c.val i : ℕ) = 2 := by decide
    exact h c⟩
  invFun c := ⟨complementColumn c.val, by
    have h : ∀ c : Column 2, ∑ i, (complementColumn c.val i : ℕ) = 1 := by decide
    exact h c⟩
  left_inv := by decide
  right_inv := by decide

def twoColumnEquiv : Fin 3 ≃ Column 2 := oneColumnEquiv.trans complementEquiv

variable (U W : Type*)

abbrev MatrixSpace :=
  {M : Fin 3 → U ⊕ W → Fin 2 //
    (∀ u, ∑ i, (M i (Sum.inl u) : ℕ) = 1) ∧
    (∀ w, ∑ i, (M i (Sum.inr w) : ℕ) = 2)}

def matrixEquiv : ((U → Fin 3) × (W → Fin 3)) ≃ MatrixSpace U W where
  toFun c := ⟨fun i j => Sum.elim
    (fun u => (oneColumnEquiv (c.1 u)).val i)
    (fun w => (twoColumnEquiv (c.2 w)).val i) j,
    ⟨fun u => (oneColumnEquiv (c.1 u)).property,
     fun w => (twoColumnEquiv (c.2 w)).property⟩⟩
  invFun M :=
    (fun u => oneColumnEquiv.symm ⟨fun i => M.val i (Sum.inl u), M.property.1 u⟩,
     fun w => twoColumnEquiv.symm ⟨fun i => M.val i (Sum.inr w), M.property.2 w⟩)
  left_inv c := by
    apply Prod.ext
    · funext u
      exact oneColumnEquiv.symm_apply_apply (c.1 u)
    · funext w
      exact twoColumnEquiv.symm_apply_apply (c.2 w)
  right_inv M := by
    apply Subtype.ext
    funext i j
    cases j with
    | inl u =>
      exact congrArg (fun c : Column 1 => c.val i)
        (oneColumnEquiv.apply_symm_apply ⟨fun k => M.val k (Sum.inl u), M.property.1 u⟩)
    | inr w =>
      exact congrArg (fun c : Column 2 => c.val i)
        (twoColumnEquiv.apply_symm_apply ⟨fun k => M.val k (Sum.inr w), M.property.2 w⟩)

@[simp] theorem matrixEquiv_inl (c : (U → Fin 3) × (W → Fin 3)) (i : Fin 3) (u : U) :
    (matrixEquiv U W c).val i (Sum.inl u) = if i = c.1 u then 1 else 0 := rfl

@[simp] theorem matrixEquiv_inr (c : (U → Fin 3) × (W → Fin 3)) (i : Fin 3) (w : W) :
    (matrixEquiv U W c).val i (Sum.inr w) = if i = c.2 w then 0 else 1 := by
  change (if (if i = c.2 w then (1 : Fin 2) else 0) = 0 then 1 else 0) = _
  split_ifs <;> simp_all

variable [Fintype U] [Fintype W]

theorem row_sum_add (c : (U → Fin 3) × (W → Fin 3)) (i : Fin 3) :
    (∑ j, ((matrixEquiv U W c).val i j : ℕ)) + (FixedBlock.row c.2 i).card =
      (FixedBlock.row c.1 i).card + Fintype.card W := by
  classical
  have hU : (∑ u : U, ((matrixEquiv U W c).val i (Sum.inl u) : ℕ)) =
      (FixedBlock.row c.1 i).card := by
    have hu (u : U) : ((matrixEquiv U W c).val i (Sum.inl u) : ℕ) =
        if c.1 u = i then 1 else 0 := by
      rw [matrixEquiv_inl]
      by_cases h : i = c.1 u
      · simp [h]
      · simp [h, Ne.symm h]
    simp_rw [hu]
    simp [FixedBlock.row]
  have hW : (∑ w : W, ((matrixEquiv U W c).val i (Sum.inr w) : ℕ)) +
      (FixedBlock.row c.2 i).card = Fintype.card W := by
    have hh (w : W) : ((matrixEquiv U W c).val i (Sum.inr w) : ℕ) +
        (if c.2 w = i then 1 else 0) = 1 := by
      rw [matrixEquiv_inr]
      by_cases h : i = c.2 w
      · simp [h]
      · simp [h, Ne.symm h]
    have hs := congrArg (fun f : W → ℕ => ∑ w, f w) (funext hh)
    simpa [Finset.sum_add_distrib, FixedBlock.row] using hs
  rw [Fintype.sum_sum_type, hU]
  omega

def fixedMarginsEquiv (r : Fin 3 → ℕ) :
    {c : (U → Fin 3) × (W → Fin 3) // ∀ i,
      (FixedBlock.row c.1 i).card + Fintype.card W = r i + (FixedBlock.row c.2 i).card} ≃
    {M : MatrixSpace U W // ∀ i, ∑ j, (M.val i j : ℕ) = r i} :=
  (matrixEquiv U W).subtypeEquiv (fun c => by
    constructor
    · intro h i
      have hh := row_sum_add U W c i
      have hi := h i
      omega
    · intro h i
      have hh := row_sum_add U W c i
      rw [h i] at hh
      exact hh.symm)

end Problem315.BinaryColumnPartitions

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

def SameFiber {n : ℕ} (a : Finset (Fin n)) (G H : SimpleGraph (Fin n)) : Prop :=
  (∀ u ∉ a, ∀ v ∉ a, G.Adj u v ↔ H.Adj u v) ∧
  (∀ u ∈ a, ∀ v ∈ a, G.Adj u v ↔ H.Adj u v) ∧
  (∀ w ∉ a, (a.filter (G.Adj w)).card = (a.filter (H.Adj w)).card)

@[refl] theorem SameFiber.refl {n : ℕ} (a : Finset (Fin n))
    (G : SimpleGraph (Fin n)) : SameFiber a G G := by
  unfold SameFiber
  exact ⟨fun _ _ _ _ => Iff.rfl, fun _ _ _ _ => Iff.rfl, fun _ _ => rfl⟩

@[symm] theorem SameFiber.symm {n : ℕ} {a : Finset (Fin n)}
    {G H : SimpleGraph (Fin n)} (h : SameFiber a G H) : SameFiber a H G :=
  ⟨fun u hu v hv => (h.1 u hu v hv).symm,
   fun u hu v hv => (h.2.1 u hu v hv).symm,
   fun w hw => (h.2.2 w hw).symm⟩

@[trans] theorem SameFiber.trans {n : ℕ} {a : Finset (Fin n)}
    {G H K : SimpleGraph (Fin n)} (h : SameFiber a G H) (k : SameFiber a H K) :
    SameFiber a G K :=
  ⟨fun u hu v hv => (h.1 u hu v hv).trans (k.1 u hu v hv),
   fun u hu v hv => (h.2.1 u hu v hv).trans (k.2.1 u hu v hv),
   fun w hw => (h.2.2 w hw).trans (k.2.2 w hw)⟩

abbrev StateSpace (n : ℕ) (d : Fin n → ℕ) := EuclideanSpace ℝ (GraphState n d)

def fiberSpace (n : ℕ) (d : Fin n → ℕ) (a : Finset (Fin n)) :
    Submodule ℝ (StateSpace n d) where
  carrier := {f | ∀ G H : GraphState n d, SameFiber a G.val H.val → f G = f H}
  zero_mem' := by intro G H h; rfl
  add_mem' := by
    intro f g hf hg G H h
    change f G + g G = f H + g H
    rw [hf G H h, hg G H h]
  smul_mem' := by
    intro c f hf G H h
    change c * f G = c * f H
    rw [hf G H h]

def expectation (n : ℕ) (d : Fin n → ℕ) (a : Finset (Fin n)) :
    StateSpace n d →L[ℝ] StateSpace n d := (fiberSpace n d a).starProjection

def fluctuation (n : ℕ) (d : Fin n → ℕ) (a : Finset (Fin n)) :
    StateSpace n d →L[ℝ] StateSpace n d := (fiberSpace n d a)ᗮ.starProjection

variable {n : ℕ} {d : Fin n → ℕ} (a : Finset (Fin n))

@[simp] theorem expectation_mem (f : StateSpace n d) :
    expectation n d a f ∈ fiberSpace n d a :=
  (fiberSpace n d a).starProjection_apply_mem f

@[simp] theorem expectation_eq_self_iff (f : StateSpace n d) :
    expectation n d a f = f ↔ f ∈ fiberSpace n d a :=
  (fiberSpace n d a).starProjection_eq_self_iff

@[simp] theorem expectation_idempotent (f : StateSpace n d) :
    expectation n d a (expectation n d a f) = expectation n d a f :=
  (expectation_eq_self_iff a _).mpr (expectation_mem a f)

@[simp] theorem fluctuation_idempotent (f : StateSpace n d) :
    fluctuation n d a (fluctuation n d a f) = fluctuation n d a f :=
  (Submodule.starProjection_eq_self_iff).mpr
    ((fiberSpace n d a)ᗮ.starProjection_apply_mem f)

def fiberStates (a : Finset (Fin n)) (G : GraphState n d) : Finset (GraphState n d) :=
  Finset.univ.filter (fun H => SameFiber a G.val H.val)

@[simp] theorem mem_fiberStates (G H : GraphState n d) :
    H ∈ fiberStates a G ↔ SameFiber a G.val H.val := by
  simp [fiberStates]

@[simp] theorem self_mem_fiberStates (G : GraphState n d) : G ∈ fiberStates a G := by
  exact (mem_fiberStates a G G).mpr (SameFiber.refl a G.val)

end PairResampling
end Problem315

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

def cell (R : Setoid α) (x : α) : Finset α :=
  Finset.univ.filter (fun y => R.r x y)

@[simp] theorem mem_cell (R : Setoid α) (x y : α) :
    y ∈ cell R x ↔ R.r x y := by simp [cell]

end Partition

end Problem315.PairFibers

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.CellProjectionTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.CellProjectionTransport

attribute [local instance] Classical.propDecidable

variable {α β : Type*} [sectionFintypeα : Fintype α] [sectionFintypeβ : Fintype β]

def restrictedSetoid (R : Setoid α) (C : α → Prop) : Setoid {x // C x} :=
  Setoid.comap Subtype.val R

def restrict (C : α → Prop) (f : EuclideanSpace ℝ α) :
    EuclideanSpace ℝ {x // C x} := WithLp.toLp 2 (fun x => f x.val)

include sectionFintypeα in
@[simp] theorem restrict_apply (C : α → Prop) (f : EuclideanSpace ℝ α)
    (x : {x // C x}) : restrict C f x = f x.val := by
  have retainedsectionFintypeα := sectionFintypeα
  exact rfl

def classEquiv (R : Setoid α) (C : α → Prop)
    (hC : ∀ x y, R.r x y → (C x ↔ C y)) (x : {x // C x}) :
    ↥(PairFibers.cell R x.val) ≃
      ↥(PairFibers.cell (restrictedSetoid R C) x) where
  toFun y := ⟨⟨y.val, (hC x.val y.val
    ((PairFibers.mem_cell R x.val y.val).mp y.property)).mp x.property⟩,
    (PairFibers.mem_cell _ _ _).mpr ((PairFibers.mem_cell R x.val y.val).mp y.property)⟩
  invFun y := ⟨y.val.val, (PairFibers.mem_cell R x.val y.val.val).mpr
    ((PairFibers.mem_cell (restrictedSetoid R C) x y.val).mp y.property)⟩
  left_inv y := by apply Subtype.ext; rfl
  right_inv y := by apply Subtype.ext; rfl

variable {n : ℕ} {d : Fin n → ℕ}

def graphSetoid (a : Finset (Fin n)) : Setoid (GraphState n d) where
  r G H := PairResampling.SameFiber a G.val H.val
  iseqv := ⟨fun G => PairResampling.SameFiber.refl a G.val,
    fun h => h.symm, fun h k => h.trans k⟩

end Problem315.CellProjectionTransport

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.CrossCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.CrossCovariance

variable {α β : Type*} [sectionFintypeα : Fintype α] [Fintype β]

def rightSliceAverage (b : β → ℝ) (q : β → ℝ) (t : ℝ) (g : β → ℝ) : ℝ :=
  (∑ y, b y * (2 - t - q y) * g y) / (∑ y, b y * (2 - t - q y))

end Problem315.CrossCovariance

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.CrossMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem315.CrossBlock

open scoped BigOperators

abbrev Matrix := Fin 2 → Fin 2 → Bool

def entry (M : Matrix) (i j : Fin 2) : Nat := if M i j then 1 else 0

def row (M : Matrix) (i : Fin 2) : Nat := ∑ j, entry M i j

def col (M : Matrix) (j : Fin 2) : Nat := ∑ i, entry M i j

def total (M : Matrix) : Nat := ∑ i, row M i

def count (s r c : Nat) : Nat :=
  (Finset.univ.filter (fun M : Matrix => total M = s ∧ row M 0 = r ∧ col M 0 = c)).card

theorem row_le_two : ∀ (M : Matrix) (i : Fin 2), row M i ≤ 2 := by
  decide

theorem col_le_two : ∀ (M : Matrix) (j : Fin 2), col M j ≤ 2 := by
  decide

end Problem315.CrossBlock

end OAI
end

section
-- module Solutions.OAIQW_Problem315.CrossCellMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.CrossCellMoments

attribute [local instance] Classical.propDecidable

variable {α β : Type*} [sectionFintypeα : Fintype α] [sectionFintypeβ : Fintype β]

abbrev Cell (s : ℕ) (r : α → Fin 3) (c : β → Fin 3) :=
  {z : CrossBlock.Matrix × α × β //
    CrossBlock.total z.1 = s ∧ CrossBlock.row z.1 0 = (r z.2.1).val ∧
      CrossBlock.col z.1 0 = (c z.2.2).val}

instance cellFintype (s : ℕ) (r : α → Fin 3) (c : β → Fin 3) :
    Fintype (Cell s r c) := Fintype.ofFinite _

def offCenter (r : α → Fin 3) (x : α) : ℝ := if r x = 1 then 0 else 1

def conditionalRight (s : ℕ) (r : α → Fin 3) (c : β → Fin 3)
    (x : α) (g : β → ℝ) : ℝ := by
  classical
  exact (∑ z ∈ (Finset.univ : Finset (Cell s r c)).filter
    (fun z => z.val.2.1 = x), g z.val.2.2) /
      ((Finset.univ : Finset (Cell s r c)).filter
        (fun z => z.val.2.1 = x)).card

def conditionalLeft (s : ℕ) (r : α → Fin 3) (c : β → Fin 3)
    (y : β) (f : α → ℝ) : ℝ := by
  classical
  exact (∑ z ∈ (Finset.univ : Finset (Cell s r c)).filter
    (fun z => z.val.2.2 = y), f z.val.2.1) /
      ((Finset.univ : Finset (Cell s r c)).filter
        (fun z => z.val.2.2 = y)).card

end Problem315.CrossCellMoments

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.CrossCellConditionalExpectation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.CrossCellMoments

attribute [local instance] Classical.propDecidable
variable {α β : Type*} [Fintype α] [Fintype β]

def firstPartition (s : ℕ) (r : α → Fin 3) (c : β → Fin 3) : Setoid (Cell s r c) :=
  Setoid.ker (fun z => z.val.2.1)

def secondPartition (s : ℕ) (r : α → Fin 3) (c : β → Fin 3) : Setoid (Cell s r c) :=
  Setoid.ker (fun z => z.val.2.2)

end Problem315.CrossCellMoments

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.CrossIndependent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.CrossBlock

def independentMargin (s : ℕ) (r : Fin 3) : ℝ :=
  match s with
  | 0 => if r = 0 then 1 else 0
  | 1 => if r ≤ 1 then 1 else 0
  | 3 => if 1 ≤ r then 1 else 0
  | 4 => if r = 2 then 1 else 0
  | _ => 0

end Problem315.CrossBlock

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.SwitchFoundations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace Problem315

def reverseProposal {n : Nat} (p : SwitchProposal n) : SwitchProposal n :=
  ⟨p.1, ⟨(p.2.val.2, p.2.val.1), Ne.symm p.2.property⟩⟩

@[simp] theorem removedMatching_reverse {n : Nat} (p : SwitchProposal n) :
    removedMatching (reverseProposal p) = addedMatching p := rfl

@[simp] theorem addedMatching_reverse {n : Nat} (p : SwitchProposal n) :
    addedMatching (reverseProposal p) = removedMatching p := rfl

@[simp] theorem reverseProposal_reverse {n : Nat} (p : SwitchProposal n) :
    reverseProposal (reverseProposal p) = p := by
  rcases p with ⟨S, ⟨⟨M, N⟩, h⟩⟩
  rfl

theorem validSwitch_matchings_disjoint {n : Nat} {G : SimpleGraph (Fin n)}
    {p : SwitchProposal n} (h : validSwitch G p) {u v : Fin n}
    (hm : (removedMatching p).Adj u v) : ¬ (addedMatching p).Adj u v := by
  intro hn
  exact h.2 hn (h.1 hm)

theorem validSwitch_reverse_replace {n : Nat} {G : SimpleGraph (Fin n)}
    {p : SwitchProposal n} (h : validSwitch G p) :
    validSwitch (replaceEdges G (removedMatching p) (addedMatching p))
      (reverseProposal p) := by
  constructor
  · intro u v hn
    exact Or.inr hn
  · intro u v hm he
    rcases he with he | hn
    · exact he.2 hm
    · exact validSwitch_matchings_disjoint h hm hn

theorem replaceEdges_reverse {n : Nat} {G : SimpleGraph (Fin n)}
    {p : SwitchProposal n} (h : validSwitch G p) :
    replaceEdges (replaceEdges G (removedMatching p) (addedMatching p))
      (addedMatching p) (removedMatching p) = G := by
  ext u v
  change (((G.Adj u v ∧ ¬ (removedMatching p).Adj u v) ∨
    (addedMatching p).Adj u v) ∧ ¬ (addedMatching p).Adj u v) ∨
    (removedMatching p).Adj u v ↔ G.Adj u v
  constructor
  · rintro (⟨hG | hN, hn⟩ | hm)
    · exact hG.1
    · exact False.elim (hn hN)
    · exact h.1 hm
  · intro hG
    by_cases hm : (removedMatching p).Adj u v
    · exact Or.inr hm
    · exact Or.inl ⟨Or.inl ⟨hG, hm⟩, fun hn => h.2 hn hG⟩

theorem proposalResult_of_valid {n : Nat} {G : SimpleGraph (Fin n)}
    {p : SwitchProposal n} (h : validSwitch G p) :
    proposalResult G p = replaceEdges G (removedMatching p) (addedMatching p) := by
  simp [proposalResult, h]

theorem proposalResult_reverse {n : Nat} {G : SimpleGraph (Fin n)}
    {p : SwitchProposal n} (h : validSwitch G p) :
    proposalResult (proposalResult G p) (reverseProposal p) = G := by
  rw [proposalResult_of_valid h,
    proposalResult_of_valid (validSwitch_reverse_replace h)]
  exact replaceEdges_reverse h

theorem perfectMatching_degree {n : Nat} {S : FourSet n}
    (M : PerfectMatching S) (v : Fin n) :
    graphDegree M.val v = if v ∈ S.val then 1 else 0 := by
  classical
  by_cases hv : v ∈ S.val
  · obtain ⟨w, hw, hu⟩ := (M.property v).1 hv
    have hs : Finset.univ.filter (fun x => M.val.Adj v x) = {w} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨fun hx => hu x hx, fun hx => hx ▸ hw⟩
    simp [graphDegree, hs, hv]
  · have hs : Finset.univ.filter (fun x => M.val.Adj v x) = ∅ := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
        iff_false]
      exact (M.property v).2 hv x
    simp [graphDegree, hs, hv]

theorem matchings_degree_eq {n : Nat} (p : SwitchProposal n) (v : Fin n) :
    graphDegree (removedMatching p) v = graphDegree (addedMatching p) v := by
  exact (perfectMatching_degree p.2.val.1 v).trans
    (perfectMatching_degree p.2.val.2 v).symm

theorem replaceEdges_degree_add {n : Nat} {G : SimpleGraph (Fin n)}
    {p : SwitchProposal n} (h : validSwitch G p) (v : Fin n) :
    graphDegree (replaceEdges G (removedMatching p) (addedMatching p)) v +
      graphDegree (removedMatching p) v =
    graphDegree G v + graphDegree (addedMatching p) v := by
  classical
  simp only [graphDegree, Finset.card_eq_sum_ones, Finset.sum_filter,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro w hw
  by_cases hg : G.Adj v w <;>
    by_cases hm : (removedMatching p).Adj v w <;>
    by_cases hn : (addedMatching p).Adj v w
  all_goals simp_all [replaceEdges, h.1, h.2]

theorem proposalResult_degree {n : Nat} (G : SimpleGraph (Fin n))
    (p : SwitchProposal n) (v : Fin n) :
    graphDegree (proposalResult G p) v = graphDegree G v := by
  classical
  by_cases h : validSwitch G p
  · rw [proposalResult_of_valid h]
    have ha := replaceEdges_degree_add h v
    rw [matchings_degree_eq p v] at ha
    exact Nat.add_right_cancel ha
  · simp [proposalResult, h]

theorem proposalResult_realizes {n : Nat} {d : Fin n → Nat}
    {G : SimpleGraph (Fin n)} (hG : Realizes n d G) (p : SwitchProposal n) :
    Realizes n d (proposalResult G p) := by
  intro v
  rw [proposalResult_degree]
  exact hG v

end Problem315

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.FourVertexSwitch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem315

def FourDistinct {α : Type*} (a b c d : α) : Prop :=
  a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d

def twoEdgeGraph {n : Nat} (a b c d : Fin n)
    (hab : a ≠ b) (hcd : c ≠ d) : SimpleGraph (Fin n) where
  Adj u v := (u = a ∧ v = b) ∨ (u = b ∧ v = a) ∨
    (u = c ∧ v = d) ∨ (u = d ∧ v = c)
  symm := by
    constructor
    intro u v huv
    tauto
  loopless := by
    constructor
    intro v hv
    rcases hv with h | h | h | h
    · exact hab (h.1.symm.trans h.2)
    · exact hab (h.2.symm.trans h.1)
    · exact hcd (h.1.symm.trans h.2)
    · exact hcd (h.2.symm.trans h.1)

theorem twoEdgeGraph_matching {n : Nat} (a b c d : Fin n)
    (h : FourDistinct a b c d) :
    IsPerfectMatchingOn {a, b, c, d}
      (twoEdgeGraph a b c d h.1 h.2.2.2.2.2) := by
  rcases h with ⟨hab, hac, had, hbc, hbd, hcd⟩
  intro v
  constructor
  · intro hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · refine ⟨b, ?_, ?_⟩
      · exact Or.inl ⟨rfl, rfl⟩
      · intro y hy
        simp_all [twoEdgeGraph]
    · refine ⟨a, ?_, ?_⟩
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · intro y hy
        simp_all [twoEdgeGraph]
        aesop
    · refine ⟨d, ?_, ?_⟩
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
      · intro y hy
        simp_all [twoEdgeGraph]
        aesop
    · refine ⟨c, ?_, ?_⟩
      · exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))
      · intro y hy
        simp_all [twoEdgeGraph]
        aesop
  · intro hv w hw
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hv
    change (v = a ∧ w = b) ∨ (v = b ∧ w = a) ∨
      (v = c ∧ w = d) ∨ (v = d ∧ w = c) at hw
    tauto

def fourVertexProposal {n : Nat} (a b c d : Fin n)
    (h : FourDistinct a b c d) : SwitchProposal n := by
  classical
  rcases h with ⟨hab, hac, had, hbc, hbd, hcd⟩
  let S : FourSet n := ⟨{a, b, c, d}, by
    simp [hab, hac, had, hbc, hbd, hcd]⟩
  have hfirst : IsPerfectMatchingOn S.val (twoEdgeGraph a b c d hab hcd) :=
    twoEdgeGraph_matching a b c d ⟨hab, hac, had, hbc, hbd, hcd⟩
  have hsecond : IsPerfectMatchingOn S.val (twoEdgeGraph a c b d hac hbd) := by
    have hm := twoEdgeGraph_matching a c b d ⟨hac, hab, had, hbc.symm, hcd, hbd⟩
    convert hm using 1
    ext x
    simp [S, or_left_comm]
  refine ⟨S, ⟨(⟨twoEdgeGraph a b c d hab hcd, hfirst⟩,
    ⟨twoEdgeGraph a c b d hac hbd, hsecond⟩), ?_⟩⟩
  intro heq
  have he := congrArg (fun M : PerfectMatching S => M.val.Adj a b) heq
  simp [twoEdgeGraph, hab, hac, had, hbc, hbd, Ne.symm hab] at he

@[simp] theorem removedMatching_fourVertexProposal {n : Nat} (a b c d : Fin n)
    (h : FourDistinct a b c d) (u v : Fin n) :
    (removedMatching (fourVertexProposal a b c d h)).Adj u v ↔
      (u = a ∧ v = b) ∨ (u = b ∧ v = a) ∨
      (u = c ∧ v = d) ∨ (u = d ∧ v = c) := by
  rcases h with ⟨hab, hac, had, hbc, hbd, hcd⟩
  rfl

@[simp] theorem addedMatching_fourVertexProposal {n : Nat} (a b c d : Fin n)
    (h : FourDistinct a b c d) (u v : Fin n) :
    (addedMatching (fourVertexProposal a b c d h)).Adj u v ↔
      (u = a ∧ v = c) ∨ (u = c ∧ v = a) ∨
      (u = b ∧ v = d) ∨ (u = d ∧ v = b) := by
  rcases h with ⟨hab, hac, had, hbc, hbd, hcd⟩
  rfl

end Problem315

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.MatchingCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem315.MatchingCount

abbrev FixedPointFreeInvolution (V : Type*) :=
  {f : V → V // Function.Involutive f ∧ ∀ v, f v ≠ v}

instance instFintypeFixedPointFreeInvolutionOfDecidableEq {V : Type*} [Fintype V] [DecidableEq V] :
    Fintype (FixedPointFreeInvolution V) := by
  letI : DecidablePred (fun f : V → V => Function.Involutive f ∧ ∀ v, f v ≠ v) :=
    fun f => inferInstanceAs (Decidable ((∀ v, f (f v) = v) ∧ ∀ v, f v ≠ v))
  exact Subtype.fintype _

noncomputable def involutionCongr {V W : Type*} (e : V ≃ W) :
    FixedPointFreeInvolution V ≃ FixedPointFreeInvolution W where
  toFun f := ⟨fun w => e (f.val (e.symm w)), by
    constructor
    · intro w
      simp only [Equiv.symm_apply_apply]
      rw [f.property.1 (e.symm w), Equiv.apply_symm_apply]
    · intro w h
      have h' := congrArg e.symm h
      simp only [Equiv.symm_apply_apply] at h'
      exact f.property.2 (e.symm w) h'⟩
  invFun f := ⟨fun v => e.symm (f.val (e v)), by
    constructor
    · intro v
      simp only [Equiv.apply_symm_apply]
      rw [f.property.1 (e v), Equiv.symm_apply_apply]
    · intro v h
      have h' := congrArg e h
      simp only [Equiv.apply_symm_apply] at h'
      exact f.property.2 (e v) h'⟩
  left_inv f := by ext v; simp
  right_inv f := by ext v; simp

variable {n : ℕ} {S : FourSet n}

theorem matching_neighbor_mem (M : PerfectMatching S)
    {u v : Fin n} (h : M.val.Adj u v) : v ∈ S.val := by
  by_contra hv
  exact ((M.property v).2 hv u) (M.val.symm.symm u v h)

noncomputable def mate (M : PerfectMatching S) (v : S.val) : S.val :=
  ⟨Classical.choose ((M.property v.val).1 v.property).exists,
    matching_neighbor_mem M (Classical.choose_spec ((M.property v.val).1 v.property).exists)⟩

theorem mate_adj (M : PerfectMatching S) (v : S.val) :
    M.val.Adj v.val (mate M v).val :=
  Classical.choose_spec ((M.property v.val).1 v.property).exists

theorem mate_unique (M : PerfectMatching S) (v : S.val) {w : Fin n}
    (hw : M.val.Adj v.val w) : w = (mate M v).val :=
  ((M.property v.val).1 v.property).unique hw (mate_adj M v)

noncomputable def matchingToInvolution (M : PerfectMatching S) :
    FixedPointFreeInvolution S.val := ⟨mate M, by
  constructor
  · intro v
    apply Subtype.ext
    exact (mate_unique M (mate M v) (M.val.symm.symm _ _ (mate_adj M v))).symm
  · intro v h
    have hh := mate_adj M v
    rw [h] at hh
    exact M.val.loopless.irrefl _ hh⟩

def involutionGraph (f : FixedPointFreeInvolution S.val) : SimpleGraph (Fin n) where
  Adj u v := ∃ (hu : u ∈ S.val) (hv : v ∈ S.val), f.val ⟨u, hu⟩ = ⟨v, hv⟩
  symm := by
    constructor
    rintro u v ⟨hu, hv, h⟩
    refine ⟨hv, hu, ?_⟩
    rw [← h, f.property.1]
  loopless := by
    constructor
    rintro v ⟨hv, hv', h⟩
    exact f.property.2 ⟨v, hv⟩ h

noncomputable def involutionToMatching (f : FixedPointFreeInvolution S.val) :
    PerfectMatching S := ⟨involutionGraph f, by
  intro v
  constructor
  · intro hv
    refine ⟨(f.val ⟨v, hv⟩).val, ?_, ?_⟩
    · exact ⟨hv, (f.val ⟨v, hv⟩).property, rfl⟩
    · rintro w ⟨hv', hw, h⟩
      exact (congrArg Subtype.val h).symm
  · intro hv w h
    exact hv h.choose⟩

noncomputable def matchingEquivInvolution (S : FourSet n) :
    PerfectMatching S ≃ FixedPointFreeInvolution S.val where
  toFun := matchingToInvolution
  invFun := involutionToMatching
  left_inv M := by
    apply Subtype.ext
    apply SimpleGraph.ext
    funext u v
    apply propext
    constructor
    · rintro ⟨hu, hv, h⟩
      have hh := mate_adj M ⟨u, hu⟩
      change mate M ⟨u, hu⟩ = ⟨v, hv⟩ at h
      rw [h] at hh
      exact hh
    · intro h
      have hu := matching_neighbor_mem M (M.val.symm.symm _ _ h)
      have hv := matching_neighbor_mem M h
      refine ⟨hu, hv, ?_⟩
      apply Subtype.ext
      exact (mate_unique M ⟨u, hu⟩ h).symm
  right_inv f := by
    apply Subtype.ext
    funext v
    apply Subtype.ext
    exact (mate_unique (involutionToMatching f) v
      ⟨v.property, (f.val v).property, rfl⟩).symm

end Problem315.MatchingCount

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.KernelNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace Problem315

def proposalState {n : ℕ} {d : Fin n → ℕ}
    (G : GraphState n d) (p : SwitchProposal n) : GraphState n d :=
  ⟨proposalResult G.val p, proposalResult_realizes G.property p⟩

end Problem315

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.SwitchFlip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace
attribute [local instance] Classical.propDecidable

namespace Problem315.SwitchFlip

variable {n : ℕ} {d : Fin n → ℕ}

lemma not_valid_reverse {G : SimpleGraph (Fin n)} {p : SwitchProposal n}
    (h : validSwitch G p) : ¬ validSwitch G (reverseProposal p) := by
  intro hr
  obtain ⟨u, hu⟩ := Finset.card_pos.mp (show 0 < p.1.val.card by rw [p.1.property]; omega)
  obtain ⟨v, hv, _⟩ := (p.2.val.1.property u).1 hu
  exact hr.2 hv (h.1 hv)

lemma valid_reverse_result {G : GraphState n d} {p : SwitchProposal n}
    (h : validSwitch G.val p) :
    validSwitch (proposalState G p).val (reverseProposal p) := by
  change validSwitch (proposalResult G.val p) (reverseProposal p)
  rw [proposalResult_of_valid h]
  exact validSwitch_reverse_replace h

lemma state_reverse {G : GraphState n d} {p : SwitchProposal n}
    (h : validSwitch G.val p) :
    proposalState (proposalState G p) (reverseProposal p) = G := by
  apply Subtype.ext
  exact proposalResult_reverse h

def flip (p : SwitchProposal n) (G : GraphState n d) : GraphState n d :=
  if validSwitch G.val p then proposalState G p
  else if validSwitch G.val (reverseProposal p) then proposalState G (reverseProposal p)
  else G

@[simp] theorem flip_of_valid (p : SwitchProposal n) (G : GraphState n d)
    (h : validSwitch G.val p) : flip p G = proposalState G p := by
  simp [flip, h]

@[simp] theorem flip_of_reverse_valid (p : SwitchProposal n) (G : GraphState n d)
    (h : validSwitch G.val (reverseProposal p)) :
    flip p G = proposalState G (reverseProposal p) := by
  have hn : ¬ validSwitch G.val p := by simpa using not_valid_reverse h
  simp [flip, hn, h]

@[simp] theorem flip_reverse (p : SwitchProposal n) (G : GraphState n d) :
    flip (reverseProposal p) G = flip p G := by
  by_cases h : validSwitch G.val p
  · simp [flip, h, not_valid_reverse h]
  · by_cases hr : validSwitch G.val (reverseProposal p) <;> simp [flip, h, hr]

 theorem flip_involutive (p : SwitchProposal n) :
    Function.Involutive (flip (d := d) p) := by
  intro G
  by_cases h : validSwitch G.val p
  · rw [flip_of_valid p G h,
      flip_of_reverse_valid p _ (valid_reverse_result h), state_reverse h]
  · by_cases hr : validSwitch G.val (reverseProposal p)
    · rw [flip_of_reverse_valid p G hr]
      have hv : validSwitch (proposalState G (reverseProposal p)).val p := by
        simpa using valid_reverse_result hr
      rw [flip_of_valid p _ hv]
      simpa using state_reverse hr
    · simp [flip, h, hr]

def equiv (p : SwitchProposal n) : Equiv.Perm (GraphState n d) :=
  ⟨flip p, flip p, flip_involutive p, flip_involutive p⟩

@[simp] theorem equiv_apply (p : SwitchProposal n) (G : GraphState n d) :
    equiv p G = flip p G := rfl

def isometry (p : SwitchProposal n) :
    PairResampling.StateSpace n d ≃ₗᵢ[ℝ] PairResampling.StateSpace n d :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (equiv p)

@[simp] theorem isometry_apply (p : SwitchProposal n)
    (f : PairResampling.StateSpace n d) (G : GraphState n d) :
    isometry p f G = f (flip p G) := rfl

def operator (p : SwitchProposal n) :
    PairResampling.StateSpace n d →L[ℝ] PairResampling.StateSpace n d :=
  (isometry p).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem operator_apply (p : SwitchProposal n)
    (f : PairResampling.StateSpace n d) (G : GraphState n d) :
    operator p f G = f (flip p G) := rfl

@[simp] theorem operator_involutive (p : SwitchProposal n)
    (f : PairResampling.StateSpace n d) : operator p (operator p f) = f := by
  ext G
  simp only [operator_apply, flip_involutive p G]

def projection (p : SwitchProposal n) :
    PairResampling.StateSpace n d →L[ℝ] PairResampling.StateSpace n d :=
  (1 / 2 : ℝ) • (ContinuousLinearMap.id ℝ _ - operator p)

@[simp] theorem projection_apply (p : SwitchProposal n)
    (f : PairResampling.StateSpace n d) (G : GraphState n d) :
    projection p f G = (f G - f (flip p G)) / 2 := by
  simp [projection, div_eq_mul_inv, mul_comm]

@[simp] theorem projection_reverse (p : SwitchProposal n) :
    projection (d := d) (reverseProposal p) = projection p := by
  ext f G
  simp only [projection_apply, flip_reverse]

end Problem315.SwitchFlip

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.CrossTogglePairs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.CrossToggle

open SwitchFlip

attribute [local instance] Classical.propDecidable

variable {n : ℕ} {d : Fin n → ℕ}

def crossProposal (i j k l : Fin n) (h : FourDistinct i j k l) : SwitchProposal n :=
  fourVertexProposal i k l j
    (show FourDistinct i k l j from
      ⟨h.2.1, h.2.2.1, h.1, h.2.2.2.2.2, h.2.2.2.1.symm, h.2.2.2.2.1.symm⟩)

abbrev VertexPair (n : ℕ) := {a : Finset (Fin n) // a.card = 2}

def first (a : VertexPair n) : Fin n :=
  Classical.choose (Finset.card_eq_two.mp a.property)

def second (a : VertexPair n) : Fin n :=
  Classical.choose (Classical.choose_spec (Finset.card_eq_two.mp a.property))

theorem first_ne_second (a : VertexPair n) : first a ≠ second a :=
  (Classical.choose_spec (Classical.choose_spec (Finset.card_eq_two.mp a.property))).1

theorem pair_eq (a : VertexPair n) : a.val = {first a, second a} :=
  (Classical.choose_spec (Classical.choose_spec (Finset.card_eq_two.mp a.property))).2

theorem endpoints_distinct (a b : VertexPair n) (h : Disjoint a.val b.val) :
    FourDistinct (first a) (second a) (first b) (second b) := by
  have hfirst (x : VertexPair n) : first x ∈ x.val := by rw [pair_eq]; simp
  have hsecond (x : VertexPair n) : second x ∈ x.val := by rw [pair_eq]; simp
  have hn := Finset.disjoint_left.mp h
  refine ⟨first_ne_second a, ?_, ?_, ?_, ?_, first_ne_second b⟩
  · intro he; exact hn (hfirst a) (he ▸ hfirst b)
  · intro he; exact hn (hfirst a) (he ▸ hsecond b)
  · intro he; exact hn (hsecond a) (he ▸ hfirst b)
  · intro he; exact hn (hsecond a) (he ▸ hsecond b)

def pairProposal (a b : VertexPair n) (h : Disjoint a.val b.val) : SwitchProposal n :=
  crossProposal (first a) (second a) (first b) (second b) (endpoints_distinct a b h)

def pairProjection (a b : VertexPair n) :
    PairResampling.StateSpace n d →L[ℝ] PairResampling.StateSpace n d :=
  if h : Disjoint a.val b.val then projection (pairProposal a b h) else 0

end Problem315.CrossToggle

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

def restrictCell (C : GraphState n d → Prop) (f : StateSpace n d) : StateSpace n d :=
  WithLp.toLp 2 (fun G => if C G then f G else 0)

@[simp] theorem restrictCell_apply (C : GraphState n d → Prop)
    (f : StateSpace n d) (G : GraphState n d) :
    restrictCell C f G = if C G then f G else 0 := rfl

@[simp] theorem restrictCell_idempotent (C : GraphState n d → Prop)
    (f : StateSpace n d) : restrictCell C (restrictCell C f) = restrictCell C f := by
  ext G
  by_cases h : C G <;> simp [h]

@[simp] theorem restrictCell_sub (C : GraphState n d → Prop)
    (f g : StateSpace n d) : restrictCell C (f - g) = restrictCell C f - restrictCell C g := by
  ext G
  by_cases h : C G <;> simp [restrictCell, h]

end Problem315.PairResampling

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.CrossToggleGain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.CrossToggle

attribute [local instance] Classical.propDecidable
variable {n : ℕ} {d : Fin n → ℕ}

def gain (a b : Finset (Fin n)) :
    PairResampling.StateSpace n d →L[ℝ] PairResampling.StateSpace n d :=
  if ha : a.card = 2 then
    if hb : b.card = 2 then pairProjection ⟨a, ha⟩ ⟨b, hb⟩ else 0
  else 0

end Problem315.CrossToggle

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.DisjointEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical

namespace Problem315.DisjointEncoding

variable {V : Type*}

def edgeBit (G : SimpleGraph V) (u v : V) : Nat := if G.Adj u v then 1 else 0

@[simp] theorem edgeBit_eq_iff (G H : SimpleGraph V) (u v : V) :
    edgeBit G u v = edgeBit H u v ↔ (G.Adj u v ↔ H.Adj u v) := by
  by_cases hG : G.Adj u v <;> by_cases hH : H.Adj u v <;> simp [edgeBit, hG, hH]

def Outside (e : Fin 4 ↪ V) (w : V) : Prop := ∀ a, w ≠ e a

structure SameCell (e : Fin 4 ↪ V) (G H : SimpleGraph V) : Prop where
  outer : ∀ u v, Outside e u → Outside e v → (G.Adj u v ↔ H.Adj u v)
  leftInternal : G.Adj (e 0) (e 1) ↔ H.Adj (e 0) (e 1)
  rightInternal : G.Adj (e 2) (e 3) ↔ H.Adj (e 2) (e 3)
  leftCount : ∀ w, Outside e w →
    edgeBit G (e 0) w + edgeBit G (e 1) w =
      edgeBit H (e 0) w + edgeBit H (e 1) w
  rightCount : ∀ w, Outside e w →
    edgeBit G (e 2) w + edgeBit G (e 3) w =
      edgeBit H (e 2) w + edgeBit H (e 3) w

structure SameCoordinates (e : Fin 4 ↪ V) (G H : SimpleGraph V) : Prop where
  cross02 : G.Adj (e 0) (e 2) ↔ H.Adj (e 0) (e 2)
  cross03 : G.Adj (e 0) (e 3) ↔ H.Adj (e 0) (e 3)
  cross12 : G.Adj (e 1) (e 2) ↔ H.Adj (e 1) (e 2)
  cross13 : G.Adj (e 1) (e 3) ↔ H.Adj (e 1) (e 3)
  leftChoice : ∀ w, Outside e w → (G.Adj (e 0) w ↔ H.Adj (e 0) w)
  rightChoice : ∀ w, Outside e w → (G.Adj (e 2) w ↔ H.Adj (e 2) w)

theorem block_to_outside (e : Fin 4 ↪ V) (G H : SimpleGraph V)
    (hc : SameCell e G H) (he : SameCoordinates e G H)
    (a : Fin 4) (w : V) (hw : Outside e w) :
    G.Adj (e a) w ↔ H.Adj (e a) w := by
  fin_cases a
  · exact he.leftChoice w hw
  · change G.Adj (e 1) w ↔ H.Adj (e 1) w
    apply (edgeBit_eq_iff G H _ _).mp
    have hfirst := (edgeBit_eq_iff G H (e 0) w).mpr (he.leftChoice w hw)
    have hsum := hc.leftCount w hw
    omega
  · exact he.rightChoice w hw
  · change G.Adj (e 3) w ↔ H.Adj (e 3) w
    apply (edgeBit_eq_iff G H _ _).mp
    have hfirst := (edgeBit_eq_iff G H (e 2) w).mpr (he.rightChoice w hw)
    have hsum := hc.rightCount w hw
    omega

theorem block_to_block (e : Fin 4 ↪ V) (G H : SimpleGraph V)
    (hc : SameCell e G H) (he : SameCoordinates e G H) (a b : Fin 4) :
    G.Adj (e a) (e b) ↔ H.Adj (e a) (e b) := by
  have h01 := hc.leftInternal
  have h23 := hc.rightInternal
  have h02 := he.cross02
  have h03 := he.cross03
  have h12 := he.cross12
  have h13 := he.cross13
  fin_cases a <;> fin_cases b
  · simp
  · exact h01
  · exact h02
  · exact h03
  · exact (G.adj_comm _ _).trans (h01.trans (H.adj_comm _ _))
  · simp
  · exact h12
  · exact h13
  · exact (G.adj_comm _ _).trans (h02.trans (H.adj_comm _ _))
  · exact (G.adj_comm _ _).trans (h12.trans (H.adj_comm _ _))
  · simp
  · exact h23
  · exact (G.adj_comm _ _).trans (h03.trans (H.adj_comm _ _))
  · exact (G.adj_comm _ _).trans (h13.trans (H.adj_comm _ _))
  · exact (G.adj_comm _ _).trans (h23.trans (H.adj_comm _ _))
  · simp

theorem graph_eq_of_cell_coordinates (e : Fin 4 ↪ V) (G H : SimpleGraph V)
    (hc : SameCell e G H) (he : SameCoordinates e G H) : G = H := by
  ext u v
  by_cases hu : ∃ a, u = e a
  · obtain ⟨a, rfl⟩ := hu
    by_cases hv : ∃ b, v = e b
    · obtain ⟨b, rfl⟩ := hv
      exact block_to_block e G H hc he a b
    · exact block_to_outside e G H hc he a v (by simpa [Outside] using hv)
  · have hu' : Outside e u := by simpa [Outside] using hu
    by_cases hv : ∃ b, v = e b
    · obtain ⟨b, rfl⟩ := hv
      simpa only [SimpleGraph.adj_comm] using block_to_outside e G H hc he b u hu'
    · exact hc.outer u v hu' (by simpa [Outside] using hv)

theorem SameCell.refl (e : Fin 4 ↪ V) (G : SimpleGraph V) : SameCell e G G := by
  constructor <;> intros <;> rfl

theorem SameCell.symm {e : Fin 4 ↪ V} {G H : SimpleGraph V}
    (h : SameCell e G H) : SameCell e H G := by
  exact ⟨fun u v hu hv => (h.outer u v hu hv).symm,
    h.leftInternal.symm, h.rightInternal.symm,
    fun w hw => (h.leftCount w hw).symm, fun w hw => (h.rightCount w hw).symm⟩

theorem SameCell.trans {e : Fin 4 ↪ V} {G H K : SimpleGraph V}
    (h : SameCell e G H) (h' : SameCell e H K) : SameCell e G K := by
  exact ⟨fun u v hu hv => (h.outer u v hu hv).trans (h'.outer u v hu hv),
    h.leftInternal.trans h'.leftInternal, h.rightInternal.trans h'.rightInternal,
    fun w hw => (h.leftCount w hw).trans (h'.leftCount w hw),
    fun w hw => (h.rightCount w hw).trans (h'.rightCount w hw)⟩

def leftIndex (i : Fin 2) : Fin 4 := ⟨i.val, by omega⟩

def rightIndex (i : Fin 2) : Fin 4 := ⟨i.val + 2, by omega⟩

end Problem315.DisjointEncoding

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.DisjointReconstruct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace Problem315.DisjointEncoding

variable {V : Type*}

def blockEquiv (e : Fin 4 ↪ V) : Fin 4 ⊕ {w : V // Outside e w} ≃ V :=
  Equiv.ofBijective (Sum.elim e Subtype.val) (by
    constructor
    · rintro (a | u) (b | v) h
      · exact congrArg Sum.inl (e.injective h)
      · exact False.elim (v.property a h.symm)
      · exact False.elim (u.property b h)
      · exact congrArg Sum.inr (Subtype.ext h)
    · intro v
      by_cases h : ∃ a, v = e a
      · obtain ⟨a, ha⟩ := h
        exact ⟨Sum.inl a, ha.symm⟩
      · exact ⟨Sum.inr ⟨v, by simpa [Outside] using h⟩, rfl⟩)

@[simp] theorem blockEquiv_inl (e : Fin 4 ↪ V) (a : Fin 4) :
    blockEquiv e (Sum.inl a) = e a := rfl

@[simp] theorem blockEquiv_inr (e : Fin 4 ↪ V) (w : {w : V // Outside e w}) :
    blockEquiv e (Sum.inr w) = w.val := rfl

@[simp] theorem blockEquiv_symm_endpoint (e : Fin 4 ↪ V) (a : Fin 4) :
    (blockEquiv e).symm (e a) = Sum.inl a :=
  (blockEquiv e).symm_apply_apply (Sum.inl a)

@[simp] theorem blockEquiv_symm_outside (e : Fin 4 ↪ V) (w : {w : V // Outside e w}) :
    (blockEquiv e).symm w.val = Sum.inr w :=
  (blockEquiv e).symm_apply_apply (Sum.inr w)

def glueGraph {α β : Type*} (I : SimpleGraph α) (B : α → β → Prop)
    (O : SimpleGraph β) : SimpleGraph (α ⊕ β) where
  Adj u v := match u, v with
    | Sum.inl a, Sum.inl b => I.Adj a b
    | Sum.inl a, Sum.inr w => B a w
    | Sum.inr w, Sum.inl a => B a w
    | Sum.inr u, Sum.inr v => O.Adj u v
  symm := by
    constructor
    rintro (a | u) (b | v) h
    · exact h.symm
    · exact h
    · exact h
    · exact h.symm
  loopless := by
    constructor
    rintro (a | w) h
    · exact I.irrefl h
    · exact O.irrefl h

def reconstruct (e : Fin 4 ↪ V) (I : SimpleGraph (Fin 4))
    (B : Fin 4 → {w : V // Outside e w} → Prop)
    (O : SimpleGraph {w : V // Outside e w}) : SimpleGraph V :=
  (glueGraph I B O).comap (blockEquiv e).symm

@[simp] theorem reconstruct_block_block (e : Fin 4 ↪ V) (I : SimpleGraph (Fin 4))
    (B : Fin 4 → {w : V // Outside e w} → Prop)
    (O : SimpleGraph {w : V // Outside e w}) (a b : Fin 4) :
    (reconstruct e I B O).Adj (e a) (e b) ↔ I.Adj a b := by
  simp [reconstruct, SimpleGraph.comap_adj, glueGraph]

@[simp] theorem reconstruct_block_outside (e : Fin 4 ↪ V) (I : SimpleGraph (Fin 4))
    (B : Fin 4 → {w : V // Outside e w} → Prop)
    (O : SimpleGraph {w : V // Outside e w}) (a : Fin 4) (w : {w : V // Outside e w}) :
    (reconstruct e I B O).Adj (e a) w.val ↔ B a w := by
  simp [reconstruct, SimpleGraph.comap_adj, glueGraph]

@[simp] theorem reconstruct_outside_block (e : Fin 4 ↪ V) (I : SimpleGraph (Fin 4))
    (B : Fin 4 → {w : V // Outside e w} → Prop)
    (O : SimpleGraph {w : V // Outside e w}) (a : Fin 4) (w : {w : V // Outside e w}) :
    (reconstruct e I B O).Adj w.val (e a) ↔ B a w := by
  simp [reconstruct, SimpleGraph.comap_adj, glueGraph]

@[simp] theorem reconstruct_outside_outside (e : Fin 4 ↪ V) (I : SimpleGraph (Fin 4))
    (B : Fin 4 → {w : V // Outside e w} → Prop)
    (O : SimpleGraph {w : V // Outside e w}) (u v : {w : V // Outside e w}) :
    (reconstruct e I B O).Adj u.val v.val ↔ O.Adj u v := by
  simp [reconstruct, SimpleGraph.comap_adj, glueGraph]

theorem reconstruct_graph (e : Fin 4 ↪ V) (G : SimpleGraph V) :
    reconstruct e (G.comap e) (fun a w => G.Adj (e a) w.val)
      (G.comap (fun w : {w : V // Outside e w} => w.val)) = G := by
  ext u v
  obtain ⟨u, rfl⟩ := (blockEquiv e).surjective u
  obtain ⟨v, rfl⟩ := (blockEquiv e).surjective v
  cases u <;> cases v <;> simp [SimpleGraph.adj_comm]

def BoundaryMatches (e : Fin 4 ↪ V) (G : SimpleGraph V)
    (B : Fin 4 → {w : V // Outside e w} → Prop) : Prop :=
  ∀ w, ((if B 0 w then 1 else 0) + (if B 1 w then 1 else 0) =
      edgeBit G (e 0) w.val + edgeBit G (e 1) w.val) ∧
    ((if B 2 w then 1 else 0) + (if B 3 w then 1 else 0) =
      edgeBit G (e 2) w.val + edgeBit G (e 3) w.val)

theorem sameCell_reconstruct (e : Fin 4 ↪ V) (G : SimpleGraph V)
    (I : SimpleGraph (Fin 4))
    (B : Fin 4 → {w : V // Outside e w} → Prop)
    (hleft : I.Adj 0 1 ↔ G.Adj (e 0) (e 1))
    (hright : I.Adj 2 3 ↔ G.Adj (e 2) (e 3))
    (hB : BoundaryMatches e G B) :
    SameCell e G (reconstruct e I B (G.comap Subtype.val)) := by
  constructor
  · intro u v hu hv
    simpa using (reconstruct_outside_outside e I B (G.comap Subtype.val)
      ⟨u, hu⟩ ⟨v, hv⟩).symm
  · simpa using hleft.symm
  · simpa using hright.symm
  · intro w hw
    simp only [edgeBit]
    rw [reconstruct_block_outside e I B (G.comap Subtype.val) 0 ⟨w, hw⟩,
      reconstruct_block_outside e I B (G.comap Subtype.val) 1 ⟨w, hw⟩]
    exact (hB ⟨w, hw⟩).1.symm
  · intro w hw
    simp only [edgeBit]
    rw [reconstruct_block_outside e I B (G.comap Subtype.val) 2 ⟨w, hw⟩,
      reconstruct_block_outside e I B (G.comap Subtype.val) 3 ⟨w, hw⟩]
    exact (hB ⟨w, hw⟩).2.symm

variable [Fintype V]

theorem degree_eq_sum_bits (G : SimpleGraph V) (v : V) :
    G.degree v = ∑ w, if G.Adj v w then (1 : Nat) else 0 := by
  simpa using G.degree_eq_sum_if_adj (R := Nat) v

theorem degree_reconstruct_block (e : Fin 4 ↪ V) (I : SimpleGraph (Fin 4))
    (B : Fin 4 → {w : V // Outside e w} → Prop)
    (O : SimpleGraph {w : V // Outside e w}) (a : Fin 4) :
    (reconstruct e I B O).degree (e a) =
      I.degree a + (Finset.univ.filter (fun w => B a w)).card := by
  rw [degree_eq_sum_bits (reconstruct e I B O) _,
    ← (blockEquiv e).sum_comp
      (fun v => if (reconstruct e I B O).Adj (e a) v then (1 : Nat) else 0),
    Fintype.sum_sum_type]
  simp only [blockEquiv_inl, blockEquiv_inr, reconstruct_block_block,
    reconstruct_block_outside, degree_eq_sum_bits, Finset.card_filter]

theorem degree_reconstruct_outside (e : Fin 4 ↪ V) (I : SimpleGraph (Fin 4))
    (B : Fin 4 → {w : V // Outside e w} → Prop)
    (O : SimpleGraph {w : V // Outside e w}) (w : {w : V // Outside e w}) :
    (reconstruct e I B O).degree w.val =
      (Finset.univ.filter (fun a => B a w)).card + O.degree w := by
  rw [degree_eq_sum_bits (reconstruct e I B O) _,
    ← (blockEquiv e).sum_comp
      (fun v => if (reconstruct e I B O).Adj w.val v then (1 : Nat) else 0),
    Fintype.sum_sum_type]
  simp only [blockEquiv_inl, blockEquiv_inr, reconstruct_outside_block,
    reconstruct_outside_outside, degree_eq_sum_bits, Finset.card_filter]

theorem degree_outside_preserved (e : Fin 4 ↪ V) (G : SimpleGraph V)
    (I : SimpleGraph (Fin 4))
    (B : Fin 4 → {w : V // Outside e w} → Prop)
    (hB : BoundaryMatches e G B) (w : {w : V // Outside e w}) :
    (reconstruct e I B (G.comap Subtype.val)).degree w.val = G.degree w.val := by
  have hcolumn : (Finset.univ.filter (fun a => B a w)).card =
      (Finset.univ.filter (fun a : Fin 4 => G.Adj (e a) w.val)).card := by
    simp only [Finset.card_filter, Fin.sum_univ_four]
    have h1 := (hB w).1
    have h2 := (hB w).2
    simp only [edgeBit] at h1 h2
    omega
  have hG := degree_reconstruct_outside e (G.comap e)
    (fun a w => G.Adj (e a) w.val) (G.comap Subtype.val) w
  rw [reconstruct_graph] at hG
  rw [degree_reconstruct_outside, hcolumn]
  exact hG.symm

theorem degree_preserved_of_block (e : Fin 4 ↪ V) (G : SimpleGraph V)
    (I : SimpleGraph (Fin 4))
    (B : Fin 4 → {w : V // Outside e w} → Prop)
    (hB : BoundaryMatches e G B)
    (hblock : ∀ a, I.degree a + (Finset.univ.filter (fun w => B a w)).card =
      G.degree (e a)) :
    ∀ v, (reconstruct e I B (G.comap Subtype.val)).degree v = G.degree v := by
  intro v
  obtain ⟨v, rfl⟩ := (blockEquiv e).surjective v
  cases v with
  | inl a =>
    change (reconstruct e I B (G.comap Subtype.val)).degree (e a) = G.degree (e a)
    rw [degree_reconstruct_block]
    exact hblock a
  | inr w => exact degree_outside_preserved e G I B hB w

end Problem315.DisjointEncoding

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.DisjointBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace Problem315.DisjointEncoding

variable {V : Type*} [sectionFintypeV : Fintype V]

def leftCounts (e : Fin 4 ↪ V) (G : SimpleGraph V) (w : {w : V // Outside e w}) : Nat :=
  edgeBit G (e 0) w.val + edgeBit G (e 1) w.val

def rightCounts (e : Fin 4 ↪ V) (G : SimpleGraph V) (w : {w : V // Outside e w}) : Nat :=
  edgeBit G (e 2) w.val + edgeBit G (e 3) w.val

include sectionFintypeV in
theorem edgeBit_le_one (G : SimpleGraph V) (u v : V) : edgeBit G u v ≤ 1 := by
  have retainedsectionFintypeV := sectionFintypeV
  unfold edgeBit
  split_ifs <;> omega

theorem leftCounts_le_two (e : Fin 4 ↪ V) (G : SimpleGraph V)
    (w : {w : V // Outside e w}) : leftCounts e G w ≤ 2 := by
  have h0 := edgeBit_le_one G (e 0) w.val
  have h1 := edgeBit_le_one G (e 1) w.val
  unfold leftCounts
  omega

theorem rightCounts_le_two (e : Fin 4 ↪ V) (G : SimpleGraph V)
    (w : {w : V // Outside e w}) : rightCounts e G w ≤ 2 := by
  have h0 := edgeBit_le_one G (e 2) w.val
  have h1 := edgeBit_le_one G (e 3) w.val
  unfold rightCounts
  omega

def assignmentBoundary (e : Fin 4 ↪ V) (G : SimpleGraph V)
    (U W : Finset {w : V // Outside e w}) :
    Fin 4 → {w : V // Outside e w} → Prop :=
  ![BinaryAssignments.first (leftCounts e G) U,
    BinaryAssignments.second (leftCounts e G) U,
    BinaryAssignments.first (rightCounts e G) W,
    BinaryAssignments.second (rightCounts e G) W]

theorem assignmentBoundary_matches (e : Fin 4 ↪ V) (G : SimpleGraph V)
    (U W : Finset {w : V // Outside e w})
    (hU : U ⊆ BinaryAssignments.singletons (leftCounts e G))
    (hW : W ⊆ BinaryAssignments.singletons (rightCounts e G)) :
    BoundaryMatches e G (assignmentBoundary e G U W) := by
  intro w
  constructor
  · exact BinaryAssignments.indicator_sum (leftCounts e G) (leftCounts_le_two e G) U hU w
  · exact BinaryAssignments.indicator_sum (rightCounts e G) (rightCounts_le_two e G) W hW w

theorem assignmentBoundary_card_zero (e : Fin 4 ↪ V) (G : SimpleGraph V)
    (U W : Finset {w : V // Outside e w})
    (hU : U ⊆ BinaryAssignments.singletons (leftCounts e G)) :
    (Finset.univ.filter (assignmentBoundary e G U W 0)).card =
      (BinaryAssignments.common (leftCounts e G)).card + U.card :=
  BinaryAssignments.first_card _ _ hU

theorem assignmentBoundary_card_one (e : Fin 4 ↪ V) (G : SimpleGraph V)
    (U W : Finset {w : V // Outside e w})
    (hU : U ⊆ BinaryAssignments.singletons (leftCounts e G)) :
    (Finset.univ.filter (assignmentBoundary e G U W 1)).card + U.card =
      (BinaryAssignments.common (leftCounts e G)).card +
        (BinaryAssignments.singletons (leftCounts e G)).card :=
  BinaryAssignments.second_card_add _ _ hU

theorem assignmentBoundary_card_two (e : Fin 4 ↪ V) (G : SimpleGraph V)
    (U W : Finset {w : V // Outside e w})
    (hW : W ⊆ BinaryAssignments.singletons (rightCounts e G)) :
    (Finset.univ.filter (assignmentBoundary e G U W 2)).card =
      (BinaryAssignments.common (rightCounts e G)).card + W.card :=
  BinaryAssignments.first_card _ _ hW

theorem assignmentBoundary_card_three (e : Fin 4 ↪ V) (G : SimpleGraph V)
    (U W : Finset {w : V // Outside e w})
    (hW : W ⊆ BinaryAssignments.singletons (rightCounts e G)) :
    (Finset.univ.filter (assignmentBoundary e G U W 3)).card + W.card =
      (BinaryAssignments.common (rightCounts e G)).card +
        (BinaryAssignments.singletons (rightCounts e G)).card :=
  BinaryAssignments.second_card_add _ _ hW

end Problem315.DisjointEncoding

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.DisjointInternal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace Problem315.DisjointEncoding

def internalAdj (l r : Bool) (M : CrossBlock.Matrix) : Fin 4 → Fin 4 → Bool :=
  ![![false, l, M 0 0, M 0 1],
    ![l, false, M 1 0, M 1 1],
    ![M 0 0, M 1 0, false, r],
    ![M 0 1, M 1 1, r, false]]

def internalGraph (l r : Bool) (M : CrossBlock.Matrix) : SimpleGraph (Fin 4) where
  Adj a b := internalAdj l r M a b = true
  symm := by
    constructor
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [internalAdj]
  loopless := by
    constructor
    intro a h
    fin_cases a <;> simp_all [internalAdj]

@[simp] theorem internalGraph_left (l r : Bool) (M : CrossBlock.Matrix) :
    (internalGraph l r M).Adj 0 1 ↔ l = true := by simp [internalGraph, internalAdj]

@[simp] theorem internalGraph_right (l r : Bool) (M : CrossBlock.Matrix) :
    (internalGraph l r M).Adj 2 3 ↔ r = true := by simp [internalGraph, internalAdj]

@[simp] theorem internalGraph_cross (l r : Bool) (M : CrossBlock.Matrix) (a b : Fin 2) :
    (internalGraph l r M).Adj (leftIndex a) (rightIndex b) ↔ M a b = true := by
  fin_cases a <;> fin_cases b <;> simp [internalGraph, internalAdj, leftIndex, rightIndex]

theorem internalGraph_degree_left (l r : Bool) (M : CrossBlock.Matrix) (a : Fin 2) :
    (internalGraph l r M).degree (leftIndex a) =
      (if l then 1 else 0) + CrossBlock.row M a := by
  rw [degree_eq_sum_bits, Fin.sum_univ_four]
  simp only [CrossBlock.row, Fin.sum_univ_two, CrossBlock.entry]
  fin_cases a <;>
    simp [internalGraph, internalAdj, leftIndex] <;> ring_nf

theorem internalGraph_degree_right (l r : Bool) (M : CrossBlock.Matrix) (a : Fin 2) :
    (internalGraph l r M).degree (rightIndex a) =
      (if r then 1 else 0) + CrossBlock.col M a := by
  rw [degree_eq_sum_bits, Fin.sum_univ_four]
  simp only [CrossBlock.col, Fin.sum_univ_two, CrossBlock.entry]
  fin_cases a <;>
    simp [internalGraph, internalAdj, rightIndex] <;> ring_nf

end Problem315.DisjointEncoding

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.DisjointRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace Problem315.DisjointEncoding

variable {V : Type*} [sectionFintypeV : Fintype V]

def crossCode (e : Fin 4 ↪ V) (G : SimpleGraph V) : CrossBlock.Matrix :=
  fun a b => decide (G.Adj (e (leftIndex a)) (e (rightIndex b)))

def leftAssignment (e : Fin 4 ↪ V) (G H : SimpleGraph V) :
    Finset {w : V // Outside e w} :=
  (BinaryAssignments.singletons (leftCounts e G)).filter (fun w => H.Adj (e 0) w.val)

def rightAssignment (e : Fin 4 ↪ V) (G H : SimpleGraph V) :
    Finset {w : V // Outside e w} :=
  (BinaryAssignments.singletons (rightCounts e G)).filter (fun w => H.Adj (e 2) w.val)

def realizeCoordinates (e : Fin 4 ↪ V) (G : SimpleGraph V)
    (M : CrossBlock.Matrix) (U W : Finset {w : V // Outside e w}) : SimpleGraph V :=
  reconstruct e (internalGraph (decide (G.Adj (e 0) (e 1)))
    (decide (G.Adj (e 2) (e 3))) M) (assignmentBoundary e G U W) (G.comap Subtype.val)

theorem realizeCoordinates_sameCell (e : Fin 4 ↪ V) (G : SimpleGraph V)
    (M : CrossBlock.Matrix) (U W : Finset {w : V // Outside e w})
    (hU : U ⊆ BinaryAssignments.singletons (leftCounts e G))
    (hW : W ⊆ BinaryAssignments.singletons (rightCounts e G)) :
    SameCell e G (realizeCoordinates e G M U W) := by
  apply sameCell_reconstruct
  · simp
  · simp
  · exact assignmentBoundary_matches e G U W hU hW

@[simp] theorem crossCode_realizeCoordinates (e : Fin 4 ↪ V) (G : SimpleGraph V)
    (M : CrossBlock.Matrix) (U W : Finset {w : V // Outside e w}) :
    crossCode e (realizeCoordinates e G M U W) = M := by
  have retainedsectionFintypeV := sectionFintypeV
  funext a b
  simp [crossCode, realizeCoordinates]

theorem leftAssignment_realizeCoordinates (e : Fin 4 ↪ V) (G : SimpleGraph V)
    (M : CrossBlock.Matrix) (U W : Finset {w : V // Outside e w})
    (hU : U ⊆ BinaryAssignments.singletons (leftCounts e G)) :
    leftAssignment e G (realizeCoordinates e G M U W) = U := by
  ext w
  simp only [leftAssignment, Finset.mem_filter, realizeCoordinates,
    reconstruct_block_outside]
  change (w ∈ BinaryAssignments.singletons (leftCounts e G) ∧
    BinaryAssignments.first (leftCounts e G) U w) ↔ w ∈ U
  constructor
  · intro h
    exact (BinaryAssignments.first_on_singletons _ U w h.1).mp h.2
  · intro h
    exact ⟨hU h, (BinaryAssignments.first_on_singletons _ U w (hU h)).mpr h⟩

theorem rightAssignment_realizeCoordinates (e : Fin 4 ↪ V) (G : SimpleGraph V)
    (M : CrossBlock.Matrix) (U W : Finset {w : V // Outside e w})
    (hW : W ⊆ BinaryAssignments.singletons (rightCounts e G)) :
    rightAssignment e G (realizeCoordinates e G M U W) = W := by
  ext w
  simp only [rightAssignment, Finset.mem_filter, realizeCoordinates,
    reconstruct_block_outside]
  change (w ∈ BinaryAssignments.singletons (rightCounts e G) ∧
    BinaryAssignments.first (rightCounts e G) W w) ↔ w ∈ W
  constructor
  · intro h
    exact (BinaryAssignments.first_on_singletons _ W w h.1).mp h.2
  · intro h
    exact ⟨hW h, (BinaryAssignments.first_on_singletons _ W w (hW h)).mpr h⟩

theorem first_edge_iff_of_counts (G H K : SimpleGraph V) (i j w : V)
    (hH : edgeBit G i w + edgeBit G j w = edgeBit H i w + edgeBit H j w)
    (hK : edgeBit G i w + edgeBit G j w = edgeBit K i w + edgeBit K j w)
    (hsingle : edgeBit G i w + edgeBit G j w = 1 → (H.Adj i w ↔ K.Adj i w)) :
    H.Adj i w ↔ K.Adj i w := by
  by_cases h : edgeBit G i w + edgeBit G j w = 1
  · exact hsingle h
  · apply (edgeBit_eq_iff H K i w).mp
    have hHi := edgeBit_le_one H i w
    have hHj := edgeBit_le_one H j w
    have hKi := edgeBit_le_one K i w
    have hKj := edgeBit_le_one K j w
    omega

theorem graph_eq_of_cell_assignments (e : Fin 4 ↪ V) (G H K : SimpleGraph V)
    (hH : SameCell e G H) (hK : SameCell e G K)
    (hM : crossCode e H = crossCode e K)
    (hU : leftAssignment e G H = leftAssignment e G K)
    (hW : rightAssignment e G H = rightAssignment e G K) : H = K := by
  apply graph_eq_of_cell_coordinates e H K (hH.symm.trans hK)
  constructor
  · have h := congrFun (congrFun hM 0) 0
    simpa [crossCode, leftIndex, rightIndex] using h
  · have h := congrFun (congrFun hM 0) 1
    simpa [crossCode, leftIndex, rightIndex] using h
  · have h := congrFun (congrFun hM 1) 0
    simpa [crossCode, leftIndex, rightIndex] using h
  · have h := congrFun (congrFun hM 1) 1
    simpa [crossCode, leftIndex, rightIndex] using h
  · intro w hw
    apply first_edge_iff_of_counts G H K (e 0) (e 1) w
      (hH.leftCount w hw) (hK.leftCount w hw)
    intro hs
    have h := Finset.ext_iff.mp hU ⟨w, hw⟩
    have member : ⟨w, hw⟩ ∈ BinaryAssignments.singletons (leftCounts e G) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩
    constructor
    · intro adjacent
      exact (Finset.mem_filter.mp (h.mp (Finset.mem_filter.mpr ⟨member, adjacent⟩))).2
    · intro adjacent
      exact (Finset.mem_filter.mp (h.mpr (Finset.mem_filter.mpr ⟨member, adjacent⟩))).2
  · intro w hw
    apply first_edge_iff_of_counts G H K (e 2) (e 3) w
      (hH.rightCount w hw) (hK.rightCount w hw)
    intro hs
    have h := Finset.ext_iff.mp hW ⟨w, hw⟩
    have member : ⟨w, hw⟩ ∈ BinaryAssignments.singletons (rightCounts e G) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩
    constructor
    · intro adjacent
      exact (Finset.mem_filter.mp (h.mp (Finset.mem_filter.mpr ⟨member, adjacent⟩))).2
    · intro adjacent
      exact (Finset.mem_filter.mp (h.mpr (Finset.mem_filter.mpr ⟨member, adjacent⟩))).2

theorem realizeCoordinates_encode (e : Fin 4 ↪ V) (G H : SimpleGraph V)
    (hH : SameCell e G H) :
    realizeCoordinates e G (crossCode e H) (leftAssignment e G H)
      (rightAssignment e G H) = H := by
  have hU : leftAssignment e G H ⊆ BinaryAssignments.singletons (leftCounts e G) :=
    Finset.filter_subset _ _
  have hW : rightAssignment e G H ⊆ BinaryAssignments.singletons (rightCounts e G) :=
    Finset.filter_subset _ _
  apply graph_eq_of_cell_assignments e G _ H
    (realizeCoordinates_sameCell e G _ _ _ hU hW) hH
  · exact crossCode_realizeCoordinates e G _ _ _
  · exact leftAssignment_realizeCoordinates e G _ _ _ hU
  · exact rightAssignment_realizeCoordinates e G _ _ _ hW

@[ext] structure FeasibleCoordinates (e : Fin 4 ↪ V) (G : SimpleGraph V) where
  matrix : CrossBlock.Matrix
  left : Finset {w : V // Outside e w}
  right : Finset {w : V // Outside e w}
  left_subset : left ⊆ BinaryAssignments.singletons (leftCounts e G)
  right_subset : right ⊆ BinaryAssignments.singletons (rightCounts e G)
  degrees : ∀ a,
    (internalGraph (decide (G.Adj (e 0) (e 1))) (decide (G.Adj (e 2) (e 3))) matrix).degree a +
      (Finset.univ.filter (assignmentBoundary e G left right a)).card = G.degree (e a)

abbrev DegreeCell (e : Fin 4 ↪ V) (G : SimpleGraph V) :=
  {H : SimpleGraph V // SameCell e G H ∧ ∀ v, H.degree v = G.degree v}

def cellEncode (e : Fin 4 ↪ V) (G : SimpleGraph V) (H : DegreeCell e G) :
    FeasibleCoordinates e G where
  matrix := crossCode e H.val
  left := leftAssignment e G H.val
  right := rightAssignment e G H.val
  left_subset := Finset.filter_subset _ _
  right_subset := Finset.filter_subset _ _
  degrees := by
    intro a
    have h := congrArg (fun K : SimpleGraph V => K.degree (e a))
      (realizeCoordinates_encode e G H.val H.property.1)
    unfold realizeCoordinates at h
    rw [degree_reconstruct_block] at h
    exact h.trans (H.property.2 (e a))

def cellDecode (e : Fin 4 ↪ V) (G : SimpleGraph V) (c : FeasibleCoordinates e G) :
    DegreeCell e G :=
  ⟨realizeCoordinates e G c.matrix c.left c.right,
    realizeCoordinates_sameCell e G _ _ _ c.left_subset c.right_subset,
    degree_preserved_of_block e G _ _
      (assignmentBoundary_matches e G _ _ c.left_subset c.right_subset) c.degrees⟩

def degreeCellEquiv (e : Fin 4 ↪ V) (G : SimpleGraph V) :
    DegreeCell e G ≃ FeasibleCoordinates e G where
  toFun := cellEncode e G
  invFun := cellDecode e G
  left_inv H := by
    apply Subtype.ext
    exact realizeCoordinates_encode e G H.val H.property.1
  right_inv c := by
    apply FeasibleCoordinates.ext
    · exact crossCode_realizeCoordinates e G _ _ _
    · exact leftAssignment_realizeCoordinates e G _ _ _ c.left_subset
    · exact rightAssignment_realizeCoordinates e G _ _ _ c.right_subset

end Problem315.DisjointEncoding

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.DisjointCoordinateFeasibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace Problem315.CrossBlock

theorem total_eq_row_add (M : Matrix) : total M = row M 0 + row M 1 := by
  simp [total, Fin.sum_univ_two]

theorem total_eq_col_add (M : Matrix) : total M = col M 0 + col M 1 := by
  simp only [total, row, col, Fin.sum_univ_two]
  omega

end Problem315.CrossBlock

namespace Problem315.DisjointEncoding
variable {V : Type*} [Fintype V]

theorem coordinate_degrees_iff
    (e : Fin 4 ↪ V) (G : SimpleGraph V)
    (M : CrossBlock.Matrix) (U W : Finset {w : V // Outside e w})
    (hU : U ⊆ BinaryAssignments.singletons (leftCounts e G))
    (hW : W ⊆ BinaryAssignments.singletons (rightCounts e G)) :
    (∀ a,
      (internalGraph (decide (G.Adj (e 0) (e 1)))
        (decide (G.Adj (e 2) (e 3))) M).degree a +
        (Finset.univ.filter (assignmentBoundary e G U W a)).card = G.degree (e a)) ↔
    CrossBlock.total M = CrossBlock.total (crossCode e G) ∧
      CrossBlock.row M 0 + U.card =
        CrossBlock.row (crossCode e G) 0 + (leftAssignment e G G).card ∧
      CrossBlock.col M 0 + W.card =
        CrossBlock.col (crossCode e G) 0 + (rightAssignment e G G).card := by
  let l := decide (G.Adj (e 0) (e 1))
  let r := decide (G.Adj (e 2) (e 3))
  let M₀ := crossCode e G
  let U₀ := leftAssignment e G G
  let W₀ := rightAssignment e G G
  have hU₀ : U₀ ⊆ BinaryAssignments.singletons (leftCounts e G) := Finset.filter_subset _ _
  have hW₀ : W₀ ⊆ BinaryAssignments.singletons (rightCounts e G) := Finset.filter_subset _ _
  have hbase := (cellEncode e G ⟨G, SameCell.refl e G, fun _ => rfl⟩).degrees
  change ∀ a, (internalGraph l r M₀).degree a +
    (Finset.univ.filter (assignmentBoundary e G U₀ W₀ a)).card = G.degree (e a) at hbase
  have hbase0 := hbase 0
  have hbase1 := hbase 1
  have hbase2 := hbase 2
  have hbase3 := hbase 3
  have hd0 := internalGraph_degree_left l r M 0
  have hd1 := internalGraph_degree_left l r M 1
  have hd2 := internalGraph_degree_right l r M 0
  have hd3 := internalGraph_degree_right l r M 1
  have hd00 := internalGraph_degree_left l r M₀ 0
  have hd01 := internalGraph_degree_left l r M₀ 1
  have hd02 := internalGraph_degree_right l r M₀ 0
  have hd03 := internalGraph_degree_right l r M₀ 1
  change (internalGraph l r M).degree 0 = _ at hd0
  change (internalGraph l r M).degree 1 = _ at hd1
  change (internalGraph l r M).degree 2 = _ at hd2
  change (internalGraph l r M).degree 3 = _ at hd3
  change (internalGraph l r M₀).degree 0 = _ at hd00
  change (internalGraph l r M₀).degree 1 = _ at hd01
  change (internalGraph l r M₀).degree 2 = _ at hd02
  change (internalGraph l r M₀).degree 3 = _ at hd03
  have hb0 := assignmentBoundary_card_zero e G U W hU
  have hb1 := assignmentBoundary_card_one e G U W hU
  have hb2 := assignmentBoundary_card_two e G U W hW
  have hb3 := assignmentBoundary_card_three e G U W hW
  have hb00 := assignmentBoundary_card_zero e G U₀ W₀ hU₀
  have hb01 := assignmentBoundary_card_one e G U₀ W₀ hU₀
  have hb02 := assignmentBoundary_card_two e G U₀ W₀ hW₀
  have hb03 := assignmentBoundary_card_three e G U₀ W₀ hW₀
  have ht := CrossBlock.total_eq_row_add M
  have ht₀ := CrossBlock.total_eq_row_add M₀
  have hc := CrossBlock.total_eq_col_add M
  have hc₀ := CrossBlock.total_eq_col_add M₀
  change (∀ a, (internalGraph l r M).degree a +
    (Finset.univ.filter (assignmentBoundary e G U W a)).card = G.degree (e a)) ↔
    CrossBlock.total M = CrossBlock.total M₀ ∧
      CrossBlock.row M 0 + U.card = CrossBlock.row M₀ 0 + U₀.card ∧
      CrossBlock.col M 0 + W.card = CrossBlock.col M₀ 0 + W₀.card
  constructor
  · intro h
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    omega
  · rintro ⟨htotal, hleft, hright⟩ a
    have h0 : (internalGraph l r M).degree 0 +
        (Finset.univ.filter (assignmentBoundary e G U W 0)).card = G.degree (e 0) := by omega
    have h1 : (internalGraph l r M).degree 1 +
        (Finset.univ.filter (assignmentBoundary e G U W 1)).card = G.degree (e 1) := by omega
    have h2 : (internalGraph l r M).degree 2 +
        (Finset.univ.filter (assignmentBoundary e G U W 2)).card = G.degree (e 2) := by omega
    have h3 : (internalGraph l r M).degree 3 +
        (Finset.univ.filter (assignmentBoundary e G U W 3)).card = G.degree (e 3) := by omega
    fin_cases a
    · exact h0
    · exact h1
    · exact h2
    · exact h3

end Problem315.DisjointEncoding

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.DisjointCellCounting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace Problem315.DisjointMarginal

variable {V : Type*} [Fintype V]
open DisjointEncoding

abbrev MarginData {α : Type*} [Fintype α] (A : Finset α) (q : Nat) :=
  {x : Fin 3 × Finset α // x.2 ⊆ A ∧ x.1.val + x.2.card = q}

abbrev LeftData (e : Fin 4 ↪ V) (G : SimpleGraph V) :=
  MarginData (BinaryAssignments.singletons (leftCounts e G))
    (CrossBlock.row (crossCode e G) 0 + (leftAssignment e G G).card)

abbrev RightData (e : Fin 4 ↪ V) (G : SimpleGraph V) :=
  MarginData (BinaryAssignments.singletons (rightCounts e G))
    (CrossBlock.col (crossCode e G) 0 + (rightAssignment e G G).card)

abbrev MatrixFiber (s : Nat) (r c : Fin 3) :=
  {M : CrossBlock.Matrix // CrossBlock.total M = s ∧
    CrossBlock.row M 0 = r.val ∧ CrossBlock.col M 0 = c.val}

abbrev JointData (e : Fin 4 ↪ V) (G : SimpleGraph V) :=
  Σ x : LeftData e G, Σ y : RightData e G,
    MatrixFiber (CrossBlock.total (crossCode e G)) x.val.1 y.val.1

def leftData (e : Fin 4 ↪ V) (G : SimpleGraph V) (c : FeasibleCoordinates e G) :
    LeftData e G :=
  ⟨(⟨CrossBlock.row c.matrix 0, by have := CrossBlock.row_le_two c.matrix 0; omega⟩, c.left),
    c.left_subset,
    ((coordinate_degrees_iff e G c.matrix c.left c.right c.left_subset c.right_subset).mp
      c.degrees).2.1⟩

def rightData (e : Fin 4 ↪ V) (G : SimpleGraph V) (c : FeasibleCoordinates e G) :
    RightData e G :=
  ⟨(⟨CrossBlock.col c.matrix 0, by have := CrossBlock.col_le_two c.matrix 0; omega⟩, c.right),
    c.right_subset,
    ((coordinate_degrees_iff e G c.matrix c.left c.right c.left_subset c.right_subset).mp
      c.degrees).2.2⟩

def toJointData (e : Fin 4 ↪ V) (G : SimpleGraph V) (c : FeasibleCoordinates e G) :
    JointData e G :=
  ⟨leftData e G c, rightData e G c, c.matrix,
    ((coordinate_degrees_iff e G c.matrix c.left c.right c.left_subset c.right_subset).mp
      c.degrees).1, rfl, rfl⟩

def fromJointData (e : Fin 4 ↪ V) (G : SimpleGraph V) (z : JointData e G) :
    FeasibleCoordinates e G where
  matrix := z.2.2.val
  left := z.1.val.2
  right := z.2.1.val.2
  left_subset := z.1.property.1
  right_subset := z.2.1.property.1
  degrees := by
    apply (coordinate_degrees_iff e G _ _ _ z.1.property.1 z.2.1.property.1).mpr
    exact ⟨z.2.2.property.1,
      by rw [z.2.2.property.2.1]; exact z.1.property.2,
      by rw [z.2.2.property.2.2]; exact z.2.1.property.2⟩

def coordinatesEquiv (e : Fin 4 ↪ V) (G : SimpleGraph V) :
    FeasibleCoordinates e G ≃ JointData e G where
  toFun := toJointData e G
  invFun := fromJointData e G
  left_inv c := by ext <;> rfl
  right_inv z := by
    rcases z with ⟨⟨⟨⟨r,hrlt⟩,U⟩,hU⟩, ⟨⟨⟨c,hclt⟩,W⟩,hW⟩, M, hs, hr, hc⟩
    dsimp only at hr hc
    subst r
    subst c
    rfl

def degreeCellJointEquiv (e : Fin 4 ↪ V) (G : SimpleGraph V) :
    DegreeCell e G ≃ JointData e G :=
  (degreeCellEquiv e G).trans (coordinatesEquiv e G)

def flag (r : Fin 3) : ℝ := if r = 1 then 0 else 1

end Problem315.DisjointMarginal

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.DisjointStateCell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical

namespace Problem315.DisjointEncoding

theorem qualified_degree (n : Nat) (G : SimpleGraph (Fin n)) (v : Fin n) :
    graphDegree G v = G.degree v := by
  unfold graphDegree SimpleGraph.degree
  congr 1
  ext w
  simp

def stateCellToDegreeCell {n : Nat} {d : Fin n → Nat}
    (e : Fin 4 ↪ Fin n) (G : GraphState n d) :
    {H : GraphState n d // SameCell e G.val H.val} ≃ DegreeCell e G.val where
  toFun H := ⟨H.val.val, H.property, by
    intro v
    rw [← qualified_degree, ← qualified_degree]
    exact (H.val.property v).trans (G.property v).symm⟩
  invFun H := ⟨⟨H.val, by
    intro v
    rw [qualified_degree, H.property.2 v, ← qualified_degree]
    exact G.property v⟩, H.property.1⟩
  left_inv H := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv H := by apply Subtype.ext; rfl

def graphStateCellEquiv {n : Nat} {d : Fin n → Nat}
    (e : Fin 4 ↪ Fin n) (G : GraphState n d) :
    {H : GraphState n d // SameCell e G.val H.val} ≃ FeasibleCoordinates e G.val :=
  (stateCellToDegreeCell e G).trans (degreeCellEquiv e G.val)

end Problem315.DisjointEncoding

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.DisjointStateLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace Problem315.DisjointMarginal
open DisjointEncoding

variable {n : Nat} {d : Fin n → Nat}

abbrev StateCell (e : Fin 4 ↪ Fin n) (G : GraphState n d) :=
  {H : GraphState n d // SameCell e G.val H.val}

instance stateCellNonempty (e : Fin 4 ↪ Fin n) (G : GraphState n d) :
    Nonempty (StateCell e G) := ⟨⟨G, SameCell.refl e G.val⟩⟩

def stateLeftData (e : Fin 4 ↪ Fin n) (G : GraphState n d) (H : StateCell e G) :
    LeftData e G.val := leftData e G.val (graphStateCellEquiv e G H)

def stateRightData (e : Fin 4 ↪ Fin n) (G : GraphState n d) (H : StateCell e G) :
    RightData e G.val := rightData e G.val (graphStateCellEquiv e G H)

@[simp] theorem stateLeftData_subset (e : Fin 4 ↪ Fin n) (G : GraphState n d)
    (H : StateCell e G) : (stateLeftData e G H).val.2 = leftAssignment e G.val H.val.val := rfl

@[simp] theorem stateRightData_subset (e : Fin 4 ↪ Fin n) (G : GraphState n d)
    (H : StateCell e G) : (stateRightData e G H).val.2 = rightAssignment e G.val H.val.val := rfl

def stateCellJointEquiv (e : Fin 4 ↪ Fin n) (G : GraphState n d) :
    StateCell e G ≃ JointData e G.val :=
  (stateCellToDegreeCell e G).trans (degreeCellJointEquiv e G.val)

end Problem315.DisjointMarginal

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.DisjointCrossCellEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.DisjointMarginal
attribute [local instance] Classical.propDecidable
open DisjointEncoding

variable {V : Type*} [Fintype V]

def jointCrossEquiv (e : Fin 4 ↪ V) (G : SimpleGraph V) :
    JointData e G ≃ CrossCellMoments.Cell (CrossBlock.total (crossCode e G))
      (fun x : LeftData e G => x.val.1) (fun y : RightData e G => y.val.1) where
  toFun z := ⟨(z.2.2.val, z.1, z.2.1), z.2.2.property⟩
  invFun z := ⟨z.val.2.1, z.val.2.2, z.val.1, z.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable {n : Nat} {d : Fin n → Nat}

abbrev CrossCell (e : Fin 4 ↪ Fin n) (G : GraphState n d) :=
  CrossCellMoments.Cell (CrossBlock.total (crossCode e G.val))
    (fun x : LeftData e G.val => x.val.1) (fun y : RightData e G.val => y.val.1)

def stateCellCrossEquiv (e : Fin 4 ↪ Fin n) (G : GraphState n d) :
    StateCell e G ≃ CrossCell e G :=
  (stateCellJointEquiv e G).trans (jointCrossEquiv e G.val)

@[simp] theorem stateCellCrossEquiv_left (e : Fin 4 ↪ Fin n) (G : GraphState n d)
    (H : StateCell e G) :
    (stateCellCrossEquiv e G H).val.2.1 = stateLeftData e G H := rfl

@[simp] theorem stateCellCrossEquiv_right (e : Fin 4 ↪ Fin n) (G : GraphState n d)
    (H : StateCell e G) :
    (stateCellCrossEquiv e G H).val.2.2 = stateRightData e G H := rfl

@[simp] theorem stateCellCrossEquiv_matrix (e : Fin 4 ↪ Fin n) (G : GraphState n d)
    (H : StateCell e G) :
    (stateCellCrossEquiv e G H).val.1 = crossCode e H.val.val := rfl

end Problem315.DisjointMarginal

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.PairFiber
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.PairFiber

variable {V : Type*} [sectionFintypeV : Fintype V]

def Outside (i j w : V) : Prop := w ≠ i ∧ w ≠ j

def edgeBit (G : SimpleGraph V) (u v : V) : Nat := by
  classical
  exact if G.Adj u v then 1 else 0

def key (i j : V) (G : SimpleGraph V) :
    (V → V → Prop) × Prop × (V → Nat) :=
  (fun u v => Outside i j u ∧ Outside i j v ∧ G.Adj u v,
   G.Adj i j, fun w => edgeBit G i w + edgeBit G j w)

def singletonSet (G : SimpleGraph V) (i j : V) : Finset V := by
  classical
  exact Finset.univ.filter (fun w => Outside i j w ∧ Xor (G.Adj i w) (G.Adj j w))

def leftSet (G : SimpleGraph V) (i j : V) : Finset V := by
  classical
  exact Finset.univ.filter (fun w => Outside i j w ∧ G.Adj i w ∧ ¬ G.Adj j w)

def commonSet (G : SimpleGraph V) (i j : V) : Finset V := by
  classical
  exact Finset.univ.filter (fun w => Outside i j w ∧ G.Adj i w ∧ G.Adj j w)

@[simp] theorem mem_singletonSet (G : SimpleGraph V) (i j w : V) :
    w ∈ singletonSet G i j ↔ Outside i j w ∧ Xor (G.Adj i w) (G.Adj j w) := by
  classical
  simp [singletonSet]

@[simp] theorem mem_leftSet (G : SimpleGraph V) (i j w : V) :
    w ∈ leftSet G i j ↔ Outside i j w ∧ G.Adj i w ∧ ¬ G.Adj j w := by
  classical
  simp [leftSet]

@[simp] theorem mem_commonSet (G : SimpleGraph V) (i j w : V) :
    w ∈ commonSet G i j ↔ Outside i j w ∧ G.Adj i w ∧ G.Adj j w := by
  classical
  simp [commonSet]

theorem leftSet_subset_singletonSet (G : SimpleGraph V) (i j : V) :
    leftSet G i j ⊆ singletonSet G i j := by
  intro w hw
  rcases (mem_leftSet G i j w).mp hw with ⟨ho, hi, hj⟩
  exact (mem_singletonSet G i j w).mpr ⟨ho, Or.inl ⟨hi, hj⟩⟩

include sectionFintypeV in
theorem key_count {i j : V} {G H : SimpleGraph V}
    (h : key i j G = key i j H) (w : V) :
    edgeBit G i w + edgeBit G j w = edgeBit H i w + edgeBit H j w := by
  have retainedsectionFintypeV := sectionFintypeV
  exact
  congrFun (congrArg (fun k => k.2.2) h) w

include sectionFintypeV in
theorem key_internal {i j : V} {G H : SimpleGraph V}
    (h : key i j G = key i j H) : G.Adj i j ↔ H.Adj i j := by
  have retainedsectionFintypeV := sectionFintypeV
  exact
  Iff.of_eq (congrArg (fun k => k.2.1) h)

include sectionFintypeV in
theorem key_outside {i j u v : V} {G H : SimpleGraph V}
    (h : key i j G = key i j H) (hu : Outside i j u) (hv : Outside i j v) :
    G.Adj u v ↔ H.Adj u v := by
  have retainedsectionFintypeV := sectionFintypeV
  have hh := congrFun (congrFun (congrArg Prod.fst h) u) v
  change (Outside i j u ∧ Outside i j v ∧ G.Adj u v) =
    (Outside i j u ∧ Outside i j v ∧ H.Adj u v) at hh
  simpa only [hu, hv, true_and] using Iff.of_eq hh

theorem singletonSet_eq_of_key_eq {i j : V} {G H : SimpleGraph V}
    (h : key i j G = key i j H) : singletonSet G i j = singletonSet H i j := by
  classical
  ext w
  have hc := key_count h w
  by_cases gi : G.Adj i w <;> by_cases gj : G.Adj j w <;>
    by_cases hi : H.Adj i w <;> by_cases hj : H.Adj j w <;>
    simp_all [edgeBit, Xor]

theorem commonSet_eq_of_key_eq {i j : V} {G H : SimpleGraph V}
    (h : key i j G = key i j H) : commonSet G i j = commonSet H i j := by
  classical
  ext w
  have hc := key_count h w
  by_cases gi : G.Adj i w <;> by_cases gj : G.Adj j w <;>
    by_cases hi : H.Adj i w <;> by_cases hj : H.Adj j w <;>
    simp_all [edgeBit]

theorem key_left_adj {i j w : V} {G H : SimpleGraph V}
    (h : key i j G = key i j H)
    (hl : leftSet G i j = leftSet H i j) (ho : Outside i j w) :
    G.Adj i w ↔ H.Adj i w := by
  classical
  have hc := key_count h w
  have hm : w ∈ leftSet G i j ↔ w ∈ leftSet H i j := by rw [hl]
  simp only [mem_leftSet] at hm
  by_cases gi : G.Adj i w <;> by_cases gj : G.Adj j w <;>
    by_cases hi : H.Adj i w <;> by_cases hj : H.Adj j w <;>
    simp_all [edgeBit]

theorem key_right_adj {i j w : V} {G H : SimpleGraph V}
    (h : key i j G = key i j H)
    (hl : leftSet G i j = leftSet H i j) (ho : Outside i j w) :
    G.Adj j w ↔ H.Adj j w := by
  classical
  have hc := key_count h w
  have hm := key_left_adj h hl ho
  by_cases gi : G.Adj i w <;> by_cases gj : G.Adj j w <;>
    by_cases hi : H.Adj i w <;> by_cases hj : H.Adj j w <;>
    simp_all [edgeBit]

theorem graph_eq_of_key_leftSet_eq {i j : V} {G H : SimpleGraph V}
    (h : key i j G = key i j H)
    (hl : leftSet G i j = leftSet H i j) : G = H := by
  classical
  ext u v
  by_cases ui : u = i
  · subst u
    by_cases vi : v = i
    · subst v; simp
    by_cases vj : v = j
    · subst v; exact key_internal h
    exact key_left_adj h hl ⟨vi, vj⟩
  by_cases uj : u = j
  · subst u
    by_cases vi : v = i
    · subst v; simpa only [G.adj_comm, H.adj_comm] using key_internal h
    by_cases vj : v = j
    · subst v; simp
    exact key_right_adj h hl ⟨vi, vj⟩
  by_cases vi : v = i
  · subst v
    simpa only [G.adj_comm, H.adj_comm] using key_left_adj h hl (show Outside i j u from ⟨ui, uj⟩)
  by_cases vj : v = j
  · subst v
    simpa only [G.adj_comm, H.adj_comm] using key_right_adj h hl (show Outside i j u from ⟨ui, uj⟩)
  exact key_outside h ⟨ui, uj⟩ ⟨vi, vj⟩

include sectionFintypeV in
theorem key_swap (G : SimpleGraph V) (i j : V) : key i j G = key j i G := by
  have retainedsectionFintypeV := sectionFintypeV
  apply Prod.ext
  · funext u v
    apply propext
    dsimp [key, Outside]
    tauto
  · apply Prod.ext
    · exact propext (G.adj_comm i j)
    · funext w
      exact Nat.add_comm _ _

def assemble (G : SimpleGraph V) (i j : V) (hij : i ≠ j)
    (A B : Finset V)
    (hA : ∀ w ∈ A, Outside i j w)
    (hB : ∀ w ∈ B, Outside i j w) : SimpleGraph V where
  Adj u v :=
    (Outside i j u ∧ Outside i j v ∧ G.Adj u v) ∨
    (((u = i ∧ v = j) ∨ (u = j ∧ v = i)) ∧ G.Adj i j) ∨
    (u = i ∧ v ∈ A) ∨ (v = i ∧ u ∈ A) ∨
    (u = j ∧ v ∈ B) ∨ (v = j ∧ u ∈ B)
  symm := by
    constructor
    intro u v h
    rcases h with h | h | h | h | h | h
    · exact Or.inl ⟨h.2.1, h.1, G.symm.symm u v h.2.2⟩
    · exact Or.inr (Or.inl ⟨by tauto, h.2⟩)
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h.1, h.2⟩)))
    · exact Or.inr (Or.inr (Or.inl ⟨h.1, h.2⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h.1, h.2⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h.1, h.2⟩))))
  loopless := by
    constructor
    intro v h
    rcases h with h | h | h | h | h | h
    · exact G.irrefl h.2.2
    · rcases h.1 with ⟨hi, hj⟩ | ⟨hj, hi⟩ <;> exact hij (hi.symm.trans hj)
    · exact (hA v h.2).1 h.1
    · exact (hA v h.2).1 h.1
    · exact (hB v h.2).2 h.1
    · exact (hB v h.2).2 h.1

include sectionFintypeV in
theorem assemble_adj_left (G : SimpleGraph V) (i j : V) (hij : i ≠ j)
    (A B : Finset V) (hA : ∀ w ∈ A, Outside i j w)
    (hB : ∀ w ∈ B, Outside i j w) {w : V} (hw : Outside i j w) :
    (assemble G i j hij A B hA hB).Adj i w ↔ w ∈ A := by
  have retainedsectionFintypeV := sectionFintypeV
  simp [assemble, Outside, hij, hw.1, hw.2]

include sectionFintypeV in
theorem assemble_adj_right (G : SimpleGraph V) (i j : V) (hij : i ≠ j)
    (A B : Finset V) (hA : ∀ w ∈ A, Outside i j w)
    (hB : ∀ w ∈ B, Outside i j w) {w : V} (hw : Outside i j w) :
    (assemble G i j hij A B hA hB).Adj j w ↔ w ∈ B := by
  have retainedsectionFintypeV := sectionFintypeV
  simp [assemble, Outside, Ne.symm hij, hw.1, hw.2]

include sectionFintypeV in
theorem assemble_adj_internal (G : SimpleGraph V) (i j : V) (hij : i ≠ j)
    (A B : Finset V) (hA : ∀ w ∈ A, Outside i j w)
    (hB : ∀ w ∈ B, Outside i j w) :
    (assemble G i j hij A B hA hB).Adj i j ↔ G.Adj i j := by
  have retainedsectionFintypeV := sectionFintypeV
  have hja : j ∉ A := fun h => (hA j h).2 rfl
  have hib : i ∉ B := fun h => (hB i h).1 rfl
  simp [assemble, Outside, hij, Ne.symm hij, hja, hib]

include sectionFintypeV in
theorem assemble_adj_outside (G : SimpleGraph V) (i j : V) (hij : i ≠ j)
    (A B : Finset V) (hA : ∀ w ∈ A, Outside i j w)
    (hB : ∀ w ∈ B, Outside i j w) {u v : V}
    (hu : Outside i j u) (hv : Outside i j v) :
    (assemble G i j hij A B hA hB).Adj u v ↔ G.Adj u v := by
  have retainedsectionFintypeV := sectionFintypeV
  simp [assemble, hu, hv, hu.1, hu.2, hv.1, hv.2]

def trade (G : SimpleGraph V) (i j : V) (hij : i ≠ j)
    (T : Finset V) (hT : T ⊆ singletonSet G i j) : SimpleGraph V := by
  classical
  refine assemble G i j hij (commonSet G i j ∪ T)
    (commonSet G i j ∪ (singletonSet G i j \ T)) ?_ ?_
  · intro w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · exact ((mem_commonSet G i j w).mp hw).1
    · exact ((mem_singletonSet G i j w).mp (hT hw)).1
  · intro w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · exact ((mem_commonSet G i j w).mp hw).1
    · exact ((mem_singletonSet G i j w).mp (Finset.mem_sdiff.mp hw).1).1

theorem trade_adj_left (G : SimpleGraph V) (i j : V) (hij : i ≠ j)
    (T : Finset V) (hT : T ⊆ singletonSet G i j)
    {w : V} (hw : Outside i j w) :
    (trade G i j hij T hT).Adj i w ↔ (G.Adj i w ∧ G.Adj j w) ∨ w ∈ T := by
  classical
  unfold trade
  rw [assemble_adj_left _ _ _ _ _ _ _ _ hw]
  simp [hw]

theorem trade_adj_right (G : SimpleGraph V) (i j : V) (hij : i ≠ j)
    (T : Finset V) (hT : T ⊆ singletonSet G i j)
    {w : V} (hw : Outside i j w) :
    (trade G i j hij T hT).Adj j w ↔
      (G.Adj i w ∧ G.Adj j w) ∨ (Xor (G.Adj i w) (G.Adj j w) ∧ w ∉ T) := by
  classical
  unfold trade
  rw [assemble_adj_right _ _ _ _ _ _ _ _ hw]
  simp [hw]

theorem trade_adj_internal (G : SimpleGraph V) (i j : V) (hij : i ≠ j)
    (T : Finset V) (hT : T ⊆ singletonSet G i j) :
    (trade G i j hij T hT).Adj i j ↔ G.Adj i j := by
  unfold trade
  exact assemble_adj_internal _ _ _ _ _ _ _ _

theorem trade_adj_outside (G : SimpleGraph V) (i j : V) (hij : i ≠ j)
    (T : Finset V) (hT : T ⊆ singletonSet G i j)
    {u v : V} (hu : Outside i j u) (hv : Outside i j v) :
    (trade G i j hij T hT).Adj u v ↔ G.Adj u v := by
  unfold trade
  exact assemble_adj_outside _ _ _ _ _ _ _ _ hu hv

include sectionFintypeV in
theorem key_eq_of {i j : V} {G H : SimpleGraph V}
    (ho : ∀ u v, Outside i j u → Outside i j v → (G.Adj u v ↔ H.Adj u v))
    (hi : G.Adj i j ↔ H.Adj i j)
    (hc : ∀ w, edgeBit G i w + edgeBit G j w = edgeBit H i w + edgeBit H j w) :
    key i j G = key i j H := by
  have retainedsectionFintypeV := sectionFintypeV
  apply Prod.ext
  · funext u v
    apply propext
    change (Outside i j u ∧ Outside i j v ∧ G.Adj u v) ↔
      (Outside i j u ∧ Outside i j v ∧ H.Adj u v)
    constructor
    · intro h; exact ⟨h.1, h.2.1, (ho u v h.1 h.2.1).mp h.2.2⟩
    · intro h; exact ⟨h.1, h.2.1, (ho u v h.1 h.2.1).mpr h.2.2⟩
  · exact Prod.ext (propext hi) (funext hc)

theorem key_trade (G : SimpleGraph V) (i j : V) (hij : i ≠ j)
    (T : Finset V) (hT : T ⊆ singletonSet G i j) :
    key i j (trade G i j hij T hT) = key i j G := by
  classical
  apply key_eq_of
  · intro u v hu hv
    exact trade_adj_outside G i j hij T hT hu hv
  · exact trade_adj_internal G i j hij T hT
  · intro w
    by_cases wi : w = i
    · subst w
      have hi := trade_adj_internal G i j hij T hT
      simp only [edgeBit, SimpleGraph.irrefl, ↓reduceIte, zero_add]
      rw [(trade G i j hij T hT).adj_comm, G.adj_comm, hi]
    by_cases wj : w = j
    · subst w
      have hi := trade_adj_internal G i j hij T hT
      simp [edgeBit, hi]
    have ho : Outside i j w := ⟨wi, wj⟩
    have hl := trade_adj_left G i j hij T hT ho
    have hr := trade_adj_right G i j hij T hT ho
    have ht : w ∈ T → Xor (G.Adj i w) (G.Adj j w) :=
      fun hw => ((mem_singletonSet G i j w).mp (hT hw)).2
    simp only [edgeBit, hl, hr]
    by_cases gi : G.Adj i w <;> by_cases gj : G.Adj j w <;>
      by_cases wt : w ∈ T <;> simp_all [Xor]

theorem leftSet_trade (G : SimpleGraph V) (i j : V) (hij : i ≠ j)
    (T : Finset V) (hT : T ⊆ singletonSet G i j) :
    leftSet (trade G i j hij T hT) i j = T := by
  classical
  ext w
  by_cases ho : Outside i j w
  · have hl := trade_adj_left G i j hij T hT ho
    have hr := trade_adj_right G i j hij T hT ho
    have ht : w ∈ T → Xor (G.Adj i w) (G.Adj j w) :=
      fun hw => ((mem_singletonSet G i j w).mp (hT hw)).2
    simp only [mem_leftSet, ho, true_and, hl, hr]
    by_cases gi : G.Adj i w <;> by_cases gj : G.Adj j w <;>
      by_cases wt : w ∈ T <;> simp_all [Xor]
  · have ht : w ∉ T := fun hw => ho ((mem_singletonSet G i j w).mp (hT hw)).1
    simp [ho, ht]

end Problem315.PairFiber

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.PairFiberDegree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace Problem315.PairFiber

theorem edgeBit_symm {V : Type*} [Fintype V]
    (G : SimpleGraph V) (u v : V) : edgeBit G u v = edgeBit G v u := by
  unfold edgeBit
  congr 1
  exact propext (G.adj_comm u v)

theorem graphDegree_eq_sum_edgeBit {n : ℕ} (G : SimpleGraph (Fin n)) (u : Fin n) :
    graphDegree G u = ∑ w, edgeBit G u w := by
  classical
  simp [graphDegree, edgeBit]

theorem degree_left_formula {n : ℕ} (G : SimpleGraph (Fin n))
    {i j : Fin n} (hij : i ≠ j) :
    graphDegree G i = edgeBit G i j + (commonSet G i j).card + (leftSet G i j).card := by
  classical
  have hp (w : Fin n) : edgeBit G i w =
      (if w = j then edgeBit G i j else 0) +
      (if w ∈ commonSet G i j then 1 else 0) +
      (if w ∈ leftSet G i j then 1 else 0) := by
    by_cases hwi : w = i
    · subst w
      simp [edgeBit, Outside, hij]
    by_cases hwj : w = j
    · subst w
      simp [edgeBit, Outside, Ne.symm hij]
    by_cases hiw : G.Adj i w <;> by_cases hjw : G.Adj j w <;>
      simp [edgeBit, Outside, hwi, hwj, hiw, hjw]
  rw [graphDegree_eq_sum_edgeBit]
  calc
    (∑ w, edgeBit G i w) = ∑ w, ((if w = j then edgeBit G i j else 0) +
      (if w ∈ commonSet G i j then 1 else 0) +
      (if w ∈ leftSet G i j then 1 else 0)) :=
        Finset.sum_congr rfl (fun w _ => hp w)
    _ = _ := by simp [Finset.sum_add_distrib, commonSet, leftSet]

theorem leftSet_card_eq_iff_degree_eq {n : ℕ} {G H : SimpleGraph (Fin n)}
    {i j : Fin n} (hij : i ≠ j) (hk : key i j G = key i j H) :
    (leftSet G i j).card = (leftSet H i j).card ↔ graphDegree G i = graphDegree H i := by
  have hi : edgeBit G i j = edgeBit H i j := by
    unfold edgeBit
    congr 1
    exact propext (key_internal hk)
  have hc := commonSet_eq_of_key_eq hk
  rw [degree_left_formula G hij, degree_left_formula H hij, hi, hc]
  omega

theorem singleton_card_split {n : ℕ} (G : SimpleGraph (Fin n)) (i j : Fin n) :
    (singletonSet G i j).card = (leftSet G i j).card + (leftSet G j i).card := by
  classical
  have hu : singletonSet G i j = leftSet G i j ∪ leftSet G j i := by
    ext w
    simp only [mem_singletonSet, Finset.mem_union, mem_leftSet, Outside, Xor]
    tauto
  have hd : Disjoint (leftSet G i j) (leftSet G j i) := by
    apply Finset.disjoint_left.mpr
    intro w hw hw'
    exact ((mem_leftSet G i j w).mp hw).2.2 ((mem_leftSet G j i w).mp hw').2.1
  rw [hu, Finset.card_union_of_disjoint hd]

theorem degree_outside_formula {n : ℕ} (G : SimpleGraph (Fin n))
    {i j : Fin n} (hij : i ≠ j) (w : Fin n) :
    graphDegree G w = edgeBit G w i + edgeBit G w j +
      ∑ x ∈ Finset.univ.filter (Outside i j), edgeBit G w x := by
  classical
  have hp (x : Fin n) : edgeBit G w x =
      (if x = i then edgeBit G w i else 0) +
      (if x = j then edgeBit G w j else 0) +
      (if Outside i j x then edgeBit G w x else 0) := by
    by_cases hxi : x = i
    · subst x
      simp [Outside, hij]
    by_cases hxj : x = j
    · subst x
      simp [Outside, Ne.symm hij]
    simp [Outside, hxi, hxj]
  rw [graphDegree_eq_sum_edgeBit]
  calc
    (∑ x, edgeBit G w x) =
        ∑ x, ((if x = i then edgeBit G w i else 0) +
          (if x = j then edgeBit G w j else 0) +
          (if Outside i j x then edgeBit G w x else 0)) :=
      Finset.sum_congr rfl (fun x _ => hp x)
    _ = _ := by simp [Finset.sum_filter, Finset.sum_add_distrib]

theorem degree_outside_eq_of_key_eq {n : ℕ} {G H : SimpleGraph (Fin n)}
    {i j w : Fin n} (hij : i ≠ j) (hk : key i j G = key i j H)
    (hw : Outside i j w) : graphDegree G w = graphDegree H w := by
  classical
  have hc := key_count hk w
  have hc' : edgeBit G w i + edgeBit G w j = edgeBit H w i + edgeBit H w j := by
    simpa only [edgeBit_symm G i w, edgeBit_symm G j w,
      edgeBit_symm H i w, edgeBit_symm H j w] using hc
  rw [degree_outside_formula G hij w, degree_outside_formula H hij w, hc']
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  have hxo := (Finset.mem_filter.mp hx).2
  unfold edgeBit
  congr 1
  exact propext (key_outside hk hw hxo)

theorem degrees_eq_of_key_leftSet_card_eq {n : ℕ} {G H : SimpleGraph (Fin n)}
    {i j : Fin n} (hij : i ≠ j) (hk : key i j G = key i j H)
    (hl : (leftSet G i j).card = (leftSet H i j).card) :
    ∀ v, graphDegree G v = graphDegree H v := by
  have hi := (leftSet_card_eq_iff_degree_eq hij hk).mp hl
  have hs := congrArg Finset.card (singletonSet_eq_of_key_eq hk)
  have hr : (leftSet G j i).card = (leftSet H j i).card := by
    rw [singleton_card_split G i j, singleton_card_split H i j, hl] at hs
    omega
  have hks : key j i G = key j i H :=
    (key_swap G i j).symm.trans (hk.trans (key_swap H i j))
  have hj := (leftSet_card_eq_iff_degree_eq (Ne.symm hij) hks).mp hr
  intro v
  by_cases hvi : v = i
  · simpa [hvi] using hi
  by_cases hvj : v = j
  · simpa [hvj] using hj
  exact degree_outside_eq_of_key_eq hij hk ⟨hvi, hvj⟩

end Problem315.PairFiber

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.PairFiberEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem315.PairFiber

variable {V : Type*} [Fintype V]

abbrev Assignment (G : SimpleGraph V) (i j : V) :=
  {T : Finset V // T ⊆ singletonSet G i j ∧ T.card = (leftSet G i j).card}

abbrev GraphFiber (G : SimpleGraph V) (i j : V) :=
  {H : SimpleGraph V // key i j H = key i j G ∧
    (leftSet H i j).card = (leftSet G i j).card}

def graphFiberEquiv (G : SimpleGraph V) (i j : V) (hij : i ≠ j) :
    GraphFiber G i j ≃ Assignment G i j where
  toFun H := ⟨leftSet H.val i j, by
    constructor
    · rw [← singletonSet_eq_of_key_eq H.property.1]
      exact leftSet_subset_singletonSet H.val i j
    · exact H.property.2⟩
  invFun T := ⟨trade G i j hij T.val T.property.1, by
    constructor
    · exact key_trade _ _ _ _ _ _
    · rw [leftSet_trade]
      exact T.property.2⟩
  left_inv H := by
    have hsub : leftSet H.val i j ⊆ singletonSet G i j := by
      rw [← singletonSet_eq_of_key_eq H.property.1]
      exact leftSet_subset_singletonSet _ _ _
    apply Subtype.ext
    change trade G i j hij (leftSet H.val i j) hsub = H.val
    apply graph_eq_of_key_leftSet_eq
    · exact (key_trade G i j hij (leftSet H.val i j) hsub).trans H.property.1.symm
    · exact leftSet_trade G i j hij (leftSet H.val i j) hsub
  right_inv T := by
    apply Subtype.ext
    change leftSet (trade G i j hij T.val T.property.1) i j = T.val
    exact leftSet_trade G i j hij T.val T.property.1

@[simp] theorem graphFiberEquiv_apply (G : SimpleGraph V) (i j : V) (hij : i ≠ j)
    (H : GraphFiber G i j) : (graphFiberEquiv G i j hij H).val = leftSet H.val i j := rfl

@[simp] theorem graphFiberEquiv_symm_apply (G : SimpleGraph V) (i j : V) (hij : i ≠ j)
    (T : Assignment G i j) :
    ((graphFiberEquiv G i j hij).symm T).val = trade G i j hij T.val T.property.1 := rfl

abbrev StateFiber {n : Nat} {d : Fin n → Nat}
    (G : GraphState n d) (i j : Fin n) :=
  {H : GraphState n d // key i j H.val = key i j G.val}

def stateGraphFiberEquiv {n : Nat} {d : Fin n → Nat}
    (G : GraphState n d) (i j : Fin n) (hij : i ≠ j) :
    StateFiber G i j ≃ GraphFiber G.val i j where
  toFun H := ⟨H.val.val, H.property,
    (leftSet_card_eq_iff_degree_eq hij H.property).mpr
      ((H.val.property i).trans (G.property i).symm)⟩
  invFun H := ⟨⟨H.val, fun v =>
      (degrees_eq_of_key_leftSet_card_eq hij H.property.1 H.property.2 v).trans
        (G.property v)⟩, H.property.1⟩
  left_inv H := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv H := by
    apply Subtype.ext
    rfl

def stateFiberEquiv {n : Nat} {d : Fin n → Nat}
    (G : GraphState n d) (i j : Fin n) (hij : i ≠ j) :
    StateFiber G i j ≃ Assignment G.val i j :=
  (stateGraphFiberEquiv G i j hij).trans (graphFiberEquiv G.val i j hij)

@[simp] theorem stateFiberEquiv_apply {n : Nat} {d : Fin n → Nat}
    (G : GraphState n d) (i j : Fin n) (hij : i ≠ j) (H : StateFiber G i j) :
    (stateFiberEquiv G i j hij H).val = leftSet H.val.val i j := rfl

@[simp] theorem stateFiberEquiv_symm_apply {n : Nat} {d : Fin n → Nat}
    (G : GraphState n d) (i j : Fin n) (hij : i ≠ j) (T : Assignment G.val i j) :
    ((stateFiberEquiv G i j hij).symm T).val.val =
      trade G.val i j hij T.val T.property.1 := rfl

end Problem315.PairFiber

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.PairFiberBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.PairFiber
attribute [local instance] Classical.propDecidable

variable {n : Nat}

theorem pair_neighbor_count (G : SimpleGraph (Fin n)) (i j : Fin n) (hij : i ≠ j)
    (w : Fin n) :
    (({i, j} : Finset (Fin n)).filter (G.Adj w)).card =
      edgeBit G i w + edgeBit G j w := by
  classical
  by_cases hi : G.Adj i w <;> by_cases hj : G.Adj j w <;>
    simp [Finset.filter_insert, Finset.filter_singleton, edgeBit, G.adj_comm w i, G.adj_comm w j, hi, hj, hij]

theorem sameFiber_iff_key_eq (i j : Fin n) (hij : i ≠ j)
    (G H : SimpleGraph (Fin n)) :
    PairResampling.SameFiber {i, j} G H ↔ key i j G = key i j H := by
  classical
  constructor
  · intro h
    apply key_eq_of
    · intro u v hu hv
      exact h.1 u (by simpa [Outside] using hu) v (by simpa [Outside] using hv)
    · exact h.2.1 i (by simp) j (by simp)
    · intro w
      by_cases wi : w = i
      · subst w
        have hi := h.2.1 j (by simp) i (by simp)
        simp [edgeBit, hi]
      by_cases wj : w = j
      · subst w
        have hi := h.2.1 i (by simp) j (by simp)
        simp [edgeBit, hi]
      rw [← pair_neighbor_count G i j hij w, ← pair_neighbor_count H i j hij w]
      exact h.2.2 w (by simp [wi, wj])
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro u hu v hv
      exact key_outside h (by simpa [Outside] using hu) (by simpa [Outside] using hv)
    · intro u hu v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
      rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
      · simp
      · exact key_internal h
      · simpa only [G.adj_comm, H.adj_comm] using key_internal h
      · simp
    · intro w hw
      rw [pair_neighbor_count G i j hij w, pair_neighbor_count H i j hij w]
      exact key_count h w

def resamplingFiberEquiv {d : Fin n → Nat}
    (G : GraphState n d) (i j : Fin n) (hij : i ≠ j) :
    (PairResampling.fiberStates {i, j} G) ≃ Assignment G.val i j := by
  classical
  let e : (PairResampling.fiberStates {i, j} G) ≃ StateFiber G i j :=
    { toFun := fun H => ⟨H.val,
        ((sameFiber_iff_key_eq i j hij G.val H.val.val).mp
          ((PairResampling.mem_fiberStates {i, j} G H.val).mp H.property)).symm⟩
      invFun := fun H => ⟨H.val,
        (PairResampling.mem_fiberStates {i, j} G H.val).mpr
          ((sameFiber_iff_key_eq i j hij G.val H.val.val).mpr H.property.symm)⟩
      left_inv := fun H => by apply Subtype.ext; rfl
      right_inv := fun H => by apply Subtype.ext; rfl }
  exact e.trans (stateFiberEquiv G i j hij)

@[simp] theorem resamplingFiberEquiv_symm_val {d : Fin n → Nat}
    (G : GraphState n d) (i j : Fin n) (hij : i ≠ j) (T : Assignment G.val i j) :
    ((resamplingFiberEquiv G i j hij).symm T).val =
      ((stateFiberEquiv G i j hij).symm T).val := rfl

end Problem315.PairFiber

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.PairEqualityProjection
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

def observable (i k l : Fin n) : StateSpace n d :=
  WithLp.toLp 2 (fun G => if G.val.Adj i k ↔ G.val.Adj i l then 1 else 0)

def centered (i j k l : Fin n) : StateSpace n d :=
  fluctuation n d {i,j} (observable i k l)

def active (i j k l : Fin n) (G : GraphState n d) : Prop :=
  k ∈ singletonSet G.val i j ∧ l ∈ singletonSet G.val i j

def equalitySpace (i j k l : Fin n) : Submodule ℝ (StateSpace n d) where
  carrier := {f | ∀ G : GraphState n d, ∃ c : ℝ,
    ∀ H : GraphState n d, SameFiber {i,j} G.val H.val →
      f H = c * (if active i j k l G then centered i j k l H else 0)}
  zero_mem' := by
    intro G
    exact ⟨0, fun H h => by simp⟩
  add_mem' := by
    intro f g hf hg G
    obtain ⟨c,hc⟩ := hf G
    obtain ⟨e,he⟩ := hg G
    refine ⟨c+e, fun H h => ?_⟩
    change f H + g H = _
    rw [hc H h, he H h, add_mul]
  smul_mem' := by
    intro c f hf G
    obtain ⟨e,he⟩ := hf G
    refine ⟨c*e, fun H h => ?_⟩
    change c * f H = _
    rw [he H h, mul_assoc]

def projection (i j k l : Fin n) : StateSpace n d →L[ℝ] StateSpace n d :=
  (equalitySpace i j k l).starProjection

@[simp] theorem projection_eq_self_iff (i j k l : Fin n) (f : StateSpace n d) :
    projection i j k l f = f ↔ f ∈ equalitySpace i j k l :=
  Submodule.starProjection_eq_self_iff

def crossTotal (i j k l : Fin n) (G : GraphState n d) : ℕ :=
  edgeBit G.val i k + edgeBit G.val j k +
    (edgeBit G.val i l + edgeBit G.val j l)

def multiply (f g : StateSpace n d) : StateSpace n d :=
  WithLp.toLp 2 (fun G => f G * g G)

end Problem315.PairEquality

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.DisjointGraphAffine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical

namespace Problem315.DisjointMarginal
open DisjointEncoding
variable {n : Nat} {d : Fin n → Nat}

def crossCellRestriction (e : Fin 4 ↪ Fin n) (G : GraphState n d)
    (f : PairResampling.StateSpace n d) : EuclideanSpace ℝ (CrossCell e G) :=
  WithLp.toLp 2 (fun z => f ((stateCellCrossEquiv e G).symm z).val)

@[simp] theorem crossCellRestriction_apply_equiv
    (e : Fin 4 ↪ Fin n) (G : GraphState n d)
    (f : PairResampling.StateSpace n d) (H : StateCell e G) :
    crossCellRestriction e G f (stateCellCrossEquiv e G H) = f H.val := by
  simp [crossCellRestriction]

end Problem315.DisjointMarginal

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.DisjointProjectionCell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.DisjointEncoding

attribute [local instance] Classical.propDecidable
variable {n : ℕ} {d : Fin n → ℕ}

def stateCellSetoid (e : Fin 4 ↪ Fin n) : Setoid (GraphState n d) where
  r G H := SameCell e G.val H.val
  iseqv := ⟨fun G => SameCell.refl e G.val,
    fun h => h.symm, fun h h' => h.trans h'⟩

abbrev CellIndex (e : Fin 4 ↪ Fin n) (d : Fin n → ℕ) := Quotient (stateCellSetoid (d := d) e)

noncomputable instance instFintypeCellIndex (e : Fin 4 ↪ Fin n) : Fintype (CellIndex e d) := Fintype.ofFinite _

def cellIndex (e : Fin 4 ↪ Fin n) (G : GraphState n d) : CellIndex e d := Quotient.mk _ G

@[simp] theorem cellIndex_eq_iff (e : Fin 4 ↪ Fin n) (G H : GraphState n d) :
    cellIndex e G = cellIndex e H ↔ SameCell e G.val H.val :=
  Quotient.eq

end Problem315.DisjointEncoding

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.FiniteKernelTV
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators RealInnerProductSpace
open WithLp

namespace Problem315.Analytic

variable {α : Type*} [Fintype α]

def zeroSumSpace (α : Type*) [Fintype α] : Submodule ℝ (EuclideanSpace ℝ α) where
  carrier := {f | ∑ i, f i = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change ∑ i, x i = 0 at hx
    change ∑ i, y i = 0 at hy
    change ∑ i, (x + y) i = 0
    simp only [PiLp.add_apply, Finset.sum_add_distrib, hx, hy, add_zero]
  smul_mem' := by
    intro c x hx
    change ∑ i, x i = 0 at hx
    change ∑ i, (c • x) i = 0
    simp only [PiLp.smul_apply, smul_eq_mul, ← Finset.mul_sum, hx, mul_zero]

@[simp] theorem mem_zeroSumSpace (f : EuclideanSpace ℝ α) :
    f ∈ zeroSumSpace α ↔ ∑ i, f i = 0 := Iff.rfl

variable [DecidableEq α]

def centeredPoint (a : α) : EuclideanSpace ℝ α :=
  toLp 2 (fun i => (if i = a then (1 : ℝ) else 0) - 1 / (Fintype.card α : ℝ))

end Problem315.Analytic

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.ForcedColumns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.ForcedColumns

variable {C : Type*}

abbrev MatrixSpace (k : C → ℕ) :=
  {M : Fin 3 → C → Fin 2 // ∀ c, ∑ i, (M i c : ℕ) = k c}

abbrev One (k : C → ℕ) := {c : C // k c = 1}
abbrev Two (k : C → ℕ) := {c : C // k c = 2}

lemma column_zero (v : Fin 3 → Fin 2) (h : ∑ i, (v i : ℕ) = 0) :
    ∀ i, v i = 0 := by
  have ht : ∀ v : Fin 3 → Fin 2, (∑ i, (v i : ℕ)) = 0 → ∀ i, v i = 0 := by decide
  exact ht v h

lemma column_three (v : Fin 3 → Fin 2) (h : ∑ i, (v i : ℕ) = 3) :
    ∀ i, v i = 1 := by
  have ht : ∀ v : Fin 3 → Fin 2, (∑ i, (v i : ℕ)) = 3 → ∀ i, v i = 1 := by decide
  exact ht v h

def restrict (k : C → ℕ) (M : MatrixSpace k) :
    BinaryColumnPartitions.MatrixSpace (One k) (Two k) :=
  ⟨fun i => Sum.elim (fun c => M.val i c.val) (fun c => M.val i c.val),
    ⟨fun c => (M.property c.val).trans c.property,
     fun c => (M.property c.val).trans c.property⟩⟩

def extend (k : C → ℕ) (hk : ∀ c, k c ≤ 3)
    (M : BinaryColumnPartitions.MatrixSpace (One k) (Two k)) : MatrixSpace k := by
  classical
  refine ⟨fun i c => if h1 : k c = 1 then M.val i (Sum.inl ⟨c, h1⟩)
    else if h2 : k c = 2 then M.val i (Sum.inr ⟨c, h2⟩)
    else if k c = 3 then 1 else 0, ?_⟩
  intro c
  by_cases h1 : k c = 1
  · simpa [h1] using M.property.1 ⟨c, h1⟩
  · by_cases h2 : k c = 2
    · simpa [h2] using M.property.2 ⟨c, h2⟩
    · by_cases h3 : k c = 3
      · simp [h3]
      · have h0 : k c = 0 := by have := hk c; omega
        simp [h0]

@[simp] theorem restrict_extend (k : C → ℕ) (hk : ∀ c, k c ≤ 3)
    (M : BinaryColumnPartitions.MatrixSpace (One k) (Two k)) :
    restrict k (extend k hk M) = M := by
  classical
  apply Subtype.ext
  funext i c
  cases c with
  | inl c => simp [restrict, extend, c.property]
  | inr c => simp [restrict, extend, c.property]

@[simp] theorem extend_restrict (k : C → ℕ) (hk : ∀ c, k c ≤ 3)
    (M : MatrixSpace k) : extend k hk (restrict k M) = M := by
  classical
  apply Subtype.ext
  funext i c
  by_cases h1 : k c = 1
  · simp [extend, restrict, h1]
  · by_cases h2 : k c = 2
    · simp [extend, restrict, h2]
    · by_cases h3 : k c = 3
      · have he : M.val i c = 1 := column_three (fun j => M.val j c)
          ((M.property c).trans h3) i
        simp [extend, h3, he]
      · have h0 : k c = 0 := by have := hk c; omega
        have he : M.val i c = 0 := column_zero (fun j => M.val j c)
          ((M.property c).trans h0) i
        simp [extend, h0, he]

def matrixEquiv (k : C → ℕ) (hk : ∀ c, k c ≤ 3) :
    MatrixSpace k ≃ BinaryColumnPartitions.MatrixSpace (One k) (Two k) where
  toFun := restrict k
  invFun := extend k hk
  left_inv := extend_restrict k hk
  right_inv := restrict_extend k hk

attribute [local instance] Classical.propDecidable
variable [Fintype C]

def offset (k : C → ℕ) : ℕ := Fintype.card {c : C // k c = 3}

theorem row_sum (k : C → ℕ) (hk : ∀ c, k c ≤ 3)
    (M : MatrixSpace k) (i : Fin 3) :
    (∑ c, (M.val i c : ℕ)) =
      (∑ c, ((restrict k M).val i c : ℕ)) + offset k := by
  classical
  have hs (a : ℕ) : (∑ c : {c : C // k c = a}, (M.val i c.val : ℕ)) =
      ∑ c : C, if k c = a then (M.val i c : ℕ) else 0 := by
    symm
    simpa only [Finset.sum_filter] using
      (Finset.sum_subtype (Finset.univ.filter (fun c => k c = a))
        (by intro c; simp) (fun c => (M.val i c : ℕ)))
  have hp (c : C) : (M.val i c : ℕ) =
      (if k c = 1 then (M.val i c : ℕ) else 0) +
      (if k c = 2 then (M.val i c : ℕ) else 0) +
      (if k c = 3 then 1 else 0) := by
    have hc : k c = 0 ∨ k c = 1 ∨ k c = 2 ∨ k c = 3 := by
      have := hk c
      omega
    rcases hc with h | h | h | h
    · have he := column_zero _ ((M.property c).trans h) i
      simp [h, he]
    · simp [h]
    · simp [h]
    · have he := column_three _ ((M.property c).trans h) i
      simp [h, he]
  have ht := congrArg (fun f : C → ℕ => ∑ c, f c) (funext hp)
  simp only [Finset.sum_add_distrib] at ht
  rw [Fintype.sum_sum_type]
  change (∑ c, (M.val i c : ℕ)) =
    ((∑ c : One k, (M.val i c.val : ℕ)) +
      ∑ c : Two k, (M.val i c.val : ℕ)) + offset k
  rw [hs 1, hs 2]
  have ho : (∑ c : C, if k c = 3 then 1 else 0) = offset k := by
    simp [offset, Fintype.card_subtype]
  simpa only [ho] using ht

theorem offset_le_row_sum (k : C → ℕ) (hk : ∀ c, k c ≤ 3)
    (M : MatrixSpace k) (i : Fin 3) : offset k ≤ ∑ c, (M.val i c : ℕ) := by
  rw [row_sum k hk M i]
  omega

def fixedMarginsEquiv (k : C → ℕ) (hk : ∀ c, k c ≤ 3)
    (r : Fin 3 → ℕ) (hr : ∀ i, offset k ≤ r i) :
    {M : MatrixSpace k // ∀ i, ∑ c, (M.val i c : ℕ) = r i} ≃
      {M : BinaryColumnPartitions.MatrixSpace (One k) (Two k) //
        ∀ i, ∑ c, (M.val i c : ℕ) = r i - offset k} :=
  (matrixEquiv k hk).subtypeEquiv (fun M => by
    constructor
    · intro h i
      have hh := row_sum k hk M i
      have hi := h i
      change (∑ c, ((restrict k M).val i c : ℕ)) = r i - offset k
      omega
    · intro h i
      have hh := row_sum k hk M i
      have hi := h i
      have hle := hr i
      change (∑ c, ((restrict k M).val i c : ℕ)) = r i - offset k at hi
      omega)

abbrev FullMargins (k : C → ℕ) (r : Fin 3 → ℕ) :=
  {M : Fin 3 → C → Fin 2 //
    (∀ i, ∑ c, (M i c : ℕ) = r i) ∧ ∀ c, ∑ i, (M i c : ℕ) = k c}

def nestEquiv (k : C → ℕ) (r : Fin 3 → ℕ) :
    FullMargins k r ≃ {M : MatrixSpace k // ∀ i, ∑ c, (M.val i c : ℕ) = r i} where
  toFun M := ⟨⟨M.val, M.property.2⟩, M.property.1⟩
  invFun M := ⟨M.val.val, M.property, M.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem bounds_of_nonempty (k : C → ℕ) (r : Fin 3 → ℕ)
    (h : Nonempty (FullMargins k r)) :
    (∀ c, k c ≤ 3) ∧ ∀ i, offset k ≤ r i := by
  obtain ⟨M⟩ := h
  have hk (c : C) : k c ≤ 3 := by
    rw [← M.property.2 c]
    calc
      (∑ i, (M.val i c : ℕ)) ≤ ∑ _i : Fin 3, 1 := by
        apply Finset.sum_le_sum
        intro i hi
        have := (M.val i c).isLt
        omega
      _ = 3 := by simp
  refine ⟨hk, ?_⟩
  intro i
  have hi := offset_le_row_sum k hk ⟨M.val, M.property.2⟩ i
  simpa only [M.property.1 i] using hi

abbrev Colorings (k : C → ℕ) (r : Fin 3 → ℕ) :=
  {c : (One k → Fin 3) × (Two k → Fin 3) // ∀ i,
    (FixedBlock.row c.1 i).card + Fintype.card (Two k) =
      (r i - offset k) + (FixedBlock.row c.2 i).card}

def coloringEquiv (k : C → ℕ) (r : Fin 3 → ℕ)
    (h : Nonempty (FullMargins k r)) : FullMargins k r ≃ Colorings k r :=
  (nestEquiv k r).trans
    ((fixedMarginsEquiv k (bounds_of_nonempty k r h).1 r
      (bounds_of_nonempty k r h).2).trans
      (BinaryColumnPartitions.fixedMarginsEquiv (One k) (Two k)
        (fun i => r i - offset k)).symm)

end Problem315.ForcedColumns

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.FrameSynthesis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

open scoped BigOperators

namespace Problem315.FrameSynthesis

variable {ι E : Type*} [Fintype ι] [sectionDecidableEqι : DecidableEq ι]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local notation "⟪" x ", " y "⟫" => inner ℝ x y

def synthesis (z : ι → E) : EuclideanSpace ℝ ι →ₗ[ℝ] E where
  toFun c := ∑ i, c i • z i
  map_add' c d := by
    simp only [PiLp.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a c := by
    simp only [PiLp.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply]

include sectionDecidableEqι in
@[simp] theorem synthesis_apply (z : ι → E) (c : EuclideanSpace ℝ ι) :
    synthesis z c = ∑ i, c i • z i := by
  have retainedsectionDecidableEqι := sectionDecidableEqι
  exact rfl

@[simp] theorem synthesis_single (z : ι → E) (i : ι) (a : ℝ) :
    synthesis z (EuclideanSpace.single i a) = a • z i := by
  classical
  simp [synthesis, EuclideanSpace.single]

section Adjoint
variable [FiniteDimensional ℝ E]

@[simp] theorem adjoint_synthesis_apply (z : ι → E) (f : E) (i : ι) :
    (synthesis z).adjoint f i = ⟪z i, f⟫ := by
  classical
  have h := (synthesis z).adjoint_inner_right (EuclideanSpace.single i 1) f
  simpa [EuclideanSpace.inner_single_left] using h

end Adjoint


end Problem315.FrameSynthesis

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.FrozenRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem315

def FrozenRowsAgree {n : Nat} (G H : SimpleGraph (Fin n))
    (R : Finset (Fin n)) : Prop :=
  ∀ u, u ∉ R → ∀ v, G.Adj u v ↔ H.Adj u v

end Problem315

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.HavelInduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.HavelCanonical

def AgreeOutside {V : Type*} (R : Finset V) (G H : SimpleGraph V) : Prop :=
  ∀ v, v ∉ R → ∀ w, G.Adj v w ↔ H.Adj v w

end Problem315.HavelCanonical

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.MatrixRowVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace Problem315.MatrixRowVariance

variable {C : Type*} [Fintype C]

def positive (k : C → ℕ) (r : Fin 3 → ℕ) (i : Fin 3) : ℕ :=
  (r i - ForcedColumns.offset k) - Fintype.card (ForcedColumns.Two k)

def negative (k : C → ℕ) (r : Fin 3 → ℕ) (i : Fin 3) : ℕ :=
  Fintype.card (ForcedColumns.Two k) - (r i - ForcedColumns.offset k)

theorem coloring_constraints_iff (k : C → ℕ) (r : Fin 3 → ℕ)
    (c : (ForcedColumns.One k → Fin 3) × (ForcedColumns.Two k → Fin 3)) :
    (∀ i, (FixedBlock.row c.1 i).card + Fintype.card (ForcedColumns.Two k) =
      (r i - ForcedColumns.offset k) + (FixedBlock.row c.2 i).card) ↔
    (∀ i, (FixedBlock.row c.1 i).card + negative k r i =
      (FixedBlock.row c.2 i).card + positive k r i) := by
  constructor <;> intro h i
  · have hi := h i
    unfold positive negative
    omega
  · have hi := h i
    unfold positive negative at hi
    omega

def coloringsBalanceEquiv (k : C → ℕ) (r : Fin 3 → ℕ) :
    ForcedColumns.Colorings k r ≃
      BalancedBlockVariance.Balanced (ForcedColumns.One k) (ForcedColumns.Two k)
        (positive k r) (negative k r) :=
  Equiv.subtypeEquivRight (coloring_constraints_iff k r)

def fullBalanceEquiv (k : C → ℕ) (r : Fin 3 → ℕ)
    (h : Nonempty (ForcedColumns.FullMargins k r)) :
    ForcedColumns.FullMargins k r ≃
      BalancedBlockVariance.Balanced (ForcedColumns.One k) (ForcedColumns.Two k)
        (positive k r) (negative k r) :=
  (ForcedColumns.coloringEquiv k r h).trans (coloringsBalanceEquiv k r)

end Problem315.MatrixRowVariance

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.PairAffineInteraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped RealInnerProductSpace

namespace Problem315.PairEquality
open PairResampling PairFiber
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {d : Fin n → ℕ}

def AffineFlagImage (i j k l : Fin n) (f : StateSpace n d) : Prop :=
  ∃ base weight : StateSpace n d,
    base ∈ fiberSpace n d {i,j} ∧ weight ∈ fiberSpace n d {i,j} ∧
    (∀ G : GraphState n d, crossTotal i j k l G ≠ 2 → weight G = 0) ∧
    f = base + multiply weight (observable i k l)

end Problem315.PairEquality

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.PairFiberOrientation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.PairFiber
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V]

@[simp] theorem singletonSet_swap (G : SimpleGraph V) (i j : V) :
    singletonSet G j i = singletonSet G i j := by
  ext w
  simp only [mem_singletonSet, Outside, Xor]
  tauto

end Problem315.PairFiber

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

@[simp] theorem active_swap_left (i j k l : Fin n) (G : GraphState n d) :
    active j i k l G ↔ active i j k l G := by
  simp only [active, singletonSet_swap]

@[simp] theorem active_swap_right (i j k l : Fin n) (G : GraphState n d) :
    active i j l k G ↔ active i j k l G := by
  exact and_comm

end Problem315.PairEquality

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

def equalIndicator (i j : V) (S : Finset V) : ℝ :=
  if (i ∈ S ↔ j ∈ S) then 1 else 0

@[simp] theorem equalIndicator_sq (i j : V) (S : Finset V) :
    (equalIndicator i j S)^2 = equalIndicator i j S := by
  unfold equalIndicator
  split_ifs <;> norm_num

def equalMean (U : Finset V) (q : ℕ) : ℝ :=
  ((q : ℝ) * ((q : ℝ) - 1) +
    ((U.card : ℝ) - q) * ((U.card : ℝ) - q - 1)) /
    ((U.card : ℝ) * ((U.card : ℝ) - 1))

def centeredEqual (U : Finset V) (q : ℕ) (i j : V) (S : Finset V) : ℝ :=
  equalIndicator i j S - equalMean U q

@[simp] theorem equalIndicator_map_embedding {W : Type*} [DecidableEq W]
    (e : V ↪ W) (i j : V) (S : Finset V) :
    equalIndicator (e i) (e j) (S.map e) = equalIndicator i j S := by
  simp [equalIndicator]

include sectionDecidableEqV in
@[simp] theorem equalMean_map_embedding {W : Type*} [DecidableEq W]
    (e : V ↪ W) (U : Finset V) (q : ℕ) :
    equalMean (U.map e) q = equalMean U q := by
  have retainedsectionDecidableEqV := sectionDecidableEqV
  simp [equalMean]

@[simp] theorem centeredEqual_map_embedding {W : Type*} [DecidableEq W]
    (e : V ↪ W) (U : Finset V) (q : ℕ) (i j : V) (S : Finset V) :
    centeredEqual (U.map e) q (e i) (e j) (S.map e) = centeredEqual U q i j S := by
  simp [centeredEqual]

end Problem315.SliceMoments

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

abbrev AssignmentSpace (G : GraphState n d) (i j : Fin n) :=
  EuclideanSpace ℝ (Assignment G.val i j)

def assignmentRestriction (G : GraphState n d) (i j : Fin n) (hij : i ≠ j) :
    StateSpace n d →ₗ[ℝ] AssignmentSpace G i j where
  toFun f := WithLp.toLp 2 (fun T => f ((stateFiberEquiv G i j hij).symm T).val)
  map_add' _ _ := by ext T; rfl
  map_smul' _ _ := by ext T; rfl

@[simp] theorem assignmentRestriction_apply (G : GraphState n d) (i j : Fin n)
    (hij : i ≠ j) (f : StateSpace n d) (T : Assignment G.val i j) :
    assignmentRestriction G i j hij f T = f ((stateFiberEquiv G i j hij).symm T).val := rfl

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

abbrev Slice (α : Type*) (q : ℕ) := {s : Finset α // s.card = q}

def boundedSliceEquiv (U : Finset α) (q : ℕ) :
    {s : Finset α // s ⊆ U ∧ s.card = q} ≃ Slice U q where
  toFun s := ⟨s.val.subtype (fun x => x ∈ U), by
    rw [Finset.card_subtype, Finset.filter_eq_self.mpr s.property.1]
    exact s.property.2⟩
  invFun s := ⟨s.val.map (Function.Embedding.subtype (fun x => x ∈ U)),
    ⟨fun _ hx => Finset.property_of_mem_map_subtype _ hx, by simpa using s.property⟩⟩
  left_inv s := Subtype.ext (Finset.subtype_map_of_mem s.property.1)
  right_inv s := by
    apply Subtype.ext
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, hxy⟩ := Finset.mem_map.mp (Finset.mem_subtype.mp hx)
      have heq : y = x := Subtype.ext hxy
      simpa [← heq] using hy
    · intro hx
      exact Finset.mem_subtype.mpr (Finset.mem_map.mpr ⟨x, hx, rfl⟩)

def relabel {q : ℕ} (σ : Equiv.Perm α) (s : Slice α q) : Slice α q :=
  ⟨s.val.map σ.toEmbedding, by simpa using s.property⟩

include sectionFintypeα sectionDecidableEqα in
@[simp] theorem relabel_one {q : ℕ} (s : Slice α q) : relabel 1 s = s := by
  have retainedsectionFintypeα := sectionFintypeα
  have retainedsectionDecidableEqα := sectionDecidableEqα
  apply Subtype.ext
  change s.val.map (Function.Embedding.refl α) = s.val
  exact Finset.map_refl

include sectionFintypeα sectionDecidableEqα in
@[simp] theorem relabel_mul {q : ℕ} (σ τ : Equiv.Perm α) (s : Slice α q) :
    relabel (σ * τ) s = relabel σ (relabel τ s) := by
  have retainedsectionFintypeα := sectionFintypeα
  have retainedsectionDecidableEqα := sectionDecidableEqα
  apply Subtype.ext
  simp only [relabel, Finset.map_map]
  rfl

def relabelEquiv {q : ℕ} (σ : Equiv.Perm α) : Equiv.Perm (Slice α q) where
  toFun := relabel σ
  invFun := relabel σ⁻¹
  left_inv s := by rw [← relabel_mul, inv_mul_cancel, relabel_one]
  right_inv s := by rw [← relabel_mul, mul_inv_cancel, relabel_one]

@[simp] theorem relabelEquiv_apply {q : ℕ} (σ : Equiv.Perm α) (s : Slice α q) :
    relabelEquiv σ s = relabel σ s := rfl

@[reducible] def mulAction (q : ℕ) : MulAction (Equiv.Perm α) (Slice α q) where
  smul := relabel
  one_smul := relabel_one
  mul_smul := relabel_mul

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

def assignmentSliceEquiv (G : SimpleGraph V) (i j : V) :
    Assignment G i j ≃ Slice (singletonSet G i j) (leftSet G i j).card :=
  boundedSliceEquiv (singletonSet G i j) (leftSet G i j).card

end Problem315.PairFiber

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.SliceNormalizedFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.SliceNormalized

variable {V : Type*} [Fintype V] [sectionDecidableEqV : DecidableEq V]

abbrev State (V : Type*) [Fintype V] (q : ℕ) :=
  ↥((Finset.univ : Finset V).powersetCard q)

abbrev Space (V : Type*) [Fintype V] (q : ℕ) := EuclideanSpace ℝ (State V q)

def raw (q : ℕ) (i j : V) : Space V q :=
  WithLp.toLp 2 (fun S => if i = j then 0 else
    SliceMoments.centeredEqual Finset.univ q i j S.val)

def denominator (V : Type*) [Fintype V] (q : ℕ) : ℝ :=
  Real.sqrt (2 * (Nat.choose (Fintype.card V) q : ℝ) *
    SliceMoments.equalMean (Finset.univ : Finset V) q *
      (1 - SliceMoments.equalMean (Finset.univ : Finset V) q))

def column (q : ℕ) (i j : V) : Space V q :=
  (denominator V q)⁻¹ • raw q i j

@[simp] theorem raw_diag (q : ℕ) (i : V) : raw q i i = 0 := by
  ext S
  simp [raw]

@[simp] theorem column_diag (q : ℕ) (i : V) : column q i i = 0 := by
  simp [column]

end Problem315.SliceNormalized

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

def cardSliceEquivPowerset {V : Type*} [Fintype V] (q : ℕ) :
    SlicePermutationAction.Slice V q ≃ SliceNormalized.State V q where
  toFun S := ⟨S.val, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, S.property⟩⟩
  invFun S := ⟨S.val, (Finset.mem_powersetCard.mp S.property).2⟩
  left_inv S := by apply Subtype.ext; rfl
  right_inv S := by apply Subtype.ext; rfl

end Problem315.PairFiber

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.PairOrbit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem315.PairOrbit

variable {α : Type*} [sectionFintypeα : Fintype α] [DecidableEq α]

def membershipColor (S T : Finset α) (a : α) : Bool × Bool :=
  (decide (a ∈ S), decide (a ∈ T))

end Problem315.PairOrbit

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

def constantPair (a : ℝ) (i j : V) : ℝ := if i = j then 0 else a

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

abbrev State (α : Type*) [Fintype α] (q : ℕ) :=
  ↥((Finset.univ : Finset α).powersetCard q)

def relabel (q : ℕ) (e : Equiv.Perm α) : Equiv.Perm (State α q) where
  toFun S := ⟨S.val.image e, by
    have hc := (Finset.mem_powersetCard.mp S.property).2
    simp [Finset.mem_powersetCard, Finset.card_image_of_injective _ e.injective, hc]⟩
  invFun S := ⟨S.val.image e.symm, by
    have hc := (Finset.mem_powersetCard.mp S.property).2
    simp [Finset.mem_powersetCard, Finset.card_image_of_injective _ e.symm.injective, hc]⟩
  left_inv S := by apply Subtype.ext; simp [Finset.image_image]
  right_inv S := by apply Subtype.ext; simp [Finset.image_image]

@[simp] theorem relabel_val (q : ℕ) (e : Equiv.Perm α) (S : State α q) :
    (relabel q e S).val = S.val.image e := rfl

def swapState (q : ℕ) (a b : α) : Equiv.Perm (State α q) :=
  relabel q (Equiv.swap a b)

@[simp] theorem swapState_twice (q : ℕ) (a b : α) (S : State α q) :
    swapState q a b (swapState q a b S) = S := by
  apply Subtype.ext
  simp [swapState, Finset.image_image, Function.comp_def]

def moveOperator (q : ℕ) (a b : α) :
    EuclideanSpace ℝ (State α q) →ₗ[ℝ] EuclideanSpace ℝ (State α q) where
  toFun f := WithLp.toLp 2 (fun S => f (swapState q a b S))
  map_add' _ _ := by ext S; rfl
  map_smul' _ _ := by ext S; rfl

@[simp] theorem moveOperator_apply (q : ℕ) (a b : α)
    (f : EuclideanSpace ℝ (State α q)) (S : State α q) :
    moveOperator q a b f S = f (swapState q a b S) := rfl

end Problem315.SliceEuclideanGenerator

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

def pullback {q : ℕ} (e : Ω ≃ State V q) :
    Space V q ≃ₗᵢ[ℝ] EuclideanSpace ℝ Ω :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e.symm

include sectionDecidableEqV in
@[simp] theorem pullback_apply {q : ℕ} (e : Ω ≃ State V q)
    (f : Space V q) (ω : Ω) : pullback e f ω = f (e ω) := by
  have retainedsectionDecidableEqV := sectionDecidableEqV
  exact rfl

end Problem315.SliceNormalized

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

namespace Problem315.CellVarianceGluing

variable {α κ : Type*} [sectionFintypeα : Fintype α] [sectionFintypeκ : Fintype κ]

def restrict (key : α → κ) (k : κ) :
    EuclideanSpace ℝ α →ₗ[ℝ] EuclideanSpace ℝ {x // key x = k} where
  toFun f := WithLp.toLp 2 (fun x => f x.val)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

include sectionFintypeα sectionFintypeκ in
@[simp] theorem restrict_apply (key : α → κ) (k : κ)
    (f : EuclideanSpace ℝ α) (x : {x // key x = k}) :
    restrict key k f x = f x.val := by
  have retainedsectionFintypeα := sectionFintypeα
  have retainedsectionFintypeκ := sectionFintypeκ
  exact rfl

def cellSpace (key : α → κ) : Submodule ℝ (EuclideanSpace ℝ α) where
  carrier := {f | ∀ x y, key x = key y → f x = f y}
  zero_mem' := by intro x y h; rfl
  add_mem' := by
    intro f g hf hg x y h
    change f x + g x = f y + g y
    rw [hf x y h, hg x y h]
  smul_mem' := by
    intro c f hf x y h
    change c * f x = c * f y
    rw [hf x y h]

def center (key : α → κ) : EuclideanSpace ℝ α →L[ℝ] EuclideanSpace ℝ α :=
  (cellSpace key).starProjection

end Problem315.CellVarianceGluing

end

end OAI
end


