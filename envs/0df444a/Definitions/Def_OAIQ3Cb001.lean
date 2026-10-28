-- Prove2me | Definitions.Def_OAIQ3Cb001
-- name    : OAIQ3Cb001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T06:25:01.039643+00:00
-- url     : https://prove2.me/theorems/09683993-a90f-4bf6-a35f-d8a8fc3b8746
-- title:
--   Definitions bundle OAIQ3Cb001 of the split of OpenAI, Bounded-degree coboundary expanders in every dimension
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CoboundaryExpanders.main`, carved from OpenAI's openai/math development (OpenAI, *Bounded-degree coboundary expanders in every dimension*, OpenAI Math Release, September 24, 2026, result family 177, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 331 declarations of OpenAI's Lean: 165 definitions, 11 inductive types or structures, 12 instances and 143 theorems. The definitions and types are `OAI.CoboundaryExpanders.CosetConstruction.subgroupFintype`, `OAI.CoboundaryExpanders.CosetModules.orbitVector`, `OAI.CoboundaryExpanders.EdgeMixing.Active`, `OAI.CoboundaryExpanders.EdgeMixing.Connected`, `OAI.CoboundaryExpanders.EdgeMixing.Embedding`, `OAI.CoboundaryExpanders.EdgeMixing.Embedding.extend`, `OAI.CoboundaryExpanders.EdgeMixing.Rayleigh`, `OAI.CoboundaryExpanders.EdgeMixing.action`, `OAI.CoboundaryExpanders.EdgeMixing.activeEmbedding`, `OAI.CoboundaryExpanders.EdgeMixing.activeGraph`, `OAI.CoboundaryExpanders.EdgeMixing.bipartiteEdge`, `OAI.CoboundaryExpanders.EdgeMixing.chi`, `OAI.CoboundaryExpanders.EdgeMixing.energy`, `OAI.CoboundaryExpanders.EdgeMixing.mass`, `OAI.CoboundaryExpanders.EdgeMixing.pairing`, `OAI.CoboundaryExpanders.EdgeMixing.selected`, `OAI.CoboundaryExpanders.EdgeMixing.volume`, `OAI.CoboundaryExpanders.Elementary.OffCleared`, `OAI.CoboundaryExpanders.FatLadders.Balanced`, `OAI.CoboundaryExpanders.FatLadders.Collision`, `OAI.CoboundaryExpanders.FatLadders.LinkCorrection`, `OAI.CoboundaryExpanders.FatLadders.LocalMixing`, `OAI.CoboundaryExpanders.FatLadders.Minimal`, `OAI.CoboundaryExpanders.FatLadders.NearMinimal`, `OAI.CoboundaryExpanders.FatLadders.NoBad`, `OAI.CoboundaryExpanders.FatLadders.Path`, `OAI.CoboundaryExpanders.FatLadders.WeightedEq`, `OAI.CoboundaryExpanders.FatLadders.atom`, `OAI.CoboundaryExpanders.FatLadders.chamberWeight`, `OAI.CoboundaryExpanders.FatLadders.collisionMass`, `OAI.CoboundaryExpanders.FatLadders.delta`, `OAI.CoboundaryExpanders.FatLadders.deltaHom`, `OAI.CoboundaryExpanders.FatLadders.fatAt`, `OAI.CoboundaryExpanders.FatLadders.fatBudget`, `OAI.CoboundaryExpanders.FatLadders.fatFamily`, `OAI.CoboundaryExpanders.FatLadders.fatThreshold`, `OAI.CoboundaryExpanders.FatLadders.indicator`, `OAI.CoboundaryExpanders.FatLadders.k`, `OAI.CoboundaryExpanders.FatLadders.level`, `OAI.CoboundaryExpanders.FatLadders.linkEdge` and 136 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/Coboundary, in whole or in part: `Coboundary_Chains`, `Coboundary_ChamberCones`, `Coboundary_Chambers`, `Coboundary_Cones`, `Coboundary_Expansion`, `Coboundary_FatLadders`, `Coboundary_Flags`, `Coboundary_Frames`, `Coboundary_Joins`, `Coboundary_LinkSpectrum`, `Coboundary_Links`, `Coboundary_Mixing`, `Coboundary_Polynomial`, `Coboundary_Realization`, `Coboundary_Spectral`, `Coboundary_Windows`, `Congruence_Coinvariants`, `Congruence_Elementary`, `Congruence_HomologyEdge`, `Congruence_OddHomology`, `Congruence_Parabolic`, `Congruence_Patterns`, `Congruence_ProStability`, `Congruence_Resolution`, `Congruence_Transfer`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ3Cb002`.
-- source:
--   OpenAI, Bounded-degree coboundary expanders in every dimension, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 177; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Bounded-degree-coboundary-expanders-in-every-dimension-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Coboundary at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ3_Cob.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib's newer `TensorProduct.inductionOn` (no `zero` case: it is the `tmul` case at
`0 ⊗ₜ 0`); ours has only `TensorProduct.induction_on`, which asks for one. Not named
`TensorProduct.inductionOn`: inside `namespace OAI` that would make `open TensorProduct` open
`OAI.TensorProduct` instead of Mathlib's. -/
@[elab_as_elim]
theorem tensorInductionOn {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {motive : TensorProduct R M N → Prop} (z : TensorProduct R M N)
    (tmul : ∀ x y, motive (TensorProduct.tmul R x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z (by simpa using tmul 0 0) tmul add
/-- Mathlib's newer case names for `FreeGroup.induction_on` (`one`, where ours says `C1`). -/
@[elab_as_elim]
theorem freeGroupInductionOn {α : Type*} {C : FreeGroup α → Prop} (z : FreeGroup α) (one : C 1)
    (of : ∀ x, C (FreeGroup.of x)) (inv_of : ∀ x, C (FreeGroup.of x) → C (FreeGroup.of x)⁻¹)
    (mul : ∀ x y, C x → C y → C (x * y)) : C z :=
  FreeGroup.induction_on z one of inv_of mul
/-- The first projection of a probability measure on a product: found by instance search in d13f23b
(total `Measure.map`), here a measurable map. -/
instance isProbabilityMeasure_map_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.fst) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
instance isProbabilityMeasure_map_snd {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.snd) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
instance isProbabilityMeasure_map_subtype_val {α : Type*} [MeasurableSpace α] {p : α → Prop}
    {μ : MeasureTheory.Measure {a // p a}} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Subtype.val) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable
/-- Mathlib d13f23b's `YoungDiagram.card_transpose`. -/
@[simp]
theorem _root_.YoungDiagram.card_transpose (μ : YoungDiagram) : μ.transpose.card = μ.card := by
  unfold YoungDiagram.card
  apply Finset.card_bij (fun c _ => c.swap)
  · intro c hc
    have : c ∈ μ.transpose := hc
    rw [YoungDiagram.mem_transpose] at this
    exact this
  · intro a _ b _ h
    simpa using h
  · intro b hb
    refine ⟨b.swap, ?_, by simp⟩
    show b.swap ∈ μ.transpose
    rw [YoungDiagram.mem_transpose]
    simpa using hb
/-- For a measurable equivalence `e`, `IsProbabilityMeasure (μ.map e)` is found by instance search
(Mathlib d13f23b finds it for every map `f`: there `Measure.map` of a non-measurable map is a Dirac
mass, here it is `0`, so only the measurable case can be shimmed). -/
instance isProbabilityMeasure_map_measurableEquiv {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]
    (e : α ≃ᵐ β) : MeasureTheory.IsProbabilityMeasure (μ.map e) :=
  MeasureTheory.Measure.isProbabilityMeasure_map e.measurable.aemeasurable
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Coboundary_Chains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Augmented F2 simplicial chains, boundaries, exactness, and relative attachments.
-/

noncomputable section
open scoped BigOperators

namespace CoboundaryExpanders.InfiniteChains

namespace Attachment
variable {V W : Type} [DecidableEq V] [DecidableEq W]

lemma erase_disjSum_inl (A : Finset W) (B : Finset V) (w : W) :
    (A.disjSum B).erase (.inl w) = (A.erase w).disjSum B := by
  ext (x | x) <;> simp [Finset.mem_erase]

lemma erase_disjSum_inr (A : Finset W) (B : Finset V) (v : V) :
    (A.disjSum B).erase (.inr v) = A.disjSum (B.erase v) := by
  ext (x | x) <;> simp [Finset.mem_erase]

end Attachment
end CoboundaryExpanders.InfiniteChains

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Coboundary_Cones
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Quantitative chain cones, face-model transport, relabeling, and exactness under retractions.
-/

section
open scoped BigOperators

namespace CoboundaryExpanders.InfiniteChains.Cone
open Attachment
variable {V W : Type} [DecidableEq V] [DecidableEq W]

def carrierBound : ℕ → ℕ
  | 0 => 1
  | n+1 => 1 + (n+1)*carrierBound n

end CoboundaryExpanders.InfiniteChains.Cone

open scoped BigOperators
open scoped BigOperators Matrix
open scoped Matrix

end

open scoped Polynomial BigOperators

namespace CoboundaryExpanders.InfiniteChains.Cone

section
open Attachment
variable {V W : Type} [DecidableEq V] [DecidableEq W]

lemma image_erase_of_injOn (f : V → W) (s : Finset V)
    (hf : Set.InjOn f (s : Set V)) (v : V) (hv : v ∈ s) :
    (s.erase v).image f = (s.image f).erase (f v) := by
  ext w
  constructor
  · rintro hw
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hw
    refine Finset.mem_erase.mpr ⟨?_,Finset.mem_image.mpr ⟨u,(Finset.mem_erase.mp hu).2,rfl⟩⟩
    intro he
    exact (Finset.mem_erase.mp hu).1 (hf (Finset.mem_erase.mp hu).2 hv he)
  · intro hw
    exact Finset.erase_image_subset_image_erase f s v hw
end

section
variable {V : Type} [DecidableEq V]
def tagBy (F : Finset V) (v : V) : V ⊕ V := if v ∈ F then Sum.inl v else Sum.inr v
end

open Attachment
end CoboundaryExpanders.InfiniteChains.Cone

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Coboundary_Flags
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Complete flags, spherical opposition, unitriangular groups, and the flag-coset model.
-/

noncomputable section
open scoped BigOperators

namespace CoboundaryExpanders.SphericalOpposition
open Module
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

variable {N : ℕ}

namespace CompleteFlag
variable [FiniteDimensional K V]

omit [FiniteDimensional K V] in
lemma disjoint_map_subtype_iff (W : Submodule K V) (A : Submodule K W) (B : Submodule K V) :
    Disjoint (A.map W.subtype) B ↔ Disjoint A (B.comap W.subtype) := by
  rw [Submodule.disjoint_def, Submodule.disjoint_def]
  constructor
  · intro h x hx hy
    apply Subtype.ext
    exact h x.val ⟨x, hx, rfl⟩ hy
  · intro h x hx hy
    obtain ⟨y, hyA, rfl⟩ := hx
    exact congrArg Subtype.val (h y hyA hy)

omit [FiniteDimensional K V] in
lemma map_comap_lower (W A : Submodule K V) (hA : A ≤ W) :
    (A.comap W.subtype).map W.subtype = A := by
  rw [Submodule.map_comap_subtype, inf_eq_right.mpr hA]

omit [FiniteDimensional K V] in
lemma rank_comap_lower (W A : Submodule K V) (hA : A ≤ W) :
    finrank K (A.comap W.subtype) = finrank K A := by
  rw [← Submodule.finrank_map_subtype_eq, map_comap_lower W A hA]

end CompleteFlag

end CoboundaryExpanders.SphericalOpposition

namespace CoboundaryExpanders.SphericalOpposition.CompleteFlag
open Module InfiniteChains InfiniteChains.Attachment InfiniteChains.Cone
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {N : ℕ}

def eliminationBound (R r S : ℕ) : ℕ := (2*R+2)^(r*S)*S

def fillingBound (R r S : ℕ) : ℕ := (1+carrierBound r)*eliminationBound R r S

def fieldBound (R r S : ℕ) : ℕ := 1+r*eliminationBound R r S

end CoboundaryExpanders.SphericalOpposition.CompleteFlag

namespace CoboundaryExpanders.SphericalOpposition.CompleteFlag
open Module Submodule
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {N : ℕ}

def suffixIndex (i : Fin (N+1)) (j : Fin (N-i.val)) : Fin N := ⟨i.val+j.val, by omega⟩

lemma suffixIndex_injective (i : Fin (N+1)) : Function.Injective (suffixIndex i) := by
  intro a b h
  apply Fin.ext
  have hh := congrArg Fin.val h
  dsimp [suffixIndex] at hh
  omega

omit [FiniteDimensional K V] in
lemma basis_equiv_span_range {α : Type} (b b' : Basis (Fin N) K V) (v : α → Fin N) :
    (span K (Set.range (fun a => b (v a)))).map (b.equiv b' (Equiv.refl _)).toLinearMap =
      span K (Set.range (fun a => b' (v a))) := by
  rw [Submodule.map_span, ← Set.range_comp]
  simp only [Function.comp_def, LinearEquiv.coe_coe, Basis.equiv_apply, Equiv.refl_apply]

end CoboundaryExpanders.SphericalOpposition.CompleteFlag

namespace CoboundaryExpanders.SphericalOpposition.CompleteFlag
open Module Submodule
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {N : ℕ}

omit [FiniteDimensional K V] in
lemma suffix_span_image (b : Basis (Fin N) K V) (i : Fin (N+1)) :
    Set.range (fun j : Fin (N-i.val) => b (suffixIndex i j)) =
      b '' {j : Fin N | i.val ≤ j.val} := by
  ext v
  constructor
  · rintro ⟨j,rfl⟩
    exact ⟨suffixIndex i j,by dsimp [suffixIndex]; omega,rfl⟩
  · rintro ⟨j,hj,rfl⟩
    change i.val ≤ j.val at hj
    refine ⟨⟨j.val-i.val,by omega⟩,?_⟩
    dsimp only
    apply congrArg b
    apply Fin.ext
    dsimp [suffixIndex]
    omega

end CoboundaryExpanders.SphericalOpposition.CompleteFlag

namespace CoboundaryExpanders.SphericalOpposition.CompleteFlag
open Module Submodule
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {N : ℕ}

def tailIndex (i : Fin (N+1)) (j : Fin i.val) : Fin N := ⟨N-i.val+j.val,by omega⟩

end CoboundaryExpanders.SphericalOpposition.CompleteFlag

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Congruence_Elementary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Elementary matrices, Euclidean generation, block matrices, and residue-field pivot arguments.
-/

section
open scoped BigOperators
open scoped BigOperators Matrix
open scoped Matrix

open scoped BigOperators
open scoped BigOperators Matrix
open scoped Matrix
open scoped BigOperators InnerProductSpace

namespace CoboundaryExpanders.Elementary
variable {A F : Type*} [CommRing A] [CommRing F] {n : ℕ}

def OffCleared (g : Matrix.SpecialLinearGroup (Fin n) A) (k : ℕ) : Prop :=
  ∀ i j, i ≠ j → j.val * n + i.val < k → g i j = 0

end CoboundaryExpanders.Elementary

end

open scoped BigOperators Matrix
attribute [local instance] Classical.decEq

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Congruence_Patterns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Pattern subgroups, matrix opposition, block decompositions, and suffix equivalences.
-/

noncomputable section
open scoped BigOperators
open scoped BigOperators Matrix
open scoped Matrix

namespace CoboundaryExpanders.MatrixOpposition

section
open Elementary
open scoped Matrix BigOperators
variable {K : Type} [Field K] {a b : ℕ}

def blockMatrix (A : Matrix (Fin a) (Fin a) K) (B : Matrix (Fin b) (Fin b) K) :
    Matrix (Fin (a+b)) (Fin (a+b)) K :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A 0 0 B)

@[simp] lemma blockMatrix_ll (A : Matrix (Fin a) (Fin a) K) (B : Matrix (Fin b) (Fin b) K)
    (i j : Fin a) : blockMatrix A B (i.castAdd b) (j.castAdd b) = A i j := by
  change Matrix.fromBlocks A 0 0 B (finSumFinEquiv.symm (finSumFinEquiv (Sum.inl i)))
    (finSumFinEquiv.symm (finSumFinEquiv (Sum.inl j))) = _
  simp
@[simp] lemma blockMatrix_rr (A : Matrix (Fin a) (Fin a) K) (B : Matrix (Fin b) (Fin b) K)
    (i j : Fin b) : blockMatrix A B (i.natAdd a) (j.natAdd a) = B i j := by
  change Matrix.fromBlocks A 0 0 B (finSumFinEquiv.symm (finSumFinEquiv (Sum.inr i)))
    (finSumFinEquiv.symm (finSumFinEquiv (Sum.inr j))) = _
  simp
@[simp] lemma blockMatrix_lr (A : Matrix (Fin a) (Fin a) K) (B : Matrix (Fin b) (Fin b) K)
    (i : Fin a) (j : Fin b) : blockMatrix A B (i.castAdd b) (j.natAdd a) = 0 := by
  change Matrix.fromBlocks A 0 0 B (finSumFinEquiv.symm (finSumFinEquiv (Sum.inl i)))
    (finSumFinEquiv.symm (finSumFinEquiv (Sum.inr j))) = _
  simp
@[simp] lemma blockMatrix_rl (A : Matrix (Fin a) (Fin a) K) (B : Matrix (Fin b) (Fin b) K)
    (i : Fin b) (j : Fin a) : blockMatrix A B (i.natAdd a) (j.castAdd b) = 0 := by
  change Matrix.fromBlocks A 0 0 B (finSumFinEquiv.symm (finSumFinEquiv (Sum.inr i)))
    (finSumFinEquiv.symm (finSumFinEquiv (Sum.inl j))) = _
  simp

lemma blockMatrix_det (A : Matrix (Fin a) (Fin a) K) (B : Matrix (Fin b) (Fin b) K) :
    (blockMatrix A B).det = A.det * B.det := by
  rw [blockMatrix,Matrix.det_reindex_self,Matrix.det_fromBlocks_zero₂₁]

lemma blockMatrix_mul (A A' : Matrix (Fin a) (Fin a) K) (B B' : Matrix (Fin b) (Fin b) K) :
    blockMatrix (A*A') (B*B') = blockMatrix A B * blockMatrix A' B' := by
  unfold blockMatrix
  change (Matrix.reindexRingEquiv K finSumFinEquiv) _ =
    (Matrix.reindexRingEquiv K finSumFinEquiv) _ * (Matrix.reindexRingEquiv K finSumFinEquiv) _
  rw [← map_mul]
  congr 1
  simp [Matrix.fromBlocks_multiply]

lemma blockMatrix_one : blockMatrix (1 : Matrix (Fin a) (Fin a) K)
    (1 : Matrix (Fin b) (Fin b) K) = 1 := by
  unfold blockMatrix
  rw [Matrix.fromBlocks_one]
  exact (Matrix.reindexRingEquiv K finSumFinEquiv).map_one

end

open Elementary SphericalOpposition SphericalOpposition.CompleteFlag
open scoped Matrix Pointwise
variable {K : Type} [Field K] {a b N : ℕ}

abbrev Cut (N : ℕ) := {c : ℕ // 0 < c ∧ c < N}

end CoboundaryExpanders.MatrixOpposition

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Coboundary_Polynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Polynomial-vector leading terms, degree reduction, and normalized rational lattice representatives.
-/

noncomputable section
open scoped Polynomial BigOperators

namespace CoboundaryExpanders.PolynomialVectors
variable {K : Type} [Field K] {N : ℕ}
abbrev V (K : Type) (N : ℕ) [Field K] := Fin N → K[X]

def Leading (v : V K N) (i : Fin N) (a : ℕ) : Prop :=
  (v i).coeff a ≠ 0 ∧ ∀ j b, N*a+i.val < N*b+j.val → (v j).coeff b = 0

lemma leading_ne_zero {v : V K N} {i : Fin N} {a : ℕ} (h : Leading v i a) : v ≠ 0 := by
  intro hv
  subst v
  simpa using h.1

lemma weight_injective {i j : Fin N} {a b : ℕ}
    (h : N*a+i.val = N*b+j.val) : i = j ∧ a = b := by
  have he : i.val = j.val := by
    have hh := congrArg (fun x => x % N) h
    simpa [Nat.add_mod,Nat.mod_eq_of_lt i.isLt,Nat.mod_eq_of_lt j.isLt] using hh
  refine ⟨Fin.ext he,?_⟩
  have hm : N*a = N*b := by omega
  exact Nat.eq_of_mul_eq_mul_left (Nat.zero_lt_of_lt i.isLt) hm

lemma leading_unique {v : V K N} {i j : Fin N} {a b : ℕ}
    (hi : Leading v i a) (hj : Leading v j b) : i = j ∧ a = b := by
  apply weight_injective
  apply le_antisymm
  · by_contra h
    exact hi.1 (hj.2 i a (by omega))
  · by_contra h
    exact hj.1 (hi.2 j b (by omega))

lemma exists_leading {v : V K N} (hv : v ≠ 0) : ∃ i a, Leading v i a := by
  classical
  let s : Finset ℕ := Finset.univ.biUnion fun i : Fin N =>
    (v i).support.image (fun a => N*a+i.val)
  have hs : s.Nonempty := by
    obtain ⟨i,hi⟩ : ∃ i, v i ≠ 0 := by
      by_contra h
      push Not at h
      exact hv (funext h)
    obtain ⟨a,ha⟩ := Polynomial.support_nonempty.mpr hi
    refine ⟨N*a+i.val,Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,?_⟩⟩
    exact Finset.mem_image.mpr ⟨a,ha,rfl⟩
  have hm := Finset.max'_mem s hs
  obtain ⟨i,_,ha⟩ := Finset.mem_biUnion.mp hm
  obtain ⟨a,ha,he⟩ := Finset.mem_image.mp ha
  refine ⟨i,a,Polynomial.mem_support_iff.mp ha,?_⟩
  intro j b hb
  by_contra hn
  have hb' : N*b+j.val ∈ s := Finset.mem_biUnion.mpr
    ⟨j,Finset.mem_univ _,Finset.mem_image.mpr ⟨b,Polynomial.mem_support_iff.mpr hn,rfl⟩⟩
  have hh := Finset.le_max' s _ hb'
  omega

lemma leading_monomial (i : Fin N) (a : ℕ) :
    Leading (Pi.single i (Polynomial.X^a : K[X])) i a := by
  classical
  constructor
  · simp
  · intro j b h
    by_cases hj : j = i
    · subst j
      have : b ≠ a := by intro hb; subst b; omega
      simp [this]
    · simp [Pi.single_eq_of_ne hj]

lemma leading_smul {v : V K N} {i : Fin N} {a : ℕ} (h : Leading v i a)
    {c : K} (hc : c ≠ 0) : Leading (c • v) i a := by
  constructor
  · simpa using mul_ne_zero hc h.1
  · intro j b hj
    simp [h.2 j b hj]

lemma leading_X_pow {v : V K N} {i : Fin N} {a : ℕ} (h : Leading v i a)
    (m : ℕ) : Leading ((Polynomial.X^m : K[X]) • v) i (a+m) := by
  constructor
  · simpa only [Pi.smul_apply,smul_eq_mul,Polynomial.coeff_X_pow_mul,not_lt.mpr (by omega : m ≤ a+m),
      ite_false,Nat.add_sub_cancel] using h.1
  · intro j b hb
    simp only [Pi.smul_apply,smul_eq_mul,Polynomial.coeff_X_pow_mul']
    split_ifs with hbm
    · apply h.2
      have he : N*b = N*(b-m)+N*m := by rw [← Nat.mul_add,Nat.sub_add_cancel hbm]
      simp only [Nat.mul_add] at hb
      omega
    · rfl

lemma leading_cancel {v w : V K N} {i : Fin N} {a : ℕ}
    (hv : Leading v i a) (hw : Leading w i a) :
    v - ((v i).coeff a / (w i).coeff a) • w = 0 ∨
    ∃ j b, Leading (v - ((v i).coeff a / (w i).coeff a) • w) j b ∧
      N*b+j.val < N*a+i.val := by
  classical
  let z := v - ((v i).coeff a / (w i).coeff a) • w
  by_cases hz : z = 0
  · exact Or.inl hz
  · right
    obtain ⟨j,b,hb⟩ := exists_leading hz
    refine ⟨j,b,hb,?_⟩
    by_contra hle
    have hzai : (z i).coeff a = 0 := by
      dsimp [z]
      simp [hw.1]
    rcases lt_or_eq_of_le (by omega : N*a+i.val ≤ N*b+j.val) with hlt | he
    · apply hb.1
      dsimp [z]
      simp [hv.2 j b hlt,hw.2 j b hlt]
    · obtain ⟨rfl,rfl⟩ := weight_injective he
      exact hb.1 hzai

end CoboundaryExpanders.PolynomialVectors

namespace CoboundaryExpanders.PolynomialVectors
attribute [local instance] Classical.propDecidable
open scoped Polynomial BigOperators
variable {K : Type} [Field K] {N : ℕ}

def HasPivots (A : Submodule K[X] (V K N)) : Prop :=
  ∀ i : Fin N, ∃ a v, v ∈ A ∧ Leading v i a

lemma hasPivots_of_bound (A : Submodule K[X] (V K N)) (m : ℕ)
    (hm : ∀ i : Fin N, Pi.single i (Polynomial.X^m : K[X]) ∈ A) : HasPivots A := by
  intro i
  exact ⟨m,_,hm i,leading_monomial i m⟩

noncomputable def pivotDegree (A : Submodule K[X] (V K N)) (hA : HasPivots A) (i : Fin N) : ℕ :=
  Nat.find (hA i)

lemma pivotDegree_min (A : Submodule K[X] (V K N)) (hA : HasPivots A)
    (i : Fin N) {v : V K N} (hv : v ∈ A) {a : ℕ} (ha : Leading v i a) :
    pivotDegree A hA i ≤ a := Nat.find_min' (hA i) ⟨v,hv,ha⟩

noncomputable def pivotRaw (A : Submodule K[X] (V K N)) (hA : HasPivots A) (i : Fin N) : V K N :=
  Classical.choose (Nat.find_spec (hA i))

lemma pivotRaw_mem (A : Submodule K[X] (V K N)) (hA : HasPivots A) (i : Fin N) :
    pivotRaw A hA i ∈ A := (Classical.choose_spec (Nat.find_spec (hA i))).1
lemma pivotRaw_leading (A : Submodule K[X] (V K N)) (hA : HasPivots A) (i : Fin N) :
    Leading (pivotRaw A hA i) i (pivotDegree A hA i) :=
  (Classical.choose_spec (Nat.find_spec (hA i))).2

noncomputable def pivot (A : Submodule K[X] (V K N)) (hA : HasPivots A) (i : Fin N) : V K N :=
  (((pivotRaw A hA i) i).coeff (pivotDegree A hA i))⁻¹ • pivotRaw A hA i

lemma pivot_mem (A : Submodule K[X] (V K N)) (hA : HasPivots A) (i : Fin N) : pivot A hA i ∈ A :=
  (A.restrictScalars K).smul_mem _ (pivotRaw_mem A hA i)

lemma pivot_leading (A : Submodule K[X] (V K N)) (hA : HasPivots A) (i : Fin N) :
    Leading (pivot A hA i) i (pivotDegree A hA i) :=
  leading_smul (pivotRaw_leading A hA i) (inv_ne_zero (pivotRaw_leading A hA i).1)

lemma span_pivots (A : Submodule K[X] (V K N)) (hA : HasPivots A) :
    Submodule.span K[X] (Set.range (pivot A hA)) = A := by
  classical
  let B := Submodule.span K[X] (Set.range (pivot A hA))
  have hBA : B ≤ A := Submodule.span_le.mpr (by rintro _ ⟨i,rfl⟩; exact pivot_mem A hA i)
  refine le_antisymm hBA ?_
  have step : ∀ k, ∀ (v : V K N) (i : Fin N) (a : ℕ), v ∈ A →
      Leading v i a → N*a+i.val = k → v ∈ B := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro v i a hv hlead he
      have hai := pivotDegree_min A hA i hv hlead
      let w := (Polynomial.X^(a-pivotDegree A hA i) : K[X]) • pivot A hA i
      have hw : Leading w i a := by
        have hh := leading_X_pow (pivot_leading A hA i) (a-pivotDegree A hA i)
        simpa only [Nat.add_sub_of_le hai] using hh
      have hwB : w ∈ B := B.smul_mem _ (Submodule.subset_span ⟨i,rfl⟩)
      let c := (v i).coeff a / (w i).coeff a
      have hcB : c • w ∈ B := (B.restrictScalars K).smul_mem c hwB
      have hcA : c • w ∈ A := hBA hcB
      have hzA : v-c • w ∈ A := A.sub_mem hv hcA
      rcases leading_cancel hlead hw with hz | ⟨j,b,hz,hlt⟩
      · have hh : v = c • w := sub_eq_zero.mp hz
        exact hh ▸ hcB
      · have hzB := ih (N*b+j.val) (by omega) (v-c • w) j b hzA hz rfl
        have hh : v = (v-c • w)+c • w := (sub_add_cancel _ _).symm
        exact hh ▸ B.add_mem hzB hcB
  intro v hv
  by_cases hz : v = 0
  · exact hz ▸ B.zero_mem
  · obtain ⟨i,a,hlead⟩ := exists_leading hz
    exact step (N*a+i.val) v i a hv hlead rfl

end CoboundaryExpanders.PolynomialVectors

namespace CoboundaryExpanders.PolynomialVectors
open scoped Polynomial BigOperators
variable {K : Type} [Field K] {N : ℕ}

lemma leading_natDegree_le {v : V K N} {i : Fin N} {a : ℕ}
    (h : Leading v i a) (j : Fin N) : (v j).natDegree ≤ a := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro b hb
  apply h.2
  have hh := Nat.mul_le_mul_left N (show a+1 ≤ b by omega)
  simp only [Nat.mul_add,Nat.mul_one] at hh
  have hi := i.isLt
  omega

lemma leading_mul {v : V K N} {i : Fin N} {a : ℕ}
    (h : Leading v i a) (f : K[X]) (hf : f ≠ 0) :
    Leading (f • v) i (a+f.natDegree) := by
  constructor
  · change (f * v i).coeff (a+f.natDegree) ≠ 0
    rw [Nat.add_comm a,Polynomial.coeff_mul_add_eq_of_natDegree_le le_rfl (leading_natDegree_le h i)]
    exact mul_ne_zero (by simpa using Polynomial.leadingCoeff_ne_zero.mpr hf) h.1
  · intro j b hb
    change (f * v j).coeff b = 0
    rw [Polynomial.coeff_mul]
    apply Finset.sum_eq_zero
    rintro ⟨c,d⟩ hcd
    have he := Finset.HasAntidiagonal.mem_antidiagonal.mp hcd
    by_cases hc : f.natDegree < c
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hc,zero_mul]
    · have hcm := Nat.mul_le_mul_left N (show c ≤ f.natDegree by omega)
      have hbm : N*b = N*c+N*d := by rw [← Nat.mul_add,he]
      have hh : N*a+i.val < N*d+j.val := by
        simp only [Nat.mul_add] at hb
        omega
      rw [h.2 j d hh,mul_zero]

end CoboundaryExpanders.PolynomialVectors

namespace CoboundaryExpanders.PolynomialVectors
open scoped Polynomial BigOperators
variable {K : Type} [Field K] {N : ℕ}

noncomputable def columnReflect (B : Matrix (Fin N) (Fin N) K[X]) (a : Fin N → ℕ) :
    Matrix (Fin N) (Fin N) K[X] := fun i j => Polynomial.reflect (a j) (B i j)

end CoboundaryExpanders.PolynomialVectors

namespace CoboundaryExpanders.PolynomialVectors
open scoped Polynomial BigOperators
variable {K : Type} [Field K] {N : ℕ}

lemma span_of_minimal (A : Submodule K[X] (V K N))
    (b : Fin N → V K N) (degree : Fin N → ℕ)
    (hb : ∀ i, b i ∈ A) (hbLead : ∀ i, Leading (b i) i (degree i))
    (hmin : ∀ {v : V K N} {i : Fin N} {r : ℕ}, v ∈ A → Leading v i r → degree i ≤ r) :
    Submodule.span K[X] (Set.range (b)) = A := by
  classical
  let B := Submodule.span K[X] (Set.range (b))
  have hBA : B ≤ A := Submodule.span_le.mpr (by rintro _ ⟨i,rfl⟩; exact hb i)
  refine le_antisymm hBA ?_
  have step : ∀ k, ∀ (v : V K N) (i : Fin N) (a : ℕ), v ∈ A →
      Leading v i a → N*a+i.val = k → v ∈ B := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro v i a hv hlead he
      have hai := hmin hv hlead
      let w := (Polynomial.X^(a-degree i) : K[X]) • b i
      have hw : Leading w i a := by
        have hh := leading_X_pow (hbLead i) (a-degree i)
        simpa only [Nat.add_sub_of_le hai] using hh
      have hwB : w ∈ B := B.smul_mem _ (Submodule.subset_span ⟨i,rfl⟩)
      let c := (v i).coeff a / (w i).coeff a
      have hcB : c • w ∈ B := (B.restrictScalars K).smul_mem c hwB
      have hcA : c • w ∈ A := hBA hcB
      have hzA : v-c • w ∈ A := A.sub_mem hv hcA
      rcases leading_cancel hlead hw with hz | ⟨j,b,hz,hlt⟩
      · have hh : v = c • w := sub_eq_zero.mp hz
        exact hh ▸ hcB
      · have hzB := ih (N*b+j.val) (by omega) (v-c • w) j b hzA hz rfl
        have hh : v = (v-c • w)+c • w := (sub_add_cancel _ _).symm
        exact hh ▸ B.add_mem hzB hcB
  intro v hv
  by_cases hz : v = 0
  · exact hz ▸ B.zero_mem
  · obtain ⟨i,a,hlead⟩ := exists_leading hz
    exact step (N*a+i.val) v i a hv hlead rfl

end CoboundaryExpanders.PolynomialVectors

namespace CoboundaryExpanders.PolynomialVectors
open scoped Polynomial BigOperators
variable {K : Type} [Field K] {N : ℕ}

lemma pivotDegree_antitone {A B : Submodule K[X] (V K N)} (hA : HasPivots A) (hB : HasPivots B)
    (hBA : B ≤ A) (i : Fin N) : pivotDegree A hA i ≤ pivotDegree B hB i :=
  pivotDegree_min A hA i (hBA (pivot_mem B hB i)) (pivot_leading B hB i)

lemma eq_of_le_same_pivots {A B : Submodule K[X] (V K N)} (hA : HasPivots A) (hB : HasPivots B)
    (hBA : B ≤ A) (hdeg : ∀ i, pivotDegree A hA i = pivotDegree B hB i) : A = B := by
  have hAspan := span_of_minimal A (pivot B hB) (pivotDegree B hB)
    (fun i => hBA (pivot_mem B hB i)) (pivot_leading B hB)
    (fun hv hl => by rw [← hdeg]; exact pivotDegree_min A hA _ hv hl)
  exact hAspan.symm.trans (span_pivots B hB)

noncomputable def powerLinear (m : ℕ) : V K N →ₗ[K[X]] V K N where
  toFun v := (Polynomial.X^m : K[X]) • v
  map_add' v w := smul_add _ _ _
  map_smul' c v := by simp [smul_smul,mul_comm]

noncomputable def powerShift (A : Submodule K[X] (V K N)) (m : ℕ) : Submodule K[X] (V K N) :=
  A.map (powerLinear m)

lemma powerShift_hasPivots (A : Submodule K[X] (V K N)) (hA : HasPivots A) (m : ℕ) :
    HasPivots (powerShift A m) := by
  intro i
  refine ⟨pivotDegree A hA i+m,(Polynomial.X^m : K[X]) • pivot A hA i,?_,?_⟩
  · exact ⟨pivot A hA i,pivot_mem A hA i,rfl⟩
  · exact leading_X_pow (pivot_leading A hA i) m

lemma pivotDegree_powerShift (A : Submodule K[X] (V K N)) (hA : HasPivots A) (m : ℕ) (i : Fin N) :
    pivotDegree (powerShift A m) (powerShift_hasPivots A hA m) i = pivotDegree A hA i+m := by
  let hS := powerShift_hasPivots A hA m
  apply le_antisymm
  · exact pivotDegree_min _ hS i ⟨pivot A hA i,pivot_mem A hA i,rfl⟩
      (leading_X_pow (pivot_leading A hA i) m)
  · obtain ⟨v,hv,he⟩ := pivot_mem (powerShift A m) hS i
    have hv0 : v ≠ 0 := by
      intro hz
      have hh := leading_ne_zero (pivot_leading (powerShift A m) hS i)
      apply hh
      rw [← he,hz,map_zero]
    obtain ⟨j,b,hb⟩ := exists_leading hv0
    have hl : Leading ((Polynomial.X^m : K[X]) • v) i (pivotDegree (powerShift A m) hS i) := by
      change Leading (powerLinear m v) i _
      rw [he]
      exact pivot_leading _ hS i
    obtain ⟨hji,hd⟩ := leading_unique (leading_X_pow hb m) hl
    subst j
    have hmin := pivotDegree_min A hA i hv hb
    change pivotDegree A hA i + m ≤ pivotDegree (powerShift A m) hS i
    omega

lemma interval_pivot_increment {A B : Submodule K[X] (V K N)} (hA : HasPivots A) (hB : HasPivots B)
    (hBA : B ≤ A) (hAB : powerShift A 1 ≤ B) (i : Fin N) :
    pivotDegree B hB i = pivotDegree A hA i ∨ pivotDegree B hB i = pivotDegree A hA i+1 := by
  have hlo := pivotDegree_antitone hA hB hBA i
  have hhi := pivotDegree_antitone hB (powerShift_hasPivots A hA 1) hAB i
  rw [pivotDegree_powerShift A hA 1 i] at hhi
  omega

noncomputable def incrementSet (A B : Submodule K[X] (V K N)) (hA : HasPivots A) (hB : HasPivots B) : Finset (Fin N) :=
  Finset.univ.filter (fun i => pivotDegree A hA i < pivotDegree B hB i)

lemma incrementSet_mono {A B C : Submodule K[X] (V K N)}
    (hA : HasPivots A) (hB : HasPivots B) (hC : HasPivots C) (hCB : C ≤ B) :
    incrementSet A B hA hB ⊆ incrementSet A C hA hC := by
  classical
  intro i hi
  simp only [incrementSet,Finset.mem_filter,Finset.mem_univ,true_and] at hi ⊢
  exact lt_of_lt_of_le hi (pivotDegree_antitone hB hC hCB i)

lemma interval_incrementSet_eq_iff {A B C : Submodule K[X] (V K N)}
    (hA : HasPivots A) (hB : HasPivots B) (hC : HasPivots C)
    (hBA : B ≤ A) (hCB : C ≤ B) (hAC : powerShift A 1 ≤ C) :
    incrementSet A B hA hB = incrementSet A C hA hC ↔ B = C := by
  classical
  constructor
  · intro he
    apply eq_of_le_same_pivots hB hC hCB
    intro i
    have hb := interval_pivot_increment hA hB hBA (hAC.trans hCB) i
    have hc := interval_pivot_increment hA hC (hCB.trans hBA) hAC i
    have hh := Finset.ext_iff.mp he i
    simp only [incrementSet,Finset.mem_filter,Finset.mem_univ,true_and] at hh
    omega
  · rintro rfl
    rfl

end CoboundaryExpanders.PolynomialVectors

namespace CoboundaryExpanders.PolynomialVectors
open scoped Polynomial BigOperators
variable {K : Type} [Field K] {N : ℕ}

lemma full_chain_permutation (S : Fin (N+1) → Finset (Fin N)) (hS : StrictMono S) :
    ∃ σ : Equiv.Perm (Fin N), ∀ r : Fin N,
      S r.succ = insert (σ r) (S r.castSucc) ∧ σ r ∉ S r.castSucc := by
  classical
  have hcard (r : Fin (N+1)) : (S r).card = r.val := by
    let f (r : Fin (N+1)) : Fin (N+1) := ⟨(S r).card,
      Nat.lt_succ_of_le (by simpa using Finset.card_le_card (Finset.subset_univ (S r)))⟩
    have hf : StrictMono f := by
      intro r s hrs
      exact Finset.card_lt_card (hS hrs)
    have he := congr_fun hf.eq_id r
    exact congrArg Fin.val he
  have hex (r : Fin N) : ∃ i : Fin N, S r.succ = insert i (S r.castSucc) ∧ i ∉ S r.castSucc := by
    have hsub := hS.monotone (show r.castSucc ≤ r.succ from Nat.le_succ r.val)
    have hd : (S r.succ \ S r.castSucc).card = 1 := by
      rw [Finset.card_sdiff_of_subset hsub,hcard,hcard]
      simp
    obtain ⟨i,hi⟩ := Finset.card_eq_one.mp hd
    refine ⟨i,?_,?_⟩
    · ext j
      have hh := Finset.ext_iff.mp hi j
      simp only [Finset.mem_sdiff,Finset.mem_singleton] at hh
      simp only [Finset.mem_insert]
      constructor
      · intro hj
        by_cases hj0 : j ∈ S r.castSucc
        · exact Or.inr hj0
        · exact Or.inl (hh.mp ⟨hj,hj0⟩)
      · rintro (rfl|hj)
        · exact (hh.mpr rfl).1
        · exact hsub hj
    · have hh : i ∈ S r.succ \ S r.castSucc := by rw [hi]; simp
      exact (Finset.mem_sdiff.mp hh).2
  choose σ hσ using hex
  have hinj : Function.Injective σ := by
    suffices hh : ∀ i j : Fin N, i < j → σ i ≠ σ j by
      intro i j he
      rcases lt_trichotomy i j with h | h | h
      · exact False.elim (hh i j h he)
      · exact h
      · exact False.elim (hh j i h he.symm)
    intro i j hij he
    have hle : i.succ ≤ j.castSucc := by
      change i.val+1 ≤ j.val
      exact hij
    have hmem : σ i ∈ S i.succ := by rw [(hσ i).1]; simp
    have hh := hS.monotone hle hmem
    rw [he] at hh
    exact (hσ j).2 hh
  let e : Equiv.Perm (Fin N) := Equiv.ofBijective σ
    ⟨hinj,Finite.surjective_of_injective hinj⟩
  exact ⟨e,hσ⟩

theorem full_flag_increment_permutation
    (A : Submodule K[X] (V K N)) (hA : HasPivots A)
    (B : Fin (N+1) → Submodule K[X] (V K N))
    (hB : ∀ r, HasPivots (B r)) (hanti : StrictAnti B)
    (hzero : B 0 = A) (hbelow : ∀ r, powerShift A 1 ≤ B r) :
    ∃ σ : Equiv.Perm (Fin N), ∀ r : Fin N,
      incrementSet A (B r.succ) hA (hB r.succ) =
        insert (σ r) (incrementSet A (B r.castSucc) hA (hB r.castSucc)) ∧
      σ r ∉ incrementSet A (B r.castSucc) hA (hB r.castSucc) := by
  apply full_chain_permutation (fun r => incrementSet A (B r) hA (hB r))
  intro r s hrs
  have hBA : B r ≤ A := by rw [← hzero]; exact hanti.antitone (Fin.zero_le _)
  have hSB := hanti hrs
  have hsub := incrementSet_mono hA (hB r) (hB s) hSB.le
  apply lt_of_le_of_ne hsub
  intro he
  have hsame := (interval_incrementSet_eq_iff hA (hB r) (hB s) hBA hSB.le (hbelow s)).mp he
  exact hSB.ne hsame.symm

end CoboundaryExpanders.PolynomialVectors

namespace CoboundaryExpanders.PolynomialVectors
open scoped Polynomial BigOperators
variable {K : Type} [Field K] {N : ℕ}

lemma leading_weight_bound {v : V K N} {i : Fin N} {a : ℕ}
    (h : Leading v i a) (j : Fin N) (hj : v j ≠ 0) :
    N*(v j).natDegree+j.val ≤ N*a+i.val := by
  by_contra hn
  have hc := h.2 j (v j).natDegree (by omega)
  exact (Polynomial.leadingCoeff_ne_zero.mpr hj) hc

lemma leading_pivot_natDegree {v : V K N} {i : Fin N} {a : ℕ}
    (h : Leading v i a) : (v i).natDegree = a :=
  le_antisymm (leading_natDegree_le h i) (Polynomial.le_natDegree_of_ne_zero h.1)

lemma leading_mulVec (C : Matrix (Fin N) (Fin N) K[X]) (M : ℕ)
    (hC : ∀ j, Leading (fun i => C i j) j M)
    {v : V K N} {i : Fin N} {a : ℕ} (hv : Leading v i a) :
    Leading (C.mulVec v) i (a+M) := by
  classical
  have he : C.mulVec v = ∑ j, v j • (fun k => C k j) := by
    funext k
    simp only [Matrix.mulVec,dotProduct,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  rw [he]
  have hv0 : v i ≠ 0 := by intro hz; simpa [hz] using hv.1
  have hi : Leading (v i • fun k => C k i) i (a+M) := by
    simpa [leading_pivot_natDegree hv,Nat.add_comm] using leading_mul (hC i) (v i) hv0
  constructor
  · have hh : ((∑ j, v j • (fun k => C k j)) i).coeff (a+M) =
        ((v i • fun k => C k i) i).coeff (a+M) := by
      simp only [Finset.sum_apply,Polynomial.finsetSum_coeff]
      apply Finset.sum_eq_single i
      · intro j _ hji
        by_cases hj0 : v j = 0
        · simp [hj0]
        · apply (leading_mul (hC j) (v j) hj0).2
          have hj := leading_weight_bound hv j hj0
          have hne : N*(v j).natDegree+j.val ≠ N*a+i.val := by
            intro heq
            exact hji (weight_injective heq).1
          simp only [Nat.mul_add]
          omega
      · simp
    rw [hh]
    exact hi.1
  · intro k e he
    simp only [Finset.sum_apply,Polynomial.finsetSum_coeff]
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj0 : v j = 0
    · simp [hj0]
    · apply (leading_mul (hC j) (v j) hj0).2
      have hj := leading_weight_bound hv j hj0
      simp only [Nat.mul_add] at he ⊢
      omega

noncomputable def matrixLinear (C : Matrix (Fin N) (Fin N) K[X]) : V K N →ₗ[K[X]] V K N :=
  Matrix.toLin' C

lemma image_hasPivots (C : Matrix (Fin N) (Fin N) K[X]) (M : ℕ)
    (hC : ∀ j, Leading (fun i => C i j) j M)
    (A : Submodule K[X] (V K N)) (hA : HasPivots A) :
    HasPivots (A.map (matrixLinear C)) := by
  intro i
  refine ⟨pivotDegree A hA i+M,C.mulVec (pivot A hA i),?_,?_⟩
  · exact ⟨pivot A hA i,pivot_mem A hA i,rfl⟩
  · exact leading_mulVec C M hC (pivot_leading _ _ _)

end CoboundaryExpanders.PolynomialVectors

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Coboundary_Windows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Affine windows, residue chambers, lattice flags, and chamber parametrizations.
-/

noncomputable section
open scoped Polynomial BigOperators

namespace CoboundaryExpanders.PolynomialVectors
open scoped Polynomial BigOperators
variable {K : Type} [Field K] {N : ℕ}

structure ResidueChamber where
  top : Submodule K[X] (V K N)
  hasTop : HasPivots top
  stage : Fin (N+1) → Submodule K[X] (V K N)
  hasStage : ∀ r, HasPivots (stage r)
  strict : StrictAnti stage
  initial : stage 0 = top
  lower : ∀ r, powerShift top 1 ≤ stage r

namespace ResidueChamber
variable (C : ResidueChamber (K := K) (N := N))

noncomputable def word : Equiv.Perm (Fin N) :=
  (full_flag_increment_permutation C.top C.hasTop C.stage C.hasStage C.strict C.initial C.lower).choose

lemma word_spec (r : Fin N) :
    incrementSet C.top (C.stage r.succ) C.hasTop (C.hasStage r.succ) =
      insert (C.word r) (incrementSet C.top (C.stage r.castSucc) C.hasTop (C.hasStage r.castSucc)) ∧
    C.word r ∉ incrementSet C.top (C.stage r.castSucc) C.hasTop (C.hasStage r.castSucc) :=
  (full_flag_increment_permutation C.top C.hasTop C.stage C.hasStage C.strict C.initial C.lower).choose_spec r

lemma increments (r : Fin (N+1)) :
    incrementSet C.top (C.stage r) C.hasTop (C.hasStage r) =
      Finset.univ.filter (fun i => (C.word.symm i).val < r.val) := by
  classical
  induction r using Fin.induction with
  | zero =>
    rw [show incrementSet C.top (C.stage 0) C.hasTop (C.hasStage 0) = ∅ from by
      ext i
      simp only [incrementSet,Finset.mem_filter,Finset.mem_univ,true_and,Finset.notMem_empty,iff_false,not_lt]
      simpa only [C.initial] using (le_refl (pivotDegree C.top C.hasTop i))]
    simp
  | succ r ih =>
    rw [(C.word_spec r).1,ih]
    ext i
    simp only [Finset.mem_insert,Finset.mem_filter,Finset.mem_univ,true_and,Fin.val_succ,Fin.val_castSucc]
    constructor
    · rintro (rfl|hi)
      · simp
      · omega
    · intro hi
      by_cases he : C.word.symm i = r
      · exact Or.inl (by rw [← he]; exact (C.word.apply_symm_apply i).symm)
      · have hn : (C.word.symm i).val ≠ r.val := fun h => he (Fin.ext h)
        exact Or.inr (by omega)

lemma stage_degree (r : Fin (N+1)) (i : Fin N) :
    pivotDegree (C.stage r) (C.hasStage r) i = pivotDegree C.top C.hasTop i +
      (if (C.word.symm i).val < r.val then 1 else 0) := by
  classical
  have ht : C.stage r ≤ C.top := by rw [← C.initial]; exact C.strict.antitone (Fin.zero_le r)
  have hh := interval_pivot_increment C.hasTop (C.hasStage r) ht (C.lower r) i
  have hm := Finset.ext_iff.mp (C.increments r) i
  simp only [incrementSet,Finset.mem_filter,Finset.mem_univ,true_and] at hm
  split_ifs with h
  · have hg := hm.mpr h
    omega
  · have hg : ¬pivotDegree C.top C.hasTop i < pivotDegree (C.stage r) (C.hasStage r) i := mt hm.mp h
    omega

noncomputable def window : Fin N → ℤ := fun r =>
  (N*pivotDegree C.top C.hasTop (C.word r)+(C.word r).val : ℕ)

end ResidueChamber
end CoboundaryExpanders.PolynomialVectors

namespace CoboundaryExpanders.RationalLattices
open scoped Polynomial BigOperators
open PolynomialVectors
variable (K : Type) [Field K] (N : ℕ)

noncomputable def reflectedMatrix (g : Matrix (Fin N) (Fin N) K[X]) (M : ℕ) :
    Matrix (Fin N) (Fin N) K[X] := fun i j => Polynomial.reflect M (g i j)

end CoboundaryExpanders.RationalLattices

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Coboundary_Chambers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Bounded and full chambers, codistance, descent cores, and their affine-window descriptions.
-/

noncomputable section
open scoped Polynomial BigOperators

namespace CoboundaryExpanders.PolynomialVectors
open scoped Polynomial BigOperators
variable {K : Type} [Field K] {N : ℕ}
lemma powerLinear_injective (m : ℕ) : Function.Injective (powerLinear (K := K) (N := N) m) := by
  intro v w h
  funext i
  have hi := congrFun h i
  change (Polynomial.X^m : K[X]) * v i = (Polynomial.X^m : K[X]) * w i at hi
  exact mul_left_cancel₀ (pow_ne_zero _ Polynomial.X_ne_zero) hi
lemma powerShift_strictMono (m : ℕ) : StrictMono (fun A : Submodule K[X] (V K N) => powerShift A m) :=
  Submodule.map_strictMono_of_injective (powerLinear_injective m)
lemma powerShift_mono (m : ℕ) : Monotone (fun A : Submodule K[X] (V K N) => powerShift A m) :=
  (powerShift_strictMono m).monotone

namespace ResidueChamber
variable (C : ResidueChamber (K := K) (N := N))
def nextIndex (_C : ResidueChamber (K := K) (N := N)) (hN : 0 < N) : Fin (N+1) := ⟨1,by omega⟩
noncomputable def rotateStage (hN : 0 < N) (r : Fin (N+1)) : Submodule K[X] (V K N) :=
  if hr : r.val < N then C.stage ⟨r.val+1,by omega⟩
  else powerShift (C.stage (C.nextIndex hN)) 1
lemma rotateStage_has (hN : 0 < N) (r : Fin (N+1)) : HasPivots (C.rotateStage hN r) := by
  unfold rotateStage
  split_ifs
  · exact C.hasStage _
  · exact powerShift_hasPivots _ (C.hasStage _) 1
lemma rotateStage_lower (hN : 0 < N) (r : Fin (N+1)) :
    powerShift (C.stage (C.nextIndex hN)) 1 ≤ C.rotateStage hN r := by
  unfold rotateStage
  split_ifs
  · apply le_trans _ (C.lower _)
    apply powerShift_mono 1
    rw [← C.initial]
    exact C.strict.antitone (Fin.zero_le _)
  · exact le_rfl

end ResidueChamber
end CoboundaryExpanders.PolynomialVectors

namespace CoboundaryExpanders.PolynomialVectors
open scoped Polynomial BigOperators
variable {K : Type} [Field K] {N : ℕ}

lemma leading_combination_max (b : Fin N → V K N) (a : Fin N → ℕ)
    (hb : ∀ i, Leading (b i) i (a i)) (f : Fin N → K[X])
    (i : Fin N) (hfi : f i ≠ 0)
    (hmax : ∀ j, f j ≠ 0 → N*(a j+(f j).natDegree)+j.val ≤ N*(a i+(f i).natDegree)+i.val) :
    Leading (∑ j, f j • b j) i (a i+(f i).natDegree) := by
  classical
  have hi := leading_mul (hb i) (f i) hfi
  constructor
  · have hh : ((∑ j, f j • b j) i).coeff (a i+(f i).natDegree) =
        ((f i • b i) i).coeff (a i+(f i).natDegree) := by
      simp only [Finset.sum_apply,Polynomial.finsetSum_coeff]
      apply Finset.sum_eq_single i
      · intro j _ hji
        by_cases hj : f j = 0
        · simp [hj]
        · apply (leading_mul (hb j) (f j) hj).2
          have hle := hmax j hj
          have hne : N*(a j+(f j).natDegree)+j.val ≠ N*(a i+(f i).natDegree)+i.val := by
            intro he
            exact hji (weight_injective he).1
          omega
      · simp
    exact hh ▸ hi.1
  · intro k e he
    simp only [Finset.sum_apply,Polynomial.finsetSum_coeff]
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : f j = 0
    · simp [hj]
    · exact (leading_mul (hb j) (f j) hj).2 k e (lt_of_le_of_lt (hmax j hj) he)

end CoboundaryExpanders.PolynomialVectors

namespace CoboundaryExpanders.PolynomialVectors
open scoped Polynomial BigOperators
variable {K : Type} [Field K] {N : ℕ}

lemma combination_pivot_degree (b : Fin N → V K N) (a : Fin N → ℕ)
    (hb : ∀ i, Leading (b i) i (a i)) (f : Fin N → K[X]) (i : Fin N) (e : ℕ)
    (hl : Leading (∑ j, f j • b j) i e) : f i ≠ 0 ∧ e = a i+(f i).natDegree := by
  classical
  let s := Finset.univ.filter (fun j => f j ≠ 0)
  have hs : s.Nonempty := by
    by_contra hn
    have hz : ∀ j, f j = 0 := by
      intro j
      by_contra hj
      exact hn ⟨j,by simp [s,hj]⟩
    have he : (∑ j, f j • b j) = 0 := by simp [hz]
    exact leading_ne_zero hl he
  let w (j : Fin N) := N*(a j+(f j).natDegree)+j.val
  obtain ⟨j,hjs,hmax⟩ := Finset.exists_max_image s w hs
  have hj : f j ≠ 0 := (Finset.mem_filter.mp hjs).2
  have hl' := leading_combination_max b a hb f j hj
    (fun k hk => hmax k (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hk⟩))
  obtain ⟨hji,he⟩ := leading_unique hl' hl
  subst j
  exact ⟨hj,he.symm⟩

lemma span_hasPivots (b : Fin N → V K N) (a : Fin N → ℕ)
    (hb : ∀ i, Leading (b i) i (a i)) :
    HasPivots (Submodule.span K[X] (Set.range b)) :=
  fun i => ⟨a i,b i,Submodule.subset_span ⟨i,rfl⟩,hb i⟩

lemma span_pivotDegree (b : Fin N → V K N) (a : Fin N → ℕ)
    (hb : ∀ i, Leading (b i) i (a i)) (i : Fin N) :
    pivotDegree (Submodule.span K[X] (Set.range b)) (span_hasPivots b a hb) i = a i := by
  let hA := span_hasPivots b a hb
  apply le_antisymm
  · exact pivotDegree_min _ hA i (Submodule.subset_span ⟨i,rfl⟩) (hb i)
  · obtain ⟨f,hf⟩ := (Submodule.mem_span_range_iff_exists_fun K[X]).mp (pivot_mem _ hA i)
    have hl : Leading (∑ j, f j • b j) i (pivotDegree _ hA i) := hf.symm ▸ pivot_leading _ hA i
    have he := (combination_pivot_degree b a hb f i _ hl).2
    omega

noncomputable def diagonalFamily (b : Fin N → V K N) (s : Finset (Fin N)) (i : Fin N) : V K N :=
  if i ∈ s then (Polynomial.X : K[X]) • b i else b i

noncomputable def diagonalModule (b : Fin N → V K N) (s : Finset (Fin N)) : Submodule K[X] (V K N) :=
  Submodule.span K[X] (Set.range (diagonalFamily b s))

lemma diagonal_leading (b : Fin N → V K N) (a : Fin N → ℕ)
    (hb : ∀ i, Leading (b i) i (a i)) (s : Finset (Fin N)) (i : Fin N) :
    Leading (diagonalFamily b s i) i (a i + if i ∈ s then 1 else 0) := by
  classical
  dsimp [diagonalFamily]
  split_ifs
  · simpa using leading_X_pow (hb i) 1
  · simpa using hb i

lemma diagonal_hasPivots (b : Fin N → V K N) (a : Fin N → ℕ)
    (hb : ∀ i, Leading (b i) i (a i)) (s : Finset (Fin N)) :
    HasPivots (diagonalModule b s) :=
  span_hasPivots (diagonalFamily b s) _ (diagonal_leading b a hb s)

lemma diagonal_pivotDegree (b : Fin N → V K N) (a : Fin N → ℕ)
    (hb : ∀ i, Leading (b i) i (a i)) (s : Finset (Fin N)) (i : Fin N) :
    pivotDegree (diagonalModule b s) (diagonal_hasPivots b a hb s) i =
      a i + if i ∈ s then 1 else 0 :=
  span_pivotDegree _ _ (diagonal_leading b a hb s) i

lemma diagonal_antitone (b : Fin N → V K N) {s t : Finset (Fin N)} (hst : s ⊆ t) :
    diagonalModule b t ≤ diagonalModule b s := by
  classical
  apply Submodule.span_le.mpr
  rintro _ ⟨i,rfl⟩
  by_cases his : i ∈ s
  · have hit := hst his
    exact Submodule.subset_span ⟨i,by simp [diagonalFamily,his,hit]⟩
  · by_cases hit : i ∈ t
    · have hi : b i ∈ diagonalModule b s :=
        Submodule.subset_span ⟨i,by simp [diagonalFamily,his]⟩
      simpa [diagonalFamily,hit] using (diagonalModule b s).smul_mem Polynomial.X hi
    · exact Submodule.subset_span ⟨i,by simp [diagonalFamily,his,hit]⟩

lemma diagonal_le_span (b : Fin N → V K N) (s : Finset (Fin N)) :
    diagonalModule b s ≤ Submodule.span K[X] (Set.range b) := by
  have hh := diagonal_antitone b (Finset.empty_subset s)
  have he : diagonalFamily b ∅ = b := by funext i; simp [diagonalFamily]
  simpa only [diagonalModule,he] using hh

lemma diagonal_eq_span (b : Fin N → V K N) :
    diagonalModule b ∅ = Submodule.span K[X] (Set.range b) := by
  have he : diagonalFamily b ∅ = b := by funext i; simp [diagonalFamily]
  simp only [diagonalModule,he]

end CoboundaryExpanders.PolynomialVectors

namespace CoboundaryExpanders.PolynomialVectors
open scoped Polynomial BigOperators
variable {K : Type} [Field K] {N : ℕ}

lemma diagonal_eq_powerShift (b : Fin N → V K N) :
    diagonalModule b Finset.univ = powerShift (Submodule.span K[X] (Set.range b)) 1 := by
  classical
  unfold diagonalModule powerShift
  rw [Submodule.map_span,← Set.range_comp]
  congr 2
  funext i
  simp [diagonalFamily,powerLinear]

lemma diagonal_injective (b : Fin N → V K N) (a : Fin N → ℕ)
    (hb : ∀ i, Leading (b i) i (a i)) : Function.Injective (diagonalModule b) := by
  classical
  intro s t he
  ext i
  have hs := diagonal_pivotDegree b a hb s i
  have ht := diagonal_pivotDegree b a hb t i
  simp only [he] at hs
  by_cases his : i ∈ s <;> by_cases hit : i ∈ t <;> simp_all

lemma diagonal_strictAnti (b : Fin N → V K N) (a : Fin N → ℕ)
    (hb : ∀ i, Leading (b i) i (a i)) : StrictAnti (diagonalModule b) := by
  intro s t hst
  exact lt_of_le_of_ne (diagonal_antitone b hst.le)
    (fun he => hst.ne ((diagonal_injective b a hb he).symm))

noncomputable def wordPrefix (π : Equiv.Perm (Fin N)) (r : Fin (N+1)) : Finset (Fin N) :=
  Finset.univ.filter fun i => (π.symm i).val < r.val

lemma wordPrefix_strict (π : Equiv.Perm (Fin N)) : StrictMono (wordPrefix π) := by
  classical
  intro r s hrs
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro i hi
    have hh := (Finset.mem_filter.mp hi).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,lt_trans hh hrs⟩
  · intro he
    let j : Fin N := ⟨r.val,by have := s.isLt; change r.val < s.val at hrs; omega⟩
    have hj : π j ∈ wordPrefix π s := by
      simp only [wordPrefix,Finset.mem_filter,Finset.mem_univ,true_and,Equiv.symm_apply_apply]
      exact hrs
    rw [← he] at hj
    simp [wordPrefix,j] at hj

lemma wordPrefix_zero (π : Equiv.Perm (Fin N)) : wordPrefix π 0 = ∅ := by
  classical
  simp [wordPrefix]

noncomputable def diagonalChamber (b : Fin N → V K N) (a : Fin N → ℕ)
    (hb : ∀ i, Leading (b i) i (a i)) (π : Equiv.Perm (Fin N)) : ResidueChamber (K := K) (N := N) where
  top := Submodule.span K[X] (Set.range b)
  hasTop := span_hasPivots b a hb
  stage r := diagonalModule b (wordPrefix π r)
  hasStage r := diagonal_hasPivots b a hb _
  strict := by
    intro r s hrs
    exact diagonal_strictAnti b a hb (wordPrefix_strict π hrs)
  initial := by rw [wordPrefix_zero,diagonal_eq_span]
  lower r := by
    rw [← diagonal_eq_powerShift]
    exact diagonal_antitone b (Finset.subset_univ _)

end CoboundaryExpanders.PolynomialVectors

namespace CoboundaryExpanders.PolynomialVectors
open scoped Polynomial BigOperators
variable {K : Type} [Field K] {N : ℕ}
lemma powerShift_add (A : Submodule K[X] (V K N)) (a b : ℕ) :
    powerShift (powerShift A a) b = powerShift A (a+b) := by
  unfold powerShift
  rw [← Submodule.map_comp]
  apply congrArg (fun f : V K N →ₗ[K[X]] V K N => A.map f)
  apply LinearMap.ext
  intro v
  funext i
  change (Polynomial.X^b : K[X]) * ((Polynomial.X^a : K[X])*v i) =
    (Polynomial.X^(a+b) : K[X])*v i
  rw [pow_add]
  ring

namespace ResidueChamber
variable (C : ResidueChamber (K := K) (N := N))
noncomputable def scale (m : ℕ) : ResidueChamber (K := K) (N := N) where
  top := powerShift C.top m
  hasTop := powerShift_hasPivots _ C.hasTop m
  stage r := powerShift (C.stage r) m
  hasStage r := powerShift_hasPivots _ (C.hasStage r) m
  strict := by intro r s h; exact powerShift_strictMono m (C.strict h)
  initial := by rw [C.initial]
  lower r := by
    rw [powerShift_add,show m+1 = 1+m by omega,← powerShift_add]
    exact powerShift_mono m (C.lower r)
end ResidueChamber
end CoboundaryExpanders.PolynomialVectors

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Coboundary_Joins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Binary and finite joins, augmented exactness, and bounded cone constructions.
-/

open scoped Polynomial BigOperators

namespace CoboundaryExpanders.InfiniteChains.Join

section
open Attachment Cone
open scoped BigOperators
variable {V : Type} [DecidableEq V]
def fiber {L : ℕ} (s : Finset (Fin L × V)) (i : Fin L) : Finset V :=
  (s.filter fun x => x.1 = i).image Prod.snd
@[simp] lemma mem_fiber {L : ℕ} (s : Finset (Fin L × V)) (i : Fin L) (v : V) :
    v ∈ fiber s i ↔ (i,v) ∈ s := by
  simp only [fiber,Finset.mem_image,Finset.mem_filter]
  constructor
  · rintro ⟨⟨j,w⟩,⟨hm,hj⟩,hw⟩
    dsimp only at hj hw
    simpa only [hj,hw] using hm
  · intro h
    exact ⟨(i,v),⟨h,rfl⟩,rfl⟩

def splitEquiv (L : ℕ) : (Fin (L+1) × V) ≃ (V ⊕ (Fin L × V)) where
  toFun x := Fin.cases (Sum.inl x.2) (fun i => Sum.inr (i,x.2)) x.1
  invFun := Sum.elim (fun v => (0,v)) (fun x => (x.1.succ,x.2))
  left_inv := by rintro ⟨i,v⟩; induction i using Fin.cases <;> rfl
  right_inv := by intro x; cases x <;> rfl
omit [DecidableEq V] in
@[simp] lemma splitEquiv_zero (L : ℕ) (v : V) : splitEquiv L (0,v) = Sum.inl v := rfl
omit [DecidableEq V] in
@[simp] lemma splitEquiv_succ (L : ℕ) (i : Fin L) (v : V) :
    splitEquiv L (i.succ,v) = Sum.inr (i,v) := rfl
def oneEquiv : (Fin 1 × V) ≃ V where
  toFun := Prod.snd
  invFun v := (0,v)
  left_inv := by rintro ⟨i,v⟩; have hi : i = 0 := Subsingleton.elim _ _; simp only [hi]
  right_inv _ := rfl

end

open Attachment Cone
open scoped BigOperators
end CoboundaryExpanders.InfiniteChains.Join

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Coboundary_ChamberCones
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Finite pivots, polynomial residue-chamber links, and exactness via finite joins.
-/

noncomputable section
open scoped Polynomial BigOperators

namespace CoboundaryExpanders.FinitePivots
open scoped BigOperators
variable {K : Type} [Field K] {N : ℕ}

def Leading (v : Fin N → K) (i : Fin N) : Prop :=
  v i ≠ 0 ∧ ∀ j, i < j → v j = 0

def HasPivot (W : Submodule K (Fin N → K)) (i : Fin N) : Prop :=
  ∃ v ∈ W, Leading v i

def prefSpace (K : Type) [Field K] (N k : ℕ) : Submodule K (Fin N → K) where
  carrier := {v | ∀ i, k ≤ i.val → v i = 0}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy i hi; simp [hx i hi,hy i hi]
  smul_mem' := by intro a x hx i hi; simp [hx i hi]

lemma exists_leading {v : Fin N → K} (hv : v ≠ 0) : ∃ i, Leading v i := by
  classical
  let s := Finset.univ.filter (fun i => v i ≠ 0)
  have hs : s.Nonempty := by
    by_contra hn
    apply hv
    ext i
    by_contra hi
    exact hn ⟨i,by simpa [s] using hi⟩
  refine ⟨s.max' hs,(Finset.mem_filter.mp (Finset.max'_mem s hs)).2,?_⟩
  intro j hj
  by_contra hz
  have hle := Finset.le_max' s j (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hz⟩)
  exact (not_lt_of_ge hle) hj

end CoboundaryExpanders.FinitePivots

namespace CoboundaryExpanders.PolynomialVectors
open scoped Polynomial BigOperators
variable {K : Type} [Field K] {N M : ℕ}

lemma C_smul_vector (c : K) (v : V K N) : (Polynomial.C c) • v = c • v := by
  funext i
  exact (Polynomial.smul_eq_C_mul c).symm

def selectedSection (b : Fin N → V K N) (σ : Fin M → Fin N) :
    (Fin M → K) →ₗ[K] V K N where
  toFun x := ∑ r, x r • b (σ r)
  map_add' x y := by simp [add_smul,Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.smul_sum,mul_smul]

lemma selectedSection_leading (b : Fin N → V K N) (a : Fin N → ℕ)
    (hb : ∀ i, Leading (b i) i (a i)) (σ : Fin M → Fin N)
    (hσ : StrictMono (fun r => N*a (σ r)+(σ r).val))
    (x : Fin M → K) (r : Fin M) (hx : FinitePivots.Leading x r) :
    Leading (selectedSection b σ x) (σ r) (a (σ r)) := by
  classical
  have hsec (i : Fin N) (e : ℕ) :
      ((selectedSection b σ x) i).coeff e = ∑ j, x j * (b (σ j) i).coeff e := by
    simp [selectedSection,Finset.sum_apply,Polynomial.finsetSum_coeff]
  constructor
  · rw [hsec,Finset.sum_eq_single r]
    · exact mul_ne_zero hx.1 (hb (σ r)).1
    · intro j _ hj
      rcases lt_or_gt_of_ne hj with hlt | hgt
      · rw [(hb (σ j)).2 (σ r) (a (σ r)) (hσ hlt),mul_zero]
      · rw [hx.2 j hgt,zero_mul]
    · simp
  · intro i e he
    rw [hsec]
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : j ≤ r
    · rw [(hb (σ j)).2 i e ((hσ.monotone hj).trans_lt he),mul_zero]
    · rw [hx.2 j (lt_of_not_ge hj),zero_mul]

noncomputable def selectedResidue (b : Fin N → V K N) (σ : Fin M → Fin N)
    (D : Submodule K[X] (V K N)) : Submodule K (Fin M → K) :=
  (D.restrictScalars K).comap (selectedSection b σ)

lemma selectedSection_polynomial (b : Fin N → V K N) (σ : Fin M → Fin N) (x : Fin M → K) :
    selectedSection b σ x = ∑ r, Polynomial.C (x r) • b (σ r) := by
  simp only [selectedSection,LinearMap.coe_mk,AddHom.coe_mk,C_smul_vector]

end CoboundaryExpanders.PolynomialVectors

namespace CoboundaryExpanders.PolynomialVectors
open scoped Polynomial BigOperators
variable {K : Type} [Field K] {N M : ℕ}

lemma X_smul_mem_diagonal (b : Fin N → V K N) (s : Finset (Fin N)) (v : V K N)
    (hv : v ∈ Submodule.span K[X] (Set.range b)) : (Polynomial.X : K[X]) • v ∈ diagonalModule b s := by
  classical
  obtain ⟨f,rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K[X]).mp hv
  rw [Finset.smul_sum]
  apply Submodule.sum_mem
  intro i _
  rw [smul_comm]
  apply Submodule.smul_mem
  by_cases hi : i ∈ s
  · exact Submodule.subset_span ⟨i,by simp [diagonalFamily,hi]⟩
  · apply Submodule.smul_mem
    exact Submodule.subset_span ⟨i,by simp [diagonalFamily,hi]⟩

lemma selectedSection_mem_span (b : Fin N → V K N) (σ : Fin M → Fin N) (x : Fin M → K) :
    selectedSection b σ x ∈ Submodule.span K[X] (Set.range b) := by
  rw [selectedSection_polynomial]
  apply Submodule.sum_mem
  intro r _
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨σ r,rfl⟩)

lemma polynomial_smul_section_mod (b : Fin N → V K N) (σ : Fin M → Fin N)
    (f : K[X]) (x : Fin M → K) :
    f • selectedSection b σ x - selectedSection b σ (f.coeff 0 • x) ∈
      diagonalModule b (Finset.univ.image σ) := by
  have hd : Polynomial.X ∣ f-Polynomial.C (f.coeff 0) := Polynomial.X_dvd_iff.mpr (by simp)
  obtain ⟨q,hq⟩ := hd
  have he : f • selectedSection b σ x - selectedSection b σ (f.coeff 0 • x) =
      q • ((Polynomial.X : K[X]) • selectedSection b σ x) := by
    rw [map_smul,← C_smul_vector,← sub_smul,hq,mul_comm,mul_smul]
  rw [he]
  apply Submodule.smul_mem
  exact X_smul_mem_diagonal b _ _ (selectedSection_mem_span b σ x)

noncomputable def liftSelected (b : Fin N → V K N) (σ : Fin M → Fin N)
    (W : Submodule K (Fin M → K)) : Submodule K[X] (V K N) where
  carrier := {v | ∃ c ∈ diagonalModule b (Finset.univ.image σ), ∃ x ∈ W, v = c+selectedSection b σ x}
  zero_mem' := ⟨0,Submodule.zero_mem _,0,W.zero_mem,by simp⟩
  add_mem' := by
    rintro v w ⟨c,hc,x,hx,rfl⟩ ⟨d,hd,y,hy,rfl⟩
    refine ⟨c+d,Submodule.add_mem _ hc hd,x+y,W.add_mem hx hy,?_⟩
    rw [map_add]
    abel
  smul_mem' := by
    rintro f v ⟨c,hc,x,hx,rfl⟩
    refine ⟨f • c + (f • selectedSection b σ x - selectedSection b σ (f.coeff 0 • x)),
      Submodule.add_mem _ (Submodule.smul_mem _ f hc) (polynomial_smul_section_mod b σ f x),
      f.coeff 0 • x,W.smul_mem _ hx,?_⟩
    rw [smul_add]
    abel

lemma diagonal_le_liftSelected (b : Fin N → V K N) (σ : Fin M → Fin N)
    (W : Submodule K (Fin M → K)) : diagonalModule b (Finset.univ.image σ) ≤ liftSelected b σ W := by
  intro v hv
  exact ⟨v,hv,0,W.zero_mem,by simp⟩

lemma liftSelected_le_span (b : Fin N → V K N) (σ : Fin M → Fin N)
    (W : Submodule K (Fin M → K)) : liftSelected b σ W ≤ Submodule.span K[X] (Set.range b) := by
  rintro v ⟨c,hc,x,hx,rfl⟩
  exact Submodule.add_mem _ (diagonal_le_span b _ hc) (selectedSection_mem_span b σ x)

end CoboundaryExpanders.PolynomialVectors

namespace CoboundaryExpanders.FinitePivots
open Module
variable {K : Type} [Field K] {N : ℕ}

noncomputable def prefEquiv (k : ℕ) (hk : k ≤ N) :
    (Fin k → K) ≃ₗ[K] prefSpace K N k where
  toFun x := ⟨fun i => if h : i.val < k then x ⟨i.val,h⟩ else 0, by
    intro i hi
    simp [show ¬i.val < k from by omega]⟩
  invFun y := fun i => y.val ⟨i.val,lt_of_lt_of_le i.isLt hk⟩
  left_inv x := by funext i; simp
  right_inv y := by
    apply Subtype.ext
    funext i
    dsimp only
    split_ifs with hi
    · rfl
    · exact (y.property i (by omega)).symm
  map_add' x y := by
    apply Subtype.ext
    funext i
    change (if h : i.val < k then (x+y) ⟨i.val,h⟩ else 0) =
      (if h : i.val < k then x ⟨i.val,h⟩ else 0) + (if h : i.val < k then y ⟨i.val,h⟩ else 0)
    split_ifs <;> simp_all
  map_smul' c x := by
    apply Subtype.ext
    funext i
    change (if h : i.val < k then (c • x) ⟨i.val,h⟩ else 0) =
      c • (if h : i.val < k then x ⟨i.val,h⟩ else 0)
    split_ifs <;> simp_all

lemma prefSpace_finrank (k : ℕ) (hk : k ≤ N) : finrank K (prefSpace K N k) = k := by
  rw [← (prefEquiv (K := K) k hk).finrank_eq]
  simp

end CoboundaryExpanders.FinitePivots

namespace CoboundaryExpanders.PolynomialVectors
open scoped Polynomial BigOperators
open Module InfiniteChains InfiniteChains.Attachment InfiniteChains.Cone
variable {K : Type} [Field K] {N M : ℕ}

abbrev SelectedInterval (b : Fin N → V K N) (σ : Fin M → Fin N) :=
  {D : Submodule K[X] (V K N) // diagonalModule b (Finset.univ.image σ) ≤ D ∧
    D ≤ Submodule.span K[X] (Set.range b)}

lemma selectedInterval_hasPivots (b : Fin N → V K N) (a : Fin N → ℕ)
    (hb : ∀ i, Leading (b i) i (a i)) (σ : Fin M → Fin N) (D : SelectedInterval b σ) :
    HasPivots D.val := by
  intro i
  obtain ⟨m,v,hv,hl⟩ := diagonal_hasPivots b a hb (Finset.univ.image σ) i
  exact ⟨m,v,D.property.1 hv,hl⟩

def PrefixPattern (b : Fin N → V K N) (a : Fin N → ℕ)
    (hb : ∀ i, Leading (b i) i (a i)) (σ : Fin M → Fin N) (D : SelectedInterval b σ) : Prop :=
  ∃ k : ℕ, 0 < k ∧ k < M ∧ ∀ r,
    pivotDegree D.val (selectedInterval_hasPivots b a hb σ D) (σ r) = a (σ r) ↔ k ≤ r.val

end CoboundaryExpanders.PolynomialVectors

namespace CoboundaryExpanders.PolynomialVectors
open scoped Polynomial BigOperators
variable {K : Type} [Field K] {N M : ℕ}

lemma selected_pivot_bounds (b : Fin N → V K N) (a : Fin N → ℕ)
    (hb : ∀ i, Leading (b i) i (a i)) (σ : Fin M → Fin N)
    (D : SelectedInterval b σ) (i : Fin N) :
    a i ≤ pivotDegree D.val (selectedInterval_hasPivots b a hb σ D) i ∧
      pivotDegree D.val (selectedInterval_hasPivots b a hb σ D) i ≤
        a i + if i ∈ Finset.univ.image σ then 1 else 0 := by
  constructor
  · have h := pivotDegree_antitone (span_hasPivots b a hb)
      (selectedInterval_hasPivots b a hb σ D) D.property.2 i
    rwa [span_pivotDegree b a hb i] at h
  · have h := pivotDegree_antitone (selectedInterval_hasPivots b a hb σ D)
      (diagonal_hasPivots b a hb (Finset.univ.image σ)) D.property.1 i
    rwa [diagonal_pivotDegree b a hb (Finset.univ.image σ) i] at h

end CoboundaryExpanders.PolynomialVectors

namespace CoboundaryExpanders.PolynomialVectors
open scoped Polynomial BigOperators
variable {K : Type} [Field K] {N : ℕ}
lemma diagonalFamily_union (b : Fin N → V K N) (s t : Finset (Fin N))
    (h : Disjoint s t) : diagonalFamily (diagonalFamily b s) t = diagonalFamily b (s ∪ t) := by
  classical
  funext i
  have hh := Finset.disjoint_left.mp h
  by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;> simp_all [diagonalFamily]
lemma diagonalModule_union (b : Fin N → V K N) (s t : Finset (Fin N))
    (h : Disjoint s t) : diagonalModule (diagonalFamily b s) t = diagonalModule b (s ∪ t) := by
  unfold diagonalModule
  rw [diagonalFamily_union b s t h]

noncomputable def wordSlice (π : Equiv.Perm (Fin N)) (a b : Fin (N+1)) : Fin (b.val-a.val) → Fin N :=
  fun r => π ⟨a.val+r.val,by have := r.isLt; have := b.isLt; omega⟩
lemma mem_wordSlice_image (π : Equiv.Perm (Fin N)) (a b : Fin (N+1)) (i : Fin N) :
    i ∈ Finset.univ.image (wordSlice π a b) ↔ a.val ≤ (π.symm i).val ∧ (π.symm i).val < b.val := by
  classical
  simp only [Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨r,rfl⟩
    simp only [wordSlice,Equiv.symm_apply_apply,Fin.val_mk]
    have := r.isLt
    omega
  · rintro ⟨ha,hb⟩
    refine ⟨⟨(π.symm i).val-a.val,by omega⟩,?_⟩
    change π ⟨a.val+((π.symm i).val-a.val),_⟩ = i
    have he : (⟨a.val+((π.symm i).val-a.val),by omega⟩ : Fin N) = π.symm i := Fin.ext (by dsimp only; omega)
    rw [he,Equiv.apply_symm_apply]
lemma wordPrefix_disjoint_slice (π : Equiv.Perm (Fin N)) (a b : Fin (N+1)) :
    Disjoint (wordPrefix π a) (Finset.univ.image (wordSlice π a b)) := by
  classical
  apply Finset.disjoint_left.mpr
  intro i hi hs
  have hh := (mem_wordSlice_image π a b i).mp hs
  simp only [wordPrefix,Finset.mem_filter,Finset.mem_univ,true_and] at hi
  omega
lemma wordPrefix_union_slice (π : Equiv.Perm (Fin N)) (a b : Fin (N+1)) (hab : a ≤ b) :
    wordPrefix π a ∪ Finset.univ.image (wordSlice π a b) = wordPrefix π b := by
  classical
  ext i
  rw [Finset.mem_union,mem_wordSlice_image]
  simp only [wordPrefix,Finset.mem_filter,Finset.mem_univ,true_and]
  change a.val ≤ b.val at hab
  omega

end CoboundaryExpanders.PolynomialVectors

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Coboundary_Links
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Coset-link identifications, product and cut models, and all proper-link cone bounds.
-/

noncomputable section
open scoped BigOperators
open scoped BigOperators Matrix
open scoped Matrix

namespace CoboundaryExpanders.MatrixOpposition
open SphericalOpposition SphericalOpposition.CompleteFlag InfiniteChains Cone
open scoped Pointwise
variable {K : Type} [Field K] {N : ℕ}

instance cutDecidableEq : DecidableEq (Cut N) := Classical.decEq _
instance cutFinite : Finite (Cut N) := Finite.of_injective (fun c : Cut N => (⟨c.val,c.property.2⟩ : Fin N))
  (fun _ _ h => Subtype.ext (congrArg Fin.val h))
noncomputable instance cutFintype : Fintype (Cut N) := Fintype.ofFinite _

def cutTypeEquiv : Cut N ≃ Fin (N-1) where
  toFun c := ⟨N-c.val-1,by have h:=c.property; omega⟩
  invFun i := ⟨N-i.val-1,by have h:=i.isLt; omega⟩
  left_inv c := by apply Subtype.ext; have h:=c.property; dsimp; omega
  right_inv i := by apply Fin.ext; have h:=i.isLt; dsimp; omega

end CoboundaryExpanders.MatrixOpposition

namespace CoboundaryExpanders.MatrixOpposition
open SphericalOpposition SphericalOpposition.CompleteFlag InfiniteChains Cone
variable {K : Type} [Field K] {a b : ℕ}

def middleCut (ha : 0 < a) (hb : 0 < b) : Cut (a+b) := ⟨a,ha,by omega⟩

end CoboundaryExpanders.MatrixOpposition

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Coboundary_LinkSpectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Rank-two incidence geometry, weighted Rayleigh inequalities, and spectral bounds for links.
-/

noncomputable section
open scoped BigOperators
open scoped BigOperators Matrix
open scoped Matrix

namespace CoboundaryExpanders.RankTwoGeometry

section
open MatrixOpposition Elementary
open scoped Matrix
variable {K : Type} [Field K]

def matrix3 (a b c : K) : Matrix (Fin 3) (Fin 3) K := !![1,a,c; 0,1,b; 0,0,1]
lemma matrix3_det (a b c : K) : (matrix3 a b c).det = 1 := by
  simp [matrix3,Matrix.det_fin_three]

def pointCut : Cut 3 := ⟨2,by decide⟩
def lineCut : Cut 3 := ⟨1,by decide⟩

end

open MatrixOpposition InfiniteChains Cone
variable {K : Type} [Field K]
local instance instDecidableEq_solutions : DecidableEq K := Classical.decEq _

abbrev Vert (K : Type) := (K × K) ⊕ (K × K)

lemma cuts3 (i : Cut 3) : i = pointCut ∨ i = lineCut := by
  have hi := i.property
  by_cases h : i.val = 2
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext (by dsimp [lineCut]; omega))

def incident (P L : K × K) : Prop := P.2 = L.1*P.1+L.2

end CoboundaryExpanders.RankTwoGeometry

namespace CoboundaryExpanders.RankTwo
variable {K : Type} [Field K] [Fintype K]
local instance instDecidableEq_solutions : DecidableEq K := Classical.decEq _

def lineSum (f : K → K → ℝ) (a b : K) : ℝ := ∑ x, f x (a*x+b)
def pointSum (g : K → K → ℝ) (x y : K) : ℝ := ∑ a, g a (y-a*x)
def energy (f : K → K → ℝ) : ℝ := ∑ x, ∑ y, (f x y)^2

def pairing (f g : K → K → ℝ) : ℝ := ∑ x, ∑ y, f x y * g x y

def total (f : K → K → ℝ) : ℝ := ∑ x, ∑ y, f x y

def center (f : K → K → ℝ) (x y : K) : ℝ :=
  f x y - total f / (Fintype.card K : ℝ)^2

end CoboundaryExpanders.RankTwo

namespace CoboundaryExpanders.EdgeMixing
variable {V : Type*} [Fintype V]
def mass (e : V → V → ℝ) (x : V) : ℝ := ∑ y, e x y
def energy (e : V → V → ℝ) (f : V → ℝ) : ℝ := ∑ x, mass e x * (f x)^2
def pairing (e : V → V → ℝ) (f g : V → ℝ) : ℝ := ∑ x, ∑ y, e x y * f x * g y
def Rayleigh (e : V → V → ℝ) (lam : ℝ) : Prop :=
  ∀ f : V → ℝ, (∑ x, mass e x * f x) = 0 → pairing e f f ≤ lam*energy e f
end CoboundaryExpanders.EdgeMixing

namespace CoboundaryExpanders.RankTwo
variable {K : Type} [Field K] [Fintype K]
local instance instDecidableEq_solutions_1 : DecidableEq K := Classical.decEq _
abbrev Vert (K : Type) := (K×K) ⊕ (K×K)
def edge : Vert K → Vert K → ℝ
  | .inl P, .inr L => if P.2 = L.1*P.1+L.2 then 1 else 0
  | .inr L, .inl P => if P.2 = L.1*P.1+L.2 then 1 else 0
  | _, _ => 0

end CoboundaryExpanders.RankTwo

namespace CoboundaryExpanders.EdgeMixing
variable {V W : Type} [Fintype V] [Fintype W]
lemma sum_embedding (f : V → W) (hf : Function.Injective f) (F : W → ℝ)
    (hF : ∀ y, y ∉ Set.range f → F y = 0) : (∑ y,F y) = ∑ x,F (f x) := by
  classical
  rw [←Finset.sum_image (s:=Finset.univ) (f:=F) (g:=f) (fun _ _ _ _ h => hf h)]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro y _ hy
  exact hF y (by simpa only [Finset.mem_image,Finset.mem_univ,true_and,Set.mem_range] using hy)

structure Embedding (e : V → V → ℝ) (d : W → W → ℝ) where
  vertex : V → W
  injective : Function.Injective vertex
  edge_eq : ∀ x y, d (vertex x) (vertex y) = e x y
  outside_zero : ∀ y, y ∉ Set.range vertex → ∀ z, d y z = 0

namespace Embedding
variable {e : V → V → ℝ} {d : W → W → ℝ} (M : Embedding e d)
  (hd : ∀ x y,d x y = d y x)
include M hd

lemma mass_map (x : V) : mass d (M.vertex x) = mass e x := by
  unfold mass
  rw [sum_embedding M.vertex M.injective _ (fun y hy => by rw [hd,M.outside_zero y hy])]
  simp only [M.edge_eq]
end Embedding
end CoboundaryExpanders.EdgeMixing

namespace CoboundaryExpanders.RankTwoGeometry
open InfiniteChains MatrixOpposition
variable {K : Type} [Field K] [Fintype K]
local instance instDecidableEq_solutions_1 : DecidableEq K := Classical.decEq _

end CoboundaryExpanders.RankTwoGeometry

namespace CoboundaryExpanders.EdgeMixing

section
variable {V W : Type} [Fintype V] [Fintype W]
attribute [local instance] Classical.propDecidable
namespace Embedding
variable {e : V → V → ℝ} {d : W → W → ℝ} (M : Embedding e d)
def extend (f : V → ℝ) (y : W) : ℝ :=
  if h : y ∈ Set.range M.vertex then f h.choose else 0
end Embedding

end

variable {A B : Type} [Fintype A] [Fintype B]
def bipartiteEdge : A ⊕ B → A ⊕ B → ℝ
  | Sum.inl _,Sum.inr _ => 1
  | Sum.inr _,Sum.inl _ => 1
  | _,_ => 0
@[simp] lemma bipartite_mass_left (a : A) : mass (bipartiteEdge (B:=B)) (Sum.inl a) = Fintype.card B := by
  simp [mass,Fintype.sum_sum_type,bipartiteEdge]
@[simp] lemma bipartite_mass_right (b : B) : mass (bipartiteEdge (A:=A)) (Sum.inr b) = Fintype.card A := by
  simp [mass,Fintype.sum_sum_type,bipartiteEdge]

end CoboundaryExpanders.EdgeMixing

namespace CoboundaryExpanders.InfiniteChains.Join
open Cone
variable {V W : Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
attribute [local instance] Classical.propDecidable
omit [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] in
@[simp] lemma left_single_inl (x : V) : ({Sum.inl x}:Finset (V ⊕ W)).toLeft = {x} := by ext y; simp
omit [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] in
@[simp] lemma right_single_inl (x : V) : ({Sum.inl x}:Finset (V ⊕ W)).toRight = ∅ := by ext y; simp
omit [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] in
@[simp] lemma left_single_inr (x : W) : ({Sum.inr x}:Finset (V ⊕ W)).toLeft = ∅ := by ext y; simp
omit [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] in
@[simp] lemma right_single_inr (x : W) : ({Sum.inr x}:Finset (V ⊕ W)).toRight = {x} := by ext y; simp

end CoboundaryExpanders.InfiniteChains.Join

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Coboundary_FatLadders
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Balanced chamber weights, fat ladders, degeneracy, and cochain counting.
-/

noncomputable section
open scoped BigOperators
open scoped BigOperators Matrix
open scoped Matrix

namespace CoboundaryExpanders.FatLadders

section
attribute [local instance] Classical.propDecidable
variable {V : Type*} [DecidableEq V]

inductive Path (F : Finset V → Prop) (s : Finset V) : Finset V → Prop
  | refl : F s → Path F s s
  | step {a : Finset V} (v : V) : Path F s a → v ∉ a → F (insert v a) →
      Path F s (insert v a)

def NoBad (F : Finset V → Prop) (T : Finset V) : Prop :=
  ∀ a ⊆ T, ∀ x ∈ a, ∀ y ∈ a, x ≠ y →
    F (a.erase x) → F (a.erase y) → F ((a.erase x).erase y)

def Minimal (F : Finset V → Prop) (s : Finset V) : Prop :=
  F s ∧ ∀ x ∈ s, ¬ F (s.erase x)

abbrev k := ZMod 2

def indicator (F : Finset V → Prop) (s : Finset V) : k := if F s then 1 else 0

def delta (f : Finset V → k) (s : Finset V) : k := ∑ x ∈ s, f (s.erase x)

end

section
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

def level (r : ℕ) : Finset (Finset V) := Finset.univ.powersetCard r
omit [DecidableEq V] in
@[simp] lemma mem_level {r : ℕ} {s : Finset V} : s ∈ level (V:=V) r ↔ s.card = r := by
  simp [level]

def atom (w : Finset V → ℝ) (f : Finset V → k) (s : Finset V) : ℝ :=
  if f s = 0 then 0 else w s

def norm (w : Finset V → ℝ) (r : ℕ) (f : Finset V → k) : ℝ :=
  ∑ s ∈ level r, atom w f s

def starSum (r : ℕ) (s : Finset V) (f : Finset V → ℝ) : ℝ :=
  ∑ t ∈ level r, if s ⊆ t then f t else 0

def starNorm (w : Finset V → ℝ) (r : ℕ) (s : Finset V) (f : Finset V → k) : ℝ :=
  starSum r s (atom w f)

omit [Fintype V] [DecidableEq V] in
lemma atom_nonneg {w : Finset V → ℝ} (hw : ∀ s, 0 ≤ w s) (f : Finset V → k) (s) :
    0 ≤ atom w f s := by unfold atom; split_ifs; exact le_rfl; exact hw s
omit [DecidableEq V] in
lemma norm_nonneg {w : Finset V → ℝ} (hw : ∀ s, 0 ≤ w s) (r) (f : Finset V → k) :
    0 ≤ norm w r f := Finset.sum_nonneg (fun s _ => atom_nonneg hw f s)
omit [Fintype V] [DecidableEq V] in
lemma atom_add_le {w : Finset V → ℝ} (hw : ∀ s, 0 ≤ w s) (f g : Finset V → k) (s) :
    atom w (f+g) s ≤ atom w f s + atom w g s := by
  unfold atom
  simp only [Pi.add_apply]
  by_cases hf : f s = 0 <;> by_cases hg : g s = 0 <;> simp [hf,hg]
  split_ifs <;> linarith [hw s]

def minimalFaces (F : Finset V → Prop) : Finset (Finset V) :=
  Finset.univ.filter (Minimal F)

def NearMinimal (w : Finset V → ℝ) (r : ℕ) (ε : ℝ) (f : Finset V → k) : Prop :=
  ∀ s : Finset V, s.Nonempty → s.card < r → ∀ b : Finset V → k,
    (∀ t, ¬ s ⊆ t → b t = 0) →
    (1-ε) * starNorm w r s f ≤ starNorm w r s (f + delta b)

def LinkCorrection (w : Finset V → ℝ) (r : ℕ) (C : ℝ) : Prop :=
  ∀ s : Finset V, s.Nonempty → s.card ≤ r → ∀ g : Finset V → k,
    (∀ t, ¬ s ⊆ t → g t = 0) →
    ∃ b : Finset V → k, (∀ t, ¬ s ⊆ t → b t = 0) ∧
      (s.card = r → ∀ t ∈ level r, delta b t = 0) ∧
      starNorm w r s (g + delta b) ≤ C * starNorm w (r+1) s (delta g)

end

section
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

def chamberWeight {A : Type*} [Fintype A] (c : A → Finset V) (μ : A → ℝ)
    (s : Finset V) : ℝ := ∑ a, if s ⊆ c a then μ a else 0

structure Balanced (w : Finset V → ℝ) (N : ℕ) : Prop where
  nonneg : ∀ s, 0 ≤ w s
  vanish : ∀ s, N < s.card → w s = 0
  balance : ∀ s R, s.card ≤ R → starSum R s w =
    (Nat.choose (N-s.card) (R-s.card):ℝ)*w s

end

section
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

def Collision (F : Finset V → Prop) (s a : Finset V) : Prop :=
  ∃ x ∈ a, ∃ y ∈ a, x ≠ y ∧ (a.erase x).erase y = s ∧
    F (a.erase x) ∧ F (a.erase y)

def collisionMass (w : Finset V → ℝ) (F : Finset V → Prop) (s : Finset V) : ℝ :=
  ∑ a ∈ level (s.card+2), if Collision F s a then w a else 0

def thinBases (F : Finset V → Prop) (r : ℕ) : Finset (Finset V) :=
  Finset.univ.filter (fun s => s.card < r ∧ ¬ F s)

end

section
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

omit [Fintype V] [DecidableEq V] in
@[simp] lemma atom_indicator (w : Finset V → ℝ) (F : Finset V → Prop) (s : Finset V) :
    atom w (indicator F) s = if F s then w s else 0 := by
  by_cases h : F s <;> simp [atom,indicator,h]

def fatAt (w : Finset V → ℝ) (N : ℕ) (θ : ℕ → ℝ) (f : Finset V → k) :
    ℕ → Finset V → Prop
  | 0, s => f s ≠ 0 ∧ 0 < w s
  | k+1, s => 0 < w s ∧ θ s.card * (N-s.card:ℕ) * w s ≤
      starNorm w (s.card+1) s (indicator (fatAt w N θ f k))

def fatFamily (w : Finset V → ℝ) (N r : ℕ) (θ : ℕ → ℝ) (f : Finset V → k)
    (s : Finset V) : Prop := s.card ≤ r ∧ fatAt w N θ f (r-s.card) s

def fatBudget (N : ℕ) (η : ℝ) : ℕ → ℝ
  | 0 => 1
  | k+1 => (N:ℝ) * (fatBudget N η k)^2 / η

def fatThreshold (N r : ℕ) (η : ℝ) (j : ℕ) : ℝ := η / fatBudget N η (r-j-1)

end

variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

def LocalMixing (w : Finset V → ℝ) (N : ℕ) (lam : ℝ) : Prop :=
  ∀ (F : Finset V → Prop) (s : Finset V), s.card < N → ∀ t : ℝ, 0 ≤ t →
    starNorm w (s.card+1) s (indicator F) ≤ t*(N-s.card:ℕ)*w s →
    collisionMass w F s ≤ (t+lam)*(N:ℝ)*starNorm w (s.card+1) s (indicator F)

end CoboundaryExpanders.FatLadders

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Coboundary_Spectral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Self-adjoint operator estimates and the weighted-graph spectral trickling argument.
-/

noncomputable section
open scoped BigOperators
open scoped BigOperators Matrix
open scoped Matrix
open scoped BigOperators InnerProductSpace

namespace CoboundaryExpanders.Spectral

open scoped BigOperators InnerProductSpace
variable {V : Type} [Fintype V]

structure WeightedGraph (V : Type) [Fintype V] where
  edge : V → V → ℝ
  nonneg : ∀ u v, 0 ≤ edge u v
  symm : ∀ u v, edge u v = edge v u
  row_pos : ∀ u, 0 < ∑ v, edge u v

namespace WeightedGraph
open WithLp
local instance instDecidableEq : DecidableEq V := Classical.decEq _
variable (G : WeightedGraph V)
def mass (u : V) : ℝ := ∑ v, G.edge u v
def energy (f : V → ℝ) : ℝ := ∑ u, G.mass u * (f u)^2
def pairing (f g : V → ℝ) : ℝ := ∑ u, ∑ v, G.edge u v * f u * g v
def action (f : V → ℝ) (u : V) : ℝ := (∑ v, G.edge u v * f v) / G.mass u
def Connected : Prop := ∀ u v : V, Relation.ReflTransGen (fun u v => 0 < G.edge u v) u v

def coord (f : V → ℝ) : EuclideanSpace ℝ V := toLp 2 (fun u => Real.sqrt (G.mass u) * f u)
def uncoord (v : EuclideanSpace ℝ V) : V → ℝ := fun u => v u / Real.sqrt (G.mass u)
def matrix : Matrix V V ℝ := fun u v => G.edge u v / (Real.sqrt (G.mass u)*Real.sqrt (G.mass v))
def operator : EuclideanSpace ℝ V →ₗ[ℝ] EuclideanSpace ℝ V := G.matrix.toEuclideanLin

end WeightedGraph
end CoboundaryExpanders.Spectral

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Coboundary_Mixing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Small-set expansion, local spectral descent, connectedness, and uniform coset mixing.
-/

section
open scoped BigOperators
open scoped BigOperators Matrix
open scoped Matrix

namespace CoboundaryExpanders.EdgeMixing
variable {V : Type*} [Fintype V]
attribute [local instance] Classical.propDecidable

def volume (e : V → V → ℝ) : ℝ := ∑ x, mass e x
def selected (e : V → V → ℝ) (P : V → Prop) : ℝ := ∑ x, if P x then mass e x else 0
def chi (P : V → Prop) (x : V) : ℝ := if P x then 1 else 0

end CoboundaryExpanders.EdgeMixing

namespace CoboundaryExpanders.FatLadders
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

def linkEdge (w : Finset V → ℝ) (s : Finset V) (x y : V) : ℝ :=
  if x ∉ s ∧ y ∉ s ∧ x ≠ y then w (insert x (insert y s)) else 0

end CoboundaryExpanders.FatLadders

end

open scoped BigOperators
open scoped BigOperators Matrix
open scoped Matrix
open scoped BigOperators InnerProductSpace

namespace CoboundaryExpanders.EdgeMixing

section
variable {V W : Type} [Fintype V] [Fintype W]
attribute [local instance] Classical.propDecidable

def action (e : V → V → ℝ) (f : V → ℝ) (x : V) : ℝ := (∑ y,e x y*f y)/mass e x
abbrev Active (e : V → V → ℝ) := {x : V // 0 < mass e x}
def Connected (e : V → V → ℝ) : Prop :=
  ∀ x y : Active e, Relation.ReflTransGen (fun a b : Active e => 0 < e a.val b.val) x y

lemma edge_le_mass {e : V → V → ℝ} (he : ∀ x y,0 ≤ e x y) (x y : V) : e x y ≤ mass e x := by
  exact Finset.single_le_sum (fun z _ => he x z) (Finset.mem_univ y)
lemma edge_zero_of_nonactive {e : V → V → ℝ} (he : ∀ x y,0 ≤ e x y) {x : V}
    (hx : ¬0 < mass e x) (y : V) : e x y = 0 :=
  le_antisymm ((edge_le_mass he x y).trans (not_lt.mp hx)) (he x y)

def activeEmbedding (e : V → V → ℝ) (he : ∀ x y,0 ≤ e x y) :
    Embedding (fun x y : Active e => e x.val y.val) e where
  vertex := Subtype.val
  injective := Subtype.val_injective
  edge_eq := fun _ _ => rfl
  outside_zero := by
    intro x hx y
    exact edge_zero_of_nonactive he (fun h => hx ⟨⟨x,h⟩,rfl⟩) y

def activeGraph (e : V → V → ℝ) (he : ∀ x y,0 ≤ e x y)
    (hs : ∀ x y,e x y = e y x) : Spectral.WeightedGraph (Active e) where
  edge := fun x y => e x.val y.val
  nonneg := fun x y => he x.val y.val
  symm := fun x y => hs x.val y.val
  row_pos := by
    intro x
    have hm := (activeEmbedding e he).mass_map hs x
    change mass (fun x y : Active e => e x.val y.val) x > 0
    rw [←hm]
    exact x.property

end

end CoboundaryExpanders.EdgeMixing

namespace CoboundaryExpanders.FatLadders

section
variable {V : Type} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

def triangle (w : Finset V → ℝ) (s : Finset V) (x y z : V) : ℝ :=
  if x ∉ s then linkEdge w (insert x s) y z else 0
end

end CoboundaryExpanders.FatLadders

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Coboundary_Expansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Local repairs, fat-ladder inequalities, and uniform raw cosystolic expansion.
-/

noncomputable section
open scoped BigOperators
open scoped BigOperators Matrix
open scoped Matrix
open scoped BigOperators InnerProductSpace

namespace CoboundaryExpanders.FatLadders
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

def linkRestrict (s : Finset V) (g : Finset V → k) (a : Finset V) : k := g (s ∪ a)
def linkLift (s : Finset V) (b : Finset V → k) (t : Finset V) : k :=
  if s ⊆ t then b (t \ s) else 0

def linkNorm (w : Finset V → ℝ) (s : Finset V) (j : ℕ) (f : Finset V → k) : ℝ :=
  ∑ a ∈ level j, if Disjoint s a then atom (fun a => w (s ∪ a)) f a else 0

end CoboundaryExpanders.FatLadders

namespace CoboundaryExpanders.FatLadders
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

omit [Fintype V] in
@[simp] lemma delta_zero : delta (0 : Finset V → k) = 0 := by funext s; simp [delta]
omit [Fintype V] in
@[simp] lemma delta_add (f g : Finset V → k) : delta (f+g) = delta f + delta g := by
  funext s
  simp [delta,Finset.sum_add_distrib]

omit [DecidableEq V] in
@[simp] lemma norm_zero (w : Finset V → ℝ) (r) : norm w r 0 = 0 := by simp [norm,atom]

omit [DecidableEq V] in
lemma norm_add_le {w : Finset V → ℝ} (hw : ∀ s, 0 ≤ w s) (r) (f g : Finset V → k) :
    norm w r (f+g) ≤ norm w r f + norm w r g := by
  rw [norm,norm,norm,← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun s _ => atom_add_le hw f g s)

def WeightedEq (w : Finset V → ℝ) (r : ℕ) (f g : Finset V → k) : Prop :=
  ∀ s ∈ level r, w s ≠ 0 → f s = g s

end CoboundaryExpanders.FatLadders

namespace CoboundaryExpanders.LocalRepair

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

structure Size (A : Type*) [AddCommGroup A] where
  val : A → ℝ
  zero : val 0 = 0
  nonneg : ∀ a, 0 ≤ val a
  triangle : ∀ a b, val (a+b) ≤ val a + val b

instance instCoeFunSizeForallReal : CoeFun (Size A) (fun _ => A → ℝ) := ⟨Size.val⟩

end CoboundaryExpanders.LocalRepair

namespace CoboundaryExpanders.FatLadders

section
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

def normSize (w : Finset V → ℝ) (hw : ∀ s, 0 ≤ w s) (r : ℕ) :
    LocalRepair.Size (Finset V → k) where
  val := norm w r
  zero := norm_zero w r
  nonneg := norm_nonneg hw r
  triangle := norm_add_le hw r

def deltaHom : (Finset V → k) →+ (Finset V → k) where
  toFun := delta
  map_zero' := delta_zero
  map_add' := delta_add

end

end CoboundaryExpanders.FatLadders

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Coboundary_Frames
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Unimodular frames, bad-simplex transport, height reduction, and partial-basis exactness.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

namespace CoboundaryExpanders.Unimodular
open InfiniteChains InfiniteChains.Attachment
variable {R M V W : Type} [CommRing R] [AddCommGroup M] [Module R M]
variable [DecidableEq V] [DecidableEq W]

def disjSumEquiv (s : Finset V) (t : Finset W) : (s ⊕ t) ≃ s.disjSum t :=
  Equiv.ofBijective (Sum.elim (fun v => ⟨Sum.inl v.val, by simp⟩)
    (fun w => ⟨Sum.inr w.val, by simp⟩)) (by
      constructor
      · intro x y h
        cases x with
        | inl x => cases y with
          | inl y => exact congrArg Sum.inl (Subtype.ext (Sum.inl.inj (congrArg Subtype.val h)))
          | inr y =>
            have hh : Sum.inl x.val = Sum.inr y.val := congrArg (fun z : s.disjSum t => z.val) h
            cases hh
        | inr x => cases y with
          | inl y =>
            have hh : Sum.inr x.val = Sum.inl y.val := congrArg (fun z : s.disjSum t => z.val) h
            cases hh
          | inr y => exact congrArg Sum.inr (Subtype.ext (Sum.inr.inj (congrArg Subtype.val h)))
      · rintro ⟨x,hx⟩
        cases x with
        | inl x => exact ⟨Sum.inl ⟨x, by simpa using hx⟩, rfl⟩
        | inr x => exact ⟨Sum.inr ⟨x, by simpa using hx⟩, rfl⟩)

def insertEquiv (a : V) (s : Finset V) (ha : a ∉ s) : (Unit ⊕ s) ≃ ↥(insert a s) :=
  Equiv.ofBijective (Sum.elim (fun _ => ⟨a, Finset.mem_insert_self _ _⟩)
    (fun v => ⟨v.val, Finset.mem_insert_of_mem v.property⟩)) (by
      constructor
      · intro x y h
        cases x with
        | inl x => cases y with
          | inl y => congr
          | inr y =>
            have hh : a = y.val := congrArg (fun z : ↥(insert a s) => z.val) h
            exact (ha (hh ▸ y.property)).elim
        | inr x => cases y with
          | inl y =>
            have hh : x.val = a := congrArg (fun z : ↥(insert a s) => z.val) h
            exact (ha (hh ▸ x.property)).elim
          | inr y => exact congrArg Sum.inr (Subtype.ext (congrArg (fun z : ↥(insert a s) => z.val) h))
      · rintro ⟨x,hx⟩
        obtain rfl | hx := Finset.mem_insert.mp hx
        · exact ⟨Sum.inl (), rfl⟩
        · exact ⟨Sum.inr ⟨x,hx⟩,rfl⟩)

end CoboundaryExpanders.Unimodular

end

noncomputable section


namespace CoboundaryExpanders.InfiniteChains.HeightReduction
open Attachment
attribute [local instance] Classical.propDecidable Classical.decEq
variable {V : Type} [DecidableEq V]

abbrev Bad (h : V → ℕ) (H : ℕ) := {v // H ≤ h v}
abbrev Good (h : V → ℕ) (H : ℕ) := {v // ¬ H ≤ h v}

def split (h : V → ℕ) (H : ℕ) : Bad h H ⊕ Good h H ≃ V :=
  Equiv.sumCompl (fun v => H ≤ h v)

end CoboundaryExpanders.InfiniteChains.HeightReduction

end

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

namespace CoboundaryExpanders.Unimodular
open InfiniteChains InfiniteChains.Attachment
open InfiniteChains.HeightReduction

structure EuclideanHeight (R : Type) [CommRing R] where
  height : R → ℕ
  zero_iff : ∀ a, height a = 0 ↔ a = 0
  reduce : ∀ a b, b ≠ 0 → ∃ q, height (a-q*b) < height b

variable {R M V : Type} [CommRing R] [AddCommGroup M] [Module R M] [DecidableEq V]

abbrev standardCoordinate {S : Type} (i : S) : S → R :=
  @Pi.single S (fun _ => R) (fun _ => inferInstance) (Classical.decEq S) i 1

def fieldHeight (K : Type) [Field K] : EuclideanHeight K where
  height a := if a = 0 then 0 else 1
  zero_iff a := by by_cases h : a = 0 <;> simp [h]
  reduce a b hb := by
    refine ⟨a / b, ?_⟩
    simp [div_mul_cancel₀ a hb, hb]

def polynomialHeight (K : Type) [Field K] : EuclideanHeight (Polynomial K) where
  height a := if a = 0 then 0 else a.natDegree+1
  zero_iff a := by by_cases h : a = 0 <;> simp [h]
  reduce a b hb := by
    refine ⟨a / b, ?_⟩
    rw [mul_comm (a/b) b, ← EuclideanDomain.mod_eq_sub_mul_div]
    by_cases hz : a % b = 0
    · simp [hz, hb]
    · have hh := Polynomial.natDegree_lt_natDegree hz (Polynomial.degree_mod_lt a hb)
      simp only [hz, hb, ite_false]
      omega

end CoboundaryExpanders.Unimodular

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Congruence_Transfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Odd-index transfer, comparison of bar resolutions, and homology-coinvariant models.
-/

section
open CategoryTheory
open scoped BigOperators

namespace CoboundaryExpanders.Transfer

section
open Representation

variable {k G V W : Type*} [CommRing k] [Group G]
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

def inclusion (ρ : Representation k G V) (S : Subgroup G) :
    Coinvariants (ρ.comp S.subtype) →ₗ[k] ρ.Coinvariants :=
  Coinvariants.lift _ (Coinvariants.mk ρ) fun s => by
    ext v
    exact Coinvariants.mk_self_apply ρ s v

@[simp] theorem inclusion_mk (ρ : Representation k G V) (S : Subgroup G) (v : V) :
    inclusion ρ S (Coinvariants.mk (ρ.comp S.subtype) v) = Coinvariants.mk ρ v := rfl

variable (ρ : Representation k G V) (S : Subgroup G) [S.Normal] [Fintype (G ⧸ S)]

omit [Fintype (G ⧸ S)] in
@[simp] theorem quotient_action_mk (g : G) (v : V) :
    ρ.quotientToCoinvariants S (g : G ⧸ S) (Coinvariants.mk _ v) =
      Coinvariants.mk _ (ρ g v) := rfl

def normTransfer : ρ.Coinvariants →ₗ[k] Coinvariants (ρ.comp S.subtype) :=
  Coinvariants.lift _
    ((ρ.quotientToCoinvariants S).norm ∘ₗ Coinvariants.mk (ρ.comp S.subtype)) fun g => by
      ext v
      change (ρ.quotientToCoinvariants S).norm (Coinvariants.mk _ (ρ g v)) = _
      rw [← quotient_action_mk]
      exact Representation.norm_self_apply _ _ _

@[simp] theorem normTransfer_mk (v : V) :
    normTransfer ρ S (Coinvariants.mk ρ v) =
      ∑ q : G ⧸ S, ρ.quotientToCoinvariants S q (Coinvariants.mk _ v) := by
  simp [normTransfer, Representation.norm]

omit [Fintype (G ⧸ S)] in
@[simp] theorem inclusion_quotient_action (q : G ⧸ S)
    (v : Coinvariants (ρ.comp S.subtype)) :
    inclusion ρ S (ρ.quotientToCoinvariants S q v) = inclusion ρ S v := by
  induction q using QuotientGroup.induction_on with
  | H g =>
    induction v using Coinvariants.induction_on with
    | h v => simp

variable {ρ S}

omit [S.Normal] [Fintype (G ⧸ S)] in
theorem inclusion_natural {τ : Representation k G W} (φ : ρ.IntertwiningMap τ) :
    Coinvariants.map ρ τ φ ∘ₗ inclusion ρ S =
      inclusion τ S ∘ₗ Coinvariants.map (ρ.comp S.subtype) (τ.comp S.subtype)
        ⟨φ.toLinearMap, fun s => φ.isIntertwining' s⟩ := by
  apply Coinvariants.hom_ext
  ext v
  rfl

theorem normTransfer_natural {τ : Representation k G W} (φ : ρ.IntertwiningMap τ) :
    Coinvariants.map (ρ.comp S.subtype) (τ.comp S.subtype)
        ⟨φ.toLinearMap, fun s => φ.isIntertwining' s⟩ ∘ₗ normTransfer ρ S =
      normTransfer τ S ∘ₗ Coinvariants.map ρ τ φ := by
  apply Coinvariants.hom_ext
  ext v
  simp only [LinearMap.comp_apply, normTransfer_mk, map_sum, Coinvariants.map_mk]
  apply Finset.sum_congr rfl
  intro q _
  induction q using QuotientGroup.induction_on with
  | H g =>
    simp only [quotient_action_mk, Coinvariants.map_mk]
    exact congrArg (Coinvariants.mk _) (LinearMap.congr_fun (φ.isIntertwining' g) v)

end

universe u
variable {k G : Type u} [CommRing k] [Group G]
    (S : Subgroup G) [S.Normal] [Fintype (G ⧸ S)]

abbrev subgroupCoinvariantsFunctor : Rep k G ⥤ ModuleCat k :=
  Rep.resFunctor S.subtype ⋙ Rep.coinvariantsFunctor k S

def inclusionNatTrans : subgroupCoinvariantsFunctor (k := k) S ⟶
    Rep.coinvariantsFunctor k G where
  app A := ModuleCat.ofHom (inclusion A.ρ S)
  naturality {A B} φ := by
    apply ModuleCat.hom_ext
    exact (inclusion_natural (S := S) φ.hom).symm

def transferNatTrans : Rep.coinvariantsFunctor k G ⟶
    subgroupCoinvariantsFunctor (k := k) S where
  app A := ModuleCat.ofHom (normTransfer A.ρ S)
  naturality {A B} φ := by
    apply ModuleCat.hom_ext
    exact (normTransfer_natural (S := S) φ.hom).symm

abbrev subgroupChains (C : ChainComplex (Rep k G) ℕ) : ChainComplex (ModuleCat k) ℕ :=
  ((subgroupCoinvariantsFunctor (k := k) S).mapHomologicalComplex _).obj C

abbrev ambientChains (C : ChainComplex (Rep k G) ℕ) : ChainComplex (ModuleCat k) ℕ :=
  ((Rep.coinvariantsFunctor k G).mapHomologicalComplex _).obj C

def chainInclusion (C : ChainComplex (Rep k G) ℕ) :
    subgroupChains S C ⟶ ambientChains C :=
  ((inclusionNatTrans (k := k) S).mapHomologicalComplex _).app C

def chainTransfer (C : ChainComplex (Rep k G) ℕ) :
    ambientChains C ⟶ subgroupChains S C :=
  ((transferNatTrans (k := k) S).mapHomologicalComplex _).app C

end CoboundaryExpanders.Transfer

open CategoryTheory
open scoped BigOperators
open CategoryTheory Finsupp

end

open CategoryTheory
open scoped BigOperators
open CategoryTheory Finsupp
open CategoryTheory Finsupp MonoidalCategory

namespace CoboundaryExpanders.Transfer

section
open CategoryTheory Representation Finsupp
universe u
variable {k G : Type u} [CommRing k] [Group G] [DecidableEq G]
    (S : Subgroup G) [S.Normal] [Fintype (G ⧸ S)]

def trivialInclusion : Rep.trivial k S k ⟶ Rep.res S.subtype (Rep.trivial k G k) :=
  𝟙 (Rep.trivial k S k)

variable {H : Type u} [Group H]

def trivialCoefficients (f : H →* G) :
    Rep.trivial k H k ⟶ Rep.res f (Rep.trivial k G k) :=
  𝟙 (Rep.trivial k H k)

end

open Representation
universe u
variable {k G : Type u} [CommRing k] [Group G]
    (S : Subgroup G) [S.Normal] [Fintype (G ⧸ S)]

def quotientActionNatTrans (q : G ⧸ S) :
    subgroupCoinvariantsFunctor (k := k) S ⟶ subgroupCoinvariantsFunctor S where
  app A := ModuleCat.ofHom (A.ρ.quotientToCoinvariants S q)
  naturality {A B} φ := by
    apply ModuleCat.hom_ext
    apply Coinvariants.hom_ext
    ext v
    induction q using QuotientGroup.induction_on with
    | H g =>
      change Coinvariants.mk (B.ρ.comp S.subtype) (B.ρ g (φ.hom v)) =
        Coinvariants.mk (B.ρ.comp S.subtype) (φ.hom (A.ρ g v))
      exact congrArg (Coinvariants.mk _) (LinearMap.congr_fun (φ.hom.isIntertwining' g) v).symm

def chainQuotientAction (C : ChainComplex (Rep k G) ℕ) (q : G ⧸ S) :
    subgroupChains S C ⟶ subgroupChains S C :=
  ((quotientActionNatTrans (k := k) S q).mapHomologicalComplex _).app C

end CoboundaryExpanders.Transfer

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Congruence_Coinvariants
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Simplicial group actions, permutation modules, coset sums, and chain coinvariants.
-/

open CategoryTheory
open scoped BigOperators
open CategoryTheory Finsupp
open CategoryTheory Finsupp MonoidalCategory
open scoped BigOperators Matrix
open scoped Matrix
open scoped MonoidAlgebra

namespace CoboundaryExpanders.CosetModules

section
universe u
variable {k G : Type u} [Field k] [Group G]

def orbitVector (H : Subgroup G) (A : Rep k G) (x : A)
    (hx : ∀ h : H, A.ρ h x = x) : G ⧸ H → A :=
  Quotient.lift (fun g : G => A.ρ g x) (by
    intro a b hab
    have hh : a⁻¹ * b ∈ H := QuotientGroup.leftRel_apply.mp hab
    have he := hx ⟨a⁻¹ * b, hh⟩
    have hm := congrArg (A.ρ a) he
    simpa only [Subtype.coe_mk, ← Module.End.mul_apply, ← map_mul,
      mul_inv_cancel_left] using hm.symm)

@[simp] theorem orbitVector_mk (H : Subgroup G) (A : Rep k G) (x : A)
    (hx : ∀ h : H, A.ρ h x = x) (g : G) :
    orbitVector H A x hx (QuotientGroup.mk g) = A.ρ g x := rfl

theorem orbitVector_smul (H : Subgroup G) (A : Rep k G) (x : A)
    (hx : ∀ h : H, A.ρ h x = x) (g : G) (q : G ⧸ H) :
    orbitVector H A x hx (g • q) = A.ρ g (orbitVector H A x hx q) := by
  induction q using Quotient.inductionOn with | h a =>
    change A.ρ (g * a) x = A.ρ g (A.ρ a x)
    rw [map_mul, Module.End.mul_apply]

end

end CoboundaryExpanders.CosetModules

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Congruence_Resolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Partial resolutions, orbit projectivity, and homology of finite congruence coset complexes.
-/

noncomputable section
open CategoryTheory
open scoped BigOperators
open CategoryTheory Finsupp
open CategoryTheory Finsupp MonoidalCategory
open scoped BigOperators Matrix
open scoped Matrix
open scoped MonoidAlgebra
open CategoryTheory CategoryTheory.Limits

namespace CoboundaryExpanders.KernelCosetOrbits
variable {G Q : Type} [Group G] [Group Q] (f : G →* Q) (H : Subgroup G)

theorem stabilizer_eq_bot (hH : Set.InjOn f H) (a : G ⧸ H) :
    MulAction.stabilizer f.ker a = ⊥ := by
  apply le_antisymm _ bot_le
  intro k hk
  induction a using Quotient.inductionOn with | h a =>
    have hfix : QuotientGroup.mk (k.val*a) = (QuotientGroup.mk a : G ⧸ H) := hk
    have hmem : a⁻¹*k.val*a ∈ H := by
      have ht := QuotientGroup.leftRel_apply.mp (Quotient.exact hfix.symm)
      simpa [mul_assoc] using ht
    have he : f (a⁻¹*k.val*a) = f 1 := by
      simp only [map_mul, map_inv, show f k.val = 1 from k.property, map_one]
      simp
    have hx := hH hmem H.one_mem he
    have hk1 : k.val = 1 := by
      have hh := congrArg (fun z => a*z*a⁻¹) hx
      simpa [mul_assoc] using hh
    exact Subtype.ext hk1

end CoboundaryExpanders.KernelCosetOrbits

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Coboundary_Realization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Finite labeled coset complexes, purity, growth, incidence bounds, and weighted expansion reduction.
-/

noncomputable section
open CategoryTheory
open scoped BigOperators
open CategoryTheory Finsupp
open CategoryTheory Finsupp MonoidalCategory
open scoped BigOperators Matrix
open scoped Matrix
open scoped MonoidAlgebra
open CategoryTheory CategoryTheory.Limits
open Filter

namespace CoboundaryExpanders.CosetConstruction

section

variable {G : Type*} [Group G] [Fintype G] {n : ℕ}

noncomputable local instance subgroupFintype (K : Subgroup G) : Fintype K :=
  Fintype.ofFinite K

end

end CoboundaryExpanders.CosetConstruction

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Congruence_HomologyEdge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Abstract augmented resolutions and bounded homology edge surjectivity.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace CoboundaryExpanders.HomologyEdge

section
universe u
variable {k G : Type u} [CommRing k] [Group G]

abbrev Hmap {A B : Rep.{u} k G} (f : A ⟶ B) (n : ℕ) := (groupHomology.functor k G n).map f

namespace Bounded
structure BoundedPieces (N : ℕ) where
  K : ℕ → Rep.{u} k G
  C : ℕ → Rep.{u} k G
  inc : ∀ s, K (s+1) ⟶ C s
  sur : ∀ s, C s ⟶ K s
  zero : ∀ s, inc s ≫ sur s = 0
  exact : ∀ s, s ≤ N → (ShortComplex.mk (inc s) (sur s) (zero s)).ShortExact

variable {N : ℕ} (P : BoundedPieces (k := k) (G := G) N)

abbrev Hmap {A B : Rep.{u} k G} (f : A ⟶ B) (n : ℕ) := (groupHomology.functor k G n).map f

end Bounded
end

universe u
variable {k G : Type u} [CommRing k] [Group G]

structure AugmentedData where
  D : ℕ → Rep.{u} k G
  d : ∀ s, D (s+1) ⟶ D s
  square : ∀ s, d (s+1) ≫ d s = 0

namespace AugmentedData
variable (A : AugmentedData (k := k) (G := G))
def K : ℕ → Rep.{u} k G
  | 0 => A.D 0
  | s+1 => kernel (A.d s)
def inc (s : ℕ) : A.K (s+1) ⟶ A.D (s+1) := kernel.ι (A.d s)
instance inc_mono (s : ℕ) : Mono (A.inc s) := by
  change Mono (kernel.ι (A.d s))
  infer_instance
def sur : ∀ s, A.D (s+1) ⟶ A.K s
  | 0 => A.d 0
  | s+1 => kernel.lift (A.d s) (A.d (s+1)) (A.square s)
@[simp] lemma sur_inc (s : ℕ) : A.sur (s+1) ≫ A.inc s = A.d (s+1) := by
  exact kernel.lift_ι _ _ _
lemma zero (s : ℕ) : A.inc s ≫ A.sur s = 0 := by
  cases s with
  | zero => exact kernel.condition _
  | succ s =>
    rw [← cancel_mono (A.inc s), Category.assoc, sur_inc, zero_comp]
    exact kernel.condition _

lemma short_exact (s : ℕ) [Epi (A.sur s)] :
    (ShortComplex.mk (A.inc s) (A.sur s) (A.zero s)).ShortExact := by
  refine {exact := ?_, mono_f := inferInstance, epi_g := inferInstance}
  refine ShortComplex.exact_of_f_is_kernel
    (ShortComplex.mk (A.inc s) (A.sur s) (A.zero s)) ?_
  cases s with
  | zero => exact kernelIsKernel _
  | succ s =>
    apply KernelFork.IsLimit.ofι'
    intro W f hf
    have hfd : f ≫ A.d (s+1) = 0 := by
      rw [← A.sur_inc s, ← Category.assoc, hf, zero_comp]
    exact ⟨kernel.lift (A.d (s+1)) f hfd, kernel.lift_ι _ _ _⟩

def pieces (N : ℕ) (h0 : Epi (A.d 0))
    (he : ∀ s, s < N → (ShortComplex.mk (A.d (s+1)) (A.d s) (A.square s)).Exact) :
    Bounded.BoundedPieces (k := k) (G := G) N where
  K := A.K
  C s := A.D (s+1)
  inc := A.inc
  sur := A.sur
  zero := A.zero
  exact s hs := by
    have : Epi (A.sur s) := by
      cases s with
      | zero => exact h0
      | succ s => exact (he s (by omega)).epi_kernelLift
    exact A.short_exact s

end AugmentedData
end CoboundaryExpanders.HomologyEdge

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Congruence_OddHomology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Permutation orbit parameters, locally finite odd groups, quotient coinvariants, and bar augmentations.
-/


section
open scoped BigOperators

namespace CoboundaryExpanders.LocallyFiniteOdd
open Representation
variable {G V W : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup W] [Module (ZMod 2) W]

lemma coinvariant_relation_support (ρ : Representation (ZMod 2) G V)
    (x : V) (hx : x ∈ Coinvariants.ker ρ) :
    ∃ s : Finset G, ∀ S : Subgroup G, (∀ g ∈ s, g ∈ S) →
      x ∈ Coinvariants.ker (ρ.comp S.subtype) := by
  classical
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨g,v⟩,rfl⟩ := hx
    refine ⟨{g},fun S hS => ?_⟩
    exact Coinvariants.sub_mem_ker (ρ := ρ.comp S.subtype) ⟨g,hS g (by simp)⟩ v
  | zero => exact ⟨∅,fun _ _ => Submodule.zero_mem _⟩
  | add x y hx hy ex ey =>
    obtain ⟨s,hs⟩ := ex
    obtain ⟨t,ht⟩ := ey
    refine ⟨s ∪ t,fun S hS => (Coinvariants.ker _).add_mem ?_ ?_⟩
    · exact hs S (fun g hg => hS g (Finset.mem_union_left _ hg))
    · exact ht S (fun g hg => hS g (Finset.mem_union_right _ hg))
  | smul a x hx ex =>
    obtain ⟨s,hs⟩ := ex
    exact ⟨s,fun S hS => (Coinvariants.ker _).smul_mem a (hs S hS)⟩

lemma norm_zero_of_relation [Fintype G] (ρ : Representation (ZMod 2) G V)
    (x : V) (hx : x ∈ Coinvariants.ker ρ) : ρ.norm x = 0 := by
  have h : Coinvariants.ker ρ ≤ LinearMap.ker ρ.norm := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨g,v⟩,rfl⟩
    change ρ.norm (ρ g v - v) = 0
    rw [map_sub,Representation.norm_self_apply,sub_self]
  exact h hx

lemma coinvariant_norm_subgroup (ρ : Representation (ZMod 2) G V)
    (S : Subgroup G) [Fintype S] (hodd : Odd (Fintype.card S)) (v : V) :
    Coinvariants.mk ρ (Representation.norm (ρ.comp S.subtype) v) = Coinvariants.mk ρ v := by
  have hcard : (Fintype.card S : ZMod 2) = 1 := by
    obtain ⟨a,ha⟩ := hodd
    rw [ha]
    have ht : (2 : ZMod 2) = 0 := by decide
    simp [Nat.cast_add,Nat.cast_mul,ht]
  simp only [Representation.norm,LinearMap.sum_apply,map_sum]
  have he (s : S) : Coinvariants.mk ρ ((ρ.comp S.subtype) s v) = Coinvariants.mk ρ v :=
    Coinvariants.mk_self_apply ρ s.val v
  simp only [he,Finset.sum_const,Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul (R := ZMod 2),hcard,one_smul]

theorem coinvariants_map_injective
    (H : ∀ s : Finset G, ∃ S : Subgroup G, Finite S ∧ Odd (Nat.card S) ∧ ∀ g ∈ s, g ∈ S)
    (ρ : Representation (ZMod 2) G V) (τ : Representation (ZMod 2) G W)
    (f : ρ.IntertwiningMap τ) (hf : Function.Injective f) :
    Function.Injective (Coinvariants.map ρ τ f) := by
  classical
  have hz : ∀ c, Coinvariants.map ρ τ f c = 0 → c = 0 := by
    intro c
    induction c using Coinvariants.induction_on with
    | h v =>
      intro hv
      rw [Coinvariants.map_mk] at hv
      obtain ⟨s,hs⟩ := coinvariant_relation_support τ (f v) ((Coinvariants.mk_eq_zero τ).mp hv)
      obtain ⟨S,hfin,hodd,hS⟩ := H s
      have : Finite S := hfin
      let : Fintype S := Fintype.ofFinite S
      have hzero : Representation.norm (τ.comp S.subtype) (f v) = 0 :=
        norm_zero_of_relation _ _ (hs S hS)
      have hnorm : f (Representation.norm (ρ.comp S.subtype) v) = Representation.norm (τ.comp S.subtype) (f v) := by
        simp only [Representation.norm,LinearMap.sum_apply,map_sum]
        apply Finset.sum_congr rfl
        intro s _
        exact LinearMap.congr_fun (f.isIntertwining' s.val) v
      have hvan : Representation.norm (ρ.comp S.subtype) v = 0 := by
        apply hf
        rw [hnorm,hzero,map_zero]
      rw [← coinvariant_norm_subgroup ρ S (by simpa only [Fintype.card_eq_nat_card] using hodd) v,hvan,map_zero]
  intro a b hab
  apply sub_eq_zero.mp
  apply hz
  rw [map_sub,hab,sub_self]

end CoboundaryExpanders.LocallyFiniteOdd

open scoped BigOperators
open CategoryTheory CategoryTheory.Limits

end

section
open scoped BigOperators
open CategoryTheory CategoryTheory.Limits
open CategoryTheory CategoryTheory.Limits Representation

namespace CoboundaryExpanders.QuotientCoinvariants

section
variable {G : Type} [Group G] (N : Subgroup G) [N.Normal]

abbrev L := Rep.quotientToCoinvariantsFunctor (ZMod 2) N
abbrev R := Rep.resFunctor (QuotientGroup.mk' N) (k := ZMod 2)

noncomputable def homTo {X : Rep (ZMod 2) G} {Y : Rep (ZMod 2) (G ⧸ N)}
    (f : (L N).obj X ⟶ Y) : X ⟶ (R N).obj Y :=
  Rep.ofHom ⟨f.hom.toLinearMap ∘ₗ Coinvariants.mk (X.ρ.comp N.subtype), by
    intro g
    ext x
    exact LinearMap.congr_fun (f.hom.isIntertwining' (QuotientGroup.mk' N g))
      (Coinvariants.mk _ x)⟩

noncomputable def homFrom {X : Rep (ZMod 2) G} {Y : Rep (ZMod 2) (G ⧸ N)}
    (f : X ⟶ (R N).obj Y) : (L N).obj X ⟶ Y := by
  let h (s : N) : f.hom.toLinearMap ∘ₗ (X.ρ.comp N.subtype) s = f.hom.toLinearMap := by
    ext x
    have he := LinearMap.congr_fun (f.hom.isIntertwining' s.val) x
    have hs : QuotientGroup.mk' N s.val = 1 := by simp
    change f.hom.toLinearMap (X.ρ s.val x) = Y.ρ (QuotientGroup.mk' N s.val) (f.hom.toLinearMap x) at he
    change f.hom.toLinearMap (X.ρ s.val x) = f.hom.toLinearMap x
    rw [hs,map_one,Module.End.one_apply] at he
    exact he
  let m : Coinvariants (X.ρ.comp N.subtype) →ₗ[ZMod 2] Y :=
    Coinvariants.lift _ f.hom.toLinearMap h
  refine Rep.ofHom ⟨m,fun g => ?_⟩
  refine QuotientGroup.induction_on g (fun g => ?_)
  apply Coinvariants.hom_ext
  ext x
  exact LinearMap.congr_fun (f.hom.isIntertwining' g) x

noncomputable def homEquiv (X : Rep (ZMod 2) G) (Y : Rep (ZMod 2) (G ⧸ N)) :
    ((L N).obj X ⟶ Y) ≃ (X ⟶ (R N).obj Y) where
  toFun := homTo N
  invFun := homFrom N
  left_inv f := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply Coinvariants.hom_ext
    rfl
  right_inv f := by
    ext x
    rfl

noncomputable def adjunction : L N ⊣ R N :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv N
      homEquiv_naturality_left_symm := by
        intro X' X Y f g
        apply Rep.hom_ext
        apply Representation.IntertwiningMap.ext
        apply Coinvariants.hom_ext
        rfl
      homEquiv_naturality_right := by
        intro X Y Y' f g
        ext x
        rfl }

instance instAdditiveRepZModOfNatNatQuotientSubgroupL : (L N).Additive where
  map_add := by
    intro X Y f g
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply Coinvariants.hom_ext
    rfl

instance instIsLeftAdjointRepZModOfNatNatQuotientSubgroupL : (L N).IsLeftAdjoint := (adjunction N).isLeftAdjoint

instance instPreservesProjectiveObjectsRepZModOfNatNatQuotientSubgroupL : (L N).PreservesProjectiveObjects :=
  Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms (adjunction N)

end

section
variable {G : Type} [Group G] (N : Subgroup G) [N.Normal]
variable (H : ∀ s : Finset N, ∃ S : Subgroup N, Finite S ∧ Odd (Nat.card S) ∧ ∀ g ∈ s, g ∈ S)

include H

theorem preservesMonomorphisms : (L N).PreservesMonomorphisms where
  preserves f hf := by
    apply (Rep.mono_iff_injective _).mpr
    exact LocallyFiniteOdd.coinvariants_map_injective H _ _
      ((Rep.resFunctor N.subtype).map f).hom ((Rep.mono_iff_injective f).mp hf)

theorem preservesHomology : (L N).PreservesHomology := by
  let := preservesMonomorphisms N H
  exact Functor.preservesHomology_of_preservesMonos_and_cokernels _

noncomputable def descendedResolution {X : Rep.{0} (ZMod 2) G}
    (P : ProjectiveResolution X) : ProjectiveResolution ((L N).obj X) := by
  letI := preservesHomology N H
  exact (L N).mapProjectiveResolution P

end

variable {G : Type} [Group G] (N : Subgroup G) [N.Normal]

noncomputable def inflatedTrivialIso :
    Rep.trivialFunctor (ZMod 2) (G ⧸ N) ⋙ R N ≅ Rep.trivialFunctor (ZMod 2) G :=
  NatIso.ofComponents (fun X => Iso.refl _) (by intro X Y f; rfl)

noncomputable def totalAdjunction :
    L N ⋙ Rep.coinvariantsFunctor (ZMod 2) (G ⧸ N) ⊣ Rep.trivialFunctor (ZMod 2) G :=
  ((adjunction N).comp (Rep.coinvariantsAdjunction (ZMod 2) (G ⧸ N))).ofNatIsoRight
    (inflatedTrivialIso N)

noncomputable def totalCoinvariantsIso :
    L N ⋙ Rep.coinvariantsFunctor (ZMod 2) (G ⧸ N) ≅ Rep.coinvariantsFunctor (ZMod 2) G :=
  Adjunction.leftAdjointUniq (totalAdjunction N) (Rep.coinvariantsAdjunction (ZMod 2) G)

noncomputable def trivialIso :
    (L N).obj (Rep.trivial (ZMod 2) G (ZMod 2)) ≅ Rep.trivial (ZMod 2) (G ⧸ N) (ZMod 2) where
  hom := homFrom N (𝟙 _)
  inv := Rep.ofHom ⟨Coinvariants.mk ((Rep.trivial (ZMod 2) G (ZMod 2)).ρ.comp N.subtype), by
    intro g
    refine QuotientGroup.induction_on g (fun g => ?_)
    rfl⟩
  hom_inv_id := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply Coinvariants.hom_ext
    rfl
  inv_hom_id := by
    ext
    rfl

end CoboundaryExpanders.QuotientCoinvariants

open scoped BigOperators
open CategoryTheory CategoryTheory.Limits
open CategoryTheory CategoryTheory.Limits Representation
open CategoryTheory CategoryTheory.Limits Representation MonoidalCategory

namespace CoboundaryExpanders.QuotientCoinvariants
variable {G : Type} [Group G] (N : Subgroup G) [N.Normal]
variable (H : ∀ s : Finset N, ∃ S : Subgroup N, Finite S ∧ Odd (Nat.card S) ∧ ∀ g ∈ s, g ∈ S)

noncomputable def quotientResolution [DecidableEq G] :
    ProjectiveResolution (Rep.trivial (ZMod 2) (G ⧸ N) (ZMod 2)) where
  complex := (descendedResolution N H (Rep.barResolution (ZMod 2) G)).complex
  projective := (descendedResolution N H (Rep.barResolution (ZMod 2) G)).projective
  π := (descendedResolution N H (Rep.barResolution (ZMod 2) G)).π ≫
    (ChainComplex.single₀ _).map (trivialIso N).hom

end CoboundaryExpanders.QuotientCoinvariants

end

section
open scoped BigOperators
open CategoryTheory CategoryTheory.Limits
open CategoryTheory CategoryTheory.Limits Representation
open CategoryTheory CategoryTheory.Limits Representation MonoidalCategory
open CategoryTheory CategoryTheory.Limits Representation Finsupp

namespace CoboundaryExpanders.QuotientCoinvariants
variable {G : Type} [Group G] [DecidableEq G] (N : Subgroup G) [N.Normal]

noncomputable def quotientBarF (n : ℕ) :
    (Rep.barComplex (ZMod 2) G).X n ⟶
      (R N).obj ((Rep.barComplex (ZMod 2) (G ⧸ N)).X n) :=
  Rep.freeLift (ZMod 2) G _ (fun x : Fin n → G =>
    Finsupp.single (fun i => QuotientGroup.mk' N (x i)) (.single (1 : G ⧸ N) (1 : ZMod 2)))

omit [DecidableEq G] in
@[simp] theorem quotientBarF_single (n : ℕ) (x : Fin n → G) (g : G) (r : ZMod 2) :
    (quotientBarF N n).hom (Finsupp.single x (.single g r)) =
      Finsupp.single (fun i => QuotientGroup.mk' N (x i)) (.single (QuotientGroup.mk' N g) r) := by
  change (Representation.freeLift
    ((Representation.free (ZMod 2) (G ⧸ N) (Fin n → G ⧸ N)).comp (QuotientGroup.mk' N))
    (fun x : Fin n → G => Finsupp.single (fun i => QuotientGroup.mk' N (x i))
      (.single (1 : G ⧸ N) (1 : ZMod 2))))
    (Finsupp.single x (.single g r)) = _
  rw [Representation.freeLift_single_single]
  change r • Representation.free (ZMod 2) (G ⧸ N) (Fin n → G ⧸ N) (QuotientGroup.mk' N g) _ = _
  rw [Representation.free_single_single]
  simp

noncomputable def quotientBar [DecidableEq (G ⧸ N)] :
    ((L N).mapHomologicalComplex _).obj (Rep.barComplex (ZMod 2) G) ⟶
      Rep.barComplex (ZMod 2) (G ⧸ N) where
  f n := homFrom N (quotientBarF N n)
  comm' i j hij := by
    cases hij
    apply (homEquiv N _ _).injective
    apply Rep.free_ext
    intro x
    change ((Rep.barComplex (ZMod 2) (G ⧸ N)).d (j + 1) j).hom
      ((quotientBarF N (j + 1)).hom (Finsupp.single x (.single 1 1))) =
      (quotientBarF N j).hom
      (((Rep.barComplex (ZMod 2) G).d (j + 1) j).hom (Finsupp.single x (.single 1 1)))
    rw [Rep.barComplex.d_def,Rep.barComplex.d_def,quotientBarF_single]
    simp only [map_one]
    rw [Rep.barComplex.d_single,Rep.barComplex.d_single]
    have hq : ∀ (n : ℕ) (x : Fin n → G) (g : G) (r : ZMod 2),
        (quotientBarF N n).hom (Finsupp.single x (.single g r)) =
          Finsupp.single (fun i => QuotientGroup.mk' N (x i)) (.single (QuotientGroup.mk' N g) r) :=
      quotientBarF_single N
    simp only [map_add,map_sum,hq]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    congr 2
    exact (Fin.comp_contractNth (· * ·) (· * ·) (fun a b : G => (map_mul (QuotientGroup.mk' N) a b).symm) i x).symm

end CoboundaryExpanders.QuotientCoinvariants

open scoped BigOperators
open CategoryTheory CategoryTheory.Limits
open CategoryTheory CategoryTheory.Limits Representation
open CategoryTheory CategoryTheory.Limits Representation MonoidalCategory
open CategoryTheory CategoryTheory.Limits Representation Finsupp
open CategoryTheory CategoryTheory.Limits Representation Finsupp Rep TensorProduct

end

section
open scoped BigOperators
open CategoryTheory CategoryTheory.Limits
open CategoryTheory CategoryTheory.Limits Representation
open CategoryTheory CategoryTheory.Limits Representation MonoidalCategory
open CategoryTheory CategoryTheory.Limits Representation Finsupp
open CategoryTheory CategoryTheory.Limits Representation Finsupp Rep TensorProduct
open CategoryTheory Finsupp MonoidalCategory

namespace CoboundaryExpanders.QuotientCoinvariantModel
universe u
variable {k G : Type u} [CommRing k] [Group G] [DecidableEq G]

abbrev complex : ChainComplex (ModuleCat k) ℕ :=
  ((Rep.coinvariantsFunctor k G).mapHomologicalComplex _).obj (Rep.barComplex k G)

def chainsIso : groupHomology.inhomogeneousChains (Rep.trivial k G k) ≅
    complex (k := k) (G := G) :=
  groupHomology.inhomogeneousChainsIso (Rep.trivial k G k) ≪≫
    (NatIso.mapHomologicalComplex
      (Functor.isoWhiskerRight (leftUnitorNatIso (Rep k G)) (Rep.coinvariantsFunctor k G)) _).app
        (Rep.barComplex k G)

@[simp] theorem chainsIso_hom_single (n : ℕ) (x : Fin n → G) (r : k) :
    (chainsIso (k := k) (G := G)).hom.f n (single x r) =
      Representation.Coinvariants.mk (Representation.free k G (Fin n → G))
        (single x (.single (1 : G) r)) := by
  change (Rep.coinvariantsFunctor k G).map (λ_ (Rep.free k G (Fin n → G))).hom
    (Rep.finsuppToCoinvariantsTensorFree (Rep.trivial k G k) (Fin n → G)
      (single x r)) = _
  rw [Rep.finsuppToCoinvariantsTensorFree_single]
  simp

end CoboundaryExpanders.QuotientCoinvariantModel

namespace CoboundaryExpanders.QuotientCoinvariants
open Representation
variable {G : Type} [Group G] [DecidableEq G] (N : Subgroup G) [N.Normal] [DecidableEq (G ⧸ N)]

noncomputable def coinvariantQuotient :
    QuotientCoinvariantModel.complex (k := ZMod 2) (G := G) ⟶
      QuotientCoinvariantModel.complex (k := ZMod 2) (G := G ⧸ N) :=
  ((NatIso.mapHomologicalComplex (totalCoinvariantsIso N) _).app (Rep.barComplex (ZMod 2) G)).inv ≫
    ((Rep.coinvariantsFunctor (ZMod 2) (G ⧸ N)).mapHomologicalComplex _).map (quotientBar N)

noncomputable def trivialQuotient : Rep.trivial (ZMod 2) G (ZMod 2) ⟶
    Rep.res (QuotientGroup.mk' N) (Rep.trivial (ZMod 2) (G ⧸ N) (ZMod 2)) := 𝟙 _

end CoboundaryExpanders.QuotientCoinvariants

end

open scoped BigOperators
open CategoryTheory CategoryTheory.Limits
open CategoryTheory CategoryTheory.Limits Representation
open CategoryTheory CategoryTheory.Limits Representation MonoidalCategory
open CategoryTheory CategoryTheory.Limits Representation Finsupp
open CategoryTheory CategoryTheory.Limits Representation Finsupp Rep TensorProduct
open CategoryTheory Finsupp MonoidalCategory
open CategoryTheory

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Congruence_Parabolic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Actual parabolic stabilizers, F2 homological stability maps, and matrix duality.
-/


section
open CategoryTheory
open scoped Matrix

namespace CoboundaryExpanders.MatrixDual
variable {A B : Type*} [CommRing A] [CommRing B]
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
local notation "SL" => Matrix.SpecialLinearGroup

@[simp] lemma transpose_mul (x y : SL ι A) :
    (x * y).transpose = y.transpose * x.transpose := by
  apply Subtype.ext
  exact Matrix.transpose_mul _ _

@[simp] lemma transpose_one : (1 : SL ι A).transpose = 1 := by
  apply Subtype.ext
  exact Matrix.transpose_one

@[simp] lemma transpose_transpose (x : SL ι A) : x.transpose.transpose = x := by
  rfl

@[simp] lemma transpose_inv (x : SL ι A) : (x⁻¹).transpose = x.transpose⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  rw [← transpose_mul, inv_mul_cancel, transpose_one]

def dual : MulAut (SL ι A) where
  toFun x := (x⁻¹).transpose
  invFun x := (x⁻¹).transpose
  left_inv x := by simp
  right_inv x := by simp
  map_mul' x y := by simp

@[simp] lemma dual_apply (x : SL ι A) : dual x = (x⁻¹).transpose := rfl

@[simp] lemma dual_dual (x : SL ι A) : dual (dual x) = x := by simp

lemma map_transpose (f : A →+* B) (x : SL ι A) :
    Matrix.SpecialLinearGroup.map f x.transpose = (Matrix.SpecialLinearGroup.map f x).transpose := rfl

lemma map_dual (f : A →+* B) (x : SL ι A) :
    Matrix.SpecialLinearGroup.map f (dual x) = dual (Matrix.SpecialLinearGroup.map f x) := by
  simp only [dual_apply, map_transpose, map_inv]

end CoboundaryExpanders.MatrixDual

end

open CategoryTheory

end

end OAI
end

section
-- module Solutions.OAIQ3_Cob.Congruence_ProStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Positive exactness, coefficient change, Bockstein groups, integral pro-stability support, and F2 reductions.
-/

noncomputable section
open CategoryTheory
open scoped BigOperators
open CategoryTheory Finsupp
open CategoryTheory Finsupp MonoidalCategory
open scoped BigOperators Matrix
open scoped Matrix
open scoped MonoidAlgebra
open CategoryTheory CategoryTheory.Limits
open Filter

namespace CoboundaryExpanders.ProCoefficientChange

structure Tower where
  V : ℕ → Type
  ab : ∀ m, AddCommGroup (V m)
  mod : ∀ m, Module ℤ (V m)
  trans : ∀ m n, m ≤ n → V n →ₗ[ℤ] V m
  trans_self : ∀ m h, trans m m h = LinearMap.id
  trans_comp : ∀ m n r hmn hnr, (trans m n hmn).comp (trans n r hnr) = trans m r (hmn.trans hnr)
attribute [instance] Tower.ab Tower.mod

end CoboundaryExpanders.ProCoefficientChange

namespace CoboundaryExpanders.GroupProStability
open ProCoefficientChange
attribute [local instance 2000] Rep.hV2
attribute [local instance 3000] ModuleCat.isModule

structure Groups where
  G : ℕ → Type
  grp : ∀ m, Group (G m)
  trans : ∀ m n, m ≤ n → G n →* G m
  trans_self : ∀ m h, trans m m h = MonoidHom.id _
  trans_comp : ∀ m n r hmn hnr, (trans m n hmn).comp (trans n r hnr) = trans m r (hmn.trans hnr)
attribute [instance] Groups.grp

end CoboundaryExpanders.GroupProStability

end

end OAI
end


