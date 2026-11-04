-- Prove2me | Definitions.Def_OAISignedSweepsProofDefs
-- name    : OAISignedSweepsProofDefs
-- status  : Definition
-- author  : @wurtle
-- created : 2026-11-03T23:34:24.07584+00:00
-- url     : https://prove2.me/theorems/338dfcdf-2b1d-485c-a1eb-00df3478f463
-- title:
--   Coefficients, signed word spaces, type projections and mark budgets for signed sweep moments
-- statement:
--   This block collects the definitions used in the statements of the intermediate results of the signed sweep moment induction for the Thorp shuffle. It extends the definitions of `SignedSweepMoment`.
--
--   1. **Coefficients.** For a finite group $G$ and $f:G\to\mathbb{C}$, $\pi(f)=\sum_gf(g)\pi(g)$ is the action of $f$ in a representation $\pi$ (`coefficientAction`). Convolution, involution, powers, list products, the pushforward along a homomorphism, products over blocks and the normalized average of a subgroup are `coefficientProduct`, `coefficientStar`, `coefficientPower`, `coefficientListProduct`, `coefficientPush`, `productCoefficient`, `subgroupAverageCoefficient`. The representation `finiteRegularRepresentation` is the regular one on $\ell^2(G)$.
--
--   2. **Words.** `WordSpace p C` is $\ell^2(C^p)$, with $S_p$ permuting positions (`wordRepresentation`). On words over $C\sqcup C$, `signedWordRepresentation` multiplies this action by the sign of the permutation induced between the odd positions (`wordPhase`, via `equivSign`).
--
--   3. **Type projections.** `wordTypeProjection` is the orthogonal projection onto the $S^\mu$-isotypic subspace (`isotypicSubrepresentation`). `pairTypeProjection` sums, over placements of the even sites (`EvenAllocation`), the tensor product of two such projections, transported by `pairWordEmbedding` and `hilbertBlock`. A `PairType p` is a pair of partitions of total size $p$, with projection `projector`, entropy `entropy` and height `height`. `blockTypeProjection` and `blockEntropy` extend these to blocks through an enumeration of sites (`groupedWordOperator`).
--
--   4. **Marks and budgets.** `MarkedAssignment l n` is an injection of $l$ marks into $n$ sites, `markedInjection` enumerates the unmarked sites, and `markedBoardPlacement` transports marks to a rectangle (`HolePlacement`). With $h$ marks in a line of size $t$, `clippedBudget` is $\max\{0,\tau h\log t-h\log(t/h)\}$; `holeBudget` and `holePrefactor` are the sum of these budgets and the product of inverse falling factorials over rows and columns. `holeClippingError` is $ms^{1-\kappa}\log s+sm^{1-\kappa}\log m$. The error terms are `localTraceError` and `typedLineError`.
--
--   5. **Sweeps on a rectangle.** `sweepBoard` identifies $2^{a+b}$ positions with a $2^a\times2^b$ rectangle through the binary coordinates, and `columnEnumeration`, `rowEnumeration`, `blockPermutation` give its lines. `sweepCoefficient` is the group-algebra element of a sweep, with powers of its positive squares `sweepPowerCoefficient`, `columnPowerCoefficient`, `rowPowerCoefficient`.
--
--   These are the objects of Sections 2-4 of the source, in its representation-theoretic normalization.
--
--   **Formalization Note** The declarations are reproduced verbatim from the upstream modules, together with the short lemmas their bodies need (for instance, that `wordPhase` is multiplicative). Module comments mark their upstream origin. One anonymous local instance is given an explicit name so importing files can reactivate it.
-- source:
--   OpenAI, "Signed tensor densities and diagram budgets for the Thorp shuffle" (September 26, 2026), openai/math preprints/Signed-tensor-densities-and-diagram-budgets-for-coordinate-sweeps-September-26-2026/paper.pdf, Sections 2-4. Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SignedSweeps/ (openai/math, Apache-2.0)

-- Carved from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a (Apache-2.0),
-- lean/OAI/Probability/SignedSweeps/, ported to Lean 4.33.1 / Mathlib 0df444a.
-- Declarations are verbatim upstream; the mathematics and the Lean code are OpenAI's.

import Mathlib
import Definitions.Def_SignedSweepMoment

section
-- module OAI.Probability.SignedSweeps.HoleEntropy
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module

def occupancy {l q : ℕ} (f : Fin l → Fin q) (j : Fin q) : Fin (l + 1) :=
  ⟨(Finset.univ.filter (fun i => f i = j)).card,
    Nat.lt_succ_iff.mpr ((Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
      (Fintype.card_fin l))⟩

abbrev HolePlacement (s m l : ℕ) :=
  {z : Fin l → Fin s × Fin m // Function.Injective z}

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.BudgetBounds
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module

def clippedBudget (τ : ℝ) (a h : ℕ) : ℝ :=
  max 0 (τ * h * Real.log a - (h : ℝ) * Real.log ((a : ℝ) / h))

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.FallingFactorials
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module

def holePrefactor {s m l : ℕ} (z : HolePlacement s m l) : ℝ :=
  (∏ j : Fin m, (s.descFactorial (occupancy (fun i => (z.1 i).2) j).val : ℝ)⁻¹) *
    ∏ j : Fin s, (m.descFactorial (occupancy (fun i => (z.1 i).1) j).val : ℝ)⁻¹

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.HoleCount
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module

def holeBudget {s m l : ℕ} (τ : ℝ) (z : Fin l → Fin s × Fin m) : ℝ :=
  (∑ j : Fin m, clippedBudget τ s (occupancy (fun i => (z i).2) j).val) +
    ∑ j : Fin s, clippedBudget τ m (occupancy (fun i => (z i).1) j).val

def holeClippingError (κ : ℝ) (s m : ℕ) : ℝ :=
  (m : ℝ) * (s : ℝ) ^ (1 - κ) * Real.log s +
    (s : ℝ) * (m : ℝ) ^ (1 - κ) * Real.log m

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.ProvedRanges
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators Classical ComplexOrder
variable {G : Type*} [Fintype G] [Group G]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

def finiteRegularRepresentation : Representation ℂ G (EuclideanSpace ℂ G) where
  toFun g := (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Equiv.mulLeft g)).toLinearEquiv.toLinearMap
  map_one' := by ext f h; change f (1⁻¹ * h) = f h; simp
  map_mul' := by
    intro g h; ext f k
    change f ((g * h)⁻¹ * k) = f (h⁻¹ * (g⁻¹ * k))
    simp [mul_assoc]

def coefficientAction (ρ : Representation ℂ G E) (f : G → ℂ) : E →ₗ[ℂ] E :=
  ∑ g, f g • ρ g

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.TensorCommutant
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

def wordPositionEquiv {p : ℕ} {C : Type*} (g : SymmetricGroup p) :
    Equiv.Perm (Fin p → C) where
  toFun w := w ∘ g.symm
  invFun w := w ∘ g
  left_inv w := by ext i; simp
  right_inv w := by ext i; simp

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.Isotypic
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module
variable {G E F : Type*} [Monoid G] [AddCommGroup E] [Module ℂ E]
  [AddCommGroup F] [Module ℂ F]

def isotypicSubrepresentation (ρ : Representation ℂ G E) (σ : Representation ℂ G F) :
    Subrepresentation σ where
  toSubmodule := ⨆ f : Representation.IntertwiningMap ρ σ, f.toLinearMap.range
  apply_mem_toSubmodule g x hx := by
    refine Submodule.iSup_induction (motive := fun x => σ g x ∈
      ⨆ f : Representation.IntertwiningMap ρ σ, f.toLinearMap.range)
      (fun f : Representation.IntertwiningMap ρ σ => f.toLinearMap.range) hx ?_ ?_ ?_
    · intro f y hy
      obtain ⟨v, rfl⟩ := hy
      exact (le_iSup (fun f : Representation.IntertwiningMap ρ σ => f.toLinearMap.range) f)
        ⟨ρ g v, Representation.IntertwiningMap.isIntertwining ρ σ f g v⟩
    · simp
    · intro x y hx hy
      simpa only [map_add] using Submodule.add_mem _ hx hy

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module
variable {G E F : Type*} [Group G] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F]
variable (ρ : Representation ℂ G E) (σ : Representation ℂ G F)
  (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖) (hσ : ∀ g x, ‖σ g x‖ = ‖x‖)

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.WordIsotypic
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

abbrev WordSpace (p : ℕ) (C : Type*) := EuclideanSpace ℂ (Fin p → C)

def wordIsometry {p : ℕ} {C : Type*} [Fintype C] (g : SymmetricGroup p) :
    WordSpace p C ≃ₗᵢ[ℂ] WordSpace p C :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (wordPositionEquiv g)

def wordRepresentation (p : ℕ) (C : Type*) [Fintype C] :
    Representation ℂ (SymmetricGroup p) (WordSpace p C) where
  toFun g := (wordIsometry (C := C) g).toLinearEquiv.toLinearMap
  map_one' := by
    ext f w
    change f (w ∘ (1 : SymmetricGroup p)) = f w
    rfl
  map_mul' := by
    intro g h
    ext f w
    change f (w ∘ (g * h : SymmetricGroup p)) = f ((w ∘ g) ∘ h)
    rfl

abbrev wordMatrixEquiv (p : ℕ) (C : Type*) [Fintype C] :=
  LinearMap.toMatrixOrthonormal (EuclideanSpace.basisFun (Fin p → C) ℂ)

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.WordEmbedding
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module
variable {I J : Type*} [Fintype I] [Fintype J]

def euclideanEmbeddingLinear (e : I ↪ J) : EuclideanSpace ℂ I →ₗ[ℂ] EuclideanSpace ℂ J where
  toFun v := ∑ i, v i • EuclideanSpace.single (e i) 1
  map_add' v w := by simp only [PiLp.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c v := by simp only [PiLp.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply]

omit [Fintype J] in
lemma euclideanEmbeddingLinear_apply (e : I ↪ J) (v : EuclideanSpace ℂ I) (j : J) :
    euclideanEmbeddingLinear e v j = ∑ i, if e i = j then v i else 0 := by
  simp only [euclideanEmbeddingLinear, LinearMap.coe_mk, AddHom.coe_mk,
    WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, PiLp.single_apply, smul_eq_mul]
  change (∑ i, v i * (if j = e i then 1 else 0)) = _
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : e i = j
  · simp only [h, ite_true, mul_one]
  · rw [if_neg h, if_neg (Ne.symm h), mul_zero]

omit [Fintype J] in
lemma euclideanEmbeddingLinear_at (e : I ↪ J) (v : EuclideanSpace ℂ I) (i : I) :
    euclideanEmbeddingLinear e v (e i) = v i := by
  rw [euclideanEmbeddingLinear_apply]
  simp only [e.injective.eq_iff, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

lemma euclideanEmbeddingLinear_inner (e : I ↪ J) (v w : EuclideanSpace ℂ I) :
    inner ℂ (euclideanEmbeddingLinear e v) (euclideanEmbeddingLinear e w) = inner ℂ v w := by
  change inner ℂ (∑ i, v i • EuclideanSpace.single (e i) 1) (euclideanEmbeddingLinear e w) = _
  rw [sum_inner]
  simp only [inner_smul_left, EuclideanSpace.inner_single_left, map_one, one_mul,
    euclideanEmbeddingLinear_at]
  simp only [PiLp.inner_apply, RCLike.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

def euclideanEmbedding (e : I ↪ J) : EuclideanSpace ℂ I →ₗᵢ[ℂ] EuclideanSpace ℂ J :=
  (euclideanEmbeddingLinear e).isometryOfInner (euclideanEmbeddingLinear_inner e)

def euclideanTensorEquiv :
    (EuclideanSpace ℂ I ⊗[ℂ] EuclideanSpace ℂ J) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (I × J) :=
  ((EuclideanSpace.basisFun I ℂ).tensorProduct (EuclideanSpace.basisFun J ℂ)).repr

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

def pairColorWord {u v p : ℕ} {C : Type*} (e : (Fin u ⊕ Fin v) ≃ Fin p)
    (w : (Fin u → C) × (Fin v → C)) : Fin p → C ⊕ C :=
  Sum.elim (fun i => Sum.inl (w.1 i)) (fun j => Sum.inr (w.2 j)) ∘ e.symm

def pairColorEmbedding {u v p : ℕ} {C : Type*} (e : (Fin u ⊕ Fin v) ≃ Fin p) :
    ((Fin u → C) × (Fin v → C)) ↪ (Fin p → C ⊕ C) where
  toFun := pairColorWord e
  inj' := by
    intro x y he
    apply Prod.ext
    · funext i
      have hi := congrFun he (e (Sum.inl i))
      simpa only [pairColorWord, Function.comp_apply, Equiv.symm_apply_apply,
        Sum.elim_inl, Sum.inl.injEq] using hi
    · funext j
      have hj := congrFun he (e (Sum.inr j))
      simpa only [pairColorWord, Function.comp_apply, Equiv.symm_apply_apply,
        Sum.elim_inr, Sum.inr.injEq] using hj

def pairWordEmbedding {u v p : ℕ} {C : Type*} [Fintype C]
    (e : (Fin u ⊕ Fin v) ≃ Fin p) :
    (WordSpace u C ⊗[ℂ] WordSpace v C) →ₗᵢ[ℂ] WordSpace p (C ⊕ C) :=
  (euclideanEmbedding (pairColorEmbedding e)).comp euclideanTensorEquiv.toLinearIsometry

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.HilbertBlocks
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F]

def hilbertBlock (j : E →ₗᵢ[ℂ] F) : (E →ₗ[ℂ] E) →ₗ[ℂ] (F →ₗ[ℂ] F) where
  toFun A := j.toLinearMap ∘ₗ A ∘ₗ j.toLinearMap.adjoint
  map_add' A B := by ext x; simp
  map_smul' c A := by ext x; simp

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module
variable {I J : Type*} [Fintype I] [Fintype J]

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.WordAllocations
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

abbrev EvenAllocation (u p : ℕ) := {S : Finset (Fin p) // S.card = u}

lemma allocation_complement_card {u v p : ℕ} (h : u + v = p) (S : EvenAllocation u p) :
    Fintype.card {i : Fin p // i ∉ S.1} = v := by
  have ht := Fintype.card_subtype_compl (fun i : Fin p => i ∈ S.1)
  have he : Fintype.card {i : Fin p // i ∈ S.1} = u := by simpa using S.2
  rw [he, Fintype.card_fin] at ht
  omega

def allocationEquiv {u v p : ℕ} (h : u + v = p) (S : EvenAllocation u p) :
    (Fin u ⊕ Fin v) ≃ Fin p :=
  (Equiv.sumCongr (Finset.equivFinOfCardEq S.2).symm
    (Fintype.equivFinOfCardEq (allocation_complement_card h S)).symm).trans
      (Equiv.sumCompl (fun i : Fin p => i ∈ S.1))

def wordEvenSites {p : ℕ} {C : Type*} (w : Fin p → C ⊕ C) : Finset (Fin p) :=
  Finset.univ.filter (fun i => ∃ c, w i = Sum.inl c)

@[simp] lemma mem_wordEvenSites {p : ℕ} {C : Type*} (w : Fin p → C ⊕ C) (i : Fin p) :
    i ∈ wordEvenSites w ↔ ∃ c, w i = Sum.inl c := by simp [wordEvenSites]

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.PairWordTypes
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

def wordTypeProjection {p : ℕ} (μ : Partition p) (C : Type*) [Fintype C] :
    WordSpace p C →ₗ[ℂ] WordSpace p C :=
  (isotypicSubrepresentation (spechtRepresentation μ)
    (wordRepresentation p C)).toSubmodule.starProjection.toLinearMap

def pairTypeProjection {u v p : ℕ} (h : u + v = p)
    (α : Partition u) (β : Partition v) (C : Type*) [Fintype C] :
    WordSpace p (C ⊕ C) →ₗ[ℂ] WordSpace p (C ⊕ C) :=
  ∑ S : EvenAllocation u p, hilbertBlock (pairWordEmbedding (C := C) (allocationEquiv h S))
    (TensorProduct.map (wordTypeProjection α C) (wordTypeProjection β C))

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.EquivSign
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical

def enumeratedPermutation {A B : Type*} [Fintype A] [Fintype B] (e : A ≃ B) :
    Equiv.Perm (Fin (Fintype.card A)) :=
  (Fintype.equivFin A).symm.trans (e.trans ((Fintype.equivFin B).trans
    (finCongr (Fintype.card_congr e)).symm))

def equivSign {A B : Type*} [Fintype A] [Fintype B] (e : A ≃ B) : ℤˣ :=
  Equiv.Perm.sign (enumeratedPermutation e)

lemma enumeratedPermutation_refl {A : Type*} [Fintype A] :
    enumeratedPermutation (Equiv.refl A) = 1 := by
  ext i
  simp [enumeratedPermutation]

lemma enumeratedPermutation_trans {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (e : A ≃ B) (f : B ≃ C) :
    enumeratedPermutation (e.trans f) =
      (finCongr (Fintype.card_congr e)).symm.permCongr (enumeratedPermutation f) *
        enumeratedPermutation e := by
  ext i
  simp [enumeratedPermutation, Equiv.permCongr_apply]

@[simp] lemma equivSign_refl {A : Type*} [Fintype A] :
    equivSign (Equiv.refl A) = 1 := by
  rw [equivSign, enumeratedPermutation_refl, map_one]

lemma equivSign_trans {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (e : A ≃ B) (f : B ≃ C) :
    equivSign (e.trans f) = equivSign f * equivSign e := by
  simp only [equivSign, enumeratedPermutation_trans, map_mul, Equiv.Perm.sign_permCongr]

def complexEquivSign {A B : Type*} [Fintype A] [Fintype B] (e : A ≃ B) : ℂ :=
  ((equivSign e : ℤ) : ℂ)

@[simp] lemma complexEquivSign_refl {A : Type*} [Fintype A] :
    complexEquivSign (Equiv.refl A) = 1 := by simp [complexEquivSign]

lemma complexEquivSign_trans {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (e : A ≃ B) (f : B ≃ C) :
    complexEquivSign (e.trans f) = complexEquivSign f * complexEquivSign e := by
  simp [complexEquivSign, equivSign_trans]

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.SignedWords
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
open Module

lemma wordEvenSites_comp_mem {p : ℕ} {C : Type*} (g : SymmetricGroup p)
    (w : Fin p → C ⊕ C) (i : Fin p) :
    i ∈ wordEvenSites (w ∘ g) ↔ g i ∈ wordEvenSites w := by
  simp only [mem_wordEvenSites, Function.comp_apply]

def oddPositionSetEquiv {p : ℕ} (g : SymmetricGroup p)
    (S T : Finset (Fin p)) (h : ∀ i, i ∈ T ↔ g i ∈ S) :
    {i : Fin p // i ∉ T} ≃ {i : Fin p // i ∉ S} where
  toFun i := ⟨g i, fun hi => i.2 ((h i).mpr hi)⟩
  invFun i := ⟨g.symm i, by simpa only [h, Equiv.apply_symm_apply] using i.2⟩
  left_inv i := by apply Subtype.ext; exact g.symm_apply_apply i
  right_inv i := by apply Subtype.ext; exact g.apply_symm_apply i

def oddPositionEquiv {p : ℕ} {C : Type*} (g : SymmetricGroup p)
    (w : Fin p → C ⊕ C) :
    {i : Fin p // i ∉ wordEvenSites (w ∘ g)} ≃ {i : Fin p // i ∉ wordEvenSites w} :=
  oddPositionSetEquiv g (wordEvenSites w) (wordEvenSites (w ∘ g))
    (wordEvenSites_comp_mem g w)

lemma oddPositionEquiv_one {p : ℕ} {C : Type*} (w : Fin p → C ⊕ C) :
    oddPositionEquiv 1 w = Equiv.refl {i : Fin p // i ∉ wordEvenSites w} := by
  apply Equiv.ext
  intro i
  rfl

lemma oddPositionEquiv_mul {p : ℕ} {C : Type*} (g h : SymmetricGroup p)
    (w : Fin p → C ⊕ C) :
    oddPositionEquiv (g*h) w = (oddPositionEquiv h (w ∘ g)).trans (oddPositionEquiv g w) := by
  apply Equiv.ext
  intro i
  rfl

def wordPhase {p : ℕ} {C : Type*} (g : SymmetricGroup p) (w : Fin p → C ⊕ C) : ℂ :=
  complexEquivSign (oddPositionEquiv g w)

@[simp] lemma wordPhase_one {p : ℕ} {C : Type*} (w : Fin p → C ⊕ C) :
    wordPhase 1 w = 1 := by
  exact (congrArg (fun e => complexEquivSign e) (oddPositionEquiv_one w)).trans
    (complexEquivSign_refl)

lemma wordPhase_mul {p : ℕ} {C : Type*} (g h : SymmetricGroup p) (w : Fin p → C ⊕ C) :
    wordPhase (g*h) w = wordPhase g w * wordPhase h (w ∘ g) := by
  exact (congrArg (fun e => complexEquivSign e) (oddPositionEquiv_mul g h w)).trans
    (complexEquivSign_trans _ _)

def signedWordLinear {p : ℕ} {C : Type*} [Fintype C] (g : SymmetricGroup p) :
    WordSpace p (C ⊕ C) →ₗ[ℂ] WordSpace p (C ⊕ C) where
  toFun f := WithLp.toLp 2 (fun w => wordPhase g w * f (w ∘ g))
  map_add' f h := by ext w; exact mul_add _ _ _
  map_smul' c f := by ext w; exact mul_left_comm _ _ _

@[simp] lemma signedWordLinear_apply {p : ℕ} {C : Type*} [Fintype C]
    (g : SymmetricGroup p) (f : WordSpace p (C ⊕ C)) (w : Fin p → C ⊕ C) :
    signedWordLinear g f w = wordPhase g w * f (w ∘ g) := rfl

def signedWordRepresentation (p : ℕ) (C : Type*) [Fintype C] :
    Representation ℂ (SymmetricGroup p) (WordSpace p (C ⊕ C)) where
  toFun := signedWordLinear
  map_one' := by ext f w; simp only [signedWordLinear_apply, wordPhase_one, one_mul]; rfl
  map_mul' g h := by
    ext f w
    simp only [signedWordLinear_apply, Module.End.mul_apply, wordPhase_mul]
    exact mul_assoc _ _ _

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.PairDecomposition
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

abbrev PairType (p : ℕ) := Σ u : Fin (p+1), Partition u.1 × Partition (p-u.1)

end SignedSweeps
end

noncomputable section
namespace SignedSweeps.PairType
open scoped BigOperators TensorProduct Classical
open Module

def projector {p : ℕ} (t : PairType p) (C : Type*) [Fintype C] :
    WordSpace p (C ⊕ C) →ₗ[ℂ] WordSpace p (C ⊕ C) :=
  pairTypeProjection (Nat.add_sub_of_le (Nat.le_of_lt_succ t.1.2)) t.2.1 t.2.2 C

def entropy {p : ℕ} (t : PairType p) : ℝ := signedEntropy t.2.1 t.2.2

def height {p : ℕ} (t : PairType p) : ℕ := max (t.2.1.1.colLen 0) (t.2.2.1.colLen 0)

end SignedSweeps.PairType
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.MarkedSites
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

abbrev MarkedAssignment (l n : ℕ) := Fin l ↪ Fin n

abbrev MarkedComplement {l n : ℕ} (z : MarkedAssignment l n) :=
  {x : Fin n // x ∉ Set.range z}

lemma markedComplement_card {p l n : ℕ} (h : p+l=n) (z : MarkedAssignment l n) :
    Fintype.card (MarkedComplement z) = p := by
  rw [Fintype.card_subtype_compl (fun x => x ∈ Set.range z)]
  have hr : Fintype.card (Set.range z) = l := by
    simpa using Fintype.card_congr (Equiv.ofInjective z z.injective).symm
  rw [hr, Fintype.card_fin]
  omega

def markedSites {p l n : ℕ} (h : p+l=n) (z : MarkedAssignment l n) :
    Fin p ≃ MarkedComplement z :=
  (Fintype.equivFinOfCardEq (markedComplement_card h z)).symm

def markedInjection {p l n : ℕ} (h : p+l=n) (z : MarkedAssignment l n) :
    Fin p ↪ Fin n := (markedSites h z).toEmbedding.trans (Function.Embedding.subtype _)

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.CoefficientAlgebra
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators ComplexOrder Classical
open Module
variable {G : Type*} [Group G] [Fintype G]

def coefficientProduct (f k : G → ℂ) (g : G) : ℂ := ∑ h : G, f h * k (h⁻¹ * g)

def coefficientStar (f : G → ℂ) (g : G) : ℂ := star (f g⁻¹)

def coefficientOne (g : G) : ℂ := if g = 1 then 1 else 0

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators ComplexOrder Classical
open Module
variable {G : Type*} [Group G] [Fintype G]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.BlockPermutations
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
variable {J : Type*} [Fintype J] {A : J → Type*} [∀ j, Fintype (A j)]

def sigmaPermutation : (∀ j, Equiv.Perm (A j)) →* Equiv.Perm (Σ j, A j) where
  toFun := Equiv.Perm.sigmaCongrRight
  map_one' := by apply Equiv.ext; intro x; cases x; rfl
  map_mul' g h := by apply Equiv.ext; intro x; cases x; rfl

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
variable {J : Type*} [Fintype J] {p : ℕ} {k : J → ℕ}

def blockPermutation (e : (Σ j, Fin (k j)) ≃ Fin p) :
    (∀ j, SymmetricGroup (k j)) →* SymmetricGroup p :=
  e.permCongrHom.toMonoidHom.comp sigmaPermutation

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.PiTensorMatrix
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct ComplexOrder Classical
open Module
variable {J : Type*} [Fintype J] {I : J → Type*} [∀ j, Fintype (I j)]

def piTensorMatrix (A : ∀ j, Matrix (I j) (I j) ℂ) :
    Matrix (∀ j, I j) (∀ j, I j) ℂ := fun w z => ∏ j, A j (w j) (z j)

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.WordGrouping
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct ComplexOrder Classical

variable {J C : Type*} [Fintype J] [Fintype C] {p : ℕ} {k : J → ℕ}

def groupWordEquiv (e : (Σ j, Fin (k j)) ≃ Fin p) :
    (Fin p → C) ≃ (∀ j, Fin (k j) → C) where
  toFun w j i := w (e ⟨j,i⟩)
  invFun w i := w (e.symm i).1 (e.symm i).2
  left_inv w := by
    funext i
    change w (e (e.symm i)) = w i
    rw [Equiv.apply_symm_apply]
  right_inv w := by
    funext j i
    change (fun x : Σ j, Fin (k j) => w x.1 x.2) (e.symm (e ⟨j,i⟩)) = w j i
    rw [Equiv.symm_apply_apply]

def groupedWordMatrix (e : (Σ j, Fin (k j)) ≃ Fin p)
    (A : ∀ j, Matrix (Fin (k j) → C) (Fin (k j) → C) ℂ) :
    Matrix (Fin p → C) (Fin p → C) ℂ :=
  (piTensorMatrix A).submatrix (groupWordEquiv e) (groupWordEquiv e)

def groupedWordOperator (e : (Σ j, Fin (k j)) ≃ Fin p)
    (A : ∀ j, WordSpace (k j) C →ₗ[ℂ] WordSpace (k j) C) :
    WordSpace p C →ₗ[ℂ] WordSpace p C :=
  (wordMatrixEquiv p C).symm (groupedWordMatrix e (fun j => wordMatrixEquiv (k j) C (A j)))

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.CoefficientPush
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
variable {G H : Type*} [Group G] [Fintype G] [Group H] [Fintype H]

def coefficientPush (φ : G →* H) (f : G → ℂ) (h : H) : ℂ :=
  ∑ g, if φ g = h then f g else 0

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
variable {G H : Type*} [Group G] [Fintype G] [Group H] [Fintype H]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
variable {J : Type*} [Fintype J] {G : J → Type*}
  [∀ j, Group (G j)] [∀ j, Fintype (G j)]

def productCoefficient (f : ∀ j, G j → ℂ) (g : ∀ j, G j) : ℂ := ∏ j, f j (g j)

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
variable {G : Type*} [Group G] [Fintype G]

def coefficientPower (f : G → ℂ) : ℕ → G → ℂ
  | 0 => coefficientOne
  | r+1 => coefficientProduct (coefficientPower f r) f

def coefficientListProduct : List (G → ℂ) → G → ℂ
  | [] => coefficientOne
  | f::fs => coefficientProduct f (coefficientListProduct fs)

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
variable {G : Type*} [Group G] [Fintype G]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.CoefficientUniform
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
variable {G H K : Type*} [Group G] [Fintype G] [Group H] [Fintype H]
  [Group K] [Fintype K]

def subgroupAverageCoefficient (S : Subgroup G) : G → ℂ :=
  coefficientPush S.subtype (fun _ => (Fintype.card S : ℂ)⁻¹)

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
variable {G H K : Type*} [Group G] [Fintype G] [Group H] [Fintype H]
  [Group K] [Fintype K]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
variable {J : Type*} [Fintype J] {G H : J → Type*}
  [∀ j, Group (G j)] [∀ j, Fintype (G j)] [∀ j, Group (H j)] [∀ j, Fintype (H j)]

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.ProvedRanges4
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators Classical

def splitBinary (a b : ℕ) : BinaryPositions (a + b) ≃ BinaryPositions a × BinaryPositions b where
  toFun := fun x => (fun i => x (i.castAdd b), fun j => x (j.natAdd a))
  invFun := fun x => Fin.append x.1 x.2
  left_inv x := Fin.append_castAdd_natAdd
  right_inv x := by
    apply Prod.ext <;> funext i <;> simp

def sweepBoard (a b : ℕ) : Fin (2 ^ (a + b)) ≃ Fin (2 ^ a) × Fin (2 ^ b) :=
  (positionsEquiv (a+b)).symm.trans ((splitBinary a b).trans
    (Equiv.prodCongr (positionsEquiv a) (positionsEquiv b)))

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators Classical
variable {K E : Type*} [CommSemiring K] [AddCommMonoid E] [Module K E]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators Classical
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators Classical

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators ComplexOrder Classical
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators ComplexOrder Classical
variable {I R : Type*} [Fintype I] [LinearOrder I] [Semiring R]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators ComplexOrder Classical
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators ComplexOrder Classical

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.SweepBlockLayers
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical

def columnEnumeration (a b : ℕ) : (Σ _ : Fin (2^b), Fin (2^a)) ≃ Fin (2^(a+b)) :=
  (Equiv.sigmaEquivProd (Fin (2^b)) (Fin (2^a))).trans
    ((Equiv.prodComm _ _).trans (sweepBoard a b).symm)

def rowEnumeration (a b : ℕ) : (Σ _ : Fin (2^a), Fin (2^b)) ≃ Fin (2^(a+b)) :=
  (Equiv.sigmaEquivProd (Fin (2^a)) (Fin (2^b))).trans (sweepBoard a b).symm

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.OccupiedCounts
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical

def markedBoardPlacement {l n s m : ℕ} (e : Fin n ≃ Fin s × Fin m) :
    MarkedAssignment l n ≃ HolePlacement s m l where
  toFun z := ⟨fun i => e (z i), e.injective.comp z.injective⟩
  invFun z := ⟨fun i => e.symm (z.1 i), e.symm.injective.comp z.2⟩
  left_inv z := by ext i; simp
  right_inv z := by apply Subtype.ext; funext i; simp

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.LocalTraceBudget
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical

def localTraceError (t q B : ℕ) : ℝ :=
  (2*(Nat.sqrt t : ℝ)+26*(q:ℝ)^2+8*q+1)*Real.log B+8*q+1

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.GroupedTypes
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical

variable {J C : Type*} [Fintype J] [Fintype C] {p : ℕ} {k : J → ℕ}

def blockTypeProjection (e : (Σ j, Fin (k j)) ≃ Fin p) (t : ∀ j, PairType (k j)) :
    WordSpace p (C ⊕ C) →ₗ[ℂ] WordSpace p (C ⊕ C) :=
  groupedWordOperator e (fun j => (t j).projector C)

def blockEntropy (t : ∀ j, PairType (k j)) : ℝ := ∑ j, (t j).entropy

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.BlockTraceBudget
namespace OAI

noncomputable section
namespace SignedSweeps.PairType
open scoped BigOperators Classical

lemma size_eq {p : ℕ} (t : PairType p) : t.1.1+(p-t.1.1)=p :=
  Nat.add_sub_of_le (Nat.le_of_lt_succ t.1.2)

lemma extended_size_eq {p n : ℕ} (t : PairType p) (hpn : p ≤ n) :
    t.1.1+(p-t.1.1)+(n-p)=n := by rw [t.size_eq, Nat.add_sub_of_le hpn]

end SignedSweeps.PairType
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
variable {J : Type*} [Fintype J] {p t q B : ℕ} {k : J → ℕ}

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.OccupiedTrace
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical

def typedLineError (t q R : ℕ) : ℝ :=
  localTraceError t q R + (4*(Nat.sqrt t : ℝ)+1)*Real.log R + 2*(q:ℝ)^2*Real.log R

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.SweepCoefficients
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical

variable {G H : Type*} [Group G] [Fintype G] [Group H] [Fintype H]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical
local instance (priority := 2000) instDecidableEqFin_oAI_1 (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

def sweepCoefficient (d : ℕ) : SymmetricGroup (2^d) → ℂ :=
  coefficientListProduct ((List.ofFn (fun i : Fin d =>
    subgroupAverageCoefficient (coordinateSubgroup d i))).reverse)

def sweepPowerCoefficient (d r : ℕ) (left : Bool) : SymmetricGroup (2^d) → ℂ :=
  coefficientPower (if left then
    coefficientProduct (sweepCoefficient d) (coefficientStar (sweepCoefficient d))
    else coefficientProduct (coefficientStar (sweepCoefficient d)) (sweepCoefficient d)) r

def columnPowerCoefficient (a b r : ℕ) : SymmetricGroup (2^(a+b)) → ℂ :=
  coefficientPush (blockPermutation (columnEnumeration a b))
    (productCoefficient (fun _ => sweepPowerCoefficient a r true))

def rowPowerCoefficient (a b r : ℕ) : SymmetricGroup (2^(a+b)) → ℂ :=
  coefficientPush (blockPermutation (rowEnumeration a b))
    (productCoefficient (fun _ => sweepPowerCoefficient b r false))

end SignedSweeps
end

end OAI
end


