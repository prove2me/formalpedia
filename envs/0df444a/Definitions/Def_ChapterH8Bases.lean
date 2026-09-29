-- Prove2me | Definitions.Def_ChapterH8Bases
-- name    : ChapterH8Bases
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-09T23:02:40.869581+00:00
-- url     : https://prove2.me/theorems/a6c08dd8-fa2a-4cbb-95cf-5cf6b84a9458
-- title:
--   `BookProof/ChapterH8.lean` proves that the Hashimoto SIRK approximation orders nest, for an abstract pair of isometric e ...
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.H8Bases`, source chapter `BookProof/ChapterH8Bases.lean`).
--
--   `BookProof/ChapterH8.lean` proves that the Hashimoto SIRK approximation orders nest, for an abstract pair of isometric embeddings `Vₘ = Vₙ ∘ J`. This companion module shows those hypotheses are **not vacuous**: they are met by any pair of nested orthonormal families, and in particular by the orthonormal Krylov bases the SIRK method actually builds.
--
--   * `orthonormalEmbedding` / `orthonormalEmbeddingLI` — the isometric embedding `EuclideanSpace ℂ (Fin m) →L[ℂ] E` of an orthonormal family, with `orthonormalEmbedding_single`, `orthonormalEmbedding_inner`, `orthonormalEmbedding_adjoint_comp` (`V∗V = 1`) and `orthonormalEmbedding_range` (its range is the span of the family); * `coordIncl` — the coordinate inclusion along `Fin.castLE`, with `coordIncl_single` and `coordIncl_adjoint_comp` (`J∗J = 1`); * `orthonormalEmbedding_nested` — the factorization `Vₘ = Vₙ ∘ J` for nested families, hence the hypothesis-free instances `sirk_band_refinement_of_orthonormal` and `sirk_compression_submatrix_of_orthonormal`; * `krylovOrthonormalSeq` — Gram–Schmidt applied to `k ↦ Hᵏ v`; its prefixes are orthonormal (`krylovOrthonormal_orthonormal`), nested by construction (`krylovOrthonormal_nested`) and span the Krylov subspaces (`krylovOrthonormal_span`). `krylovEmbedding` packages the prefix as an isometry with `krylovEmbedding_range = krylovSpan H v n`, and `sirk_band_refinement_krylov` is the refinement theorem for the Krylov flag itself.
--
--   Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`).
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterH8Bases.lean

import Definitions.Def_ChapterH8
import Mathlib

import Mathlib

/-!
# Chapter H8b — the SIRK nesting hypotheses are realized by Krylov bases

`BookProof/ChapterH8.lean` proves that the Hashimoto SIRK approximation orders
nest, for an abstract pair of isometric embeddings `Vₘ = Vₙ ∘ J`.  This companion
module shows those hypotheses are **not vacuous**: they are met by any pair of
nested orthonormal families, and in particular by the orthonormal Krylov bases the
SIRK method actually builds.

## Deliverables

* `orthonormalEmbedding` / `orthonormalEmbeddingLI` — the isometric embedding
  `EuclideanSpace ℂ (Fin m) →L[ℂ] E` of an orthonormal family, with
  `orthonormalEmbedding_single`, `orthonormalEmbedding_inner`,
  `orthonormalEmbedding_adjoint_comp` (`V∗V = 1`) and `orthonormalEmbedding_range`
  (its range is the span of the family);
* `coordIncl` — the coordinate inclusion along `Fin.castLE`, with
  `coordIncl_single` and `coordIncl_adjoint_comp` (`J∗J = 1`);
* `orthonormalEmbedding_nested` — the factorization `Vₘ = Vₙ ∘ J` for nested
  families, hence the hypothesis-free instances
  `sirk_band_refinement_of_orthonormal` and
  `sirk_compression_submatrix_of_orthonormal`;
* `krylovOrthonormalSeq` — Gram–Schmidt applied to `k ↦ Hᵏ v`; its prefixes are
  orthonormal (`krylovOrthonormal_orthonormal`), nested by construction
  (`krylovOrthonormal_nested`) and span the Krylov subspaces
  (`krylovOrthonormal_span`).  `krylovEmbedding` packages the prefix as an
  isometry with `krylovEmbedding_range = krylovSpan H v n`, and
  `sirk_band_refinement_krylov` is the refinement theorem for the Krylov flag
  itself.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

noncomputable section

namespace BookProof.ChapterH8

open BookProof.ChapterH4 BookProof.ChapterH5 BookProof.ChapterH6

/-! ## Part 1 — the nesting hypotheses are realized by nested orthonormal bases

The refinement theorems of `ChapterH8` are stated for an abstract pair of
isometric embeddings `Vₘ = Vₙ ∘ J`.  This part shows that the hypotheses are not
vacuous: they are met by *any* pair of nested orthonormal families. -/

section Realization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

open ContinuousLinearMap

/-- The linear isometry `EuclideanSpace ℂ (Fin m) → E` sending the `i`-th
coordinate vector to `w i`, for an orthonormal family `w`. -/
def orthonormalEmbeddingLI {m : ℕ} (w : Fin m → E) (hw : Orthonormal ℂ w) :
    EuclideanSpace ℂ (Fin m) →ₗᵢ[ℂ] E :=
  LinearMap.isometryOfOrthonormal (((EuclideanSpace.basisFun (Fin m) ℂ).toBasis.constr ℂ) w)
    (v := (EuclideanSpace.basisFun (Fin m) ℂ).toBasis)
    (by simp)
    (by
      have h : ((((EuclideanSpace.basisFun (Fin m) ℂ).toBasis.constr ℂ) w) ∘
          (EuclideanSpace.basisFun (Fin m) ℂ).toBasis) = w := by
        funext i
        simp
      rw [h]
      exact hw)

/-- The Krylov-style embedding `V : EuclideanSpace ℂ (Fin m) →L[ℂ] E` attached to an
orthonormal family `w` (for SIRK: an orthonormal basis of the order-`m` Krylov
subspace). -/
def orthonormalEmbedding {m : ℕ} (w : Fin m → E) (hw : Orthonormal ℂ w) :
    EuclideanSpace ℂ (Fin m) →L[ℂ] E :=
  (orthonormalEmbeddingLI w hw).toContinuousLinearMap







/-- The coordinate inclusion `J : EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin n)`
along `Fin.castLE`, for `m ≤ n`: the concrete `J` of the refinement theorems. -/
def coordIncl {m n : ℕ} (hmn : m ≤ n) :
    EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
  orthonormalEmbedding (fun i => EuclideanSpace.single (Fin.castLE hmn i) (1 : ℂ))
    (by
      have h2 := (EuclideanSpace.basisFun (Fin n) ℂ).orthonormal.comp
        (Fin.castLE hmn) (Fin.castLE_injective hmn)
      have h3 : (⇑(EuclideanSpace.basisFun (Fin n) ℂ) ∘ Fin.castLE hmn)
          = fun i => EuclideanSpace.single (Fin.castLE hmn i) (1 : ℂ) := by
        funext i
        simp [EuclideanSpace.basisFun_apply]
      rw [h3] at h2
      exact h2)













end Realization

/-! ## Part 2 — the nested orthonormal Krylov bases exist

Gram–Schmidt applied to the Krylov sequence `k ↦ Hᵏ v`, indexed by `ℕ`, produces a
*single* orthonormal sequence whose prefixes are orthonormal bases of the Krylov
subspaces.  Nesting is then automatic — the order-`m` basis is literally the first
`m` members of the order-`n` one — so the realization of Part 1 applies to the
Krylov flag itself. -/

section KrylovBases

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

open ContinuousLinearMap InnerProductSpace



omit [CompleteSpace E] in
/-- Linear independence of a prefix also gives linear independence of every
initial segment `Set.Iic i`, in the form Gram–Schmidt asks for. -/
theorem li_Iic_of_li_Fin {f : ℕ → E} {n : ℕ} (hli : LinearIndependent ℂ (fun i : Fin n => f i))
    {i : ℕ} (hi : i < n) :
    LinearIndependent ℂ (f ∘ (Subtype.val : Set.Iic i → ℕ)) := by
  have he : Function.Injective (fun j : Set.Iic i => (⟨j.1, lt_of_le_of_lt j.2 hi⟩ : Fin n)) := by
    intro a b hab
    apply Subtype.ext
    simpa [Fin.ext_iff] using hab
  exact hli.comp _ he

omit [CompleteSpace E] in
/-- **Prefix orthonormality.**  If the first `n` members of an `ℕ`-indexed family
are linearly independent, the first `n` normalized Gram–Schmidt vectors are
orthonormal — no global linear independence is needed. -/
theorem gramSchmidtNormed_orthonormal_prefix {f : ℕ → E} {n : ℕ}
    (hli : LinearIndependent ℂ (fun i : Fin n => f i)) :
    Orthonormal ℂ (fun i : Fin n => gramSchmidtNormed ℂ f (i : ℕ)) := by
  constructor
  · intro i
    exact gramSchmidtNormed_unit_length_coe (i : ℕ) (li_Iic_of_li_Fin hli i.2)
  · intro i j hij
    have hne : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
    have h := gramSchmidt_orthogonal ℂ f hne
    simp only [gramSchmidtNormed]
    rw [inner_smul_left, inner_smul_right, h]
    simp

/-- The orthonormal Krylov sequence: Gram–Schmidt applied to `k ↦ Hᵏ v`.  Its
prefixes are the nested orthonormal Krylov bases used by the SIRK method. -/
def krylovOrthonormalSeq (H : E →ₗ[ℂ] E) (v : E) : ℕ → E :=
  gramSchmidtNormed ℂ (fun k : ℕ => (H ^ k) v)



omit [CompleteSpace E] in
/-- **The order-`n` Krylov basis is orthonormal** as soon as the Krylov sequence
has not broken down before order `n`. -/
theorem krylovOrthonormal_orthonormal (H : E →ₗ[ℂ] E) (v : E) {n : ℕ}
    (hli : LinearIndependent ℂ (fun i : Fin n => (H ^ (i : ℕ)) v)) :
    Orthonormal ℂ (fun i : Fin n => krylovOrthonormalSeq H v (i : ℕ)) :=
  gramSchmidtNormed_orthonormal_prefix hli





/-- The order-`n` **Krylov embedding** `Vₙ : EuclideanSpace ℂ (Fin n) →L[ℂ] E`: the
isometry sending coordinate vectors to the orthonormal Krylov basis. -/
def krylovEmbedding (H : E →ₗ[ℂ] E) (v : E) {n : ℕ}
    (hli : LinearIndependent ℂ (fun i : Fin n => (H ^ (i : ℕ)) v)) :
    EuclideanSpace ℂ (Fin n) →L[ℂ] E :=
  orthonormalEmbedding (fun i : Fin n => krylovOrthonormalSeq H v (i : ℕ))
    (krylovOrthonormal_orthonormal H v hli)





end KrylovBases

end BookProof.ChapterH8

end


