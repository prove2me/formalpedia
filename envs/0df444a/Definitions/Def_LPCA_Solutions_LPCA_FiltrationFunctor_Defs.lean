-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_FiltrationFunctor_Defs
-- name    : LPCA_Solutions_LPCA_FiltrationFunctor_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-21T21:20:20.444535+00:00
-- url     : https://prove2.me/theorems/a26ae30e-7693-4222-9f8e-7c72b97043ef
-- title:
--   Filtration Functor for localized persistent commutative algebra
-- statement:
--   This bundle supplies filtration Functor for localized persistent commutative algebra. The bundle contains the selected declarations used by this attachment checkpoint, with the hypotheses of their Lean statements retained. Its role as a dependency does not assert a stronger comparison, scalar compatibility or persistence theorem than those declarations state.
--
--   The included constructions and necessary compatibility results are:
--
--   - Inclusion of face families reverses the inclusion of the actual Stanley--Reisner ideals in the same ambient polynomial ring.
--   - The genuine quotient-induced surjection, as an algebra map over the ambient polynomial ring, so its scalar action is the original one.
--   - Reversed structure maps on the original legacy-Ext support functor.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Solutions/LPCA_FiltrationFunctor.lean, selected declarations in lines 16–108; source SHA-256 1b276b32f586aa4772974ecb446b2fd1a7a619750fa760515c8a5ddf79dbb60e; source certificate Sapelo2 job 49172236.

import Mathlib.Algebra.Homology.LocalCohomology
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Definitions.Def_LPCA

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

namespace LPCA

open CategoryTheory

universe u

variable {V : Type u} [DecidableEq V]

theorem level_faces_mono (K : Complex V) (f : Finset V → ℝ)
    (hf : FiltrationMonotone K f) {s t : ℝ} (hst : s ≤ t) :
    (level K f hf s).faces ⊆ (level K f hf t).faces := by
  intro F hF
  obtain ⟨hFK, hFs⟩ := Finset.mem_filter.mp hF
  exact Finset.mem_filter.mpr ⟨hFK, hFs.trans hst⟩

theorem deletion_faces_mono {K L : Complex V} (h : K.faces ⊆ L.faces) (i : V) :
    (deletion K i).faces ⊆ (deletion L i).faces := by
  intro F hF
  obtain ⟨hFK, hi⟩ := Finset.mem_filter.mp hF
  exact Finset.mem_filter.mpr ⟨h hFK, hi⟩

theorem link_faces_mono {K L : Complex V} (h : K.faces ⊆ L.faces) (σ : Finset V) :
    (link K σ).faces ⊆ (link L σ).faces := by
  intro F hF
  obtain ⟨hFK, hd, hu⟩ := Finset.mem_filter.mp hF
  exact Finset.mem_filter.mpr ⟨h hFK, hd, h hu⟩

variable (k : Type u) [Field k]

/-- Inclusion of face families reverses the inclusion of the actual
Stanley--Reisner ideals in the same ambient polynomial ring. -/
theorem srIdeal_antitone {K L : Complex V} (h : K.faces ⊆ L.faces) :
    srIdeal k L ≤ srIdeal k K := by
  apply Ideal.span_le.mpr
  rintro p ⟨F, hFL, rfl⟩
  exact Ideal.subset_span ⟨F, (fun hFK => hFL (h hFK)), rfl⟩

/-- The genuine quotient-induced surjection, as an algebra map over the
ambient polynomial ring, so its scalar action is the original one. -/
noncomputable def faceRingRestriction {K L : Complex V} (h : K.faces ⊆ L.faces) :
    FaceRing k L →ₐ[MvPolynomial V k] FaceRing k K :=
  Ideal.Quotient.factorₐ (MvPolynomial V k) (srIdeal_antitone k h)

theorem faceRingRestriction_mk {K L : Complex V} (h : K.faces ⊆ L.faces)
    (p : MvPolynomial V k) :
    faceRingRestriction k h (Ideal.Quotient.mk (srIdeal k L) p) =
      Ideal.Quotient.mk (srIdeal k K) p := rfl



theorem faceRingRestriction_refl (K : Complex V) :
    faceRingRestriction k (Finset.Subset.refl K.faces) =
      AlgHom.id (MvPolynomial V k) (FaceRing k K) := by
  exact Ideal.Quotient.factorₐ_refl (R := MvPolynomial V k) (srIdeal k K)

theorem faceRingRestriction_comp {K L M : Complex V}
    (hKL : K.faces ⊆ L.faces) (hLM : L.faces ⊆ M.faces) :
    (faceRingRestriction k hKL).comp (faceRingRestriction k hLM) =
      faceRingRestriction k (hKL.trans hLM) := by
  exact Ideal.Quotient.factorₐ_comp (MvPolynomial V k)
    (srIdeal_antitone k hLM) (srIdeal_antitone k hKL)

noncomputable def faceRingModuleRestriction {K L : Complex V} (h : K.faces ⊆ L.faces) :
    ModuleCat.of (MvPolynomial V k) (FaceRing k L) ⟶
      ModuleCat.of (MvPolynomial V k) (FaceRing k K) :=
  ModuleCat.ofHom (faceRingRestriction k h).toLinearMap

theorem faceRingModuleRestriction_refl (K : Complex V) :
    faceRingModuleRestriction k (Finset.Subset.refl K.faces) = 𝟙 _ := by
  apply ModuleCat.hom_ext
  exact congrArg AlgHom.toLinearMap (faceRingRestriction_refl k K)

theorem faceRingModuleRestriction_comp {K L M : Complex V}
    (hKL : K.faces ⊆ L.faces) (hLM : L.faces ⊆ M.faces) :
    faceRingModuleRestriction k hLM ≫ faceRingModuleRestriction k hKL =
      faceRingModuleRestriction k (hKL.trans hLM) := by
  apply ModuleCat.hom_ext
  exact congrArg AlgHom.toLinearMap (faceRingRestriction_comp k hKL hLM)

/-- Reversed structure maps on the original legacy-Ext support functor. -/
noncomputable def supportCohomologyRestriction {K L : Complex V}
    (h : K.faces ⊆ L.faces) (T : Finset V) (q : ℕ) :
    supportCohomology k L T q ⟶ supportCohomology k K T q :=
  (localCohomology (coordinateIdeal k T) q).map (faceRingModuleRestriction k h)

theorem supportCohomologyRestriction_refl (K : Complex V) (T : Finset V) (q : ℕ) :
    supportCohomologyRestriction k (Finset.Subset.refl K.faces) T q = 𝟙 _ := by
  rw [supportCohomologyRestriction, faceRingModuleRestriction_refl]
  exact CategoryTheory.Functor.map_id _ _

theorem supportCohomologyRestriction_comp {K L M : Complex V}
    (hKL : K.faces ⊆ L.faces) (hLM : L.faces ⊆ M.faces) (T : Finset V) (q : ℕ) :
    supportCohomologyRestriction k hLM T q ≫ supportCohomologyRestriction k hKL T q =
      supportCohomologyRestriction k (hKL.trans hLM) T q := by
  rw [supportCohomologyRestriction, supportCohomologyRestriction,
    ← Functor.map_comp, faceRingModuleRestriction_comp]
  rfl



end LPCA


