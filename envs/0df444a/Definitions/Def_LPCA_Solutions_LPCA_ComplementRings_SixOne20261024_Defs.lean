-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_ComplementRings_SixOne20261024_Defs
-- name    : LPCA_Solutions_LPCA_ComplementRings_SixOne20261024_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-24T20:04:32.687981+00:00
-- url     : https://prove2.me/theorems/db29ada6-4248-4088-b3fc-8ffc96d8f56f
-- title:
--   Complement Rings — coordinate chain dependencies
-- statement:
--   This bundle supplies the selected constructions and proved compatibility results for complement rings used in the coordinate Čech chain comparison. Each construction retains the rings, categories, grading indices and hypotheses in its formal declaration.
--
--   Set the complementary variables to zero, on the actual face-ring quotients.
--
--   Inclusion of the remaining variables, descended to the actual face-ring quotients.
--
--   Once all faces use the remaining variables, removing ghost coordinates is
--   a canonical equivalence of genuine polynomial-quotient k-algebras.
-- source:
--   https://arxiv.org/abs/2609.02858v1, Section 6, Theorem 6.1 and its formalization dependencies. Certified Lean source: Solutions/LPCA_ComplementRings.lean, selected declarations in lines 27–162; source SHA-256 556f520bf8ea8ab96c88b637daa2b1a4116b6eeaafa4ca7c5b7de6574f2bc05f; exact-source certificate Sapelo2 job 49296539.

import Mathlib.Algebra.Homology.LocalCohomology
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Tactic
import Definitions.Def_LPCA
import Definitions.Def_LPCA_Solutions_LPCA_ComplementRings_Defs

set_option autoImplicit false

namespace LPCA

universe u

variable {V W : Type u} [DecidableEq V] [DecidableEq W]
variable (k : Type u) [Field k]





private theorem rename_squarefree (e : W ↪ V) (F : Finset W) :
    MvPolynomial.rename e (∏ j ∈ F, MvPolynomial.X j : MvPolynomial W k) =
      ∏ v ∈ F.map e, MvPolynomial.X v := by
  simp only [map_prod, MvPolynomial.rename_X, Finset.prod_map]

private theorem rename_srIdeal_le (K : Complex V) (e : W ↪ V) :
    srIdeal k (restrictComplex K e) ≤
      RingHom.ker (((Ideal.Quotient.mkₐ k (srIdeal k K)).comp
        (MvPolynomial.rename e)).toRingHom) := by
  apply Ideal.span_le.mpr
  rintro p ⟨F, hF, rfl⟩
  change Ideal.Quotient.mk (srIdeal k K)
    (MvPolynomial.rename e (∏ j ∈ F, MvPolynomial.X j)) = 0
  rw [rename_squarefree]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.subset_span ⟨F.map e, (mem_restrictComplex K e F).not.mp hF, rfl⟩

/-- Inclusion of the remaining variables, descended to the actual face-ring quotients. -/
noncomputable def faceRingRename (K : Complex V) (e : W ↪ V) :
    FaceRing k (restrictComplex K e) →ₐ[k] FaceRing k K :=
  Ideal.Quotient.liftₐ (srIdeal k (restrictComplex K e))
    ((Ideal.Quotient.mkₐ k (srIdeal k K)).comp (MvPolynomial.rename e))
    (fun p hp => rename_srIdeal_le k K e hp)

@[simp] theorem faceRingRename_mk (K : Complex V) (e : W ↪ V)
    (p : MvPolynomial W k) :
    faceRingRename k K e (Ideal.Quotient.mk (srIdeal k (restrictComplex K e)) p) =
      Ideal.Quotient.mk (srIdeal k K) (MvPolynomial.rename e p) := rfl

private theorem killCompl_squarefree_mem (K : Complex V) (e : W ↪ V)
    (F : Finset V) (hF : F ∉ K.faces) :
    MvPolynomial.killCompl e.injective (∏ v ∈ F, MvPolynomial.X v : MvPolynomial V k) ∈
      srIdeal k (restrictComplex K e) := by
  classical
  by_cases hr : ∀ v ∈ F, v ∈ Set.range e
  · let G := F.preimage e e.injective.injOn
    have hG : G.map e = F := by
      ext v
      constructor
      · intro hv
        obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hv
        exact Finset.mem_preimage.mp hw
      · intro hv
        obtain ⟨w, rfl⟩ := hr v hv
        exact Finset.mem_map.mpr ⟨w, Finset.mem_preimage.mpr hv, rfl⟩
    have hGnf : G ∉ (restrictComplex K e).faces := by
      simpa only [mem_restrictComplex, hG] using hF
    have hp : (∏ v ∈ F, MvPolynomial.X v : MvPolynomial V k) =
        MvPolynomial.rename e (∏ w ∈ G, MvPolynomial.X w) := by
      rw [rename_squarefree, hG]
    rw [hp, MvPolynomial.killCompl_rename_app]
    exact Ideal.subset_span ⟨G, hGnf, rfl⟩
  · push_neg at hr
    obtain ⟨v, hv, hvr⟩ := hr
    have hk : MvPolynomial.killCompl e.injective (MvPolynomial.X v : MvPolynomial V k) = 0 := by
      rw [MvPolynomial.killCompl, MvPolynomial.aeval_X, dif_neg hvr]
    rw [map_prod, Finset.prod_eq_zero hv hk]
    exact zero_mem _

private theorem killCompl_srIdeal_le (K : Complex V) (e : W ↪ V) :
    srIdeal k K ≤ RingHom.ker
      (((Ideal.Quotient.mkₐ k (srIdeal k (restrictComplex K e))).comp
        (MvPolynomial.killCompl e.injective)).toRingHom) := by
  apply Ideal.span_le.mpr
  rintro p ⟨F, hF, rfl⟩
  change Ideal.Quotient.mk (srIdeal k (restrictComplex K e))
    (MvPolynomial.killCompl e.injective (∏ v ∈ F, MvPolynomial.X v)) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (killCompl_squarefree_mem k K e F hF)

/-- Set the complementary variables to zero, on the actual face-ring quotients. -/
noncomputable def faceRingKillCompl (K : Complex V) (e : W ↪ V) :
    FaceRing k K →ₐ[k] FaceRing k (restrictComplex K e) :=
  Ideal.Quotient.liftₐ (srIdeal k K)
    ((Ideal.Quotient.mkₐ k (srIdeal k (restrictComplex K e))).comp
      (MvPolynomial.killCompl e.injective))
    (fun p hp => killCompl_srIdeal_le k K e hp)

@[simp] theorem faceRingKillCompl_mk (K : Complex V) (e : W ↪ V)
    (p : MvPolynomial V k) :
    faceRingKillCompl k K e (Ideal.Quotient.mk (srIdeal k K) p) =
      Ideal.Quotient.mk (srIdeal k (restrictComplex K e))
        (MvPolynomial.killCompl e.injective p) := rfl

theorem faceRingKillCompl_comp_rename (K : Complex V) (e : W ↪ V) :
    (faceRingKillCompl k K e).comp (faceRingRename k K e) =
      AlgHom.id k (FaceRing k (restrictComplex K e)) := by
  apply Ideal.Quotient.algHom_ext
  apply AlgHom.ext
  intro p
  change faceRingKillCompl k K e
    (faceRingRename k K e (Ideal.Quotient.mk _ p)) = Ideal.Quotient.mk _ p
  rw [faceRingRename_mk, faceRingKillCompl_mk, MvPolynomial.killCompl_rename_app]

theorem variableClass_eq_zero_outside
    (K : Complex V) (e : W ↪ V)
    (hK : ∀ F ∈ K.faces, ∀ v ∈ F, v ∈ Set.range e)
    (v : V) (hv : v ∉ Set.range e) : variableClass k K v = 0 := by
  have hnf : {v} ∉ K.faces := by
    intro h
    exact hv (hK {v} h v (by simp))
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.subset_span ⟨{v}, hnf, by simp⟩

theorem faceRingRename_comp_killCompl
    (K : Complex V) (e : W ↪ V)
    (hK : ∀ F ∈ K.faces, ∀ v ∈ F, v ∈ Set.range e) :
    (faceRingRename k K e).comp (faceRingKillCompl k K e) =
      AlgHom.id k (FaceRing k K) := by
  classical
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro v
  change faceRingRename k K e
    (faceRingKillCompl k K e (Ideal.Quotient.mk _ (MvPolynomial.X v))) =
      Ideal.Quotient.mk _ (MvPolynomial.X v)
  rw [faceRingKillCompl_mk, faceRingRename_mk]
  by_cases hv : v ∈ Set.range e
  · obtain ⟨w, rfl⟩ := hv
    have hk : MvPolynomial.killCompl e.injective
        (MvPolynomial.X (e w) : MvPolynomial V k) = MvPolynomial.X w := by
      simpa only [MvPolynomial.rename_X] using
        MvPolynomial.killCompl_rename_app e.injective (MvPolynomial.X w : MvPolynomial W k)
    rw [hk, MvPolynomial.rename_X]
  · have hk : MvPolynomial.killCompl e.injective (MvPolynomial.X v : MvPolynomial V k) = 0 := by
      rw [MvPolynomial.killCompl, MvPolynomial.aeval_X, dif_neg hv]
    rw [hk, map_zero, map_zero]
    exact (variableClass_eq_zero_outside k K e hK v hv).symm

/-- Once all faces use the remaining variables, removing ghost coordinates is
a canonical equivalence of genuine polynomial-quotient k-algebras. -/
noncomputable def faceRingRestrictionEquiv
    (K : Complex V) (e : W ↪ V)
    (hK : ∀ F ∈ K.faces, ∀ v ∈ F, v ∈ Set.range e) :
    FaceRing k (restrictComplex K e) ≃ₐ[k] FaceRing k K :=
  AlgEquiv.ofAlgHom (faceRingRename k K e) (faceRingKillCompl k K e)
    (faceRingRename_comp_killCompl k K e hK) (faceRingKillCompl_comp_rename k K e)







end LPCA


