-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocRing
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocRing
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:45:00.808425+00:00
-- url     : https://prove2.me/theorems/53501bf8-6845-4718-9431-c64e0fac8322
-- title:
--   Statements Semiloc Ring
-- statement:
--   Definitions and structural lemmas for Statements Semiloc Ring, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StatementsSemilocRing.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IdDeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LocRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter
section Semiloc
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
def semiLocRing (P : Ideal (MRing ι)) (𝒲 : Set (Ideal (MRing ι))) : Subring (FractionRing (MRing ι ⧸ P)) :=
  Subring.closure {x | ∃ (u w : MRing ι) (a : K → ℕ)
    (hw : Ideal.Quotient.mk P w ∈ nonZeroDivisors (MRing ι ⧸ P)),
    (∀ W ∈ 𝒲, w ∉ W) ∧ IsMultiHomog u a ∧ IsMultiHomog w a ∧
      x = IsLocalization.mk' (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P u) ⟨_, hw⟩}
end Semiloc
section Block
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
def fibreOver (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (W : Ideal (MRing ι)) :
    Set (Ideal (MRing ι')) :=
  {W' | IsMultiProjPrime W' ∧ P' ≤ W' ∧ imageZ v W' = W}
open Classical in

theorem rename_isMultiHomog {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) :
    IsMultiHomog (rename v f) (Function.extend κ a 0) := by
  intro m' hm' k'
  rw [support_rename_of_injective hv.2.1, Finset.mem_image] at hm'
  obtain ⟨m, hm, rfl⟩ := hm'
  have hblock : ∀ (F : (Σ k', ι' k') → ℕ), ∑ i, F ⟨k', i⟩ = ∑ q, if q.1 = k' then F q else 0 := by
    intro F
    rw [Fintype.sum_sigma, Finset.sum_eq_single k']
    · simp
    · intro b _ hb
      simp [hb]
    · simp
  rw [hblock]
  have h1 : (∑ q, if q.1 = k' then Finsupp.mapDomain v m q else 0) =
      ∑ p, if κ p.1 = k' then m p else 0 := by
    have := Finsupp.sum_mapDomain_index_inj (h := fun (q : Σ k', ι' k') (n : ℕ) => if q.1 = k' then n else 0)
      (s := m) hv.2.1
    rw [Finsupp.sum_fintype _ _ (by simp), Finsupp.sum_fintype _ _ (by simp)] at this
    simpa [hv.2.2.1] using this
  have h2 : (∑ p : Σ k, ι k, if κ p.1 = k' then m p else 0) = ∑ k, if κ k = k' then a k else 0 := by
    rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs with hk
    · exact hf m hm k
    · simp
  convert h1.trans h2
  by_cases h : ∃ k, κ k = k'
  · obtain ⟨k, rfl⟩ := h
    rw [hv.1.extend_apply, Finset.sum_eq_single k]
    · simp
    · intro b _ hb
      simp [hv.1.ne hb]
    · simp
  · rw [Function.extend_apply' _ _ _ h]
    refine (Finset.sum_eq_zero fun k _ => ?_).symm
    rw [if_neg fun hk => h ⟨k, hk⟩]
abbrev quotMapZ (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) :
    MRing ι ⧸ imageZ v P' →+* MRing ι' ⧸ P' :=
  Ideal.quotientMap P' (rename v : MRing ι →ₐ[ℤ] MRing ι').toRingHom le_rfl
omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] in
theorem quotMapZ_injective (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) :
    Function.Injective (quotMapZ v P') :=
  Ideal.quotientMap_injective
omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] in

theorem imageZ_isPrime_of_prime (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) [P'.IsPrime] :
    (imageZ v P').IsPrime :=
  Ideal.comap_isPrime _ _
def fracMapZ (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) [P'.IsPrime] :
    FractionRing (MRing ι ⧸ imageZ v P') →+* FractionRing (MRing ι' ⧸ P') :=
  haveI := imageZ_isPrime_of_prime v P'
  IsFractionRing.lift (g := (algebraMap (MRing ι' ⧸ P') (FractionRing (MRing ι' ⧸ P'))).comp (quotMapZ v P'))
    ((IsFractionRing.injective (MRing ι' ⧸ P') (FractionRing (MRing ι' ⧸ P'))).comp (quotMapZ_injective v P'))
omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] in
theorem fracMapZ_algebraMap (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) [P'.IsPrime] (f : MRing ι) :
    fracMapZ v P' (algebraMap _ _ (Ideal.Quotient.mk (imageZ v P') f)) =
      algebraMap _ _ (Ideal.Quotient.mk P' (rename v f)) := by
  have := imageZ_isPrime_of_prime v P'
  unfold fracMapZ
  rw [IsFractionRing.lift_algebraMap]
  rfl
theorem fracMapZ_mem {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    (P' : Ideal (MRing ι')) [P'.IsPrime] (W : Ideal (MRing ι)) (x : FractionRing (MRing ι ⧸ imageZ v P'))
    (hx : x ∈ locRing (imageZ v P') W) : fracMapZ v P' x ∈ semiLocRing P' (fibreOver v P' W) := by
  have := imageZ_isPrime_of_prime v P'
  have hle : locRing (imageZ v P') W ≤ (semiLocRing P' (fibreOver v P' W)).comap (fracMapZ v P') := by
    rw [locRing, Subring.closure_le]
    rintro _ ⟨u, w, a, hw, hwW, hu, hwa, rfl⟩
    rw [SetLike.mem_coe, Subring.mem_comap]
    have hw0 : rename v w ∉ P' := by
      intro h
      apply nonZeroDivisors.ne_zero hw
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact h
    have hw' : Ideal.Quotient.mk P' (rename v w) ∈ nonZeroDivisors (MRing ι' ⧸ P') :=
      mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
    apply Subring.subset_closure
    refine ⟨rename v u, rename v w, Function.extend κ a 0, hw', ?_, rename_isMultiHomog hv hu,
      rename_isMultiHomog hv hwa, ?_⟩
    · rintro W' ⟨-, -, hW'⟩ hmem
      apply hwW
      rw [← hW']
      exact hmem
    · rw [IsFractionRing.mk'_eq_div, IsFractionRing.mk'_eq_div, map_div₀]
      exact congrArg₂ (· / ·) (fracMapZ_algebraMap v P' u) (fracMapZ_algebraMap v P' w)
  exact hle hx
def locToSemiloc {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    (P' : Ideal (MRing ι')) [P'.IsPrime] (W : Ideal (MRing ι)) :
    locRing (imageZ v P') W →+* semiLocRing P' (fibreOver v P' W) :=
  (fracMapZ v P').restrict _ _ (fun x hx => fracMapZ_mem hv P' W x hx)
end Block
namespace SemilocRing
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
open Classical in

def blkW : (Σ k, ι k) → K → ℕ := fun p => Pi.single p.1 1
end SemilocRing
section Example
end Example
end GroundTheory.Heights₂.Heights.Inter


