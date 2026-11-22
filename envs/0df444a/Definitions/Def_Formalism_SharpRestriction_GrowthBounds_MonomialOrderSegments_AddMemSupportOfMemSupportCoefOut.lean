-- Prove2me | Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
-- name    : Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:45:37.905572+00:00
-- url     : https://prove2.me/theorems/a36bccb9-54df-4220-8a12-a5677a8a7ad7
-- title:
--   Add Mem Support Of Mem Support Coef Out
-- statement:
--   Definitions and structural lemmas for Add Mem Support Of Mem Support Coef Out, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
namespace Formalism.MainNotions.PlaneGram
section Lord
variable {R : Type} [Semiring R]
end Lord
section Pge
variable {R : Type} [CommSemiring R] {σ : Type}
def pge (n : WithTop ℤ) (G : MvPolynomial σ (LaurentPolynomial R)) : Prop :=
  ∀ β, n ≤ lord (G.coeff β)
end Pge
section Basic
variable {K : Type} [Field K] {L : Type} [DecidableEq L] {r : ℕ} (sg : L → Bool) (S : Finset L)
abbrev subV : MvPolynomial (L × Fin r) K →+* MvPolynomial (L × Fin r) (LauF K r) :=
  substS (lauι K r) sg S (hMat K r) (hInvT K r)
end Basic
section Exps
variable {L : Type} {r : ℕ} (out : L → Prop) [DecidablePred out]
end Exps
section Subst
variable {K : Type} [Field K] {L : Type} [DecidableEq L] {r : ℕ} {R : Type} [CommRing R]
  (ι : K →+* R) (sg : L → Bool) (S : Finset L) (A B : Matrix (Fin r) (Fin r) R)
def subX (x : L × Fin r) : MvPolynomial (L × Fin r) R :=
  if x.1 ∈ S then
    (if sg x.1 then ∑ b, MvPolynomial.C (A x.2 b) * X (x.1, b)
     else ∑ b, MvPolynomial.C (B x.2 b) * X (x.1, b))
  else X x
variable (out : L → Prop) [DecidablePred out]
end Subst
section CoefOut
variable {K : Type} [Field K] {L : Type} [DecidableEq L] {r : ℕ}
  (out : L → Prop) [DecidablePred out]
theorem coefOut_eq_sum (μ : L × Fin r →₀ ℕ) (F : MvPolynomial (L × Fin r) K)
    (s : Finset (L × Fin r →₀ ℕ)) (hs : F.support ⊆ s) :
    coefOut out μ F = ∑ α ∈ s, if eOut out α = μ then monomial (eIn out α) (F.coeff α) else 0 := by
  unfold coefOut
  refine Finset.sum_subset hs fun α _ hα => ?_
  rw [notMem_support_iff.mp hα, monomial_zero, ite_self]
theorem coefOut_add (μ : L × Fin r →₀ ℕ) (F G : MvPolynomial (L × Fin r) K) :
    coefOut out μ (F + G) = coefOut out μ F + coefOut out μ G := by
  rw [coefOut_eq_sum out μ (F + G) (F.support ∪ G.support) support_add,
    coefOut_eq_sum out μ F (F.support ∪ G.support) Finset.subset_union_left,
    coefOut_eq_sum out μ G (F.support ∪ G.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  split_ifs
  · rw [coeff_add, map_add]
  · rw [add_zero]
theorem coefOut_smul (μ : L × Fin r →₀ ℕ) (a : K) (F : MvPolynomial (L × Fin r) K) :
    coefOut out μ (a • F) = a • coefOut out μ F := by
  rw [coefOut_eq_sum out μ (a • F) F.support support_smul, coefOut, Finset.smul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  split_ifs
  · rw [coeff_smul, smul_monomial]
  · rw [smul_zero]
def coefOutL (μ : L × Fin r →₀ ℕ) : MvPolynomial (L × Fin r) K →ₗ[K] MvPolynomial (L × Fin r) K where
  toFun := coefOut out μ
  map_add' := coefOut_add out μ
  map_smul' := coefOut_smul out μ
variable (sg : L → Bool) (S : Finset L)
end CoefOut
section Nonneg
variable {K : Type} [Field K]
variable {L : Type} [DecidableEq L] {r : ℕ} (sg : L → Bool) (S : Finset L)
end Nonneg
section Rename
variable {K : Type} [Field K] {L : Type} [DecidableEq L] {L' : Type} [DecidableEq L'] {r : ℕ}
end Rename
section Hcomp
variable {L : Type} {r : ℕ}
def HomD {R : Type} [CommSemiring R] (d : L → ℕ) (G : MvPolynomial (L × Fin r) R) : Prop :=
  ∀ β ∈ G.support, ∀ i, ldeg β i = d i
section HomD
variable {R : Type} [CommSemiring R]
end HomD
variable {K : Type} [Field K] [DecidableEq L] {R : Type} [CommRing R]
  (ι : K →+* R) (sg : L → Bool) (S : Finset L) (A B : Matrix (Fin r) (Fin r) R)
variable [Fintype L]
def hcomp (d : L → ℕ) (F : MvPolynomial (L × Fin r) K) : MvPolynomial (L × Fin r) K :=
  ∑ α ∈ F.support, if (∀ i, ldeg α i = d i) then monomial α (F.coeff α) else 0
end Hcomp
section Vala
variable {K : Type} [Field K] {L : Type} [DecidableEq L] {r : ℕ} (sg : L → Bool) (S : Finset L)
variable {sg S}
end Vala
section FromV2
variable {K : Type} [Field K] [CharZero K] {L : Type} [Fintype L] [DecidableEq L] {r : ℕ} [NeZero r]
  {sg : L → Bool} {S : Finset L}
end FromV2
section TotallyRealRoots
variable {K : Type} [Field K]
variable {L : Type} [DecidableEq L] {r : ℕ} {sg : L → Bool} {S : Finset L}
end TotallyRealRoots
end Formalism.MainNotions.PlaneGram


