-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_SphericalMinuscule
-- name    : GroundTheory_AutomorphicForms_SphericalMinuscule
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T12:26:56.159133+00:00
-- url     : https://prove2.me/theorems/12e1a78f-707c-538d-a3f5-5ea07b10d5d9
-- title:
--   Spherical Minuscule
-- statement:
--   Definitions and structural lemmas for Spherical Minuscule, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalMinuscule.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalTriangular
import Theorems.Thm_GroundTheory_Automorphic_HeckeAlgebra_mul_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GroundTheory.Automorphic
open MeasureTheory Matrix GLnLocal Iwasawa HeckeAlgebra AddMonoidAlgebra
open ValuativeRel (valuation)
open scoped ValuativeRel
namespace Spherical
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
local notation "π" => (GLnLocal.uniformizer F : F)
variable (F) in

def MBdd (t : ℤ) (A : Matrix (Fin n) (Fin n) F) : Prop := ∀ i j, Bdd F t (A i j)
variable (F n) in

def minusculeSet (k : ℕ) : Set (GL (Fin n) F) :=
  {g | (∀ i j, g i j ∈ 𝒪[F]) ∧ (∀ i j, π * (g⁻¹ : GL (Fin n) F) i j ∈ 𝒪[F]) ∧
    valuation F (g : Matrix (Fin n) (Fin n) F).det = valuation F π ^ k}
def lamS (S : Finset (Fin n)) : Fin n → ℤ := fun i => if i ∈ S then 1 else 0
def Pairs (S : Finset (Fin n)) : Type := {p : Fin n × Fin n // p.1 ∈ S ∧ p.2 ∉ S ∧ p.1 < p.2}
instance (S : Finset (Fin n)) : Fintype (Pairs S) := by
  unfold Pairs
  infer_instance
instance (S : Finset (Fin n)) : DecidableEq (Pairs S) := by
  unfold Pairs
  infer_instance
variable (F) in

def residueLift : 𝓀[F] → 𝒪[F] :=
  Function.surjInv (IsLocalRing.residue_surjective (R := 𝒪[F]))
def cMat (S : Finset (Fin n)) (c : Pairs S → 𝓀[F]) : Matrix (Fin n) (Fin n) F :=
  fun i j => if h : i ∈ S ∧ j ∉ S ∧ i < j then ((residueLift F (c ⟨(i, j), h⟩) : 𝒪[F]) : F) else 0
theorem cMat_apply_of_not {S : Finset (Fin n)} (c : Pairs S → 𝓀[F]) {i j : Fin n}
    (h : ¬(i ∈ S ∧ j ∉ S ∧ i < j)) : cMat S c i j = 0 := dif_neg h
theorem cMat_mul_cMat {S : Finset (Fin n)} (c c' : Pairs S → 𝓀[F]) : cMat S c * cMat S c' = 0 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hl : l ∈ S
  · rw [cMat_apply_of_not c (fun h => h.2.1 hl), zero_mul]
  · rw [cMat_apply_of_not c' (fun h => hl h.1), mul_zero]
def unipC (S : Finset (Fin n)) (c : Pairs S → 𝓀[F]) : GL (Fin n) F where
  val := 1 + cMat S c
  inv := 1 - cMat S c
  val_inv := by rw [mul_sub, mul_one, add_mul, one_mul, cMat_mul_cMat, add_zero, add_sub_cancel_right]
  inv_val := by rw [mul_add, mul_one, sub_mul, one_mul, cMat_mul_cMat, sub_zero, sub_add_cancel]
def gMat (S : Finset (Fin n)) (c : Pairs S → 𝓀[F]) : GL (Fin n) F :=
  unipC S c * torusPow F n (lamS S)
end Spherical
end GroundTheory.Automorphic


