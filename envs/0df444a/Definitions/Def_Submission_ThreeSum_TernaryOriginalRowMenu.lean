-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryOriginalRowMenu
-- name    : Submission_ThreeSum_TernaryOriginalRowMenu
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:06:56.373925+00:00
-- url     : https://prove2.me/theorems/1bf05859-a2f2-456d-bf1f-80300260888c
-- title:
--   Ternary Original Row Menu
-- statement:
--   Definitions and structural lemmas for Ternary Original Row Menu, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryOriginalRowMenu.lean

import Definitions.Def_Submission_ThreeSum_HashFamily
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.FieldTheory.Finite.GaloisField
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
attribute [local simp] ThreeSum.HashFamily.hashMap_apply


set_option autoImplicit false
noncomputable section
namespace ThreeSum.TernaryOriginalRowMenu
open Finset
open Polynomial
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {K E : Type*} [Field K] [Field E] [Algebra K E]
  [Fintype K] [Fintype E] [DecidableEq K] [DecidableEq E]
def vectorPoly (Λ : ℕ) : (Fin Λ → K) →ₗ[K] E[X] :=
  ((Polynomial.ofFn Λ).restrictScalars K).comp
    (LinearMap.pi fun i => (Algebra.linearMap K E).comp (LinearMap.proj i))
def evalVector (Λ : ℕ) (x : E) : (Fin Λ → K) →ₗ[K] E :=
  ((Polynomial.aeval x).toLinearMap.restrictScalars K).comp (vectorPoly (E := E) Λ)
def pairing (ℓ : E →ₗ[K] K) : E →ₗ[K] Module.Dual K E :=
  LinearMap.mk₂ K (fun a y => ℓ (a*y))
    (by intro a b y; simp [add_mul])
    (by intro c a y; simp [smul_mul_assoc])
    (by intro a y z; simp [mul_add])
    (by intro c a y; simp [mul_smul_comm])
def jointMap {t : ℕ} (ℓ : E →ₗ[K] K) (v : Fin t → E) : E →ₗ[K] (Fin t → K) :=
  LinearMap.pi fun i => pairing ℓ (v i)
def combination {Λ t : ℕ} (v : Fin t → Fin Λ → K) (c : Fin t → K) : E[X] :=
  vectorPoly Λ (∑ i, c i • v i)
def badSeeds {Λ t : ℕ} (v : Fin t → Fin Λ → K) : Finset E :=
  (univ.erase (0 : Fin t → K)).biUnion fun c =>
    univ.filter fun x => (combination (E := E) v c).eval x = 0
def row (Λ : ℕ) (ℓ : E →ₗ[K] K) (seed : E × E) : (Fin Λ → K) →ₗ[K] K :=
  ((pairing ℓ).flip seed.2).comp (evalVector Λ seed.1)
def menuEvent {Λ t : ℕ} (ℓ : E →ₗ[K] K) (v : Fin t → Fin Λ → K)
    (target : Fin t → K) : Finset (E × E) :=
  univ.filter fun seed => ∀ i, row Λ ℓ seed (v i) = target i
def seedRow (Λ : ℕ) (ℓ : E →ₗ[K] K) (seed : E × E) : Fin Λ → K :=
  fun i => row Λ ℓ seed (Pi.single i 1)
def admissible (Λ : ℕ) (ℓ : E →ₗ[K] K) (V : Submodule K (Fin Λ → K)) : Finset (E × E) :=
  univ.filter fun seed => seedRow Λ ℓ seed ∉ V
end ThreeSum.TernaryOriginalRowMenu


