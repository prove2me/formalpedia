-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsQuasiFinitePolynomialMap
-- name    : Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsQuasiFinitePolynomialMap
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:16:35.275859+00:00
-- url     : https://prove2.me/theorems/4d5bb82c-b8d7-409a-8862-49a82789a648
-- title:
--   Exists Quasi Finite Polynomial Map
-- statement:
--   Definitions and structural lemmas for Exists Quasi Finite Polynomial Map, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsQuasiFinitePolynomialMap.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.NoetherInt
open Polynomial
end GlobalTheory.NoetherInt
namespace GlobalTheory.NoetherInt
open MvPolynomial
section shear
variable {A : Type*} [CommRing A] {n : ℕ}
noncomputable def shearHom (A : Type*) [CommRing A] (n u : ℕ) (c : A) :
    MvPolynomial (Fin (n + 1)) A →ₐ[A] MvPolynomial (Fin (n + 1)) A :=
  aeval fun i ↦ if i = 0 then X 0 else X i + c • X 0 ^ (u ^ i.1)
lemma shearHom_comp_neg (u : ℕ) (c : A) :
    (shearHom A n u c).comp (shearHom A n u (-c)) = AlgHom.id _ _ := by
  apply MvPolynomial.algHom_ext
  intro i
  cases i using Fin.cases <;> simp [shearHom]
noncomputable def shear (A : Type*) [CommRing A] (n u : ℕ) :
    MvPolynomial (Fin (n + 1)) A ≃ₐ[A] MvPolynomial (Fin (n + 1)) A :=
  AlgEquiv.ofAlgHom (shearHom A n u 1) (shearHom A n u (-1))
    (shearHom_comp_neg u 1)
    (by have := shearHom_comp_neg (A := A) (n := n) u (-1); rwa [neg_neg] at this)
end shear
section lead
variable {k : Type*} [Field k] {n : ℕ} (f : MvPolynomial (Fin (n + 1)) k)
variable (v w : Fin (n + 1) →₀ ℕ)
local notation3 "up" => 2 + f.totalDegree
local notation3 "r" => fun (i : Fin (n + 1)) ↦ up ^ i.1
local notation3 "T" => shear k n (2 + f.totalDegree)
end lead
end GlobalTheory.NoetherInt
namespace GlobalTheory.NoetherInt
open MvPolynomial
end GlobalTheory.NoetherInt
namespace GlobalTheory.NoetherInt
open MvPolynomial
end GlobalTheory.NoetherInt
namespace GlobalTheory
open IsLocalRing
end GlobalTheory


