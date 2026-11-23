-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TwConj
-- name    : Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TwConj
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:40:39.723459+00:00
-- url     : https://prove2.me/theorems/92469481-18de-4b19-81db-999389ccedc9
-- title:
--   Tw Conj
-- statement:
--   Definitions and structural lemmas for Tw Conj, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/TwConj.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
namespace GlobalTheory.Tw
variable {n : ℕ} {R : Type} [CommRing R] [StarRing R]
def Phi (n : ℕ) (R : Type) [CommRing R] : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => if (i : ℕ) + (j : ℕ) + 1 = n then (-1) ^ (i : ℕ) else 0
def theta (g : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R := Phi n R * (g⁻¹)ᴴ * (Phi n R)ᵀ
def nrm (δ : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R := δ * theta δ
def twConj (x δ : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R := x⁻¹ * δ * theta x
def Reg (δ : Matrix (Fin n) (Fin n) R) : Prop := IsUnit δ ∧ (nrm δ).charpoly.Separable
def cent (δ : Matrix (Fin n) (Fin n) R) : Set (Matrix (Fin n) (Fin n) R) := {g | IsUnit g ∧ g * δ = δ * theta g}
def adj (δ g : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R := δ * Phi n R * gᴴ * (Phi n R)ᵀ * δ⁻¹
end GlobalTheory.Tw


