-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsIsKroneckerCharOfDiscr
-- name    : Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsIsKroneckerCharOfDiscr
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:24:44.559801+00:00
-- url     : https://prove2.me/theorems/e124bbdb-9505-43ff-87a9-0b284b702a2a
-- title:
--   Exists Is Kronecker Char Of Discr
-- statement:
--   Definitions and structural lemmas for Exists Is Kronecker Char Of Discr, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsIsKroneckerCharOfDiscr.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
open scoped NumberTheorySymbols
namespace GlobalTheory.QuadraticZeta
section Ring
variable {R : Type*} [CommRing R]
end Ring
variable {K : Type*} [Field K] [NumberField K]
def kroneckerAt (D : ℤ) (p : ℕ) : ℤ := if p = 2 then ZMod.χ₈ (D : ZMod 8) else J(D | p)
noncomputable def idealCount (K : Type*) [Field K] [NumberField K] (n : ℕ) : ℕ :=
  {I : Ideal (𝓞 K) | Ideal.absNorm I = n}.ncard
section
variable (b : Basis (Fin 2) ℤ (𝓞 K)) (h0 : b 0 = 1) {t n : ℤ} (hw : b 1 ^ 2 = t * b 1 - n)
  {p : ℕ} (hp : p.Prime) {P : Ideal (𝓞 K)} (hPm : P.IsMaximal)
  (hP : P.under ℤ = .span {(p : ℤ)})
include h0 hw hp hPm hP
end
end GlobalTheory.QuadraticZeta
namespace GlobalTheory
open QuadraticZeta
def IsKroneckerChar {d : ℕ} (χ : DirichletCharacter ℂ d) : Prop :=
  ∀ n : ℕ, Odd n → χ n = (J(-(d : ℤ) | n) : ℤ)
namespace IsKroneckerChar
variable {d : ℕ} {χ : DirichletCharacter ℂ d} (hχ : IsKroneckerChar χ)
include hχ
end IsKroneckerChar
variable {K : Type*} [Field K] [NumberField K] {d : ℕ}
end GlobalTheory


