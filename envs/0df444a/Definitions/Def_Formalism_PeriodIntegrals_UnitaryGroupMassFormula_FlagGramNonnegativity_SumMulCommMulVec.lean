-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FlagGramNonnegativity_SumMulCommMulVec
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FlagGramNonnegativity_SumMulCommMulVec
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:13:51.334735+00:00
-- url     : https://prove2.me/theorems/9a75e48c-ea80-43e9-8a0f-fa104fb5a997
-- title:
--   Sum Mul Comm Mul Vec
-- statement:
--   Definitions and structural lemmas for Sum Mul Comm Mul Vec, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FlagGramNonnegativity/SumMulCommMulVec.lean

import Definitions.Def_Formalism_PeriodIntegrals_FlagGramNonneg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix PI.FlagGramNonneg
namespace PI.UnitaryGroupMassFormula.FlagGramNonneg
section Vec
variable {E : Type} [Field E] [StarRing E] {V : Type} [AddCommGroup V] [Module E V]
def amat (hT : V →ₗ⋆[E] V →ₗ[E] E) {r : ℕ} (e e' : Fin r → V) : Matrix (Fin r) (Fin r) E :=
  fun a b => hT (e a) (e' b)
def uvec (hT : V →ₗ⋆[E] V →ₗ[E] E) {r : ℕ} (e : Fin r → V) (z' : V) : Fin r → E :=
  fun a => hT (e a) z'
def vvec (hT : V →ₗ⋆[E] V →ₗ[E] E) {r : ℕ} (z : V) (e' : Fin r → V) : Fin r → E :=
  fun b => hT z (e' b)
def sval (hT : V →ₗ⋆[E] V →ₗ[E] E) {r : ℕ} (e e' : Fin r → V) (z z' : V) : E :=
  hT z z' - vvec hT z e' ⬝ᵥ ((amat hT e e')⁻¹ *ᵥ uvec hT e z')
def zt (hT : V →ₗ⋆[E] V →ₗ[E] E) {r : ℕ} (e e' : Fin r → V) (z : V) : V :=
  z - ∑ a, star ((vvec hT z e' ᵥ* (amat hT e e')⁻¹) a) • e a
def zt' (hT : V →ₗ⋆[E] V →ₗ[E] E) {r : ℕ} (e e' : Fin r → V) (z' : V) : V :=
  z' - ∑ b, ((amat hT e e')⁻¹ *ᵥ uvec hT e z') b • e' b
def yv (hT : V →ₗ⋆[E] V →ₗ[E] E) {r : ℕ} (e e' : Fin r → V) (a : Fin r) : V :=
  e a - ∑ b, (amat hT e e')⁻¹ b a • e' b
variable (hT : V →ₗ⋆[E] V →ₗ[E] E) {r : ℕ} (e e' : Fin r → V) (z z' : V)
end Vec
end PI.UnitaryGroupMassFormula.FlagGramNonneg


