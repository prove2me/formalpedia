-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HeckeLEntireAndNonzeroAtOne
-- name    : Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HeckeLEntireAndNonzeroAtOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:48:46.557898+00:00
-- url     : https://prove2.me/theorems/9a8a3632-7d46-446c-8895-d018eaa11ed4
-- title:
--   Hecke LEntire And Nonzero At One
-- statement:
--   Definitions and structural lemmas for Hecke LEntire And Nonzero At One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/HeckeLEntireAndNonzeroAtOne.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EntireEqOfHalfPlane
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AdelicCMFields_UnitaryHeckeCharacterIdele
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Host (HChar)
open GlobalTheory.CMVal (Ideles eulerFactor IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleNorm)
namespace GlobalTheory.HeckeOne
variable {K : Type} [Field K] [NumberField K]
def IsNormPow (χ : HChar K) (t : ℝ) : Prop :=
  ∀ x : Ideles K, ((χ.1 x : ℂˣ) : ℂ) = ((ideleNorm x : ℝ) : ℂ) ^ ((t : ℂ) * Complex.I)
def IsContAtOne (χ : HChar K) (Λ : ℂ → ℂ) : Prop :=
  AnalyticAt ℂ Λ 1 ∧ ∀ s : ℂ, 1 < s.re → HasProd (eulerFactor χ s) (Λ s)
end GlobalTheory.HeckeOne
namespace GlobalTheory.Published
open GlobalTheory.HeckeOne
def HeckeLEntireAndNonzeroAtOne : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (χ : HChar K), χ.IsUnitary →
    ((¬ ∃ t : ℝ, IsNormPow χ t) → ∃ Λ : ℂ → ℂ, IsHeckeL χ Λ) ∧
    (χ ≠ 1 → ∃ Λ : ℂ → ℂ, IsContAtOne χ Λ ∧ Λ 1 ≠ 0)
end GlobalTheory.Published
namespace GlobalTheory.HeckeOne
variable {K : Type} [Field K] [NumberField K]
variable (K) in

def normChar (t : ℝ) : HChar K :=
  ⟨Circle.toUnits.comp (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.UnitaryHeckeChar.normPow K t).toHom,
    Units.continuous_iff.2
      ⟨continuous_subtype_val.comp (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.UnitaryHeckeChar.normPow K t).continuous_toHom,
        continuous_subtype_val.comp (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.UnitaryHeckeChar.normPow K t).continuous_toHom.inv |>.congr
          fun x => by
            rw [Units.val_inv_eq_inv_val]
            exact Circle.coe_inv _⟩,
    fun k => by
      rw [MonoidHom.comp_apply]
      exact (congrArg Circle.toUnits
        ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.UnitaryHeckeChar.normPow K t).map_principal k)).trans (map_one _)⟩
end GlobalTheory.HeckeOne


