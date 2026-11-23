-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SplitLocF
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_SplitLocF
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:38:54.405686+00:00
-- url     : https://prove2.me/theorems/32f1ee4c-ab5c-4964-9f54-5f00c43df432
-- title:
--   Split Loc F
-- statement:
--   Definitions and structural lemmas for Split Loc F, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SplitLocF.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_DatumF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF IsDedekindDomain NumberField
open scoped TensorProduct
namespace GlobalTheory.HeckeSplitGen
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (F E) in

def intAEF : AddSubgroup (Af F ⊗[F] E) :=
  AddSubgroup.closure {y | ∃ a : Af F, (∀ v : HeightOneSpectrum (𝓞 F), a v ∈ v.adicCompletionIntegers F) ∧
    ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)}
def splitLocF (σ : E →ₐ[F] E) : Set (AEF F E)ˣ :=
  {x | ∃ e, IsSplitIdemF σ e ∧ (e + cAF σ e) * ((x : AEF F E) - 1) = (x : AEF F E) - 1}
variable (F E) in

def modSetF (N : ℕ) : Set (AEF F E)ˣ :=
  {x | infPartF F E (x : AEF F E) = 1 ∧
    (∃ r ∈ intAEF F E, finPartF F E (x : AEF F E) - 1 = (N : Af F ⊗[F] E) * r) ∧
    finPartF F E ((x⁻¹ : (AEF F E)ˣ) : AEF F E) ∈ intAEF F E}
def grpHF (σ : E →ₐ[F] E) (N : ℕ) : Subgroup (AEF F E)ˣ :=
  Subgroup.closure (Set.range (Units.map (incAF F E).toMonoidHom) ∪ splitLocF σ ∪ modSetF F E N)
end GlobalTheory.HeckeSplitGen
end


