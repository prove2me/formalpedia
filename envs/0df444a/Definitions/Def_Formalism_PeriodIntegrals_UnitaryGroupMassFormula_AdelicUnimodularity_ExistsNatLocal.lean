-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_ExistsNatLocal
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_ExistsNatLocal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:30:42.323231+00:00
-- url     : https://prove2.me/theorems/fcbd4f12-47c6-4285-88ab-65fc15258f04
-- title:
--   Exists Nat Local
-- statement:
--   Definitions and structural lemmas for Exists Nat Local, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnimodularity/ExistsNatLocal.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.WAU.B
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
variable {F : Type} [Field F] [NumberField F]
theorem exists_close (v : HeightOneSpectrum (𝓞 F)) (c : F) (x : v.adicCompletion F) :
    ∃ k : F, algebraMap F (v.adicCompletion F) c * (x - algebraMap F (v.adicCompletion F) k) ∈
      v.adicCompletionIntegers F := by
  have hopen : IsOpen {y : v.adicCompletion F |
      algebraMap F (v.adicCompletion F) c * (x - y) ∈ v.adicCompletionIntegers F} :=
    (Valued.isOpen_valuationSubring (v.adicCompletion F)).preimage
      (continuous_const.mul (continuous_const.sub continuous_id))
  obtain ⟨k, hk⟩ := (denseRange_algebraMap F v).exists_mem_open hopen ⟨x, by simp⟩
  exact ⟨k, hk⟩
abbrev Bad (F : Type) [Field F] [NumberField F] (M : ℕ) : Set (HeightOneSpectrum (𝓞 F)) :=
  HeightOneSpectrum.Support (𝓞 F) ((M : F)⁻¹)
def cls (M : ℕ) (a : FiniteAdeleRing (𝓞 F) F) : Bad F M → F :=
  fun v => (exists_close v.1 ((M : F)⁻¹) (a v.1)).choose
end PI.WAU.B


