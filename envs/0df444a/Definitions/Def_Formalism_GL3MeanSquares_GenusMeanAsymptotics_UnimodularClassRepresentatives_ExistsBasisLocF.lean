-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsBasisLocF
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsBasisLocF
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:40:45.224862+00:00
-- url     : https://prove2.me/theorems/b8931c03-f919-4bc4-ba40-2c326da093c5
-- title:
--   Exists Basis Loc F
-- statement:
--   Definitions and structural lemmas for Exists Basis Loc F, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsBasisLocF.lean

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
namespace Formalism.HermitianLattices.Ext.L3.LocalSpans
variable {K F : Type} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
abbrev sF (K : Type) {F : Type} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra F K]
    (𝔭 : Ideal (𝓞 F)) [𝔭.IsPrime] : Submonoid (𝓞 K) :=
  Algebra.algebraMapSubmonoid (𝓞 K) 𝔭.primeCompl
theorem sF_le (𝔭 : Ideal (𝓞 F)) [𝔭.IsPrime] : sF K 𝔭 ≤ nonZeroDivisors (𝓞 K) :=
  algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul _ 𝔭.primeCompl_le_nonZeroDivisors
abbrev RP (K : Type) {F : Type} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra F K]
    (𝔭 : Ideal (𝓞 F)) [𝔭.IsPrime] : Subalgebra (𝓞 K) K :=
  Localization.subalgebra.ofField K (sF K 𝔭) (sF_le 𝔭)
end Formalism.HermitianLattices.Ext.L3.LocalSpans


