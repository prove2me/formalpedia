-- Prove2me | Definitions.Def_CompanionTheory_AutomorphicTheory_HeckeStandardModules_HeckeA
-- name    : CompanionTheory_AutomorphicTheory_HeckeStandardModules_HeckeA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:19:23.917353+00:00
-- url     : https://prove2.me/theorems/3a9bf802-d989-401c-a53c-fa8bbe5cf883
-- title:
--   Hecke A
-- statement:
--   Definitions and structural lemmas for Hecke A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/HeckeStandardModules/HeckeA.lean

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_HeckeActMem
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Heckebasic
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_EvalFg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG Formalism.UG.P
noncomputable section
namespace CompanionTheory.HeckeA
variable {G H W : Type} [Group G] [Group H] [AddCommGroup W] [Module ℂ W] (ι : H →* G) (K : Subgroup H)
def op (φ : H → ℂ) (f : G → W) (g : G) : W := ∑ᶠ c : H ⧸ K, φ c.out • f (g * ι c.out)
def Inv (f : G → W) : Prop := ∀ g, ∀ k ∈ K, f (g * ι k) = f g
variable {K}
section FG
variable {R : Type} [CommRing R] [Algebra R ℂ]
end FG
end CompanionTheory.HeckeA


