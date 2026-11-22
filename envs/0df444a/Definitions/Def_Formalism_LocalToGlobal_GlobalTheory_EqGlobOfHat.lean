-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_EqGlobOfHat
-- name    : Formalism_LocalToGlobal_GlobalTheory_EqGlobOfHat
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:43:48.793135+00:00
-- url     : https://prove2.me/theorems/7b328269-09bd-40b7-b59d-c132fcbb3856
-- title:
--   Eq Glob Of Hat
-- statement:
--   Definitions and structural lemmas for Eq Glob Of Hat, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/EqGlobOfHat.lean

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsDual
import Definitions.Def_Formalism_LocalRingCardinality_DataLevel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
namespace Formalism.L2.GlobalTheoryTheory.Comp
open Formalism.UG Formalism.UG.CS Formalism.UG.P Formalism.BasicNotions
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ιA" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
def IsLat (Λ : Submodule (𝓞 E) (n → E)) : Prop :=
  Module.Finite (𝓞 E) Λ ∧ Submodule.span E (Λ : Set (n → E)) = ⊤
variable (F) in

abbrev hat (Λ : Submodule (𝓞 E) (n → E)) : Submodule 𝒮 (n → 𝒜) :=
  latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ
def dl (σ : E →ₐ[F] E) (J : Matrix n n E) (Λ : Submodule (𝓞 E) (n → E)) : Submodule (𝓞 E) (n → E) :=
  Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J Λ)
end Formalism.L2.GlobalTheoryTheory.Comp
end


