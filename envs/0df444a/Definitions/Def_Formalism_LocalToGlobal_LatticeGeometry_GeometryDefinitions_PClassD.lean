-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_GeometryDefinitions_PClassD
-- name    : Formalism_LocalToGlobal_LatticeGeometry_GeometryDefinitions_PClassD
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T12:33:19.616157+00:00
-- url     : https://prove2.me/theorems/2967983d-1424-4f41-b135-5bb1020aa8f6
-- title:
--   PClass D
-- statement:
--   Definitions and structural lemmas for PClass D, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/LatticeGeometry/GeometryDefinitions/PClassD.lean

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AdelstabL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain Formalism.UG Formalism.UG.P
namespace Formalism.L2.Geo.Def.PC
section LG
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]
local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
abbrev SV (E : Type) [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) :
    Subring (E ⊗[F] v.adicCompletion F) :=
  tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring
abbrev latA (Λ : Submodule (𝓞 E) (n → E)) : Submodule 𝒮 (n → 𝒜) := latS (F := F) 𝔸 𝒮 Λ
abbrev latV (v : HeightOneSpectrum (𝓞 F)) (Λ : Submodule (𝓞 E) (n → E)) :
    Submodule (SV E v) (n → E ⊗[F] v.adicCompletion F) := latS (F := F) (v.adicCompletion F) (SV E v) Λ
end LG
end Formalism.L2.Geo.Def.PC


