-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_BlockActions_FiniteAdeleRingNontrivial
-- name    : Formalism_LocalToGlobal_GlobalTheory_BlockActions_FiniteAdeleRingNontrivial
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:16:34.868809+00:00
-- url     : https://prove2.me/theorems/d64535d7-279f-4a7e-8bd5-08111477fffd
-- title:
--   Finite Adele Ring Nontrivial
-- statement:
--   Definitions and structural lemmas for Finite Adele Ring Nontrivial, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/BlockActions/FiniteAdeleRingNontrivial.lean

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_BlockActions_LatSOfMem
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_InclusionInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain Formalism.UG
namespace Formalism.L2.GlobalTheoryTheory.Br
section Proof
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ι" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
end Proof
end Formalism.L2.GlobalTheoryTheory.Br


