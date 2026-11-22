-- Prove2me | Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Cartan
-- name    : Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Cartan
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:25:13.609942+00:00
-- url     : https://prove2.me/theorems/e7eaf18d-50b6-4f67-8354-b7bea3ca0171
-- title:
--   Cartan
-- statement:
--   Definitions and structural lemmas for Cartan, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Cartan.lean

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
namespace Formalism.UG.P
section Smith
variable {R : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  {n : Type} [Fintype n] [DecidableEq n]
end Smith
section Generic
variable {L : Type} [Field L] (O : Subring L) {n : Type} [Fintype n] [DecidableEq n]
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
end Generic
section Unique
variable {L : Type} [Field L] (O : Subring L) {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
end Unique
section Decomp
variable {L : Type} [Field L] (O : Subring L) {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
end Decomp
section Adic
open IsDedekindDomain NumberField
end Adic
end Formalism.UG.P


