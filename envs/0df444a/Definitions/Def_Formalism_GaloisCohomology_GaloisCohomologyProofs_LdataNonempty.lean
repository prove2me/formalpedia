-- Prove2me | Definitions.Def_Formalism_GaloisCohomology_GaloisCohomologyProofs_LdataNonempty
-- name    : Formalism_GaloisCohomology_GaloisCohomologyProofs_LdataNonempty
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:40:59.044258+00:00
-- url     : https://prove2.me/theorems/01753c30-4341-49f8-a77f-15401ec632d2
-- title:
--   Ldata Nonempty
-- statement:
--   Definitions and structural lemmas for Ldata Nonempty, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisCohomology/GaloisCohomologyProofs/LdataNonempty.lean

import Definitions.Def_Formalism_GaloisCohomology_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Representation ReciprocityTheory.Gal Formalism.ConjugateSelfDual
namespace Formalism.GaloisCohomology
section
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  (l : ℕ) [Fact l.Prime]
end
end Formalism.GaloisCohomology


