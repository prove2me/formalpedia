-- Prove2me | Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawaC
-- name    : Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawaC
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:49:15.139802+00:00
-- url     : https://prove2.me/theorems/387ca095-d778-42e8-a68b-9d95f373a484
-- title:
--   FIwasawa C
-- statement:
--   Definitions and structural lemmas for FIwasawa C, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/FIwasawaC.lean

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawaB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG Matrix
namespace Formalism.UG.P
section FIwasawaRed
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) {n : ℕ}
def fIwasawaTri (r : ℕ) (M : Matrix (Fin n) (Fin n) L) : Prop :=
  ∀ i j : Fin n, j.val < r → j < i → M i j = 0
def fIwasawaKm (M : Matrix (Fin n) (Fin n) L) : Prop := fIwasawaUn σ M ∧ fIwasawaInt M
end FIwasawaRed
end Formalism.UG.P


