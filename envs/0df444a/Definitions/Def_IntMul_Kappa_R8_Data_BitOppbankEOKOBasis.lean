-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankEOKOBasis
-- name    : IntMul_Kappa_R8_Data_BitOppbankEOKOBasis
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T17:16:05.933346+00:00
-- url     : https://prove2.me/theorems/6a576d7c-4525-4300-8122-c47eebddd34c
-- title:
--   S0/Si0 invertibility from inhabited densified FB0
-- statement:
--   # Flag-basis invertibility for `ch0O`
--
--   Given inhabited densified `Pnd.FB0`, the Classical.epsilon choices $S_0,S_0^{-1}$ are mutual inverses, so the one-run channel meets `EOKO` hypotheses `hS`/`hSi`.
--
--   **Formalization Note.** Namespace `EOKOBasis`.
-- source:
--   EOKO hS/hSi from FB0

import Mathlib
import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.dupNamespace false

/-! # S0/Si0 invertibility from inhabited densified FB0 -/

namespace IntMul.Kappa.R8.Bit.Oppbank.EOKOBasis

open Matrix
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet

theorem S0_mul_Si0 (h : ∃ S Sinv, FB0 S Sinv) : S0 * Si0 = 1 := by
  have hS : ∃ Sinv, FB0 S0 Sinv :=
    Classical.epsilon_spec (p := fun S : Matrix (Fin 529) Pr23 ℚ => ∃ Sinv, FB0 S Sinv) h
  have hFB : FB0 S0 Si0 :=
    Classical.epsilon_spec (p := fun Sinv : Matrix Pr23 (Fin 529) ℚ => FB0 S0 Sinv) hS
  exact hFB.1

theorem Si0_mul_S0 (h : ∃ S Sinv, FB0 S Sinv) : Si0 * S0 = 1 := by
  have hS : ∃ Sinv, FB0 S0 Sinv :=
    Classical.epsilon_spec (p := fun S : Matrix (Fin 529) Pr23 ℚ => ∃ Sinv, FB0 S Sinv) h
  have hFB : FB0 S0 Si0 :=
    Classical.epsilon_spec (p := fun Sinv : Matrix Pr23 (Fin 529) ℚ => FB0 S0 Sinv) hS
  exact hFB.2.1

theorem ch0O_hS (h : ∃ S Sinv, FB0 S Sinv) : (toNB ch0O).S * (toNB ch0O).Si = 1 := by
  change S0 * Si0 = 1
  exact S0_mul_Si0 h

theorem ch0O_hSi (h : ∃ S Sinv, FB0 S Sinv) : (toNB ch0O).Si * (toNB ch0O).S = 1 := by
  change Si0 * S0 = 1
  exact Si0_mul_S0 h

end IntMul.Kappa.R8.Bit.Oppbank.EOKOBasis


