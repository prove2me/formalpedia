-- Prove2me | Definitions.Def_RiemannMasullo_RapidDecaySequenceSubmodule
-- name    : RiemannMasullo_RapidDecaySequenceSubmodule
-- status  : Definition
-- author  : @dga471
-- created : 2026-11-21T02:36:24.996486+00:00
-- url     : https://prove2.me/theorems/ca32902e-6227-476b-9c8b-8d84dddb2fbd
-- title:
--   The submodule of rapidly decreasing complex lattice sequences
-- statement:
--   Complex lattice sequences having finite weighted absolute sums of every order form a submodule under pointwise operations.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L537-L541

import Theorems.Thm_RiemannMasullo_rapidDecaySequenceSubmodule_zero_mem
import Theorems.Thm_RiemannMasullo_rapidDecaySequenceSubmodule_add_mem
import Theorems.Thm_RiemannMasullo_rapidDecaySequenceSubmodule_smul_mem
open scoped ENNReal
noncomputable section
namespace RiemannMasullo
def rapidDecaySequenceSubmodule (r : ℕ) : Submodule ℂ ((Fin r → ℤ) → ℂ) where
  carrier := {s | ∀ j, rapidDecaySequenceBound j s < ⊤}
  zero_mem' := rapidDecaySequenceSubmodule_zero_mem
  add_mem' := rapidDecaySequenceSubmodule_add_mem
  smul_mem' := rapidDecaySequenceSubmodule_smul_mem
end RiemannMasullo


