-- Prove2me | solution 1 for Aggmetrics.DataStream.spec_composition_invariant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:28:54.981733+00:00
-- url     : https://prove2.me/submissions/42f02294-3a3e-4bec-9859-284676b28226

import Definitions.Def_Aggmetrics_DataStream
import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamProb

set_option autoImplicit true
open Finset Matrix MeasureTheory ProbabilityTheory
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution {m : ℕ} (π π' : Fin m → ℝ) (c : Fin m → Fin m → ℝ) (j : Fin m)
    (h : ∀ k ∈ univ.erase j, π k / (1 - π j) = π' k / (1 - π' j)) :
    specFormula π c j = specFormula π' c j :=
  Finset.sum_congr rfl (fun k hk => by rw [h k hk])
end Aggmetrics.DataStream
