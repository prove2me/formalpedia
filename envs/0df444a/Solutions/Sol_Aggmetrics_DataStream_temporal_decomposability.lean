-- Prove2me | solution 1 for Aggmetrics.DataStream.temporal_decomposability
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:02:38.286777+00:00
-- url     : https://prove2.me/submissions/70f74c75-42a8-4efd-86b4-a5a1495da32a

import Definitions.Def_Aggmetrics_Basic
import Definitions.Def_Aggmetrics_DataStream
import Theorems.Thm_Aggmetrics_weighted_ratio_mixture


set_option autoImplicit true
open Finset MeasureTheory
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution {m : ℕ} (hm : 0 < m) (a b : Fin 4 → ℝ) (v : Fin m → Fin 4 → ℝ)
    (hden : ∀ j, 0 < ∑ i, b i * v j i) :
    (∑ j, ∑ i, a i * v j i) / (∑ j, ∑ i, b i * v j i)
      = ∑ j, ((∑ i, b i * v j i) / ∑ l, ∑ i, b i * v l i)
          * ((∑ i, a i * v j i) / (∑ i, b i * v j i)) :=
  weighted_ratio_mixture hm (fun j => ∑ i, a i * v j i) (fun j => ∑ i, b i * v j i) hden
end Aggmetrics.DataStream
