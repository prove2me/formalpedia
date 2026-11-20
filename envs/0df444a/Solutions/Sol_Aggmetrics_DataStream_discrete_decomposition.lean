-- Prove2me | solution 1 for Aggmetrics.DataStream.discrete_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:01:37.441492+00:00
-- url     : https://prove2.me/submissions/2e0df545-8364-433d-b364-6ef9e6b2c972

import Definitions.Def_Aggmetrics_Basic
import Definitions.Def_Aggmetrics_DataStreamTemporal

set_option autoImplicit true
open Finset Matrix
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution {m : ℕ} (ω0 ω1 M0 M1 : Fin m → ℝ) :
    ∑ j, (ω1 j * M1 j - ω0 j * M0 j)
      = ∑ j, ((ω0 j + ω1 j) / 2) * (M1 j - M0 j)
        + ∑ j, (ω1 j - ω0 j) * ((M0 j + M1 j) / 2) := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring
end Aggmetrics.DataStream
