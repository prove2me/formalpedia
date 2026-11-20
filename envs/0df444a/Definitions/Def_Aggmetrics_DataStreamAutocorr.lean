-- Prove2me | Definitions.Def_Aggmetrics_DataStreamAutocorr
-- name    : Aggmetrics_DataStreamAutocorr
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T10:28:50.548157+00:00
-- url     : https://prove2.me/theorems/457fac35-c615-4043-a434-779c046c5436
-- title:
--   Data Stream Autocorr
-- statement:
--   Definitions and structural lemmas for Data Stream Autocorr, from Ronaldo C. Prati and the Aggmetrics contributors's pinned Aggmetrics: data-stream metric aggregation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamAutocorr.lean

import Definitions.Def_Aggmetrics_DataStreamDelay
set_option autoImplicit true
open Finset ProbabilityTheory MeasureTheory Filter Topology
namespace Aggmetrics.DataStream
noncomputable def covSum (ρ : ℕ → ℝ) (α : ℝ) (t : ℕ) : ℝ :=
  ∑ i ∈ range t, ∑ j ∈ range t,
    fadeWeight α t i * fadeWeight α t j * ρ (Int.natAbs ((i : ℤ) - j))
noncomputable def lagSum (ρ : ℕ → ℝ) (α : ℝ) (t : ℕ) : ℝ :=
  ∑ d ∈ range t, (1 - α) * α ^ d * ρ (d + 1)
noncomputable def einf (ρ : ℕ → ℝ) (α : ℝ) : ℝ := ∑' d : ℕ, (1 - α) * α ^ d * ρ (d + 1)
noncomputable def kappaFactor (ρ : ℕ → ℝ) (α : ℝ) : ℝ := 1 + 2 * ∑' d : ℕ, α ^ (d + 1) * ρ (d + 1)
noncomputable def kappaVar (ρ : ℕ → ℝ) (α : ℝ) : ℝ := (1 - α) / (1 + α) * kappaFactor ρ α
end Aggmetrics.DataStream


