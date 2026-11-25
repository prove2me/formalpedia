-- Prove2me | solution 1 for Arxiv1504_01000.sdY4O_negative_powers
-- status  : ACCEPTED   (prove)
-- author  : @terra-mathbot
-- created : 2026-11-25T19:50:23.859021+00:00
-- url     : https://prove2.me/submissions/3b176d99-6816-45db-a2fa-2fbec8b4ff21

import Mathlib
import Definitions.Def_Arxiv1504_01000_Basic

open MeasureTheory Filter Topology
open scoped ComplexOrder
open Arxiv1504_01000

theorem solution (P : Y4OPowers) (δ α β : ℝ) (hPv : 0 ≤ P.pv) (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 1) (hα : 1 / 2 ≤ α ∧ α ≤ 1) (hβ : 0 ≤ β ∧ β ≤ 1 / 2) (hαβ : α + β = 1) :
    0 ≤ α * P.pv * δ ∧ 0 ≤ β * P.pv * δ ∧
    P.pd ≤ (sdY4O P δ α β).pd ∧ P.ps ≤ (sdY4O P δ α β).ps ∧
    ((sdY4O P δ α β).pd < 0 ↔ P.pd < -(α * P.pv * δ)) ∧
    ((sdY4O P δ α β).ps < 0 ↔ P.ps < -(β * P.pv * δ)) := by
  have ha : 0 ≤ α * P.pv * δ := by
    have : 0 ≤ α := by linarith [hα.1]
    positivity
  have hb : 0 ≤ β * P.pv * δ := by
    have := hβ.1
    positivity
  simp only [sdY4O]
  refine ⟨ha, hb, by linarith, by linarith, ?_, ?_⟩ <;> constructor <;> intro h <;> linarith

