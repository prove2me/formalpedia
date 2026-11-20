-- Prove2me | Definitions.Def_Aggmetrics_DataStreamDelay
-- name    : Aggmetrics_DataStreamDelay
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T10:17:05.34018+00:00
-- url     : https://prove2.me/theorems/1bb2ceb4-23dc-49a7-83c7-c56def073bc4
-- title:
--   Data Stream Delay
-- statement:
--   Definitions and structural lemmas for Data Stream Delay, from Ronaldo C. Prati and the Aggmetrics contributors's pinned Aggmetrics: data-stream metric aggregation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamDelay.lean

import Definitions.Def_Aggmetrics_DataStreamTemporal
set_option autoImplicit true
open Finset Matrix MeasureTheory
namespace Aggmetrics.DataStream
noncomputable def defect {m : ℕ} (T : ℝ → ℝ → ℝ) (yt p : Fin m → ℝ) : ℝ :=
  ∑ b, |∑ a, T (yt a) (p b) - p b| + ∑ a, |∑ b, T (yt a) (p b) - yt a|
noncomputable def softEx : Fin 3 → ℝ := ![1 / 8, 1 / 8, 3 / 4]
noncomputable def unified {m n : ℕ} (w O : Fin n → ℝ) (y yt p : Fin n → Fin m → ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  ∑ k, (O k * w k) • outer (y k) (p k) + ∑ k, ((1 - O k) * w k) • outer (yt k) (p k)
open scoped Classical in
/-- Label vector of instance `k` in the state after `n` instances: the verified label if the
instance is audited and its label has arrived (`arr k ≤ n`), the stand-in otherwise. -/
noncomputable def zvec {m : ℕ} (y yt : ℕ → Fin m → ℝ) (aud : ℕ → Prop) (arr : ℕ → ℕ)
    (n k : ℕ) : Fin m → ℝ :=
  if aud k ∧ arr k ≤ n then y k else yt k
open scoped Classical in
/-- Algorithm 1 with exponential fading and no eviction. At step `n + 1` it decays the state,
credits the stand-in of the new instance `n` and, for every audited instance whose label arrives
at this step, swaps the stand-in for the verified term. -/
noncomputable def algState {m : ℕ} (α : ℝ) (y yt p : ℕ → Fin m → ℝ) (aud : ℕ → Prop)
    (arr : ℕ → ℕ) : ℕ → Matrix (Fin m) (Fin m) ℝ
  | 0 => 0
  | n + 1 =>
      (α • algState α y yt p aud arr n + (1 - α) • outer (yt n) (p n))
        + ∑ k ∈ (range (n + 1)).filter (fun k => aud k ∧ arr k = n + 1),
            fadeWeight α (n + 1) k • (outer (y k) (p k) - outer (yt k) (p k))
def active {m : ℕ} (u : Fin m → Bool) : ℕ := (univ.filter fun j => u j = true).card
noncomputable def macroExclude {m : ℕ} (u : Fin m → Bool) (v : Fin m → ℝ) : Option ℝ :=
  if active u = 0 then none else some ((∑ j, if u j = true then v j else 0) / (active u : ℝ))
noncomputable def macroZero {m : ℕ} (u : Fin m → Bool) (v : Fin m → ℝ) : Option ℝ :=
  some ((∑ j, if u j = true then v j else 0) / (m : ℝ))
noncomputable def macroNan {m : ℕ} (u : Fin m → Bool) (v : Fin m → ℝ) : Option ℝ :=
  if ∀ j, u j = true then some ((∑ j, v j) / (m : ℝ)) else none
def perClass (policy : String) {m : ℕ} (u : Fin m → Bool) (v : Fin m → ℝ) (j : Fin m) :
    Option ℝ :=
  if u j = true then some (v j) else
    if policy = "zero" then some 0 else if policy = "one" then some 1 else none
end Aggmetrics.DataStream


