-- Prove2me | Definitions.Def_Aggmetrics_DataStreamEviction
-- name    : Aggmetrics_DataStreamEviction
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T10:22:28.165439+00:00
-- url     : https://prove2.me/theorems/1b3899aa-40d7-4011-8c42-332b6e1e19d2
-- title:
--   Data Stream Eviction
-- statement:
--   Definitions and structural lemmas for Data Stream Eviction, from Ronaldo C. Prati and the Aggmetrics contributors's pinned Aggmetrics: data-stream metric aggregation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamEviction.lean

import Definitions.Def_Aggmetrics_DataStream
import Definitions.Def_Aggmetrics_DataStreamDelay
set_option autoImplicit true
open Finset Matrix
open scoped Classical
namespace Aggmetrics.DataStream
noncomputable def algStateE {m : ℕ} (α ε : ℝ) (y yt p : ℕ → Fin m → ℝ) (aud : ℕ → Prop)
    (arr : ℕ → ℕ) : ℕ → Matrix (Fin m) (Fin m) ℝ
  | 0 => 0
  | n + 1 =>
      (α • algStateE α ε y yt p aud arr n + (1 - α) • outer (yt n) (p n))
        + ∑ k ∈ (range (n + 1)).filter
            (fun k => aud k ∧ arr k = n + 1 ∧ (k = n ∨ ε ≤ fadeWeight α n k)),
            fadeWeight α (n + 1) k • (outer (y k) (p k) - outer (yt k) (p k))
def discarded (α ε : ℝ) (aud : ℕ → Prop) (arr : ℕ → ℕ) (n k : ℕ) : Prop :=
  aud k ∧ arr k ≤ n ∧ k + 1 ≠ arr k ∧ fadeWeight α (arr k - 1) k < ε
noncomputable def lostState {m : ℕ} (α ε : ℝ) (y yt p : ℕ → Fin m → ℝ) (aud : ℕ → Prop)
    (arr : ℕ → ℕ) (n : ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  ∑ k ∈ range n, if discarded α ε aud arr n k then
    fadeWeight α n k • (outer (y k) (p k) - outer (yt k) (p k)) else 0
end Aggmetrics.DataStream


