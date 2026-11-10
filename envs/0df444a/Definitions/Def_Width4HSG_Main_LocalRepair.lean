-- Prove2me | Definitions.Def_Width4HSG_Main_LocalRepair
-- name    : Width4HSG_Main_LocalRepair
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T22:19:25.103273+00:00
-- url     : https://prove2.me/theorems/684c845a-b85e-4ef7-995c-cfa586a48361
-- title:
--   Compatible local repairs, comparative gain and accumulated charge
-- statement:
--   A local repair acts on one interval and its entrance state. Allowed states are live, include the start, and contain each repaired exit. Natural-number charges cover each block’s Hamming edits. Comparative gain is repaired minus unrepaired suffix density from the same entrance and candidate block. The global cost accumulates these charges while following actual repaired exit states in order.
-- source:
--   Krak, Beyond Width-3: Better Hitting Set Generators for Width-4 Read-Once Branching Programs, STOC 2027 submission, p. 30, PDF SHA256 4ef018bd96382f87d7be4ed375c984df83c46ccdc42ab98e0d7d589b27b1c050

import Mathlib
import Definitions.Def_Width4HSG_Main_Checkpoints

noncomputable section
open scoped BigOperators

namespace Width4HSG.Main

def LiveProgram.block {n d : ℕ} (P : LiveProgram n d) (a b : ℕ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => ∃ t : Fin d, a ≤ t.val ∧ t.val < b ∧ P.read t = some i)

def LiveProgram.blockExit {n d : ℕ} (P : LiveProgram n d) (a b : ℕ)
    (s : Fin 3) (z : P.block a b → Bool) : Option (Fin 3) := by
  classical
  exact P.runFrom a b (some s)
    (fun i => if h : i.val ∈ P.block a b then z ⟨i.val,h⟩ else false)

structure LocalRepair {n d : ℕ} (P : LiveProgram n d) (T : CheckpointPartition d) where
  allowed : Fin (T.intervals + 1) → Finset (Fin 3)
  starts : P.start ∈ allowed 0
  repair : (j : Fin T.intervals) → Fin 3 →
    (P.block (T.cut j.castSucc).val (T.cut j.succ).val → Bool) →
    (P.block (T.cut j.castSucc).val (T.cut j.succ).val → Bool)
  charge : (j : Fin T.intervals) → Fin 3 →
    (P.block (T.cut j.castSucc).val (T.cut j.succ).val → Bool) → ℕ
  closes : ∀ j s, s ∈ allowed j.castSucc → ∀ z,
    ∃ v ∈ allowed j.succ,
      P.blockExit (T.cut j.castSucc).val (T.cut j.succ).val s (repair j s z) = some v
  covers : ∀ j s, s ∈ allowed j.castSucc → ∀ z,
    hamming z (repair j s z) ≤ charge j s z

def LocalRepair.gain {n d : ℕ} {P : LiveProgram n d} {T : CheckpointPartition d}
    (R : LocalRepair P T) (j : Fin T.intervals) (s : Fin 3)
    (z : P.block (T.cut j.castSucc).val (T.cut j.succ).val → Bool) : ℝ :=
  P.suffix (T.cut j.succ).val
    (P.blockExit (T.cut j.castSucc).val (T.cut j.succ).val s (R.repair j s z)) -
  P.suffix (T.cut j.succ).val
    (P.blockExit (T.cut j.castSucc).val (T.cut j.succ).val s z)

def LocalRepair.cost {n d : ℕ} {P : LiveProgram n d} {T : CheckpointPartition d}
    (R : LocalRepair P T) (x : P.free → Bool) : ℕ :=
  ((List.finRange T.intervals).foldl (fun acc j =>
    match acc.1 with
    | none => acc
    | some s =>
      let z := fun i : P.block (T.cut j.castSucc).val (T.cut j.succ).val => P.bit x i.val
      (P.blockExit (T.cut j.castSucc).val (T.cut j.succ).val s (R.repair j s z),
       acc.2 + R.charge j s z)) (some P.start, 0)).2

end Width4HSG.Main


