-- Prove2me | Definitions.Def_Width4HSG_Main_ROBP
-- name    : Width4HSG_Main_ROBP
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T22:17:09.200838+00:00
-- url     : https://prove2.me/theorems/e3c32ffd-132a-49db-9366-06894f581786
-- title:
--   Definition 1.1 and Definition 1.3 — ordered ROBPs and hitting
-- statement:
--   An ordered deterministic width-w length-n branching program has a start state, a transition at each input position, and a final acceptance label. States use Fin w; smaller layers are padded by unreachable states. The input is read once in its original order. Density is uniform acceptance probability. An ε-HSG hits every function in its class whose density is strictly greater than ε.
-- source:
--   Krak, Beyond Width-3: Better Hitting Set Generators for Width-4 Read-Once Branching Programs, STOC 2027 submission, p. 3, PDF SHA256 4ef018bd96382f87d7be4ed375c984df83c46ccdc42ab98e0d7d589b27b1c050

import Mathlib
import Definitions.Def_Width4HSG_Main_FiniteCube

noncomputable section
open scoped BigOperators

namespace Width4HSG.Main

structure ROBP (w n : ℕ) where
  start : Fin w
  step : Fin n → Fin w → Bool → Fin w
  accept : Fin w → Bool

def ROBP.state {w n : ℕ} (P : ROBP w n) (x : Bits n) (t : ℕ) : Fin w :=
  ((List.finRange n).filter (fun i => i.val < t)).foldl
    (fun q i => P.step i q (x i)) P.start

def ROBP.eval {w n : ℕ} (P : ROBP w n) (x : Bits n) : Bool :=
  P.accept (P.state x n)

def density {n : ℕ} (f : Bits n → Bool) : ℝ := average (fun x => indicator (f x))

def Hits {n : ℕ} (H : Set (Bits n)) (f : Bits n → Bool) : Prop :=
  ∃ x ∈ H, f x = true

def IsHSG {n s : ℕ} (F : Set (Bits n → Bool)) (ε : ℝ)
    (G : Bits s → Bits n) : Prop :=
  ∀ f ∈ F, ε < density f → ∃ y, f (G y) = true

def widthClass (w n : ℕ) : Set (Bits n → Bool) :=
  {f | ∃ P : ROBP w n, P.eval = f}

end Width4HSG.Main


