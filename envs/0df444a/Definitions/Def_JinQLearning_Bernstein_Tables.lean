-- Prove2me | Definitions.Def_JinQLearning_Bernstein_Tables
-- name    : JinQLearning_Bernstein_Tables
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T14:34:09.030372+00:00
-- url     : https://prove2.me/theorems/5e6dd156-5dee-47e2-ab35-7a481f7916b2
-- title:
--   Online Q-learning table update and chronological replay
-- statement:
--   Initialize every Q entry to H and each triple's observation list to empty. Its length, sum and sum of squares encode the count and raw accumulators. The clipped value at a nonterminal stage is min{H,max_a Q_h(x,a)} and the terminal value is zero. On observing successor y at (h,x,a), record the current next-stage clipped value z, compute the bonus with z appended, and replace just Q_h(x,a) by (1-alpha_t)Q_h(x,a)+alpha_t[r_h(x,a)+z+b_t]. All other entries and observation lists are preserved. An episode stores its played Markov policy and H+1 states. Its updates run in increasing stage order, and replay folds completed episodes from oldest to newest. A snapshot replays only episodes strictly before k. The extra historical lists preserve exactly the accumulators of Algorithm 2 without asserting its storage bound. Next-stage values in a visit are recorded once, never retrospectively recomputed.
-- source:
--   Jin, Allen-Zhu, Bubeck & Jordan, Is Q-learning Provably Efficient?, arXiv:1807.03765v1, pp. 5, 8, 15–16, equations (4.1), (C.1)–(C.3), Algorithm 2.

import Definitions.Def_JinQLearning_Bernstein_Values
import Definitions.Def_JinQLearning_Bernstein_Bonus

open scoped BigOperators
noncomputable section

namespace JinQLearning.Bernstein

/-- Online Q entries and the observed values at each triple, oldest first.
Counts, μ, σ and previous β are computed from these lists without changing any update. -/
structure Tables (S A H : ℕ) where
  Q : Fin H → Fin S → Fin A → ℝ
  observations : Fin H → Fin S → Fin A → List ℝ

variable {S A H : ℕ} [NeZero A]

def initialTables : Tables S A H := ⟨fun _ _ _ => H, fun _ _ _ => []⟩

def tableValue (q : Tables S A H) (h : ℕ) (x : Fin S) : ℝ :=
  if hh : h < H then min (H : ℝ) (actionMax (q.Q ⟨h, hh⟩ x)) else 0

def visitBonus (q : Tables S A H) (c₁ c₂ ℓ : ℝ)
    (h : Fin H) (x : Fin S) (a : Fin A) (y : Fin S) : ℝ :=
  bonus S A H c₁ c₂ ℓ (q.observations h x a) (tableValue q (h.val + 1) y)

/-- One actual observation, followed by the single visited-entry update. -/
def update (M : Model S A H) (c₁ c₂ ℓ : ℝ) (q : Tables S A H)
    (h : Fin H) (x : Fin S) (a : Fin A) (y : Fin S) : Tables S A H := by
  classical
  let z := tableValue q (h.val + 1) y
  let α := VLearning.CCE.lr H ((q.observations h x a).length + 1)
  let b := bonus S A H c₁ c₂ ℓ (q.observations h x a) z
  exact ⟨fun h' x' a' => if h' = h ∧ x' = x ∧ a' = a then
      (1 - α) * q.Q h x a + α * (reward M h x a + z + b) else q.Q h' x' a',
    fun h' x' a' => if h' = h ∧ x' = x ∧ a' = a then
      q.observations h x a ++ [z] else q.observations h' x' a'⟩

abbrev Episode (S A H : ℕ) := Policy S A H × (Fin (H + 1) → Fin S)
abbrev Path (S A H K : ℕ) := Fin K → Episode S A H

def episodeAction (e : Episode S A H) (h : Fin H) : Fin A := e.1 h (e.2 h.castSucc)

/-- Sequential updates in increasing stage order. -/
def episodeUpdate (M : Model S A H) (c₁ c₂ ℓ : ℝ) (q : Tables S A H)
    (e : Episode S A H) : Tables S A H :=
  (List.finRange H).foldl (fun q h =>
    update M c₁ c₂ ℓ q h (e.2 h.castSucc) (episodeAction e h) (e.2 h.succ)) q

/-- Deterministic replay of exactly the previous completed episodes. -/
def replay (M : Model S A H) (c₁ c₂ ℓ : ℝ) (past : List (Episode S A H)) : Tables S A H :=
  past.foldl (episodeUpdate M c₁ c₂ ℓ) initialTables

def pastEpisodes {K : ℕ} (ω : Path S A H K) (k : ℕ) : List (Episode S A H) :=
  (List.ofFn ω).take k

def snapshot {K : ℕ} (M : Model S A H) (c₁ c₂ ℓ : ℝ) (ω : Path S A H K)
    (k : ℕ) : Tables S A H := replay M c₁ c₂ ℓ (pastEpisodes ω k)

end JinQLearning.Bernstein


