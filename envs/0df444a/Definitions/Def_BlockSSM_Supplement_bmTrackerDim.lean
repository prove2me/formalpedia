-- Prove2me | Definitions.Def_BlockSSM_Supplement_bmTrackerDim
-- name    : BlockSSM_Supplement_bmTrackerDim
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:01:44.378897+00:00
-- url     : https://prove2.me/theorems/8b2b039d-2139-4d48-a52d-fc93cda78b19
-- title:
--   Bounded-margin trackers and $n^{\mathrm{bm}}_b(G)$
-- statement:
--   Let $T$ be a one-layer tracker of a group $G$ (Definition 1), with word maps $F_s$, start state $h_0$ and running products $\pi(s)=g_T\cdots g_1$. The tracker has **bounded margin** if its reachable set $R=\{F_s(h_0)\}$ is bounded and there is $\varepsilon>0$ with
--   $$
--   \pi(s)\neq\pi(t)\ \Longrightarrow\ \|F_s(h_0)-F_t(h_0)\|\ge\varepsilon\qquad\text{for all words }s,t .
--   $$
--   The reachable set need not be finite. The **bounded-margin dimension** $n^{\mathrm{bm}}_b(G)$ is the least hidden dimension of a tracker with blocks of size at most $b$ whose decoder tracks $G$ and which has bounded margin, and $\infty$ if there is none.
--
--   This replaces finite reachability by a robustness condition; Theorem 12 shows that it gives the same dimension.
--
--   **Formalization Note** Boundedness and the margin use the Euclidean norm; since all norms on $\mathbb C^n$ are equivalent and $\varepsilon$ is existential, any norm gives the same notion. The minimum is an infimum in $\mathbb N\cup\{\infty\}$.
-- source:
--   C. Geng, The State Complexity of Block-Diagonal State Space Models, STOC 2027 submission manuscript (sha256 f9071794…), Definition 11, p.5 (PDF p.6)

import Mathlib
import Definitions.Def_BlockSSM_Tracker_Tracks
import Definitions.Def_BlockSSM_Supplement_l2dist

universe u

namespace BlockSSM.Supplement

open BlockSSM

/-- **Bounded margin.** Geng, *The State Complexity of Block-Diagonal State Space Models*, STOC 2027 submission manuscript (sha256 f9071794…), Definition 11, p.5 (PDF p.6): "A tracker has bounded margin if R is
bounded and some ε > 0 satisfies π(s) ≠ π(t) ⟹ ‖F_s(h₀) − F_t(h₀)‖ ≥ ε."

**Formalization Note.** `R = {F_s(h₀)}` is bounded in the Euclidean norm `l2norm`, and the
margin is measured with the Euclidean distance `l2dist` (all norms on `ℂⁿ` are equivalent and
`ε` is existential, so the choice of norm does not change the notion). The reachable set need
not be finite. -/
def HasBoundedMargin {G : Type u} [Group G] {b : ℕ∞} (T : Tracker G b) : Prop :=
  (∃ C : ℝ, ∀ s : List G, l2norm (T.wordMap s T.h₀) ≤ C) ∧
  ∃ ε : ℝ, 0 < ε ∧ ∀ s t : List G, wordProd s ≠ wordProd t →
    ε ≤ l2dist (T.wordMap s T.h₀) (T.wordMap t T.h₀)

/-- **The bounded-margin dimension `n^bm_b(G)`.** Geng, *The State Complexity of Block-Diagonal State Space Models*, STOC 2027 submission manuscript (sha256 f9071794…), Definition 11, p.5 (PDF p.6): "Let n^bm_b(G)
denote its minimum dimension": the least hidden dimension of a tracker (Definition 1) whose decoder
tracks `G` and which has bounded margin.

**Formalization Note.** The infimum is taken in `ℕ∞` (`⊤` when no such tracker exists). The
tracker is not required to be finite-state. -/
noncomputable def bmTrackerDim (G : Type u) [Group G] (b : ℕ∞) : ℕ∞ :=
  sInf {D : ℕ∞ | ∃ T : Tracker G b, T.Tracks ∧ HasBoundedMargin T ∧ D = (T.hiddenDim : ℕ∞)}

end BlockSSM.Supplement


