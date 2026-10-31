-- Prove2me | Definitions.Def_SepCostShare_Algorithm
-- name    : SepCostShare_Algorithm
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:25:33.082819+00:00
-- url     : https://prove2.me/theorems/0aba3059-6b83-4d6c-aef2-4ca8e46ac2e4
-- title:
--   Algorithm 1: loop conditions (1), (2), its steps and runs
-- statement:
--   Algorithm 1 transforms a profile $B$ of a matroid game into an enforceable profile. With the current profile $B'$, a resource $e$ satisfies
--
--   * **condition (1)** if $d_{i,e}>\bar\Delta^e_i(B')$ for some $i\in N_e(B')$;
--   * **condition (2)** if $N_e(B')\ne\emptyset$ and $c_e(B')>\sum_{i\in N_e(B')}\bigl(\bar\Delta^e_i(B')-d_{i,e}\bigr)$.
--
--   The while-loop of Line 2 runs as long as some resource $e$ satisfies (1) or (2); it **stops** at $B'$ when none does. For a chosen such $e$:
--
--   1. if (1) holds for some $i\in N_e(B')$ (Line 3), choose $f_i\in\arg\min_{f\in E,\ B'_i+f-e\in\mathcal B_i}\pi^f_i$ (Line 4) and update $B'_i\leftarrow B'_i+f_i-e$ (Line 5);
--   2. otherwise (2) holds (Line 6), and while (2) holds on $e$ (Line 7): pick $i\in N_e(B')$ with $\pi^e_i>\bar\Delta^e_i(B')$ (Line 8), choose $f_i$ as in Line 4 (Line 9) and update $B'_i\leftarrow B'_i+f_i-e$ (Line 10).
--
--   Every choice (of $e$, $i$ and the minimizer $f_i$) is free. A **run** is a sequence of states $s_0,\dots,s_k$, each a profile together with the control point (the test of Line 2, or the loop of Line 7 on a resource $e$), starting at $(B,\text{Line }2)$; every transition performs exactly one exchange. The **iterations of the while-loop of Line 2** are the transitions taken from the test of Line 2.
--
--   **Formalization Note** Condition (2) is tested only on resources used by some player (see the theorems' lists of differences). A transition from Line 2 on a resource that satisfies (2) but not (1) performs Line 6 and the first iteration of the loop of Line 7; after each iteration of that loop control stays in the loop if (2) still holds on $e$ and returns to Line 2 otherwise. Line 8 prints $\pi^i_e$; it is $\pi^e_i$ (as in the proof of Theorem 5).
-- source:
--   Harks, Hoefer, Huber & Surek, Efficient Black-Box Reductions for Separable Cost Sharing, arXiv:1802.10351v1, Algorithm 1, p.7 (conditions (1), (2), Lines 1–10)

import Mathlib
import Definitions.Def_SepCostShare_MatroidGame
import Definitions.Def_SepCostShare_Deviation

namespace SepCostShare

variable {N E : Type*} [Fintype N] [DecidableEq N] [Fintype E] [DecidableEq E]

/-- **Loop condition (1)** of Algorithm 1, arXiv:1802.10351v1, p.7, for resource `e` at profile
`B`: `dᵢ,ₑ > Δ̄ᵉᵢ(B)` for some `i ∈ Nₑ(B)`. -/
def MatroidGame.cond1 (G : MatroidGame N E) (B : N → Finset E) (e : E) : Prop :=
  ∃ i ∈ G.users e B, G.deltaBar B i e < G.d i e

/-- **Loop condition (2)** of Algorithm 1, arXiv:1802.10351v1, p.7, for resource `e` at profile
`B`: `cₑ(B) > Σ_{i∈Nₑ(B)} (Δ̄ᵉᵢ(B) − dᵢ,ₑ)`, tested only for resources with `Nₑ(B) ≠ ∅`.

**Formalization Note.** The restriction to used resources is a correction: as printed, (2) holds
at every unused resource with `cₑ(∅) > 0` and Line 8 must then pick a player from `Nₑ(B) = ∅`. -/
def MatroidGame.cond2 (G : MatroidGame N E) (B : N → Finset E) (e : E) : Prop :=
  (G.users e B).Nonempty ∧
    ∑ i ∈ G.users e B, (G.deltaBar B i e - G.d i e) < G.c e (G.users e B)

/-- The while-loop of Line 2 of Algorithm 1 stops at `B`: no resource satisfies (1) or (2). -/
def MatroidGame.Stopped (G : MatroidGame N E) (B : N → Finset E) : Prop :=
  ∀ e : E, ¬ G.cond1 B e ∧ ¬ G.cond2 B e

/-- `f ∈ arg min_{f∈E, Bᵢ+f−e∈𝓑ᵢ} πᶠᵢ` (Lines 4 and 9 of Algorithm 1, p.7). Any minimizer may be
chosen. -/
def MatroidGame.IsArgmin (G : MatroidGame N E) (B : N → Finset E) (i : N) (e f : E) : Prop :=
  f ∈ G.alts B i e ∧ ∀ g ∈ G.alts B i e, G.pi i f ≤ G.pi i g

/-- One execution of **Lines 3–5** of Algorithm 1 (p.7): a resource `e` and a player `i ∈ Nₑ(B)`
with `dᵢ,ₑ > Δ̄ᵉᵢ(B)` (so `e` satisfies (1)), a minimizer `fᵢ`, and the update
`Bᵢ ← Bᵢ + fᵢ − e`. -/
def MatroidGame.Type1Step (G : MatroidGame N E) (B B' : N → Finset E) : Prop :=
  ∃ e : E, ∃ i ∈ G.users e B, G.deltaBar B i e < G.d i e ∧
    ∃ f : E, G.IsArgmin B i e f ∧ B' = G.swap B i e f

/-- One iteration of the **inner while-loop, Lines 7–10** of Algorithm 1 (p.7) on resource `e`:
(2) holds on `e`; pick `i ∈ Nₑ(B)` with `πᵉᵢ > Δ̄ᵉᵢ(B)` (Line 8), a minimizer `fᵢ` (Line 9), and
update `Bᵢ ← Bᵢ + fᵢ − e` (Line 10). -/
def MatroidGame.InnerStep (G : MatroidGame N E) (e : E) (B B' : N → Finset E) : Prop :=
  G.cond2 B e ∧ ∃ i ∈ G.users e B, G.deltaBar B i e < G.pi i e ∧
    ∃ f : E, G.IsArgmin B i e f ∧ B' = G.swap B i e f

/-- One **exchange step** of Algorithm 1 (p.7) as a transition between states `(B, mode)`. Mode
`none` means control is at the test of Line 2; mode `some e` means control is inside the
while-loop of Line 7 on resource `e`. Every transition performs exactly one exchange
`Bᵢ ← Bᵢ + fᵢ − e`:

* from `(B, none)`: Lines 3–5 for a resource satisfying (1) (`Type1Step`), back to Line 2; or,
  for a resource `e` that satisfies (2) but not (1) (Line 6), the first iteration of the loop of
  Line 7 on `e`;
* from `(B, some e)`: the next iteration of the loop of Line 7 on `e`.

After an iteration of the loop of Line 7 the mode is `some e` if (2) still holds on `e` and
`none` (back to Line 2) otherwise. -/
def MatroidGame.AlgStep (G : MatroidGame N E) :
    (N → Finset E) × Option E → (N → Finset E) × Option E → Prop
  | (B, none), (B', m) =>
      (G.Type1Step B B' ∧ m = none) ∨
        ∃ e : E, ¬ G.cond1 B e ∧ G.InnerStep e B B' ∧
          (G.cond2 B' e → m = some e) ∧ (¬ G.cond2 B' e → m = none)
  | (B, some e), (B', m) =>
      G.InnerStep e B B' ∧ (G.cond2 B' e → m = some e) ∧ (¬ G.cond2 B' e → m = none)

/-- A **run of Algorithm 1** with `k` exchanges from input profile `B` (Line 1: `B′ ← B`): states
`s 0, …, s k` with `s 0 = (B, none)` and `s t → s (t+1)` an `AlgStep` for every `t < k`. -/
def MatroidGame.IsRun (G : MatroidGame N E) (B : N → Finset E)
    (s : ℕ → (N → Finset E) × Option E) (k : ℕ) : Prop :=
  s 0 = (B, none) ∧ ∀ t < k, G.AlgStep (s t) (s (t + 1))

/-- The number of **iterations of the while-loop of Line 2** in the first `k` steps of a run: the
steps taken from a state at Line 2 (each such iteration performs Lines 3–5, or Line 6 and the
first iteration of the loop of Line 7). -/
def MatroidGame.outerIters (_G : MatroidGame N E) (s : ℕ → (N → Finset E) × Option E)
    (k : ℕ) : ℕ :=
  ((Finset.range k).filter fun t => (s t).2 = none).card

end SepCostShare


