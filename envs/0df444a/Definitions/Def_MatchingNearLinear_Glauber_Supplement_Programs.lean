-- Prove2me | Definitions.Def_MatchingNearLinear_Glauber_Supplement_Programs
-- name    : MatchingNearLinear_Glauber_Supplement_Programs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:54:13.135612+00:00
-- url     : https://prove2.me/theorems/de9a6963-d5f2-4261-9b73-921c743094a7
-- title:
--   Input layouts and outputs of the matching programs
-- statement:
--   The input of the sampler and of the counter is placed in memory one value per cell: the words $n$ and $m$, the real $\varepsilon$, then for each edge $e=0,\dots,m-1$ the words $u_e,v_e$ (its endpoints) and the real $\lambda_e$. The input of the GD simulator is the words $n,m,N$, the same edge list with activities, the indicator word of each edge in the starting matching $M_0$, and the update tape $(e_s,B_s)$, $s=1,\dots,N$, as words.
--
--   A program outputs an edge set $S$ by holding in output cells $0,\dots,m-1$ the indicator words $\mathbf 1\{e\in S\}$, and a real $x$ by holding it in output cell $0$. The **output law** of a matching-valued program assigns to $S$ the probability, over the program's own random choices, that it halts with output $S$.
--
--   **Formalization Note** Fixed-width cells mean no variable-length decoding is needed (§2.3).
-- source:
--   Tianshun Miao, Yitong Yin, Sampling Matchings in Near-linear Time, STOC 2027 submission #444 (October 2026), §2.3, printed p. 9 (PDF p. 11); §5.1, printed p. 22 (PDF p. 24); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/444.pdf

import Mathlib
import Definitions.Def_MatchingNearLinear_Glauber_Supplement_CREW
import Definitions.Def_MatchingNearLinear_Glauber_Supplement_Peeling

set_option autoImplicit false

/-!
# Input layouts and outputs of the matching programs

Miao–Yin, *Sampling Matchings in Near-linear Time*, STOC 2027 submission #444, §2.3
(printed p. 9, PDF p. 11): the input is the labeled edge list with its activities, placed in
memory one value per cell, so no variable-length decoding is needed.
-/

namespace MatchingNearLinear.Glauber.Supplement

open scoped BigOperators
noncomputable section
open Classical

open MatchingNearLinear.Glauber
open CREW

/-- The labeled edge list with activities: cells `u_e, v_e, λ_e` for `e = 0,…,m-1`. -/
def edgeCells {n m : ℕ} (G : Input n m) (lam : Fin m → ℝ) : List Cell :=
  (List.finRange m).flatMap fun e => [.word (G.u e).val, .word (G.v e).val, .num (lam e)]

/-- Input of the sampler and of the counter: `n, m, ε`, then the edge list with activities. -/
def graphInput {n m : ℕ} (G : Input n m) (lam : Fin m → ℝ) (ε : ℝ) : List Cell :=
  [.word n, .word m, .num ε] ++ edgeCells G lam

/-- Input of the GD simulator: `n, m, N`, the edge list with activities, the indicator of the
starting matching on each edge, then the update tape `(e_s, B_s)`, `s = 1,…,N`. -/
def simulationInput {n m N : ℕ} (G : Input n m) (lam : Fin m → ℝ) (M0 : Config m)
    (tape : Fin N → Fin m × Bool) : List Cell :=
  [.word n, .word m, .word N] ++ edgeCells G lam ++
    (List.finRange m).map (fun e => .word (if e ∈ M0 then 1 else 0)) ++
    (List.finRange N).flatMap fun s =>
      [.word (tape s).1.val, .word (if (tape s).2 then 1 else 0)]

/-- Output cells `0,…,m-1` hold the indicator words of the edge set `S`. -/
def OutputsConfig {R : ℕ} (m : ℕ) (c : Configuration R) (S : Config m) : Prop :=
  ∀ e : Fin m, c.result e.val = .word (if e ∈ S then 1 else 0)

/-- Output cell `0` holds the real `x`. -/
def OutputsReal {R : ℕ} (c : Configuration R) (x : ℝ) : Prop := c.result 0 = .num x

/-- The output law of a matching-valued program: the probability, over the program's own
random choices, that it halts with output `S`. -/
def configLaw (P : Program) (cap : ℕ) (input : List Cell) (m : ℕ) (S : Config m) : ℝ :=
  prob P cap input (fun _ c => OutputsConfig m c S)

end

end MatchingNearLinear.Glauber.Supplement


