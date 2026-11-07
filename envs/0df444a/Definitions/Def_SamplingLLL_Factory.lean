-- Prove2me | Definitions.Def_SamplingLLL_Factory
-- name    : SamplingLLL_Factory
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:54:54.302667+00:00
-- url     : https://prove2.me/theorems/a59ca3e8-a019-4a57-b8d2-cfaa472145a9
-- title:
--   The scalar factory: signed experiment, reciprocal coin, packet generator
-- statement:
--   Data for the scalar factory: for update tasks $i$, a budget $B_i$; for each transcript a sign $\epsilon_t$ and an ordered multiset $C_t$ of child types; an executable proposal; and the exact local joint operation. The signed experiment proposes $t$, runs the local operation, and requests a coin for each occurrence in $C_t$; its value is $\epsilon_t B_i$ if all succeed and $0$ otherwise. The reciprocal coin repeats "with probability $\alpha_i=2B_i/(1+B_i)$ continue, else accept"; on continue it runs the experiment $Y_i$ and tosses a coin of bias $(Y_i+B_i)/(2B_i)$, and a failed toss returns false. The packet generator precedes the experiment by an independent $B_i$-coin.
--
--   **Formalization Note** All child coins of an experiment are requested, as the text says ("for each occurrence"), which is the count in the response (7). The toss of bias $(Y_i+B_i)/(2B_i)$ is written by its three cases $0,\tfrac12,1$. Levels stand in for the strict recursion: `coinLevel (k+1)` is built on `coinLevel k`.
-- source:
--   Achlioptas, Counting and Sampling by Local Repair: From the Lovász Local Lemma to Random k-SAT, STOC 2027 submission (manuscript sha256 7a943167…), Appendix A.4, pp.21–22

import Mathlib
import Definitions.Def_SamplingLLL_Primitives

set_option autoImplicit false

open scoped ENNReal

namespace SamplingLLL

open Proc

/-- The data of the scalar factory of Appendix A.4, p.21, for update tasks of type `ι`, transcripts `τ`
and local marks `Mk`: a budget `B_i`, for a transcript its sign `ε_t` and its ordered child types `C_t`,
an executable proposal `q_i` (an outcome carries the exact proposal probability of its transcript;
`none` is `⊥`), and the exact local joint operation (`none` is a rejection).

Source: Achlioptas, STOC 2027 submission (manuscript sha256 7a943167…), Appendix A.4, pp.21–22. -/
structure Factory (ι τ Mk : Type) where
  /-- The budget `B_i`. -/
  budget : ι → ℚ
  /-- The charge for computing the budget. -/
  budgetCost : ι → ℕ
  /-- The sign `ε_t`, in `{1, -1}`. -/
  sgn : τ → ℤ
  /-- The ordered multiset of child types `C_t` of the transcript `t` of `i`. -/
  kids : ι → τ → List ι
  /-- The proposal. -/
  propose : ι → Proc (Option (τ × ℚ))
  /-- The exact local joint operation at a transcript with its proposal probability. -/
  localOp : ι → τ → ℚ → Proc (Option Mk)

namespace Factory

variable {ι τ Mk : Type} (F : Factory ι τ Mk)

/-- Request a coin for each occurrence in the list, **all of them** (p.22: "for each occurrence"). -/
noncomputable def allCoins (coin : ι → Proc Bool) : List ι → Proc Bool
  | [] => pure true
  | j :: l => do
    let b ← coin j
    let b' ← allCoins coin l
    pure (b && b')

/-- The signed experiment of Lemma A.5, proof, p.22: propose; run the exact local operation; request all
child coins, each from `coin`. Its value is `ε_t B_i` on `some (t, mark)` and `0` on `none`. -/
noncomputable def experiment (coin : ι → Proc Bool) (i : ι) : Proc (Option (τ × Mk)) := do
  match ← F.propose i with
  | none => pure none
  | some (t, q) =>
    match ← F.localOp i t q with
    | none => pure none
    | some mark =>
      let ok ← allCoins coin (F.kids i t)
      if ok then pure (some (t, mark)) else pure none

/-- The reciprocal coin of Lemma A.5, proof, p.22, one counted invocation (weight `w i`) of bias
`s_i/(1-r_i)`: repeat "with probability `α_i = 2B_i/(1+B_i)` continue, else accept"; on continue, run the
signed experiment `Y_i` and toss the coin of bias `(Y_i+B_i)/(2B_i)`, which is `0`, `½`, `1` on
`Y_i = -B_i, 0, B_i`; a failed toss returns `false`. -/
noncomputable def coinAt (w : ι → ℕ) (coin : ι → Proc Bool) (i : ι) : Proc Bool := do
  countCall (w i)
  tick (F.budgetCost i)
  let B := F.budget i
  let twoB ← qmul 2 B
  let oneB ← qadd 1 B
  let α ← qdiv twoB oneB
  loop (fun _ : Unit => do
    let go ← ratCoin α
    if go then do
      match ← experiment F coin i with
      | none =>
        let b ← flip
        if b then pure (Sum.inl ()) else pure (Sum.inr false)
      | some (t, _) =>
        if F.sgn t = 1 then pure (Sum.inl ()) else pure (Sum.inr false)
    else pure (Sum.inr true)) ()

/-- The unnormalized packet generator, p.22: an independent `B_i`-coin, then the experiment. -/
noncomputable def generator (coin : ι → Proc Bool) (i : ι) : Proc (Option (τ × Mk)) := do
  tick (F.budgetCost i)
  let b ← ratCoin (F.budget i)
  if b then experiment F coin i else pure none

/-- The reciprocal coins by levels: `level (k+1)` is built on `level k`; `level 0` has mass `0`. Since all
calls have strict type, a coin of rank below `k` is served by `coinLevel w k`. -/
noncomputable def coinLevel (w : ι → ℕ) : ℕ → ι → Proc Bool
  | 0 => fun _ _ => 0
  | k + 1 => coinAt F w (coinLevel w k)

/-- The proposal probability `q_i(t)`, the mass of the proposal on `t`. -/
noncomputable def qOf (i : ι) (t : τ) : ℝ :=
  (probOf (F.propose i) fun o => ∃ r, o = some (t, r)).toReal

/-- `s_i = 1 - B_i`. -/
def sOf (i : ι) : ℝ := 1 - (F.budget i : ℝ)

/-- A child coin with the exact bias `s_j/(1-r_j)`, counted only when its type is `j₀`. A row run on these
coins, with weight `0` for itself, has expected calls equal to its aggregate number of direct type-`j₀`
coin requests. Used only to read the response (7) off the reciprocal coin. -/
noncomputable def stubCoin [DecidableEq ι] (r : ι → ℝ) (j₀ j : ι) : Proc Bool := do
  countCall (if j = j₀ then 1 else 0)
  bernoulli (ENNReal.ofReal (F.sOf j / (1 - r j)))

/-- The value `ε_t B_i` of an outcome of the experiment. -/
noncomputable def signedMass (p : Proc (Option (τ × Mk))) : ℝ :=
  (probOf p fun o => ∃ t mk, o = some (t, mk) ∧ F.sgn t = 1).toReal -
    (probOf p fun o => ∃ t mk, o = some (t, mk) ∧ F.sgn t = -1).toReal

end Factory

end SamplingLLL


