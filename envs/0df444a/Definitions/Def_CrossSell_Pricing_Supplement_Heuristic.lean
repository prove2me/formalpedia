-- Prove2me | Definitions.Def_CrossSell_Pricing_Supplement_Heuristic
-- name    : CrossSell_Pricing_Supplement_Heuristic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T02:51:58.583304+00:00
-- url     : https://prove2.me/theorems/7639c203-4d73-4d3b-a0eb-2e48eb18762e
-- title:
--   §4.2, steps 1–3 — printed prefix search and counterexample data
-- statement:
--   Index the N secondary products in weakly decreasing order of r_l-s_l and set T_n to the first n products. For each n choose a main permutation sigma_n sorted by the aggregate markups computed using that particular T_n. The candidate objective is the published true profit
--   $$C(m,n)=\Pi(S_{m,n},T_n,p,r),\qquad 1\le m\le M,\quad1\le n\le N.$$
--   The printed heuristic returns any pair maximizing C over precisely these candidates. The outside sales contribution is evaluated directly by the published profit, so no undefined sigma(0,n) is used. Both printed order conditions are stated for actual main products only: the margin-weighted attractions decrease and the attractions increase with secondary index.
--
--   For the Theorem 5 counterexample the file supplies one main product and three secondary products. Main price is 1, main cost is zero and main attraction is 1/10. Secondary prices and margins are (10,1,1); their attractions after a main purchase are (1,1,1), while their outside attractions are (1/100,1/100,10). Utilities are real logarithms of these positive attractions plus their prices. These are explicit witness data for the refutation, not an alternative demand model.
-- source:
--   Ke & Wang, Cross-Category Retailing Management: Substitution and Complementarity, accepted manuscript (SSRN 3383023), pp. 20, 22–23, secondary margin order and heuristic steps 1–3; p. 23, Theorem 5 (counterexample data supplied locally)

import Mathlib
import Definitions.Def_CrossSell_Pricing_Supplement_Assortment

namespace CrossSell.Pricing.Supplement
open Finset

/-- Secondary products are indexed in decreasing margin order. -/
def secondaryPrefix {N : ℕ} (n : ℕ) : Finset (Fin N) :=
  Finset.univ.filter (fun l => l.val < n)

/-- Actual profit of candidate (m,n), including unpermuted outcome-0 sales. -/
noncomputable def candidateProfit {M N : ℕ} (u c p : Fin M → ℝ) (s r : Fin N → ℝ)
    (v : Option (Fin M) → Fin N → ℝ) (σ : ℕ → Equiv.Perm (Fin M)) (m n : ℕ) : ℝ :=
  profit (offerPrefix (σ n) m) (fun _ => secondaryPrefix n) u c s v p r

/-- The complete printed search, with strictly positive prefix lengths. -/
def PrintedHeuristic {M N : ℕ} (u c p : Fin M → ℝ) (s r : Fin N → ℝ)
    (v : Option (Fin M) → Fin N → ℝ) (σ : ℕ → Equiv.Perm (Fin M)) (m n : ℕ) : Prop :=
  Antitone (fun l => r l - s l) ∧
  (∀ n', 1 ≤ n' → n' ≤ N →
    Sorted (aggMarkup (fun _ => secondaryPrefix n') c s v p r) (σ n')) ∧
  1 ≤ m ∧ m ≤ M ∧ 1 ≤ n ∧ n ≤ N ∧
  ∀ m' n', 1 ≤ m' → m' ≤ M → 1 ≤ n' → n' ≤ N →
    candidateProfit u c p s r v σ m' n' ≤ candidateProfit u c p s r v σ m n

/-- Precisely the two printed conditions, for actual main products only. -/
def PrintedConditions {M N : ℕ} (s r : Fin N → ℝ)
    (v : Option (Fin M) → Fin N → ℝ) : Prop :=
  ∀ i : Fin M, Antitone (fun l => (r l - s l) * Real.exp (v (some i) l - r l)) ∧
    Monotone (fun l => Real.exp (v (some i) l - r l))

/-- A positive-margin witness exposing the omitted outside-outcome conditions. -/
def counterR (l : Fin 3) : ℝ := if l.val = 0 then 10 else 1
noncomputable def counterV : Option (Fin 1) → Fin 3 → ℝ
  | some _, l => counterR l
  | none, l => counterR l + Real.log (if l.val = 2 then 10 else (1 / 100 : ℝ))
noncomputable def counterU (_ : Fin 1) : ℝ := 1 - Real.log 10

end CrossSell.Pricing.Supplement


