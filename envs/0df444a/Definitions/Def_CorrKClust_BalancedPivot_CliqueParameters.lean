-- Prove2me | Definitions.Def_CorrKClust_BalancedPivot_CliqueParameters
-- name    : CorrKClust_BalancedPivot_CliqueParameters
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:43:20.338231+00:00
-- url     : https://prove2.me/theorems/f9d8a691-c950-4e2b-b639-567dbd788972
-- title:
--   Sorted clique sizes and the parameters s, r, a
-- statement:
--   For a multiset $w$ of positive integer clique sizes, sort it as $w_1\ge\cdots\ge w_q$. Put $s=\sum_{i>k}w_i$. When $q>k\ge1$, $r$ is the least integer in $\{0,\ldots,k-1\}$ with
--   $$w_{r+1}<\frac{\sum_{i>r}w_i}{k-r}=:a.$$
--   When $q\le k$, set $a=s=0$ and use the irrelevant default $r=0$. Also define $F(x)=\sum_i\min\{w_i,x\}$.
--
--   These parameters depend only on the multiset, and apply to both the pivot-cluster instance and a fixed optimal unconstrained partition. Strict stopping peels sizes equal to $a$. The definitions have total default values outside the positive-size, positive-k domain; selected statements use only their specified domain.
-- source:
--   Mahsa Derakhshan, Andisheh Ghasemi, Rajmohan Rajaraman, Omer Wasim, Tegan Wilson, STOC 2027 submission #302 (October 2026), Definitions 3.2–3.3; §7.3.4 (13)–(14), pp. 12–40, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/302.pdf

import Mathlib

set_option autoImplicit false
open Classical
noncomputable section

namespace CorrKClust.BalancedPivot

/-- Definitions 3.2--3.3: clique sizes in nonincreasing order. -/
def sortedSizes (w : Multiset ℕ) : List ℕ := w.sort (· ≥ ·)

def tailSize (w : Multiset ℕ) (r : ℕ) : ℕ := ((sortedSizes w).drop r).sum

def cliqueS (w : Multiset ℕ) (k : ℕ) : ℕ := tailSize w k

/-- Least strict stopping index; the default is used only outside the positive-size domain. -/
def cliqueR (w : Multiset ℕ) (k : ℕ) : ℕ :=
  if w.card ≤ k then 0 else
    ((List.range k).find? (fun r => decide
      (((sortedSizes w).getD r 0 : ℝ) < (tailSize w r : ℝ) / ((k - r : ℕ) : ℝ)))).getD 0

def cliqueA (w : Multiset ℕ) (k : ℕ) : ℝ :=
  if w.card ≤ k then 0 else (tailSize w (cliqueR w k) : ℝ) / ((k - cliqueR w k : ℕ) : ℝ)

/-- F(x) from §7.3.4, (13)--(14). -/
def waterFill (w : Multiset ℕ) (x : ℝ) : ℝ := (w.map (fun a => min (a : ℝ) x)).sum

end CorrKClust.BalancedPivot


