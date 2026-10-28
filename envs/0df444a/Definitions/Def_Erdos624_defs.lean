-- Prove2me | Definitions.Def_Erdos624_defs
-- name    : Erdos624_defs
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T18:45:32.66758+00:00
-- url     : https://prove2.me/theorems/3d114ec5-8d5b-4470-8502-9ece4c0c05fa
-- title:
--   Erdős Problem 624: eventually surjective maps $f:\mathcal P(X)\to X$ and the threshold $H(n)$
-- statement:
--   Let $X$ be a set of size $n$ (represented by $\mathrm{Fin}\,n$). **ExistsEventuallySurjective $n$ $m$** holds if there is a map $f:\mathcal P(X)\to X$ such that for every $Y\subseteq X$ with $|Y|\ge m$,
--
--   $$\{f(A):A\subseteq Y\}=X.$$
--
--   **$H(n)$** is the least such $m$ (and $H(0)=0$). Erdős Problem 624 asks to prove $H(n)-\log_2 n\to\infty$. Both definitions are copied verbatim from Google DeepMind's Formal Conjectures file for Problem 624.
-- source:
--   Erdős Problem 624, https://www.erdosproblems.com/624; Formal Conjectures FormalConjectures/ErdosProblems/624.lean (ExistsEventuallySurjective, H)

import Mathlib

namespace Erdos624

open Finset

/-- Verbatim from Formal Conjectures `FormalConjectures/ErdosProblems/624.lean`. -/
def ExistsEventuallySurjective (n m : ℕ) : Prop :=
  ∃ (f : Finset (Fin n) → Fin n),
    ∀ (Y : Finset (Fin n)), #Y ≥ m →
      Y.powerset.image f = Finset.univ

/-- Verbatim from Formal Conjectures: `H n` is the least admissible threshold `m` (and `0` for `n = 0`). -/
noncomputable def H (n : ℕ) : ℕ :=
  if 0 < n then
    sInf {m : ℕ | ExistsEventuallySurjective n m}
  else 0

end Erdos624


