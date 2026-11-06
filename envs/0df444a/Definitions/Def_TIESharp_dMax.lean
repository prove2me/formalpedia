-- Prove2me | Definitions.Def_TIESharp_dMax
-- name    : TIESharp_dMax
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:37:50.926198+00:00
-- url     : https://prove2.me/theorems/98d711b2-147f-4c1c-9b88-f4f156998d48
-- title:
--   Largest supported job cost $d_i$
-- statement:
--   For the Bounded-Square probabilities $q$ at profile $t$, machine $i$'s largest supported job cost is
--   $$d_i=\max\{t_{ij}: q_{ij}>0\},$$
--   with $d_i=0$ if $q_{ij}=0$ for every job $j$. It bounds the width of machine $i$'s load range under slot rounding.
-- source:
--   Li, Sharp Bounds for Truthful-in-Expectation Scheduling, arXiv:2611.05134 (held version, sha256 e611c390…b70e5481), Proposition 3.4, p.11; Lemma 5.2, p.23

import Mathlib
import Definitions.Def_TIESharp_bsProb

set_option autoImplicit false

namespace TIESharp

/-- The **largest supported job cost** of machine `i` (Li, *Sharp Bounds for
Truthful-in-Expectation Scheduling*, arXiv:2611.05134, Proposition 3.4, p.11, and Lemma 5.2,
p.23): `d_i = max{t_ij : q_ij > 0}`, "with d_i = 0 if q_ij = 0 for every job j". Here `q` is the
Bounded-Square probability `bsProb`.

**Formalization Note.** The maximum is `Finset.sup'` over the nonempty set of supported jobs; the
empty case is the explicit `0` of the paper. -/
noncomputable def dMax {n m : ℕ} (t : Fin n → Fin m → ℝ) (i : Fin n) : ℝ :=
  if h : (Finset.univ.filter (fun j => 0 < bsProb t i j)).Nonempty then
    (Finset.univ.filter (fun j => 0 < bsProb t i j)).sup' h (fun j => t i j)
  else 0

end TIESharp


