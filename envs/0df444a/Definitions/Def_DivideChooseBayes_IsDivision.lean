-- Prove2me | Definitions.Def_DivideChooseBayes_IsDivision
-- name    : DivideChooseBayes_IsDivision
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:26:17.105679+00:00
-- url     : https://prove2.me/theorems/c3d21e19-1e0c-43cc-849e-ba74b786a473
-- title:
--   Division $q \in [-1,1]^n$
-- statement:
--   A **division** of $n$ divisible goods is a vector $p\in[0,1]^n$; in the auxiliary variables $q_i=2p_i-1$ it is a vector $q\in[-1,1]^n$. The paper "frequently refer[s] to a division as $p$ or $q$ interchangeably".
--
--   **Formalization Note** Divisions are represented by $q$; $p_i = q_i/2+1/2$, and $q\in[-1,1]^n$ exactly when $p\in[0,1]^n$.
-- source:
--   Tucker-Foltz & Zeckhauser, Playing Divide-and-Choose Given Uncertain Preferences, arXiv:2207.03076v2, p.5, (ii); §3.1, p.6, Eqs. (1)–(2)

import Mathlib

namespace DivideChooseBayes

/-- **Division (in the variables `q`).**
Tucker-Foltz & Zeckhauser, *Playing Divide-and-Choose Given Uncertain Preferences*,
arXiv:2207.03076v2, p.5, (ii), and §3.1, p.6, Eqs. (1)–(2).

A division is a vector `p ∈ [0,1]ⁿ`; in the auxiliary variables `qᵢ = 2pᵢ − 1` it is a vector
`q ∈ [−1,1]ⁿ`. "We frequently refer to a division as p or q interchangeably" (p.6).

**Formalization Note.** Divisions are represented by `q`; `p = pOfQ q` (Eq. (2)), and
`q ∈ [−1,1]ⁿ ↔ pOfQ q ∈ [0,1]ⁿ`. -/
def IsDivision {ι : Type*} (q : ι → ℝ) : Prop := ∀ i, q i ∈ Set.Icc (-1 : ℝ) 1

end DivideChooseBayes


