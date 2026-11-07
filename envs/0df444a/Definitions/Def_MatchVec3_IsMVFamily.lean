-- Prove2me | Definitions.Def_MatchVec3_IsMVFamily
-- name    : MatchVec3_IsMVFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:40:49.4412+00:00
-- url     : https://prove2.me/theorems/2e7cc31f-72ad-4ee2-a61a-38b6251f40bb
-- title:
--   Matching vector family
-- statement:
--   Let $m,n,K$ be natural numbers. A **matching vector family** in $\mathbb Z_m^n$ of size $K$ is a pair of ordered lists $U=(u_1,\dots,u_K)$, $V=(v_1,\dots,v_K)$ of vectors of $\mathbb Z_m^n$ such that
--
--   $$\langle u_i,v_i\rangle=0\quad\text{for all }i,\qquad \langle u_i,v_j\rangle\neq0\quad\text{for all }i\neq j.$$
--
--   This is the object all of the mission's bounds are about. Definition 1.1 of the paper fixes a set $S\subseteq\mathbb Z_m\setminus\{0\}$ of allowed off-diagonal values; here $S$ is the whole of $\mathbb Z_m\setminus\{0\}$, and restrictions on the values are expressed separately.
--
--   **Formalization Note** The lists are functions on `Fin K`. The paper's moduli are positive; `ZMod 0` is $\mathbb Z$ and is not a modulus, so theorems that need it carry a hypothesis on $m$.
-- source:
--   Aggarwal, Obremski, Subexponential Upper Bounds for 3-Restricted Matching Vector Families, STOC 2027 submission (manuscript sha256 44199413…), Definition 1.1, p.2

import Mathlib

namespace MatchVec3

/-- **Matching vector family** (Aggarwal, Obremski, *Subexponential Upper Bounds for 3-Restricted
Matching Vector Families*, STOC 2027 submission (manuscript sha256 44199413…), Definition 1.1, p.2).
A pair of ordered lists `U = (u_1, …, u_K)`, `V = (v_1, …, v_K)` in `Z_m^n` with `⟨u_i, v_i⟩ = 0` for
all `i` and `⟨u_i, v_j⟩ ≠ 0` for all `i ≠ j`.

**Formalization Note** The lists are functions `Fin K → Fin n → ZMod m`, so repetitions are not
excluded by the type; they are excluded by the two conditions. The paper's moduli are positive
(`m ≥ 2` in the abstract); `ZMod 0 = ℤ` is not a modulus, and every theorem of this mission that
needs it carries a hypothesis on `m`. -/
def IsMVFamily {m n K : ℕ} (U V : Fin K → Fin n → ZMod m) : Prop :=
  (∀ i, U i ⬝ᵥ V i = 0) ∧ ∀ i j, i ≠ j → U i ⬝ᵥ V j ≠ 0

end MatchVec3


