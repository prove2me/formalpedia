-- Prove2me | Definitions.Def_OnlineRandomization_Restart_GameProperties
-- name    : OnlineRandomization_Restart_GameProperties
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T08:11:52.503202+00:00
-- url     : https://prove2.me/theorems/d67d93d7-64e5-4dd5-948d-46101fca667e
-- title:
--   Monotonicity, locality, discrepancy and a bound on the diameter of a request-answer game
-- statement:
--   Let $F$ be a request-answer game with cost functions $f_n$ and off-line optimum $c$.
--
--   1. $F$ is **monotone** if extending a request-answer sequence cannot decrease its cost: $f_{n+1}(rt, ab) \ge f_n(r, a)$ for all $n$, $r \in R^n$, $t \in R$, $a \in A^n$, $b \in A$.
--   2. $F$ is **local** if for every real $h > 0$ only finitely many request sequences $r$ have $c(r) \le h$.
--   3. The **discrepancy** of two request-answer sequences $(r, a)$ and $(r', a')$ (each with as many answers as requests) is
--   $$\delta((r,a),(r',a')) = f(rr', aa') - f(r,a) - f(r',a').$$
--   4. A real number $D$ **bounds the diameter** of $F$ if $|\delta((r,a),(r',a'))| \le D$ for all such pairs. The **diameter** $D(F)$ is the supremum of $|\delta|$; $F$ has finite diameter exactly when some real $D$ bounds it, and $D(F)$ is then the least such bound.
--
--   The diameter bounds how much the past requests and answers can change the incremental cost of a continuation. All $K$-server games and task systems are monotone; $K$-server games on finite graphs have finite diameter.
--
--   **Formalization Note** Instead of defining $D(F)$ as a real supremum (which Lean evaluates to $0$ on an unbounded set), the predicate `DiameterBound F D` says that $D$ is an upper bound for $|\delta|$. A statement proved for every such $D$ applies in particular to $D = D(F)$ whenever the diameter is finite. Locality is stated for $h > 0$ as on the page; it implies the version for all $h$.
-- source:
--   Ben-David, Borodin, Karp, Tardos and Wigderson, On the power of randomization in on-line algorithms, Algorithmica 11 (1994), manuscript pp. 16-17, §4 (monotonicity, locality, discrepancy, diameter)

import Mathlib
import Definitions.Def_OnlineRandomization_Restart_Model

namespace OnlineRandomization.Restart

/-- p. 16, monotonicity: `f_{n+1}(rt, ab) ≥ f_n(r, a)` for all `r ∈ R^n`, `t ∈ R`,
`a ∈ A^n`, `b ∈ A`. -/
def IsMonotone {R A : Type*} (F : Game R A) : Prop :=
  ∀ (r : List R) (a : List A) (t : R) (b : A), r.length = a.length →
    F.cost r a ≤ F.cost (r ++ [t]) (a ++ [b])

/-- p. 16, locality: for every positive real `h`, only finitely many request sequences
have off-line optimum `c(r) ≤ h`. -/
def IsLocal {R A : Type*} [Fintype A] [Nonempty A] (F : Game R A) : Prop :=
  ∀ h : ℝ, 0 < h → {r : List R | F.opt r ≤ h}.Finite

/-- p. 17: the discrepancy
`δ((r, a), (r', a')) = f(rr', aa') − f(r, a) − f(r', a')`. -/
def discrepancy {R A : Type*} (F : Game R A) (r : List R) (a : List A) (r' : List R)
    (a' : List A) : ℝ :=
  F.cost (r ++ r') (a ++ a') - F.cost r a - F.cost r' a'

/-- p. 17: `D` bounds the diameter of the game, `D(F) = sup |δ((r, a), (r', a'))|` over all
pairs of request-answer sequences of equal lengths, i.e. `D(F) ≤ D`. The game has a finite
diameter iff such a real `D` exists, and `D(F)` is the least one. -/
def DiameterBound {R A : Type*} (F : Game R A) (D : ℝ) : Prop :=
  ∀ (r : List R) (a : List A) (r' : List R) (a' : List A),
    r.length = a.length → r'.length = a'.length → |discrepancy F r a r' a'| ≤ D

end OnlineRandomization.Restart


