-- Prove2me | Definitions.Def_PopularMixed_Arrays
-- name    : PopularMixed_Arrays
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:55:31.583642+00:00
-- url     : https://prove2.me/theorems/210a08d2-60be-4176-a93e-a37d69c83a06
-- title:
--   The arrays $X'_u$, the matchings $M_t$ and the witnesses $\vec\alpha^t$ (Section 3)
-- statement:
--   Fix $(\vec x,\vec\alpha)\in\mathcal P'_G$ and put $r_a=(1+\alpha_a)/2$, $r_b=(1-\alpha_b)/2$.
--
--   1. $X_a$ lists $a$'s partners in $\vec x$ in increasing order of $a$'s preference ($\ell(a)$ first), each cell of length $x(a,\cdot)$; its initial $r_a$ fraction is the **positive** sub-array and the rest the **negative** sub-array (Definition 3). $X_b$ lists $b$'s partners in decreasing order of $b$'s preference; its initial $r_b$ fraction is **negative**, the rest **positive** (Definition 4).
--   2. $X'_u$ is $X_u$ with its two sub-arrays swapped (Figs. 2–3): $X'_a$ starts with the negative sub-array of $X_a$, $X'_b$ with the positive sub-array of $X_b$.
--   3. For $t\in[0,1)$, the line $L_t$ at distance $t$ meets (or touches the left boundary of) one cell $c_u(t)$ of each $X'_u$, and $M_t=\{(u,v):u\in A\cup B,\ v\text{ in cell }c_u(t)\}$.
--   4. $\alpha^t_u=-1$ if $c_u(t)$ is in the negative sub-array of $X'_u$, and $\alpha^t_u=1$ otherwise.
--
--   In closed form, the cell of $b$ in $X_a$ is $[L_a(b),L_a(b)+x(a,b))$ with $L_a(b)=\sum_{b'\prec_a b}x(a,b')$ (including $x(a,\ell(a))$), the cell of $a$ in $X_b$ is $[U_b(a),U_b(a)+x(a,b))$ with $U_b(a)=\sum_{a'\succ_b a}x(a',b)$, and $X'_u(t)=X_u(\operatorname{frac}(t+r_u))$. These objects turn a popular fractional matching into popular matchings in the proof of Theorem 3.1.
--
--   **Formalization Note** Cells are half-open on the right, matching "intersects or touches the left boundary" (PDF p.8). `belowA`, `belowB` are the $\prec$ sums including the last resort, `aboveB` is $U_b(a)$. `Mt` is the set of $(a,b)\in E$ with $b$ in $c_a(t)$ or $a$ in $c_b(t)$. `alphaT α t (inl a) = −1` iff $t<1-r_a$; `alphaT α t (inr b) = 1` iff $t<1-r_b$.
-- source:
--   Huang–Kavitha, Popularity, Mixed Matchings, and Self-duality, conference version (SODA 2017), Section 3, PDF p.7 (r_a, r_b, X_a, Definition 3, Fig. 2), PDF p.8 (X_b, Definition 4, Fig. 3, Section 3.1: M_t), PDF p.9 (α^t).

import Mathlib
import Definitions.Def_PopularMixed_Model
import Definitions.Def_PopularMixed_Fractional

namespace PopularMixed

/-!
Huang–Kavitha, *Popularity, Mixed Matchings, and Self-duality*, conference version (SODA 2017),
Section 3, PDF pp.7–9: for a pair `(x, α)` (a fractional matching and a witness), the values
`r_a`, `r_b`, the arrays `X_a`, `X_b`, the reordered arrays `X′_a`, `X′_b` (Definitions 3–4,
Figs. 2–3), the set `M_t` (Section 3.1, PDF p.8) and the vector `α^t` (PDF p.9).

**Formalization Note (closed form of the arrays).**
* `X_a` lists `a`'s partners in `x` in increasing order of `a`'s preference, `ℓ(a)` first; a
  cell has the length of its coordinate. The cell of a neighbour `b` is the half-open interval
  `[L_a(b), L_a(b) + x(a,b))` with `L_a(b) = Σ_{b′ ≺_a b} x(a,b′)` (`belowA`, the sum including
  `x(a, ℓ(a))`); `ℓ(a)`'s cell is `[0, x(a,ℓ(a)))`.
* `X_b` lists `b`'s partners in decreasing order of `b`'s preference, `ℓ(b)` last. The cell of a
  neighbour `a` is `[U_b(a), U_b(a) + x(a,b))` with `U_b(a) = Σ_{a′ ≻_b a} x(a′,b)` (`aboveB`).
* The positive sub-array of `X_a` is `[0, r_a)` and the negative one `[r_a, 1)` (Definition 3);
  the negative sub-array of `X_b` is `[0, r_b)` and the positive one `[r_b, 1)` (Definition 4).
  Swapping the two sub-arrays (Figs. 2–3) gives `X′_u(t) = X_u(frac(t + r_u))` for `t ∈ [0,1)`
  and `r_u ∈ [0,1]`: `X′_a` begins with the negative sub-array of `X_a`, `X′_b` with the positive
  sub-array of `X_b`, and a cell cut by the swap line becomes two cells.
* `L_t` "intersects or touches the left boundary" of exactly one cell of each row (PDF p.8):
  cells are half-open on the right. `M_t` contains `(a,b)` iff `b` is in `c_a(t)` or `a` is in
  `c_b(t)` (`M_t = {(u,v) : u ∈ A ∪ B, v in cell c_u(t)}`).
* `α^t_u = −1` if `c_u(t)` is in the negative sub-array of `X′_u`, `+1` otherwise: for `a`, the
  negative sub-array of `X′_a` is `[0, 1 − r_a)`; for `b`, the positive sub-array of `X′_b` is
  `[0, 1 − r_b)`.
-/

open Finset

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- `r_a = (1 + α_a)/2`, i.e. `2r_a − 1 = α_a` (PDF p.7). -/
noncomputable def rA (α : A ⊕ B → ℝ) (a : A) : ℝ := (1 + α (Sum.inl a)) / 2

/-- `r_b = (1 − α_b)/2`, i.e. `1 − 2r_b = α_b` (PDF p.7). -/
noncomputable def rB (α : A ⊕ B → ℝ) (b : B) : ℝ := (1 - α (Sum.inr b)) / 2

namespace Instance

variable (G : Instance A B)

/-- `Σ_{b′ ≺_a b} x(a,b′)`, including the last-resort coordinate `x(a, ℓ(a))` (PDF p.4
convention): the left end of `b`'s cell in `X_a`. -/
def belowA (x : A → B → ℝ) (a : A) (b : B) : ℝ :=
  lrA x a + ∑ b' ∈ univ.filter (fun b' => (a, b') ∈ G.E ∧ G.rankA a b < G.rankA a b'), x a b'

/-- `Σ_{a′ ≺_b a} x(a′,b)`, including the last-resort coordinate `x(b, ℓ(b))`. -/
def belowB (x : A → B → ℝ) (b : B) (a : A) : ℝ :=
  lrB x b + ∑ a' ∈ univ.filter (fun a' => (a', b) ∈ G.E ∧ G.rankB b a < G.rankB b a'), x a' b

/-- `Σ_{a′ ≻_b a} x(a′,b)`: the left end of `a`'s cell in `X_b`. -/
def aboveB (x : A → B → ℝ) (b : B) (a : A) : ℝ :=
  ∑ a' ∈ univ.filter (fun a' => (a', b) ∈ G.E ∧ G.rankB b a' < G.rankB b a), x a' b

/-- Position `s ∈ [0,1)` of `X_a` lies in the cell of the neighbour `b`. -/
def InCellA (x : A → B → ℝ) (a : A) (s : ℝ) (b : B) : Prop :=
  (a, b) ∈ G.E ∧ G.belowA x a b ≤ s ∧ s < G.belowA x a b + x a b

/-- Position `s ∈ [0,1)` of `X_b` lies in the cell of the neighbour `a`. -/
def InCellB (x : A → B → ℝ) (b : B) (s : ℝ) (a : A) : Prop :=
  (a, b) ∈ G.E ∧ G.aboveB x b a ≤ s ∧ s < G.aboveB x b a + x a b

open Classical in
/-- `M_t` (PDF p.8): the pairs `(a,b) ∈ E` such that `b` is in the cell `c_a(t)` of `X′_a`
(position `frac(t + r_a)` of `X_a`) or `a` is in the cell `c_b(t)` of `X′_b` (position
`frac(t + r_b)` of `X_b`). -/
noncomputable def Mt (x : A → B → ℝ) (α : A ⊕ B → ℝ) (t : ℝ) : Finset (A × B) :=
  G.E.filter fun p =>
    G.InCellA x p.1 (Int.fract (t + rA α p.1)) p.2 ∨ G.InCellB x p.2 (Int.fract (t + rB α p.2)) p.1

end Instance

/-- `α^t` (PDF p.9): `α^t_u = −1` if the cell of `X′_u` met by `L_t` is negative, `+1` if it is
positive. For `a ∈ A` the negative sub-array of `X′_a` is `[0, 1 − r_a)`; for `b ∈ B` the
positive sub-array of `X′_b` is `[0, 1 − r_b)`. -/
noncomputable def alphaT (α : A ⊕ B → ℝ) (t : ℝ) : A ⊕ B → ℝ
  | Sum.inl a => if t < 1 - rA α a then -1 else 1
  | Sum.inr b => if t < 1 - rB α b then 1 else -1

end PopularMixed


