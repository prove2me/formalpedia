-- Prove2me | Definitions.Def_StochasticProg_IntegerLShaped_Instance
-- name    : StochasticProg_IntegerLShaped_Instance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T20:11:05.532576+00:00
-- url     : https://prove2.me/theorems/57a9102a-4a3f-4316-869f-f25635384a5e
-- title:
--   Stochastic integer program: recourse data, restrictions, feasibility, and the cut right-hand side
-- statement:
--   A **stochastic integer program (SIP)** in the sense of Birge and Louveaux, Chapter 7,
--   extends a two-stage stochastic linear program with fixed recourse (`Recourse.Instance`:
--   first-stage data $A, b, c$, fixed recourse matrix $W$, and $K$ scenarios of
--   $(q_k, h_k, T_k)$ with probabilities $p_k$) by two extra restrictions:
--
--   $$
--   (\mathrm{SIP}) \quad \min_{x \in X} c^{\mathsf T}x + \mathbb E_\xi \min_y \{ q(\omega)^{\mathsf T} y \mid W(\omega)y = h(\omega) - T(\omega)x,\ y \in Y\}
--   \quad \text{s.t. } Ax = b.
--   $$
--
--   $X$ is a first-stage restriction (which, in §7.2, will further require every
--   coordinate of $x$ to be binary) and $Y$ is a second-stage restriction — typically an
--   integrality restriction on the recourse variable $y$, though the definition itself
--   leaves $Y$ an arbitrary subset of $\mathbb R^{n_2}$.
--
--   Given such an instance `d`, `QValY d x k` is the second-stage value at scenario $k$
--   with $y \in Y$ imposed, $Q(x,\xi_k) = \min_y \{ q_k^{\mathsf T}y \mid Wy = h_k - T_k x,\
--   y \ge 0,\ y \in Y\}$ (extended-real, $+\infty$ when infeasible); `QY d x` is its
--   probability-weighted sum over scenarios, combined with the book's own convention for
--   mixing infeasible and unbounded scenario values; `objY d x` is the deterministic
--   equivalent objective $c^{\mathsf T}x + Q(x)$.
--
--   `K1X d` is the first-stage feasible region $\{x \mid Ax=b,\ x\ge0,\ x\in X\}$. The
--   instance has **relatively complete recourse** when every point of `K1X d` is also
--   second-stage feasible, i.e. $K1X \subseteq \{x \mid Q(x) \ne +\infty\}$ — the same
--   "$K_2 \supseteq K_1$" condition Chapter 3 (p. 138) states for the continuous recourse
--   problem, restated for the $Y$-restricted value here. A first-stage point $x$ is
--   **binary** when every coordinate equals $0$ or $1$ (§7.2, p. 291), the standing
--   hypothesis of this chunk.
--
--   For a subset $S$ of the first-stage index set, `delta S x` is $\delta(x,S) = \sum_{i \in
--   S} x_i - \sum_{i \notin S} x_i$ (Eq. (2.2)), `indicator S` is the point with $x_i=1$ for
--   $i \in S$ and $x_i=0$ otherwise, and `cutRHS L qS S x` is the right-hand side of
--   optimality cut (2.1), $(q_S-L)\,\delta(x,S) - (q_S-L)(|S|-1) + L$.
--
--   **Formalization Note** Taking $Y = \mathrm{Set.univ}$ in an instance recovers exactly
--   the continuous relaxation already defined by `Recourse.Instance` (`Recourse.QVal`,
--   `Recourse.Q`), without a second, separate definition. This is a narrower object than
--   the book's general $C(x)$ of Eq. (1.3)-(1.4), however: the book's $C(x)$ is computed
--   over $\overline Y$, the continuous/LP-relaxation of $Y$, which can retain bounds $Y$
--   imposes beyond integrality (the book's own worked example on p. 290 gives binary
--   $Y=\{0,1\}^{m_2}$, so $\overline Y=[0,e]$, not $\mathbb R_{\ge0}^{n_2}$). Dropping $Y$
--   entirely (`d.toInstance`, i.e. $Y=\mathrm{Set.univ}$) coincides with $\overline Y$
--   only when $Y$ is itself an unbounded integrality restriction — the case this mission's
--   Proposition 1 (`prop1_cuts_valid_for_sip`) is stated for; see that item's own
--   Formalization Note.
-- source:
--   Birge & Louveaux, Introduction to Stochastic Programming, 2nd ed., Springer 2011, pp. 289-291, Chapter 7, Eq. (1.1)-(1.2), §7.2 Assumption 2 and Eq. (2.1)-(2.2)

import Mathlib
import Definitions.Def_StochasticProg_Recourse_Instance

namespace StochasticProg.IntegerLShaped

open StochasticProg.Recourse

variable {n1 n2 m1 m2 K : ℕ}

/-- A stochastic integer program (SIP), Ch. 7 §7.1 Eq. (1.1)-(1.2), p. 289: the same
recourse data as `Recourse.Instance` (first-stage `A, b, c`, fixed recourse `W`, `K`
scenarios of `(q, h, T)` with probabilities `p`), together with a first-stage
restriction `X` ("`x ∈ X`", Eq. (1.1)) and a second-stage integrality (or other)
restriction `Y` on the recourse variable ("`y ∈ Y`", Eq. (1.2)). -/
structure Data (n1 n2 m1 m2 K : ℕ) extends Instance n1 n2 m1 m2 K where
  X : Set (Fin n1 → ℝ)
  Y : Set (Fin n2 → ℝ)

variable (d : Data n1 n2 m1 m2 K)

/-- The second-stage value `Q(x,ξ_k)` with the restriction `y ∈ Y` imposed (Eq. (1.2),
p. 289): `sInf` of the empty set is `⊤` (infeasible), matching the book's convention
(as in `Recourse.QVal`). -/
noncomputable def QValY (d : Data n1 n2 m1 m2 K) (x : Fin n1 → ℝ) (k : Fin K) : EReal :=
  sInf {z : EReal | ∃ y : Fin n2 → ℝ, y ∈ d.Y ∧ (∀ i, 0 ≤ y i) ∧
    Matrix.mulVec d.W y = d.h k - Matrix.mulVec (d.T k) x ∧
    z = ((dotProduct (d.q k) y : ℝ) : EReal)}

/-- `Q(x) = E_ξ Q(x,ξ)` with `Y` imposed (Eq. (1.1)), combined via `Recourse.bookAdd`
(the same `+∞ + (-∞) = +∞` convention, p. 109). -/
noncomputable def QY (d : Data n1 n2 m1 m2 K) (x : Fin n1 → ℝ) : EReal :=
  (List.ofFn (fun k : Fin K => (d.p k : EReal) * QValY d x k)).foldr bookAdd 0

/-- The deterministic-equivalent objective `z(x) = cᵀx + Q(x)` for the SIP, with `Y`
imposed (Eq. (1.1)/(DEP) p. 290). -/
noncomputable def objY (d : Data n1 n2 m1 m2 K) (x : Fin n1 → ℝ) : EReal :=
  ((dotProduct d.c x : ℝ) : EReal) + QY d x

/-- First-stage feasibility for the SIP: `x ∈ K1` (Ch. 3, `Ax = b`, `x ≥ 0`) and
`x ∈ X` (Eq. (1.1)). -/
def K1X (d : Data n1 n2 m1 m2 K) : Set (Fin n1 → ℝ) :=
  K1 d.toInstance ∩ d.X

/-- "It is said to have relatively complete recourse when `K2 ⊇ K1`" (Ch. 3 p. 138),
restated for the `Y`-restricted recourse value of this chapter: every SIP-feasible `x`
is second-stage feasible under `Y`. -/
def RelativelyCompleteRecourse (d : Data n1 n2 m1 m2 K) : Prop :=
  K1X d ⊆ {x | QY d x ≠ ⊤}

/-- "the first-stage variables are binary variables" (§7.2, p. 291). -/
def Binary (x : Fin n1 → ℝ) : Prop := ∀ i, x i = 0 ∨ x i = 1

/-- `δ(x,S) = Σ_{i∈S} x_i − Σ_{i∉S} x_i`, Eq. (2.2), p. 291. -/
def delta (S : Finset (Fin n1)) (x : Fin n1 → ℝ) : ℝ :=
  (∑ i ∈ S, x i) - ∑ i ∈ Sᶜ, x i

/-- The indicator first-stage point "`x_i = 1, i ∈ S`, `x_i = 0, i ∉ S`" of §7.2,
Proposition 3. -/
def indicator (S : Finset (Fin n1)) : Fin n1 → ℝ := fun i => if i ∈ S then 1 else 0

/-- The right-hand side of optimality cut (2.1), p. 291:
`(qS − L)(Σ_{i∈S} x_i − Σ_{i∉S} x_i) − (qS − L)(|S| − 1) + L`. -/
def cutRHS (L qS : ℝ) (S : Finset (Fin n1)) (x : Fin n1 → ℝ) : ℝ :=
  (qS - L) * delta S x - (qS - L) * ((S.card : ℝ) - 1) + L

end StochasticProg.IntegerLShaped


