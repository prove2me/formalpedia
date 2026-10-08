-- Prove2me | Definitions.Def_BellmanDP_ExistUnique_SupEquation
-- name    : BellmanDP_ExistUnique_SupEquation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T15:28:34.868973+00:00
-- url     : https://prove2.me/theorems/805c65e4-bb03-49c6-8f5b-2e1450de7375
-- title:
--   The functional equation $f(p)=\sup_q[g(p,q)+h(p,q)f(T(p,q))]$, its successive approximations and radial suprema
-- statement:
--   This file sets up the general functional equation of Chapter IV of Bellman's *Dynamic Programming*. A state $p$ lies in a set $E$ (in the theorems, a domain $D \subseteq \mathbb{R}^N$), a decision $q$ ranges over a set $S$, and $g(p,q)$, $h(p,q)$, $T(p,q)$ are the one-stage return, the multiplier and the next state. The objects are:
--
--   1. The one-stage return $g(p,q) + h(p,q)\,f(T(p,q))$ of a function $f$.
--   2. The predicate that $f$ satisfies Bellman's equation (1.1) at $p$,
--   $$f(p) = \sup_{q \in S}\big[g(p,q) + h(p,q)\,f(T(p,q))\big],$$
--   meaning that the set of one-stage returns is bounded above and $f(p)$ is its least upper bound.
--   3. The operator $f \mapsto \sup_q[g + h\,f\circ T]$, the initial approximation $f_0(p) = \sup_q g(p,q)$ (Theorem 1 (3a)), and the successive approximations $f_{n+1}(p) = \sup_q[g(p,q) + h(p,q) f_n(T(p,q))]$ (Theorem 1 (3b)) from any starting function.
--   4. The radial supremum $\sup_{p \in D,\ \|p\| \le c}\ \sup_q |\varphi(p,q)|$; for $\varphi = g$ this is Bellman's $v(c)$ of condition (3.1e), and for $\varphi = G - g$ it is the $u(c)$ of (6.5).
--   5. The class of functions bounded in every finite part of $D$: for each $c$, $f$ is bounded on $\{p \in D : \|p\| \le c\}$.
--   6. Continuity of $\varphi(p,q)$ in $p$ on bounded portions of $D$, uniformly for all $q \in S$: for every $c$ and $\varepsilon > 0$ one $\delta > 0$ serves all $q$ and all $p, p' \in D$ with $\|p\|, \|p'\| \le c$.
--
--   These objects are shared by Theorems 1–4 of the chapter.
--
--   **Formalization Note** The operator, $f_0$ and the radial supremum are real `iSup`/`sSup`, which Lean sets to $0$ on sets that are unbounded above or empty; the theorems evaluate them only where the book's boundedness conditions make the supremum genuine. The solution predicate itself uses `IsLUB`, so it has no junk value. Item 6 reads "continuous in $p$, uniformly for all $q$" as uniform equicontinuity on each bounded portion of $D$; when $D$ is closed this is equivalent to pointwise equicontinuity, since then bounded portions of $D$ are compact.
-- source:
--   Bellman, Dynamic Programming, Princeton University Press (1957; Princeton Landmarks ed. 2010), DOI 10.2307/j.ctv1nxcw0f, Chapter IV, § 1, Eq. (1.1), p. 116; § 3, conditions (1a)-(1e) and Theorem 1, (3a)-(3b), pp. 119-120; § 4, Theorem 2, p. 121; § 6, Eq. (6.5), p. 124

import Mathlib

namespace BellmanDP.ExistUnique

/-- Bellman, *Dynamic Programming*, Ch. IV, § 1, Eq. (1.1), p. 116: the one-stage return
`g(p, q) + h(p, q) f(T(p, q))` of choosing `q ∈ S` in state `p` and continuing with `f`. -/
def stageReturn {E S : Type*} (g h : E → S → ℝ) (T : E → S → E) (f : E → ℝ) (p : E) (q : S) :
    ℝ :=
  g p q + h p q * f (T p q)

/-- Eq. (1.1) at the state `p`: `f(p) = Sup_q [g(p, q) + h(p, q) f(T(p, q))]`, the supremum
over `q ∈ S` taken in the genuine sense (`IsLUB`: the set of one-stage returns is bounded above
and `f p` is its least upper bound). -/
def SolvesAt {E S : Type*} (g h : E → S → ℝ) (T : E → S → E) (f : E → ℝ) (p : E) : Prop :=
  IsLUB (Set.range (stageReturn g h T f p)) (f p)

/-- The right-hand side of (1.1) as an operator, `Sup_q [g(p, q) + h(p, q) f(T(p, q))]`, used to
define the successive approximations (3.3b), (4.3). It is a real `iSup`; it is only evaluated
where the returns are bounded above, in which case it is the book's supremum. -/
noncomputable def supOp {E S : Type*} (g h : E → S → ℝ) (T : E → S → E) (f : E → ℝ) (p : E) :
    ℝ :=
  ⨆ q, stageReturn g h T f p q

/-- Ch. IV, Theorem 1, (3a), p. 119, and (4.3), p. 121: the initial approximation
`f₀(p) = Sup_q g(p, q)` (a real `iSup`, evaluated where `g(p, ·)` is bounded). -/
noncomputable def supG {E S : Type*} (g : E → S → ℝ) (p : E) : ℝ :=
  ⨆ q, g p q

/-- Ch. IV, Theorem 1, (3b), p. 119: the successive approximations
`f_{n+1}(p) = Sup_q [g(p, q) + h(p, q) f_n(T(p, q))]` started from `f₀`. -/
noncomputable def succApprox {E S : Type*} (g h : E → S → ℝ) (T : E → S → E) (f₀ : E → ℝ) :
    ℕ → E → ℝ
  | 0 => f₀
  | n + 1 => supOp g h T (succApprox g h T f₀ n)

/-- Ch. IV, § 3, (1e), p. 119, and § 6, Eq. (6.5), p. 124: the radial supremum
`Sup_{‖p‖ ≤ c, p ∈ D} Sup_q |φ(p, q)|`. With `φ = g` this is `v(c)`; with `φ = G − g` it is
`u(c)`. It is a real `sSup`; the theorems use it only where `φ` is bounded on
`{p ∈ D, ‖p‖ ≤ c}` (value `0` if that set is empty). -/
noncomputable def radialSup {E S : Type*} [Norm E] (D : Set E) (φ : E → S → ℝ) (c : ℝ) : ℝ :=
  sSup {x : ℝ | ∃ p ∈ D, ‖p‖ ≤ c ∧ ∃ q : S, x = |φ p q|}

/-- "Bounded in any finite part of `D`" (Ch. IV, Theorem 2, p. 121): `f` is bounded on
`{p ∈ D : ‖p‖ ≤ c}` for every `c`. -/
def BoundedOnBoundedParts {E : Type*} [Norm E] (D : Set E) (f : E → ℝ) : Prop :=
  ∀ c : ℝ, ∃ M : ℝ, ∀ p ∈ D, ‖p‖ ≤ c → |f p| ≤ M

/-- "`φ(p, q)` is continuous in `p` in any bounded portion of `D`, uniformly for all `q ∈ S`"
(Ch. IV, Theorem 1, pp. 119–120), read as uniform equicontinuity: for every `c` and `ε > 0`
there is one `δ > 0` that works for all `q ∈ S` and all `p, p' ∈ D` with `‖p‖, ‖p'‖ ≤ c`. -/
def UnifContInP {E S Y : Type*} [SeminormedAddCommGroup E] [PseudoMetricSpace Y] (D : Set E)
    (φ : E → S → Y) : Prop :=
  ∀ c ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ p ∈ D, ∀ p' ∈ D, ‖p‖ ≤ c → ‖p'‖ ≤ c →
    dist p p' < δ → ∀ q : S, dist (φ p q) (φ p' q) < ε

end BellmanDP.ExistUnique


