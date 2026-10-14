-- Prove2me | Definitions.Def_ObsCostMDP_WellPosed_QVI
-- name    : ObsCostMDP_WellPosed_QVI
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T20:50:10.175027+00:00
-- url     : https://prove2.me/theorems/5b1f4ac1-0f4a-4fc7-a331-e920aec362a0
-- title:
--   Problem 3.1 and Assumptions 3.2, 3.12 — the QVI (3.1) with inspection operator (3.2), sub- and supersolutions
-- statement:
--   This file sets up the abstract quasi-variational inequality (QVI) of Section 3 of Reisinger and Tam.
--
--   Let $X$ be a finite state space and $A$ a finite nonempty action set. Unknowns are functions $u:\mathbb N\times X\to\mathbb R^A$ with components $u_a(n,x)$, also written $u^n_{a,x}$. A **driver** is a family $\{F_a\}_{a\in A}$ of functions $F_a:\mathbb N\times X\times\mathbb R^A\times\mathbb R^{\mathbb N\times X}\to\mathbb R$; the third argument is a vector $r\in\mathbb R^A$ and the fourth a whole function $\phi:\mathbb N\times X\to\mathbb R$. A sequence $\{Q_n\}\subset\mathbb R^{X\times X}$ is **substochastic** if its entries are nonnegative and its row sums are at most $1$. Given a vector $c\in\mathbb R^{X\times A}$, the **inspection operator** is
--
--   $$\mathcal M u(n,x)=\big(Q_n\,\overline{u^1-c}\big)_x,\qquad \big(\overline{u^1-c}\big)_y=\max_{a\in A}\big(u^1_{a,y}-c_{a,y}\big).$$
--
--   It reads $u$ only at time $1$ and does not depend on the action. The QVI (3.1) of Problem 3.1 is
--
--   $$\min\big\{F_a(n,x,u(n,x),u_a),\;u_a(n,x)-\mathcal Mu(n,x)\big\}=0,\qquad n\in\mathbb N,\ x\in X,\ a\in A.$$
--
--   A function $u$ is a **subsolution** (resp. **supersolution**, **solution**) if the left side is $\le0$ (resp. $\ge0$, $=0$) at every $(n,x,a)$. A function is **bounded** if all its components are bounded by one constant.
--
--   **Assumption 3.2** (with constant $\beta$) asks:
--
--   1. $\beta>0$, and for all $n,x$, all bounded $u\le v$ (componentwise), all $r,s\in\mathbb R^A$ and $a\in A$ with $\theta:=r_a-s_a=\max_{j\in A}(r_j-s_j)\ge0$,
--   $$F_a(n,x,r,u_a+\theta)-F_a(n,x,s,v_a)\ge\beta\theta;$$
--   2. for every $n,a,r$ and bounded $\phi$, the map $x\mapsto F_a(n,x,r,\phi)$ is bounded; and for every $a$ and bounded $\phi$, the map $r\mapsto F_a(n,x,r,\phi)$ is uniformly continuous on bounded sets of $r$, uniformly in $(n,x)$.
--
--   **Assumption 3.12** asks that for every $(n,x)$ there is a finite set $\Omega_{n,x}\subset\mathbb N\times X$ such that $F_a(n,x,r,\phi)$ depends only on the values of $\phi$ on $\Omega_{n,x}$, for every $a$ and $r$.
--
--   These are the objects of the paper's main well-posedness result, Theorem 3.13, and of the comparison principle, Proposition 3.3. The discounted observation-cost QVI (2.11) is an instance.
--
--   **Formalization Note** $u$ is curried as `u n x a` $=u_a(n,x)$, $c$ as `c a x` $=c_{a,x}$, and the driver as `F a n x r φ`. Time ranges over all of $\mathbb N$, including $0$, as "$n\in\mathbb N$" in (3.1); $u^1$ is `u 1`. "Substochastic" is read as nonnegative entries with row sums at most $1$. "$\theta$ is the maximum of $r-s$" is stated as $r_j-s_j\le r_a-s_a$ for all $j$, which is equivalent. In Assumption 3.2.2, continuity in $x$ is automatic on the finite discrete set $X$ and is omitted; "continuous bounded $\phi$" is "bounded $\phi$"; bounded sets of $r$ are the cubes $\{|r_j|\le R\ \forall j\}$.
-- source:
--   Reisinger & Tam, Markov decision processes with observation costs: framework and computation with a penalty scheme, arXiv:2201.07908v3, p. 15, Problem 3.1, (3.1), (3.2) and Assumption 3.2; p. 19, Assumption 3.12

import Mathlib

namespace ObsCostMDP.WellPosed

/-- A **driver** of Problem 3.1 (Reisinger–Tam, arXiv:2201.07908v3, p. 15): the family
`{F_a}_{a ∈ A}` with `F_a : ℕ × X × ℝ^A × ℝ^{ℕ×X} → ℝ`. `F a n x r φ` is `F_a(n, x, r, φ)`:
the third argument is a vector `r ∈ ℝ^A` (in (3.1) the value `u(n, x)`), the fourth a whole
function `φ : ℕ × X → ℝ` (in (3.1) the component `u_a`). -/
abbrev Driver (X A : Type*) := A → ℕ → X → (A → ℝ) → (ℕ → X → ℝ) → ℝ

/-- A function `u : ℕ × X → ℝ^A` is **bounded** if all its components are bounded by one
constant. **Formalization Note**: `u` is curried as `u n x a = u_a(n, x)`. -/
def IsBounded {X A : Type*} (u : ℕ → X → A → ℝ) : Prop :=
  ∃ K : ℝ, ∀ n x a, |u n x a| ≤ K

/-- A real function `φ : ℕ × X → ℝ` is bounded. -/
def IsBoundedFn {X : Type*} (φ : ℕ → X → ℝ) : Prop :=
  ∃ K : ℝ, ∀ n x, |φ n x| ≤ K

/-- `{Q_n}` is a sequence of **substochastic matrices** (p. 15, after (3.2)): nonnegative entries
and row sums bounded by `1`. -/
def IsSubstochastic {X : Type*} [Fintype X] (Q : ℕ → Matrix X X ℝ) : Prop :=
  ∀ n, (∀ x y, 0 ≤ Q n x y) ∧ ∀ x, ∑ y, Q n x y ≤ 1

/-- The maximum over actions `max_{a ∈ A} w_a` of a vector `w ∈ ℝ^A` (the overline of (3.2)). -/
def actMax {A : Type*} [Fintype A] [Nonempty A] (w : A → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty w

/-- The **inspection operator** (3.2), p. 15:
`Mu(n, x) = (Q_n \overline{u¹ − c})_x` with `(\overline{u¹ − c})_y = max_{a∈A}(u¹_{a,y} − c_{a,y})`.
It reads `u` at time `1` only and does not depend on the action. `c a y = c_{a,y}`. -/
def inspection {X A : Type*} [Fintype X] [Fintype A] [Nonempty A]
    (Q : ℕ → Matrix X X ℝ) (c : A → X → ℝ) (u : ℕ → X → A → ℝ) (n : ℕ) (x : X) : ℝ :=
  ∑ y, Q n x y * actMax (fun a => u 1 y a - c a y)

/-- The left side of the QVI (3.1), p. 15:
`min {F_a(n, x, u(n, x), u_a), u_a(n, x) − Mu(n, x)}`. -/
def residual {X A : Type*} [Fintype X] [Fintype A] [Nonempty A]
    (F : Driver X A) (Q : ℕ → Matrix X X ℝ) (c : A → X → ℝ) (u : ℕ → X → A → ℝ)
    (n : ℕ) (x : X) (a : A) : ℝ :=
  min (F a n x (u n x) (fun m y => u m y a)) (u n x a - inspection Q c u n x)

/-- `u` is a **subsolution** of (3.1): the residual is `≤ 0` for every `n ∈ ℕ`, `x`, `a`
(Proposition 3.3, p. 15). -/
def IsSubsolution {X A : Type*} [Fintype X] [Fintype A] [Nonempty A]
    (F : Driver X A) (Q : ℕ → Matrix X X ℝ) (c : A → X → ℝ) (u : ℕ → X → A → ℝ) : Prop :=
  ∀ n x a, residual F Q c u n x a ≤ 0

/-- `u` is a **supersolution** of (3.1): the residual is `≥ 0` for every `n ∈ ℕ`, `x`, `a`. -/
def IsSupersolution {X A : Type*} [Fintype X] [Fintype A] [Nonempty A]
    (F : Driver X A) (Q : ℕ → Matrix X X ℝ) (c : A → X → ℝ) (u : ℕ → X → A → ℝ) : Prop :=
  ∀ n x a, 0 ≤ residual F Q c u n x a

/-- `u` **solves** the QVI (3.1) of Problem 3.1: the residual is `0` for every `n ∈ ℕ`, `x`, `a`.
**Formalization Note**: `n` ranges over all of `ℕ` (including `0`), as "n ∈ ℕ" in (3.1);
`u¹` is `u 1`. -/
def IsSolution {X A : Type*} [Fintype X] [Fintype A] [Nonempty A]
    (F : Driver X A) (Q : ℕ → Matrix X X ℝ) (c : A → X → ℝ) (u : ℕ → X → A → ℝ) : Prop :=
  ∀ n x a, residual F Q c u n x a = 0

/-- **Assumption 3.2** (p. 15) with constant `β`:
1. `β > 0`, and for all `n, x`, bounded `u ≤ v : ℕ × X → ℝ^A`, `r, s ∈ ℝ^A` and `a` such that
   `θ := r_a − s_a = max_{j∈A}(r_j − s_j) ≥ 0`:
   `F_a(n, x, r, u_a + θ) − F_a(n, x, s, v_a) ≥ βθ`.
2. For every `n, a, r` and bounded `φ`, `x ↦ F_a(n, x, r, φ)` is bounded (continuity in `x` is
   automatic on the finite discrete set `X`); and for every `a` and bounded `φ`,
   `r ↦ F_a(n, x, r, φ)` is uniformly continuous on bounded sets of `r`, uniformly in `(n, x)`.
**Formalization Note**: "θ = max_j (r_j − s_j)" is written as `∀ j, r_j − s_j ≤ r_a − s_a`
(equivalent, since the index `a` belongs to `A`). Bounded sets of `r` are the cubes
`{r : ∀ j, |r_j| ≤ R}`. -/
def Assumption32 {X A : Type*} (F : Driver X A) (β : ℝ) : Prop :=
  0 < β ∧
  (∀ (n : ℕ) (x : X) (u v : ℕ → X → A → ℝ), IsBounded u → IsBounded v →
      (∀ m y j, u m y j ≤ v m y j) →
      ∀ (r s : A → ℝ) (a : A), (∀ j, r j - s j ≤ r a - s a) → 0 ≤ r a - s a →
        β * (r a - s a) ≤
          F a n x r (fun m y => u m y a + (r a - s a)) - F a n x s (fun m y => v m y a)) ∧
  (∀ (n : ℕ) (a : A) (r : A → ℝ) (φ : ℕ → X → ℝ), IsBoundedFn φ →
      ∃ K : ℝ, ∀ x, |F a n x r φ| ≤ K) ∧
  (∀ (a : A) (φ : ℕ → X → ℝ), IsBoundedFn φ → ∀ R ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧ ∀ (n : ℕ) (x : X) (r s : A → ℝ),
        (∀ j, |r j| ≤ R) → (∀ j, |s j| ≤ R) → (∀ j, |r j - s j| < δ) →
          |F a n x r φ - F a n x s φ| < ε)

/-- **Assumption 3.12** (p. 19): for each `(n, x)` there is a finite set `Ω_{n,x} ⊆ ℕ × X` such
that, for every `a` and `r`, `F_a(n, x, r, φ)` depends only on the values of `φ` on `Ω_{n,x}`. -/
def Assumption312 {X A : Type*} (F : Driver X A) : Prop :=
  ∀ (n : ℕ) (x : X), ∃ Ω : Finset (ℕ × X), ∀ (a : A) (r : A → ℝ) (φ ψ : ℕ → X → ℝ),
    (∀ p ∈ Ω, φ p.1 p.2 = ψ p.1 p.2) → F a n x r φ = F a n x r ψ

end ObsCostMDP.WellPosed


