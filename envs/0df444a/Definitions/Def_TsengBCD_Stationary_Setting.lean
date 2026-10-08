-- Prove2me | Definitions.Def_TsengBCD_Stationary_Setting
-- name    : TsengBCD_Stationary_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T22:17:17.270979+00:00
-- url     : https://prove2.me/theorems/0d577eb9-845f-4818-a218-dfe51170f909
-- title:
--   §1–§3, pp. 476–479 — blocks, dom, lower directional derivative, stationary / coordinatewise minimum / regular points, block pseudoconvexity, the BCD method (2)–(3), its rules, A1, A2
-- statement:
--   This file fixes the objects of §§1–3 of Tseng (2001) on which Theorem 4.1 and Lemma 3.1 are stated.
--
--   **Blocks.** Let $N\ge 1$ and $n_1,\dots,n_N$ be positive integers (§1, p. 476). A point of $\mathbb R^{n_1+\cdots+n_N}$ is written $x=(x_1,\dots,x_N)$ with coordinate blocks $x_k\in\mathbb R^{n_k}$, and $(0,\dots,d_k,\dots,0)$ denotes the vector whose $k$th block is $d_k$ and whose other blocks are zero. Functions take values in $\mathbb R\cup\{\infty\}$.
--
--   **Form (1).** $f(x_1,\dots,x_N)=f_0(x_1,\dots,x_N)+\sum_{k=1}^N f_k(x_k)$ with $f_0:\mathbb R^{n_1+\cdots+n_N}\to\mathbb R\cup\{\infty\}$ and $f_k:\mathbb R^{n_k}\to\mathbb R\cup\{\infty\}$.
--
--   **Notation (p. 477).** For a function $h$, $\operatorname{dom}h=\{x: h(x)<\infty\}$; for $x\in\operatorname{dom}h$ the (lower) directional derivative is
--   $$h'(x;d)=\liminf_{\lambda\downarrow 0}\frac{h(x+\lambda d)-h(x)}{\lambda}\in[-\infty,\infty].$$
--   The level set of $f$ at $x^0$ is $X^0=\{x: f(x)\le f(x^0)\}$.
--
--   **Block pseudoconvexity and uniqueness (pp. 477–478).** For a set $I$ of blocks, $f$ is *pseudoconvex in $(x_i)_{i\in I}$* if $f(x+d)\ge f(x)$ whenever $x\in\operatorname{dom}f$, $d$ vanishes outside the blocks in $I$, and $f'(x;d)\ge 0$; that is, for every value of the other blocks the function of $(x_i)_{i\in I}$ is pseudoconvex. $f$ *has at most one minimum in $x_k$* if, for every value of the other blocks, the function $x_k\mapsto f(x_1,\dots,x_N)$ has at most one minimum point, a minimum point being a point of its effective domain at which it attains its infimum.
--
--   **Stationarity notions (p. 479).**
--   1. $z$ is a *stationary point* of $f$ if $z\in\operatorname{dom}f$ and $f'(z;d)\ge 0$ for all $d$.
--   2. $z$ is a *coordinatewise minimum point* of $f$ if $z\in\operatorname{dom}f$ and $f(z+(0,\dots,d_k,\dots,0))\ge f(z)$ for all $d_k\in\mathbb R^{n_k}$ and all $k$ (4).
--   3. $f$ is *regular at* $z\in\operatorname{dom}f$ if $f'(z;d)\ge 0$ for every $d=(d_1,\dots,d_N)$ such that $f'(z;(0,\dots,d_k,\dots,0))\ge 0$ for $k=1,\dots,N$ (5).
--
--   **BCD method (2)–(3), p. 478.** From $x^0\in\operatorname{dom}f$, iteration $r+1$ chooses an index $s$ and sets $x^{r+1}_s\in\arg\min_{x_s}f(x^r_1,\dots,x^r_{s-1},x_s,x^r_{s+1},\dots,x^r_N)$, $x^{r+1}_j=x^r_j$ for $j\ne s$. The **essentially cyclic rule** asks for a constant $T\ge N$ such that every index is chosen at least once among any $T$ consecutive iterations; the **cyclic rule** chooses $s=k$ at iterations $k,k+N,k+2N,\dots$.
--
--   **Assumptions A1, A2 (p. 479).** A function $g$ is Gâteaux-differentiable at $z$ if there is a linear functional $L$ (written $d\mapsto\langle\nabla g(z),d\rangle$) with $[g(z+\lambda d)-g(z)]/\lambda\to L(d)$ as $\lambda\to 0$ for every $d$.
--   1. (A1) $\operatorname{dom}f_0$ is open and $f_0$ is Gâteaux-differentiable on $\operatorname{dom}f_0$.
--   2. (A2) $f_0$ is Gâteaux-differentiable on $\operatorname{int}(\operatorname{dom}f_0)$ and, for every $z\in\operatorname{dom}f\cap\operatorname{bdry}(\operatorname{dom}f_0)$, where $\operatorname{bdry}(S)=S\setminus\operatorname{int}(S)$, there are $k$ and $d_k$ with $f(z+(0,\dots,d_k,\dots,0))<f(z)$.
--
--   These are the objects in which Lemma 3.1 and Theorem 4.1 are stated.
--
--   **Formalization Note.** Values in $\mathbb R\cup\{\infty\}$ are `EReal`; the theorems add the standing hypothesis that the functions never take the value $-\infty$. The directional derivative is the `EReal` lower limit over $\lambda\to 0^+$ of $(h(x+\lambda d)-h(x))\cdot\lambda^{-1}$; it is used only at points of $\operatorname{dom}h$. Blocks are 0-based: paper block $k\in\{1,\dots,N\}$ is the Lean index $k-1$. The block dimensions $n_k$ are arbitrary natural numbers in Lean; the paper takes them positive, and a zero-dimensional block changes none of these definitions. The product type carries the sup norm of its blocks rather than the Euclidean norm; no statement depends on this, since compactness, boundedness, continuity and cluster points agree for equivalent norms. A BCD run is a pair $(s,x)$ where `s r` is the block chosen at iteration $r+1$ (the step from $x^r$ to $x^{r+1}$); "$x^{r+1}\in\operatorname{dom}f$" follows from minimality and $x^r\in\operatorname{dom}f$. The sentence defining block pseudoconvexity is printed truncated on pp. 477–478; the reading above is the one the proofs on pp. 482–483 use.
-- source:
--   Tseng, Convergence of a block coordinate descent method for nondifferentiable minimization, J. Optim. Theory Appl. 109 (2001), pp. 476–479, (1)–(5), §2, Assumptions A1, A2

import Mathlib

namespace TsengBCD.Stationary

open Filter Topology

/-- The space `ℜ^{n₁+⋯+n_N}` of block vectors `x = (x₁, …, x_N)`, `x_k ∈ ℜ^{n_k}`.
Paper block `k ∈ {1, …, N}` is the Lean index `k - 1 : Fin N`. -/
abbrev X {N : ℕ} (n : Fin N → ℕ) := (k : Fin N) → EuclideanSpace ℝ (Fin (n k))

/-- Form (1): `f(x) = f₀(x) + ∑_{k=1}^N f_k(x_k)`. -/
noncomputable def fSum {N : ℕ} {n : Fin N → ℕ} (f0 : X n → EReal)
    (fk : (k : Fin N) → EuclideanSpace ℝ (Fin (n k)) → EReal) : X n → EReal :=
  fun x => f0 x + ∑ k, fk k (x k)

/-- Effective domain `dom h = {x | h(x) < ∞}` (p. 477). -/
def dom {V : Type*} (h : V → EReal) : Set V := {x | h x ≠ ⊤}

/-- The level set `X⁰ = {x | f(x) ≤ f(x⁰)}` (p. 478). -/
def levelSet {V : Type*} (f : V → EReal) (x0 : V) : Set V := {x | f x ≤ f x0}

/-- The lower directional derivative (p. 477):
`h′(x; d) = liminf_{λ ↓ 0} [h(x + λd) − h(x)]/λ`, an extended real number.
It is only used at points `x ∈ dom h`. -/
noncomputable def dirDeriv {V : Type*} [AddCommGroup V] [Module ℝ V] (h : V → EReal)
    (x d : V) : EReal :=
  Filter.liminf (fun t : ℝ => (h (x + t • d) - h x) * ((t⁻¹ : ℝ) : EReal)) (𝓝[>] 0)

/-- Stationary point (p. 479): `z ∈ dom f` and `f′(z; d) ≥ 0` for all `d`. -/
def IsStationary {N : ℕ} {n : Fin N → ℕ} (f : X n → EReal) (z : X n) : Prop :=
  f z ≠ ⊤ ∧ ∀ d : X n, 0 ≤ dirDeriv f z d

/-- Coordinatewise minimum point (4), p. 479: `z ∈ dom f` and
`f(z + (0, …, d_k, …, 0)) ≥ f(z)` for all `d_k` and all blocks `k`. -/
def IsCoordMin {N : ℕ} {n : Fin N → ℕ} (f : X n → EReal) (z : X n) : Prop :=
  f z ≠ ⊤ ∧ ∀ (k : Fin N) (dk : EuclideanSpace ℝ (Fin (n k))), f z ≤ f (z + Pi.single k dk)

/-- Regularity (5), p. 479: `z ∈ dom f` and `f′(z; d) ≥ 0` for every `d = (d₁, …, d_N)` such that
`f′(z; (0, …, d_k, …, 0)) ≥ 0` for `k = 1, …, N`. -/
def IsRegularAt {N : ℕ} {n : Fin N → ℕ} (f : X n → EReal) (z : X n) : Prop :=
  f z ≠ ⊤ ∧ ∀ d : X n, (∀ k, 0 ≤ dirDeriv f z (Pi.single k (d k))) → 0 ≤ dirDeriv f z d

/-- "`f(x₁, …, x_N)` is pseudoconvex in `(x_i)_{i ∈ I}`" (pp. 477–478): for every value of the
blocks outside `I`, the function of the blocks in `I` is pseudoconvex, i.e.
`f(x + d) ≥ f(x)` whenever `x ∈ dom f`, `d` vanishes off the blocks in `I`, and `f′(x; d) ≥ 0`. -/
def PseudoconvexIn {N : ℕ} {n : Fin N → ℕ} (f : X n → EReal) (I : Set (Fin N)) : Prop :=
  ∀ x d : X n, (∀ j, j ∉ I → d j = 0) → f x ≠ ⊤ → 0 ≤ dirDeriv f x d → f x ≤ f (x + d)

/-- "`f(x₁, …, x_N)` has at most one minimum (point) in `x_k`" (pp. 477–478): for every value of
the other blocks, the function `x_k ↦ f(x₁, …, x_N)` has at most one minimum point, a minimum point
being a point of its effective domain at which it attains its infimum. -/
def AtMostOneMinIn {N : ℕ} {n : Fin N → ℕ} (f : X n → EReal) (k : Fin N) : Prop :=
  ∀ (x : X n) (a b : EuclideanSpace ℝ (Fin (n k))),
    f (Function.update x k a) ≠ ⊤ →
    (∀ c, f (Function.update x k a) ≤ f (Function.update x k c)) →
    (∀ c, f (Function.update x k b) ≤ f (Function.update x k c)) → a = b

/-- A run of the BCD method (2)–(3), §2, p. 478. `s r` is the block chosen at iteration `r + 1`
(the step from `x^r` to `x^{r+1}`); `x 0 ∈ dom f`; `x^{r+1}` agrees with `x^r` off block `s r`
and minimizes `f` over that block with the other blocks fixed. -/
def IsBCDRun {N : ℕ} {n : Fin N → ℕ} (f : X n → EReal) (s : ℕ → Fin N) (x : ℕ → X n) : Prop :=
  f (x 0) ≠ ⊤ ∧ ∀ r, (∀ j, j ≠ s r → x (r + 1) j = x r j) ∧
    ∀ y, f (x (r + 1)) ≤ f (Function.update (x r) (s r) y)

/-- Essentially cyclic rule (p. 478): there is `T ≥ N` such that every block is chosen at least once
in any `T` consecutive iterations. -/
def IsEssCyclic {N : ℕ} (s : ℕ → Fin N) : Prop :=
  ∃ T : ℕ, N ≤ T ∧ ∀ (r : ℕ) (k : Fin N), ∃ j < T, s (r + j) = k

/-- Cyclic rule (p. 478): block `k` is chosen at iterations `k, k + N, k + 2N, …`. -/
def IsCyclic {N : ℕ} (s : ℕ → Fin N) : Prop :=
  ∀ r, (s r : ℕ) = r % N

/-- `g` is Gâteaux-differentiable at `z`: there is a linear functional `L` (the map
`d ↦ ⟨∇g(z), d⟩`) with `[g(z + λd) − g(z)]/λ → L(d)` as `λ → 0`, `λ ≠ 0`, for every `d`. -/
def GateauxAt {N : ℕ} {n : Fin N → ℕ} (g : X n → EReal) (z : X n) : Prop :=
  ∃ L : X n →L[ℝ] ℝ, ∀ d : X n,
    Tendsto (fun t : ℝ => (g (z + t • d) - g z) * ((t⁻¹ : ℝ) : EReal)) (𝓝[≠] 0) (𝓝 (L d : EReal))

/-- Assumption A1 (p. 479): `dom f₀` is open and `f₀` is Gâteaux-differentiable on `dom f₀`. -/
def AssumptionA1 {N : ℕ} {n : Fin N → ℕ} (f0 : X n → EReal) : Prop :=
  IsOpen (dom f0) ∧ ∀ z ∈ dom f0, GateauxAt f0 z

/-- Assumption A2 (p. 479): `f₀` is Gâteaux-differentiable on `int(dom f₀)` and, for every
`z ∈ dom f ∩ bdry(dom f₀)` with `bdry(S) = S \ int(S)`, some block step strictly decreases `f`. -/
def AssumptionA2 {N : ℕ} {n : Fin N → ℕ} (f0 : X n → EReal)
    (fk : (k : Fin N) → EuclideanSpace ℝ (Fin (n k)) → EReal) : Prop :=
  (∀ z ∈ interior (dom f0), GateauxAt f0 z) ∧
    ∀ z : X n, fSum f0 fk z ≠ ⊤ → z ∈ dom f0 \ interior (dom f0) →
      ∃ (k : Fin N) (dk : EuclideanSpace ℝ (Fin (n k))),
        fSum f0 fk (z + Pi.single k dk) < fSum f0 fk z

end TsengBCD.Stationary


