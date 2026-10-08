-- Prove2me | Definitions.Def_IncProx_Randomized_Basic
-- name    : IncProx_Randomized_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:39:54.18727+00:00
-- url     : https://prove2.me/theorems/43fc57ed-db06-4597-a421-744b092fcd64
-- title:
--   Problem (5)–(6), $F^*$, $X^*$, the randomized iterations (42)–(44), the past history $\mathcal F_k$ and Assumptions 3–4
-- statement:
--   This file fixes the objects of Section 4 of Bertsekas, *Incremental Proximal Methods for Large Scale Convex Optimization*.
--
--   **The problem.** Let $X\subseteq\mathbb R^n$ be a nonempty closed convex set and let $f_i,h_i:\mathbb R^n\to\mathbb R$, $i=1,\dots,m$, be real-valued convex functions. With $F_i=f_i+h_i$ the problem is
--   $$\text{minimize } F(x)=\sum_{i=1}^m F_i(x)\quad\text{subject to } x\in X. \qquad (5)\text{–}(6)$$
--   Its optimal value is $F^*=\inf_{x\in X}F(x)\in[-\infty,\infty)$ and its optimal set is $X^*=\{x^*\in X\mid F(x^*)=F^*\}$, which may be empty. A vector $g$ is a **subgradient** of $f$ at $x$ (written $\tilde\nabla f(x)$) if $f(x)+g'(y-x)\le f(y)$ for all $y$, and $P_X(u)$ is the Euclidean projection of $u$ on $X$, the point of $X$ nearest to $u$.
--
--   **One step.** With component $i$ and stepsize $a>0$, the three iterations take $x$ through $z$ to $x'$:
--   1. (19)/(42): $z=P_X(x-a\tilde\nabla f_i(z))$, $x'=P_X(z-a\tilde\nabla h_i(z))$;
--   2. (20)/(43): $z=x-a\tilde\nabla f_i(z)$, $x'=P_X(z-a\tilde\nabla h_i(z))$;
--   3. (21)/(44): $z=x-a\tilde\nabla h_i(x)$, $x'=P_X(z-a\tilde\nabla f_i(x'))$.
--
--   The subgradient of $f_i$ is the one at the point the step names that makes the implicit equation hold; such a step is exactly the proximal step of the paper.
--
--   **The randomized run.** On a probability space $(\Omega,\mathcal F,\mu)$ the component used at iteration $k$ is a random variable $\omega_k$ with values in $\{1,\dots,m\}$. For every $k$ and every component $i$ the run carries the step that iteration $k$ would take from $x_k$ "if $\omega_k$ would be $i$": the point $z_k^i$, the two subgradients, and the would-be next iterate $x_{k+1}^i$. The realized step is $z_k=z_k^{\omega_k}$, $x_{k+1}=x_{k+1}^{\omega_k}$. The **past history** at $k$ is the $\sigma$-algebra
--   $$\mathcal F_k=\sigma(x_k,z_{k-1},x_{k-1},\dots,z_0,x_0).$$
--
--   **Assumptions 3(a)/4(a).** Each $\omega_k$ is uniformly distributed over $\{1,\dots,m\}$ and independent of $\mathcal F_k$.
--
--   **Assumption 3(b)** (for (42), (43)). There is $c\in\mathbb R$ such that for all $k$, with probability 1, for all $i$,
--   $$\max\{\|\tilde\nabla f_i(z_k^i)\|,\|\tilde\nabla h_i(z_k^i)\|\}\le c,\qquad \max\{f_i(x_k)-f_i(z_k^i),\,h_i(x_k)-h_i(z_k^i)\}\le c\|x_k-z_k^i\|.$$
--
--   **Assumption 4(b)** (for (44)). There is $c\in\mathbb R$ such that for all $k$, with probability 1, for all $i$,
--   $$\max\{\|\tilde\nabla f_i(x_{k+1}^i)\|,\|\tilde\nabla h_i(x_k)\|\}\le c,\qquad f_i(x_k)-f_i(x_{k+1}^i)\le c\|x_k-x_{k+1}^i\|.$$
--
--   The predicate `RandHyp` bundles a run of one of (42)–(44) with stepsizes $\alpha_k$, a deterministic starting point $x_0$, measurability of the iterates, $\mathcal F_k$-measurability of the would-be step at $k$, Assumption 3(a)/4(a), and Assumption 3(b) or 4(b). The file also defines the first index $N=\min\{k\ge0\mid x_k\in L\}\in\mathbb N\cup\{\infty\}$ at which a run enters a set $L$.
--
--   These objects are the common setting of Propositions 7–9 and of the inequalities (58)–(59).
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)`; components are indexed by `Fin m`, i.e. $0,\dots,m-1$ instead of $1,\dots,m$. $P_X$ is the predicate "$p\in X$ and $\|u-p\|\le\|u-y\|$ for all $y\in X$"; for closed convex nonempty $X$ the projection exists and is unique, so no junk value enters. $F^*$ is an `EReal` infimum, so $F^*=-\infty$ is representable, and $X^*$ is defined through it. The paper states the standing assumptions of p. 4 once; here they are the structure `Problem.Standing`. The paper says $\omega_k$ is "independent of the past history"; we state this as independence of $\sigma(\omega_k)$ from $\mathcal F_k$, and add as hypotheses what makes it meaningful: the iterates are measurable, the would-be step at $k$ (for every $i$) is $\mathcal F_k$-measurable, and $x_0$ is a fixed vector. The stepsize enters (42)–(44) as one sequence $\alpha_k$; the paper prints a constant $\alpha$ in (42)–(43) because §4 begins with constant stepsizes.
-- source:
--   Bertsekas, Incremental Proximal Methods for Large Scale Convex Optimization, LIDS-P-2847 (rev. March 2011), p. 4 (5)–(6), p. 7 (19)–(21), p. 8 (F*, X*), p. 15 (42)–(44) and Assumption 3, p. 16 Assumption 4

import Mathlib

namespace IncProx.Randomized

open Filter Topology MeasureTheory ProbabilityTheory

/-- ℝⁿ with the standard Euclidean norm ‖·‖ and inner product x′y (footnote 1). -/
abbrev Vec (n : ℕ) := EuclideanSpace ℝ (Fin n)

variable {n m : ℕ}

/-- `g` is a subgradient of the real-valued function `f` at `x` (footnote 2: ∇̃f(x) ∈ ∂f(x)). -/
def IsSubgrad (f : Vec n → ℝ) (x g : Vec n) : Prop :=
  ∀ y, f x + inner ℝ g (y - x) ≤ f y

/-- `p = P_X(u)`: `p` is the Euclidean projection of `u` on `X` (a nearest point of `X`). -/
def IsProj (X : Set (Vec n)) (u p : Vec n) : Prop :=
  p ∈ X ∧ ∀ y ∈ X, ‖u - p‖ ≤ ‖u - y‖

/-- The data of problem (5)–(6): the set `X` and the components `f i`, `h i`, `i : Fin m`. -/
structure Problem (n m : ℕ) where
  X : Set (Vec n)
  f : Fin m → Vec n → ℝ
  h : Fin m → Vec n → ℝ

namespace Problem

/-- Standing assumptions (p. 4): `X` nonempty closed convex; `f i`, `h i` real-valued convex. -/
structure Standing (P : Problem n m) : Prop where
  X_nonempty : P.X.Nonempty
  X_closed : IsClosed P.X
  X_convex : Convex ℝ P.X
  f_convex : ∀ i, ConvexOn ℝ Set.univ (P.f i)
  h_convex : ∀ i, ConvexOn ℝ Set.univ (P.h i)

/-- `F_i = f_i + h_i` (6). -/
def Fi (P : Problem n m) (i : Fin m) (x : Vec n) : ℝ := P.f i x + P.h i x

/-- `F = Σ_i F_i` (5). -/
noncomputable def F (P : Problem n m) (x : Vec n) : ℝ := ∑ i, P.Fi i x

/-- `F* = inf_{x ∈ X} F(x)` (p. 8), in `EReal`: it may be `−∞`. -/
noncomputable def Fstar (P : Problem n m) : EReal := ⨅ x ∈ P.X, ((P.F x : ℝ) : EReal)

/-- `X* = {x* ∈ X | F(x*) = F*}` (p. 8); possibly empty. -/
def Xstar (P : Problem n m) : Set (Vec n) := {x | x ∈ P.X ∧ ((P.F x : ℝ) : EReal) = P.Fstar}

end Problem

/-- The three iterations (19), (20), (21) of p. 7; their randomized versions are (42), (43), (44). -/
inductive Alg
  | a19 | a20 | a21

/-- One step of iteration (19), (20) or (21) with component `i` and stepsize `a`: from `x` through
`z` to `x'`, where `gF` is the subgradient of `f i` and `gH` the subgradient of `h i` the step uses.
(19): z = P_X(x − a gF), gF ∈ ∂f_i(z);  x' = P_X(z − a gH), gH ∈ ∂h_i(z).
(20): z = x − a gF,      gF ∈ ∂f_i(z);  x' = P_X(z − a gH), gH ∈ ∂h_i(z).
(21): z = x − a gH,      gH ∈ ∂h_i(x);  x' = P_X(z − a gF), gF ∈ ∂f_i(x'). -/
def Step (P : Problem n m) : Alg → Fin m → ℝ → Vec n → Vec n → Vec n → Vec n → Vec n → Prop
  | .a19, i, a, x, z, gF, gH, x' => IsSubgrad (P.f i) z gF ∧ IsProj P.X (x - a • gF) z ∧
      IsSubgrad (P.h i) z gH ∧ IsProj P.X (z - a • gH) x'
  | .a20, i, a, x, z, gF, gH, x' => IsSubgrad (P.f i) z gF ∧ z = x - a • gF ∧
      IsSubgrad (P.h i) z gH ∧ IsProj P.X (z - a • gH) x'
  | .a21, i, a, x, z, gF, gH, x' => IsSubgrad (P.h i) x gH ∧ z = x - a • gH ∧
      IsSubgrad (P.f i) x' gF ∧ IsProj P.X (z - a • gF) x'

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A run of the randomized iteration `A` ((42), (43) or (44) = `Step` with `.a19`, `.a20`, `.a21`)
with stepsizes `α k`. For every k, every component i and every outcome s, `zc k i s`, `gFc k i s`,
`gHc k i s`, `xc k i s` are the z, the two subgradients and the next iterate that the k-th step
produces from `x k s` "if ω_k would be i" (the z_k^i, x_{k+1}^i of Assumptions 3–4); the realized
step is the one with i = ω_k(s). -/
def IsRandRun (P : Problem n m) (A : Alg) (α : ℕ → ℝ) (ω : ℕ → Ω → Fin m)
    (x : ℕ → Ω → Vec n) (zc gFc gHc xc : ℕ → Fin m → Ω → Vec n) : Prop :=
  ∀ k s, (∀ i, Step P A i (α k) (x k s) (zc k i s) (gFc k i s) (gHc k i s) (xc k i s)) ∧
    x (k + 1) s = xc k (ω k s) s

/-- The realized z_k = z_k^{ω_k}. -/
def zOf (ω : ℕ → Ω → Fin m) (zc : ℕ → Fin m → Ω → Vec n) (k : ℕ) (s : Ω) : Vec n :=
  zc k (ω k s) s

/-- The past history F_k = {x_k, z_{k−1}, x_{k−1}, …, z_0, x_0} (pp. 15, 16), as the σ-algebra
generated by x_0, …, x_k and z_0, …, z_{k−1}. -/
def hist (x z : ℕ → Ω → Vec n) (k : ℕ) : MeasurableSpace Ω :=
  (⨆ j ∈ Finset.range (k + 1), MeasurableSpace.comap (x j) inferInstance) ⊔
    (⨆ j ∈ Finset.range k, MeasurableSpace.comap (z j) inferInstance)

/-- Assumptions 3(a) = 4(a): each ω_k is a random variable, uniformly distributed over the m
components, and independent of the past history F_k. -/
def UniformIndepOfPast (μ : Measure Ω) (ω : ℕ → Ω → Fin m) (x z : ℕ → Ω → Vec n) : Prop :=
  ∀ k, Measurable (ω k) ∧ (∀ i, μ {s | ω k s = i} = (m : ENNReal)⁻¹) ∧
    Indep (MeasurableSpace.comap (ω k) inferInstance) (hist x z k) μ

/-- Assumption 3(b) ((45), (46)), for iterations (42)/(43): for every k, with probability 1, for
all i, ‖∇̃f_i(z_k^i)‖ ≤ c, ‖∇̃h_i(z_k^i)‖ ≤ c, f_i(x_k) − f_i(z_k^i) ≤ c‖x_k − z_k^i‖ and
h_i(x_k) − h_i(z_k^i) ≤ c‖x_k − z_k^i‖. -/
def Assumption3b (μ : Measure Ω) (P : Problem n m) (x : ℕ → Ω → Vec n)
    (zc gFc gHc : ℕ → Fin m → Ω → Vec n) (c : ℝ) : Prop :=
  ∀ k, ∀ᵐ s ∂μ, ∀ i, ‖gFc k i s‖ ≤ c ∧ ‖gHc k i s‖ ≤ c ∧
    P.f i (x k s) - P.f i (zc k i s) ≤ c * ‖x k s - zc k i s‖ ∧
    P.h i (x k s) - P.h i (zc k i s) ≤ c * ‖x k s - zc k i s‖

/-- Assumption 4(b) ((47), (48)), for iteration (44); here `gFc k i` is ∇̃f_i(x_{k+1}^i) and
`gHc k i` is ∇̃h_i(x_k): for every k, with probability 1, for all i, both have norm ≤ c and
f_i(x_k) − f_i(x_{k+1}^i) ≤ c‖x_k − x_{k+1}^i‖. -/
def Assumption4b (μ : Measure Ω) (P : Problem n m) (x : ℕ → Ω → Vec n)
    (gFc gHc xc : ℕ → Fin m → Ω → Vec n) (c : ℝ) : Prop :=
  ∀ k, ∀ᵐ s ∂μ, ∀ i, ‖gFc k i s‖ ≤ c ∧ ‖gHc k i s‖ ≤ c ∧
    P.f i (x k s) - P.f i (xc k i s) ≤ c * ‖x k s - xc k i s‖

/-- The part (b) assumption that goes with the iteration: Assumption 3(b) for (42) and (43),
Assumption 4(b) for (44). -/
def RandAssumptionFor (μ : Measure Ω) (P : Problem n m) (A : Alg) (x : ℕ → Ω → Vec n)
    (zc gFc gHc xc : ℕ → Fin m → Ω → Vec n) (c : ℝ) : Prop :=
  match A with
  | .a19 => Assumption3b μ P x zc gFc gHc c
  | .a20 => Assumption3b μ P x zc gFc gHc c
  | .a21 => Assumption4b μ P x gFc gHc xc c

/-- The setting of §4: `x` is a run of the randomized iteration `A` ((42), (43) or (44)) with
stepsizes `α`, components `ω`, would-be steps `zc, gFc, gHc, xc`, deterministic start `x₀` and
constant `c`, such that
* the iterates `x k` are random variables (measurable);
* the would-be step at k (for every component i) is a function of the past history F_k, i.e.
  measurable with respect to `hist x z k`, where z is the realized sequence z_k = z_k^{ω_k};
* Assumption 3(a)/4(a) holds (ω_k uniform on the components and independent of F_k);
* Assumption 3(b) (for (42), (43)) or 4(b) (for (44)) holds with the constant `c`. -/
structure RandHyp (μ : Measure Ω) (P : Problem n m) (A : Alg) (α : ℕ → ℝ)
    (ω : ℕ → Ω → Fin m) (x : ℕ → Ω → Vec n) (zc gFc gHc xc : ℕ → Fin m → Ω → Vec n)
    (x₀ : Vec n) (c : ℝ) : Prop where
  run : IsRandRun P A α ω x zc gFc gHc xc
  start : x 0 = fun _ => x₀
  x_meas : ∀ k, Measurable (x k)
  step_meas : ∀ k i, Measurable[hist x (zOf ω zc) k] (zc k i) ∧
    Measurable[hist x (zOf ω zc) k] (gFc k i) ∧ Measurable[hist x (zOf ω zc) k] (gHc k i) ∧
    Measurable[hist x (zOf ω zc) k] (xc k i)
  omega : UniformIndepOfPast μ ω x (zOf ω zc)
  bound : RandAssumptionFor μ P A x zc gFc gHc xc c

/-- The index of the first iterate in the set `L`, in `ℕ∞` (`⊤` if the run never enters `L`):
N(s) = min{k ≥ 0 | x_k(s) ∈ L}. -/
noncomputable def firstHit (x : ℕ → Ω → Vec n) (L : Set (Vec n)) (s : Ω) : ℕ∞ :=
  ⨅ (k : ℕ) (_ : x k s ∈ L), (k : ℕ∞)

end IncProx.Randomized


