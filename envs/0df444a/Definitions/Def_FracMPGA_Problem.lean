-- Prove2me | Definitions.Def_FracMPGA_Problem
-- name    : FracMPGA_Problem
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:39:53.704023+00:00
-- url     : https://prove2.me/theorems/03daf162-ae08-48c2-ac9d-04d747212d25
-- title:
--   The fractional program (1) and its extended objectives $F$ (8) and $Q$ (9)
-- statement:
--   The data of the single-ratio fractional program
--   $$
--   \min\Big\{\frac{f(x)+h(x)}{g(x)}:\ x\in\Omega\Big\},\qquad \Omega=\{x\in\mathbb R^n: g(x)\ne0\},
--   $$
--   with a block-separable $f(x)=\sum_{i=1}^N f_i(x_i)$, where the subvectors $x_1,\dots,x_N$ partition the coordinates of $x$ and $f_i:\mathbb R^{n_i}\to(-\infty,+\infty]$.
--
--   From the data the module defines $\zeta=f+h$, $\eta(x,y)=\langle x,y\rangle-g^*(y)$, the block $x_i$ of $x$, the update $[x_1;\dots;x_{i-1};z;x_{i+1};\dots;x_N]$, and the two extended objectives
--   $$
--   F(x)=\begin{cases}\dfrac{f(x)+h(x)}{g(x)}, & x\in\Omega\cap\operatorname{dom}f,\\ +\infty,&\text{else,}\end{cases}\qquad
--   Q(x,y)=\begin{cases}\dfrac{\zeta(x)}{\eta(x,y)}, & (x,y)\in\operatorname{dom}f\times\operatorname{dom}g^*,\ \eta(x,y)>0,\\ +\infty,&\text{else.}\end{cases}
--   $$
--   $Q$ is also given as a function on the Euclidean product $\mathbb R^n\times\mathbb R^n$, for its subdifferentials and KL property.
--
--   **Formalization Note** The block structure is a surjective map from coordinates to blocks; paper block $i\in\{1,\dots,N\}$ is the index $i-1$. The function $h$ is real-valued: the paper's $h:\mathbb R^n\to(-\infty,+\infty]$ only enters through $\zeta$ and through $\nabla h$ on the open set $\Omega$, and its values off $\Omega$ change neither $F$, $Q$, a critical point nor an accepted step of the algorithm.
-- source:
--   Zhou, Zhang, Li, An equivalent reformulation and multi-proximity gradient algorithms for a class of nonsmooth fractional programming, arXiv:2311.00957v2, §1, p.2 (problem (1)); §3, p.9, (8) and (9)

import Mathlib
import Definitions.Def_fenchelConjugate
import Definitions.Def_FracMPGA_liftedRatio

open scoped InnerProductSpace

namespace FracMPGA

/-- The data of the **single-ratio fractional program** (1) of Zhou, Zhang, Li,
arXiv:2311.00957v2, §1, p.2:
`min { (f(x) + h(x)) / g(x) : x ∈ Ω }`, `Ω := {x ∈ ℝⁿ : g(x) ≠ 0}`, with the block-separable
numerator `f(x) = Σ_{i=1}^N f_i(x_i)`, where the subvectors `x_1, …, x_N` partition the
components of `x` and `f_i : ℝ^{n_i} → (−∞, +∞]`.

* `blk j` is the block containing coordinate `j`; `blk` is surjective, so every block is a
  nonempty subvector. Paper block `i ∈ {1, …, N}` is the index `i − 1 : Fin N`.
* `fb i` is `f_i`, a function on the block space `ℝ^{n_i}` = `EuclideanSpace ℝ {j // blk j = i}`.
* `h` and `g` are the remaining functions; `g` is real-valued, as Assumption 1(iii) requires.

**Formalization Note** The paper takes `h : ℝⁿ → (−∞, +∞]` proper lower semicontinuous and only
uses it through `ζ = f + h` and through `∇h` on the open set `Ω`. Here `h` is real-valued; its
values off `Ω` never change `F`, `Q`, a critical point, or an accepted step of Algorithm 1 (a
trial point outside `Ω` fails the line-search test because `η(·, y) ≤ g = 0` there while
`ζ ≥ 0` on `dom f`). The hypotheses on the data are collected in `Assumption1`. -/
structure Problem (n N : ℕ) where
  /-- the block of each coordinate -/
  blk : Fin n → Fin N
  /-- every block is nonempty -/
  blk_surj : Function.Surjective blk
  /-- the block functions `f_i` -/
  fb : (i : Fin N) → EuclideanSpace ℝ {j // blk j = i} → EReal
  /-- the smooth part `h` of the numerator -/
  h : Vec n → ℝ
  /-- the denominator `g` -/
  g : Vec n → ℝ

namespace Problem

variable {n N : ℕ} (P : Problem n N)

/-- The `i`-th block `x_i` of `x`. -/
def block (x : Vec n) (i : Fin N) : EuclideanSpace ℝ {j // P.blk j = i} :=
  WithLp.toLp 2 (fun j => x j.1)

/-- `x` with its `i`-th block replaced by `z`: the vector
`[x_1; …; x_{i−1}; z; x_{i+1}; …; x_N]` of Step 2-X of Algorithm 1 (p.14). -/
def blockUpdate (x : Vec n) (i : Fin N) (z : EuclideanSpace ℝ {j // P.blk j = i}) : Vec n :=
  WithLp.toLp 2 (fun j => if hj : P.blk j = i then z ⟨j, hj⟩ else x j)

/-- The block-separable function `f(x) = Σ_{i=1}^N f_i(x_i)` (p.2), in `EReal`. -/
noncomputable def f (x : Vec n) : EReal := ∑ i, P.fb i (P.block x i)

/-- `Ω := {x ∈ ℝⁿ : g(x) ≠ 0}` (p.2). -/
def Omega : Set (Vec n) := {x | P.g x ≠ 0}

/-- `ζ(x) := f(x) + h(x)` (p.9). -/
noncomputable def zeta (x : Vec n) : EReal := P.f x + (P.h x : EReal)

/-- `η(x, y) := ⟨x, y⟩ − g*(y)` (p.9), valued in `[−∞, +∞)`. -/
noncomputable def eta (x y : Vec n) : EReal := liftDen P.g x y

/-- The **extended objective** `F` of problem (1), equation (8), p.9:
`F(x) := (f(x) + h(x)) / g(x)` if `x ∈ Ω ∩ dom(f)`, and `F(x) := +∞` otherwise.

**Formalization Note** On `Ω ∩ dom(f)` the numerator `ζ(x)` is finite (each `f_i` is bounded
below by Assumption 1), and the value is the real quotient. -/
noncomputable def F (x : Vec n) : EReal :=
  if P.g x ≠ 0 ∧ P.f x ≠ ⊤ then (((P.zeta x).toReal / P.g x : ℝ) : EReal) else ⊤

/-- The **extended objective** `Q` of the reformulated problem (5), equation (9), p.9:
`Q(x, y) := ζ(x) / η(x, y)` if `(x, y) ∈ dom(f) × dom(g*)` and `η(x, y) > 0`, and
`Q(x, y) := +∞` otherwise. It is the lifted ratio `ρ` of p.6 with `φ₁ = ζ`, `φ₂ = g`
(`dom ζ = dom f` because `h` is real-valued). -/
noncomputable def Q (x y : Vec n) : EReal := liftedRatio P.zeta P.g x y

/-- `Q` as a function on the Euclidean product `ℝⁿ × ℝⁿ` (`Pair n`); subdifferentials and the KL
property of `Q` are taken for this function. -/
noncomputable def Qp (p : Pair n) : EReal := P.Q p.ofLp.1 p.ofLp.2

end Problem

end FracMPGA


