-- Prove2me | Definitions.Def_AffinePolicies_LargeGap_Setting
-- name    : AffinePolicies_LargeGap_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T12:49:01.514151+00:00
-- url     : https://prove2.me/theorems/404bea51-7913-4da8-9280-1696d3c05cb1
-- title:
--   (1), PDF p. 2 and (19), PDF p. 16 — Π_Adapt(𝒰), z_Adapt, z_Aff, and the large-gap instance ℐ
-- statement:
--   This file fixes the two-stage adaptive problem of Bertsimas and Goyal and the large-gap instance of their Section 4.
--
--   **The two-stage problem (1).** Let $A\in\mathbb R^{m\times n_1}$, $B\in\mathbb R^{m\times n_2}$, $c\in\mathbb R^{n_1}$, $d\in\mathbb R^{n_2}$ and $\mathcal U\subseteq\mathbb R^m$. A pair $(x,y)$ consisting of a first-stage decision $x\in\mathbb R^{n_1}$ and a second-stage policy $y:\mathbb R^m\to\mathbb R^{n_2}$ is *feasible* if $x\ge 0$ and, for every $b\in\mathcal U$,
--   $$y(b)\ge 0,\qquad Ax+By(b)\ge b$$
--   (componentwise). A real $t$ *bounds the worst-case cost* of $(x,y)$ if $c^\top x+d^\top y(b)\le t$ for every $b\in\mathcal U$. The optimal value of the fully-adaptable problem is
--   $$z_{\mathrm{Adapt}}(\mathcal U)=\inf\{t : \text{some feasible }(x,y)\text{ has worst-case cost}\le t\}.$$
--   An *affine policy* is $y(b)=Pb+q$ with $P\in\mathbb R^{n_2\times m}$, $q\in\mathbb R^{n_2}$; $z_{\mathrm{Aff}}(\mathcal U)$ is the same infimum restricted to feasible pairs whose policy is affine. Feasibility requires $Pb+q\ge 0$ for every $b\in\mathcal U$. A feasible $(x,y)$ is an *optimal fully-adaptable solution* if every worst-case bound achieved by some feasible solution is also a bound for $(x,y)$; an *optimal affine solution* is defined in the same way among affine policies.
--
--   **The instance $\mathcal I$ of (19).** Fix $m\in\mathbb N$ and $\delta\in\mathbb R$, and set $n_1=n_2=m$,
--   $$\theta_0=\frac{1}{m^{(1-\delta)/2}},\qquad r=\lceil m^{1-\delta}\rceil .$$
--   The data are $c=0$, $d=e=(1,\dots,1)^\top$, $A=0$, and $B_{ij}=1$ if $i=j$, $B_{ij}=\theta_0$ otherwise. The uncertainty set is the convex hull
--   $$\mathcal U=\operatorname{conv}\Bigl(\{0\}\cup\{e_1,\dots,e_m\}\cup\{\tfrac{1}{\sqrt m}e\}\cup\{\theta_0\mathbf 1_S : S\subseteq\{1,\dots,m\},\ |S|=r\}\Bigr),$$
--   where $\mathbf 1_S$ is the indicator vector of $S$; the points $\theta_0\mathbf 1_S$ are $b^{m+2}=\theta_0(1,\dots,1,0,\dots,0)$ (with $r$ ones) and all its coordinate permutations.
--
--   **Definition 2.** A set $\mathcal U\subseteq\mathbb R^m$ is *permutation-invariant* with respect to a permutation $\tau$ of $\{1,\dots,m\}$ if $x\in\mathcal U\iff x^\tau\in\mathcal U$ for every $x$, where $x^\tau=(x_{\tau(1)},\dots,x_{\tau(m)})$.
--
--   These are the objects of every statement of the mission.
--
--   **Formalization Note** Vectors are functions `Fin m → ℝ` with the componentwise order; coordinates are 0-based. The optimal values are infima of epigraph sets (a Lean real infimum of an empty set is $0$, so statements that need the set nonempty say so). Powers $m^{a}$ are real powers (`Real.rpow`). The paper's count $N=\binom mr+m+2$ of generators is not used: $\mathcal U$ is defined by its generating set.
-- source:
--   Bertsimas & Goyal, On the power and limitations of affine policies in two-stage adaptive optimization, Math. Program. Ser. A, DOI 10.1007/s10107-011-0444-4, (1), PDF p. 2; (19), PDF p. 16; Definition 2, PDF p. 11

import Mathlib
import Definitions.Def_AffinePolicies_Simplex_Setting
import Definitions.Def_AffinePolicies_TwoGap_Setting

namespace AffinePolicies.LargeGap

open Matrix

variable {m n₁ n₂ : ℕ}

/-! ### The instance ℐ of (19), with `n₁ = n₂ = m` -/

/-- `θ₀ = 1 / m^{(1-δ)/2}` (real power). -/
noncomputable def theta0 (m : ℕ) (δ : ℝ) : ℝ := 1 / (m : ℝ) ^ ((1 - δ) / 2)

/-- `r = ⌈m^{1-δ}⌉`. -/
noncomputable def rr (m : ℕ) (δ : ℝ) : ℕ := ⌈(m : ℝ) ^ (1 - δ)⌉₊

/-- `A_ij = 0`. -/
def A19 (m : ℕ) : Matrix (Fin m) (Fin m) ℝ := 0

/-- `B_ij = 1` if `i = j`, `θ₀` otherwise. -/
noncomputable def B19 (m : ℕ) (δ : ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  fun i j => if i = j then 1 else theta0 m δ

/-- `c = 0`. -/
def c19 (m : ℕ) : Fin m → ℝ := 0

/-- `d = (1, …, 1)ᵀ`. -/
def d19 (m : ℕ) : Fin m → ℝ := fun _ => 1

/-- `θ₀ · 1_S`: the vector equal to `θ₀` on the coordinates in `S` and `0` elsewhere.
For `S.card = r` these are `b^{m+2}` (`S` = the first `r` coordinates) and its
permutations `bʲ`, `j ≥ m + 3`. -/
noncomputable def blockPt (m : ℕ) (δ : ℝ) (S : Finset (Fin m)) : Fin m → ℝ :=
  fun i => if i ∈ S then theta0 m δ else 0

/-- `𝒰 = conv{b⁰, b¹, …, b^N}`: the convex hull of `b⁰ = 0`, `bʲ = e_j` (`j = 1, …, m`),
`b^{m+1} = (1/√m)·e`, and the points `θ₀ · 1_S` for every set `S` of exactly `r`
coordinates. -/
noncomputable def U19 (m : ℕ) (δ : ℝ) : Set (Fin m → ℝ) :=
  convexHull ℝ ({0} ∪ Set.range (fun j : Fin m => (Pi.single j (1 : ℝ) : Fin m → ℝ)) ∪
    {fun _ => 1 / Real.sqrt m} ∪
    {b | ∃ S : Finset (Fin m), S.card = rr m δ ∧ b = blockPt m δ S})

/-! ### Permutations: Definition 2 -/

end AffinePolicies.LargeGap


