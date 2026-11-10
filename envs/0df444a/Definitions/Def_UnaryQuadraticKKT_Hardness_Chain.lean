-- Prove2me | Definitions.Def_UnaryQuadraticKKT_Hardness_Chain
-- name    : UnaryQuadraticKKT_Hardness_Chain
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T15:43:34.305933+00:00
-- url     : https://prove2.me/theorems/aca4aa48-c7c0-4a42-b58d-25a73bacb108
-- title:
--   The exact quadratic chain and its explicit auxiliary vector
-- statement:
--   Let $k\ge1$, $s\in\{-1,1\}$ and $m=k+2$. For real $x,y$ and $u\in\mathbb R^m$, define
--   $$
--   G(x,y,u)=3\sum_{i=1}^{m-1}(2u_i-u_{i+1})^2+9u_m^2-6xu_1+6syu_m+x^2+y^2,
--   \qquad g(x,y)=s2^{-k}xy.
--   $$
--   The explicitly defined vector is
--   $$u_i^*(x,y)=\frac{2^{1-i}x-s2^{i-m}y}{3}.$$
--   Its global minimization and KKT properties are not assumed. Global minimality means feasibility in $[-1,1]^m$ and comparison with every feasible vector. The general interval KKT predicate uses actual coordinate derivatives, feasibility, a nonnegative derivative at a lower endpoint, zero in the interior and a nonpositive derivative at an upper endpoint. In particular the auxiliary lower boundary is $-1$.
--
--   This layer supplies the exact functions and feasible sets for Lemmas 4.3–4.5, including endpoints $x,y=0,1$, either sign, and coinciding endpoint values.
--
--   **Formalization Note** Coordinate derivatives use the public derivative along a coordinate-update line. The chain is indexed by $\mathrm{Fin}(k+2)$ and all negative exponents are integer powers of the positive real number two. No conclusion is a field of a structure or an axiom.
-- source:
--   Argyrios Deligkas, Michail Fasoulakis, Stavros Ioannidis, STOC 2027 submission #1093 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1093.pdf, Section 4.2, Equations (6)–(7) and (15), pp.6–8. Canonical PDF SHA256 f4a6f774376cfc40e24acff39a11029782994f72d85350d10b69fc17030bd0a5

import Mathlib
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Quadratics

set_option autoImplicit false

namespace UnaryQuadraticKKT.Hardness
open Finset NetworkEquilibriumCLS.LinearNash

/-- Actual coordinate derivatives and feasibility on a box with specified endpoints. -/
noncomputable def IntervalKKT {ι : Type*} [DecidableEq ι]
    (lower upper : ι → ℝ) (f : (ι → ℝ) → ℝ) (z : ι → ℝ) : Prop :=
  (∀ i, lower i ≤ z i ∧ z i ≤ upper i) ∧
  ∀ i, (lower i < z i → coordinatePartial f z i ≤ 0) ∧
    (z i < upper i → 0 ≤ coordinatePartial f z i)

def InSignedCube {ι : Type*} (u : ι → ℝ) : Prop := ∀ i, -1 ≤ u i ∧ u i ≤ 1

/-- Eq. (6). Fin (k+2) uses zero-based indices; there are k+1 adjacent edges. -/
noncomputable def chainValue (k : ℕ) (s : ℤ) (x y : ℝ) (u : Fin (k + 2) → ℝ) : ℝ :=
  3 * ∑ i : Fin (k + 1),
    (2 * u ⟨i.val, by omega⟩ - u ⟨i.val + 1, by omega⟩) ^ 2 +
  9 * (u ⟨k + 1, by omega⟩) ^ 2 - 6 * x * u ⟨0, by omega⟩ +
  6 * (s : ℝ) * y * u ⟨k + 1, by omega⟩ + x ^ 2 + y ^ 2

/-- Eq. (15), i_source = i.val+1. Both exponents are integers, not truncated naturals. -/
noncomputable def chainMinimizer (k : ℕ) (s : ℤ) (x y : ℝ) (i : Fin (k + 2)) : ℝ :=
  ((2 : ℝ) ^ (-(i.val : ℤ)) * x -
    (s : ℝ) * (2 : ℝ) ^ ((i.val : ℤ) + 1 - ((k : ℤ) + 2)) * y) / 3

noncomputable def chainMonomial (k : ℕ) (s : ℤ) (x y : ℝ) : ℝ :=
  (s : ℝ) * (2 : ℝ) ^ (-(k : ℤ)) * x * y

noncomputable def ChainGlobalMin (k : ℕ) (s : ℤ) (x y : ℝ)
    (u : Fin (k + 2) → ℝ) : Prop :=
  InSignedCube u ∧ ∀ v : Fin (k + 2) → ℝ, InSignedCube v →
    chainValue k s x y u ≤ chainValue k s x y v

end UnaryQuadraticKKT.Hardness


