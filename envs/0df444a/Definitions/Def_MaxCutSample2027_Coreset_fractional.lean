-- Prove2me | Definitions.Def_MaxCutSample2027_Coreset_fractional
-- name    : MaxCutSample2027_Coreset_fractional
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:43:27.64139+00:00
-- url     : https://prove2.me/theorems/1b8d8de1-3a60-4a0b-a635-7f66833b9f1a
-- title:
--   Fractional cut boxes and comparison functionals
-- statement:
--   For vectors $r,s,q,c\in\mathbb R^V$ and a real kernel $L$, write $a^\top Lc=\sum_{u,v}a_uL_{uv}c_v$. For nonnegative vertex weights define
--   $$Z(r)=\{a:0\le a_v\le r_v\ \forall v\},\qquad F_L(r)=\max_{a\in Z(r)}a^\top L(r-a),\qquad M_q(c)=\max_{a\in Z(q)}a^\top Lc.$$
--   The symmetric comparison region and gap are
--   $$\mathcal C(r,s)=\operatorname{conv}(Z(r)\cup(-Z(r))\cup Z(s)\cup(-Z(s))),\qquad
--   \Delta_L(r,s)=\max_{c\in\mathcal C(r,s)}|M_r(c)-M_s(c)|.$$
--   An auxiliary operation denotes $\max_{c\in C}|a^\top Lc|$ for a specified set $C$. The source uses $L=K$. Importantly, $M_q$ is defined by its optimization problem; its closed form remains the content of equation (2.6).
--
--   These objects provide a shared interface for all fractional-cut milestones. **Formalization Note** Each real maximum is encoded by the supremum of its image. Under the nonnegative-vector and probability-vector domains in the theorem statements, the boxes and convex hull are nonempty compact subsets of a finite-dimensional real space. The displayed objectives are continuous, including $M_q$ as a function of $c$, so the suprema are finite and attained. On an empty domain the real supremum defaults to zero; such a domain is never used in these claims.
-- source:
--   Itamar Bender, Robert Krauthgamer, STOC 2027 submission #147 (October 2026), §2.2, equation (2.5), p. 8; §2.3, equations (2.6)–(2.8), p. 9; Lemma 2.6, p. 10. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/147.pdf (PDF SHA-256 54bb82836bdc80e7729d444c36f7299cb7d50838d4ee557decb3495e61236fa7).

import Definitions.Def_MaxCutSample2027_Coreset_model
open scoped BigOperators
noncomputable section

namespace MaxCutSample2027.Coreset

/-- Fractional cuts, for a nonnegative vector r. -/
def Z {V : Type*} (r : V → ℝ) : Set (V → ℝ) :=
  {a | ∀ v, 0 ≤ a v ∧ a v ≤ r v}

/-- aᵀ L c, with the row index first. -/
def bilinear {V : Type*} [Fintype V] (L : V → V → ℝ) (a c : V → ℝ) : ℝ :=
  ∑ u, ∑ v, a u * L u v * c v

/-- Equation (2.5). On nonnegative r this supremum is attained on a compact box. -/
def FK {V : Type*} [Fintype V] (L : V → V → ℝ) (r : V → ℝ) : ℝ :=
  sSup ((fun a => bilinear L a (r - a)) '' Z r)

/-- The defining maximum in (2.6), not its closed form. -/
def M {V : Type*} [Fintype V] (L : V → V → ℝ) (q c : V → ℝ) : ℝ :=
  sSup ((fun a => bilinear L a c) '' Z q)

/-- Equation (2.7): the convex hull of four boxes, including their negatives. -/
def Ccal {V : Type*} (r s : V → ℝ) : Set (V → ℝ) :=
  convexHull ℝ (Z r ∪ ((fun a : V → ℝ => -a) '' Z r) ∪
    Z s ∪ ((fun a : V → ℝ => -a) '' Z s))

/-- Equation (2.8). For probability vectors this is a maximum over a compact set. -/
def DeltaK {V : Type*} [Fintype V] (L : V → V → ℝ) (r s : V → ℝ) : ℝ :=
  sSup ((fun c => |M L r c - M L s c|) '' Ccal r s)

/-- The maximum used in both conclusions of Lemma 2.6. -/
def maxAbsLinear {V : Type*} [Fintype V] (L : V → V → ℝ)
    (a : V → ℝ) (C : Set (V → ℝ)) : ℝ :=
  sSup ((fun c => |bilinear L a c|) '' C)

end MaxCutSample2027.Coreset


