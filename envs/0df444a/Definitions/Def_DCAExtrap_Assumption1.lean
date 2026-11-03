-- Prove2me | Definitions.Def_DCAExtrap_Assumption1
-- name    : DCAExtrap_Assumption1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:23:18.931342+00:00
-- url     : https://prove2.me/theorems/ff8bd041-bf5f-4490-8104-d1ef07f777ce
-- title:
--   Assumption 1 on $f$, $g$, $h$, $\varphi$, $L$, $l$
-- statement:
--   Let $E$ be a finite-dimensional real inner product space. Functions $f,h:E\to\mathbb R$, $g:E\to(-\infty,+\infty]$, a kernel $\varphi:E\to\mathbb R$ and constants $L,l$ satisfy **Assumption 1** when:
--
--   1. (a) $f$ is continuously differentiable; $\varphi$ is continuously differentiable and strongly convex (there is $\rho>0$ such that $\varphi-\tfrac{\rho}{2}\|\cdot\|^2$ is convex); $L>0$, $l\ge0$; and $L\varphi-f$ and $l\varphi+f$ are convex;
--   2. (b) $g$ is proper, lower semicontinuous and convex;
--   3. (c) $h$ is convex;
--   4. (d) $F=f+g-h$ is bounded from below.
--
--   The pair of convexity conditions in (a) says that $f$ is smooth and weakly convex relative to $\varphi$; no global Lipschitz continuity of $\nabla f$ is required. The same $\varphi$, $L$ and $l$ are used by Algorithm 1.
--
--   **Formalization Note** "Nonconvex" in (a) means "not necessarily convex" and is not a hypothesis. Strong convexity is Mathlib's `StrongConvexOn Set.univ ρ φ` for some $\rho>0$, which matches $\rho(\varphi)>0$ in (7). The page prints $g:E\to\mathbb R\cap\{+\infty\}$, read as $\mathbb R\cup\{+\infty\}$; (b) reuses the published `TensorAHPE.IsProperClosedConvex`. (d) is a real lower bound $\alpha$ with $F\ge\alpha$.
-- source:
--   Phan, Le Thi, DCA based algorithm with extrapolation for nonconvex nonsmooth optimization, arXiv:2106.04743v1, Assumption 1, p.1; (7), p.4

import Mathlib
import Definitions.Def_TensorAHPE_IsProperClosedConvex
import Definitions.Def_DCAExtrap_objF

namespace DCAExtrap

/-- **Assumption 1** (Phan–Le Thi, arXiv:2106.04743v1, p.1), for given `f, g, h`, kernel `φ` and
constants `L, l`:
(a) `f : E → ℝ` is continuously differentiable, `φ` is strongly convex and continuously
differentiable, `L > 0`, `l ≥ 0`, and `Lφ − f` and `lφ + f` are convex;
(b) `g : E → ℝ ∪ {+∞}` is proper, lower semicontinuous and convex;
(c) `h : E → ℝ` is convex;
(d) `F = f + g − h` is bounded from below.

**Formalization Note.** The paper's "there exists φ … for some `L > 0` and `l ≥ 0`" makes
`φ, L, l` parameters here; the algorithm uses the same `φ, L, l`. "Strongly convex" is the
paper's `ρ(φ) > 0` with `ρ(φ) = sup{ρ ≥ 0 : φ − (ρ/2)‖·‖² convex}` ((7), p.4), i.e. some `ρ > 0`
with Mathlib's `StrongConvexOn ℝ Set.univ ρ φ` (equivalent in an inner product space to
convexity of `φ − (ρ/2)‖·‖²`). "Nonconvex" in (a) means "not necessarily convex" and is not a
hypothesis. The page's `R ∩ {+∞}` in (b) is read as `R ∪ {+∞}`: `g` is `EReal`-valued and
`TensorAHPE.IsProperClosedConvex g` says `g ≠ −∞` everywhere, `g ≢ +∞`, `g` lower
semicontinuous, and the epigraph of `g` convex. (d) is a real lower bound for `F`. -/
structure Assumption1 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (g : E → EReal) (h : E → ℝ) (φ : E → ℝ) (L l : ℝ) : Prop where
  f_contDiff : ContDiff ℝ 1 f
  φ_contDiff : ContDiff ℝ 1 φ
  φ_strongConvex : ∃ ρ : ℝ, 0 < ρ ∧ StrongConvexOn Set.univ ρ φ
  L_pos : 0 < L
  l_nonneg : 0 ≤ l
  convex_Lφ_sub_f : ConvexOn ℝ Set.univ (fun x => L * φ x - f x)
  convex_lφ_add_f : ConvexOn ℝ Set.univ (fun x => l * φ x + f x)
  g_properClosedConvex : TensorAHPE.IsProperClosedConvex g
  h_convex : ConvexOn ℝ Set.univ h
  F_bddBelow : ∃ α : ℝ, ∀ x, (α : EReal) ≤ objF f g h x

end DCAExtrap


