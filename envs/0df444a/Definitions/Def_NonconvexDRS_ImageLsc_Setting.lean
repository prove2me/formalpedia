-- Prove2me | Definitions.Def_NonconvexDRS_ImageLsc_Setting
-- name    : NonconvexDRS_ImageLsc_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T17:26:01.347397+00:00
-- url     : https://prove2.me/theorems/46d0c7da-c79d-4013-b1f8-965d6772dceb
-- title:
--   pp. 5, 17, 24 — proper and level-bounded functions, dom, the image function (Ch) of Definition 5.1, and condition (5.5)
-- statement:
--   This file fixes the objects in which Theorem 5.11 of Themelis and Patrinos is stated. Throughout, $E$ and $F$ are real inner product spaces (in the theorems, $E=\mathbb R^n$ and $F=\mathbb R^p$), and $\overline{\mathbb R}=\mathbb R\cup\{+\infty\}$.
--
--   1. **Proper.** A function $h:E\to\overline{\mathbb R}$ is proper if it never takes the value $-\infty$ and its domain is nonempty.
--   2. **Domain.** $\operatorname{dom}h=\{x\in E\mid h(x)<\infty\}$.
--   3. **Level bounded.** $h$ is level bounded if for every $\alpha\in\mathbb R$ the level set $\operatorname{lev}_{\le\alpha}h=\{x\mid h(x)\le\alpha\}$ is bounded.
--   4. **Image function (Definition 5.1).** For a linear map $C:E\to F$ and $h:E\to\overline{\mathbb R}$, the image function $(Ch):F\to[-\infty,+\infty]$ is
--   $$(Ch)(s)=\inf_{x\in E}\{h(x)\mid Cx=s\}.$$
--   The infimum over an empty set is $+\infty$, so $(Ch)(s)=+\infty$ for $s\notin C(\operatorname{dom}h)$; the value $-\infty$ is possible.
--   5. **Condition (5.5) at $\bar z$.** For $g:E\to\overline{\mathbb R}$, a linear map $B:E\to F$ and a point $\bar z\in E$,
--   $$\liminf_{\substack{\|d\|\to\infty\\ Bd\to0}} g(\bar z+d)\;\ge\;\inf_{d\in\ker B} g(\bar z+d).$$
--
--   The image function is the "epi-composition" or "infimal post-composition" of $h$ with $C$; in the paper the function $\varphi_2=(Bg)$ of the ADMM reformulation is an image function, and condition (5.5) is the paper's characterization of when it is lower semicontinuous.
--
--   **Formalization Note** $\overline{\mathbb R}$ is `EReal`; the image function is an `EReal` infimum and may be $-\infty$. The liminf in (5.5) is taken in the complete lattice $[-\infty,+\infty]$ along the filter of all $d$ with $\|d\|\to\infty$ and $Bd\to0$ (the meet of the cobounded filter and the preimage under $B$ of the neighbourhood filter of $0$). When no such $d$ exist (e.g. $B$ injective, or $E=\{0\}$) the filter is trivial, the liminf is $+\infty$, and the condition holds; this is the paper's reading of an empty liminf. Definition 5.1 prints "$Cw=s$"; it is read $Cx=s$.
-- source:
--   Themelis & Patrinos, Douglas-Rachford splitting and ADMM for nonconvex optimization: tight convergence results, arXiv:1709.05747v4, p. 5 §2.1 (dom, proper, lev, level bounded), p. 17 Definition 5.1, p. 24 Theorem 5.11 (5.5)

import Mathlib
import Definitions.Def_NonconvexDRS_ADMM_Setting
import Definitions.Def_NonconvexDRS_Tight_Setting

namespace NonconvexDRS.ImageLsc

open Filter Topology

section General

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The effective domain `dom h = {x | h x < ∞}` (p. 5). -/
def dom (h : E → EReal) : Set E := {x | h x ≠ ⊤}

/-- `h` is level bounded (p. 5): every level set `lev_{≤α} h`, `α ∈ ℝ`, is bounded. -/
def LevelBounded (h : E → EReal) : Prop :=
  ∀ α : ℝ, Bornology.IsBounded {x | h x ≤ (α : EReal)}

/-- Condition (5.5) of Theorem 5.11 (p. 24) at the point `zbar`:
`liminf_{‖d‖→∞, Bd→0} g(zbar + d) ≥ inf_{d ∈ ker B} g(zbar + d)`.
The liminf is taken along the filter of `d` with `‖d‖ → ∞` (`Bornology.cobounded`) and
`B d → 0` (`comap B (𝓝 0)`), in the complete lattice `EReal`; when that filter is trivial
(e.g. `B` injective) the liminf is `+∞` and the condition holds. -/
def Cond55 (g : E → EReal) (B : E →L[ℝ] F) (zbar : E) : Prop :=
  (⨅ (d : E) (_ : B d = 0), g (zbar + d)) ≤
    Filter.liminf (fun d => g (zbar + d)) (Bornology.cobounded E ⊓ Filter.comap B (𝓝 0))

end General

end NonconvexDRS.ImageLsc


