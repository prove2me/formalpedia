-- Prove2me | Definitions.Def_ConvexRMDP_Supplement_persp
-- name    : ConvexRMDP_Supplement_persp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T01:51:15.648573+00:00
-- url     : https://prove2.me/theorems/13a89400-1083-4545-978b-302bc7c5743b
-- title:
--   Perspective $\xi\varphi(y/\xi)$ with the convention $0\,\varphi(y/0) := \sup_{p\in\mathrm{dom}(\varphi^*)} p^\top y$
-- statement:
--   Let $\varphi : \mathbb R^\iota \to \mathbb R \cup \{+\infty\}$. Its **perspective function** maps $(\xi, y) \in \mathbb R_+ \times \mathbb R^\iota$ to
--
--   $$
--   \xi\,\varphi(y/\xi) = \begin{cases} \xi\,\varphi(y/\xi) & \text{if } \xi > 0, \\[2pt] \sup_{p \in \operatorname{dom}(\varphi^*)} p^\top y & \text{if } \xi = 0 . \end{cases}
--   $$
--
--   The paper writes $\xi \varphi(y/\xi)$ also for $\xi = 0$ with this convention. In the conic programs (5.3), (5.10) and (6.4) the perspective is applied to $\varphi = g^*$, the conjugate of a proper closed convex constraint function $g$; then $\operatorname{dom}(\varphi^*) = \operatorname{dom}(g^{**}) = \operatorname{dom}(g)$, which is the form of the convention stated on p.19. With this convention the perspective of a proper closed convex function is proper closed convex.
--
--   **Formalization Note** The value is in `EReal`. For $\xi < 0$, outside the paper's domain $\mathbb R_+$, the Lean function returns the $\xi = 0$ value; every program that uses it constrains $\xi \ge 0$.
-- source:
--   Grand-Clément & Petrik, arXiv:2209.10187v2, §5.1, p.16 (perspective function and its convention at ξ = 0); p.19 (the convention for ξ g*(y/ξ))

import Mathlib
import Definitions.Def_AubinLipschitz_effDom
import Definitions.Def_ConvexRMDP_Supplement_conj

namespace ConvexRMDP

namespace Supplement

variable {ι : Type*} [Fintype ι]

/-- **The perspective function** of `φ : ℝ^ι → ℝ ∪ {+∞}` (Grand-Clément & Petrik,
arXiv:2209.10187v2, §5.1, p.16): the map `ℝ₊ × ℝ^ι → ℝ ∪ {+∞}` sending `(ξ, y)` to `ξ φ(y/ξ)` if
`ξ > 0` and `(0, y)` to `sup_{p ∈ dom(φ*)} pᵀy`. The paper writes `ξ φ(y/ξ)` also for `ξ = 0`, with the
convention `0 φ(y/0) := sup_{p ∈ dom(φ*)} pᵀy`. In (5.3), (5.10) and (6.4) it is applied to
`φ = g*`, where `dom(g**) = dom(g)` for proper closed convex `g` (p.19).

**Formalization Note.** `EReal`-valued (the supremum over an empty domain would be `⊥`; for
`φ = g*` with `g` proper the domain `dom(g**)` is nonempty). For `ξ < 0`, outside the paper's domain
`ℝ₊`, the value is the `ξ = 0` value; every program constrains `ξ ≥ 0`. -/
noncomputable def persp (φ : (ι → ℝ) → EReal) (ξ : ℝ) (y : ι → ℝ) : EReal :=
  if 0 < ξ then (ξ : EReal) * φ (ξ⁻¹ • y)
  else ⨆ p ∈ AubinLipschitz.effDom (conj φ), ((∑ i, p i * y i : ℝ) : EReal)

end Supplement

end ConvexRMDP


