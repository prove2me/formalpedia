-- Prove2me | Definitions.Def_MartOT_Shadow_Quantile
-- name    : MartOT_Shadow_Quantile
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T00:19:24.234135+00:00
-- url     : https://prove2.me/theorems/6a1a6fb0-ba81-49a5-af50-a3aca9d29c82
-- title:
--   p. 4, p. 13, p. 24 — quantile function G_ν and the quantile slice (G_ν)_#λ_[s,s′]
-- statement:
--   Let $\nu$ be a finite Borel measure on $\mathbb R$ with distribution function $F_\nu(t)=\nu(]-\infty,t])$. Its **quantile function** is
--   $$G_\nu(s)=\inf\{t\in\mathbb R:\ s\le F_\nu(t)\},$$
--   considered for $s\in\,]0,\nu(\mathbb R)[$, where it is nondecreasing and $(G_\nu)_\#\lambda_{[0,\nu(\mathbb R)]}=\nu$ with $\lambda$ the Lebesgue measure. For $0\le s\le s'\le\nu(\mathbb R)$, the **restriction of $\nu$ between the quantiles $s$ and $s'$** is the image measure
--   $$(G_\nu)_\#\lambda_{[s,s']},$$
--   a measure of mass $s'-s$ that is dominated by $\nu$. These slices describe the shadow of an atom (Example 4.7).
--
--   **Formalization Note** Lean's `sInf` returns $0$ on sets that are empty or unbounded below; this happens only for $s\le0$ or for $s$ equal to (or above) $\nu(\mathbb R)$ when that mass is not attained, which is a Lebesgue-null set of parameters in $[s,s']\subseteq[0,\nu(\mathbb R)]$, so the slice is unaffected. The distribution function is read in $\mathbb R$ through `ENNReal.toReal`, which is exact for finite $\nu$.
-- source:
--   arXiv:1208.1509v2, §1.2, p. 4 (quantile function); p. 13; Example 4.7, p. 24; p. 26

import Mathlib

namespace MartOT.Shadow

open MeasureTheory

/-- The **quantile function** of a finite measure `ν` on `ℝ` (p. 4, p. 13):
`G_ν(s) = inf {t ∈ ℝ : s ≤ F_ν(t)}`, where `F_ν(t) = ν(]−∞, t])`; it is used on `]0, ν(ℝ)[`. -/
noncomputable def quantile (ν : Measure ℝ) (s : ℝ) : ℝ :=
  sInf {t : ℝ | s ≤ (ν (Set.Iic t)).toReal}

/-- The restriction of `ν` between the quantiles `s` and `s'` (p. 24, p. 26):
`(G_ν)_# λ_{[s, s']}`, the image of Lebesgue measure on `[s, s']` under `G_ν`. -/
noncomputable def quantileSlice (ν : Measure ℝ) (s s' : ℝ) : Measure ℝ :=
  (volume.restrict (Set.Icc s s')).map (quantile ν)

end MartOT.Shadow


