-- Prove2me | Definitions.Def_TentNoise_IsFitMap
-- name    : TentNoise_IsFitMap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:40:05.883062+00:00
-- url     : https://prove2.me/theorems/3ba75c35-41a0-49dc-aa7f-5e7d36bf3238
-- title:
--   The fitted map $g$ of Lemma B.3 ($g=h_0^{-1}$ on $[0,\tfrac12]$, $g=h_1^{-1}$ on $[\tfrac12,1]$)
-- statement:
--   Fix an integer $N\ge1$ and $0<b\le1/32$, and set
--
--   $$
--   u(y)=\frac{b}{\pi N}\sin(\pi Ny),\qquad h_0(y)=\frac y2+u(y),\qquad h_1(y)=1-\frac y2+u(y).
--   $$
--
--   The **fitted map of Lemma B.3** is
--
--   $$
--   g(x)=\begin{cases}h_0^{-1}(x),&0\le x\le\tfrac12,\\ h_1^{-1}(x),&\tfrac12\le x\le1,\end{cases}
--   $$
--
--   a perturbation of the tent map whose inverse branches are $h_0,h_1$ instead of $y/2$, $1-y/2$. It has small prediction error (of order $b/N$) but changes the reverse branch probabilities by order $b$, which is what the lower bound exploits.
--
--   **Formalization Note** The module defines $u$ (`pertU`), $h_0$ (`branch0`), $h_1$ (`branch1`) and the predicate `IsFitMap N b g`: $g(h_0(y))=y$ and $g(h_1(y))=y$ for every $y\in[0,1]$. For $N\ge1$ and $0<b\le1/32$, $h_0$ and $h_1$ are bijections of $[0,1]$ onto $[0,\tfrac12]$ and $[\tfrac12,1]$, so the predicate determines $g$ on $[0,1]$ uniquely and is the paper's piecewise definition; values off $[0,1]$ are never used. Lemma B.3 states that such a $g$ exists.
-- source:
--   Huan, Risteski, Wei, Mitigating error propagation in chaotic dynamics via inference-time noising: a view from backward sampling, STOC 2027 submission (manuscript sha256 67925b3e946da20fbfc5ba5a928c6f5743bf4b2ee96e526e8e738f0494f558e6), Lemma B.3, p.26 (PDF p.26)

import Mathlib

namespace TentNoise

/-- The perturbation `u(y) = (b/(πN)) sin(πNy)` of Lemma B.3 (Huan, Risteski, Wei, *Mitigating error propagation in chaotic dynamics via inference-time noising: a view from backward sampling*, STOC 2027 submission (manuscript sha256 67925b3e…), Lemma B.3, p.26). -/
noncomputable def pertU (N : ℕ) (b y : ℝ) : ℝ :=
  b / (Real.pi * N) * Real.sin (Real.pi * N * y)

/-- The perturbed inverse branch `h₀(y) = y/2 + u(y)` (Lemma B.3, p.26). -/
noncomputable def branch0 (N : ℕ) (b y : ℝ) : ℝ := y / 2 + pertU N b y

/-- The perturbed inverse branch `h₁(y) = 1 − y/2 + u(y)` (Lemma B.3, p.26). -/
noncomputable def branch1 (N : ℕ) (b y : ℝ) : ℝ := 1 - y / 2 + pertU N b y

/-- `g` is the fitted map of Lemma B.3 (Huan, Risteski, Wei, *Mitigating error propagation in chaotic dynamics via inference-time noising: a view from backward sampling*, STOC 2027 submission (manuscript sha256 67925b3e…), Lemma B.3, p.26):
`g(x) = h₀⁻¹(x)` for `0 ≤ x ≤ 1/2` and `g(x) = h₁⁻¹(x)` for `1/2 ≤ x ≤ 1`, where
`h₀(y) = y/2 + u(y)`, `h₁(y) = 1 − y/2 + u(y)`, `u(y) = (b/(πN)) sin(πNy)`.

**Formalization Note** The map is characterized by `g(h₀(y)) = y` and `g(h₁(y)) = y` for every
`y ∈ [0, 1]`. For `N ≥ 1` and `0 < b ≤ 1/32` (Lemma B.3's hypotheses), `h₀` and `h₁` are bijections
of `[0,1]` onto `[0, 1/2]` and `[1/2, 1]`, so this determines `g` on `[0, 1]` uniquely and is exactly
the paper's piecewise definition (both inverses give `g(1/2) = 1`). Values of `g` off `[0, 1]` are
unconstrained and never used. Lemma B.3 states that such a `g` exists. -/
def IsFitMap (N : ℕ) (b : ℝ) (g : ℝ → ℝ) : Prop :=
  ∀ y ∈ Set.Icc (0 : ℝ) 1, g (branch0 N b y) = y ∧ g (branch1 N b y) = y

end TentNoise


