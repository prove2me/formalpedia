-- Prove2me | Definitions.Def_ModelRiskOT_Duality_phiLam
-- name    : ModelRiskOT_Duality_phiLam
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T16:54:09.992999+00:00
-- url     : https://prove2.me/theorems/e81c05a0-18f5-4cf7-b288-d38c58230342
-- title:
--   $\varphi_\lambda(x)=\sup_{y\in S}\{f(y)-\lambda c(x,y)\}$ and its restriction to $y\in K$
-- statement:
--   For a cost $c$, a function $f:S\to\mathbb R$, a real $\lambda$ and a set $K\subseteq S$, define
--
--   $$\varphi^K_\lambda(x)=\sup_{y\in K}\{f(y)-\lambda c(x,y)\},\qquad \varphi_\lambda=\varphi^S_\lambda,$$
--
--   with values in $\mathbb R\cup\{\infty\}$ when $K\ne\emptyset$ (and $-\infty$ for $K=\emptyset$). $\varphi_\lambda$ is the function of Theorem 1(b), the smallest $\varphi$ with $\varphi(x)+\lambda c(x,y)\ge f(y)$ for all $x,y$; the restrictions to $K=S_\pi$ and $K=S_n$ appear in Lemma 8 and Lemma 16.
--
--   **Formalization Note** The supremum is taken in `EReal`, so $\varphi_\lambda$ may equal $+\infty$ (Remark 5 of the paper).
-- source:
--   Blanchet & Murthy, Quantifying Distributional Model Risk via Optimal Transport, arXiv:1604.01446v2, p. 7, Theorem 1(b); p. 23, Lemma 8; p. 42, Lemma 16

import Mathlib

namespace ModelRiskOT.Duality

/-- The restricted envelope `x ↦ sup_{y ∈ K} {f(y) − λ c(x, y)}`, valued in `EReal` (it may be
`+∞`; it is `⊥` only if `K = ∅`). Blanchet & Murthy, arXiv:1604.01446v2, uses it with
`K = S_π` (Lemma 8, p. 23) and `K = S_n` (Lemma 16, p. 42). -/
noncomputable def phiLamOn {S : Type*} (c : S → S → ℝ) (f : S → ℝ) (lam : ℝ) (K : Set S)
    (x : S) : EReal :=
  ⨆ y ∈ K, ((f y - lam * c x y : ℝ) : EReal)

/-- **φ_λ** of Theorem 1(b) (arXiv:1604.01446v2, p. 7): `φ_λ(x) = sup_{y ∈ S} {f(y) − λ c(x, y)}`,
a function `S → ℝ ∪ {∞}` (valued in `EReal`, never through `ℝ`). -/
noncomputable def phiLam {S : Type*} (c : S → S → ℝ) (f : S → ℝ) (lam : ℝ) : S → EReal :=
  phiLamOn c f lam Set.univ

end ModelRiskOT.Duality


