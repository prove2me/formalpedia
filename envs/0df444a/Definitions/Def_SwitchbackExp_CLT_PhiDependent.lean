-- Prove2me | Definitions.Def_SwitchbackExp_CLT_PhiDependent
-- name    : SwitchbackExp_CLT_PhiDependent
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T04:30:03.866404+00:00
-- url     : https://prove2.me/theorems/5229c906-2c64-4fd4-8f2f-44ec3c8219d7
-- title:
--   Definition EC.1, p. ec1 — ϕ-dependent random variables (Hoeffding and Robbins 1948)
-- statement:
--   Let $X_1,\dots,X_d$ be real random variables on a probability space $(\Omega,\mathcal F,\mu)$ and let $\phi\ge 0$ be an integer. The sequence is **$\phi$-dependent** if for all indices $r<s\le d$ with $s-r>\phi$ the two random vectors
--   $$(X_1,X_2,\dots,X_r)\quad\text{and}\quad(X_s,X_{s+1},\dots,X_d)$$
--   are independent under $\mu$.
--
--   In words, blocks of the sequence that are separated by more than $\phi$ indices are independent. A $0$-dependent sequence is an independent one; the block errors of a switchback experiment under the optimal design are $1$-dependent. This is the dependence notion of the central limit theorem of Romano and Wolf (Lemma EC.1).
--
--   **Formalization Note** The sequence is a function `X : ℕ → Ω → ℝ` read at the indices $1,\dots,d$; the condition $s-r>\phi$ is written $r+\phi<s$ to avoid natural-number subtraction. The vectors are `Fin r → ℝ` and `Fin (d+1-s) → ℝ` with the product σ-algebra; for $r=0$ the first vector is empty and the condition is trivial.
-- source:
--   arXiv:2009.00148v4, Definition EC.1, p. ec1 (Hoeffding and Robbins 1948)

import Mathlib

namespace SwitchbackExp.CLT

open MeasureTheory ProbabilityTheory

/-- Definition EC.1 (ϕ-dependent random variables, Hoeffding and Robbins (1948), p. ec1), for a finite
sequence `X₁, …, X_d` read at the indices `1, …, d` of `X : ℕ → Ω → ℝ`: whenever `s − r > ϕ` (written
`r + ϕ < s`) and `s ≤ d`, the vectors `(X₁, …, X_r)` and `(X_s, …, X_d)` are independent under `μ`. -/
def IsPhiDependent {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (ϕ d : ℕ) (X : ℕ → Ω → ℝ) : Prop :=
  ∀ r s : ℕ, r + ϕ < s → s ≤ d →
    IndepFun (fun ω (i : Fin r) => X ((i : ℕ) + 1) ω)
      (fun ω (i : Fin (d + 1 - s)) => X (s + (i : ℕ)) ω) μ

end SwitchbackExp.CLT


