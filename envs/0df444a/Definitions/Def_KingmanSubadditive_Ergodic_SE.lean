-- Prove2me | Definitions.Def_KingmanSubadditive_Ergodic_SE
-- name    : KingmanSubadditive_Ergodic_SE
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T11:23:47.26998+00:00
-- url     : https://prove2.me/theorems/03369102-a4e1-4e65-aed3-b313709dc4a4
-- title:
--   Condition Sᴱ for a measure-preserving transformation
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space, let $\theta:\Omega\to\Omega$ preserve $P$, and let $f_n:\Omega\to\mathbb R$ for $n\ge1$. Condition **Sᴱ** requires every $f_n$ to be integrable and, for every $m,n\ge1$ and every $\omega$,
--   $$f_{m+n}(\omega)\le f_m(\omega)+f_n(\theta^m\omega).$$
--   It also requires some real $A$ such that $\int f_n\,dP\ge-An$ for all $n\ge1$. This is Kingman's measure-preserving formulation of the subadditive-process assumptions, used in (1.3.4)–(1.3.5).
--
--   **Formalization Note** No inverse for $\theta$ and no ergodicity assumption are included. Values of $f_0$ do not enter Sᴱ.
-- source:
--   Kingman, Subadditive ergodic theory, Ann. Probab. 1(6):883–899 (1973), DOI 10.1214/aop/1176996798, p. 886, §1.3, (1.3.1)–(1.3.3)

import Mathlib

namespace KingmanSubadditive.Ergodic

open MeasureTheory

/-- Condition Sᴱ of §1.3, p. 886: a measure-preserving transformation and
integrable `f_n = x_{0n}` with the pointwise cocycle inequality (1.3.2)
and the linear mean lower bound (1.3.3). No invertibility or ergodicity
of `θ` is assumed. -/
def IsSE {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (θ : Ω → Ω) (f : ℕ → Ω → ℝ) : Prop :=
  MeasurePreserving θ P P ∧
  (∀ n : ℕ, 1 ≤ n → Integrable (f n) P) ∧
  (∀ (m n : ℕ) (ω : Ω), 1 ≤ m → 1 ≤ n →
    f (m + n) ω ≤ f m ω + f n ((θ^[m]) ω)) ∧
  ∃ A : ℝ, ∀ n : ℕ, 1 ≤ n → -A * (n : ℝ) ≤ ∫ ω, f n ω ∂P

end KingmanSubadditive.Ergodic


