-- Prove2me | Definitions.Def_NonlocalFK_IsSmallSet
-- name    : NonlocalFK_IsSmallSet
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:41:44.619988+00:00
-- url     : https://prove2.me/theorems/4cd9db96-e681-42ef-994f-fac49d4137cc
-- title:
--   The discontinuity set of Assumption 2.1
-- statement:
--   A set $D$ is **small** if $D\subset\partial_pQ$ is closed and there exist a finite set $\mathcal T=\{t_1,\dots,t_N\}\subset[0,T]$ and $\lambda\in(0,d)$ such that for any $\varepsilon>0$ there are $s_1,\dots,s_M\in\mathcal T$ and finitely many $d$-dimensional balls $B_1,\dots,B_M$ with
--
--   $$
--   D\subset\bigcup_{i=1}^M(\{s_i\}\times B_i)\cap\partial_pQ,\qquad \sum_{i=1}^M(\operatorname{diam}B_i)^\lambda<\varepsilon.
--   $$
--
--   Such a set can contain the lateral boundary at finitely many times, and meets the terminal slice in a Lebesgue-null set. It is the exceptional set off which boundary data must be continuous, in Assumption 2.1 and in Proposition A.1.
--
--   **Formalization Note** $\mathcal T$ and $\lambda$ are chosen before $\varepsilon$. The balls are open; since $\varepsilon$ is arbitrary, the closed reading is equivalent.
-- source:
--   Dai, Kou, Yang, A Stochastic Representation for Nonlocal Parabolic PDEs with Applications, SSRN 3541591, Assumption 2.1, p.7

import Definitions.Def_NonlocalFK_Diffusion

open Set

noncomputable section

namespace NonlocalFK

variable {d : ℕ}

/-- The set of Assumption 2.1 (Dai, Kou, Yang, SSRN 3541591, p.7): `D ⊂ ∂ₚQ` is closed, and there
exist a finite `𝒯 ⊂ [0, T]` and `λ ∈ (0, d)` such that for every `ε > 0` there are
`s₁, …, s_M ∈ 𝒯` and finitely many balls `B₁, …, B_M` with
`D ⊂ ⋃ᵢ ({sᵢ} × Bᵢ) ∩ ∂ₚQ` and `∑ᵢ (diam Bᵢ)^λ < ε`.

**Formalization Note.** `𝒯` and `λ` are chosen before `ε`, as on the page. The page does not say
whether the balls are open or closed; they are open here. Since `ε` is arbitrary, the two readings
agree (enlarge each ball slightly). `Metric.diam` is applied to balls, which are bounded. -/
def IsSmallSet (c : Diffusion d) (D : Set (ℝ × E d)) : Prop :=
  IsClosed D ∧ D ⊆ c.bdry ∧
  ∃ (𝒯 : Finset ℝ) (lam : ℝ), (𝒯 : Set ℝ) ⊆ Icc 0 c.T ∧ 0 < lam ∧ lam < d ∧
    ∀ ε : ℝ, 0 < ε → ∃ (M : ℕ) (s : Fin M → ℝ) (y : Fin M → E d) (ρ : Fin M → ℝ),
      (∀ i, s i ∈ 𝒯) ∧
      D ⊆ (⋃ i, {s i} ×ˢ Metric.ball (y i) (ρ i)) ∩ c.bdry ∧
      ∑ i, Metric.diam (Metric.ball (y i) (ρ i)) ^ lam < ε

end NonlocalFK


