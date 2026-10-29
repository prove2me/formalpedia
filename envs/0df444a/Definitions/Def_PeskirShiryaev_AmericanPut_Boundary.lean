-- Prove2me | Definitions.Def_PeskirShiryaev_AmericanPut_Boundary
-- name    : PeskirShiryaev_AmericanPut_Boundary
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:26:29.816933+00:00
-- url     : https://prove2.me/theorems/57d87075-edc6-4b3e-8e2a-ace99e2b6f26
-- title:
--   Stopping-set boundary, finite-horizon hitting time, and candidate class
-- statement:
--   In the geometric Brownian put model, let $V$ denote the stopping value and $G(x)=(K-x)^+$. Define the exercise boundary from the stopping set by
--   $$b(t)=\sup\{x\in[0,K]:V(t,x)=G(x)\}.$$
--   For any real function $c$ and $t\in[0,T]$, the hitting rule is
--   $$\tau_c(t,x)=\inf\{s\in[0,T-t]:X_s^x\le c(t+s)\},$$
--   with the value $T-t$ if the set is empty. A candidate boundary is continuous and nondecreasing on $[0,T]$ and satisfies $0<c(t)<K$ for $0<t<T$.
--
--   These definitions separate the actual exercise boundary from the functions tested in the uniqueness theorem.
--
--   **Formalization Note** The boundary supremum is restricted to $[0,K]$ to retain the exercise threshold at maturity, when all positive stock states have value equal to payoff. The zero stock extension supplies a member of this bounded set. The hitting-time infimum includes maturity as an extra point, implementing the empty-set convention exactly. Candidate functions are represented on $\mathbb R$ but their conditions and equality are restricted to $[0,T]$; their endpoint values are not prescribed.
-- source:
--   Peskir and Shiryaev, Optimal Stopping and Free-Boundary Problems, Birkhäuser Verlag, 2006, DOI 10.1007/978-3-7643-7390-0, pp. 380, 383, 386 (PDF 396, 399, 402), Eqs. (25.2.8)–(25.2.9), (25.2.23)–(25.2.25), Theorem 25.3

import Definitions.Def_PeskirShiryaev_AmericanPut_Model

open MeasureTheory ProbabilityTheory

open scoped NNReal ENNReal

namespace PeskirShiryaev.AmericanPut

noncomputable def Model.boundary {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω)
    (t : ℝ) : ℝ :=
  sSup {x | x ∈ Set.Icc 0 M.K ∧ M.value t x = M.payoff x}

noncomputable def Model.hit {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω)
    (c : ℝ → ℝ) (t x : ℝ) (ω : Ω) : ℝ≥0 :=
  sInf (insert (M.T - t).toNNReal
    {s : ℝ≥0 | s ≤ (M.T - t).toNNReal ∧ M.stock x s ω ≤ c (t + (s : ℝ))})

def Model.Candidate {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω)
    (c : ℝ → ℝ) : Prop :=
  ContinuousOn c (Set.Icc 0 M.T) ∧ MonotoneOn c (Set.Icc 0 M.T) ∧
    ∀ t ∈ Set.Ioo 0 M.T, 0 < c t ∧ c t < M.K

end PeskirShiryaev.AmericanPut


