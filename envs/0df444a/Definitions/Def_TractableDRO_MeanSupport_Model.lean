-- Prove2me | Definitions.Def_TractableDRO_MeanSupport_Model
-- name    : TractableDRO_MeanSupport_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T01:15:53.478688+00:00
-- url     : https://prove2.me/theorems/82a2e949-50af-4e3f-95de-7a9e3a5fafbd
-- title:
--   §3 and §5.1 — the family 𝔽₁, E_ℙ((r⁰ + r′ζ̃)⁺), its worst case over 𝔽₁, and π¹ (21)
-- statement:
--   This file sets up the objects of the mean-and-support bound of Goh and Sim (2010), §5.1.
--
--   Let $\tilde\zeta$ be a random vector in $\mathbb R^{n}$ (the paper's segregated uncertainty, $n = N_E$), and let $\mathcal V, \widehat{\mathcal V} \subseteq \mathbb R^{n}$ be two sets: $\mathcal V$ contains the support of $\tilde\zeta$ and $\widehat{\mathcal V}$ contains its (possibly uncertain) mean. A distribution of $\tilde\zeta$ is a probability measure $\mathbb P$ on $\mathbb R^{n}$.
--
--   1. **The family $\mathbb F_1$.** It consists of all probability measures $\mathbb P$ on $\mathbb R^n$ such that every coordinate of $\tilde\zeta$ is $\mathbb P$-integrable, the mean lies in $\widehat{\mathcal V}$ and $\tilde\zeta$ lies in $\mathcal V$ almost surely:
--   $$\mathbb F_1 = \{\mathbb P : \hat\zeta = \mathbb E_{\mathbb P}(\tilde\zeta) \in \widehat{\mathcal V},\ \mathbb P(\tilde\zeta \in \mathcal V) = 1\}.$$
--   2. **The expected positive part.** For $r^0 \in \mathbb R$ and $r \in \mathbb R^n$, $\mathbb E_{\mathbb P}((r^0 + r'\tilde\zeta)^+)$, where $x^+ = \max\{x, 0\}$.
--   3. **The worst-case value.** For any family $\mathbb F$ of distributions (not only $\mathbb F_1$; the same object serves $\mathbb F_2$, $\mathbb F_3$ and their intersections in Theorems 2–4), $\sup_{\mathbb P \in \mathbb F} \mathbb E_{\mathbb P}((r^0 + r'\tilde\zeta)^+)$, taken in the extended reals $[-\infty, +\infty]$; it is $-\infty$ for an empty family and $+\infty$ when the expectations are unbounded.
--   4. **The bound $\pi^1$ of (21).** For $s \in \mathbb R^n$ write
--   $$\Phi(s) = \sup_{\hat\zeta \in \widehat{\mathcal V}} \{s'\hat\zeta\} + \sup_{\zeta \in \mathcal V} \max\{r^0 + r'\zeta - s'\zeta,\ -s'\zeta\},$$
--   and set
--   $$\pi^1(r^0, r) = \inf_{s \in \mathbb R^{n}} \Phi(s).$$
--
--   These are the objects compared in Theorem 1: the bound $\pi^1$ is a deterministic optimization problem over the support sets, while the worst-case value is an optimization over distributions.
--
--   **Formalization Note** Distributions are measures `P : Measure (Fin n → ℝ)` with `IsProbabilityMeasure P`; the random vector is the identity. The mean is `MomentDRO.Conf.meanVec P` (coordinatewise integrals) from the published definition `MomentDRO_Conf_Setting`, and the family requires each coordinate to be integrable, so the mean is a true expectation. "$\mathbb P(\tilde\zeta\in\mathcal V)=1$" is `∀ᵐ ζ ∂P, ζ ∈ V`, which needs no measurability of $\mathcal V$. The positive part is `max (r0 + r ⬝ᵥ ζ) 0`. The worst-case value, both suprema and the infimum in (21) are taken in `EReal`, following the paper's convention that an infeasible maximization (minimization) has value $-\infty$ ($+\infty$): the supremum over an empty set is `⊥` and an unbounded supremum is `⊤`. The objective $\Phi(s)$ is the separate definition `pi1Obj`, so that the Remark's "attained by choosing $s$" can be stated. Mathlib's `EReal` has $\bot + \top = \bot$; this sum arises in `pi1Obj` only when $\widehat{\mathcal V}$ or $\mathcal V$ is empty.
-- source:
--   Goh & Sim, Distributionally Robust Optimization and Its Tractable Approximations, Oper. Res. 58(4), 2010, pp. 905, 909, §3 (Support, Mean), §5 opening, Theorem 1 and (21)

import Mathlib
import Definitions.Def_MomentDRO_Conf_Setting

open MeasureTheory

namespace TractableDRO.MeanSupport

/-- The family `𝔽₁` of Goh & Sim, Theorem 1 (p. 909): probability laws `P` of the segregated
random vector `ζ̃ ∈ ℝⁿ` whose coordinates are integrable (so the mean is a genuine expectation),
whose mean `E_P ζ̃` lies in `Vhat`, and which put full mass on `V` (`P(ζ̃ ∈ V) = 1`). -/
def family1 {n : ℕ} (V Vhat : Set (Fin n → ℝ)) : Set (Measure (Fin n → ℝ)) :=
  {P | IsProbabilityMeasure P ∧ (∀ i : Fin n, Integrable (fun ζ : Fin n → ℝ => ζ i) P) ∧
    MomentDRO.Conf.meanVec P ∈ Vhat ∧ ∀ᵐ ζ ∂P, ζ ∈ V}

/-- The expected positive part `E_P((r⁰ + r′ζ̃)⁺)`, written with `max · 0`. -/
noncomputable def expPos {n : ℕ} (P : Measure (Fin n → ℝ)) (r0 : ℝ) (r : Fin n → ℝ) : ℝ :=
  ∫ ζ, max (r0 + r ⬝ᵥ ζ) 0 ∂P

/-- The worst-case value `sup_{P ∈ 𝔽} E_P((r⁰ + r′ζ̃)⁺)` in the extended reals
(`⊥` for an empty family, `⊤` when unbounded). -/
noncomputable def worstCase {n : ℕ} (F : Set (Measure (Fin n → ℝ))) (r0 : ℝ)
    (r : Fin n → ℝ) : EReal :=
  ⨆ P ∈ F, ((expPos P r0 r : ℝ) : EReal)

/-- The objective of the infimum in (21) at a given `s`:
`sup_{ζ̂ ∈ Vhat} s′ζ̂ + sup_{ζ ∈ V} max{r⁰ + r′ζ − s′ζ, −s′ζ}`, in the extended reals. -/
noncomputable def pi1Obj {n : ℕ} (V Vhat : Set (Fin n → ℝ)) (r0 : ℝ) (r s : Fin n → ℝ) :
    EReal :=
  (⨆ ζh ∈ Vhat, ((s ⬝ᵥ ζh : ℝ) : EReal)) +
    ⨆ ζ ∈ V, ((max (r0 + r ⬝ᵥ ζ - s ⬝ᵥ ζ) (-(s ⬝ᵥ ζ)) : ℝ) : EReal)

/-- The bound `π¹(r⁰, r)` of (21): the infimum over `s ∈ ℝⁿ` of `pi1Obj`. -/
noncomputable def pi1 {n : ℕ} (V Vhat : Set (Fin n → ℝ)) (r0 : ℝ) (r : Fin n → ℝ) : EReal :=
  ⨅ s : Fin n → ℝ, pi1Obj V Vhat r0 r s

end TractableDRO.MeanSupport


