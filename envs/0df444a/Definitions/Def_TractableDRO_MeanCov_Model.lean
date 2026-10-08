-- Prove2me | Definitions.Def_TractableDRO_MeanCov_Model
-- name    : TractableDRO_MeanCov_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T02:16:38.55962+00:00
-- url     : https://prove2.me/theorems/b51bbdf8-a11a-4c35-a4d7-2735c0b4ee51
-- title:
--   §3, (9) and §5.2 — the family 𝔽₂, E_ℙ((r⁰ + r′ζ̃)⁺), its worst case over a family, and π² (22)
-- statement:
--   This file sets up the objects of §5.2 of Goh and Sim (2010).
--
--   Let $\tilde\zeta$ be a random vector in $\mathbb R^{n}$ (the paper's segregated uncertainty, $n = N_E$) with law $\mathbb P$. For a scalar $r^0 \in \mathbb R$ and a vector $r \in \mathbb R^{n}$ recall from the companion definition `TractableDRO.MeanSupport.Model` (which this file imports and does not redefine)
--
--   1. the **expected positive part**
--   $$E_{\mathbb P}\big((r^0 + r'\tilde\zeta)^+\big) = \int \max\{r^0 + r'\zeta,\, 0\}\, d\mathbb P(\zeta);$$
--   2. for a family $\mathbb F$ of distributions, the **worst-case value** $\sup_{\mathbb P \in \mathbb F} E_{\mathbb P}\big((r^0 + r'\tilde\zeta)^+\big)$, taken in the extended reals $[-\infty, +\infty]$, so that it equals $-\infty$ when $\mathbb F$ is empty and $+\infty$ when the expectations are unbounded;
--
--   This file defines the two objects specific to §5.2:
--
--   3. given a matrix $F \in \mathbb R^{N \times n}$ (from the relation $z = FM(z) + g$ of (9) between the primitive vector $\tilde z \in \mathbb R^{N}$ and $\tilde\zeta$), a matrix $\Sigma \in \mathbb R^{N\times N}$ and a set $\hat{\mathcal V} \subseteq \mathbb R^{n}$, the **family**
--   $$\mathbb F_2 = \Big\{\mathbb P :\ \hat\zeta = E_{\mathbb P}(\tilde\zeta) \in \hat{\mathcal V},\ E_{\mathbb P}\big(F(\tilde\zeta - \hat\zeta)(\tilde\zeta - \hat\zeta)'F'\big) = \Sigma\Big\}$$
--   of probability distributions with finite second moments whose mean lies in $\hat{\mathcal V}$ and for which the primitive vector $F\tilde\zeta + g$ has covariance $\Sigma$;
--   4. the **bound** (22)
--   $$\pi^2(r^0, r) = \inf_{y \in \{y :\, F'y = r\}} \ \sup_{\hat\zeta \in \hat{\mathcal V}} \Big\{ \tfrac12 (r^0 + r'\hat\zeta) + \tfrac12 \sqrt{(r^0 + r'\hat\zeta)^2 + y'\Sigma y} \Big\},$$
--   also in the extended reals, with the convention of p. 909 that an infeasible minimization has value $+\infty$ (and a supremum over the empty set is $-\infty$).
--
--   These are the objects of Theorem 2: the worst-case expected positive part of an affine function of $\tilde\zeta$ over $\mathbb F_2$, and the deterministic optimization problem that evaluates it.
--
--   **Formalization Note** The random vector is the identity on $\mathbb R^{n}$ (`Fin n → ℝ`) and a distribution is a measure `P` on it. The expected positive part and the worst-case value are `TractableDRO.MeanSupport.expPos` and `TractableDRO.MeanSupport.worstCase`; this file defines only `family2` and `pi2`. The mean $E_{\mathbb P}(\tilde\zeta)$ and the covariance matrix are `meanVec` and `covMat` of the published definition `MomentDRO_Conf_Setting`, and `HasSecondMoments P` (a probability measure with every coordinate in $L^2$) makes them genuine moments. The covariance condition is stated as $F\,\mathrm{Cov}_{\mathbb P}(\tilde\zeta)\,F' = \Sigma$, which equals $E_{\mathbb P}(F(\tilde\zeta - \hat\zeta)(\tilde\zeta - \hat\zeta)'F')$ by linearity of the expectation. The positive part is written `max · 0`. Both the worst-case value and $\pi^2$ are `EReal`-valued: `⨅` over an empty index is $+\infty$ and `⨆` over an empty index is $-\infty$. The paper's $\Sigma$ is written `Sig` in Lean. Indices are 0-based (`Fin`).
-- source:
--   Goh & Sim, Distributionally Robust Optimization and Its Tractable Approximations, Oper. Res. 58(4), 2010, pp. 905 (§3 Mean, Covariance), 906 ((9)), 909 (§5 opening), 910 (Theorem 2, (22))

import Mathlib
import Definitions.Def_MomentDRO_Conf_Setting
import Definitions.Def_TractableDRO_MeanSupport_Model

namespace TractableDRO.MeanCov

open MeasureTheory Matrix

/-- The family `𝔽₂` of Theorem 2 (p. 910): probability measures with finite second moments whose
mean `ζ̂ = E_P(ζ̃)` lies in `Vhat` and with `E_P(F(ζ̃ − ζ̂)(ζ̃ − ζ̂)′F′) = F · Cov_P(ζ̃) · F′ = Σ`. -/
def family2 {n N : ℕ} (F : Matrix (Fin N) (Fin n) ℝ) (Sig : Matrix (Fin N) (Fin N) ℝ)
    (Vhat : Set (Fin n → ℝ)) : Set (Measure (Fin n → ℝ)) :=
  {P | MomentDRO.Conf.HasSecondMoments P ∧ MomentDRO.Conf.meanVec P ∈ Vhat ∧
    F * MomentDRO.Conf.covMat P * Fᵀ = Sig}

/-- The bound `π²(r⁰, r)` of (22), p. 910:
`inf_{y : F′y = r} sup_{ζ̂ ∈ V̂} ½(r⁰ + r′ζ̂) + ½√((r⁰ + r′ζ̂)² + y′Σy)`, in `EReal`
(`⊤` when no `y` solves `F′y = r`, `⊥` when `V̂ = ∅` and some `y` does). -/
noncomputable def pi2 {n N : ℕ} (F : Matrix (Fin N) (Fin n) ℝ) (Sig : Matrix (Fin N) (Fin N) ℝ)
    (Vhat : Set (Fin n → ℝ)) (r0 : ℝ) (r : Fin n → ℝ) : EReal :=
  ⨅ y ∈ {y : Fin N → ℝ | Fᵀ *ᵥ y = r}, ⨆ ζh ∈ Vhat,
    ((((r0 + r ⬝ᵥ ζh) / 2 + Real.sqrt ((r0 + r ⬝ᵥ ζh) ^ 2 + y ⬝ᵥ Sig *ᵥ y) / 2 : ℝ)) : EReal)

end TractableDRO.MeanCov


