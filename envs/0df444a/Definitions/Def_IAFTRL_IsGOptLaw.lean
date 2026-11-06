-- Prove2me | Definitions.Def_IAFTRL_IsGOptLaw
-- name    : IAFTRL_IsGOptLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:44:58.192476+00:00
-- url     : https://prove2.me/theorems/5d69033f-6cdc-40d6-941b-7b6f20ae8d9e
-- title:
--   G-optimal law on a finite action set
-- statement:
--   A vector $\pi\in\mathbb R^{\mathcal A}$ is a **G-optimal law** in the sense used by Lemma D.10 if
--   1. $\pi$ is a probability distribution on $\mathcal A$;
--   2. $\Sigma(\pi)=\sum_a\pi_a\,aa^\top$ is positive definite;
--   3. $a^\top\Sigma(\pi)^{-1}a\le d$ for every action $a$.
--
--   These are the two properties of Lemma J.3 (G-optimal design on a compact spanning set), the only ones the feasibility argument of Lemma D.10 uses. By the Kiefer–Wolfowitz theorem such a law exists for every spanning finite action set.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits, arXiv:2611.01299, Lemma J.3, p.206; Lemma D.10, p.79

import Mathlib
import Definitions.Def_LinearBanditProtocol

namespace IAFTRL

open Matrix

/-- **G-optimal law on a finite action set.** Zhao–Tan, *Best-of-Both-Worlds FTRL for Linear Bandits*, arXiv:2611.01299, Lemma J.3, p.206: "There is a
finite-support probability measure `π` such that `Σ(π) = ∫ aa^⊤ π(da) ≻ 0` and
`sup_{a∈𝒜} a^⊤Σ(π)^{-1}a ≤ d`"; Lemma D.10, p.79: "let `π` be a G-optimal law".

`IsGOptLaw arms π` says that `π` is a probability vector on the actions, that
`Σ(π) = Σ_a π_a a a^⊤` is positive definite, and that `a^⊤Σ(π)^{-1}a ≤ d` for every action `a`.

**Formalization Note.** These are the two properties of Lemma J.3, the only ones Lemma D.10 uses.
`Σ(π)` is the published `BanditAlgorithm.linearAllocationMatrix arms π`. -/
def IsGOptLaw {d K : ℕ} (arms : Fin K → Fin d → ℝ) (π : Fin K → ℝ) : Prop :=
  (∀ b, 0 ≤ π b) ∧ ∑ b, π b = 1 ∧ (BanditAlgorithm.linearAllocationMatrix arms π).PosDef ∧
    ∀ a, arms a ⬝ᵥ (BanditAlgorithm.linearAllocationMatrix arms π)⁻¹ *ᵥ arms a ≤ d

end IAFTRL


