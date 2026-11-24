-- Prove2me | Definitions.Def_OfflinePolicyLearning_Trees_Supplement_Setting
-- name    : OfflinePolicyLearning_Trees_Supplement_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T08:12:07.02269+00:00
-- url     : https://prove2.me/theorems/d71728bb-672b-4091-99d5-7c37dcf2b7c3
-- title:
--   Definition 5, p. 15 and §6, p. 27 — the policy-difference class Πᴰ, its Rademacher complexity ℛₙ(Πᴰ), the score moment V*, and tree policies on a feature domain
-- statement:
--   Let $\mathcal X$ be a measurable feature space and let the $d$ actions be identified with the standard basis vectors $e_1,\dots,e_d$ of $\mathbb R^d$. A policy is a map $\pi:\mathcal X\to\{1,\dots,d\}$, and $\Pi$ is a class of policies. For a score vector $\gamma\in\mathbb R^d$ the inner product with an action is a coordinate, $\langle\gamma,\pi(x)\rangle=\gamma_{\pi(x)}$.
--
--   1. The **policy-difference class** is the set of functions on feature–score pairs
--   $$\Pi^D=\big\{(x,\gamma)\mapsto\langle\gamma,\pi_a(x)-\pi_b(x)\rangle:\ \pi_a,\pi_b\in\Pi\big\}.$$
--   2. Let $(X_1,\Gamma_1),\dots,(X_n,\Gamma_n)$ be iid with law $P$ on $\mathcal X\times\mathbb R^d$, and let $Z_1,\dots,Z_n$ be iid uniform signs independent of the sample. The **empirical Rademacher complexity** of $\Pi^D$ is
--   $$\mathcal R_n(\Pi^D;\{X_i,\Gamma_i\}_{i=1}^n)=\mathbf E\Big[\sup_{\pi_a,\pi_b\in\Pi}\frac1n\Big|\sum_{i=1}^n Z_i\langle\pi_a(X_i)-\pi_b(X_i),\Gamma_i\rangle\Big|\ \Big|\ \{X_i,\Gamma_i\}_{i=1}^n\Big],$$
--   the expectation taken over the signs, and the **Rademacher complexity** is its expectation over the sample, $\mathcal R_n(\Pi^D)=\mathbf E[\mathcal R_n(\Pi^D;\{X_i,\Gamma_i\}_{i=1}^n)]$.
--   3. The **worst-case second moment** of policy differences is
--   $$V^*=\sup_{\pi_a,\pi_b\in\Pi}\mathbf E\big[\langle\Gamma,\pi_a(X)-\pi_b(X)\rangle^2\big],\qquad (X,\Gamma)\sim P.$$
--   4. For a set $S\subseteq\mathbb R^p$ of features, the **depth-$L$ tree policies on $S$** are the maps $S\to\{1,\dots,d\}$ that agree on $S$ with the evaluation of some depth-$L$ decision tree.
--
--   These objects state Theorem 1 for general bounded score vectors and Theorem 4 for decision trees on a bounded feature domain.
--
--   **Formalization Note** The Rademacher complexity is the published generic `DRBatchBandit.rademacher` applied to $\Pi^D$; it takes the supremum of the absolute value of the signed average, as Definition 5 does, and its integrand is the empirical complexity `empiricalPolicyDiffRademacher`. The sign expectation is the average over the $2^n$ sign vectors and the sample expectation is a Bochner integral, so a non-measurable integrand would give $0$; the theorems using it restrict to finite classes of measurable policies, where the integrand is measurable and bounded. $V^*$ is a real supremum, honest for a nonempty class with bounded scores. Trees are the published `DTree` of the base mission, restricted to $S$.
-- source:
--   Zhou, Athey & Wager, Offline Multi-Action Policy Learning, arXiv:1810.04778v2, p. 14 (§4.1, the class Πᴰ), p. 15, Definition 5; p. 16, Theorem 1 (6); p. 18, Remark 6 (V*); p. 27, §6 (bounded feature domain X ⊂ ℝ^p) and §6.1

import Mathlib
import Definitions.Def_DRBatchBandit_Rademacher
import Definitions.Def_OfflinePolicyLearning_Trees_Setting

open MeasureTheory

namespace OfflinePolicyLearning.Trees.Supplement

/-- §4.1, p. 14 and Definition 5, p. 15: the policy-difference class
`Πᴰ = {(x, γ) ↦ ⟨γ, πa(x) − πb(x)⟩ : πa, πb ∈ Π}` on feature–score pairs `(x, γ) ∈ X × ℝ^d`.
Actions are `Fin d`, identified with the standard basis vectors of `ℝ^d`, so
`⟨γ, πa(x) − πb(x)⟩ = γ (πa x) − γ (πb x)`. Both orders `(πa, πb)` and `(πb, πa)` are included. -/
def policyDiffClass {X : Type*} {d : ℕ} (Pol : Set (X → Fin d)) : Set (X × (Fin d → ℝ) → ℝ) :=
  {f | ∃ πa ∈ Pol, ∃ πb ∈ Pol, f = fun z => z.2 (πa z.1) - z.2 (πb z.1)}

/-- Definition 5, item 1, p. 15: the empirical Rademacher complexity
`ℛₙ(Πᴰ; {Xᵢ, Γᵢ}) = E[sup_{πa, πb ∈ Π} |(1/n) ∑ᵢ Zᵢ ⟨πa(Xᵢ) − πb(Xᵢ), Γᵢ⟩| | {Xᵢ, Γᵢ}]` of the
sample `z = ((X₁, Γ₁), …, (Xₙ, Γₙ))`, the expectation over iid uniform signs `Z₁, …, Zₙ` written as
the average over the `2ⁿ` sign vectors (`true ↦ +1`, `false ↦ −1`). This is exactly the integrand
of `DRBatchBandit.rademacher` applied to `Πᴰ`. -/
noncomputable def empiricalPolicyDiffRademacher {X : Type*} {d n : ℕ} (Pol : Set (X → Fin d))
    (z : Fin n → X × (Fin d → ℝ)) : ℝ :=
  (1 / 2 ^ n : ℝ) * ∑ σ : Fin n → Bool,
    ⨆ f : policyDiffClass Pol, |(1 / n : ℝ) * ∑ i, (if σ i then (1 : ℝ) else -1) * f.1 (z i)|

/-- Definition 5, item 2, p. 15: the Rademacher complexity `ℛₙ(Πᴰ) = E[ℛₙ(Πᴰ; {Xᵢ, Γᵢ})]` for
`n` iid feature–score pairs `(Xᵢ, Γᵢ)` with joint law `P`: the expectation over the sample of
the empirical Rademacher complexity (the published generic `DRBatchBandit.rademacher`, applied to
`Πᴰ`; its integrand is `empiricalPolicyDiffRademacher Pol`). -/
noncomputable def policyDiffRademacher {X : Type*} [MeasurableSpace X] {d : ℕ}
    (P : Measure (X × (Fin d → ℝ))) (n : ℕ) (Pol : Set (X → Fin d)) : ℝ :=
  DRBatchBandit.rademacher P n (policyDiffClass Pol)

/-- Theorem 1 (6), p. 16, and Remark 6, p. 18, for a general score law: the worst-case second
moment `sup_{πa, πb ∈ Π} E[⟨Γ, πa(X) − πb(X)⟩²]` of a feature–score pair `(X, Γ) ∼ P`. -/
noncomputable def scoreVstar {X : Type*} [MeasurableSpace X] {d : ℕ}
    (P : Measure (X × (Fin d → ℝ))) (Pol : Set (X → Fin d)) : ℝ :=
  ⨆ πa : Pol, ⨆ πb : Pol, ∫ z, (z.2 (πa.1 z.1) - z.2 (πb.1 z.1)) ^ 2 ∂P

/-- §6, p. 27: the depth-`L` tree policies restricted to a feature domain `S ⊆ ℝ^p`
(in §6 a bounded set): the maps `S → Fin d` that agree on `S` with the evaluation of some
depth-`L` tree of the published `DTree`. -/
def treePoliciesOn (p d L : ℕ) (S : Set (Fin p → ℝ)) : Set (S → Fin d) :=
  {π | ∃ T : DTree p d L, ∀ x : S, π x = T.eval x.1}

end OfflinePolicyLearning.Trees.Supplement


