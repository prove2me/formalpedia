-- Prove2me | Definitions.Def_ShadowBootstrap_residual
-- name    : ShadowBootstrap_residual
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:22:44.688803+00:00
-- url     : https://prove2.me/theorems/c2bdc4bf-a492-41f0-b2b8-112caa3e409c
-- title:
--   The residual estimator $\Delta$ (Definition 4.1, Eq. (10))
-- statement:
--   Let $E$ be a Clifford ensemble, $\sigma$ a reference state, $U_i \sim E$ a sampled basis, and $\hat f(z)$ the empirical frequencies of $S$ independent shots on the unknown state in that basis. The **residual estimator** (Definition 4.1, p.11) is
--   $$\Delta := \sum_z \Big(\hat f(z) - \operatorname{Tr}\big(U\sigma U^\dagger|z\rangle\langle z|\big)\Big)\, \mathcal M^{-1}\big(U^\dagger|z\rangle\langle z|U\big). \tag{10}$$
--
--   The module also fixes the empirical frequencies $\hat f(z) = \frac1S\#\{a : b_a = z\}$ (§3.4), the probability $\prod_a \langle b_a|U_i\rho U_i^\dagger|b_a\rangle$ of $S$ independent shots, and the expectation over a basis $U_i \sim E$ and its $S$ shots on $\rho$, the expectation of Lemma 4.2.
--
--   **Formalization Note** The frequencies are an argument of $\Delta$, so the same object serves raw outcomes and histograms (counts divided by $S$).
-- source:
--   Cho, Kim, Shadow bootstrapping: Nearly minimal-setting pure-state tomography with shallow Clifford measurements, arXiv:2611.06073 (version of November 2, 2026, sha256 34fab758…), Definition 4.1, Eq. (10), p.11; §3.4, p.10; Lemma 4.2, p.12

import Mathlib
import Definitions.Def_ClassicalShadow_Linear_Setting

open ClassicalShadow.Linear

namespace ShadowBootstrap

/-- The empirical frequency `f̂(z) = (1/S) Σ_a 1{b_a = z}` of the outcomes `b_1, …, b_S`
(§3.4, p.10). -/
noncomputable def empFreq {n S : ℕ} (bs : Fin S → Bits n) (z : Bits n) : ℝ :=
  ((Finset.univ.filter fun a => bs a = z).card : ℝ) / S

/-- Cho, Kim, *Shadow bootstrapping: Nearly minimal-setting pure-state tomography with shallow
Clifford measurements*, arXiv:2611.06073 (version of November 2, 2026, sha256 34fab758…),
Definition 4.1, Eq. (10), p.11: the residual estimator of the basis `U_i` with frequencies `f`
and reference state `σ`,
`∆ := Σ_z (f(z) − Tr(U_i σ U_i† |z⟩⟨z|)) M⁻¹(U_i†|z⟩⟨z|U_i)`.

**Formalization Note** `Tr(UσU†|z⟩⟨z|) = ⟨z|UσU†|z⟩` is the published `diagEntry E i σ z`, and
`M⁻¹(U_i†|z⟩⟨z|U_i)` the published `shadow E (i, z)`. The frequencies are an argument so that the
same object serves raw outcomes (`empFreq`) and histograms (`counts / S`). -/
noncomputable def residual {n : ℕ} {ι : Type} [Fintype ι] (E : Primitive n ι) (σ : Op n) (i : ι)
    (f : Bits n → ℝ) : Op n :=
  ∑ z, (((f z : ℝ) : ℂ) - diagEntry E i σ z) • shadow E (i, z)

/-- The probability `∏_a ⟨b_a|U_i ρ U_i†|b_a⟩` of `S` independent shots `b_1, …, b_S` on `ρ` in the
basis `U_i`. -/
noncomputable def shotsWeight {n S : ℕ} {ι : Type} [Fintype ι] (E : Primitive n ι) (ρ : Op n)
    (i : ι) (bs : Fin S → Bits n) : ℝ :=
  ∏ a, (diagEntry E i ρ (bs a)).re

/-- The expectation `E_{U, b_1..b_S}[F(U, b)]` over a basis `U_i ∼ E` and `S` independent shots on
the state `ρ` in that basis (Lemma 4.2, p.12): `Σ_i w_i Σ_{b ∈ ({0,1}ⁿ)^S} ∏_a p_i(b_a) F(i, b)`. -/
noncomputable def resExpect {n : ℕ} {ι : Type} [Fintype ι] (E : Primitive n ι) (ρ : Op n) (S : ℕ)
    (F : ι → (Fin S → Bits n) → Op n) : Op n :=
  ∑ i, ∑ bs : Fin S → Bits n, ((E.w.prob i * shotsWeight E ρ i bs : ℝ) : ℂ) • F i bs

end ShadowBootstrap


