-- Prove2me | Definitions.Def_DrezetGHZ_Models
-- name    : DrezetGHZ_Models
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-28T19:18:05.878052+00:00
-- url     : https://prove2.me/theorems/b686499b-bdff-465b-bb89-cd0c19db87d2
-- title:
--   Locally causal beable models, and the setting-dependent model of Appendix 3
-- statement:
--   Beable models of the three-party GHZ experiment.
--
--   1. A **locally causal (Bell-local) model** on a measurable space $\Lambda$ of beables consists of:
--      - a probability measure $\rho$ on $\Lambda$ that does not depend on the settings (Eq. (18));
--      - measurable local response probabilities $P_j(\alpha\mid\lambda,\hat n)\ge0$ for $j\in\{1,2,3\}$ (Alice, Bob, Charlie), with $\sum_{\alpha=\pm1}P_j(\alpha\mid\lambda,\hat n)=1$. Each depends only on the beable $\lambda$ and that party's own setting (Eq. (17)).
--
--      Its **predicted joint probability** (Eq. (14) with (17)–(18)) is
--   $$P(\alpha,\beta,\gamma\mid\hat n_1,\hat n_2,\hat n_3)=\int_\Lambda P_1(\alpha\mid\lambda,\hat n_1)P_2(\beta\mid\lambda,\hat n_2)P_3(\gamma\mid\lambda,\hat n_3)\,d\rho(\lambda).$$
--   2. The **GHZ sign** $s(\hat n_1,\hat n_2,\hat n_3)$ is $-1$ for $(\hat x,\hat x,\hat x)$ and $+1$ for $(\hat x,\hat y,\hat y)$, $(\hat y,\hat x,\hat y)$ and $(\hat y,\hat y,\hat x)$ (see Eqs. (2)–(5)).
--   3. **Appendix 3 model.** The local responses (Eq. (43)) are
--   $$P_j(\alpha\mid\theta_j,\hat x)=\frac{1+\alpha\cos\theta_j}{2},\qquad P_j(\alpha\mid\theta_j,\hat y)=\frac{1+\alpha\sin\theta_j}{2}.$$
--   The setting-dependent density on angle triples (Eqs. (44)–(45)) is
--   $$\rho(\theta_1,\theta_2,\theta_3\mid\hat n_1,\hat n_2,\hat n_3)=\tfrac14\sum_{v_1v_2v_3=s}\delta_{(\vartheta(\hat n_1,v_1),\,\vartheta(\hat n_2,v_2),\,\vartheta(\hat n_3,v_3))},$$
--   where $\vartheta(\hat x,+1)=0$, $\vartheta(\hat x,-1)=\pi$, $\vartheta(\hat y,+1)=\pi/2$ and $\vartheta(\hat y,-1)=-\pi/2$ are the polar angles of $\pm\hat x$ and $\pm\hat y$.
--
--   The locally causal model is the object that the GHZ theorem rules out. The Appendix 3 model shows that dropping Eq. (18) removes the obstruction.
--
--   **Formalization Note** The fixed state $\psi$ is implicit. Parties are indexed $0,1,2$ in Lean. The GHZ sign is also $+1$ on the four setting triples that are not GHZ settings; the paper does not use those.
-- source:
--   A. Drezet, "An Elementary Proof That Everett's Quantum Multiverse Is Nonlocal: Bell-Locality and Branch-Symmetry in the Many-Worlds Interpretation", arXiv:2306.07794v1 [quant-ph] (2023), https://arxiv.org/abs/2306.07794, p. 5 Eqs. (14), (17), (18); p. 13 Eq. (33); pp. 21–22 Appendix 3, Eqs. (39)–(45).

import Mathlib
import Definitions.Def_DrezetGHZ_Quantum

/-!
# Beable models of the GHZ experiment (Drezet 2023, Eqs. (14), (17), (18), (33), (39)–(44))
-/

namespace DrezetGHZ

open MeasureTheory

/-- A **Bell-local (locally causal) beable model** of the three-party experiment
(Eqs. (14), (17), (18)).

* `ρ` is the probability distribution of the beables `λ ∈ Λ`; it does **not** depend on
  the settings (statistical independence / no superdeterminism, Eq. (18)).
* `P j λ n α` is the local probability `P_j(α | λ, n̂_j, ψ)` that party `j`
  (`0` = Alice, `1` = Bob, `2` = Charlie) records outcome `α ∈ {±1}` given the beable `λ`
  and **its own** setting `n` only (local factorizability, Eq. (17)).
  The fixed quantum state `ψ` is left implicit. -/
structure LocalCausalModel (Λ : Type*) [MeasurableSpace Λ] where
  /-- Setting-independent distribution `ρ(λ | ψ)` of the beables. -/
  ρ : Measure Λ
  isProbabilityMeasure : IsProbabilityMeasure ρ
  /-- Local response probabilities `P_j(α | λ, n̂_j, ψ)`. -/
  P : Fin 3 → Λ → Setting → ℤˣ → ℝ
  P_nonneg : ∀ j lam n α, 0 ≤ P j lam n α
  P_sum_one : ∀ j lam n, ∑ α, P j lam n α = 1
  P_measurable : ∀ j n α, Measurable fun lam => P j lam n α

/-- Joint outcome probability predicted by a locally causal model (Eq. (14) with (17), (18)):
`P(α, β, γ | n̂₁, n̂₂, n̂₃) = ∫ P₁(α|λ,n̂₁) P₂(β|λ,n̂₂) P₃(γ|λ,n̂₃) dρ(λ)`. -/
noncomputable def LocalCausalModel.predict {Λ : Type*} [MeasurableSpace Λ]
    (M : LocalCausalModel Λ) (n₁ n₂ n₃ : Setting) (α β γ : ℤˣ) : ℝ :=
  ∫ lam, M.P 0 lam n₁ α * M.P 1 lam n₂ β * M.P 2 lam n₃ γ ∂M.ρ

/-- The sign `s` of the GHZ constraint `αβγ = s` for the four GHZ settings
(Eqs. (2)–(5)): `-1` for `(x̂, x̂, x̂)`; `+1` for `(x̂, ŷ, ŷ)`, `(ŷ, x̂, ŷ)`, `(ŷ, ŷ, x̂)`.
(It is also `+1` on the other four setting triples, which play no role.) -/
def ghzSign : Setting → Setting → Setting → ℤˣ
  | .x, .x, .x => -1
  | _, _, _ => 1

/-- Local response probabilities of Appendix 3, Eq. (43):
`P_j(α | θ_j, x̂) = (1 + α cos θ_j)/2` and `P_j(α | θ_j, ŷ) = (1 + α sin θ_j)/2`,
where `θ_j` is the polar angle (in the `xy`-plane) of the unit vector `θ̂_j`. -/
noncomputable def appendixResponse (θ : ℝ) : Setting → ℤˣ → ℝ
  | .x, α => (1 + ((α : ℤ) : ℝ) * Real.cos θ) / 2
  | .y, α => (1 + ((α : ℤ) : ℝ) * Real.sin θ) / 2

/-- Polar angle of the unit vector `v n̂` (`v = ±1`, `n̂ ∈ {x̂, ŷ}`) in the `xy`-plane:
`x̂ ↦ 0`, `-x̂ ↦ π`, `ŷ ↦ π/2`, `-ŷ ↦ -π/2`. -/
noncomputable def settingAngle : Setting → ℤˣ → ℝ
  | .x, v => if v = 1 then 0 else Real.pi
  | .y, v => if v = 1 then Real.pi / 2 else -(Real.pi / 2)

/-- The setting-dependent ("superdeterministic") beable density of Appendix 3, Eq. (44):
`ρ(θ₁, θ₂, θ₃ | n̂₁, n̂₂, n̂₃, ψ) = ¼ ∑_{v₁v₂v₃ = s} δ(θ̂₁ − v₁n̂₁) δ(θ̂₂ − v₂n̂₂) δ(θ̂₃ − v₃n̂₃)`,
with `s = ghzSign n₁ n₂ n₃`, realised as a measure on angle triples `(θ₁, θ₂, θ₃) ∈ ℝ³`. -/
noncomputable def appendixDensity (n₁ n₂ n₃ : Setting) : Measure (ℝ × ℝ × ℝ) :=
  (1 / 4 : ENNReal) •
    ∑ v ∈ Finset.univ.filter (fun v : ℤˣ × ℤˣ × ℤˣ => v.1 * v.2.1 * v.2.2 = ghzSign n₁ n₂ n₃),
      Measure.dirac (settingAngle n₁ v.1, settingAngle n₂ v.2.1, settingAngle n₃ v.2.2)

end DrezetGHZ


