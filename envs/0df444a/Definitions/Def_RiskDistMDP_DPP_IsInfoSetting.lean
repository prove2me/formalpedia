-- Prove2me | Definitions.Def_RiskDistMDP_DPP_IsInfoSetting
-- name    : RiskDistMDP_DPP_IsInfoSetting
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:52:37.923049+00:00
-- url     : https://prove2.me/theorems/53a2f571-2f9b-4a2b-86db-9f67277b96cd
-- title:
--   Filtrations $\mathbb F\subseteq\mathbb G$ and the decision information $\mathcal U_t$
-- statement:
--   On a probability space $(\Omega,\mathcal H,\mathbb P)$, let $\mathbb F=(\mathcal F_t)$ and $\mathbb G=(\mathcal G_t)$ be filtrations of $\mathcal H$ with $\mathcal F_t\subseteq\mathcal G_t$, $\mathcal F_0=\mathcal G_0=\{\emptyset,\Omega\}$, and $\mathcal F_1$ containing all $\mathbb P$-negligible sets. The **decision information** at time $t\in\mathbb N=\{1,2,\dots\}$ is
--   $$\mathcal U_t:=\mathcal G_{t-1}\vee\mathcal F_t,\qquad \mathcal U_0:=\{\emptyset,\Omega\}.$$
--   The state process is adapted to $\mathbb F$, the actions to $\mathbb G$, and $\mathcal U_t$ is what the agent knows when it chooses $A_t$.
--
--   **Formalization Note** The ambient σ-algebra is $\mathcal H$. That $\mathcal F_1\subseteq\mathcal H$ contains every set of outer measure $0$ makes the space complete. The paper also assumes that $(\Omega,\mathcal H,\mathbb P)$ has no atoms; this is not assumed, since no result of the mission uses it.
-- source:
--   Cheng & Jaimungal, Risk-Averse Markov Decision Processes through a Distributional Lens, arXiv:2203.09612v4, §2, p. 4

import Mathlib

set_option autoImplicit false

open MeasureTheory

namespace RiskDistMDP.DPP

/-- The information structure of arXiv:2203.09612v4, §2, p.4: filtrations `𝔽 = (ℱ_t)` and
`𝔾 = (𝒢_t)` of `ℋ` on the probability space `(Ω, ℋ, ℙ)` with `ℱ_t ⊆ 𝒢_t`, `ℱ₁` containing all
`ℙ`-negligible sets, and `ℱ₀ = 𝒢₀ = {∅, Ω}`.

**Formalization Note** `ℋ` is the ambient `MeasurableSpace Ω`. Time is `t : ℕ`; the paper's
`ℕ = {1, 2, …}` and index `0` carries the trivial σ-algebras. A `ℙ`-negligible set is a set of
outer measure `0`; that all of them lie in `ℱ₁ ⊆ ℋ` makes `(Ω, ℋ, ℙ)` complete, so completeness is
not a separate field. The paper's atomlessness of `(Ω, ℋ, ℙ)` is not assumed: no result of the
mission uses it. -/
structure IsInfoSetting {Ω : Type*} [mΩ : MeasurableSpace Ω] (Pr : Measure Ω)
    (ℱ 𝒢 : ℕ → MeasurableSpace Ω) : Prop where
  F_mono : Monotone ℱ
  G_mono : Monotone 𝒢
  F_le : ∀ t, ℱ t ≤ mΩ
  G_le : ∀ t, 𝒢 t ≤ mΩ
  F_le_G : ∀ t, ℱ t ≤ 𝒢 t
  F_zero : ℱ 0 = ⊥
  G_zero : 𝒢 0 = ⊥
  null_mem : ∀ s : Set Ω, Pr s = 0 → MeasurableSet[ℱ 1] s

set_option warn.classDefReducibility false in
/-- The decision information `𝒰_t := 𝒢_{t−1} ∨ ℱ_t` for `t ∈ ℕ = {1,2,…}` and `𝒰₀ := {∅, Ω}`
(arXiv:2203.09612v4, §2, p.4). -/
def decInfo {Ω : Type*} (ℱ 𝒢 : ℕ → MeasurableSpace Ω) (t : ℕ) : MeasurableSpace Ω :=
  if t = 0 then ⊥ else 𝒢 (t - 1) ⊔ ℱ t

end RiskDistMDP.DPP


