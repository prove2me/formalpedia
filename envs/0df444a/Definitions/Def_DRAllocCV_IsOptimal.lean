-- Prove2me | Definitions.Def_DRAllocCV_IsOptimal
-- name    : DRAllocCV_IsOptimal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:14:04.421265+00:00
-- url     : https://prove2.me/theorems/f8b852e8-fe2b-45ef-8ae8-d787131ce134
-- title:
--   Optimality in (MDP)
-- statement:
--   Given an ambiguity set $\mathcal P$, problem (MDP) is
--
--   $$
--   z^\star=\sup_{(p,q)\in\mathcal X}\ \inf_{\mathbb P\in\mathcal P}\ \mathbb E_{\mathbb P}\Bigl[\sum_{i\in\mathcal I}\bigl(p_i(\tilde t)\tilde t_i-q_i(\tilde t)c_i\bigr)\Bigr].
--   $$
--
--   A mechanism $(p,q)$ is **optimal in (MDP)** if it is feasible and its worst-case expected payoff $\inf_{\mathbb P\in\mathcal P}\mathbb E_{\mathbb P}[\cdot]$ is at least that of every feasible mechanism, i.e. it attains $z^\star$.
--
--   **Formalization Note** The infimum is not formed as a real number. Instead: for every feasible $(p',q')$, every real lower bound of the expected payoffs of $(p',q')$ over $\mathcal P$ is also a lower bound of those of $(p,q)$. This is the comparison of the two infima in the extended reals, and it avoids the junk value of a real infimum of an empty or unbounded set.
-- source:
--   Bayrak, Koçyiğit, Kuhn, Pınar, Distributionally Robust Optimal Allocation with Costly Verification, arXiv:2211.15122v3, §2, p.7, (MDP) and "solvable"

import Mathlib
import Definitions.Def_DRAllocCV_Feasible
import Definitions.Def_DRAllocCV_expectedPayoff

open MeasureTheory

namespace DRAllocCV

/-- **Optimality in (MDP)** (Bayrak, Koçyiğit, Kuhn, Pınar, *Distributionally Robust Optimal Allocation with Costly Verification*, arXiv:2211.15122v3, §2, p.7): `(p, q) ∈ 𝒳` attains
`z⋆ = sup_{(p′,q′) ∈ 𝒳} inf_{ℙ ∈ 𝒫} 𝔼_ℙ[∑ᵢ (p′ᵢ(t̃) t̃ᵢ − q′ᵢ(t̃) cᵢ)]`, i.e. its worst-case
expected payoff over the ambiguity set `𝒫` is at least that of every feasible mechanism.

**Formalization Note.** Stated without a real-valued `⨅`/`⨆` (which would return junk on empty or
unbounded sets): `(p, q)` is feasible, and for every feasible `(p′, q′)` every lower bound `z` of
`{𝔼_ℙ[payoff of (p′, q′)] : ℙ ∈ 𝒫}` is also a lower bound of `{𝔼_ℙ[payoff of (p, q)] : ℙ ∈ 𝒫}`.
This is `inf_ℙ 𝔼_ℙ[(p′,q′)] ≤ inf_ℙ 𝔼_ℙ[(p,q)]` with infima in the extended reals, for every
competitor, which is the definition of attaining `z⋆`. -/
def IsOptimal {ι : Type*} [Fintype ι] [DecidableEq ι] (tlo thi : ι → ℝ)
    (Pset : Set (Measure (ι → ℝ))) (c : ι → ℝ) (p q : ι → (ι → ℝ) → ℝ) : Prop :=
  Feasible tlo thi p q ∧
  ∀ p' q', Feasible tlo thi p' q' → ∀ z : ℝ, (∀ P ∈ Pset, z ≤ expectedPayoff P c p' q') →
    ∀ P ∈ Pset, z ≤ expectedPayoff P c p q

end DRAllocCV


