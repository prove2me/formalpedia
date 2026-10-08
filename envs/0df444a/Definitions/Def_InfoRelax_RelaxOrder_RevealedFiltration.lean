-- Prove2me | Definitions.Def_InfoRelax_RelaxOrder_RevealedFiltration
-- name    : InfoRelax_RelaxOrder_RevealedFiltration
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T07:38:24.445898+00:00
-- url     : https://prove2.me/theorems/56adc92c-8c5e-4f0c-90cb-2faf43487526
-- title:
--   The relaxation $\widehat{\mathbb G}$ that reveals estimated penalties (Proposition 2.3(iv))
-- statement:
--   Let $\mathbb G=(\mathcal G_0,\dots,\mathcal G_T)$ be a filtration and, for every period $s$ and every action sequence $a$, let $\hat z_s(a)$ be an $\mathcal F$-measurable real random variable (an estimate of a penalty term). The filtration $\widehat{\mathbb G}$ assumes that, in addition to what is known under $\mathbb G$, the values $\hat z_s(a)$ are revealed in period $s$:
--   $$\widehat{\mathcal G}_t=\mathcal G_t\vee\sigma\big(\hat z_s(a):\ s\le t,\ a\in X^{T+1}\big),\qquad t=0,\dots,T.$$
--
--   A value revealed in period $s$ remains known afterwards, so $\widehat{\mathbb G}$ is increasing; it lies between $\mathbb G$ and $\mathcal F$, so it is a relaxation of $\mathbb G$. It is the information structure under which estimated penalties are used in Proposition 2.3(iv).
--
--   **Formalization Note** The estimates of every action sequence are revealed, not only of the feasible ones. The measurability of each $\hat z_s(a)$ is an argument of the definition: it is what makes $\widehat{\mathcal G}_t\subseteq\mathcal F$.
-- source:
--   Brown, Smith & Sun, Information Relaxations and Duality in Stochastic Dynamic Programs, Oper. Res. (Articles in Advance, 2010), DOI 10.1287/opre.1090.0796, p. 6, Proposition 2.3(iv)

import Mathlib

open MeasureTheory

namespace InfoRelax.RelaxOrder

/-!
# The relaxation `𝔾̂` that reveals estimated penalties (Proposition 2.3(iv))

Brown, Smith & Sun, *Information Relaxations and Duality in Stochastic Dynamic Programs*,
Oper. Res. (Articles in Advance, 2010), DOI 10.1287/opre.1090.0796, p. 6, Proposition 2.3(iv):
"Let `𝔾̂` be a relaxation of `𝔾` that assumes that in addition to what is known under `𝔾`, the
values of `ẑ_t(a)` are revealed in period `t`."

Given a filtration `𝔾` and estimates `ẑ_s(a, ω)` (Lean: `zhat s a ω`) (one real random variable for every period `s`
and every action sequence `a`),
`𝒢̂_t = 𝒢_t ∨ σ(ẑ_s(a) : s ≤ t, a ∈ X^{T+1})`.

**Formalization Note.**
* A value revealed in period `s` stays known afterwards, so period `t` sees `ẑ_s(a)` for every
  `s ≤ t`; this union over `s ≤ t` is what makes `𝔾̂` increasing.
* Every `ẑ_s(a)` is revealed, for every action sequence `a`, not only the feasible ones and not
  only the one eventually chosen.
* The hypothesis `hzhat` (each `ẑ_s(a)` is `𝓕`-measurable) is what makes `𝒢̂_t ⊆ 𝓕`, so that `𝔾̂`
  is a filtration of the ambient σ-algebra; it is an argument of the definition, not a choice.
-/

variable {Ω X : Type*} [mΩ : MeasurableSpace Ω] {T : ℕ}

/-- The filtration `𝔾̂` of Proposition 2.3(iv), p. 6:
`𝒢̂_t = 𝒢_t ∨ σ(ẑ_s(a) : s ≤ t, a ∈ X^{T+1})`. -/
def revealedFiltration (𝔾 : Filtration (Fin (T + 1)) mΩ)
    (zhat : Fin (T + 1) → (Fin (T + 1) → X) → Ω → ℝ) (hzhat : ∀ s a, Measurable (zhat s a)) :
    Filtration (Fin (T + 1)) mΩ where
  seq t := 𝔾 t ⊔ ⨆ (s : Fin (T + 1)) (_ : s ≤ t) (a : Fin (T + 1) → X),
    MeasurableSpace.comap (zhat s a) (inferInstance : MeasurableSpace ℝ)
  mono' := by
    intro i j hij
    refine sup_le_sup (𝔾.mono hij) ?_
    refine iSup₂_le fun s hs => ?_
    exact le_iSup₂_of_le s (hs.trans hij) le_rfl
  le' := by
    intro t
    refine sup_le (𝔾.le t) ?_
    refine iSup₂_le fun s _ => iSup_le fun a => ?_
    exact (hzhat s a).comap_le

end InfoRelax.RelaxOrder


