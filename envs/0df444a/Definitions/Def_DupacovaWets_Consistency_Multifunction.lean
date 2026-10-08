-- Prove2me | Definitions.Def_DupacovaWets_Consistency_Multifunction
-- name    : DupacovaWets_Consistency_Multifunction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T13:28:31.54736+00:00
-- url     : https://prove2.me/theorems/4851799c-45a4-4739-8f7c-53db892856d0
-- title:
--   Measurable multifunctions, and measurability on a subset in the trace $\sigma$-field
-- statement:
--   Let $(T,\mathcal T)$ be a measurable space and $X$ a topological space. A multifunction (set-valued map) $\Gamma:T\rightrightarrows X$ is **measurable** if for every closed set $F\subseteq X$
--
--   $$
--   \Gamma^{-1}(F)=\{t\in T : \Gamma(t)\cap F\neq\emptyset\}\in\mathcal T .
--   $$
--
--   For a subset $Z_0\subseteq T$, $\Gamma$ is **measurable on $Z_0$** if its restriction to $Z_0$ is measurable for the trace $\sigma$-field $\{Z_0\cap B : B\in\mathcal T\}$, that is, for every closed $F$ there is $B\in\mathcal T$ with $\{t\in Z_0 : \Gamma(t)\cap F\neq\emptyset\}=Z_0\cap B$.
--
--   The first notion is the one recalled on p. 11 of Dupačová and Wets. The second is how their statements "$\zeta\mapsto\Gamma(\zeta): Z_0\rightrightarrows\mathbb R^n$ is $\mathcal F^\nu$-measurable" are read when the full-measure set $Z_0$ belongs to $\mathcal F$ but not necessarily to the smaller $\sigma$-field $\mathcal F^\nu$.
-- source:
--   Dupačová & Wets, IIASA Working Paper WP-86-41 (Aug. 1986), p. 11 (measurable multifunction); pp. 20–22 (multifunctions Z₀ ⇉ Rⁿ that are F^ν-measurable)

import Mathlib
open MeasureTheory

namespace DupacovaWets.Consistency

/-- Dupačová–Wets (WP-86-41), p. 11: a multifunction `Γ : T ⇉ X` is *measurable* if
`Γ⁻¹(F) = {t | Γ(t) ∩ F ≠ ∅}` is measurable for every closed set `F ⊆ X`. -/
def IsMeasurableMultifunction {T X : Type*} [MeasurableSpace T] [TopologicalSpace X]
    (Γ : T → Set X) : Prop :=
  ∀ F : Set X, IsClosed F → MeasurableSet {t | (Γ t ∩ F).Nonempty}

/-- Measurability of the restriction of `Γ` to a subset `Z₀ ⊆ T` with respect to the trace
of the σ-algebra `m` on `Z₀`: for every closed `F`, the set `{t ∈ Z₀ | Γ(t) ∩ F ≠ ∅}` is the
trace `Z₀ ∩ B` of some `m`-measurable `B`. This is the reading of "`Γ : Z₀ ⇉ ℝⁿ` is
`F^ν`-measurable" (pp. 20–22) when `Z₀` itself need not belong to `F^ν`. -/
def IsMeasurableMultifunctionOn {T X : Type*} [TopologicalSpace X] (m : MeasurableSpace T)
    (Z₀ : Set T) (Γ : T → Set X) : Prop :=
  ∀ F : Set X, IsClosed F →
    ∃ B : Set T, MeasurableSet[m] B ∧ {t | t ∈ Z₀ ∧ (Γ t ∩ F).Nonempty} = Z₀ ∩ B

end DupacovaWets.Consistency


