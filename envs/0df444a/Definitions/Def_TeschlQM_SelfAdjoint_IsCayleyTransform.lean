-- Prove2me | Definitions.Def_TeschlQM_SelfAdjoint_IsCayleyTransform
-- name    : TeschlQM_SelfAdjoint_IsCayleyTransform
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:18:54.036776+00:00
-- url     : https://prove2.me/theorems/9ac5d8ef-8ecd-47df-a3a8-2909c35470eb
-- title:
--   Cayley transform V = (A − i)(A + i)⁻¹, isometric operators, Ran(1 − V), Eq. (2.102)
-- statement:
--   Let $A$ be a linear operator. An operator $V$ is the **Cayley transform** of $A$,
--   $$V = (A - \mathrm{i})(A + \mathrm{i})^{-1} : \operatorname{Ran}(A + \mathrm{i}) \to \operatorname{Ran}(A - \mathrm{i}),$$
--   if $\mathfrak{D}(V) = \operatorname{Ran}(A + \mathrm{i})$ and $V\big((A+\mathrm{i})\psi\big) = (A - \mathrm{i})\psi$ for every $\psi \in \mathfrak{D}(A)$.
--   An operator $V$ is **isometric** if $\|V\varphi\| = \|\varphi\|$ for all $\varphi \in \mathfrak{D}(V)$, and $\operatorname{Ran}(1 - V) = \{\varphi - V\varphi \mid \varphi \in \mathfrak{D}(V)\}$.
--
--   **Formalization Note.** The Cayley transform is given as a relation `IsCayleyTransform A V` between two `LinearPMap`s rather than as a function of `A`; the relation determines `V` uniquely from `A` (its domain and its values on that domain are prescribed), and for symmetric `A` such a `V` exists. Theorem 2.25 states both facts.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 81, Section 2.6, Eq. (2.102) and Theorem 2.25

import Mathlib
import Definitions.Def_TeschlQM_SelfAdjoint_addScalar

namespace TeschlQM.SelfAdjoint

/-- Teschl, p. 81 (Theorem 2.25): an operator `V` is *isometric* if `‖Vφ‖ = ‖φ‖` for all
`φ ∈ 𝔇(V)`. -/
def IsIsometric {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (V : H →ₗ.[ℂ] H) : Prop :=
  ∀ φ : V.domain, ‖V φ‖ = ‖(φ : H)‖

/-- `Ran(1 - V) = {φ - Vφ | φ ∈ 𝔇(V)}`. -/
def rangeOneSub {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (V : H →ₗ.[ℂ] H) : Submodule ℂ H :=
  LinearMap.range (V.domain.subtype - V.toFun)

/-- Teschl (2.102), p. 81: `V` is the *Cayley transform* of `A`,
`V = (A - i)(A + i)⁻¹ : Ran(A + i) → Ran(A - i)`. That is, `𝔇(V) = Ran(A + i)` and
`V((A + i)ψ) = (A - i)ψ` for every `ψ ∈ 𝔇(A)`. -/
def IsCayleyTransform {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A V : H →ₗ.[ℂ] H) : Prop :=
  V.domain = rangeAdd A Complex.I ∧
    ∀ ψ : A.domain, ∀ h : A ψ + Complex.I • (ψ : H) ∈ V.domain,
      V ⟨A ψ + Complex.I • (ψ : H), h⟩ = A ψ - Complex.I • (ψ : H)

end TeschlQM.SelfAdjoint


