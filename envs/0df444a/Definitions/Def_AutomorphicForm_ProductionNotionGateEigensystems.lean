-- Prove2me | Definitions.Def_AutomorphicForm_ProductionNotionGateEigensystems
-- name    : AutomorphicForm_ProductionNotionGateEigensystems
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/093123eb-f6e8-566a-be4d-46ecaeed045b
-- title:
--   Two explicit Hecke eigensystems over the rationals
-- statement:
--   Working with the project's notion of a Hecke eigensystem — a structure consisting of a nonzero ideal `level` of $\mathcal{O}_F$ together with two functions $a, b$ from the height-one spectrum of $\mathcal{O}_F$ to a commutative ring $R$ — this module records two completely explicit instances over $F = \mathbb{Q}$ with coefficients in $\mathbb{C}$, and one finiteness-type auxiliary fact.
--
--   `zeroSatakeEigensystem` has level the unit ideal $\top$ (nonzero because $1 \neq 0$, so that in the divisibility convention on ideals no maximal ideal divides it) and both coefficient functions identically zero: $a_v = 0$ and $b_v = 0$ for every $v$ in $\operatorname{HeightOneSpectrum}(\mathcal{O}_{\mathbb{Q}})$; two simp lemmas record these values. `principalShapeEigensystem` again has level $\top$, with $a_v = 2$ and $b_v = 1$ for every $v$. The pair $(2,1)$ is exactly the shape of the unit Satake datum, in the normalisation of `satakePow`, where $a$ plays the role of the sum and $b$ of the product of two Satake parameters, both equal to $1$; correspondingly $b$ is everywhere a unit, in contrast with the first eigensystem, whose $b$ vanishes identically.
--
--   The remaining declaration, `infinite_heightOneSpectrum_ratO`, asserts that $\operatorname{HeightOneSpectrum}(\mathcal{O}_{\mathbb{Q}})$ is an infinite type; it is obtained by transporting infinitude along the bijection between this spectrum and the rational primes. Its role is to guarantee that the finite exceptional sets $S$ occurring in the project's "away from a finite set" predicates (agreement away from a finite set, constancy on fibres, base change) cannot exhaust the places, so that such predicates retain content over $\mathbb{Q}$.
--
--   **Relation to Mathlib.** `HeckeEigensystem` and the `satakePow` normalisation are the project's own notions; Mathlib supplies the height-one spectrum of a Dedekind domain and the bijection `Rat.HeightOneSpectrum.primesEquiv` between the height-one spectrum of $\mathcal{O}_{\mathbb{Q}}$ and the rational primes, which is what the infinitude statement uses.
--
--   **Where it is used.** These two eigensystems serve as explicit test objects for the project's axiomatised cuspidality and base-change framework over number fields: one with identically vanishing Satake data and one with the unit Satake shape, both of level one. That framework is the interface through which the automorphic input (base change and descent for Hecke eigensystems) enters the modularity half of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_ProductionNotionGateEigensystems.lean

import Mathlib
import Definitions.Def_AutomorphicForm_HeckeEigensystem

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open IsDedekindDomain NumberField

noncomputable section

namespace AutomorphicForm

theorem infinite_heightOneSpectrum_ratO : Infinite (HeightOneSpectrum (𝓞 ℚ)) := by
  have hinj : Function.Injective
      (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm :=
    (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm.injective
  exact Infinite.of_injective _ hinj

def zeroSatakeEigensystem : HeckeEigensystem ℚ ℂ where
  level := ⊤
  level_ne_bot := by
    intro h
    have h1 : (1 : 𝓞 ℚ) ∈ (⊥ : Ideal (𝓞 ℚ)) := h ▸ Submodule.mem_top
    exact one_ne_zero (Ideal.mem_bot.mp h1)
  a := fun _ => 0
  b := fun _ => 0

@[simp] theorem zeroSatakeEigensystem_a (v : HeightOneSpectrum (𝓞 ℚ)) :
    zeroSatakeEigensystem.a v = 0 := rfl

@[simp] theorem zeroSatakeEigensystem_b (v : HeightOneSpectrum (𝓞 ℚ)) :
    zeroSatakeEigensystem.b v = 0 := rfl

def principalShapeEigensystem : HeckeEigensystem ℚ ℂ where
  level := ⊤
  level_ne_bot := by
    intro h
    have h1 : (1 : 𝓞 ℚ) ∈ (⊥ : Ideal (𝓞 ℚ)) := h ▸ Submodule.mem_top
    exact one_ne_zero (Ideal.mem_bot.mp h1)
  a := fun _ => 2
  b := fun _ => 1

end AutomorphicForm

end


