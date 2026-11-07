-- Prove2me | Definitions.Def_PlantedIQP_mobiusCoeff
-- name    : PlantedIQP_mobiusCoeff
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:19:01.807724+00:00
-- url     : https://prove2.me/theorems/fc79fb10-fafa-4f4c-ac44-1b5f7c1cda8a
-- title:
--   Multilinear coefficients and degree of a Boolean function
-- statement:
--   Every function $F:\mathbb F_2^\iota\to\mathbb F_2$ on a finite index set $\iota$ has a unique multilinear representative $\sum_{S\subseteq\iota}c_S\prod_{i\in S}x_i$. Its coefficients are given by Möbius inversion,
--
--   $$
--   c_S=\sum_{T\subseteq S}F(\mathbf 1_T),
--   $$
--
--   where $\mathbf 1_T$ is the indicator vector of $T$; in particular $c_\varnothing=F(0)$ is the constant term. $F$ has **degree at most $d$** when $c_S=0$ for every $S$ with $|S|>d$. The cubic-polynomial record of $F$ collects its coefficients on sets of size $1,2,3$.
--
--   The paper works throughout with multilinear representatives: degrees, coefficients and compositions such as $f\circ A$ refer to them. The degree predicate expresses "$\deg(g|_V)\le 2$" (Proposition 20) and "quadratic polynomial" (Lemma 40).
--
--   **Formalization Note** The record of $F$ equals the multilinear representative of $F$ exactly when $F(0)=0$ and $F$ has degree at most $3$; it is only used for such $F$.
-- source:
--   Bläser, Gullans, Hangleiter, Liu, Qiao, Verifiable quantum advantage based on polynomials with planted structures, arXiv:2609.39918 (sha256 6e261694…), Section 2.1, p.13

import Mathlib
import Definitions.Def_PlantedIQP_CubicPoly

set_option autoImplicit false

namespace PlantedIQP

/-!
# Multilinear representatives and degree of Boolean functions

Bläser et al., arXiv:2609.39918 (sha256 6e261694…), Section 2.1, p.13: "Throughout, we identify
every polynomial f : 𝔽₂ⁿ → 𝔽₂ with its unique multilinear representative in 𝔽₂[x₁, …, xₙ], i.e.,
we work in 𝔽₂[x₁, …, xₙ]/(xᵢ² − xᵢ). When referring to degrees, coefficients and (formal)
derivatives we refer to this representative, and we reduce compositions such as f ◦ A back to this
representative."

**Formalization Note.**
* For a function `F : (ι → 𝔽₂) → 𝔽₂` on a finite index set `ι`, the coefficient of the monomial
  `Π_{i∈S} x_i` in its unique multilinear representative is the Möbius sum
  `mobiusCoeff F S = Σ_{T ⊆ S} F(1_T)`, with `1_T` the indicator vector of `T`. The constant term is
  `mobiusCoeff F ∅ = F 0`, so functions with a nonzero constant term are covered.
* `DegLE F d` says the multilinear representative has degree at most `d`: every coefficient on a
  set of more than `d` indices vanishes. This is the source's `deg(g|_V) ≤ 2` (Proposition 20) and
  "quadratic polynomial" (Lemma 40).
* `CubicPoly.ofFun F` reads the degree-1, -2 and -3 coefficients of `F`. It is the multilinear
  representative of `F` exactly when `F 0 = 0` and `DegLE F 3`; it is used only for such `F`
  (the composition `f ◦ A`).
-/

/-- The indicator vector `1_T ∈ 𝔽₂^ι` of a finite set `T ⊆ ι`. -/
def indicatorVec {ι : Type*} [DecidableEq ι] (T : Finset ι) : ι → ZMod 2 :=
  fun i => if i ∈ T then 1 else 0

/-- The coefficient of `Π_{i∈S} x_i` in the multilinear representative of `F`:
`Σ_{T ⊆ S} F(1_T)` (Möbius inversion over 𝔽₂). -/
def mobiusCoeff {ι : Type*} [DecidableEq ι] (F : (ι → ZMod 2) → ZMod 2) (S : Finset ι) :
    ZMod 2 :=
  ∑ T ∈ S.powerset, F (indicatorVec T)

/-- The multilinear representative of `F` has degree at most `d`. -/
def DegLE {ι : Type*} [DecidableEq ι] (F : (ι → ZMod 2) → ZMod 2) (d : ℕ) : Prop :=
  ∀ S : Finset ι, d < S.card → mobiusCoeff F S = 0

/-- The degree-1, -2, -3 coefficients of the multilinear representative of `F : 𝔽₂ⁿ → 𝔽₂`, as a
cubic polynomial record (faithful when `F 0 = 0` and `DegLE F 3`). -/
def CubicPoly.ofFun {n : ℕ} (F : Vec n → ZMod 2) : CubicPoly n :=
  ⟨fun S => mobiusCoeff F S.1, fun S => mobiusCoeff F S.1, fun i => mobiusCoeff F {i}⟩

end PlantedIQP


