-- Prove2me | Definitions.Def_UnramifiedWhittaker_ZetaIntegrand
-- name    : UnramifiedWhittaker_ZetaIntegrand
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/adc18f8d-9d2c-5c36-b6a8-e0c7efd11b27
-- title:
--   Zeta integrand and product-measure data for idele integrals
-- statement:
--   Throughout, $F$ is a number field, $\mathbb{A}$ denotes its adele ring $\mathbb{A}_F$ and $\mathbb{A}^{\times}$ the group of its units (the ideles).
--
--   First, `zetaIntegrand` takes a function $W$ on $\mathrm{GL}_2(\mathbb{A})$, a group homomorphism $\chi : \mathbb{A}^{\times} \to \mathbb{C}^{\times}$ (no continuity or unitarity is imposed), a complex number $s$ and an idele $a$, and returns
--   $$W(\mathtt{diagOne}\,a)\cdot \chi(a)\cdot \lVert a\rVert^{\,s-1},$$
--   where `diagOne a` is the element of $\mathrm{GL}_2(\mathbb{A})$ attached to $a$ by `diagOne`, and $\lVert a\rVert$ is `ideleNorm F a`, the value at $a$ of the module character `distribHaarChar` of $\mathbb{A}$, viewed as a positive real and then as a complex number, raised to the complex power $s-1$. This is a definition only: nothing is asserted about integrability.
--
--   Second, `ProductMeasureData S ν` is a structure, relative to a finite set $S$ of finite places of $F$ and a measure $\nu$ on $\mathbb{A}^{\times}$ for a chosen measurable structure, whose fields package a constant $c$ with $c>0$, a further measure $\nu_S$, a group endomorphism $\mathrm{pr}_S$ of $\mathbb{A}^{\times}$, integer-valued functions $\mathrm{ord}_v$ on $\mathbb{A}^{\times}$ for each finite place $v$, and four theorem-valued fields. These require: the $v$-component of $\mathrm{pr}_S(a)$ is $1$ for all $v \notin S$; for every duplicate-free list $L$ of places outside $S$ and every $a$ lying in `unitIdelesOutside` for $S \cup L$ (that is, $a_v$ and $(a^{-1})_v$ integral for every finite $v \notin S\cup L$) a factorisation $a = \mathrm{pr}_S(a)\cdot\prod_{v\in L}\varpi_v^{\mathrm{ord}_v(a)}\cdot u$ with $\varpi_v = \mathtt{uniformizerIdele}\,F\,v$ and $u$ having trivial infinite component, trivial components at the places of $S$ and unit finite part; a Fubini–Tonelli statement asserting, for $f$ integrable for $\nu_S$ and absolutely summable $\varphi_v : \mathbb{Z} \to \mathbb{C}$, that $a \mapsto f(\mathrm{pr}_S(a))\prod_{v\in L}\varphi_v(\mathrm{ord}_v(a))$ is $\nu$-integrable on that set with integral $c\cdot(\int f\,d\nu_S)\cdot\prod_{v\in L}\sum_{m\in\mathbb{Z}}\varphi_v(m)$; and measurability of the sets involved. No inhabitant is produced here.
--
--   **Relation to Mathlib.** The idele norm used here is the project's `ideleNorm`, built from Mathlib's `distribHaarChar`; the zeta integrand and the product-measure data structure have no Mathlib counterpart.
--
--   **Where it is used.** These definitions set up the local–global factorisation of Hecke–Whittaker zeta integrals over the idele group, with the hypotheses needed to turn an integral over ideles that are units outside a finite set into a constant times an integral over a smaller group times a product of Euler-type sums over the integers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_UnramifiedWhittaker_ZetaIntegrand.lean

import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_NumberField_IdeleBox

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open Matrix MeasureTheory Polynomial
open IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.AdeleRing NumberField.TateGlobal
open AutomorphicForm AdelicDock

namespace UnramifiedWhittaker

def zetaIntegrand {F : Type} [Field F] [NumberField F] (W : GL (Fin 2) (AdeleRing (𝓞 F) F) → ℂ)
    (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (s : ℂ) (a : (AdeleRing (𝓞 F) F)ˣ) : ℂ :=
  W (diagOne a) * ((χ a : ℂˣ) : ℂ) * ((ideleNorm F a : ℝ) : ℂ) ^ (s - 1)

structure ProductMeasureData {F : Type} [Field F] [NumberField F] [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (ν : Measure (AdeleRing (𝓞 F) F)ˣ) where

  c : ℝ
  c_pos : 0 < c

  νS : Measure (AdeleRing (𝓞 F) F)ˣ

  projS : (AdeleRing (𝓞 F) F)ˣ →* (AdeleRing (𝓞 F) F)ˣ

  ord : HeightOneSpectrum (𝓞 F) → (AdeleRing (𝓞 F) F)ˣ → ℤ
  projS_off : ∀ (a : (AdeleRing (𝓞 F) F)ˣ) (v : HeightOneSpectrum (𝓞 F)), v ∉ S →
    ((projS a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v = 1
  decomp : ∀ (L : List (HeightOneSpectrum (𝓞 F))), (∀ v ∈ L, v ∉ S) → L.Nodup →
    ∀ a ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F (↑S ∪ {v | v ∈ L}),
      ∃ u : (AdeleRing (𝓞 F) F)ˣ, (u : AdeleRing (𝓞 F) F).1 = 1 ∧
        (∀ v ∈ S, (u : AdeleRing (𝓞 F) F).2 v = 1) ∧
        finitePartUnits (𝓞 F) F u ∈ IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 F) F ∧
        a = projS a * (L.map fun v => uniformizerIdele F v ^ ord v a).prod * u
  tonelli : ∀ (L : List (HeightOneSpectrum (𝓞 F))), (∀ v ∈ L, v ∉ S) → L.Nodup →
    ∀ (f : (AdeleRing (𝓞 F) F)ˣ → ℂ) (φ : HeightOneSpectrum (𝓞 F) → ℤ → ℂ),
      Integrable f νS → (∀ v ∈ L, Summable fun m : ℤ => ‖φ v m‖) →
        IntegrableOn (fun a => f (projS a) * (L.map fun v => φ v (ord v a)).prod)
          (NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F (↑S ∪ {v | v ∈ L}) : Set (AdeleRing (𝓞 F) F)ˣ) ν ∧
        (∫ a in (NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F (↑S ∪ {v | v ∈ L}) : Set (AdeleRing (𝓞 F) F)ˣ),
            f (projS a) * (L.map fun v => φ v (ord v a)).prod ∂ν) =
          c * (∫ a, f a ∂νS) * (L.map fun v => ∑' m : ℤ, φ v m).prod

  measurableSet : ∀ (L : List (HeightOneSpectrum (𝓞 F))), (∀ v ∈ L, v ∉ S) → L.Nodup →
    MeasurableSet (NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F (↑S ∪ {v | v ∈ L}) : Set (AdeleRing (𝓞 F) F)ˣ)

end UnramifiedWhittaker

end


