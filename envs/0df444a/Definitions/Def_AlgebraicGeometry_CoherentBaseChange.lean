-- Prove2me | Definitions.Def_AlgebraicGeometry_CoherentBaseChange
-- name    : AlgebraicGeometry_CoherentBaseChange
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/5a07cdde-fa33-5996-89c9-0308f8affa43
-- title:
--   Two-term complexes of finite free modules and their fibre ranks
-- statement:
--   Let $R$ be a commutative ring. The structure `TwoTermComplex R` packages the data of two types $C^0$, $C^1$, each carrying an additive group and $R$-module structure and each assumed finite and free as an $R$-module, together with an $R$-linear map $d : C^0 \to C^1$; the finiteness and freeness assumptions are fields of the structure, registered as instances. Four derived notions are attached to such a $G$. For a prime $\mathfrak p$ of $R$, written as a point of `PrimeSpectrum R`, with residue field $\kappa(\mathfrak p)$ taken as the residue field of the ideal $\mathfrak p$, `fibreH0` $\mathfrak p$ is the $\kappa(\mathfrak p)$-dimension (`Module.finrank`) of the kernel of the base change $d \otimes_R \kappa(\mathfrak p) : \kappa(\mathfrak p) \otimes_R C^0 \to \kappa(\mathfrak p) \otimes_R C^1$, and `fibreH1` $\mathfrak p$ is the $\kappa(\mathfrak p)$-dimension of the quotient of $\kappa(\mathfrak p) \otimes_R C^1$ by the range of that same base-changed map, i.e. of its cokernel. The integer `chi` is $\operatorname{rank}_R C^0 - \operatorname{rank}_R C^1$, formed as a difference of the two natural-number ranks inside $\mathbb Z$. For an $R$-algebra $A$, `H0 A` abbreviates the $A$-submodule $\ker(d \otimes_R A) \subseteq A \otimes_R C^0$, and `kerBaseChangeHom A` is the $A$-linear comparison map
--   $$A \otimes_R \ker d \longrightarrow \ker(d \otimes_R A)$$
--   obtained by base changing the inclusion $\ker d \hookrightarrow C^0$ and corestricting to the kernel, which is legitimate because $d$ composed with that inclusion vanishes. The auxiliary lemma `kerBaseChangeHom_apply_coe` records that the underlying element of $A \otimes_R C^0$ attached to a value of this map is the image of the same element under the base change of the inclusion. No property of these ranks or of the comparison map is asserted here: the module fixes the vocabulary in which such properties are stated.
--
--   **Relation to Mathlib.** The structure `TwoTermComplex` is the project's own packaging; it is built from Mathlib's `Module.Finite`, `Module.Free`, `LinearMap.baseChange`, `Module.finrank`, `PrimeSpectrum` and `Ideal.ResidueField` rather than from Mathlib's general homological-algebra complexes.
--
--   **Where it is used.** These definitions supply the language for semicontinuity and cohomology-and-base-change assertions: over an affine base, the cohomology of a coherent sheaf flat over the base with vanishing higher cohomology on fibres is computed by a complex of this shape, so that `fibreH0` and `fibreH1` are the fibre dimensions of $H^0$ and $H^1$, `chi` is the Euler characteristic, and `kerBaseChangeHom` is the base-change map in degree zero. They are used by the modules of the tree that need such control of families of cohomology groups.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_CoherentBaseChange.lean

import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Spectrum.Prime.Defs
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

universe u v w

namespace CoherentBaseChange

structure TwoTermComplex (R : Type u) [CommRing R] where

  C0 : Type v
  [C0_addCommGroup : AddCommGroup C0]
  [C0_module : Module R C0]
  [C0_finite : Module.Finite R C0]
  [C0_free : Module.Free R C0]

  C1 : Type v
  [C1_addCommGroup : AddCommGroup C1]
  [C1_module : Module R C1]
  [C1_finite : Module.Finite R C1]
  [C1_free : Module.Free R C1]

  d : C0 →ₗ[R] C1

attribute [instance] TwoTermComplex.C0_addCommGroup TwoTermComplex.C0_module
  TwoTermComplex.C0_finite TwoTermComplex.C0_free TwoTermComplex.C1_addCommGroup
  TwoTermComplex.C1_module TwoTermComplex.C1_finite TwoTermComplex.C1_free

namespace TwoTermComplex

variable {R : Type u} [CommRing R] (G : TwoTermComplex.{u, v} R)

def fibreH0 (𝔭 : PrimeSpectrum R) : ℕ :=
  Module.finrank 𝔭.asIdeal.ResidueField
    (LinearMap.ker (G.d.baseChange 𝔭.asIdeal.ResidueField))

def fibreH1 (𝔭 : PrimeSpectrum R) : ℕ :=
  Module.finrank 𝔭.asIdeal.ResidueField
    ((𝔭.asIdeal.ResidueField ⊗[R] G.C1) ⧸ LinearMap.range (G.d.baseChange 𝔭.asIdeal.ResidueField))

def chi : ℤ :=
  (Module.finrank R G.C0 : ℤ) - (Module.finrank R G.C1 : ℤ)

abbrev H0 (A : Type w) [CommRing A] [Algebra R A] : Submodule A (A ⊗[R] G.C0) :=
  LinearMap.ker (G.d.baseChange A)

def kerBaseChangeHom (A : Type w) [CommRing A] [Algebra R A] :
    A ⊗[R] (LinearMap.ker G.d) →ₗ[A] G.H0 A :=
  ((LinearMap.ker G.d).subtype.baseChange A).codRestrict (LinearMap.ker (G.d.baseChange A))
    (fun x => by
      rw [LinearMap.mem_ker, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp]
      have h : G.d ∘ₗ (LinearMap.ker G.d).subtype = 0 := by
        ext ⟨y, hy⟩
        exact hy
      rw [h, LinearMap.baseChange_zero, LinearMap.zero_apply])

theorem kerBaseChangeHom_apply_coe (A : Type w) [CommRing A] [Algebra R A]
    (x : A ⊗[R] (LinearMap.ker G.d)) :
    (G.kerBaseChangeHom A x : A ⊗[R] G.C0) = (LinearMap.ker G.d).subtype.baseChange A x :=
  rfl

end TwoTermComplex

end CoherentBaseChange


