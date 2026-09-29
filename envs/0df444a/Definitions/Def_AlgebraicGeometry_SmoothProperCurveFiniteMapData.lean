-- Prove2me | Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
-- name    : AlgebraicGeometry_SmoothProperCurveFiniteMapData
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/6412eb9d-e754-5d74-b28e-5d9c7ca9b585
-- title:
--   Chart-wise data for a finite map from a curve
-- statement:
--   Fix a commutative ring $R$, a scheme $C$ with a morphism $c : C \to \operatorname{Spec} R$, and a section $\varepsilon$ of $c$, i.e. an element of the subtype of morphisms $\operatorname{Spec} R \to C$ whose composite with $c$ is the identity. The structure `FiniteMapData c ε` packages, in chart form, a finite map of degree $m$ from $C$ to the projective line over $R$ whose pole divisor is supported on the section. Its fields are: two opens $U, V$ of $C$, sections $f \in \Gamma(C,U)$ and $g \in \Gamma(C,V)$, a natural number $m$; proofs that $U$ and $V$ are affine opens and that $U \sqcup V = \top$; the condition that a point lies in $U$ exactly when it is not in the image of the underlying map of $\varepsilon$; the two identifications $U \sqcap V = C_{\mathrm{basicOpen}}(f)$ and $U \sqcap V = C_{\mathrm{basicOpen}}(g)$; the relation that the restrictions of $f$ and $g$ to $U \sqcap V$ multiply to $1$; finiteness of the ring maps $\mathrm{aeval}\,f : R[X] \to \Gamma(C,U)$ and $\mathrm{aeval}\,g : R[X] \to \Gamma(C,V)$, the $R$-algebra structures on the section rings being those induced by $c$ through `Scheme.TwoAffineOpenCover.algebraOfHom`; and finally, for every local commutative $R$-algebra $S$ and every $s \in S$, that the level-set ring $S \otimes_R \Gamma(C,U)/(1 \otimes f - s \otimes 1)$ is a finite free $S$-module of rank exactly $m$.
--
--   The accompanying lemmas record that the image of $\varepsilon$ lies in $V$, that $U$ is precisely the complement of that image, that $U \sqcap V$ is affine and $C_{\mathrm{basicOpen}}(f) = C_{\mathrm{basicOpen}}(g)$, and they repackage the datum as a two-chart affine cover with $U_0 = V$, $U_1 = U$; `moduleFinite_U`, `moduleFinite_V`, `levelSet_finite` and `levelSet_finrank_eq` restate the finiteness and rank fields in module-theoretic form. Separately, the predicate `LevelSetsGenericallyEtale` on such a datum asserts the existence of a polynomial $D \in R[X]$ having at least one unit coefficient such that, for every local $R$-algebra $S$ whose structure map is a local homomorphism and every $s \in S$ with $D(s)$ a unit, the level-set algebra above is étale over $S$. Étaleness on special fibres is thus not part of the datum but an extra hypothesis to be imposed where needed.
--
--   **Relation to Mathlib.** Mathlib has no notion of this kind of chart-wise presentation of a finite map to the projective line; the structure and the predicate `LevelSetsGenericallyEtale` are the project's own, built from Mathlib's `IsAffineOpen`, `Scheme.basicOpen`, `RingHom.Finite`, `Module.Free`/`Module.finrank` and `Algebra.Etale`, and feeding the project's `Scheme.TwoAffineOpenCover`.
--
--   **Where it is used.** The datum records, without reference to a projective line as a scheme, a degree-$m$ finite map from a relative curve to $\mathbb P^1_R$ with pole only along a given section, and converts it into the two-chart affine cover on which the project's Čech-style computations of sections and cohomology over varying bases are carried out; these in turn serve the curve and Néron-model infrastructure behind the Galois-representation input to the modularity argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits NeronModelInfra

namespace AlgebraicGeometry.SmoothProperCurve

structure FiniteMapData {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) where

  U : C.Opens

  V : C.Opens

  f : Γ(C, U)

  g : Γ(C, V)

  m : ℕ
  isAffineOpen_U : IsAffineOpen U
  isAffineOpen_V : IsAffineOpen V
  sup_eq_top : U ⊔ V = ⊤

  mem_U_iff : ∀ x : C, x ∈ U ↔ x ∉ Set.range ε.1.base

  inf_eq_basicOpen : U ⊓ V = C.basicOpen f

  inf_eq_basicOpen_g : U ⊓ V = C.basicOpen g

  res_f_mul_res_g : (C.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op).hom f *
      (C.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op).hom g = 1

  finite_f : letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    (Polynomial.aeval f : Polynomial R →ₐ[R] Γ(C, U)).toRingHom.Finite

  finite_g : letI := Scheme.TwoAffineOpenCover.algebraOfHom c V
    (Polynomial.aeval g : Polynomial R →ₐ[R] Γ(C, V)).toRingHom.Finite

  levelSet_free : ∀ (S : Type u) [CommRing S] [Algebra R S] [IsLocalRing S] (s : S),
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    Module.Finite S (S ⊗[R] Γ(C, U) ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : Γ(C, U))}) ∧
      Module.Free S (S ⊗[R] Γ(C, U) ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : Γ(C, U))}) ∧
      Module.finrank S (S ⊗[R] Γ(C, U) ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : Γ(C, U))}) = m

namespace FiniteMapData

variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} (𝔉 : FiniteMapData c ε)

theorem range_subset_V : Set.range ε.1.base ⊆ (𝔉.V : Set C) := by
  rintro x ⟨y, rfl⟩
  have hx : ε.1.base y ∈ (⊤ : C.Opens) := trivial
  rw [← 𝔉.sup_eq_top, TopologicalSpace.Opens.mem_sup] at hx
  rcases hx with h | h
  · exact absurd ⟨y, rfl⟩ ((𝔉.mem_U_iff _).mp h)
  · exact h

theorem coe_U_eq_compl : (𝔉.U : Set C) = (Set.range ε.1.base)ᶜ :=
  Set.ext fun x => 𝔉.mem_U_iff x

theorem isAffineOpen_inf : IsAffineOpen (𝔉.U ⊓ 𝔉.V) := by
  rw [𝔉.inf_eq_basicOpen]; exact 𝔉.isAffineOpen_U.basicOpen _

theorem basicOpen_f_eq_basicOpen_g : C.basicOpen 𝔉.f = C.basicOpen 𝔉.g := by
  rw [← 𝔉.inf_eq_basicOpen, 𝔉.inf_eq_basicOpen_g]

def twoAffineOpenCover : C.TwoAffineOpenCover where
  U0 := 𝔉.V
  U1 := 𝔉.U
  isAffineOpen_U0 := 𝔉.isAffineOpen_V
  isAffineOpen_U1 := 𝔉.isAffineOpen_U
  sup_eq_top := by rw [sup_comm, 𝔉.sup_eq_top]
  isAffineOpen_inf := by rw [inf_comm]; exact 𝔉.isAffineOpen_inf

@[simp] theorem twoAffineOpenCover_U0 : 𝔉.twoAffineOpenCover.U0 = 𝔉.V := rfl
@[simp] theorem twoAffineOpenCover_U1 : 𝔉.twoAffineOpenCover.U1 = 𝔉.U := rfl

theorem range_subset_twoAffineOpenCover_U0 : Set.range ε.1.base ⊆ (𝔉.twoAffineOpenCover.U0 : Set C) :=
  𝔉.range_subset_V

theorem twoAffineOpenCover_U1_eq_compl : (𝔉.twoAffineOpenCover.U1 : Set C) = (Set.range ε.1.base)ᶜ :=
  𝔉.coe_U_eq_compl

theorem moduleFinite_U :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c 𝔉.U
    letI : Algebra (Polynomial R) Γ(C, 𝔉.U) := (Polynomial.aeval 𝔉.f : Polynomial R →ₐ[R] Γ(C, 𝔉.U)).toRingHom.toAlgebra
    Module.Finite (Polynomial R) Γ(C, 𝔉.U) :=
  𝔉.finite_f

theorem moduleFinite_V :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c 𝔉.V
    letI : Algebra (Polynomial R) Γ(C, 𝔉.V) := (Polynomial.aeval 𝔉.g : Polynomial R →ₐ[R] Γ(C, 𝔉.V)).toRingHom.toAlgebra
    Module.Finite (Polynomial R) Γ(C, 𝔉.V) :=
  𝔉.finite_g

theorem levelSet_finite (S : Type u) [CommRing S] [Algebra R S] [IsLocalRing S] (s : S) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c 𝔉.U
    Module.Finite S (S ⊗[R] Γ(C, 𝔉.U) ⧸
      Ideal.span {(1 : S) ⊗ₜ[R] 𝔉.f - s ⊗ₜ[R] (1 : Γ(C, 𝔉.U))}) :=
  (𝔉.levelSet_free S s).1

theorem levelSet_finrank_eq (S : Type u) [CommRing S] [Algebra R S] [IsLocalRing S] (s : S) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c 𝔉.U
    Module.finrank S (S ⊗[R] Γ(C, 𝔉.U) ⧸
      Ideal.span {(1 : S) ⊗ₜ[R] 𝔉.f - s ⊗ₜ[R] (1 : Γ(C, 𝔉.U))}) = 𝔉.m :=
  (𝔉.levelSet_free S s).2.2

def LevelSetsGenericallyEtale : Prop :=
  ∃ D : Polynomial R, (∃ i, IsUnit (D.coeff i)) ∧
    ∀ (S : Type u) [CommRing S] [Algebra R S] [IsLocalRing S] [IsLocalHom (algebraMap R S)] (s : S),
      IsUnit (Polynomial.aeval s D) →
      letI := Scheme.TwoAffineOpenCover.algebraOfHom c 𝔉.U
      Algebra.Etale S (S ⊗[R] Γ(C, 𝔉.U) ⧸
        Ideal.span {(1 : S) ⊗ₜ[R] 𝔉.f - s ⊗ₜ[R] (1 : Γ(C, 𝔉.U))})

end FiniteMapData

end AlgebraicGeometry.SmoothProperCurve

end


