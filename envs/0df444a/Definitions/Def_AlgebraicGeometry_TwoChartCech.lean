-- Prove2me | Definitions.Def_AlgebraicGeometry_TwoChartCech
-- name    : AlgebraicGeometry_TwoChartCech
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/9b25831e-f827-5701-ac91-d0c7100ba163
-- title:
--   Čech cohomology of two-chart covers; Grothendieck complexes
-- statement:
--   Over a commutative ring $R$, a [`TwoChartCech.Cover`](../def/AlgebraicGeometry_TwoChartCech.html#L17) consists of three commutative $R$-algebras $A_0$, $A_1$, $A_{01}$ together with $R$-algebra maps $\rho_0\colon A_0\to A_{01}$ and $\rho_1\colon A_1\to A_{01}$; the instances carrying the ring and algebra structures are fields of the structure. A `Sections` datum on a cover $\mathcal{U}$ consists of an $A_0$-module $M_0$, an $A_1$-module $M_1$ and an $A_{01}$-module $M_{01}$, each also an $R$-module compatibly (scalar-tower fields), together with $R$-linear maps $r_0\colon M_0\to M_{01}$, $r_1\colon M_1\to M_{01}$ and fields asserting the semilinearity $r_i(a\cdot m)=\rho_i(a)\cdot r_i(m)$. Its Čech differential is the $R$-linear map $M_0\times M_1\to M_{01}$, $(s_0,s_1)\mapsto r_1(s_1)-r_0(s_0)$; `H0` is its kernel, regarded as an $R$-submodule of $M_0\times M_1$, and `H1` is the quotient of $M_{01}$ by its range, as a type. Membership in `H0` is characterised by $r_0(s_0)=r_1(s_1)$.
--
--   For a unit $t\in A_{01}^{\times}$, `lineBundle` is the sections datum with $M_i=A_i$, $M_{01}=A_{01}$, $r_0=\rho_0$ and $r_1=t\cdot\rho_1$; `structureSheaf` is the case $t=1$, and $H^0$ is described by $\rho_0(p_0)=t\,\rho_1(p_1)$. `Cover.trivial` takes all three algebras to be $R$ with identity maps, and `Sections.ofSubmodules` builds, from submodules $N_0,N_1\le N_{01}$ of one $R$-module with the two inclusions, a sections datum over the trivial cover, whose $H^0$ consists of pairs with equal images.
--
--   The second half concerns base change for an arbitrary $R$-linear map $d\colon C^0\to C^1$: the comparison $A\otimes_R\ker d\to\ker(d\otimes_R A)$, and, for a commuting square from $d_K\colon K^0\to K^1$ to $d$, the induced maps on kernels and cokernels, both before and after tensoring with $A$. A `GrothendieckComplex` for $d$ packages a two-term complex $G$ of finite free $R$-modules (a [`CoherentBaseChange.TwoTermComplex`](../def/AlgebraicGeometry_CoherentBaseChange.html#L19)), maps $\iota_0,\iota_1$ with $d\circ\iota_0=\iota_1\circ d_G$, and two fields asserting that for every commutative $R$-algebra $A$ the induced maps on $\ker(d_G\otimes_R A)\to\ker(d\otimes_R A)$ and on the corresponding cokernels are bijective.
--
--   **Relation to Mathlib.** Mathlib has quasi-coherent sheaves and sheaf cohomology on schemes, but no packaged two-chart cover with its module-level Čech complex; these structures are the project's own. The kernel-comparison map here is the same construction as the one attached to [`CoherentBaseChange.TwoTermComplex`](../def/AlgebraicGeometry_CoherentBaseChange.html#L19), stated for an arbitrary $R$-linear map.
--
--   **Where it is used.** These structures give the module-level vocabulary for the Čech cohomology of a line bundle on a space covered by two affine charts with affine overlap, and for comparing such cohomology with that of a two-term complex of finite free modules after arbitrary base change; the `GrothendieckComplex` fields are exactly what is needed to transport semicontinuity and base-change statements from the free two-term complex to the original one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_TwoChartCech.lean

import Definitions.Def_AlgebraicGeometry_CoherentBaseChange
import Mathlib.Algebra.Algebra.Hom
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.TensorProduct.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

universe u v w

namespace TwoChartCech

structure Cover (R : Type u) [CommRing R] where

  A0 : Type v

  A1 : Type v

  A01 : Type v
  [A0_commRing : CommRing A0]
  [A0_algebra : Algebra R A0]
  [A1_commRing : CommRing A1]
  [A1_algebra : Algebra R A1]
  [A01_commRing : CommRing A01]
  [A01_algebra : Algebra R A01]

  ρ0 : A0 →ₐ[R] A01

  ρ1 : A1 →ₐ[R] A01

attribute [instance] Cover.A0_commRing Cover.A0_algebra Cover.A1_commRing Cover.A1_algebra
  Cover.A01_commRing Cover.A01_algebra

structure Sections {R : Type u} [CommRing R] (𝒰 : Cover.{u, v} R) where

  M0 : Type w

  M1 : Type w

  M01 : Type w
  [M0_addCommGroup : AddCommGroup M0]
  [M0_moduleA : Module 𝒰.A0 M0]
  [M0_module : Module R M0]
  [M0_tower : IsScalarTower R 𝒰.A0 M0]
  [M1_addCommGroup : AddCommGroup M1]
  [M1_moduleA : Module 𝒰.A1 M1]
  [M1_module : Module R M1]
  [M1_tower : IsScalarTower R 𝒰.A1 M1]
  [M01_addCommGroup : AddCommGroup M01]
  [M01_moduleA : Module 𝒰.A01 M01]
  [M01_module : Module R M01]
  [M01_tower : IsScalarTower R 𝒰.A01 M01]

  r0 : M0 →ₗ[R] M01

  r1 : M1 →ₗ[R] M01

  r0_smul : ∀ (a : 𝒰.A0) (m : M0), r0 (a • m) = 𝒰.ρ0 a • r0 m

  r1_smul : ∀ (a : 𝒰.A1) (m : M1), r1 (a • m) = 𝒰.ρ1 a • r1 m

attribute [instance] Sections.M0_addCommGroup Sections.M0_moduleA Sections.M0_module
  Sections.M0_tower Sections.M1_addCommGroup Sections.M1_moduleA Sections.M1_module
  Sections.M1_tower Sections.M01_addCommGroup Sections.M01_moduleA Sections.M01_module
  Sections.M01_tower

namespace Sections

variable {R : Type u} [CommRing R] {𝒰 : Cover.{u, v} R} (S : Sections.{u, v, w} 𝒰)

def cechDiff : S.M0 × S.M1 →ₗ[R] S.M01 := (-S.r0).coprod S.r1

theorem cechDiff_apply (s : S.M0 × S.M1) : S.cechDiff s = S.r1 s.2 - S.r0 s.1 := by
  simp [cechDiff, LinearMap.coprod_apply, sub_eq_neg_add]

abbrev H0 : Submodule R (S.M0 × S.M1) := LinearMap.ker S.cechDiff

theorem mem_H0_iff (s : S.M0 × S.M1) : s ∈ S.H0 ↔ S.r0 s.1 = S.r1 s.2 := by
  rw [LinearMap.mem_ker, cechDiff_apply, sub_eq_zero, eq_comm]

abbrev H1 : Type w := S.M01 ⧸ LinearMap.range S.cechDiff

end Sections

namespace Cover

variable {R : Type u} [CommRing R] (𝒰 : Cover.{u, v} R)

@[reducible] def lineBundle (t : 𝒰.A01ˣ) : Sections.{u, v, v} 𝒰 where
  M0 := 𝒰.A0
  M1 := 𝒰.A1
  M01 := 𝒰.A01
  r0 := 𝒰.ρ0.toLinearMap
  r1 := (t : 𝒰.A01) • 𝒰.ρ1.toLinearMap
  r0_smul a m := by simp
  r1_smul a m := by simp [mul_left_comm]

@[simp] theorem lineBundle_r0_apply (t : 𝒰.A01ˣ) (p : 𝒰.A0) : (𝒰.lineBundle t).r0 p = 𝒰.ρ0 p := rfl
@[simp] theorem lineBundle_r1_apply (t : 𝒰.A01ˣ) (p : 𝒰.A1) :
    (𝒰.lineBundle t).r1 p = (t : 𝒰.A01) * 𝒰.ρ1 p := rfl

theorem mem_H0_lineBundle_iff (t : 𝒰.A01ˣ) (p : 𝒰.A0 × 𝒰.A1) :
    p ∈ (𝒰.lineBundle t).H0 ↔ 𝒰.ρ0 p.1 = (t : 𝒰.A01) * 𝒰.ρ1 p.2 :=
  (𝒰.lineBundle t).mem_H0_iff p

abbrev structureSheaf : Sections.{u, v, v} 𝒰 := 𝒰.lineBundle 1

theorem mem_H0_structureSheaf_iff (p : 𝒰.A0 × 𝒰.A1) :
    p ∈ 𝒰.structureSheaf.H0 ↔ 𝒰.ρ0 p.1 = 𝒰.ρ1 p.2 := by
  rw [mem_H0_lineBundle_iff, Units.val_one, one_mul]

end Cover

section Dock

variable {R : Type u} [CommRing R]
variable {C0 : Type v} {C1 : Type v} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]

def kerBaseChangeHom (d : C0 →ₗ[R] C1) (A : Type w) [CommRing A] [Algebra R A] :
    A ⊗[R] (LinearMap.ker d) →ₗ[A] LinearMap.ker (d.baseChange A) :=
  ((LinearMap.ker d).subtype.baseChange A).codRestrict (LinearMap.ker (d.baseChange A))
    (fun x => by
      rw [LinearMap.mem_ker, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp]
      have h : d ∘ₗ (LinearMap.ker d).subtype = 0 := by
        ext ⟨y, hy⟩
        exact hy
      rw [h, LinearMap.baseChange_zero, LinearMap.zero_apply])

theorem kerBaseChangeHom_apply_coe (d : C0 →ₗ[R] C1) (A : Type w) [CommRing A] [Algebra R A]
    (x : A ⊗[R] (LinearMap.ker d)) :
    (kerBaseChangeHom d A x : A ⊗[R] C0) = (LinearMap.ker d).subtype.baseChange A x :=
  rfl

def kerMap {K0 : Type v} {K1 : Type v} [AddCommGroup K0] [Module R K0] [AddCommGroup K1]
    [Module R K1] (dK : K0 →ₗ[R] K1) (d : C0 →ₗ[R] C1) (ι0 : K0 →ₗ[R] C0) (ι1 : K1 →ₗ[R] C1)
    (comm : d ∘ₗ ι0 = ι1 ∘ₗ dK) : LinearMap.ker dK →ₗ[R] LinearMap.ker d :=
  ι0.restrict fun x hx => by
    rw [LinearMap.mem_ker] at hx ⊢
    rw [← LinearMap.comp_apply, comm, LinearMap.comp_apply, hx, map_zero]

def cokerMap {K0 : Type v} {K1 : Type v} [AddCommGroup K0] [Module R K0] [AddCommGroup K1]
    [Module R K1] (dK : K0 →ₗ[R] K1) (d : C0 →ₗ[R] C1) (ι0 : K0 →ₗ[R] C0) (ι1 : K1 →ₗ[R] C1)
    (comm : d ∘ₗ ι0 = ι1 ∘ₗ dK) : (K1 ⧸ LinearMap.range dK) →ₗ[R] (C1 ⧸ LinearMap.range d) :=
  Submodule.mapQ _ _ ι1 fun y hy => by
    obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hy
    rw [Submodule.mem_comap, ← LinearMap.comp_apply, ← comm, LinearMap.comp_apply]
    exact LinearMap.mem_range_self _ _

def kerMapBaseChange {K0 : Type v} {K1 : Type v} [AddCommGroup K0] [Module R K0] [AddCommGroup K1]
    [Module R K1] (dK : K0 →ₗ[R] K1) (d : C0 →ₗ[R] C1) (ι0 : K0 →ₗ[R] C0) (ι1 : K1 →ₗ[R] C1)
    (comm : d ∘ₗ ι0 = ι1 ∘ₗ dK) (A : Type w) [CommRing A] [Algebra R A] :
    LinearMap.ker (dK.baseChange A) →ₗ[A] LinearMap.ker (d.baseChange A) :=
  (ι0.baseChange A).restrict fun x hx => by
    rw [LinearMap.mem_ker] at hx ⊢
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, comm, LinearMap.baseChange_comp,
      LinearMap.comp_apply, hx, map_zero]

def cokerMapBaseChange {K0 : Type v} {K1 : Type v} [AddCommGroup K0] [Module R K0] [AddCommGroup K1]
    [Module R K1] (dK : K0 →ₗ[R] K1) (d : C0 →ₗ[R] C1) (ι0 : K0 →ₗ[R] C0) (ι1 : K1 →ₗ[R] C1)
    (comm : d ∘ₗ ι0 = ι1 ∘ₗ dK) (A : Type w) [CommRing A] [Algebra R A] :
    ((A ⊗[R] K1) ⧸ LinearMap.range (dK.baseChange A)) →ₗ[A]
      ((A ⊗[R] C1) ⧸ LinearMap.range (d.baseChange A)) :=
  Submodule.mapQ _ _ (ι1.baseChange A) fun y hy => by
    obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hy
    rw [Submodule.mem_comap, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp, ← comm,
      LinearMap.baseChange_comp, LinearMap.comp_apply]
    exact LinearMap.mem_range_self _ _

structure GrothendieckComplex (d : C0 →ₗ[R] C1) where

  G : CoherentBaseChange.TwoTermComplex.{u, v} R

  ι0 : G.C0 →ₗ[R] C0

  ι1 : G.C1 →ₗ[R] C1
  comm : d ∘ₗ ι0 = ι1 ∘ₗ G.d
  bijective_kerMap : ∀ (A : Type u) [CommRing A] [Algebra R A],
    Function.Bijective (kerMapBaseChange G.d d ι0 ι1 comm A)
  bijective_cokerMap : ∀ (A : Type u) [CommRing A] [Algebra R A],
    Function.Bijective (cokerMapBaseChange G.d d ι0 ι1 comm A)

end Dock

def Cover.trivial (R : Type u) [CommRing R] : Cover.{u, u} R where
  A0 := R
  A1 := R
  A01 := R
  ρ0 := AlgHom.id R R
  ρ1 := AlgHom.id R R

@[reducible] def Sections.ofSubmodules {R : Type u} [CommRing R] {F : Type v} [AddCommGroup F] [Module R F]
    (N0 N1 N01 : Submodule R F) (h0 : N0 ≤ N01) (h1 : N1 ≤ N01) : Sections.{u, u, v} (Cover.trivial R) :=

  letI : Module (Cover.trivial R).A0 N0 := inferInstanceAs (Module R N0)
  letI : Module (Cover.trivial R).A1 N1 := inferInstanceAs (Module R N1)
  letI : Module (Cover.trivial R).A01 N01 := inferInstanceAs (Module R N01)
  haveI : IsScalarTower R (Cover.trivial R).A0 N0 := ⟨fun a b m => mul_smul (a : R) (b : R) m⟩
  haveI : IsScalarTower R (Cover.trivial R).A1 N1 := ⟨fun a b m => mul_smul (a : R) (b : R) m⟩
  haveI : IsScalarTower R (Cover.trivial R).A01 N01 := ⟨fun a b m => mul_smul (a : R) (b : R) m⟩
  { M0 := N0
    M1 := N1
    M01 := N01
    r0 := Submodule.inclusion h0
    r1 := Submodule.inclusion h1
    r0_smul := fun _ _ => rfl
    r1_smul := fun _ _ => rfl }

theorem Sections.mem_H0_ofSubmodules_iff {R : Type u} [CommRing R] {F : Type v} [AddCommGroup F]
    [Module R F] (N0 N1 N01 : Submodule R F) (h0 : N0 ≤ N01) (h1 : N1 ≤ N01) (p : N0 × N1) :
    p ∈ (Sections.ofSubmodules N0 N1 N01 h0 h1).H0 ↔ (p.1 : F) = p.2 :=
  ((Sections.ofSubmodules N0 N1 N01 h0 h1).mem_H0_iff p).trans
    ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

section Gates

example (R : Type u) [CommRing R] (a b : R) :
    (a, b) ∈ (Cover.trivial R).structureSheaf.H0 ↔ a = b :=
  (Cover.trivial R).mem_H0_structureSheaf_iff (a, b)

example : ((1 : (Cover.trivial ℤ).A0), (1 : (Cover.trivial ℤ).A1)) ∉ ((Cover.trivial ℤ).lineBundle (-1)).H0 := by
  rw [Cover.mem_H0_lineBundle_iff]
  change ¬ ((1 : ℤ) = (-1 : ℤ) * 1)
  decide

example : ((1 : (Cover.trivial ℤ).A0), (-1 : (Cover.trivial ℤ).A1)) ∈ ((Cover.trivial ℤ).lineBundle (-1)).H0 := by
  rw [Cover.mem_H0_lineBundle_iff]
  change ((1 : ℤ) = (-1 : ℤ) * -1)
  decide

example (R : Type u) [CommRing R] : GrothendieckComplex (0 : R →ₗ[R] R) where
  G := { C0 := R, C1 := R, d := 0 }
  ι0 := LinearMap.id
  ι1 := LinearMap.id
  comm := by simp
  bijective_kerMap A _ _ := by
    have h : ∀ x, (kerMapBaseChange (0 : R →ₗ[R] R) 0 LinearMap.id LinearMap.id (by simp) A x) = x :=
      fun x => Subtype.ext (by simp [kerMapBaseChange, LinearMap.restrict_apply])
    exact ⟨fun x y hxy => by rwa [h, h] at hxy, fun y => ⟨y, h y⟩⟩
  bijective_cokerMap A _ _ := by
    have h : ∀ z, cokerMapBaseChange (0 : R →ₗ[R] R) 0 LinearMap.id LinearMap.id (by simp) A z = z := by
      intro z
      induction z using Submodule.Quotient.induction_on with
      | _ z =>
        show Submodule.Quotient.mk ((LinearMap.id.baseChange A) z) = Submodule.Quotient.mk z
        rw [LinearMap.baseChange_id, LinearMap.id_apply]
    exact ⟨fun x y hxy => by rwa [h, h] at hxy, fun y => ⟨y, h y⟩⟩

end Gates

end TwoChartCech

end


