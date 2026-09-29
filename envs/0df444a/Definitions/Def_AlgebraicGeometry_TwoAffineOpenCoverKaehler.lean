-- Prove2me | Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverKaehler
-- name    : AlgebraicGeometry_TwoAffineOpenCoverKaehler
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/c8d47189-bd01-5110-936f-e06bdcf99db8
-- title:
--   Kähler differentials as two-chart Čech sections, with functoriality
-- statement:
--   The module has three layers. First, for commutative rings with $A$ an $R$-algebra and $B$ an $S$-algebra, a ring homomorphism $\tau\colon R\to S$ and a ring homomorphism $\varphi\colon A\to B$ with $\varphi\circ(R\to A)=(S\to B)\circ\tau$ determine a $\tau$-semilinear map [`KaehlerDifferential.mapOfRingHom`](../def/AlgebraicGeometry_TwoAffineOpenCoverKaehler.html#L16) $\Omega_{A/R}\to\Omega_{B/S}$, obtained from Mathlib's functorial map for the algebra and tower structures that the given square provides; its characteristic properties are $\mathrm{d}a\mapsto \mathrm{d}\varphi(a)$, $a\cdot\omega\mapsto\varphi(a)\cdot$ (image of $\omega$), hence $a\,\mathrm{d}a'\mapsto\varphi(a)\,\mathrm{d}\varphi(a')$. An extensionality lemma — two additive maps out of $\Omega_{A/R}$ agreeing on all $a\,\mathrm{d}a'$ are equal, since the elements $\mathrm{d}a'$ generate — yields: independence of the construction from the chosen $\tau$ when $\varphi$ is fixed, the identity case, compatibility with composition of squares, and agreement with `KaehlerDifferential.map` when $\varphi$ is the structure map.
--
--   Second, for a two-chart cover $\mathcal U=(A_0,A_1,A_{01};\rho_0,\rho_1)$ of $R$-algebras, [`TwoChartCech.Cover.kaehler`](../def/AlgebraicGeometry_TwoAffineOpenCoverKaehler.html#L120) is the `Sections` datum with modules $\Omega_{A_0/R}$, $\Omega_{A_1/R}$, $\Omega_{A_{01}/R}$ and restriction maps induced by $\rho_0,\rho_1$; its Čech differential sends $(\mathrm{d}s_0,\mathrm{d}s_1)$ to $\mathrm{d}$ of the structure-sheaf Čech difference $\rho_1s_1-\rho_0s_0$.
--
--   Third, for a scheme $X$ with a cover $\mathcal V$ by two affine opens with affine intersection and a morphism $c\colon X\to\operatorname{Spec}R$, `kaehlerSections` is this datum for the chart algebras $\Gamma(X,U_0)$, $\Gamma(X,U_1)$, $\Gamma(X,U_0\cap U_1)$. A `HomOver` $f$ over $\tau$ gives ring maps on the three chart rings (via `appLE`) commuting with the structure maps, hence $\tau$-semilinear maps on differentials which commute with the two restrictions and with the Čech differential; consequently $f$ induces semilinear maps `kaehlerH0map` on the kernel and `kaehlerH1map` on the quotient by the image. These are functorial: identities act as identities and composition is respected, and the base-change and stage morphisms give maps `kaehlerH0baseChangeMap`, `kaehlerH1baseChangeMap`, `kaehlerH0stageMap`, `kaehlerH1stageMap` satisfying the expected triangle, identity and composition identities, proved by comparing the underlying scheme morphisms.
--
--   **Relation to Mathlib.** [`KaehlerDifferential.mapOfRingHom`](../def/AlgebraicGeometry_TwoAffineOpenCoverKaehler.html#L16) repackages Mathlib's `KaehlerDifferential.map`, which needs the algebra and scalar-tower structures as instances, into a semilinear map attached to a commuting square of bare ring homomorphisms, so that restriction and base-change maps on a cover need not be registered as instances; the two-chart `Cover`/`Sections` formalism and the Čech $H^0$, $H^1$ built from it are the project's own.
--
--   **Where it is used.** These constructions supply the Čech model of $H^0$ and $H^1$ of the sheaf of relative differentials on a scheme covered by two affine opens, together with its variance in the base, which is what the relative Picard and Néron-model infrastructure of the curve side of the argument operates on.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_TwoAffineOpenCoverKaehler.lean

import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverH1BaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

universe u v

namespace KaehlerDifferential

variable {R : Type*} {S : Type*} {A : Type*} {B : Type*} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra S B]

def mapOfRingHom (τ : R →+* S) (φ : A →+* B) (h : φ.comp (algebraMap R A) = (algebraMap S B).comp τ) :
    Ω[A⁄R] →ₛₗ[τ] Ω[B⁄S] :=
  letI : Algebra R S := τ.toAlgebra
  letI : Algebra A B := φ.toAlgebra
  letI : Algebra R B := ((algebraMap S B).comp τ).toAlgebra
  haveI : IsScalarTower R S B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun r => (RingHom.congr_fun h r).symm
  haveI : SMulCommClass S A B := ⟨fun s a b => by
    rw [Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, Algebra.smul_def]; exact mul_left_comm _ _ _⟩
  { toFun := KaehlerDifferential.map R S A B
    map_add' := map_add _
    map_smul' := fun r ω => by
      rw [← IsScalarTower.algebraMap_smul A r ω, LinearMap.map_smul,
        ← IsScalarTower.algebraMap_smul B (algebraMap R A r), ← IsScalarTower.algebraMap_smul B (τ r)]
      exact congrArg (· • _) (RingHom.congr_fun h r) }

variable (τ : R →+* S) (φ : A →+* B) (h : φ.comp (algebraMap R A) = (algebraMap S B).comp τ)

@[simp] theorem mapOfRingHom_D (a : A) : mapOfRingHom τ φ h (D R A a) = D S B (φ a) :=
  letI : Algebra R S := τ.toAlgebra
  letI : Algebra A B := φ.toAlgebra
  letI : Algebra R B := ((algebraMap S B).comp τ).toAlgebra
  haveI : IsScalarTower R S B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun r => (RingHom.congr_fun h r).symm
  haveI : SMulCommClass S A B := ⟨fun s a b => by
    rw [Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, Algebra.smul_def]; exact mul_left_comm _ _ _⟩
  KaehlerDifferential.map_D R S A B a

theorem mapOfRingHom_smul (a : A) (ω : Ω[A⁄R]) : mapOfRingHom τ φ h (a • ω) = φ a • mapOfRingHom τ φ h ω :=
  letI : Algebra R S := τ.toAlgebra
  letI : Algebra A B := φ.toAlgebra
  letI : Algebra R B := ((algebraMap S B).comp τ).toAlgebra
  haveI : IsScalarTower R S B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun r => (RingHom.congr_fun h r).symm
  haveI : SMulCommClass S A B := ⟨fun s a b => by
    rw [Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, Algebra.smul_def]; exact mul_left_comm _ _ _⟩
  ((KaehlerDifferential.map R S A B).map_smul a ω).trans (IsScalarTower.algebraMap_smul B a _).symm

theorem mapOfRingHom_smul_D (a a' : A) : mapOfRingHom τ φ h (a • D R A a') = φ a • D S B (φ a') := by
  rw [mapOfRingHom_smul, mapOfRingHom_D]

omit [Algebra S B] in

theorem addMonoidHom_ext_smul_D {M : Type*} [AddCommGroup M] {f g : Ω[A⁄R] →+ M}
    (hfg : ∀ a a' : A, f (a • D R A a') = g (a • D R A a')) : f = g := by
  ext ω
  have hω : ω ∈ Submodule.span A (Set.range (D R A)) := by
    rw [KaehlerDifferential.span_range_derivation]; exact Submodule.mem_top
  obtain ⟨c, rfl⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).mp hω
  simp only [Finsupp.sum, map_sum, hfg]

theorem mapOfRingHom_congr {τ τ' : R →+* S} {φ φ' : A →+* B} (hφ : φ = φ')
    (h : φ.comp (algebraMap R A) = (algebraMap S B).comp τ) (h' : φ'.comp (algebraMap R A) = (algebraMap S B).comp τ')
    (ω : Ω[A⁄R]) : mapOfRingHom τ φ h ω = mapOfRingHom τ' φ' h' ω := by
  subst hφ
  have key := addMonoidHom_ext_smul_D (f := (mapOfRingHom τ φ h).toAddMonoidHom)
    (g := (mapOfRingHom τ' φ h').toAddMonoidHom) (fun a a' => by
      change mapOfRingHom τ φ h (a • D R A a') = mapOfRingHom τ' φ h' (a • D R A a')
      rw [mapOfRingHom_smul_D, mapOfRingHom_smul_D])
  exact DFunLike.congr_fun key ω

omit [Algebra S B] in

theorem mapOfRingHom_id (h : (RingHom.id A).comp (algebraMap R A) = (algebraMap R A).comp (RingHom.id R))
    (ω : Ω[A⁄R]) : mapOfRingHom (RingHom.id R) (RingHom.id A) h ω = ω := by
  have key := addMonoidHom_ext_smul_D (f := (mapOfRingHom (RingHom.id R) (RingHom.id A) h).toAddMonoidHom)
    (g := AddMonoidHom.id _) (fun a a' => by
      change mapOfRingHom (RingHom.id R) (RingHom.id A) h (a • D R A a') = a • D R A a'
      rw [mapOfRingHom_smul_D]; rfl)
  exact DFunLike.congr_fun key ω

theorem mapOfRingHom_comp_apply {T : Type*} {C : Type*} [CommRing T] [CommRing C] [Algebra T C]
    (υ : S →+* T) (ψ : B →+* C) (h₂ : ψ.comp (algebraMap S B) = (algebraMap T C).comp υ)
    (h₃ : (ψ.comp φ).comp (algebraMap R A) = (algebraMap T C).comp (υ.comp τ)) (ω : Ω[A⁄R]) :
    mapOfRingHom υ ψ h₂ (mapOfRingHom τ φ h ω) = mapOfRingHom (υ.comp τ) (ψ.comp φ) h₃ ω := by
  have key := addMonoidHom_ext_smul_D
    (f := (mapOfRingHom υ ψ h₂).toAddMonoidHom.comp (mapOfRingHom τ φ h).toAddMonoidHom)
    (g := (mapOfRingHom (υ.comp τ) (ψ.comp φ) h₃).toAddMonoidHom) (fun a a' => by
      change mapOfRingHom υ ψ h₂ (mapOfRingHom τ φ h (a • D R A a')) =
        mapOfRingHom (υ.comp τ) (ψ.comp φ) h₃ (a • D R A a')
      rw [mapOfRingHom_smul_D, mapOfRingHom_smul_D, mapOfRingHom_smul_D]; rfl)
  exact DFunLike.congr_fun key ω

theorem mapOfRingHom_apply_eq_map [Algebra R S] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [IsScalarTower R S B] [SMulCommClass S A B] (hφ : algebraMap A B = φ) (ω : Ω[A⁄R]) :
    mapOfRingHom τ φ h ω = KaehlerDifferential.map R S A B ω := by
  have key := addMonoidHom_ext_smul_D (f := (mapOfRingHom τ φ h).toAddMonoidHom)
    (g := (KaehlerDifferential.map R S A B).toAddMonoidHom) (fun a a' => by
      change mapOfRingHom τ φ h (a • D R A a') = KaehlerDifferential.map R S A B (a • D R A a')
      rw [mapOfRingHom_smul_D, LinearMap.map_smul, KaehlerDifferential.map_D, ← IsScalarTower.algebraMap_smul B a,
        hφ])
  exact DFunLike.congr_fun key ω

end KaehlerDifferential

namespace TwoChartCech.Cover

variable {R : Type u} [CommRing R] (𝒰 : Cover.{u, v} R)

theorem ρ0_comp_algebraMap_eq_comp_id : 𝒰.ρ0.toRingHom.comp (algebraMap R 𝒰.A0) = (algebraMap R 𝒰.A01).comp (RingHom.id R) :=
  RingHom.ext fun r => 𝒰.ρ0.commutes r
theorem ρ1_comp_algebraMap_eq_comp_id : 𝒰.ρ1.toRingHom.comp (algebraMap R 𝒰.A1) = (algebraMap R 𝒰.A01).comp (RingHom.id R) :=
  RingHom.ext fun r => 𝒰.ρ1.commutes r

@[reducible] def kaehler : Sections.{u, v, v} 𝒰 where
  M0 := Ω[𝒰.A0⁄R]
  M1 := Ω[𝒰.A1⁄R]
  M01 := Ω[𝒰.A01⁄R]
  r0 := KaehlerDifferential.mapOfRingHom (RingHom.id R) 𝒰.ρ0.toRingHom 𝒰.ρ0_comp_algebraMap_eq_comp_id
  r1 := KaehlerDifferential.mapOfRingHom (RingHom.id R) 𝒰.ρ1.toRingHom 𝒰.ρ1_comp_algebraMap_eq_comp_id
  r0_smul a m := KaehlerDifferential.mapOfRingHom_smul _ _ 𝒰.ρ0_comp_algebraMap_eq_comp_id a m
  r1_smul a m := KaehlerDifferential.mapOfRingHom_smul _ _ 𝒰.ρ1_comp_algebraMap_eq_comp_id a m

theorem kaehler_M0 : 𝒰.kaehler.M0 = Ω[𝒰.A0⁄R] := rfl
theorem kaehler_M1 : 𝒰.kaehler.M1 = Ω[𝒰.A1⁄R] := rfl
theorem kaehler_M01 : 𝒰.kaehler.M01 = Ω[𝒰.A01⁄R] := rfl

theorem kaehler_r0_smul_D (a s : 𝒰.A0) :
    𝒰.kaehler.r0 (a • KaehlerDifferential.D R 𝒰.A0 s) = 𝒰.ρ0 a • KaehlerDifferential.D R 𝒰.A01 (𝒰.ρ0 s) :=
  KaehlerDifferential.mapOfRingHom_smul_D _ _ 𝒰.ρ0_comp_algebraMap_eq_comp_id a s
theorem kaehler_r1_smul_D (a s : 𝒰.A1) :
    𝒰.kaehler.r1 (a • KaehlerDifferential.D R 𝒰.A1 s) = 𝒰.ρ1 a • KaehlerDifferential.D R 𝒰.A01 (𝒰.ρ1 s) :=
  KaehlerDifferential.mapOfRingHom_smul_D _ _ 𝒰.ρ1_comp_algebraMap_eq_comp_id a s
theorem kaehler_r0_D (s : 𝒰.A0) : 𝒰.kaehler.r0 (KaehlerDifferential.D R 𝒰.A0 s) = KaehlerDifferential.D R 𝒰.A01 (𝒰.ρ0 s) :=
  KaehlerDifferential.mapOfRingHom_D _ _ 𝒰.ρ0_comp_algebraMap_eq_comp_id s
theorem kaehler_r1_D (s : 𝒰.A1) : 𝒰.kaehler.r1 (KaehlerDifferential.D R 𝒰.A1 s) = KaehlerDifferential.D R 𝒰.A01 (𝒰.ρ1 s) :=
  KaehlerDifferential.mapOfRingHom_D _ _ 𝒰.ρ1_comp_algebraMap_eq_comp_id s

theorem kaehler_cechDiff_D (s₀ : 𝒰.A0) (s₁ : 𝒰.A1) :
    𝒰.kaehler.cechDiff (KaehlerDifferential.D R 𝒰.A0 s₀, KaehlerDifferential.D R 𝒰.A1 s₁) =
      KaehlerDifferential.D R 𝒰.A01 (𝒰.structureSheaf.cechDiff (s₀, s₁)) := by
  rw [Sections.cechDiff_apply, Sections.cechDiff_apply, kaehler_r0_D, kaehler_r1_D, map_sub,
    lineBundle_r1_apply, lineBundle_r0_apply, Units.val_one, one_mul]

end TwoChartCech.Cover

namespace AlgebraicGeometry.Scheme.TwoAffineOpenCover

open CategoryTheory CategoryTheory.Limits

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))

abbrev kaehlerSections : TwoChartCech.Sections (𝒱.cover c) := (𝒱.cover c).kaehler

namespace HomOver

variable {S : Type u} [CommRing S] {τ : R →+* S} {𝒱} {c} {Y : Scheme.{u}} {𝒲 : Y.TwoAffineOpenCover}
  {c' : Y ⟶ Spec (.of S)} (f : HomOver τ 𝒱 c 𝒲 c')

def ringHom0 : (𝒱.cover c).A0 →+* (𝒲.cover c').A0 := (f.hom.appLE 𝒱.U0 𝒲.U0 f.U0_le).hom
def ringHom1 : (𝒱.cover c).A1 →+* (𝒲.cover c').A1 := (f.hom.appLE 𝒱.U1 𝒲.U1 f.U1_le).hom
def ringHom01 : (𝒱.cover c).A01 →+* (𝒲.cover c').A01 := (f.hom.appLE (𝒱.U0 ⊓ 𝒱.U1) (𝒲.U0 ⊓ 𝒲.U1) f.inf_le).hom

theorem ringHom0_apply (x : (𝒱.cover c).A0) : f.ringHom0 x = f.map0 x := rfl
theorem ringHom1_apply (x : (𝒱.cover c).A1) : f.ringHom1 x = f.map1 x := rfl
theorem ringHom01_apply (x : (𝒱.cover c).A01) : f.ringHom01 x = f.map01 x := rfl

theorem ringHom0_comp_algebraMap : f.ringHom0.comp (algebraMap R (𝒱.cover c).A0) = (algebraMap S (𝒲.cover c').A0).comp τ :=
  RingHom.ext fun r => f.appLE_algebraMap f.U0_le r
theorem ringHom1_comp_algebraMap : f.ringHom1.comp (algebraMap R (𝒱.cover c).A1) = (algebraMap S (𝒲.cover c').A1).comp τ :=
  RingHom.ext fun r => f.appLE_algebraMap f.U1_le r
theorem ringHom01_comp_algebraMap :
    f.ringHom01.comp (algebraMap R (𝒱.cover c).A01) = (algebraMap S (𝒲.cover c').A01).comp τ :=
  RingHom.ext fun r => f.appLE_algebraMap f.inf_le r

def kaehlerMap0 : Ω[(𝒱.cover c).A0⁄R] →ₛₗ[τ] Ω[(𝒲.cover c').A0⁄S] :=
  KaehlerDifferential.mapOfRingHom τ f.ringHom0 f.ringHom0_comp_algebraMap

def kaehlerMap1 : Ω[(𝒱.cover c).A1⁄R] →ₛₗ[τ] Ω[(𝒲.cover c').A1⁄S] :=
  KaehlerDifferential.mapOfRingHom τ f.ringHom1 f.ringHom1_comp_algebraMap

def kaehlerMap01 : Ω[(𝒱.cover c).A01⁄R] →ₛₗ[τ] Ω[(𝒲.cover c').A01⁄S] :=
  KaehlerDifferential.mapOfRingHom τ f.ringHom01 f.ringHom01_comp_algebraMap

theorem kaehlerMap0_smul_D (a s : (𝒱.cover c).A0) :
    f.kaehlerMap0 (a • KaehlerDifferential.D R _ s) = f.map0 a • KaehlerDifferential.D S _ (f.map0 s) :=
  KaehlerDifferential.mapOfRingHom_smul_D _ _ f.ringHom0_comp_algebraMap a s
theorem kaehlerMap1_smul_D (a s : (𝒱.cover c).A1) :
    f.kaehlerMap1 (a • KaehlerDifferential.D R _ s) = f.map1 a • KaehlerDifferential.D S _ (f.map1 s) :=
  KaehlerDifferential.mapOfRingHom_smul_D _ _ f.ringHom1_comp_algebraMap a s
theorem kaehlerMap01_smul_D (a s : (𝒱.cover c).A01) :
    f.kaehlerMap01 (a • KaehlerDifferential.D R _ s) = f.map01 a • KaehlerDifferential.D S _ (f.map01 s) :=
  KaehlerDifferential.mapOfRingHom_smul_D _ _ f.ringHom01_comp_algebraMap a s

theorem kaehlerMap01_r0 (ω : Ω[(𝒱.cover c).A0⁄R]) :
    f.kaehlerMap01 ((𝒱.kaehlerSections c).r0 ω) = (𝒲.kaehlerSections c').r0 (f.kaehlerMap0 ω) := by
  have key := KaehlerDifferential.addMonoidHom_ext_smul_D
    (f := f.kaehlerMap01.toAddMonoidHom.comp (𝒱.kaehlerSections c).r0.toAddMonoidHom)
    (g := (𝒲.kaehlerSections c').r0.toAddMonoidHom.comp f.kaehlerMap0.toAddMonoidHom) (fun a s => by
      change f.kaehlerMap01 ((𝒱.kaehlerSections c).r0 (a • KaehlerDifferential.D R _ s)) =
        (𝒲.kaehlerSections c').r0 (f.kaehlerMap0 (a • KaehlerDifferential.D R _ s))
      rw [TwoChartCech.Cover.kaehler_r0_smul_D, kaehlerMap01_smul_D, kaehlerMap0_smul_D,
        TwoChartCech.Cover.kaehler_r0_smul_D, f.map01_ρ0, f.map01_ρ0])
  exact DFunLike.congr_fun key ω

theorem kaehlerMap01_r1 (ω : Ω[(𝒱.cover c).A1⁄R]) :
    f.kaehlerMap01 ((𝒱.kaehlerSections c).r1 ω) = (𝒲.kaehlerSections c').r1 (f.kaehlerMap1 ω) := by
  have key := KaehlerDifferential.addMonoidHom_ext_smul_D
    (f := f.kaehlerMap01.toAddMonoidHom.comp (𝒱.kaehlerSections c).r1.toAddMonoidHom)
    (g := (𝒲.kaehlerSections c').r1.toAddMonoidHom.comp f.kaehlerMap1.toAddMonoidHom) (fun a s => by
      change f.kaehlerMap01 ((𝒱.kaehlerSections c).r1 (a • KaehlerDifferential.D R _ s)) =
        (𝒲.kaehlerSections c').r1 (f.kaehlerMap1 (a • KaehlerDifferential.D R _ s))
      rw [TwoChartCech.Cover.kaehler_r1_smul_D, kaehlerMap01_smul_D, kaehlerMap1_smul_D,
        TwoChartCech.Cover.kaehler_r1_smul_D, f.map01_ρ1, f.map01_ρ1])
  exact DFunLike.congr_fun key ω

theorem kaehlerMap01_cechDiff (s : Ω[(𝒱.cover c).A0⁄R] × Ω[(𝒱.cover c).A1⁄R]) :
    f.kaehlerMap01 ((𝒱.kaehlerSections c).cechDiff s) =
      (𝒲.kaehlerSections c').cechDiff (f.kaehlerMap0 s.1, f.kaehlerMap1 s.2) := by
  rw [TwoChartCech.Sections.cechDiff_apply, TwoChartCech.Sections.cechDiff_apply, map_sub, kaehlerMap01_r0,
    kaehlerMap01_r1]

theorem range_kaehler_cechDiff_le_comap :
    LinearMap.range (𝒱.kaehlerSections c).cechDiff ≤
      (LinearMap.range (𝒲.kaehlerSections c').cechDiff).comap f.kaehlerMap01 := by
  rintro _ ⟨s, rfl⟩
  rw [Submodule.mem_comap, kaehlerMap01_cechDiff]
  exact LinearMap.mem_range_self _ _

theorem kaehlerMap_mem_H0 (x : (𝒱.kaehlerSections c).H0) :
    (f.kaehlerMap0 x.val.1, f.kaehlerMap1 x.val.2) ∈ (𝒲.kaehlerSections c').H0 := by
  rw [LinearMap.mem_ker, ← kaehlerMap01_cechDiff, LinearMap.mem_ker.mp x.2, map_zero]

def kaehlerH0map : (𝒱.kaehlerSections c).H0 →ₛₗ[τ] (𝒲.kaehlerSections c').H0 where
  toFun x := ⟨(f.kaehlerMap0 x.val.1, f.kaehlerMap1 x.val.2), f.kaehlerMap_mem_H0 x⟩
  map_add' x y := by
    apply Subtype.ext
    change (f.kaehlerMap0 (x.val.1 + y.val.1), f.kaehlerMap1 (x.val.2 + y.val.2)) =
      (f.kaehlerMap0 x.val.1 + f.kaehlerMap0 y.val.1, f.kaehlerMap1 x.val.2 + f.kaehlerMap1 y.val.2)
    rw [map_add, map_add]
  map_smul' r x := by
    apply Subtype.ext
    change (f.kaehlerMap0 (r • x.val.1), f.kaehlerMap1 (r • x.val.2)) =
      (τ r • f.kaehlerMap0 x.val.1, τ r • f.kaehlerMap1 x.val.2)
    rw [LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ]

theorem kaehlerH0map_apply_coe (x : (𝒱.kaehlerSections c).H0) :
    (f.kaehlerH0map x).val = (f.kaehlerMap0 x.val.1, f.kaehlerMap1 x.val.2) :=
  rfl

def kaehlerH1map : (𝒱.kaehlerSections c).H1 →ₛₗ[τ] (𝒲.kaehlerSections c').H1 :=
  Submodule.mapQ _ _ f.kaehlerMap01 f.range_kaehler_cechDiff_le_comap

theorem kaehlerH1map_mk (η : Ω[(𝒱.cover c).A01⁄R]) :
    f.kaehlerH1map (Submodule.Quotient.mk η) = Submodule.Quotient.mk (f.kaehlerMap01 η) := rfl

section Functoriality

variable {τ' : R →+* S} {T : Type u} [CommRing T] {υ : S →+* T} {Z : Scheme.{u}} {𝒳 : Z.TwoAffineOpenCover}
  {c'' : Z ⟶ Spec (.of T)}

theorem kaehlerMap0_congr {f : HomOver τ 𝒱 c 𝒲 c'} {g : HomOver τ' 𝒱 c 𝒲 c'} (hfg : f.hom = g.hom)
    (ω : Ω[(𝒱.cover c).A0⁄R]) : f.kaehlerMap0 ω = g.kaehlerMap0 ω := by
  obtain ⟨fh, _, _, _⟩ := f; obtain ⟨gh, _, _, _⟩ := g; cases hfg
  exact KaehlerDifferential.mapOfRingHom_congr rfl _ _ ω
theorem kaehlerMap1_congr {f : HomOver τ 𝒱 c 𝒲 c'} {g : HomOver τ' 𝒱 c 𝒲 c'} (hfg : f.hom = g.hom)
    (ω : Ω[(𝒱.cover c).A1⁄R]) : f.kaehlerMap1 ω = g.kaehlerMap1 ω := by
  obtain ⟨fh, _, _, _⟩ := f; obtain ⟨gh, _, _, _⟩ := g; cases hfg
  exact KaehlerDifferential.mapOfRingHom_congr rfl _ _ ω
theorem kaehlerMap01_congr {f : HomOver τ 𝒱 c 𝒲 c'} {g : HomOver τ' 𝒱 c 𝒲 c'} (hfg : f.hom = g.hom)
    (ω : Ω[(𝒱.cover c).A01⁄R]) : f.kaehlerMap01 ω = g.kaehlerMap01 ω := by
  obtain ⟨fh, _, _, _⟩ := f; obtain ⟨gh, _, _, _⟩ := g; cases hfg
  exact KaehlerDifferential.mapOfRingHom_congr rfl _ _ ω

theorem kaehlerH0map_congr {f : HomOver τ 𝒱 c 𝒲 c'} {g : HomOver τ' 𝒱 c 𝒲 c'} (hfg : f.hom = g.hom)
    (x : (𝒱.kaehlerSections c).H0) : f.kaehlerH0map x = g.kaehlerH0map x :=
  Subtype.ext (Prod.ext (kaehlerMap0_congr hfg _) (kaehlerMap1_congr hfg _))
theorem kaehlerH1map_congr {f : HomOver τ 𝒱 c 𝒲 c'} {g : HomOver τ' 𝒱 c 𝒲 c'} (hfg : f.hom = g.hom)
    (x : (𝒱.kaehlerSections c).H1) : f.kaehlerH1map x = g.kaehlerH1map x := by
  induction x using Submodule.Quotient.induction_on with
  | H η => rw [kaehlerH1map_mk, kaehlerH1map_mk, kaehlerMap01_congr hfg]

theorem id_appLE (U : X.Opens) (h : U ≤ (𝟙 X : X ⟶ X) ⁻¹ᵁ U) : (𝟙 X : X ⟶ X).appLE U U h = 𝟙 _ := by
  change (𝟙 X : X ⟶ X).app _ ≫ X.presheaf.map _ = _
  rw [Scheme.Hom.id_app]
  erw [Category.id_comp]
  exact (congrArg X.presheaf.map (Subsingleton.elim _ _)).trans (X.presheaf.map_id _)

theorem id_ringHom0 : (HomOver.id 𝒱 c).ringHom0 = RingHom.id _ := by
  change ((𝟙 X : X ⟶ X).appLE 𝒱.U0 𝒱.U0 _).hom = _; rw [id_appLE]; rfl
theorem id_ringHom1 : (HomOver.id 𝒱 c).ringHom1 = RingHom.id _ := by
  change ((𝟙 X : X ⟶ X).appLE 𝒱.U1 𝒱.U1 _).hom = _; rw [id_appLE]; rfl
theorem id_ringHom01 : (HomOver.id 𝒱 c).ringHom01 = RingHom.id _ := by
  change ((𝟙 X : X ⟶ X).appLE (𝒱.U0 ⊓ 𝒱.U1) (𝒱.U0 ⊓ 𝒱.U1) _).hom = _; rw [id_appLE]; rfl

theorem id_kaehlerMap0 (ω : Ω[(𝒱.cover c).A0⁄R]) : (HomOver.id 𝒱 c).kaehlerMap0 ω = ω :=
  (KaehlerDifferential.mapOfRingHom_congr id_ringHom0 _ (by ext; rfl) ω).trans
    (KaehlerDifferential.mapOfRingHom_id _ ω)
theorem id_kaehlerMap1 (ω : Ω[(𝒱.cover c).A1⁄R]) : (HomOver.id 𝒱 c).kaehlerMap1 ω = ω :=
  (KaehlerDifferential.mapOfRingHom_congr id_ringHom1 _ (by ext; rfl) ω).trans
    (KaehlerDifferential.mapOfRingHom_id _ ω)
theorem id_kaehlerMap01 (ω : Ω[(𝒱.cover c).A01⁄R]) : (HomOver.id 𝒱 c).kaehlerMap01 ω = ω :=
  (KaehlerDifferential.mapOfRingHom_congr id_ringHom01 _ (by ext; rfl) ω).trans
    (KaehlerDifferential.mapOfRingHom_id _ ω)

theorem id_kaehlerH0map (x : (𝒱.kaehlerSections c).H0) : (HomOver.id 𝒱 c).kaehlerH0map x = x :=
  Subtype.ext (Prod.ext (id_kaehlerMap0 _) (id_kaehlerMap1 _))
theorem id_kaehlerH1map (x : (𝒱.kaehlerSections c).H1) : (HomOver.id 𝒱 c).kaehlerH1map x = x := by
  induction x using Submodule.Quotient.induction_on with
  | H η => rw [kaehlerH1map_mk, id_kaehlerMap01]

theorem comp_ringHom0 (g : HomOver υ 𝒲 c' 𝒳 c'') (f : HomOver τ 𝒱 c 𝒲 c') :
    (g.comp f).ringHom0 = g.ringHom0.comp f.ringHom0 := by
  change ((g.hom ≫ f.hom).appLE 𝒱.U0 𝒳.U0 _).hom = ((f.hom.appLE 𝒱.U0 𝒲.U0 f.U0_le) ≫ (g.hom.appLE 𝒲.U0 𝒳.U0 g.U0_le)).hom
  rw [Scheme.Hom.appLE_comp_appLE]
theorem comp_ringHom1 (g : HomOver υ 𝒲 c' 𝒳 c'') (f : HomOver τ 𝒱 c 𝒲 c') :
    (g.comp f).ringHom1 = g.ringHom1.comp f.ringHom1 := by
  change ((g.hom ≫ f.hom).appLE 𝒱.U1 𝒳.U1 _).hom = ((f.hom.appLE 𝒱.U1 𝒲.U1 f.U1_le) ≫ (g.hom.appLE 𝒲.U1 𝒳.U1 g.U1_le)).hom
  rw [Scheme.Hom.appLE_comp_appLE]
theorem comp_ringHom01 (g : HomOver υ 𝒲 c' 𝒳 c'') (f : HomOver τ 𝒱 c 𝒲 c') :
    (g.comp f).ringHom01 = g.ringHom01.comp f.ringHom01 := by
  change ((g.hom ≫ f.hom).appLE (𝒱.U0 ⊓ 𝒱.U1) (𝒳.U0 ⊓ 𝒳.U1) _).hom =
    ((f.hom.appLE (𝒱.U0 ⊓ 𝒱.U1) (𝒲.U0 ⊓ 𝒲.U1) f.inf_le) ≫ (g.hom.appLE (𝒲.U0 ⊓ 𝒲.U1) (𝒳.U0 ⊓ 𝒳.U1) g.inf_le)).hom
  rw [Scheme.Hom.appLE_comp_appLE]

theorem comp_kaehlerMap0 (g : HomOver υ 𝒲 c' 𝒳 c'') (f : HomOver τ 𝒱 c 𝒲 c') (ω : Ω[(𝒱.cover c).A0⁄R]) :
    (g.comp f).kaehlerMap0 ω = g.kaehlerMap0 (f.kaehlerMap0 ω) :=
  (KaehlerDifferential.mapOfRingHom_congr (comp_ringHom0 g f) _
    (by rw [← comp_ringHom0]; exact (g.comp f).ringHom0_comp_algebraMap) ω).trans
    (KaehlerDifferential.mapOfRingHom_comp_apply _ _ _ _ _ _ _ ω).symm
theorem comp_kaehlerMap1 (g : HomOver υ 𝒲 c' 𝒳 c'') (f : HomOver τ 𝒱 c 𝒲 c') (ω : Ω[(𝒱.cover c).A1⁄R]) :
    (g.comp f).kaehlerMap1 ω = g.kaehlerMap1 (f.kaehlerMap1 ω) :=
  (KaehlerDifferential.mapOfRingHom_congr (comp_ringHom1 g f) _
    (by rw [← comp_ringHom1]; exact (g.comp f).ringHom1_comp_algebraMap) ω).trans
    (KaehlerDifferential.mapOfRingHom_comp_apply _ _ _ _ _ _ _ ω).symm
theorem comp_kaehlerMap01 (g : HomOver υ 𝒲 c' 𝒳 c'') (f : HomOver τ 𝒱 c 𝒲 c') (ω : Ω[(𝒱.cover c).A01⁄R]) :
    (g.comp f).kaehlerMap01 ω = g.kaehlerMap01 (f.kaehlerMap01 ω) :=
  (KaehlerDifferential.mapOfRingHom_congr (comp_ringHom01 g f) _
    (by rw [← comp_ringHom01]; exact (g.comp f).ringHom01_comp_algebraMap) ω).trans
    (KaehlerDifferential.mapOfRingHom_comp_apply _ _ _ _ _ _ _ ω).symm

theorem comp_kaehlerH0map (g : HomOver υ 𝒲 c' 𝒳 c'') (f : HomOver τ 𝒱 c 𝒲 c') (x : (𝒱.kaehlerSections c).H0) :
    (g.comp f).kaehlerH0map x = g.kaehlerH0map (f.kaehlerH0map x) :=
  Subtype.ext (Prod.ext (comp_kaehlerMap0 g f _) (comp_kaehlerMap1 g f _))
theorem comp_kaehlerH1map (g : HomOver υ 𝒲 c' 𝒳 c'') (f : HomOver τ 𝒱 c 𝒲 c') (x : (𝒱.kaehlerSections c).H1) :
    (g.comp f).kaehlerH1map x = g.kaehlerH1map (f.kaehlerH1map x) := by
  induction x using Submodule.Quotient.induction_on with
  | H η => rw [kaehlerH1map_mk, kaehlerH1map_mk, kaehlerH1map_mk, comp_kaehlerMap01]

end Functoriality

end HomOver

section BaseChange

variable (A : Type u) [CommRing A] [Algebra R A] {B : Type u} [CommRing B] [Algebra R B]

abbrev kaehlerH0baseChangeMap :
    (𝒱.kaehlerSections c).H0 →ₛₗ[algebraMap R A]
      ((𝒱.pullback c A).kaehlerSections (pullback.snd c (specMap R A))).H0 :=
  (HomOver.baseChange 𝒱 c A).kaehlerH0map

abbrev kaehlerH1baseChangeMap :
    (𝒱.kaehlerSections c).H1 →ₛₗ[algebraMap R A]
      ((𝒱.pullback c A).kaehlerSections (pullback.snd c (specMap R A))).H1 :=
  (HomOver.baseChange 𝒱 c A).kaehlerH1map

variable {A} in

abbrev kaehlerH0stageMap (g : A →ₐ[R] B) :
    ((𝒱.pullback c A).kaehlerSections (pullback.snd c (specMap R A))).H0 →ₛₗ[g.toRingHom]
      ((𝒱.pullback c B).kaehlerSections (pullback.snd c (specMap R B))).H0 :=
  (HomOver.stage 𝒱 c g).kaehlerH0map

variable {A} in

abbrev kaehlerH1stageMap (g : A →ₐ[R] B) :
    ((𝒱.pullback c A).kaehlerSections (pullback.snd c (specMap R A))).H1 →ₛₗ[g.toRingHom]
      ((𝒱.pullback c B).kaehlerSections (pullback.snd c (specMap R B))).H1 :=
  (HomOver.stage 𝒱 c g).kaehlerH1map

variable {A} {B' : Type u} [CommRing B'] [Algebra R B']

theorem stage_comp_baseChange_hom (g : A →ₐ[R] B) :
    ((HomOver.stage 𝒱 c g).comp (HomOver.baseChange 𝒱 c A)).hom = (HomOver.baseChange 𝒱 c B).hom :=
  baseChangeSnd_fst c (RelPicard.LFP.stageHom R g)

theorem stage_id_hom :
    (HomOver.stage 𝒱 c (AlgHom.id R A)).hom = (HomOver.id (𝒱.pullback c A) (pullback.snd c (specMap R A))).hom := by
  change RelPicard.baseChangeSnd c _ = 𝟙 _
  rw [← RelPicard.baseChangeSnd_id c (specMap R A)]
  congr 1
  apply Subtype.ext
  change Spec.map (CommRingCat.ofHom (RingHom.id A)) = 𝟙 _
  exact Spec.map_id _

theorem stage_comp_stage_hom (g : A →ₐ[R] B) (g' : B →ₐ[R] B') :
    ((HomOver.stage 𝒱 c g').comp (HomOver.stage 𝒱 c g)).hom = (HomOver.stage 𝒱 c (g'.comp g)).hom := by
  change RelPicard.baseChangeSnd c _ ≫ RelPicard.baseChangeSnd c _ = RelPicard.baseChangeSnd c _
  rw [RelPicard.baseChangeSnd_comp]
  congr 1
  apply Subtype.ext
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl

theorem kaehlerH0stageMap_kaehlerH0baseChangeMap (g : A →ₐ[R] B) (x : (𝒱.kaehlerSections c).H0) :
    kaehlerH0stageMap 𝒱 c g (kaehlerH0baseChangeMap 𝒱 c A x) = kaehlerH0baseChangeMap 𝒱 c B x := by
  change (HomOver.stage 𝒱 c g).kaehlerH0map ((HomOver.baseChange 𝒱 c A).kaehlerH0map x) =
    (HomOver.baseChange 𝒱 c B).kaehlerH0map x
  rw [← HomOver.comp_kaehlerH0map]
  exact HomOver.kaehlerH0map_congr (stage_comp_baseChange_hom 𝒱 c g) x
theorem kaehlerH1stageMap_kaehlerH1baseChangeMap (g : A →ₐ[R] B) (x : (𝒱.kaehlerSections c).H1) :
    kaehlerH1stageMap 𝒱 c g (kaehlerH1baseChangeMap 𝒱 c A x) = kaehlerH1baseChangeMap 𝒱 c B x := by
  change (HomOver.stage 𝒱 c g).kaehlerH1map ((HomOver.baseChange 𝒱 c A).kaehlerH1map x) =
    (HomOver.baseChange 𝒱 c B).kaehlerH1map x
  rw [← HomOver.comp_kaehlerH1map]
  exact HomOver.kaehlerH1map_congr (stage_comp_baseChange_hom 𝒱 c g) x

theorem kaehlerH0stageMap_id (x : ((𝒱.pullback c A).kaehlerSections (pullback.snd c (specMap R A))).H0) :
    kaehlerH0stageMap 𝒱 c (AlgHom.id R A) x = x :=
  (HomOver.kaehlerH0map_congr (stage_id_hom 𝒱 c) x).trans (HomOver.id_kaehlerH0map x)
theorem kaehlerH1stageMap_id (x : ((𝒱.pullback c A).kaehlerSections (pullback.snd c (specMap R A))).H1) :
    kaehlerH1stageMap 𝒱 c (AlgHom.id R A) x = x :=
  (HomOver.kaehlerH1map_congr (stage_id_hom 𝒱 c) x).trans (HomOver.id_kaehlerH1map x)

theorem kaehlerH0stageMap_comp (g : A →ₐ[R] B) (g' : B →ₐ[R] B')
    (x : ((𝒱.pullback c A).kaehlerSections (pullback.snd c (specMap R A))).H0) :
    kaehlerH0stageMap 𝒱 c g' (kaehlerH0stageMap 𝒱 c g x) = kaehlerH0stageMap 𝒱 c (g'.comp g) x := by
  change (HomOver.stage 𝒱 c g').kaehlerH0map ((HomOver.stage 𝒱 c g).kaehlerH0map x) =
    (HomOver.stage 𝒱 c (g'.comp g)).kaehlerH0map x
  rw [← HomOver.comp_kaehlerH0map]
  exact HomOver.kaehlerH0map_congr (stage_comp_stage_hom 𝒱 c g g') x
theorem kaehlerH1stageMap_comp (g : A →ₐ[R] B) (g' : B →ₐ[R] B')
    (x : ((𝒱.pullback c A).kaehlerSections (pullback.snd c (specMap R A))).H1) :
    kaehlerH1stageMap 𝒱 c g' (kaehlerH1stageMap 𝒱 c g x) = kaehlerH1stageMap 𝒱 c (g'.comp g) x := by
  change (HomOver.stage 𝒱 c g').kaehlerH1map ((HomOver.stage 𝒱 c g).kaehlerH1map x) =
    (HomOver.stage 𝒱 c (g'.comp g)).kaehlerH1map x
  rw [← HomOver.comp_kaehlerH1map]
  exact HomOver.kaehlerH1map_congr (stage_comp_stage_hom 𝒱 c g g') x

end BaseChange

end AlgebraicGeometry.Scheme.TwoAffineOpenCover

end


