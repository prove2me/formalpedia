-- Prove2me | Definitions.Def_AlgebraicGeometry_RelPicardAbelJacobiFamily
-- name    : AlgebraicGeometry_RelPicardAbelJacobiFamily
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/db2e215d-8370-5f86-97d7-08df8b17a1fb
-- title:
--   Abel–Jacobi family of line bundles on a pointed curve
-- statement:
--   Throughout, $k$ is a field and $a\colon A\to\operatorname{Spec} k$ a $k$-scheme; sections are elements of `SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a`, i.e. morphisms $\operatorname{Spec} k\to A$ over $k$, and $A.\mathrm{Modules}$ carries the symmetric monoidal structure with unit the structure sheaf. `toProdSpec a` is the morphism $A\to A\times_{\operatorname{Spec} k}\operatorname{Spec} k$ with components $\mathrm{id}_A$ and $a$; the two lemmas following it state that its composites with the first projection are the identities in both orders, and `fstPullbackToProdSpecPullbackIso`, `toProdSpecPullbackFstPullbackIso` are the resulting natural isomorphisms between the iterated pullback functors and the identity.
--
--   For a separated $a$ and sections $t,\varepsilon$, `pointSubBasepointModule t ε` is, on $A\times_k\operatorname{Spec} k$, the tensor product of the dual of the ideal sheaf of the graph of $t$ with the ideal sheaf of the graph of $\varepsilon$ — each graph being the degree-one relative effective divisor `RelEffCartierDiv.ofPoint`, whose `lineBundle` and `idealModule` are $\mathcal O(\cdot)$ and $\mathcal O(-\cdot)$ in the sense of the ideal-sheaf module construction; so this is $\mathcal O(t)\otimes\mathcal O(-\varepsilon)$. `pointsSubBasepointModule ε` extends this to a finite list of sections by recursion, the empty list giving the unit.
--
--   On $A\times_k A$ (first factor the curve, second the parameter), `diagDiv` and `constDiv ε` are the degree-one relative effective divisors over the second factor cut out by the identity $\mathrm{id}_A$ and by the constant morphism $a\circ\varepsilon$, and `ajFamily ε` is $\mathcal O(\Delta)\otimes\mathcal O(-(A\times\varepsilon))$. `isInvertible_ajFamily` asserts that this is an invertible module (locally isomorphic to the structure sheaf) when $a$ is smooth of relative dimension $1$, citing invertibility of the ideal sheaf of a relative effective divisor and stability of invertibility under dual and tensor.
--
--   Auxiliary statements: the unit module satisfies `IsAlgEquivZero a`, with witness $T'=\operatorname{Spec} k$, identity structure morphism and unit module; `IsAlgEquivZero.of_fst_pullback_iso` reduces `IsAlgEquivZero a L` to the same property for $\mathtt{toProdSpec}^{*}N$, for any $N$ isomorphic to the pullback of $L$ along the first projection; `RelEffCartierDiv.ofPoint_congr` transports `ofPoint` along an equality of sections; `baseChangeSnd_eq_mapOnProdOver` identifies the base-change morphism of the relative Picard presheaf with the corresponding map on products; and for an invertible ideal sheaf datum $I$ (locally generated on affine basic opens by a non-zero-divisor) there is an isomorphism $I^{\vee}\otimes I\cong\mathcal O$.
--
--   **Relation to Mathlib.** Mathlib supplies `Scheme.IdealSheafData`, sheaves of modules and pullback functors; the monoidal structure on `X.Modules`, the invertibility predicates for modules and for ideal sheaf data, relative effective divisors with their $\mathcal O(\pm D)$, and the predicate `IsAlgEquivZero` of algebraic equivalence to zero are the project's own notions.
--
--   **Where it is used.** These objects implement the Abel–Jacobi witness that $\mathcal O(P-\varepsilon)$ on a pointed curve is algebraically equivalent to zero: the fibre of `ajFamily ε` over a point $t$ is $\mathcal O(t)\otimes\mathcal O(-\varepsilon)$, trivial at $t=\varepsilon$. They feed the construction of the relative Picard functor cut out by fibrewise algebraic equivalence to zero, hence the Jacobian of a modular curve used in the Galois-representation input to the modularity argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_RelPicardAbelJacobiFamily.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicCurve_RelCartier
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard
  NeronModelInfra GoodReductionJacobian

noncomputable section

namespace AlgebraicGeometry.RelPicard

variable {k : Type u} [Field k] {A : Scheme.{u}} (a : A ⟶ Spec (CommRingCat.of k))

def toProdSpec : A ⟶ Limits.pullback a (𝟙 (Spec (CommRingCat.of k))) :=
  pullback.lift (𝟙 A) a (by simp)

@[reassoc (attr := simp)]
theorem toProdSpec_fst : toProdSpec a ≫ pullback.fst a (𝟙 _) = 𝟙 A := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem fst_toProdSpec : pullback.fst a (𝟙 _) ≫ toProdSpec a = 𝟙 _ := by
  apply pullback.hom_ext
  · simp only [toProdSpec, Category.assoc, pullback.lift_fst, Category.comp_id, Category.id_comp]
  · simp only [toProdSpec, Category.assoc, pullback.lift_snd, Category.id_comp]
    rw [pullback.condition, Category.comp_id]

def fstPullbackToProdSpecPullbackIso (N : (Limits.pullback a (𝟙 (Spec (CommRingCat.of k)))).Modules) :
    (Scheme.Modules.pullback (pullback.fst a (𝟙 _))).obj ((Scheme.Modules.pullback (toProdSpec a)).obj N) ≅ N :=
  (Scheme.Modules.pullbackComp _ _).app N ≪≫ (Scheme.Modules.pullbackCongr (fst_toProdSpec a)).app N ≪≫
    (Scheme.Modules.pullbackId _).app N

def toProdSpecPullbackFstPullbackIso (L : A.Modules) :
    (Scheme.Modules.pullback (toProdSpec a)).obj ((Scheme.Modules.pullback (pullback.fst a (𝟙 _))).obj L) ≅ L :=
  (Scheme.Modules.pullbackComp _ _).app L ≪≫ (Scheme.Modules.pullbackCongr (toProdSpec_fst a)).app L ≪≫
    (Scheme.Modules.pullbackId _).app L

variable {a}

theorem baseChangeSnd_eq_mapOnProdOver {T' : Scheme.{u}} {h : T' ⟶ Spec (CommRingCat.of k)}
    (t : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) h) : baseChangeSnd a t = mapOnProdOver a t.1 t.2 := rfl

theorem IsAlgEquivZero.tensorUnit (a : A ⟶ Spec (CommRingCat.of k)) : IsAlgEquivZero a (𝟙_ A.Modules) := by
  refine ⟨Spec (CommRingCat.of k), 𝟙 _, inferInstance, geometricallyIntegral_id_Spec k,
    SheafOfModules.unit (Limits.pullback a (𝟙 (Spec (CommRingCat.of k)))).ringCatSheaf, Scheme.Modules.isInvertible_unit _,
    ⟨𝟙 _, Category.comp_id _⟩, ⟨𝟙 _, Category.comp_id _⟩,
    ⟨Scheme.Modules.pullbackUnitIso _⟩, ⟨?_⟩⟩
  exact Scheme.Modules.pullbackUnitIso _ ≪≫ (Scheme.Modules.pullbackTensorUnitObjIso _).symm

theorem IsAlgEquivZero.of_fst_pullback_iso {L : A.Modules}
    {N : (Limits.pullback a (𝟙 (Spec (CommRingCat.of k)))).Modules}
    (e : (Scheme.Modules.pullback (pullback.fst a (𝟙 _))).obj L ≅ N)
    (hN : IsAlgEquivZero a ((Scheme.Modules.pullback (toProdSpec a)).obj N)) : IsAlgEquivZero a L :=
  IsAlgEquivZero.of_iso ((Scheme.Modules.pullback (toProdSpec a)).mapIso e.symm ≪≫ toProdSpecPullbackFstPullbackIso a L) hN

theorem RelEffCartierDiv.ofPoint_congr {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) [IsSeparated f] {T : Scheme.{u}}
    {g : T ⟶ S} {x y : T ⟶ 𝒞} (h : x = y) (hx : x ≫ f = g) (hy : y ≫ f = g) :
    RelEffCartierDiv.ofPoint f x hx = RelEffCartierDiv.ofPoint f y hy := by
  subst h; rfl

theorem Scheme.IdealSheafData.IsInvertible.nonempty_invModule_tensor_module_iso {X : Scheme.{u}}
    {I : X.IdealSheafData} (hI : I.IsInvertible) : Nonempty (I.invModule ⊗ I.module ≅ 𝟙_ X.Modules) :=
  ⟨β_ _ _ ≪≫ (hI.isInvertible_module.dual).2.some⟩

section
variable [IsSeparated a]

abbrev pointSubBasepointModule (t ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a) :
    (Limits.pullback a (𝟙 (Spec (CommRingCat.of k)))).Modules :=
  (RelEffCartierDiv.ofPoint a t.1 t.2).lineBundle ⊗ (RelEffCartierDiv.ofPoint a ε.1 ε.2).idealModule

def pointsSubBasepointModule (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a) :
    List (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a) → (Limits.pullback a (𝟙 (Spec (CommRingCat.of k)))).Modules
  | [] => 𝟙_ _
  | P :: Ps => pointSubBasepointModule (a := a) P ε ⊗ pointsSubBasepointModule ε Ps

@[simp] theorem pointsSubBasepointModule_nil (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a) :
    pointsSubBasepointModule (a := a) ε [] = 𝟙_ _ := rfl

@[simp] theorem pointsSubBasepointModule_cons (ε P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a)
    (Ps : List (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a)) :
    pointsSubBasepointModule (a := a) ε (P :: Ps) = pointSubBasepointModule (a := a) P ε ⊗ pointsSubBasepointModule ε Ps :=
  rfl

abbrev diagDiv : RelEffCartierDiv a 1 a := RelEffCartierDiv.ofPoint a (𝟙 A) (Category.id_comp a)

omit [IsSeparated a] in
theorem comp_point_comp (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a) : (a ≫ ε.1) ≫ a = a := by
  rw [Category.assoc, ε.2, Category.comp_id]

abbrev constDiv (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a) : RelEffCartierDiv a 1 a :=
  RelEffCartierDiv.ofPoint a (a ≫ ε.1) (comp_point_comp ε)

def ajFamily (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a) : (Limits.pullback a a).Modules :=
  (diagDiv (a := a)).lineBundle ⊗ (constDiv (a := a) ε).idealModule

theorem isInvertible_ajFamily [SmoothOfRelativeDimension 1 a] (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a) :
    Scheme.Modules.IsInvertible (ajFamily (a := a) ε) :=
  (RelEffCartierDiv.isInvertible_I _).isInvertible_invModule.tensor (RelEffCartierDiv.isInvertible_I _).isInvertible_module

end

end AlgebraicGeometry.RelPicard

end


