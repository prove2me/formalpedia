-- Prove2me | Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
-- name    : AlgebraicGeometry_RelPicardAlgEquivZeroCut
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/b2dc7349-d100-53e8-b445-5a19e3433bd3
-- title:
--   The algebraic-equivalence-to-zero cut on the relative Picard functor
-- statement:
--   Over a commutative ring $R$, fix $c \colon C \to \operatorname{Spec} R$ and a section $\varepsilon$ of $c$ (an element of `SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c`, i.e. a morphism $\operatorname{Spec} R \to C$ composing with $c$ to the identity). For $t \colon T \to \operatorname{Spec} R$ and a $k$-point $s \colon \operatorname{Spec} k \to T$ of $T$, `fibreAt c t s` is the second projection of the fibre product of $\operatorname{pr}_2 \colon C \times_R T \to T$ with $s$, that is the fibre of $C \times_R T$ at $s$ viewed as a $k$-scheme. For a $k$-scheme $a \colon A \to \operatorname{Spec} k$ and a sheaf of modules $L$ on $A$, `IsAlgEquivZero a L` asserts the existence of a $k$-scheme $h \colon T' \to \operatorname{Spec} k$ that is locally of finite type and geometrically integral, of a sheaf of modules $M$ on $A \times_k T'$ satisfying `Scheme.Modules.IsInvertible` (every point has an open neighbourhood on which the restriction of $M$ is isomorphic to the unit module), and of two sections $t_0, t_1$ of $h$ over $\operatorname{Spec} k$, such that the pullback of $M$ along the induced map $A \times_k \operatorname{Spec} k \to A \times_k T'$ determined by $t_0$ is isomorphic to the unit module, while the pullback determined by $t_1$ is isomorphic to the pullback of $L$ along the first projection. Both comparisons take place on the fibre product of $a$ with the identity of $\operatorname{Spec} k$ rather than on $A$ itself, and both are existence of an isomorphism (`Nonempty`), not a chosen one. For a rigidified line bundle $M$ on $C \times_R T$, `FibrewiseAlgEquivZero M` asserts that for every algebraically closed field $k$ and every $s \colon \operatorname{Spec} k \to T$, the restriction of $M.L$ to the fibre `fibreAt c t s` satisfies `IsAlgEquivZero`. Finally `algEquivZeroCut c ε` is the `SubPicCondition c ε` whose predicate is `FibrewiseAlgEquivZero`; its three structure fields — membership of the unit bundle, invariance under isomorphism of the underlying module, and stability under pullback along a morphism of $R$-schemes — are supplied by the lemmas `fibrewiseAlgEquivZero_unit`, `FibrewiseAlgEquivZero.congr` and `FibrewiseAlgEquivZero.pullback`, the last two resting on the corresponding statements `IsAlgEquivZero.of_iso` and `IsAlgEquivZero.pullback` for a single fibre. The auxiliary `geometricallyIntegral_id_Spec` records that the identity of $\operatorname{Spec} k$ is geometrically integral, which furnishes the witness $T' = \operatorname{Spec} k$ in the unit case.
--
--   **Relation to Mathlib.** Mathlib has no notion of algebraic equivalence of line bundles or of $\mathrm{Pic}^0$; the predicates here are the project's own, built from Mathlib's sheaves of modules (`SheafOfModules.unit` and pullback), `LocallyOfFiniteType` and `GeometricallyIntegral`, together with the project's `Scheme.Modules.IsInvertible`, `RigidifiedLineBundle` and `SubPicCondition`.
--
--   **Where it is used.** A `SubPicCondition` is the datum used to cut a subfunctor out of the rigidified relative Picard presheaf, and `RepresentsRelSubPic` asks for a scheme with a Poincaré bundle representing that subfunctor. This particular cut is the $\mathrm{Pic}^0$ condition, by which Jacobians of the modular curves occurring in the argument are singled out as relative Picard schemes with good reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace AlgebraicGeometry.RelPicard

open CategoryTheory CategoryTheory.Limits NeronModelInfra

universe u

variable {R : Type u} [CommRing R]

noncomputable def fibreAt {C T : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) (t : T ⟶ Spec (CommRingCat.of R))
    {k : Type u} [Field k] (s : Spec (CommRingCat.of k) ⟶ T) :
    pullback (pullback.snd c t) s ⟶ Spec (CommRingCat.of k) :=
  pullback.snd _ _

def IsAlgEquivZero {k : Type u} [Field k] {A : Scheme.{u}} (a : A ⟶ Spec (CommRingCat.of k)) (L : A.Modules) : Prop :=
  ∃ (T' : Scheme.{u}) (h : T' ⟶ Spec (CommRingCat.of k)) (_ : LocallyOfFiniteType h) (_ : GeometricallyIntegral h)
    (M : (pullback a h).Modules) (_ : Scheme.Modules.IsInvertible M)
    (t₀ t₁ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) h),
    Nonempty ((Scheme.Modules.pullback (baseChangeSnd a t₀)).obj M ≅
        SheafOfModules.unit (pullback a (𝟙 (Spec (CommRingCat.of k)))).ringCatSheaf) ∧
    Nonempty ((Scheme.Modules.pullback (baseChangeSnd a t₁)).obj M ≅
        (Scheme.Modules.pullback (pullback.fst a (𝟙 (Spec (CommRingCat.of k))))).obj L)

variable {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)} {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}

def FibrewiseAlgEquivZero {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (M : RigidifiedLineBundle c ε t) : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ T),
    IsAlgEquivZero (fibreAt c t s) ((Scheme.Modules.pullback (pullback.fst (pullback.snd c t) s)).obj M.L)

theorem IsAlgEquivZero.of_iso {k : Type u} [Field k] {A : Scheme.{u}} {a : A ⟶ Spec (CommRingCat.of k)}
    {L L' : A.Modules} (e : L ≅ L') (hL : IsAlgEquivZero a L) : IsAlgEquivZero a L' := by
  obtain ⟨T', h, hft, hgi, M, hM, t₀, t₁, e₀, ⟨e₁⟩⟩ := hL
  exact ⟨T', h, hft, hgi, M, hM, t₀, t₁, e₀, ⟨e₁ ≪≫ (Scheme.Modules.pullback _).mapIso e⟩⟩

theorem IsAlgEquivZero.pullback {k : Type u} [Field k] {A A' : Scheme.{u}} {a : A ⟶ Spec (CommRingCat.of k)}
    {a' : A' ⟶ Spec (CommRingCat.of k)} (e : A' ⟶ A) (he : e ≫ a = a') {L : A.Modules}
    (hL : IsAlgEquivZero a L) : IsAlgEquivZero a' ((Scheme.Modules.pullback e).obj L) := by
  obtain ⟨T', h, hft, hgi, M, hM, t₀, t₁, ⟨e₀⟩, ⟨e₁⟩⟩ := hL

  let eT : Limits.pullback a' h ⟶ Limits.pullback a h :=
    pullback.map a' h a h e (𝟙 T') (𝟙 _) (by rw [Category.comp_id, he]) (by simp)
  let e1 : Limits.pullback a' (𝟙 (Spec (CommRingCat.of k))) ⟶ Limits.pullback a (𝟙 (Spec (CommRingCat.of k))) :=
    pullback.map a' (𝟙 _) a (𝟙 _) e (𝟙 _) (𝟙 _) (by rw [Category.comp_id, he]) (by simp)
  have hsq : ∀ tt : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) h,
      baseChangeSnd a' tt ≫ eT = e1 ≫ baseChangeSnd a tt := by
    intro tt
    apply pullback.hom_ext <;>
      simp only [eT, e1, baseChangeSnd, Category.assoc, pullback.lift_fst, pullback.lift_snd,
        pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id]
  have hfst : e1 ≫ pullback.fst a (𝟙 _) = pullback.fst a' (𝟙 _) ≫ e := by
    simp only [e1, pullback.lift_fst]
  refine ⟨T', h, hft, hgi, (Scheme.Modules.pullback eT).obj M, hM.pullback eT, t₀, t₁, ⟨?_⟩, ⟨?_⟩⟩
  · exact (Scheme.Modules.pullbackComp _ _).app M ≪≫
      (Scheme.Modules.pullbackCongr (hsq t₀)).app M ≪≫
      ((Scheme.Modules.pullbackComp _ _).app M).symm ≪≫
      (Scheme.Modules.pullback e1).mapIso e₀ ≪≫
      Scheme.Modules.pullbackUnitIso e1
  · exact (Scheme.Modules.pullbackComp _ _).app M ≪≫
      (Scheme.Modules.pullbackCongr (hsq t₁)).app M ≪≫
      ((Scheme.Modules.pullbackComp _ _).app M).symm ≪≫
      (Scheme.Modules.pullback e1).mapIso e₁ ≪≫
      (Scheme.Modules.pullbackComp _ _).app L ≪≫
      (Scheme.Modules.pullbackCongr hfst).app L ≪≫
      ((Scheme.Modules.pullbackComp _ _).app L).symm

theorem geometricallyIntegral_id_Spec (k : Type u) [Field k] :
    GeometricallyIntegral (𝟙 (Spec (CommRingCat.of k))) := by
  constructor
  intro K _ y Z fst snd hP
  haveI : IsIso snd := hP.isIso_snd_of_isIso
  exact AlgebraicGeometry.IsIntegral.of_isIso (inv snd)

theorem fibrewiseAlgEquivZero_unit {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    FibrewiseAlgEquivZero (RigidifiedLineBundle.unit (c := c) (ε := ε) t) := by
  intro k _ _ s
  refine ⟨Spec (CommRingCat.of k), 𝟙 _, inferInstance, geometricallyIntegral_id_Spec k,
    SheafOfModules.unit (Limits.pullback (fibreAt c t s) (𝟙 (Spec (CommRingCat.of k)))).ringCatSheaf,
    Scheme.Modules.isInvertible_unit _, ⟨𝟙 _, Category.comp_id _⟩, ⟨𝟙 _, Category.comp_id _⟩,
    ⟨Scheme.Modules.pullbackUnitIso _⟩, ⟨?_⟩⟩
  exact Scheme.Modules.pullbackUnitIso _ ≪≫ (Scheme.Modules.pullbackUnitIso _).symm ≪≫
    (Scheme.Modules.pullback _).mapIso (Scheme.Modules.pullbackUnitIso _).symm

theorem FibrewiseAlgEquivZero.congr {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {M M' : RigidifiedLineBundle c ε t} (h : Nonempty (M.L ≅ M'.L)) (hM : FibrewiseAlgEquivZero M) :
    FibrewiseAlgEquivZero M' := by
  intro k _ _ s
  exact (hM k s).of_iso ((Scheme.Modules.pullback _).mapIso h.some)

theorem FibrewiseAlgEquivZero.pullback {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : SchemeHomOver t' t) {M : RigidifiedLineBundle c ε t}
    (hM : FibrewiseAlgEquivZero M) : FibrewiseAlgEquivZero (M.pullbackAlong ψ) := by
  intro k _ _ s'
  have hψ : pullback.snd c t' ≫ ψ.1 = baseChangeSnd c ψ ≫ pullback.snd c t := by
    simp only [baseChangeSnd, pullback.lift_snd]

  let e : Limits.pullback (pullback.snd c t') s' ⟶ Limits.pullback (pullback.snd c t) (s' ≫ ψ.1) :=
    pullback.map _ _ _ _ (baseChangeSnd c ψ) (𝟙 _) ψ.1 hψ (by simp)
  have he : e ≫ fibreAt c t (s' ≫ ψ.1) = fibreAt c t' s' := by
    simp only [e, fibreAt, pullback.lift_snd, Category.comp_id]
  have hfst : e ≫ pullback.fst (pullback.snd c t) (s' ≫ ψ.1) =
      pullback.fst (pullback.snd c t') s' ≫ baseChangeSnd c ψ := by
    simp only [e, pullback.lift_fst]
  refine IsAlgEquivZero.of_iso ?_ ((hM k (s' ≫ ψ.1)).pullback e he)
  exact (Scheme.Modules.pullbackComp _ _).app M.L ≪≫
    (Scheme.Modules.pullbackCongr hfst).app M.L ≪≫
    ((Scheme.Modules.pullbackComp _ _).app M.L).symm

noncomputable def algEquivZeroCut (c : C ⟶ Spec (CommRingCat.of R)) (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) :
    SubPicCondition c ε where
  P := fun _ M => FibrewiseAlgEquivZero M
  unit_mem := fun t => fibrewiseAlgEquivZero_unit t
  congr := fun _ _ _ h hM => hM.congr h
  pullback_mem := fun _ _ ψ _ hM => hM.pullback ψ

end AlgebraicGeometry.RelPicard


