-- Prove2me | Definitions.Def_ProEtale_Comparator_Systems
-- name    : ProEtale_Comparator_Systems
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T12:06:50.843967+00:00
-- url     : https://prove2.me/theorems/4b3ba400-1c9c-4448-9d30-49556a6649bd
-- title:
--   Étale-to-pro-étale comparison II: cohomology systems with $\mathbb{Z}/\ell^n$-coefficients and the reduction map
-- statement:
--   For a scheme $X$ and a natural number $\ell$, this file defines the inverse systems of cohomology groups that appear in the $\ell$-adic comparison.
--
--   1. The constant sheaves $\mathbb Z$ on $X_{\text{ét}}$ and on $X_{\text{proét}}$ (`etaleConstantInt`, `proetaleConstantInt`), out of which $\operatorname{Ext}$ groups compute cohomology.
--   2. The inverse system $n \mapsto \mathbb Z/\ell^n$ of abelian groups with the reduction maps (`zmodAbSystem`), and the inverse system $n \mapsto H^m(X_{\text{ét}}, \mathbb Z/\ell^n)$ of étale cohomology groups of the constant sheaves (`etaleCohomologySystem`).
--   3. For a topological abelian group $M$, the sheaf $U \mapsto \operatorname{Map}_{\mathrm{cont}}(U, M)$ on $X_{\text{proét}}$ (`topologicalSheaf`), its functoriality in $M$, and its variants lifted to a larger universe.
--   4. The inverse system of sheaves $U \mapsto \operatorname{Map}_{\mathrm{cont}}(U, \mathbb Z/\ell^n)$ (`zmodContinuousSystem`) and the system $n \mapsto H^m(X_{\text{proét}}, \mathbb Z/\ell^n)$ of their cohomology groups (`proetaleCohomologySystem`).
--   5. For $\ell$ prime, the canonical map $\rho : H^m(X_{\text{proét}}, \mathbb Z_\ell) \to \varprojlim_n H^m(X_{\text{proét}}, \mathbb Z/\ell^n)$ induced by the reductions $\mathbb Z_\ell \to \mathbb Z/\ell^n$ (`ellAdicCohomologyToLimit`).
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014), Lemma 4.2.12 (sheaves of continuous functions), Section 6.8. Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Comparator/Definitions.lean (declarations kept unchanged, unused ones removed; part 2 of 3 of that file, which is split to keep compilation short).

/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib
import Definitions.Def_ProEtale_Comparator_Sites

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false

universe u v w

open CategoryTheory Limits Opposite Abelian AlgebraicGeometry AlgebraicGeometry.Scheme
  MorphismProperty

variable (X : Scheme.{u})

open AlgebraicGeometry.Scheme ProEt

namespace EllAdicEtaleComparison

/-! ### Terminal objects and constant sheaf units -/

/-- The constant abelian sheaf `ℤ` on the small étale site (the unit for sheaf
cohomology, see `CategoryTheory.Sheaf.H`). -/
noncomputable abbrev etaleConstantInt : Sheaf X.smallEtaleTopology Ab.{u + 1} :=
  (constantSheaf X.smallEtaleTopology Ab.{u + 1}).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ))

/-- The constant abelian sheaf `ℤ` on the pro-étale site. -/
noncomputable abbrev proetaleConstantInt : Sheaf (ProEt.topology X) Ab.{u + 1} :=
  (constantSheaf (ProEt.topology X) Ab.{u + 1}).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ))

/-! ### The étale side: the system of constant sheaves `ℤ/ℓⁿℤ` -/

/-- The inverse system `n ↦ ULift ℤ/ℓⁿℤ` of abelian groups, with the reduction maps as
transition maps. -/
noncomputable def zmodAbSystem (ℓ : ℕ) : ℕᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  (Functor.ofSequence
    (X := fun n ↦ op (AddCommGrpCat.of (ULift.{u + 1} (ZMod (ℓ ^ n)))))
    (fun n ↦ (AddCommGrpCat.uliftFunctor.{u + 1}.map (AddCommGrpCat.ofHom
      (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n))).toAddMonoidHom)).op)).leftOp

/-- The transition maps of `zmodAbSystem` are the (`ULift`ed) reduction maps. -/
lemma zmodAbSystem_map_succ (ℓ n : ℕ) :
    (zmodAbSystem.{u} ℓ).map (homOfLE (Nat.le_succ n)).op =
      AddCommGrpCat.uliftFunctor.{u + 1}.map (AddCommGrpCat.ofHom
        (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n))).toAddMonoidHom) :=
  congrArg Quiver.Hom.unop
    (Functor.ofSequence_map_homOfLE_succ
      (X := fun n ↦ op (AddCommGrpCat.of (ULift.{u + 1} (ZMod (ℓ ^ n)))))
      (f := fun n ↦ (AddCommGrpCat.uliftFunctor.{u + 1}.map (AddCommGrpCat.ofHom
        (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n))).toAddMonoidHom)).op)
      n)

/-- The inverse system `n ↦ Hᵐ(X_ét, ℤ/ℓⁿℤ)` of étale cohomology groups of the constant
sheaves `ℤ/ℓⁿℤ` on the small étale site of `X`, with transition maps induced by the
reduction maps. Its value at `n` is
`AddCommGrpCat.of (Sheaf.H ((constantSheaf X.smallEtaleTopology Ab).obj
  (AddCommGrpCat.of (ULift (ZMod (ℓ ^ n))))) m)`. -/
noncomputable def etaleCohomologySystem (ℓ : ℕ) (m : ℕ) :
    ℕᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  (zmodAbSystem ℓ ⋙ constantSheaf X.smallEtaleTopology Ab.{u + 1}) ⋙
    extFunctorObj (etaleConstantInt X) m


/-! ### The pro-étale side: the system of sheaves of continuous `ℤ/ℓⁿℤ`-valued functions

In analogy with mathlib's `ellAdicSheaf` (`U ↦ C(U, ℤ_[ℓ])`), we consider the sheaves
`U ↦ C(U, ℤ/ℓⁿℤ)` on the pro-étale site of `X`. Since `ℤ/ℓⁿℤ` is discrete, these are
the sheaves of locally constant `ℤ/ℓⁿℤ`-valued functions; their cohomology is the
pro-étale cohomology of `X` with `ℤ/ℓⁿℤ`-coefficients.
-/

section Topological

variable (M : Type v) [TopologicalSpace M] [AddCommGroup M] [IsTopologicalAddGroup M]

/-- The sheaf `U ↦ C(U, M)` on the pro-étale site of `X`, for a topological abelian
group `M`. For `M = ℤ_[ℓ]` this is `X.ellAdicSheaf ℓ` (definitionally). -/
noncomputable def topologicalSheaf : Sheaf (ProEt.topology X) Ab.{max u v} :=
  ((ProEt.forget X ⋙ Over.forget _).sheafPushforwardContinuous _ _ proetaleTopology).obj
    ⟨continuousMapPresheafAb.{v} M, .of_le proetaleTopology_le_fpqcTopology <|
      isSheaf_fpqcTopology_continuousMapPresheafAb _⟩


/-- Postcomposition with a continuous additive map, as a morphism of the sheaves of
continuous maps. -/
noncomputable def topologicalSheafMap {M' : Type v} [TopologicalSpace M']
    [AddCommGroup M'] [IsTopologicalAddGroup M'] (f : M →+ M') (hf : Continuous f) :
    topologicalSheaf X M ⟶ topologicalSheaf X M' where
  hom :=
    { app := fun U ↦ AddCommGrpCat.ofHom
        (AddMonoidHom.mk' (fun g ↦ (ContinuousMap.mk f hf).comp g)
          (fun g₁ g₂ ↦ by ext x; exact map_add f _ _))
      naturality := by
        intro U V h
        apply ConcreteCategory.hom_ext
        intro g
        rfl }

/-- Functoriality of `topologicalSheafMap` in the coefficient map. -/
lemma topologicalSheafMap_comp
    {M₂ M₃ : Type v} [TopologicalSpace M₂] [AddCommGroup M₂] [IsTopologicalAddGroup M₂]
    [TopologicalSpace M₃] [AddCommGroup M₃] [IsTopologicalAddGroup M₃]
    (f : M →+ M₂) (hf : Continuous f) (g : M₂ →+ M₃) (hg : Continuous g) :
    topologicalSheafMap X M f hf ≫ topologicalSheafMap X M₂ g hg =
      topologicalSheafMap X M (g.comp f) (hg.comp hf) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- The sheaf `U ↦ C(U, M)` on the pro-étale site of `X`, as a functor in the coefficient
topological abelian group `M`. On objects it is `topologicalSheaf`, on morphisms
`topologicalSheafMap`. -/
noncomputable def topologicalSheafFunctor :
    TopModuleCat.{v} ℤ ⥤ Sheaf (ProEt.topology X) Ab.{max u v} where
  obj N := topologicalSheaf X N
  map f := topologicalSheafMap X _ f.hom.toLinearMap.toAddMonoidHom f.hom.continuous
  map_id N := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    apply ConcreteCategory.hom_ext
    intro x
    rfl
  map_comp f g := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    apply ConcreteCategory.hom_ext
    intro x
    rfl

variable {C : Type*} [Category C] {J : GrothendieckTopology C}

/-- Universe lifting on sheaves of abelian groups: `Sheaf J Ab.{u} ⥤ Sheaf J Ab.{u + 1}`,
obtained by postcomposition with `AddCommGrpCat.uliftFunctor`. -/
noncomputable def _root_.Sheaf.uliftFunctor : Sheaf J Ab.{u} ⥤ Sheaf J Ab.{max u v} :=
  sheafCompose J AddCommGrpCat.uliftFunctor

/-- The `ULift` of `topologicalSheaf X M` to `Ab.{u + 1}`. -/
noncomputable def topologicalSheafULift : Sheaf (ProEt.topology X) Ab.{max u v w} :=
  Sheaf.uliftFunctor.obj (topologicalSheaf X M)

/-- Postcomposition with a continuous additive map, as a morphism of the lifted
sheaves of continuous maps. -/
noncomputable def topologicalSheafULiftMap {M' : Type v} [TopologicalSpace M']
    [AddCommGroup M'] [IsTopologicalAddGroup M'] (f : M →+ M') (hf : Continuous f) :
    Sheaf.uliftFunctor.obj (topologicalSheaf X M) ⟶ topologicalSheafULift X M' :=
  Sheaf.uliftFunctor.map (topologicalSheafMap X M f hf)

/-- Functoriality of `topologicalSheafULiftMap` in the coefficient map. -/
lemma topologicalSheafULiftMap_comp
    {M₂ M₃ : Type v} [TopologicalSpace M₂] [AddCommGroup M₂] [IsTopologicalAddGroup M₂]
    [TopologicalSpace M₃] [AddCommGroup M₃] [IsTopologicalAddGroup M₃]
    (f : M →+ M₂) (hf : Continuous f) (g : M₂ →+ M₃) (hg : Continuous g) :
    topologicalSheafULiftMap X M f hf ≫ topologicalSheafULiftMap X M₂ g hg =
      topologicalSheafULiftMap X M (g.comp f) (hg.comp hf) := by
  simp only [topologicalSheafULiftMap, ← topologicalSheafMap_comp X M f hf g hg]
  exact Sheaf.uliftFunctor.map_comp
    (topologicalSheafMap X M f hf) (topologicalSheafMap X M₂ g hg)

end Topological

/-- The inverse system `n ↦ ℤ/ℓⁿℤ` of (discrete) topological abelian groups, with the
reduction maps as transition maps. -/
noncomputable def zmodTopSystem (ℓ : ℕ) : ℕᵒᵖ ⥤ TopModuleCat.{0} ℤ :=
  Functor.ofOpSequence
    (X := fun n ↦ TopModuleCat.of ℤ (ZMod (ℓ ^ n)))
    (fun n ↦ TopModuleCat.ofHom
      { toLinearMap := (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n))
          (ZMod (ℓ ^ n))).toAddMonoidHom.toIntLinearMap
        cont := continuous_of_discreteTopology })

/-- The inverse system `n ↦ (U ↦ C(U, ℤ/ℓⁿℤ))` of abelian sheaves on the pro-étale site
of `X`, with the reduction maps as transition maps. It is the composition of the system
of coefficient groups `zmodTopSystem` with the (lifted) sheaf-of-continuous-functions
functor. -/
noncomputable def zmodContinuousSystem (ℓ : ℕ) :
    ℕᵒᵖ ⥤ Sheaf (ProEt.topology X) Ab.{max u v} :=
  zmodTopSystem ℓ ⋙ topologicalSheafFunctor.{u, 0} X ⋙ Sheaf.uliftFunctor.{u, v}

/-- The transition maps of `zmodContinuousSystem` are induced by the reduction maps. -/
lemma zmodContinuousSystem_map_succ (ℓ n : ℕ) :
    (zmodContinuousSystem X ℓ).map (homOfLE (Nat.le_succ n)).op =
      Sheaf.uliftFunctor.map (topologicalSheafMap X (ZMod (ℓ ^ (n + 1)))
        (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n))).toAddMonoidHom
        continuous_of_discreteTopology) := by
  simp only [zmodContinuousSystem, Functor.comp_map, zmodTopSystem,
    Functor.ofOpSequence_map_homOfLE_succ]
  rfl

/-- The inverse system `n ↦ Hᵐ(X_proét, ℤ/ℓⁿℤ)` of pro-étale cohomology groups of the
sheaves of continuous `ℤ/ℓⁿℤ`-valued functions, with transition maps induced by the
reduction maps. -/
noncomputable def proetaleCohomologySystem (ℓ : ℕ) (m : ℕ) :
    ℕᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  zmodContinuousSystem.{u, u + 1} X ℓ ⋙ extFunctorObj (proetaleConstantInt X) m


/-! ### The reduction map from `ℓ`-adic cohomology to the limit -/

section Padic

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- The projections `ℤ_[ℓ] → ℤ/ℓⁿℤ` are continuous: their fibers are unions of balls
of radius `ℓ⁻ⁿ`. -/
lemma continuous_toZModPow (n : ℕ) : Continuous (PadicInt.toZModPow (p := ℓ) n) := by
  have hℓ : (0 : ℝ) < (ℓ : ℝ) := by
    exact_mod_cast (Fact.out (p := ℓ.Prime)).pos
  refine continuous_def.mpr fun s _ ↦ Metric.isOpen_iff.mpr fun x hx ↦ ?_
  refine ⟨(ℓ : ℝ) ^ (-(n : ℤ) + 1), zpow_pos hℓ _, fun y hy ↦ ?_⟩
  have h1 : ‖y - x‖ < (ℓ : ℝ) ^ (-(n : ℤ) + 1) := by
    rw [← dist_eq_norm]
    exact hy
  have h2 : ‖y - x‖ ≤ (ℓ : ℝ) ^ (-(n : ℤ)) :=
    (PadicInt.norm_le_pow_iff_norm_lt_pow_add_one (y - x) (-(n : ℤ))).mpr h1
  have h3 : PadicInt.toZModPow (p := ℓ) n (y - x) = 0 := by
    rw [← RingHom.mem_ker, PadicInt.ker_toZModPow]
    exact (PadicInt.norm_le_pow_iff_mem_span_pow (y - x) n).mp h2
  have h4 : PadicInt.toZModPow (p := ℓ) n y = PadicInt.toZModPow (p := ℓ) n x := by
    rw [map_sub, sub_eq_zero] at h3
    exact h3
  change PadicInt.toZModPow (p := ℓ) n y ∈ s
  rw [h4]
  exact hx

/-- The reduction map from the (`ULift`ed) `ℓ`-adic sheaf to the sheaf of continuous
`ℤ/ℓⁿℤ`-valued functions, induced by `PadicInt.toZModPow`. -/
noncomputable def ellAdicToZModContinuous (n : ℕ) :
    Sheaf.uliftFunctor.obj (X.ellAdicSheaf ℓ) ⟶
      Sheaf.uliftFunctor.obj (topologicalSheaf X (ZMod (ℓ ^ n))) :=
  topologicalSheafULiftMap X ℤ_[ℓ] (PadicInt.toZModPow n).toAddMonoidHom
    (continuous_toZModPow ℓ n)

/-- The reduction maps `ellAdicToZModContinuous` assemble into a cone over the system
of sheaves of continuous `ℤ/ℓⁿℤ`-valued functions, with apex the `ℓ`-adic sheaf. -/
noncomputable def ellAdicCone : Cone (zmodContinuousSystem X ℓ) where
  pt := topologicalSheafULift.{u, 0, u + 1} X ℤ_[ℓ]
  π := NatTrans.ofOpSequence
    (app := fun n ↦ ellAdicToZModContinuous X ℓ n)
    (naturality := fun n ↦ by
      simp only [Functor.const_obj_map]
      rw [zmodContinuousSystem_map_succ]
      change topologicalSheafULiftMap .. =
        topologicalSheafULiftMap .. ≫ topologicalSheafULiftMap ..
      rw [topologicalSheafULiftMap_comp]
      congr 1
      ext x
      exact (RingHom.congr_fun
        (PadicInt.zmod_cast_comp_toZModPow n (n + 1) (Nat.le_succ n)) x).symm)

/-- **The canonical map from `ℓ`-adic cohomology to the inverse limit of the pro-étale
cohomology groups with `ℤ/ℓⁿℤ`-coefficients**, induced by the reduction maps
`ℤ_[ℓ] → ℤ/ℓⁿℤ` of coefficient sheaves. -/
noncomputable def ellAdicCohomologyToLimit (m : ℕ) :
    AddCommGrpCat.of (X.EllAdicCohomology ℓ m) ⟶ limit (proetaleCohomologySystem X ℓ m) :=
  limit.lift _ ((extFunctorObj (proetaleConstantInt X) m).mapCone (ellAdicCone X ℓ))

end Padic


end EllAdicEtaleComparison


