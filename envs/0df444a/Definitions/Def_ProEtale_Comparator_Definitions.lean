-- Prove2me | Definitions.Def_ProEtale_Comparator_Definitions
-- name    : ProEtale_Comparator_Definitions
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T12:10:50.14679+00:00
-- url     : https://prove2.me/theorems/85b2e4ee-84c0-4731-8859-5bb4ac4023b9
-- title:
--   Étale-to-pro-étale comparison III: the comparison maps on cohomology with $\mathbb{Z}/\ell^n$-coefficients
-- statement:
--   For a scheme $X$, this file defines the canonical maps from étale to pro-étale cohomology with $\mathbb Z/\ell^n$-coefficients.
--
--   1. For an abelian group $M$, the canonical morphism from the constant sheaf $M$ on $X_{\text{proét}}$ to the pullback $\nu^*$ of the constant sheaf $M$ on $X_{\text{ét}}$ (`pullbackConstantComparison`).
--   2. For a topological abelian group $M$, the canonical morphism from the pullback of the constant étale sheaf $M$ to the sheaf $U \mapsto \operatorname{Map}_{\mathrm{cont}}(U, M)$ on $X_{\text{proét}}$, adjoint to the map sending an element of $M$ to the corresponding constant function (`pullbackConstantToTopological`), with its naturality in $M$.
--   3. The resulting morphism of inverse systems of sheaves over $n$ (`pullbackConstantToTopologicalSystemHom`) and the induced morphism of inverse systems of cohomology groups
--
--   $$
--   c : \bigl(H^m(X_{\text{ét}}, \mathbb Z/\ell^n)\bigr)_n \longrightarrow \bigl(H^m(X_{\text{proét}}, \mathbb Z/\ell^n)\bigr)_n
--   $$
--
--   (`etaleToProetaleCohomologySystemHom`).
--
--   Every statement relating $\ell$-adic cohomology to étale cohomology in this mission is phrased with these maps. This file imports the two preceding parts, so importing it gives access to all three.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014), Section 5.1, Lemma 4.2.12. Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Comparator/Definitions.lean (declarations kept unchanged, unused ones removed; part 3 of 3 of that file, which is split to keep compilation short).

/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib
import Definitions.Def_ProEtale_Comparator_Systems

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false

universe u v w

open CategoryTheory Limits Opposite Abelian AlgebraicGeometry AlgebraicGeometry.Scheme
  MorphismProperty

variable (X : Scheme.{u})

open AlgebraicGeometry.Scheme ProEt

namespace EllAdicEtaleComparison

/-! ### The comparison map from étale to pro-étale cohomology -/

/-- The canonical morphism from the constant pro-étale sheaf to the pullback of the
constant étale sheaf, obtained by transposing (along the constant sheaf adjunction of
the pro-étale site) the composite of the unit of the constant sheaf adjunction of the
étale site with the sections of the unit of the adjunction `ν^* ⊣ ν_*`. -/
noncomputable def pullbackConstantComparison (M : AddCommGrpCat.{u + 1}) :
    (constantSheaf (ProEt.topology X) Ab.{u + 1}).obj M ⟶
      (sheafPullback X Ab).obj ((constantSheaf X.smallEtaleTopology Ab.{u + 1}).obj M) :=
  ((constantSheafAdj (ProEt.topology X) Ab.{u + 1} (Over.mkIdTerminal _ _)).homEquiv _ _).symm
    ((constantSheafAdj X.smallEtaleTopology Ab.{u + 1} (Over.mkIdTerminal _ _)).unit.app M ≫
        ((sheafSections X.smallEtaleTopology Ab.{u + 1}).obj
          (op (Over.mk ⊤ (𝟙 X) (id_mem _ X)))).map ((sheafAdjunction X Ab).unit.app
            ((constantSheaf X.smallEtaleTopology Ab.{u + 1}).obj M)))

section PullbackToTopological

variable (M : Type) [TopologicalSpace M] [AddCommGroup M] [IsTopologicalAddGroup M]

/-- The constants map `M → C(X, M)` as a morphism into the sections of `ν_*` of the
lifted sheaf of continuous `M`-valued functions over the terminal étale `X`-scheme. -/
noncomputable def constantsToSectionsPushforward :
    AddCommGrpCat.of (ULift.{u + 1} M) ⟶
      ((sheafSections X.smallEtaleTopology Ab.{u + 1}).obj
        (op (MorphismProperty.Over.mk ⊤ (𝟙 X) (MorphismProperty.id_mem _ X)))).obj
        ((sheafPushforward X Ab).obj (topologicalSheafULift.{u, 0, u + 1} X M)) :=
  AddCommGrpCat.ofHom
    { toFun := fun m ↦ ULift.up ⟨fun _ ↦ m.down, continuous_const⟩
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }

/-- The canonical morphism from the pullback of the constant étale sheaf on `M` to the
sheaf of continuous `M`-valued functions on the pro-étale site: the double transpose
(along `ν^* ⊣ ν_*` and the constant sheaf adjunction of the étale site) of the
constants map `M → C(X, M)`. -/
noncomputable def pullbackConstantToTopological :
    (sheafPullback X Ab).obj ((constantSheaf X.smallEtaleTopology Ab.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} M))) ⟶
      topologicalSheafULift.{u, 0, u + 1} X M :=
  ((sheafAdjunction X Ab).homEquiv _ _).symm
    (((constantSheafAdj X.smallEtaleTopology Ab.{u + 1} (Over.mkIdTerminal _ _)).homEquiv
      _ _).symm (constantsToSectionsPushforward X M))

/-- Naturality of `pullbackConstantToTopological` in the coefficient group. -/
lemma pullbackConstantToTopological_naturality {M' : Type} [TopologicalSpace M']
    [AddCommGroup M'] [IsTopologicalAddGroup M'] (f : M →+ M') (hf : Continuous f) :
    (sheafPullback X Ab).map ((constantSheaf X.smallEtaleTopology Ab.{u + 1}).map
        (AddCommGrpCat.uliftFunctor.{u + 1}.map (AddCommGrpCat.ofHom f))) ≫
      pullbackConstantToTopological X M' =
        pullbackConstantToTopological X M ≫ topologicalSheafULiftMap X M f hf := by
  unfold pullbackConstantToTopological
  refine Eq.trans (Eq.trans
    ((sheafAdjunction X Ab).homEquiv_naturality_left_symm _ _).symm ?_)
    ((sheafAdjunction X Ab).homEquiv_naturality_right_symm _ _)
  refine congrArg ⇑(((sheafAdjunction X Ab).homEquiv _ _).symm) ?_
  refine Eq.trans (Eq.trans
    ((constantSheafAdj X.smallEtaleTopology Ab.{u + 1}
      (Over.mkIdTerminal _ _)).homEquiv_naturality_left_symm _ _).symm ?_)
    ((constantSheafAdj X.smallEtaleTopology Ab.{u + 1}
      (Over.mkIdTerminal _ _)).homEquiv_naturality_right_symm _ _)
  refine congrArg ⇑(((constantSheafAdj X.smallEtaleTopology Ab.{u + 1}
    (Over.mkIdTerminal _ _)).homEquiv _ _).symm) ?_
  apply ConcreteCategory.hom_ext
  intro m
  rfl

end PullbackToTopological

/-- The sheaf-level comparison: the canonical morphism of inverse systems from the
pullbacks of the constant étale sheaves `ℤ/ℓⁿℤ` to the sheaves of continuous
`ℤ/ℓⁿℤ`-valued functions on the pro-étale site. Each component is an isomorphism
("locally constant = continuous into a discrete group"), but this is a theorem
(BS, Lemma 4.2.12) and not part of the definition. -/
noncomputable def pullbackConstantToTopologicalSystemHom (ℓ : ℕ) :
    (zmodAbSystem ℓ ⋙ constantSheaf X.smallEtaleTopology Ab.{u + 1}) ⋙ sheafPullback X Ab ⟶
      zmodContinuousSystem.{u, u + 1} X ℓ :=
  NatTrans.ofOpSequence
    (app := fun n ↦ pullbackConstantToTopological X (ZMod (ℓ ^ n)))
    (naturality := fun n ↦ by
      change (sheafPullback X Ab).map ((constantSheaf _ _).map
          ((zmodAbSystem ℓ).map (homOfLE (n.le_add_right 1)).op)) ≫ _ = _
      rw [zmodAbSystem_map_succ, zmodContinuousSystem_map_succ,
        pullbackConstantToTopological_naturality X (ZMod (ℓ ^ (n + 1)))
          (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n))).toAddMonoidHom
          continuous_of_discreteTopology]
      cat_disch)

set_option maxHeartbeats 1000000 in
/-- **The canonical comparison map from étale to pro-étale cohomology with
`ℤ/ℓⁿℤ`-coefficients**, as a morphism of inverse systems: on each level it is given by
the functoriality of `Ext`-groups along the exact functor `ν^*` together with the
canonical constant sheaf comparisons `pullbackConstantComparison` (on the cohomological
unit) and `pullbackConstantToTopological` (on the coefficients). -/
noncomputable def etaleToProetaleCohomologySystemHom (ℓ m : ℕ) :
    etaleCohomologySystem X ℓ m ⟶ proetaleCohomologySystem X ℓ m where
  app k := AddCommGrpCat.ofHom
    { toFun := fun x ↦ ((Ext.mk₀ (pullbackConstantComparison X
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).comp
          (Ext.mapExactFunctor (sheafPullback X Ab) x) (zero_add m)).comp
        (Ext.mk₀ ((pullbackConstantToTopologicalSystemHom X ℓ).app k)) (add_zero m)
      map_zero' := by
        rw [Ext.mapExactFunctor_zero, Ext.comp_zero, Ext.zero_comp]
      map_add' := fun x y ↦ by
        rw [Ext.mapExactFunctor_add, Ext.comp_add, Ext.add_comp] }
  naturality {k k'} f := by
    apply ConcreteCategory.hom_ext
    intro x
    refine (ConcreteCategory.comp_apply _ _ _).trans
      (Eq.trans ?_ (ConcreteCategory.comp_apply _ _ _).symm)
    change ((Ext.mk₀ _).comp (Ext.mapExactFunctor (sheafPullback X Ab)
        (x.comp (Ext.mk₀ ((zmodAbSystem ℓ ⋙
          constantSheaf X.smallEtaleTopology Ab.{u + 1}).map f)) (add_zero m)))
          (zero_add m)).comp
          (Ext.mk₀ ((pullbackConstantToTopologicalSystemHom X ℓ).app k')) (add_zero m) =
      (((Ext.mk₀ _).comp (Ext.mapExactFunctor (sheafPullback X Ab) x) (zero_add m)).comp
          (Ext.mk₀ ((pullbackConstantToTopologicalSystemHom X ℓ).app k)) (add_zero m)).comp
        (Ext.mk₀ ((zmodContinuousSystem X ℓ).map f)) (add_zero m)
    rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]
    simp only [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀]
    rw [← Functor.comp_map (zmodAbSystem ℓ ⋙ constantSheaf X.smallEtaleTopology Ab.{u + 1})
      (sheafPullback X Ab), (pullbackConstantToTopologicalSystemHom X ℓ).naturality f]

end EllAdicEtaleComparison


