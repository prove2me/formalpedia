-- Prove2me | Definitions.Def_RPLib_FX_EtP1_04
-- name    : RPLib_FX_EtP1_04
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T01:16:21.5102+00:00
-- url     : https://prove2.me/theorems/96f18f72-8145-4a39-94d6-10a251cf216f
-- title:
--   Étale cohomology of the projective line, library file 04 of 34
-- statement:
--   File 04 of 34 of the étale cohomology library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtSheaves_GenBr`: S4-EtSheaves, part O10b: the generic Galois group maps onto `π₁(Spec A)`
--   * `S4.Def_RP_EtSheaves_FVRes`: S4-EtSheaves, part O10d-2(iii): `F_V` becomes constant on the Galois cover, so it is lisse
--   * `S4.Def_RP_EtSheaves_StalkFV`: S4-EtSheaves, part O10d-2(iv-b): the stalk of `F_V` is `V`, with the Galois action through `ρ`
--   * `S4.Def_RP_EtSheaves_GalFV`: S4-EtSheaves, part O10d-2(iv-c): the Galois representation on `(F_V)_x̄` is `ρ ∘ galFV`
--   * `S4.Def_RP_EtSheaves_ChartSch`: S4-EtSheaves, O10f part e2: charts for lisse sheaves on `Spec A`
--   * `S4.Def_RP_EtSheaves_GalGen`: S4-EtSheaves, part O10d-2(iv-c), generic point: `galFV` is `π₁ ↠ Gal(L/K)` after `genToPi1`
--   * `S4.Def_RP_EtSheaves_GalSurj`: S4-EtSheaves, part O10e(i): every finite continuous `π₁`-representation is the generic fibre of a lisse sheaf
--   * `S4.Def_RP_EtSheaves_Plumb`: S4-EtSheaves, O10c part 4: from `IsLisse` to a standard etale chart
--   * `S4.Def_RP_EtSheaves_InertiaFix`: S4-EtSheaves, O10c part 2a: an inertia element fixes a prime of `B ⊗[A] R'` over `(0)`
--   * `S4.Def_RP_EtSheaves_FibreNe`: S4-EtSheaves, O10c part 2b: a prime of `B ⊗[A] R'` containing `Q ⊗ 1`
--   * `S4.Def_RP_EtSheaves_InertiaLift`: S4-EtSheaves, O10c part 2c: lifting an inertia element to the separable closure
--   * `S4.Def_RP_EtSheaves_EssSurj`: S4-EtSheaves, O10f part f: lisse sheaves on `Spec A` are their generic Galois representations
--
--   **Formalization note.** One file of a library formalizing the étale cohomology of the projective line $\mathbf P^1_k = \operatorname{Proj} k[X_0, X_1]$ over an algebraically closed field $k$ with coefficients in sheaves of $\Lambda$-modules on the small étale site ($H^n = \operatorname{Ext}^n(\Lambda, -)$): $H^1(\mathbf P^1, \Lambda) = 0$, $H^2(\mathbf P^1, \Lambda) \cong \Lambda$ and $H^{n+3}(\mathbf P^1, F) = 0$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §1 (cohomology of curves) and Chapter III, §2 (Kummer theory); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Arcata », Chapter IV (cohomology of curves, Tsen's theorem)

import Mathlib
import Definitions.Def_RPLib_FX_EtP1_03

/-!
# Étale cohomology of the projective line, library file 04 of 34

Declarations of the formalization of the étale cohomology of the projective line over an algebraically
closed field (H¹ = 0, H² ≅ Λ, vanishing in degrees ≥ 3), re-hosted declaration by declaration from the
library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtSheaves_GenBr`: S4-EtSheaves, part O10b: the generic Galois group maps onto `π₁(Spec A)`
* `S4.Def_RP_EtSheaves_FVRes`: S4-EtSheaves, part O10d-2(iii): `F_V` becomes constant on the Galois cover, so it is lisse
* `S4.Def_RP_EtSheaves_StalkFV`: S4-EtSheaves, part O10d-2(iv-b): the stalk of `F_V` is `V`, with the Galois action through `ρ`
* `S4.Def_RP_EtSheaves_GalFV`: S4-EtSheaves, part O10d-2(iv-c): the Galois representation on `(F_V)_x̄` is `ρ ∘ galFV`
* `S4.Def_RP_EtSheaves_ChartSch`: S4-EtSheaves, O10f part e2: charts for lisse sheaves on `Spec A`
* `S4.Def_RP_EtSheaves_GalGen`: S4-EtSheaves, part O10d-2(iv-c), generic point: `galFV` is `π₁ ↠ Gal(L/K)` after `genToPi1`
* `S4.Def_RP_EtSheaves_GalSurj`: S4-EtSheaves, part O10e(i): every finite continuous `π₁`-representation is the generic fibre of a lisse sheaf
* `S4.Def_RP_EtSheaves_Plumb`: S4-EtSheaves, O10c part 4: from `IsLisse` to a standard etale chart
* `S4.Def_RP_EtSheaves_InertiaFix`: S4-EtSheaves, O10c part 2a: an inertia element fixes a prime of `B ⊗[A] R'` over `(0)`
* `S4.Def_RP_EtSheaves_FibreNe`: S4-EtSheaves, O10c part 2b: a prime of `B ⊗[A] R'` containing `Q ⊗ 1`
* `S4.Def_RP_EtSheaves_InertiaLift`: S4-EtSheaves, O10c part 2c: lifting an inertia element to the separable closure
* `S4.Def_RP_EtSheaves_EssSurj`: S4-EtSheaves, O10f part f: lisse sheaves on `Spec A` are their generic Galois representations
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtSheaves_GenBr =====
section

/-!
# S4-EtSheaves, part O10b: the generic Galois group maps onto `π₁(Spec A)`

For a field `K` (a fraction field of `A`), a field `κ` with `K → κ`, and a separably closed `Ω/κ`, the maximal
unramified extension `K_U = maxUnram A K` embeds into `Ω` over `K` (`emb`), and restriction along this embedding is a
continuous group homomorphism `toPi1 : Gal(Ω/κ) →* Pi1 A K` (`emb_toPi1`), surjective when `K → κ` is onto
(`toPi1_surjective`), with kernel the automorphisms fixing `emb(K_U)` (`toPi1_eq_one_iff`).

Specialised to the generic point `η = ⊥` of `Spec A` (`κ(η) ≅ K`, `fracIso`), this is the bridge
`genToPi1 : Gal η →* Pi1 A K` from the Galois group acting on stalks at `η̄` (`galRep`) to `GalCover`'s `π₁`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory

noncomputable section

namespace RamanujanPetersson.EtSheaves

namespace GenBr

section Abstract

variable (A K : Type) [CommRing A] [Field K] [Algebra A K]
variable (Ω : Type) [Field Ω] [Algebra K Ω] [IsSepClosed Ω]

attribute [local instance] embAlg

attribute [local instance] embTower

variable (κ : Type) [Field κ] [Algebra K κ] [Algebra κ Ω] [IsScalarTower K κ Ω]

/-- An automorphism of `K_U/K` fixing a `K`-basis of a finite subextension fixes the subextension. -/
theorem mem_fixingSubgroup_of_basis (L : IntermediateField K (maxUnram A K)) [FiniteDimensional K L]
    (τ : Pi1 A K) (hτ : ∀ i, τ ((Module.finBasis K L i : L) : maxUnram A K) = (Module.finBasis K L i : L)) :
    τ ∈ L.fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro y hy
  have h2 : y = ∑ i, (Module.finBasis K L).repr ⟨y, hy⟩ i • ((Module.finBasis K L i : L) : maxUnram A K) := by
    calc y = L.val ⟨y, hy⟩ := rfl
      _ = L.val (∑ i, (Module.finBasis K L).repr ⟨y, hy⟩ i • Module.finBasis K L i) := by
          rw [(Module.finBasis K L).sum_repr]
      _ = _ := by simp only [map_sum, map_smul, IntermediateField.coe_val]
  rw [h2, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_smul, hτ i]

/-- `toPi1` is continuous for the Krull topologies. -/
theorem toPi1_continuous [Algebra.IsSeparable κ Ω] : Continuous (toPi1 A K Ω κ) := by
  apply continuous_of_continuousAt_one _ (continuousAt_def.mpr _)
  intro N hN
  rw [map_one, krullTopology_mem_nhds_one_iff] at hN
  obtain ⟨L, hL, hO⟩ := hN
  let S : Set Ω := Set.range (fun i => emb A K Ω ((Module.finBasis K L i : L) : maxUnram A K))
  haveI : Finite S := Finite.Set.finite_range _
  haveI : FiniteDimensional κ (IntermediateField.adjoin κ S) :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsSeparable.isIntegral κ x)
  apply mem_nhds_iff.mpr
  refine ⟨((IntermediateField.adjoin κ S).fixingSubgroup : Set (Ω ≃ₐ[κ] Ω)), ?_,
    IntermediateField.fixingSubgroup_isOpen _, (IntermediateField.adjoin κ S).fixingSubgroup.one_mem⟩
  intro σ hσ
  apply hO
  simp only [SetLike.mem_coe] at hσ ⊢
  rw [IntermediateField.mem_fixingSubgroup_iff] at hσ
  apply mem_fixingSubgroup_of_basis
  intro i
  apply (emb A K Ω).toRingHom.injective
  show emb A K Ω (toPi1 A K Ω κ σ _) = emb A K Ω _
  rw [emb_toPi1]
  exact hσ _ (IntermediateField.subset_adjoin κ S ⟨i, rfl⟩)

end Abstract

section Generic

variable (A K : Type) [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]

attribute [local instance] genAlg

attribute [local instance] genAlgSep

attribute [local instance] genTower

theorem genToPi1_continuous : Continuous (genToPi1 A K) :=
  toPi1_continuous A K (SeparableClosure (genField A)) (genField A)

end Generic

end GenBr

end RamanujanPetersson.EtSheaves

end

end

-- ===== S4.Def_RP_EtSheaves_FVRes =====
section

/-!
# S4-EtSheaves, part O10d-2(iii): `F_V` becomes constant on the Galois cover, so it is lisse

For `T` etale over `Y`, restriction along the section `ι 1` is an isomorphism `F_V(T) ≅ V_X(T)` (`eT`: a section of
`F_V` is determined by `s(1)`, and `τ ↦ ρ(τ⁻¹) v` glues to a section of `F_V`, `glueV`). These are natural in `T`, so
`π^* F_V ≅ π^* V_X ≅ V_Y` (`resIso`, `pullIso`), and `F_V` is lisse for finite `V` since `π` is surjective
(`isLisse_FV`).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtSheaves.TorSec

attribute [local instance] GalCover.ring GalCover.dom GalCover.alg GalCover.inj GalCover.fin GalCover.grp GalCover.fG GalCover.act GalCover.gal

variable {A : Type} [CommRing A] [IsDomain A] {C : GalCover A} (Λ : Type) [CommRing Λ] {V : Type}
  [AddCommGroup V] [Module Λ V] (ρ : Representation Λ C.G V)

theorem eT_naturality {T' T : (SY C).Etale} (h : T' ⟶ T) (s : (FV C Λ ρ).obj.obj (op (tx T))) :
    eT Λ ρ T' (((FV C Λ ρ).obj.map ((etComp (pr C)).map h).op).hom s) =
      ((VX A Λ V).obj.map ((etComp (pr C)).map h).op).hom (eT Λ ρ T s) := by
  let s1 : (VX A Λ V).obj.obj (op (tp T)) := s.1
  change ((VX A Λ V).obj.map (sec T' 1).op).hom (((VX A Λ V).obj.map
      ((etComp (pr C)).map ((etPull (pr C)).map ((etComp (pr C)).map h))).op).hom s1) =
    ((VX A Λ V).obj.map ((etComp (pr C)).map h).op).hom (((VX A Λ V).obj.map (sec T 1).op).hom s1)
  exact (map_map_apply (VX A Λ V) _ (sec T' 1) s1).trans
    ((congrArg (fun g => ((VX A Λ V).obj.map g.op).hom s1) (sec_naturality h 1)).trans
      (map_map_apply (VX A Λ V) (sec T 1) ((etComp (pr C)).map h) s1).symm)

/-- **`F_V|_Y ≅ V_X|_Y`.** -/
def resIso : (res (pr C) Λ).obj (FV C Λ ρ) ≅ (res (pr C) Λ).obj (VX A Λ V) :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso (NatIso.ofComponents
    (fun T => (eT Λ ρ T.unop).toModuleIso) (by
      intro T T' h
      ext s
      exact eT_naturality Λ ρ h.unop s))

/-- **`π^* F_V ≅ V_Y`.** -/
def pullIso : (pull (pr C) Λ).obj (FV C Λ ρ) ≅ constSh Λ (SY C) (ModuleCat.of Λ V) :=
  (pullIsoRes (pr C) Λ).app _ ≪≫ resIso Λ ρ ≪≫ ((pullIsoRes (pr C) Λ).app _).symm ≪≫
    pullConst Λ (pr C) (ModuleCat.of Λ V)

/-- **`F_V` is lisse** for a finite `Λ`-module `V`. -/
theorem isLisse_FV [Module.Finite Λ V] : IsLisse Λ (FV C Λ ρ) := fun x => by
  obtain ⟨y, hy⟩ := pr_surjective C x
  exact ⟨MorphismProperty.Over.mk ⊤ (pr C) inferInstance, y, hy, ModuleCat.of Λ V, inferInstance,
    ⟨pullIso Λ ρ⟩⟩

end RamanujanPetersson.EtSheaves.TorSec

end

end

-- ===== S4.Def_RP_EtSheaves_StalkFV =====
section

/-!
# S4-EtSheaves, part O10d-2(iv-b): the stalk of `F_V` is `V`, with the Galois action through `ρ`

For a geometric point `t` of `Y = Spec B`, the stalk of `F_V` at `t ≫ π` is `V` (`stalkFV`: restriction to `Y`
(`resFibIso`), `F_V|_Y ≅ V_X|_Y` (`resIso`), constant stalks). Its inverse sends `v` to the germ of the section
`unitFV v` of `F_V` over `Y` (`stalkFV_inv`). The element `g ∈ G` acting on `Y` over `X` moves `unitFV v` to
`unitFV (ρ g v)` (`map_actE_unitFV`), so an automorphism `τ` of `Spec Ω` over `X` with `τ ≫ t = t ≫ g_Y` acts on the
stalk by `ρ g` (`stalkAut_stalkFV_inv`). Every such `τ` determines a unique `g` (`existsUnique_act`, trivial inertia),
`actOf`, multiplicative in `τ` (`actOf_comp`), and `τ` acts on the stalk by `ρ (actOf τ)` (`stalkAut_stalkFV`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtSheaves.TorSec

attribute [local instance] GalCover.ring GalCover.dom GalCover.alg GalCover.inj GalCover.fin GalCover.grp GalCover.fG GalCover.act GalCover.gal

variable {A : Type} [CommRing A] [IsDomain A] {C : GalCover A} (Λ : Type) [CommRing Λ] {V : Type}
  [AddCommGroup V] [Module Λ V] (ρ : Representation Λ C.G V)

/-- **The stalk of `F_V` at `t ≫ π` is `V`.** -/
def stalkFV (t : GeomPt (SY C)) : ((t.map (pr C)).stalkF Λ).obj (FV C Λ ρ) ≅ ModuleCat.of Λ V :=
  (resFibIso (pr C) t Λ (FV C Λ ρ)).symm ≪≫ (t.stalkF Λ).mapIso (resIso Λ ρ) ≪≫
    resFibIso (pr C) t Λ (VX A Λ V) ≪≫ constStalkIso Λ (t.map (pr C)) (ModuleCat.of Λ V)

theorem resIso_inv_app (T : (SY C).Etale) (z : (VX A Λ V).obj.obj (op (tx T))) :
    ((resIso Λ ρ).inv.hom.app (op T)).hom z = (eT Λ ρ T).symm z := rfl

/-- **`stalkFV⁻¹ v` is the germ of `unitFV v`.** -/
theorem stalkFV_inv (t : GeomPt (SY C)) (v : V) :
    (stalkFV Λ ρ t).inv.hom v = (t.map (pr C)).point.toPresheafFiber (tx (etId (SY C)))
      (liftX (pr C) t t.top) (FV C Λ ρ).obj (unitFV Λ ρ v) := by
  let z : (VX A Λ V).obj.obj (op (tx (etId (SY C)))) := (constUnit (ModuleCat.of Λ V) (tx (etId (SY C)))).hom v
  have h1 : (constStalkIso Λ (t.map (pr C)) (ModuleCat.of Λ V)).inv.hom v =
      (t.map (pr C)).point.toPresheafFiber (tx (etId (SY C))) (liftX (pr C) t t.top) (VX A Λ V).obj z :=
    (congrArg (fun φ => φ.hom v)
      (constUnit_germ (t.map (pr C)) (ModuleCat.of Λ V) (tx (etId (SY C))) (liftX (pr C) t t.top))).symm
  have h2 := resFibIso_inv_germ (pr C) t Λ (VX A Λ V) (etId (SY C)) t.top z
  have h3 : ((t.stalkF Λ).map (resIso Λ ρ).inv).hom
      (t.point.toPresheafFiber (etId (SY C)) t.top ((res (pr C) Λ).obj (VX A Λ V)).obj z) =
      t.point.toPresheafFiber (etId (SY C)) t.top ((res (pr C) Λ).obj (FV C Λ ρ)).obj (unitFV Λ ρ v) :=
    congrArg (fun φ => φ.hom z)
      (t.point.toPresheafFiber_naturality (resIso Λ ρ).inv.hom (etId (SY C)) t.top)
  have h4 := resFib_germ (pr C) t Λ (FV C Λ ρ) (etId (SY C)) t.top (unitFV Λ ρ v)
  calc (stalkFV Λ ρ t).inv.hom v
      = (resFib (pr C) t Λ (FV C Λ ρ)).hom (((t.stalkF Λ).map (resIso Λ ρ).inv).hom
          ((resFibIso (pr C) t Λ (VX A Λ V)).inv.hom
            ((constStalkIso Λ (t.map (pr C)) (ModuleCat.of Λ V)).inv.hom v))) := rfl
    _ = (resFib (pr C) t Λ (FV C Λ ρ)).hom (((t.stalkF Λ).map (resIso Λ ρ).inv).hom
          (t.point.toPresheafFiber (etId (SY C)) t.top ((res (pr C) Λ).obj (VX A Λ V)).obj z)) := by
        rw [h1, h2]
    _ = (resFib (pr C) t Λ (FV C Λ ρ)).hom
          (t.point.toPresheafFiber (etId (SY C)) t.top ((res (pr C) Λ).obj (FV C Λ ρ)).obj (unitFV Λ ρ v)) := by
        rw [h3]
    _ = _ := h4

/-- `g ∈ G` acting on `Y`, as an endomorphism of `Y` over `X`. -/
def actE (g : C.G) : tx (etId (SY C)) ⟶ tx (etId (SY C)) :=
  MorphismProperty.Over.homMk (act C g) (by
    change act C g ≫ 𝟙 _ ≫ pr C = 𝟙 _ ≫ pr C
    rw [Category.id_comp, act_pr]) trivial

theorem secL_mL (g : C.G) :
    secL (etId (SY C)) 1 ≫ pullback.lift (pullback.fst ((etId (SY C)).hom ≫ pr C) (pr C) ≫ act C g)
      (pullback.snd ((etId (SY C)).hom ≫ pr C) (pr C)) (by
        have h1 : act C g ≫ (etId (SY C)).hom ≫ pr C = (etId (SY C)).hom ≫ pr C := by
          change act C g ≫ 𝟙 _ ≫ pr C = 𝟙 _ ≫ pr C
          rw [Category.id_comp, act_pr]
        exact (Category.assoc _ _ _).trans ((congrArg
          (fun k => pullback.fst ((etId (SY C)).hom ≫ pr C) (pr C) ≫ k) h1).trans pullback.condition)) =
      act C g ≫ secL (etId (SY C)) g⁻¹ := by
  have key : (etId (SY C)).hom ≫ act C 1 = act C g ≫ (etId (SY C)).hom ≫ act C g⁻¹ := by
    change 𝟙 _ ≫ act C 1 = act C g ≫ 𝟙 _ ≫ act C g⁻¹
    rw [Category.id_comp, Category.id_comp, act_mul, mul_inv_cancel]
  refine pullback.hom_ext (f := (etId (SY C)).hom ≫ pr C) (g := pr C) ?_ ?_
  · exact (Category.assoc _ _ _).trans ((congrArg (fun k => secL (etId (SY C)) 1 ≫ k)
      (pullback.lift_fst _ _ _)).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ act C g) (secL_fst (etId (SY C)) 1)).trans ((Category.id_comp _).trans
      ((Category.comp_id _).symm.trans ((congrArg (fun k => act C g ≫ k) (secL_fst (etId (SY C)) g⁻¹)).symm.trans
      (Category.assoc _ _ _).symm))))))
  · exact (Category.assoc _ _ _).trans ((congrArg (fun k => secL (etId (SY C)) 1 ≫ k)
      (pullback.lift_snd _ _ _)).trans ((secL_snd (etId (SY C)) 1).trans (key.trans
      ((congrArg (fun k => act C g ≫ k) (secL_snd (etId (SY C)) g⁻¹)).symm.trans (Category.assoc _ _ _).symm))))

/-- **`ι 1 ≫ (g × 1) = g ≫ ι g⁻¹`** on `Y ×_X Y`. -/
theorem sec_actE (g : C.G) :
    sec (etId (SY C)) 1 ≫ (etComp (pr C)).map ((etPull (pr C)).map (actE g)) = actE g ≫ sec (etId (SY C)) g⁻¹ :=
  MorphismProperty.Over.Hom.ext (secL_mL g)

theorem eT_map_actE (g : C.G) (s : (FV C Λ ρ).obj.obj (op (tx (etId (SY C))))) :
    eT Λ ρ (etId (SY C)) (((FV C Λ ρ).obj.map (actE g).op).hom s) =
      ((VX A Λ V).obj.map (actE g).op).hom
        (((th C Λ ρ g⁻¹).hom.app (op (tx (etId (SY C))))).hom (eT Λ ρ (etId (SY C)) s)) := by
  let s1 : (VX A Λ V).obj.obj (op (tp (etId (SY C)))) := s.1
  have hm : ((VX A Λ V).obj.map (sec (etId (SY C)) g⁻¹).op).hom s1 =
      ((th C Λ ρ g⁻¹).hom.app (op (tx (etId (SY C))))).hom
        (((VX A Λ V).obj.map (sec (etId (SY C)) 1).op).hom s1) := by
    have h := (mem_FV_iff Λ ρ (etId (SY C)) s1).1 s.2 g⁻¹ 1
    rwa [one_mul] at h
  change ((VX A Λ V).obj.map (sec (etId (SY C)) 1).op).hom (((VX A Λ V).obj.map
      ((etComp (pr C)).map ((etPull (pr C)).map (actE g))).op).hom s1) =
    ((VX A Λ V).obj.map (actE g).op).hom (((th C Λ ρ g⁻¹).hom.app (op (tx (etId (SY C))))).hom
      (((VX A Λ V).obj.map (sec (etId (SY C)) 1).op).hom s1))
  exact (map_map_apply (VX A Λ V) ((etComp (pr C)).map ((etPull (pr C)).map (actE g))) (sec (etId (SY C)) 1) s1).trans
    ((congrArg (fun f => ((VX A Λ V).obj.map f.op).hom s1) (sec_actE g)).trans
      ((map_map_apply (VX A Λ V) (sec (etId (SY C)) g⁻¹) (actE g) s1).symm.trans
        (congrArg ((VX A Λ V).obj.map (actE g).op).hom hm)))

theorem th_constUnit (σ : C.G) (U : (SX A).Etale) (v : V) :
    ((th C Λ ρ σ).hom.app (op U)).hom ((constUnit (ModuleCat.of Λ V) U).hom v) =
      (constUnit (ModuleCat.of Λ V) U).hom (ρ σ⁻¹ v) :=
  (congrArg (fun η => (η.app (op U)).hom v) (toSheafify_naturality (SX A).smallEtaleTopology
    ((Functor.const ((SX A).Etale)ᵒᵖ).map (ModuleCat.ofHom (ρ σ⁻¹))))).symm

theorem map_constUnit {U U' : (SX A).Etale} (f : U ⟶ U') (w : V) :
    ((VX A Λ V).obj.map f.op).hom ((constUnit (ModuleCat.of Λ V) U').hom w) =
      (constUnit (ModuleCat.of Λ V) U).hom w :=
  (congrArg (fun φ => φ.hom w)
    ((toSheafify (SX A).smallEtaleTopology (constPre (ModuleCat.of Λ V))).naturality f.op)).symm

/-- **`g` moves `unitFV v` to `unitFV (ρ g v)`.** -/
theorem map_actE_unitFV (g : C.G) (v : V) :
    ((FV C Λ ρ).obj.map (actE g).op).hom (unitFV Λ ρ v) = unitFV Λ ρ (ρ g v) := by
  refine (eT Λ ρ (etId (SY C))).injective ((eT_map_actE Λ ρ g _).trans ?_)
  rw [unitFV, unitFV, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, th_constUnit, inv_inv,
    map_constUnit]

/-- **Equivariance**: `τ` with `τ ≫ t = t ≫ g_Y` acts on the stalk of `F_V` by `ρ g`. -/
theorem stalkAut_stalkFV_inv (t : GeomPt (SY C)) (g : C.G)
    (τ : Spec (CommRingCat.of t.Ω) ⟶ Spec (CommRingCat.of t.Ω))
    (hτ : τ ≫ (t.map (pr C)).pt = (t.map (pr C)).pt) (hl : τ ≫ t.pt = t.pt ≫ act C g) (v : V) :
    (((t.map (pr C)).stalkAut Λ τ hτ).app (FV C Λ ρ)).hom ((stalkFV Λ ρ t).inv.hom v) =
      (stalkFV Λ ρ t).inv.hom (ρ g v) := by
  rw [stalkFV_inv, stalkFV_inv, GeomPt.stalkAut_toPresheafFiber]
  have ha : ((t.map (pr C)).autHom τ hτ).hom.app (tx (etId (SY C))) (liftX (pr C) t t.top) =
      (t.map (pr C)).point.fiber.map (actE g) (liftX (pr C) t t.top) := Over.OverMorphism.ext hl
  rw [ha, ← map_actE_unitFV]
  exact (congrArg (fun φ => φ.hom (unitFV Λ ρ v))
    ((t.map (pr C)).point.toPresheafFiber_w (actE g) (liftX (pr C) t t.top) (FV C Λ ρ).obj)).symm

/-- **An automorphism of `Spec Ω` over `X` moves a lift to `Y` by a unique `g ∈ G`.** -/
theorem existsUnique_act {Ω : Type} [Field Ω] (l : Spec (CommRingCat.of Ω) ⟶ SY C)
    (τ : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of Ω)) (hτ : τ ≫ l ≫ pr C = l ≫ pr C) :
    ∃! g : C.G, τ ≫ l = l ≫ act C g := by
  obtain ⟨γ, rfl⟩ : ∃ γ, Spec.map γ = l := ⟨_, Spec.map_preimage l⟩
  obtain ⟨β, rfl⟩ : ∃ β, Spec.map β = τ := ⟨_, Spec.map_preimage τ⟩
  have key : ∀ g : C.G, Spec.map β ≫ Spec.map γ = Spec.map γ ≫ act C g ↔
      γ ≫ β = CommRingCat.ofHom (rh C g) ≫ γ := by
    intro g
    rw [act, ← Spec.map_comp, ← Spec.map_comp, Spec.map_inj]
  have hA : γ.hom.comp (algebraMap A C.B) = (γ ≫ β).hom.comp (algebraMap A C.B) := by
    have h1 : Spec.map (CommRingCat.ofHom (algebraMap A C.B) ≫ γ ≫ β) =
        Spec.map (CommRingCat.ofHom (algebraMap A C.B) ≫ γ) := by
      simpa only [Spec.map_comp, Category.assoc] using hτ
    exact (congrArg CommRingCat.Hom.hom (Spec.map_injective h1)).symm
  obtain ⟨σ, hσ⟩ := exists_eq_comp C γ.hom (γ ≫ β).hom hA
  have hσ' : γ ≫ β = CommRingCat.ofHom (rh C σ) ≫ γ := CommRingCat.hom_ext hσ
  refine ⟨σ, (key σ).2 hσ', fun g hg => ?_⟩
  exact eq_of_comp_eq C γ.hom (congrArg CommRingCat.Hom.hom (((key g).1 hg).symm.trans hσ'))

/-- The element of `G` by which `τ` (over `X`) moves the lift `t`. -/
def actOf (t : GeomPt (SY C)) (τ : Spec (CommRingCat.of t.Ω) ⟶ Spec (CommRingCat.of t.Ω))
    (hτ : τ ≫ (t.map (pr C)).pt = (t.map (pr C)).pt) : C.G :=
  (existsUnique_act t.pt τ hτ).exists.choose

theorem actOf_spec (t : GeomPt (SY C)) (τ : Spec (CommRingCat.of t.Ω) ⟶ Spec (CommRingCat.of t.Ω))
    (hτ : τ ≫ (t.map (pr C)).pt = (t.map (pr C)).pt) : τ ≫ t.pt = t.pt ≫ act C (actOf t τ hτ) :=
  (existsUnique_act t.pt τ hτ).exists.choose_spec

/-- **`τ` acts on the stalk of `F_V` at `t ≫ π` by `ρ (actOf τ)`.** -/
theorem stalkAut_stalkFV (t : GeomPt (SY C)) (τ : Spec (CommRingCat.of t.Ω) ⟶ Spec (CommRingCat.of t.Ω))
    (hτ : τ ≫ (t.map (pr C)).pt = (t.map (pr C)).pt) (v : V) :
    (((t.map (pr C)).stalkAut Λ τ hτ).app (FV C Λ ρ)).hom ((stalkFV Λ ρ t).inv.hom v) =
      (stalkFV Λ ρ t).inv.hom (ρ (actOf t τ hτ) v) :=
  stalkAut_stalkFV_inv Λ ρ t (actOf t τ hτ) τ hτ (actOf_spec t τ hτ) v

end RamanujanPetersson.EtSheaves.TorSec

end

end

-- ===== S4.Def_RP_EtSheaves_GalFV =====
section

/-!
# S4-EtSheaves, part O10d-2(iv-c): the Galois representation on `(F_V)_x̄` is `ρ ∘ galFV`

Every geometric point `s` of `X = Spec A` lifts to `Y = Spec B` (`exists_lift`); for a lift `l`, the stalk of `F_V`
at `s` is `V` (`stalkFVAt`), an automorphism `τ` of `Spec Ω` over `X` moves `l` by a unique `actOfL τ ∈ G`
(`actOfL_eq_iff`, multiplicative: `actOfL_comp`) and acts on the stalk by `ρ (actOfL τ)` (`stalkAut_stalkFVAt`).
At `x̄ = geomPtAt x` this gives a hom `galFV : Gal(κ(x)^sep/κ(x)) →* G` with open kernel (`isOpen_ker_galFV`, via
the regular representation and discreteness of stalks), and the Galois representation on `(F_V)_x̄` is
`ρ ∘ galFV` (`galRep_FV`, `stalkFVAt_galRep`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtSheaves.TorSec

attribute [local instance] GalCover.ring GalCover.dom GalCover.alg GalCover.inj GalCover.fin GalCover.grp GalCover.fG GalCover.act GalCover.gal

variable {A : Type} [CommRing A] [IsDomain A] {C : GalCover A}

section Act

variable (s : GeomPt (SX A)) (l : Spec (CommRingCat.of s.Ω) ⟶ SY C)

/-- The element of `G` by which `τ` (over `X`) moves the lift `l`. -/
def actOfL (hl : l ≫ pr C = s.pt) (τ : Spec (CommRingCat.of s.Ω) ⟶ Spec (CommRingCat.of s.Ω)) (hτ : τ ≫ s.pt = s.pt) : C.G :=
  actOf (liftPt s l) τ (liftPt_comp s l hl τ hτ)

theorem actOfL_spec (hl : l ≫ pr C = s.pt) (τ : Spec (CommRingCat.of s.Ω) ⟶ Spec (CommRingCat.of s.Ω)) (hτ : τ ≫ s.pt = s.pt) :
    τ ≫ l = l ≫ act C (actOfL s l hl τ hτ) :=
  actOf_spec (liftPt s l) τ (liftPt_comp s l hl τ hτ)

theorem actOfL_eq_iff (hl : l ≫ pr C = s.pt) (τ : Spec (CommRingCat.of s.Ω) ⟶ Spec (CommRingCat.of s.Ω)) (hτ : τ ≫ s.pt = s.pt)
    (g : C.G) : actOfL s l hl τ hτ = g ↔ τ ≫ l = l ≫ act C g :=
  ⟨fun h => h ▸ actOfL_spec s l hl τ hτ,
    fun h => (existsUnique_act l τ (liftPt_comp s l hl τ hτ)).unique (actOfL_spec s l hl τ hτ) h⟩

end Act

/-- **The Galois group of `κ(x)` acting through `G`**: `σ ↦` the element moving the lift `l` of `x̄`. -/
def galFV (x : SX A) (l : Spec (CommRingCat.of (geomPtAt x).Ω) ⟶ SY C) (hl : l ≫ pr C = (geomPtAt x).pt) :
    Gal x →* C.G where
  toFun σ := actOfL (geomPtAt x) l hl (galSpec x σ) (galSpec_comp x σ)
  map_one' := (actOfL_eq_iff _ l hl _ _ 1).2
    (((congrArg (fun φ : Spec (CommRingCat.of (geomPtAt x).Ω) ⟶ Spec (CommRingCat.of (geomPtAt x).Ω) => φ ≫ l)
      (galSpec_one x)).trans (Category.id_comp l)).trans
      ((Category.comp_id l).symm.trans (congrArg (fun φ => l ≫ φ) (act_one C).symm)))
  map_mul' σ τ := (actOfL_eq_iff _ l hl _ _ _).2 (by
    refine (congrArg (fun φ : Spec (CommRingCat.of (geomPtAt x).Ω) ⟶ Spec (CommRingCat.of (geomPtAt x).Ω) =>
      φ ≫ l) (galSpec_mul x σ τ)).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (fun φ => galSpec x σ ≫ φ) (actOfL_spec _ l hl _ (galSpec_comp x τ))).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (fun φ => φ ≫ act C _) (actOfL_spec _ l hl _ (galSpec_comp x σ))).trans ?_
    exact (Category.assoc _ _ _).trans (congrArg (fun φ => l ≫ φ) (act_mul C _ _)))

variable (Λ : Type) [CommRing Λ] {V : Type} [AddCommGroup V] [Module Λ V] (ρ : Representation Λ C.G V)

/-- **The stalk of `F_V` at a geometric point `s` of `X` with a lift `l` to `Y` is `V`.** -/
def stalkFVAt (s : GeomPt (SX A)) (l : Spec (CommRingCat.of s.Ω) ⟶ SY C) (hl : l ≫ pr C = s.pt) :
    (s.stalkF Λ).obj (FV C Λ ρ) ≅ ModuleCat.of Λ V :=
  eqToIso (congrArg (fun p : GeomPt (SX A) => (p.stalkF Λ).obj (FV C Λ ρ)) (liftPt_map s l hl).symm) ≪≫
    stalkFV Λ ρ (liftPt s l)

theorem stalkAut_stalkFVAt_mk (Ω : Type) [Field Ω] [IsSepClosed Ω] (pt : Spec (CommRingCat.of Ω) ⟶ SX A)
    (l : Spec (CommRingCat.of Ω) ⟶ SY C) (hl : l ≫ pr C = pt)
    (τ : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of Ω)) (hτ : τ ≫ pt = pt) (v : V) :
    (((GeomPt.mk Ω pt).stalkAut Λ τ hτ).app (FV C Λ ρ)).hom ((stalkFVAt Λ ρ (GeomPt.mk Ω pt) l hl).inv.hom v) =
      (stalkFVAt Λ ρ (GeomPt.mk Ω pt) l hl).inv.hom (ρ (actOfL (GeomPt.mk Ω pt) l hl τ hτ) v) := by
  subst hl
  exact stalkAut_stalkFV Λ ρ (liftPt (GeomPt.mk Ω (l ≫ pr C)) l) τ hτ v

/-- **Equivariance at any geometric point**: `τ` over `X` acts on `(F_V)_s` by `ρ (actOfL τ)`. -/
theorem stalkAut_stalkFVAt (s : GeomPt (SX A)) (l : Spec (CommRingCat.of s.Ω) ⟶ SY C) (hl : l ≫ pr C = s.pt)
    (τ : Spec (CommRingCat.of s.Ω) ⟶ Spec (CommRingCat.of s.Ω)) (hτ : τ ≫ s.pt = s.pt) (v : V) :
    ((s.stalkAut Λ τ hτ).app (FV C Λ ρ)).hom ((stalkFVAt Λ ρ s l hl).inv.hom v) =
      (stalkFVAt Λ ρ s l hl).inv.hom (ρ (actOfL s l hl τ hτ) v) :=
  stalkAut_stalkFVAt_mk Λ ρ s.Ω s.pt l hl τ hτ v

/-- **The Galois representation on `(F_V)_x̄` is `ρ ∘ galFV`** (inverse form). -/
theorem galRep_FV (x : SX A) (l : Spec (CommRingCat.of (geomPtAt x).Ω) ⟶ SY C)
    (hl : l ≫ pr C = (geomPtAt x).pt) (σ : Gal x) (v : V) :
    galRep Λ (FV C Λ ρ) x σ ((stalkFVAt Λ ρ (geomPtAt x) l hl).inv.hom v) =
      (stalkFVAt Λ ρ (geomPtAt x) l hl).inv.hom (ρ (galFV x l hl σ) v) :=
  stalkAut_stalkFVAt Λ ρ (geomPtAt x) l hl (galSpec x σ) (galSpec_comp x σ) v

/-- **The Galois representation on `(F_V)_x̄` is `ρ ∘ galFV`**: `e (σ • w) = ρ (galFV σ) (e w)`. -/
theorem stalkFVAt_galRep (x : SX A) (l : Spec (CommRingCat.of (geomPtAt x).Ω) ⟶ SY C)
    (hl : l ≫ pr C = (geomPtAt x).pt) (σ : Gal x) (w : stalk Λ (FV C Λ ρ) x) :
    (stalkFVAt Λ ρ (geomPtAt x) l hl).hom.hom (galRep Λ (FV C Λ ρ) x σ w) =
      ρ (galFV x l hl σ) ((stalkFVAt Λ ρ (geomPtAt x) l hl).hom.hom w) :=
  iso_conj Λ (stalkFVAt Λ ρ (geomPtAt x) l hl) (galRep Λ (FV C Λ ρ) x σ) (ρ (galFV x l hl σ))
    (galRep_FV Λ ρ x l hl σ) w

end RamanujanPetersson.EtSheaves.TorSec

end

end

-- ===== S4.Def_RP_EtSheaves_ChartSch =====
section

/-!
# S4-EtSheaves, O10f part e2: charts for lisse sheaves on `Spec A`

Let `A` be a noetherian integrally closed domain and `G` a lisse etale sheaf on `Spec A`. Then `G` has charts at the
generic point (`hChart`): every point `u` of every etale `U → Spec A` has an etale neighbourhood `T → Spec A` over `U`
on which `G` is constant and which has at most one point over the generic point.

Proof: take a trivialising `U₁ → Spec A` for `G` at the image of `u`, a point `p` of `U ×_{Spec A} U₁` over `u`, an
affine open `Spec R ⊆ U ×_{Spec A} U₁` around `p` (`R` is etale over `A`), and the localisation
`Spec (R_{f₀})_{f₁} ⊆ Spec R` of `ChartAlg.exists_chartAlg` (`chart_of` assembles the chart).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtSheaves

universe u

namespace ChartSch

section Abstract

variable {Λ : Type u} [CommRing Λ] {X : Scheme.{u}} (x0 : X) {G : EtSh Λ X}

end Abstract

section Spec

variable (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsNoetherianRing A]
  {Λ : Type} [CommRing Λ]

/-- **Lisse sheaves on `Spec A` have charts at the generic point.** -/
theorem hChart (G : EtSh Λ (Spec (CommRingCat.of A))) (hG : IsLisse Λ G) :
    FullAbs.HChart (GenBr.genPt A) G := by
  intro U u
  have : Etale U.hom := U.prop
  obtain ⟨U₁, v₁, hv₁, M, -, ⟨e⟩⟩ := hG (U.hom u)
  have : Etale U₁.hom := U₁.prop
  obtain ⟨p, hp₁, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := U.hom) (g := U₁.hom) u v₁ hv₁.symm
  let 𝒱 := (pullback U.hom U₁.hom).affineOpenCover
  obtain ⟨q, hq⟩ := 𝒱.covers p
  let b1 := 𝒱.f (𝒱.idx p)
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (b1 ≫ pullback.snd U.hom U₁.hom ≫ U₁.hom)
  let _ : Algebra A (𝒱.X (𝒱.idx p)) := ψ.hom.toAlgebra
  have hEt : Etale (Spec.map ψ) := by rw [hψ]; infer_instance
  have : Algebra.Etale A (𝒱.X (𝒱.idx p)) :=
    RingHom.etale_algebraMap.1 ((HasRingHomProperty.Spec_iff (P := @Etale)).1 hEt)
  have hqP : q.asIdeal.IsPrime := q.isPrime
  obtain ⟨f₀, f₁, P₀, hP₀, huniq⟩ := ChartAlg.exists_chartAlg (A := A) (R := 𝒱.X (𝒱.idx p)) q.asIdeal
  have hin : Spec.map (CommRingCat.ofHom (algebraMap (𝒱.X (𝒱.idx p)) (Localization.Away f₀)))
      (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away f₀) (Localization.Away f₁))) P₀) = q :=
    PrimeSpectrum.ext hP₀
  have key : ∀ w : Spec (CommRingCat.of (Localization.Away f₁)),
      U₁.hom (pullback.snd U.hom U₁.hom (b1
        (Spec.map (CommRingCat.ofHom (algebraMap (𝒱.X (𝒱.idx p)) (Localization.Away f₀)))
          (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away f₀) (Localization.Away f₁))) w)))) =
      Spec.map ψ (Spec.map (CommRingCat.ofHom (algebraMap (𝒱.X (𝒱.idx p)) (Localization.Away f₀)))
          (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away f₀) (Localization.Away f₁))) w)) := by
    intro w
    rw [hψ, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
  refine ChartSch.chart_of (GenBr.genPt A) u
    (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away f₀) (Localization.Away f₁))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (𝒱.X (𝒱.idx p)) (Localization.Away f₀))) ≫ b1) M e P₀ ?_ ?_
  · have h1 : pullback.fst U.hom U₁.hom (b1
        (Spec.map (CommRingCat.ofHom (algebraMap (𝒱.X (𝒱.idx p)) (Localization.Away f₀)))
          (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away f₀) (Localization.Away f₁))) P₀))) = u :=
      ((congrArg (pullback.fst U.hom U₁.hom) (congrArg b1 hin)).trans
        (congrArg (pullback.fst U.hom U₁.hom) hq)).trans hp₁
    exact h1
  · intro w₁ w₂ h₁ h₂
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at h₁ h₂
    have e₁ := congrArg PrimeSpectrum.asIdeal ((key w₁).symm.trans h₁)
    have e₂ := congrArg PrimeSpectrum.asIdeal ((key w₂).symm.trans h₂)
    exact huniq w₁ w₂ e₁ e₂

end Spec

end ChartSch

end RamanujanPetersson.EtSheaves

end

end

-- ===== S4.Def_RP_EtSheaves_GalGen =====
section

/-!
# S4-EtSheaves, part O10d-2(iv-c), generic point: `galFV` is `π₁ ↠ Gal(L/K)` after `genToPi1`

For a finite Galois subextension `L ⊆ K_U` unramified over `A` and its cover `C = coverOf L`
(`B` = integral closure of `A` in `L`, `G = Gal(L/K)`), restriction is a hom `resL : π₁ = Gal(K_U/K) →* G`
(`resL_spec`). The embedding `K_U → κ(η)^sep` of `GenBr` gives a lift `lGen : Spec κ(η)^sep → Spec B` of the
generic geometric point `η̄` (`hlGen`), and for it `galFV = resL ∘ genToPi1` (`galFV_gen`). Hence the Galois
representation on `(F_V)_η̄` is `ρ ∘ resL ∘ genToPi1` (`stalkFVGen_galRep`): it factors through `π₁`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory

noncomputable section

namespace RamanujanPetersson.EtSheaves.TorSec

open GenBr

attribute [local instance] GalCover.ring GalCover.dom GalCover.alg GalCover.inj GalCover.fin GalCover.grp GalCover.fG GalCover.act GalCover.gal genAlg genAlgSep genTower

theorem galFV_eq_iff {A : Type} [CommRing A] [IsDomain A] {C : GalCover A} (x : SX A)
    (l : Spec (CommRingCat.of (geomPtAt x).Ω) ⟶ SY C) (hl : l ≫ pr C = (geomPtAt x).pt) (σ : Gal x) (g : C.G) :
    galFV x l hl σ = g ↔ galSpec x σ ≫ l = l ≫ act C g :=
  actOfL_eq_iff _ l hl (galSpec x σ) (galSpec_comp x σ) g

variable (A K : Type) [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  [IsIntegrallyClosed A] [IsNoetherianRing A]
variable (L : IntermediateField K (AlgebraicClosure K)) (hL : L ∈ unramSet A K)

theorem le_maxUnram (hL' : L ∈ unramSet A K) : L ≤ maxUnram A K := by
  rw [maxUnram_eq_sSup]
  exact le_sSup hL'

/-- Restriction `π₁ = Gal(K_U/K) →* Gal(L/K)`, the group of `coverOf L`. -/
def resL : Pi1 A K →* (coverOf A K L hL).G :=
  haveI := hL.2.1
  letI : Algebra L (maxUnram A K) := (IntermediateField.inclusion (le_maxUnram A K L hL)).toAlgebra
  haveI : IsScalarTower K L (maxUnram A K) :=
    IsScalarTower.of_algHom (IntermediateField.inclusion (le_maxUnram A K L hL))
  AlgEquiv.restrictNormalHom L

theorem resL_spec (τ : Pi1 A K) (x : L) :
    IntermediateField.inclusion (le_maxUnram A K L hL) ((show L ≃ₐ[K] L from resL A K L hL τ) x) =
      τ (IntermediateField.inclusion (le_maxUnram A K L hL) x) := by
  haveI := hL.2.1
  letI : Algebra L (maxUnram A K) := (IntermediateField.inclusion (le_maxUnram A K L hL)).toAlgebra
  haveI : IsScalarTower K L (maxUnram A K) :=
    IsScalarTower.of_algHom (IntermediateField.inclusion (le_maxUnram A K L hL))
  exact τ.restrictNormal_commutes L x

/-- `B → K_U → κ(η)^sep`. -/
def gam : (coverOf A K L hL).B →+* SeparableClosure (genField A) :=
  (genEmb A K).comp ((IntermediateField.inclusion (le_maxUnram A K L hL)).toRingHom.comp
    (algebraMap (integralClosure A L) L))

/-- The lift of the generic geometric point `η̄` to `Spec B` given by `gam`. -/
def lGen : Spec (CommRingCat.of (geomPtAt (genPt A)).Ω) ⟶ SY (coverOf A K L hL) :=
  Spec.map (CommRingCat.ofHom (gam A K L hL))

theorem fracIso_algebraMap (a : A) :
    fracIso A K (algebraMap A K a) =
      (Scheme.Spec.residueFieldIso (CommRingCat.of A) (genPt A)).inv.hom (algebraMap A _ a) := by
  show (Scheme.Spec.residueFieldIso (CommRingCat.of A) (genPt A)).inv.hom
    (IsLocalization.algEquiv (nonZeroDivisors A) K (⊥ : Ideal A).ResidueField (algebraMap A K a)) = _
  rw [AlgEquiv.commutes]
  rfl

theorem gam_algebraMap (a : A) :
    IntermediateField.inclusion (le_maxUnram A K L hL) (algebraMap (integralClosure A L) L (algebraMap A _ a)) =
      algebraMap K (maxUnram A K) (algebraMap A K a) := by
  rw [← IsScalarTower.algebraMap_apply A (integralClosure A L) L, IsScalarTower.algebraMap_apply A K L,
    AlgHom.commutes]

theorem hlGen : lGen A K L hL ≫ pr (coverOf A K L hL) = (geomPtAt (genPt A)).pt := by
  change Spec.map (CommRingCat.ofHom (gam A K L hL)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap A (coverOf A K L hL).B)) =
    Spec.map (CommRingCat.ofHom (algebraMap (genField A) (SeparableClosure (genField A)))) ≫
      (Spec (CommRingCat.of A)).fromSpecResidueField (genPt A)
  refine (Spec.map_comp _ _).symm.trans ?_
  refine Eq.trans ?_ (congrArg (fun φ => Spec.map (CommRingCat.ofHom
    (algebraMap (genField A) (SeparableClosure (genField A)))) ≫ φ)
    (Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField (CommRingCat.of A) (genPt A)))
  refine Eq.trans ?_ (congrArg (fun φ => Spec.map (CommRingCat.ofHom
    (algebraMap (genField A) (SeparableClosure (genField A)))) ≫ φ) (Spec.map_comp _ _))
  refine Eq.trans ?_ (Spec.map_comp _ _)
  refine congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun a => ?_))
  exact (congrArg (genEmb A K) (gam_algebraMap A K L hL a)).trans ((genEmb_algebraMap A K _).trans
    (congrArg (algebraMap (genField A) (SeparableClosure (genField A))) (fracIso_algebraMap A K a)))

/-- **At the generic point, `galFV = resL ∘ genToPi1`**: the Galois action on `F_V` factors through `π₁`. -/
theorem galFV_gen (σ : Gal (genPt A)) :
    galFV (genPt A) (lGen A K L hL) (hlGen A K L hL) σ = resL A K L hL (genToPi1 A K σ) := by
  refine (galFV_eq_iff _ _ _ σ _).2 ?_
  change Spec.map (CommRingCat.ofHom (σ : SeparableClosure (genField A) →+* SeparableClosure (genField A))) ≫
      Spec.map (CommRingCat.ofHom (gam A K L hL)) =
    Spec.map (CommRingCat.ofHom (gam A K L hL)) ≫
      Spec.map (CommRingCat.ofHom (rh (coverOf A K L hL) (resL A K L hL (genToPi1 A K σ))))
  refine (Spec.map_comp _ _).symm.trans (Eq.trans ?_ (Spec.map_comp _ _))
  refine congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun b => ?_))
  exact (genEmb_genToPi1 A K σ _).symm.trans (congrArg (genEmb A K) (resL_spec A K L hL _ _).symm)

variable (Λ : Type) [CommRing Λ] {V : Type} [AddCommGroup V] [Module Λ V]
  (ρ : Representation Λ (coverOf A K L hL).G V)

/-- **The Galois representation on `(F_V)_η̄` is `ρ ∘ resL ∘ genToPi1`.** -/
theorem stalkFVGen_galRep (σ : Gal (genPt A)) (w : stalk Λ (FV (coverOf A K L hL) Λ ρ) (genPt A)) :
    (stalkFVAt Λ ρ (geomPtAt (genPt A)) (lGen A K L hL) (hlGen A K L hL)).hom.hom
        (galRep Λ (FV (coverOf A K L hL) Λ ρ) (genPt A) σ w) =
      ρ (resL A K L hL (genToPi1 A K σ))
        ((stalkFVAt Λ ρ (geomPtAt (genPt A)) (lGen A K L hL) (hlGen A K L hL)).hom.hom w) := by
  rw [stalkFVAt_galRep, galFV_gen]

end RamanujanPetersson.EtSheaves.TorSec

end

end

-- ===== S4.Def_RP_EtSheaves_GalSurj =====
section

/-!
# S4-EtSheaves, part O10e(i): every finite continuous `π₁`-representation is the generic fibre of a lisse sheaf

For `π₁ = Pi1 A K = Gal(K_U/K)` and a finite unramified Galois `L ⊆ K_U` with cover `C = coverOf L`:
* `resL_surjective`, `isOpen_ker_resL`: restriction `resL : π₁ ↠ Gal(L/K)` is onto with open kernel;
* `exists_resL_ker_le`: every open subgroup of `π₁` contains `ker resL` for some such `L`;
* `factorRep`: a representation `ρ'` of `π₁` with `ker resL ≤ ker ρ'` factors as `ρ ∘ resL` (`factorRep_resL`);
* `isOpen_ker_piRep`: for every `G`-module `V`, the `π₁`-representation `ρ ∘ resL` has open kernel;
* **`exists_lisse_of_rep`**: a representation of `π₁` on a finite `Λ`-module with open kernel is, up to
  isomorphism of the stalk, the Galois representation on the generic stalk `(F_V)_η̄` of the lisse sheaf `F_V`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory

noncomputable section

namespace RamanujanPetersson.EtSheaves.TorSec

open GenBr

attribute [local instance] GalCover.ring GalCover.dom GalCover.alg GalCover.inj GalCover.fin GalCover.grp GalCover.fG GalCover.act GalCover.gal genAlg genAlgSep genTower

variable (A K : Type) [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  [IsIntegrallyClosed A] [IsNoetherianRing A]

theorem resL_surjective (L : IntermediateField K (AlgebraicClosure K)) (hL : L ∈ unramSet A K) :
    Function.Surjective (resL A K L hL) := by
  haveI := hL.2.1
  letI : Algebra L (maxUnram A K) := (IntermediateField.inclusion (le_maxUnram A K L hL)).toAlgebra
  haveI : IsScalarTower K L (maxUnram A K) :=
    IsScalarTower.of_algHom (IntermediateField.inclusion (le_maxUnram A K L hL))
  exact AlgEquiv.restrictNormalHom_surjective (maxUnram A K)

theorem fix_of_resL_eq_one (L : IntermediateField K (AlgebraicClosure K)) (hL : L ∈ unramSet A K)
    (σ : Pi1 A K) (hσ : resL A K L hL σ = 1) (y : L) :
    σ (IntermediateField.inclusion (le_maxUnram A K L hL) y) =
      IntermediateField.inclusion (le_maxUnram A K L hL) y := by
  have h1 : (show L ≃ₐ[K] L from resL A K L hL σ) = 1 := hσ
  rw [← resL_spec A K L hL σ y, h1, AlgEquiv.one_apply]

/-- **Every open subgroup of `π₁` contains `ker (π₁ ↠ Gal(L/K))` for a finite unramified Galois `L`.** -/
theorem exists_resL_ker_le (N : Subgroup (Pi1 A K)) (hN : IsOpen (N : Set (Pi1 A K))) :
    ∃ (L : IntermediateField K (AlgebraicClosure K)) (hL : L ∈ unramSet A K), (resL A K L hL).ker ≤ N := by
  classical
  obtain ⟨E, hE, hEN⟩ :=
    (krullTopology_mem_nhds_one_iff K (maxUnram A K) N).mp (hN.mem_nhds N.one_mem)
  have hfg : E.FG := by
    apply IntermediateField.fg_of_fg_toSubalgebra
    apply Subalgebra.fg_of_fg_toSubmodule
    exact (Submodule.fg_iff_finiteDimensional _).mpr hE
  obtain ⟨t, htfin, hadj⟩ := IntermediateField.fg_def.mp hfg
  obtain ⟨L, hL, hle⟩ := exists_unramSet_of_finite A K
    (htfin.toFinset.image (fun x : maxUnram A K => (x : AlgebraicClosure K))) (by
      intro x hx
      obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hx
      exact y.2)
  refine ⟨L, hL, ?_⟩
  intro σ hσ
  have hσ' : resL A K L hL σ = 1 := MonoidHom.mem_ker.mp hσ
  apply hEN
  have hgen : ∀ x ∈ t, σ x = x := by
    intro x hx
    have hxL : (x : AlgebraicClosure K) ∈ L := by
      apply hle
      apply IntermediateField.subset_adjoin
      exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨x, htfin.mem_toFinset.mpr hx, rfl⟩)
    have hx' : x = IntermediateField.inclusion (le_maxUnram A K L hL) ⟨x, hxL⟩ := Subtype.ext rfl
    rw [hx']
    exact fix_of_resL_eq_one A K L hL σ hσ' ⟨x, hxL⟩
  have hEfix : E ≤ IntermediateField.fixedField (Subgroup.zpowers σ) := by
    rw [← hadj, IntermediateField.adjoin_le_iff]
    intro x hx
    rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
    intro g hg
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    induction n using Int.induction_on with
    | zero => simp
    | succ n ih => rw [zpow_add_one, AlgEquiv.mul_apply, hgen x hx, ih (Subgroup.zpow_mem_zpowers σ _)]
    | pred n ih =>
      have hinv : σ⁻¹ x = x := by
        conv_lhs => rw [← hgen x hx]
        rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
      rw [zpow_sub_one, AlgEquiv.mul_apply, hinv, ih (Subgroup.zpow_mem_zpowers σ _)]
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  exact (IntermediateField.mem_fixedField_iff _ _).mp (hEfix hx) σ (Subgroup.mem_zpowers σ)

variable {A K} (L : IntermediateField K (AlgebraicClosure K)) (hL : L ∈ unramSet A K)
variable (Λ : Type) [CommRing Λ] {V : Type} [AddCommGroup V] [Module Λ V]

/-- A representation of `π₁` killed by `ker resL` descends to `Gal(L/K)`. -/
def factorRep (ρ' : Representation Λ (Pi1 A K) V) (hk : (resL A K L hL).ker ≤ ρ'.ker) :
    Representation Λ (coverOf A K L hL).G V :=
  (QuotientGroup.lift (resL A K L hL).ker ρ' hk).comp
    (QuotientGroup.quotientKerEquivOfSurjective (resL A K L hL) (resL_surjective A K L hL)).symm.toMonoidHom

theorem factorRep_resL (ρ' : Representation Λ (Pi1 A K) V) (hk : (resL A K L hL).ker ≤ ρ'.ker)
    (σ : Pi1 A K) : factorRep L hL Λ ρ' hk (resL A K L hL σ) = ρ' σ := by
  have h : (QuotientGroup.quotientKerEquivOfSurjective (resL A K L hL) (resL_surjective A K L hL)).symm
      (resL A K L hL σ) = (σ : Pi1 A K ⧸ (resL A K L hL).ker) :=
    (MulEquiv.symm_apply_eq _).mpr rfl
  simp only [factorRep, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h]
  rfl

variable (A K)

end RamanujanPetersson.EtSheaves.TorSec

end

end

-- ===== S4.Def_RP_EtSheaves_Plumb =====
section

/-!
# S4-EtSheaves, O10c part 4: from `IsLisse` to a standard etale chart

`κ(η)^sep` is an `A`-algebra through `A → κ(η)` (`genAlgA`), and `Spec` of this map is the generic geometric point
`η̄` (`spec_algebraMap`). For a lisse `F` on `Spec A` and a prime `P` of `A` there are a standard etale `A`-algebra
`R'` and a prime `u` of `R'` over `P` such that every `σ ∈ Gal(κ(η)^sep/κ(η))` fixing the image of an `A`-algebra
map `ψ : R' → κ(η)^sep` acts trivially on the generic stalk `F_η̄` (`exists_chart`).
-/

set_option autoImplicit false
set_option warn.classDefReducibility false

open AlgebraicGeometry CategoryTheory

noncomputable section

namespace RamanujanPetersson.EtSheaves.Plumb

open GenBr

variable (A : Type) [CommRing A] [IsDomain A]

/-- The map `A → κ(η)` to the residue field at the generic point. -/
def toGen : A →+* genField A :=
  (Scheme.Spec.residueFieldIso (CommRingCat.of A) (genPt A)).inv.hom.comp
    (algebraMap A (genPt A).asIdeal.ResidueField)

/-- `κ(η)^sep` as an `A`-algebra through `κ(η)`. -/
def genAlgA : Algebra A (SeparableClosure (genField A)) :=
  ((algebraMap (genField A) (SeparableClosure (genField A))).comp (toGen A)).toAlgebra

attribute [local instance] genAlgA

theorem genAlgA_apply (a : A) :
    algebraMap A (SeparableClosure (genField A)) a =
      algebraMap (genField A) (SeparableClosure (genField A)) (toGen A a) := rfl

/-- `Spec (A → κ(η)^sep)` is the generic geometric point `η̄`. -/
theorem spec_algebraMap :
    Spec.map (CommRingCat.ofHom (algebraMap A (SeparableClosure (genField A)))) =
      (geomPtAt (genPt A)).pt := by
  change _ = Spec.map (CommRingCat.ofHom (algebraMap (genField A) (SeparableClosure (genField A)))) ≫
    (Spec (CommRingCat.of A)).fromSpecResidueField (genPt A)
  rw [← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField, ← Spec.map_comp, ← Spec.map_comp]
  rfl

/-- **HEADLINE (O10c, F4)**: a lisse `F` on `Spec A` has, over every prime `P`, a standard etale chart
`A → R'` with a prime `u` over `P`, such that any `σ` fixing an `A`-point `ψ : R' → κ(η)^sep` acts trivially on
`F_η̄`. -/
theorem exists_chart {Λ : Type} [CommRing Λ] (F : EtSh Λ (Spec (CommRingCat.of A))) (hF : IsLisse Λ F)
    (P : PrimeSpectrum A) :
    ∃ (R' : Type) (_ : CommRing R') (_ : Algebra A R') (_ : StandardEtalePresentation A R') (u : Ideal R'),
      u.IsPrime ∧ u.comap (algebraMap A R') = P.asIdeal ∧
      ∀ (ψ : R' →ₐ[A] SeparableClosure (genField A)) (σ : Gal (genPt A)), (∀ r, σ (ψ r) = ψ r) →
        galRep Λ F (genPt A) σ = LinearMap.id := by
  obtain ⟨U, v, hv, M, -, ⟨e⟩⟩ := hF P
  obtain ⟨_, ⟨V, hV, rfl⟩, hvV, -⟩ :=
    U.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ v) isOpen_univ
  have hV' : IsAffineOpen V := hV
  have : Etale U.hom := U.prop
  let φ : CommRingCat.of A ⟶ Γ(U.left, V) := Spec.preimage (hV'.fromSpec ≫ U.hom)
  have hφ : hV'.fromSpec ≫ U.hom = Spec.map φ := (Spec.map_preimage _).symm
  have hφe : φ.hom.Etale := by
    rw [← HasRingHomProperty.Spec_iff (P := @Etale), ← hφ]
    infer_instance
  let _ : Algebra A Γ(U.left, V) := φ.hom.toAlgebra
  have : Algebra.Etale A Γ(U.left, V) := hφe
  let w : PrimeSpectrum Γ(U.left, V) := hV'.primeIdealOf ⟨v, hvV⟩
  have hw : hV'.fromSpec w = v := hV'.fromSpec_primeIdealOf ⟨v, hvV⟩
  have : w.asIdeal.IsPrime := w.isPrime
  have : Algebra.IsEtaleAt A w.asIdeal :=
    Algebra.FormallyEtale.comp A Γ(U.left, V) (Localization.AtPrime w.asIdeal)
  obtain ⟨f, hfw, hstd⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := A) w.asIdeal
  have hdisj : Disjoint (Submonoid.powers f : Set Γ(U.left, V)) w.asIdeal :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime _).mpr hfw
  have hPw : (Spec.map φ) w = P := by
    rw [← hφ]
    change U.hom (hV'.fromSpec w) = P
    rw [hw, hv]
  refine ⟨Localization.Away f, inferInstance, inferInstance, hstd.nonempty_standardEtalePresentation.some,
    w.asIdeal.map (algebraMap Γ(U.left, V) (Localization.Away f)),
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers f) _ w.asIdeal w.isPrime hdisj, ?_, ?_⟩
  · rw [IsScalarTower.algebraMap_eq A Γ(U.left, V) (Localization.Away f), ← Ideal.comap_comap]
    have h1 := IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers f) (Localization.Away f)
      w.isPrime hdisj
    rw [Ideal.under] at h1
    rw [h1, ← hPw]
    rfl
  · intro ψ σ hσ
    have hl : (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap Γ(U.left, V) (Localization.Away f))) ≫ hV'.fromSpec) ≫
          U.hom = (geomPtAt (genPt A)).pt := by
      rw [Category.assoc, Category.assoc, hφ, ← Spec.map_comp, ← Spec.map_comp, ← spec_algebraMap A]
      congr 1
      refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
      change ψ (algebraMap Γ(U.left, V) (Localization.Away f) (algebraMap A Γ(U.left, V) a)) = _
      rw [← IsScalarTower.algebraMap_apply A Γ(U.left, V) (Localization.Away f)]
      exact ψ.commutes a
    refine galRep_eq_id_of_etale F (genPt A) U M e _ hl σ ?_
    rw [galSpec, ← Category.assoc, ← Spec.map_comp]
    refine congrArg (· ≫ _) (congrArg Spec.map ?_)
    exact CommRingCat.hom_ext (RingHom.ext fun r => hσ r)

end RamanujanPetersson.EtSheaves.Plumb

end

end

-- ===== S4.Def_RP_EtSheaves_InertiaFix =====
section

/-!
# S4-EtSheaves, O10c part 2a: an inertia element fixes a prime of `B ⊗[A] R'` over `(0)`

Let `τ : B ≃ₐ[A] B` satisfy `τ b - b ∈ Q` for all `b` (an inertia element at `Q`), and let `𝔮` be a
prime of `S = B ⊗[A] R'` containing `Q ⊗ 1`. Then `τ ⊗ 1` maps `𝔮` to itself. If moreover `B` is an
integrally closed domain and `R'` is standard etale over `A`, a minimal prime `𝔭 ≤ 𝔮` of `S` lies
over `(0)` (flatness) and is fixed by `τ ⊗ 1` (unibranch property, part 1).
-/

set_option autoImplicit false

open TensorProduct

noncomputable section

namespace RamanujanPetersson.EtSheaves.InertiaFix

variable {A B R' : Type*} [CommRing A] [CommRing B] [CommRing R'] [Algebra A B] [Algebra A R']

/-- The automorphism `τ ⊗ 1` of `B ⊗[A] R'`. -/
abbrev tauT (τ : B ≃ₐ[A] B) : B ⊗[A] R' ≃ₐ[A] B ⊗[A] R' :=
  Algebra.TensorProduct.congr τ AlgEquiv.refl

theorem tauT_tmul (τ : B ≃ₐ[A] B) (b : B) (r : R') : tauT τ (b ⊗ₜ r) = τ b ⊗ₜ r := by
  simp [tauT]

theorem tauT_algebraMap (τ : B ≃ₐ[A] B) (b : B) :
    tauT (R' := R') τ (algebraMap B (B ⊗[A] R') b) = algebraMap B (B ⊗[A] R') (τ b) := by
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply,
    Algebra.algebraMap_self, RingHom.id_apply, RingHom.id_apply, tauT_tmul]

/-- `τ ⊗ 1` moves every element by an element of `𝔮` when `τ` is in the inertia group of `Q`. -/
theorem sub_mem (τ : B ≃ₐ[A] B) (Q : Ideal B) (hτ : ∀ b, τ b - b ∈ Q)
    (𝔮 : Ideal (B ⊗[A] R')) (h𝔮 : ∀ b ∈ Q, b ⊗ₜ[A] (1 : R') ∈ 𝔮) (s : B ⊗[A] R') :
    tauT τ s - s ∈ 𝔮 := by
  induction s using TensorProduct.induction_on with
  | zero => simp
  | tmul b r =>
    rw [tauT_tmul, ← sub_tmul]
    have e : (τ b - b) ⊗ₜ[A] r = ((τ b - b) ⊗ₜ[A] (1 : R')) * ((1 : B) ⊗ₜ r) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [e]
    exact 𝔮.mul_mem_right _ (h𝔮 _ (hτ b))
  | add x y hx hy =>
    rw [map_add, add_sub_add_comm]
    exact 𝔮.add_mem hx hy

/-- HEADLINE: an inertia element at `Q` fixes every prime of `B ⊗[A] R'` containing `Q ⊗ 1`. -/
theorem comap_tauT_eq (τ : B ≃ₐ[A] B) (Q : Ideal B) (hτ : ∀ b, τ b - b ∈ Q)
    (𝔮 : Ideal (B ⊗[A] R')) (h𝔮 : ∀ b ∈ Q, b ⊗ₜ[A] (1 : R') ∈ 𝔮) :
    𝔮.comap (tauT τ) = 𝔮 := by
  ext s
  have h := sub_mem τ Q hτ 𝔮 h𝔮 s
  rw [Ideal.mem_comap]
  constructor
  · intro hs
    simpa using 𝔮.sub_mem hs h
  · intro hs
    simpa using 𝔮.add_mem h hs

/-- Minimal primes of a flat algebra over a domain lie over `(0)`. -/
theorem comap_eq_bot_of_mem_minimalPrimes {B S : Type*} [CommRing B] [IsDomain B] [CommRing S]
    [Algebra B S] [Module.Flat B S] {𝔭 : Ideal S} (h𝔭 : 𝔭 ∈ minimalPrimes S) :
    𝔭.comap (algebraMap B S) = ⊥ := by
  rw [eq_bot_iff]
  intro b hb
  rw [Ideal.mem_comap] at hb
  rw [Ideal.mem_bot]
  by_contra hb0
  have hreg : IsSMulRegular S b :=
    Module.Flat.isSMulRegular_of_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hb0)
  have hnz : algebraMap B S b ∈ nonZeroDivisors S := by
    rw [mem_nonZeroDivisors_iff_right]
    intro x hx
    refine hreg ?_
    show b • x = b • (0 : S)
    rw [smul_zero, Algebra.smul_def, mul_comm, hx]
  exact Set.disjoint_left.mp (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes h𝔭) hb hnz

/-- HEADLINE: an inertia element at `Q` fixes a prime of `B ⊗[A] R'` over `(0)` below `𝔮`. -/
theorem exists_fixed_prime [IsDomain B] [IsIntegrallyClosed B] (P0 : StandardEtalePresentation A R')
    (τ : B ≃ₐ[A] B) (Q : Ideal B) (hτ : ∀ b, τ b - b ∈ Q) (𝔮 : Ideal (B ⊗[A] R')) [𝔮.IsPrime]
    (h𝔮 : ∀ b ∈ Q, b ⊗ₜ[A] (1 : R') ∈ 𝔮) :
    ∃ 𝔭 : Ideal (B ⊗[A] R'), 𝔭.IsPrime ∧ 𝔭 ≤ 𝔮 ∧ 𝔭.comap (algebraMap B (B ⊗[A] R')) = ⊥ ∧
      𝔭.comap (tauT τ) = 𝔭 := by
  haveI : Algebra.IsStandardEtale A R' := ⟨⟨P0⟩⟩
  haveI : Module.Flat A R' := inferInstance
  obtain ⟨𝔭, h𝔭, h𝔭q⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal (B ⊗[A] R'))) (J := 𝔮)
    bot_le
  haveI : 𝔭.IsPrime := h𝔭.1.1
  have h0 : 𝔭.comap (algebraMap B (B ⊗[A] R')) = ⊥ := comap_eq_bot_of_mem_minimalPrimes h𝔭
  refine ⟨𝔭, inferInstance, h𝔭q, h0, ?_⟩
  refine Unibranch.unibranch (P0.baseChange (T := B)) (𝔮 := 𝔮) ?_ h𝔭q ?_ h0
  · calc 𝔭.comap (tauT τ) ≤ 𝔮.comap (tauT τ) := Ideal.comap_mono h𝔭q
      _ = 𝔮 := comap_tauT_eq τ Q hτ 𝔮 h𝔮
  · ext b
    simp only [Ideal.mem_comap, Ideal.mem_bot]
    rw [tauT_algebraMap, ← Ideal.mem_comap, h0, Ideal.mem_bot, map_eq_zero_iff τ τ.injective]

end RamanujanPetersson.EtSheaves.InertiaFix

end

end

-- ===== S4.Def_RP_EtSheaves_FibreNe =====
section

/-!
# S4-EtSheaves, O10c part 2b: a prime of `B ⊗[A] R'` containing `Q ⊗ 1`

If `Q ⊂ B` and `u ⊂ R'` are primes over the same prime of `A`, then `(B ⧸ Q) ⊗[A ⧸ P] (R' ⧸ u)` is
nonzero (tensor product of two domains over a common subring), so `Q ⊗ 1` lies in a prime of
`B ⊗[A] R'`.
-/

set_option autoImplicit false

open TensorProduct

noncomputable section

namespace RamanujanPetersson.EtSheaves.FibreNe

variable {A B R' : Type*} [CommRing A] [CommRing B] [CommRing R'] [Algebra A B] [Algebra A R']

/-- HEADLINE: primes over a common prime of `A` give a prime of `B ⊗[A] R'` containing `Q ⊗ 1`. -/
theorem exists_prime_tmul (Q : Ideal B) [Q.IsPrime] (u : Ideal R') [u.IsPrime]
    (h : u.comap (algebraMap A R') = Q.comap (algebraMap A B)) :
    ∃ 𝔮 : Ideal (B ⊗[A] R'), 𝔮.IsPrime ∧ ∀ b ∈ Q, b ⊗ₜ[A] (1 : R') ∈ 𝔮 := by
  obtain ⟨P, hP⟩ : ∃ P : Ideal A, P = Q.comap (algebraMap A B) := ⟨_, rfl⟩
  haveI : Q.LiesOver P := ⟨hP⟩
  haveI : u.LiesOver P := ⟨hP.trans h.symm⟩
  haveI : Nontrivial ((B ⧸ Q) ⊗[A ⧸ P] (R' ⧸ u)) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain (A ⧸ P) (B ⧸ Q) (R' ⧸ u)
      (FaithfulSMul.algebraMap_injective _ _) (FaithfulSMul.algebraMap_injective _ _)
  letI : CompatibleSMul (A ⧸ P) A (B ⧸ Q) (R' ⧸ u) := CompatibleSMul.isScalarTower
  let φ : B ⊗[A] R' →ₐ[A] (B ⧸ Q) ⊗[A ⧸ P] (R' ⧸ u) :=
    (Algebra.TensorProduct.mapOfCompatibleSMul (A ⧸ P) A A (B ⧸ Q) (R' ⧸ u)).comp
      (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ A Q) (Ideal.Quotient.mkₐ A u))
  obtain ⟨M, hM⟩ := Ideal.exists_maximal ((B ⧸ Q) ⊗[A ⧸ P] (R' ⧸ u))
  refine ⟨M.comap φ, Ideal.comap_isPrime _ _, fun b hb => ?_⟩
  have hb0 : Ideal.Quotient.mk Q b = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hb
  rw [Ideal.mem_comap]
  have e : φ (b ⊗ₜ 1) = 0 := by
    simp only [φ, AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, Ideal.Quotient.mkₐ_eq_mk, hb0,
      TensorProduct.zero_tmul, map_zero]
  rw [e]
  exact M.zero_mem

end RamanujanPetersson.EtSheaves.FibreNe

end

end

-- ===== S4.Def_RP_EtSheaves_InertiaLift =====
section

/-!
# S4-EtSheaves, O10c part 2c: lifting an inertia element to the separable closure

For a prime `𝔭` of `S = B ⊗[A] R'` over `(0)` fixed by `τ ⊗ 1`, the field `E = Frac (S ⧸ 𝔭)` is
separable over `L = Frac B` (it is generated by a simple root of `f`), and `τ ⊗ 1` induces
`τ_E ∈ Aut(E/K)`. Embedding `E` into a separably closed normal `Ω/K` and extending `τ_E` gives
`τ' ∈ Aut(Ω/K)` that fixes the image of `R'` and restricts to `τ` on `L`.
-/

set_option autoImplicit false

open Polynomial TensorProduct

noncomputable section

namespace RamanujanPetersson.EtSheaves.InertiaLift

/-- A root `θ` of `f` with `f'(θ) ≠ 0` is separable. -/
theorem isSeparable_root {L E : Type*} [Field L] [Field E] [Algebra L E] (θ : E) (f : L[X])
    (hf : aeval θ f = 0) (hf' : aeval θ (derivative f) ≠ 0) : IsSeparable L θ := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    simp at hf'
  have hint : IsIntegral L θ := isAlgebraic_iff_isIntegral.mp ⟨f, hf0, hf⟩
  obtain ⟨h, hh⟩ := minpoly.dvd L θ hf
  show (minpoly L θ).Separable
  rw [separable_iff_derivative_ne_zero (minpoly.irreducible hint)]
  intro hd
  apply hf'
  rw [hh, derivative_mul, hd, zero_mul, zero_add, map_mul, minpoly.aeval, zero_mul]

/-- Embed a separable `E/K` into a separably closed normal `Ω/K` and extend `σ ∈ Aut(E/K)`. -/
theorem exists_lift_aut {K E Ω : Type*} [Field K] [Field E] [Field Ω] [Algebra K E] [Algebra K Ω]
    [Algebra.IsSeparable K E] [IsSepClosed Ω] [Normal K Ω] (σ : E ≃ₐ[K] E) :
    ∃ j : E →ₐ[K] Ω, ∃ τ : Ω ≃ₐ[K] Ω, ∀ e, τ (j e) = j (σ e) := by
  let j : E →ₐ[K] Ω := IsSepClosed.lift
  letI : Algebra E Ω := j.toRingHom.toAlgebra
  haveI : IsScalarTower K E Ω := IsScalarTower.of_algebraMap_eq (fun k => (j.commutes k).symm)
  exact ⟨j, σ.liftNormal Ω, fun e => σ.liftNormal_commutes Ω e⟩

variable {A K L B R' : Type*} [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K]
  [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
  [CommRing B] [IsDomain B] [Algebra A B] [Algebra B L] [IsScalarTower A B L] [IsFractionRing B L]
  [CommRing R'] [Algebra A R']

/-- The function field `Frac (S ⧸ 𝔭)` of the branch `𝔭` of `S = B ⊗[A] R'`. -/
abbrev Fld (𝔭 : Ideal (B ⊗[A] R')) [𝔭.IsPrime] : Type _ := FractionRing (B ⊗[A] R' ⧸ 𝔭)

end RamanujanPetersson.EtSheaves.InertiaLift

end

end

-- ===== S4.Def_RP_EtSheaves_EssSurj =====
section

/-!
# S4-EtSheaves, O10f part f: lisse sheaves on `Spec A` are their generic Galois representations

`A` is a noetherian integrally closed domain with fraction field `K`, `η` the generic point of `Spec A`.
* `full`: every Galois-equivariant map of generic stalks `F_η̄ → G_η̄` (`G` lisse) is the stalk of a sheaf map;
* `fibRep`: the Galois action on the generic stalk of a lisse `F` factors through `π₁ = Pi1 A K`, with open kernel
  (`isOpen_ker_fibRep`);
* `nonempty_iso_of_stalk`: lisse sheaves with equivariantly isomorphic generic stalks are isomorphic;
* **`essSurj`**: every lisse `F` is isomorphic to the sheaf `F_V` of its fibre representation `V = F_η̄`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory

noncomputable section

namespace RamanujanPetersson.EtSheaves.EssSurj

open GenBr TorSec

attribute [local instance] GalCover.ring GalCover.dom GalCover.alg GalCover.inj GalCover.fin GalCover.grp GalCover.fG GalCover.act GalCover.gal genAlg genAlgSep genTower

section Full

variable (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsNoetherianRing A]
  {Λ : Type} [CommRing Λ]

/-- The generic point lies in every nonempty open subset of `Spec A`. -/
theorem genPt_mem (O : Set (Spec (CommRingCat.of A))) (hO : IsOpen O) (hne : O.Nonempty) : genPt A ∈ O := by
  rw [genPt_eq]
  exact ((genericPoint_spec (Spec (CommRingCat.of A))).mem_open_set_iff hO).2 (by simpa using hne)

end Full

section Rep

variable (A K : Type) [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  [IsIntegrallyClosed A] {Λ : Type} [CommRing Λ]

variable [IsNoetherianRing A]

end Rep

end RamanujanPetersson.EtSheaves.EssSurj

end

end


