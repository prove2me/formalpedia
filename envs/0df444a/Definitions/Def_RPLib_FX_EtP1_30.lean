-- Prove2me | Definitions.Def_RPLib_FX_EtP1_30
-- name    : RPLib_FX_EtP1_30
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T15:09:16.004493+00:00
-- url     : https://prove2.me/theorems/7aaf705d-4d81-5a2d-9a6c-06860e8069f5
-- title:
--   Étale cohomology of the projective line, library file 30 of 34
-- statement:
--   File 30 of 34 of the étale cohomology library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtCompact_P1Sky`: S4-EtCompact, E1b (O7b): `H¹` of point-supported sheaves on a union of two affines; `P¹`
--   * `S4.Def_RP_EtCompact_StkTr`: S4-EtCompact, E2 (O7b): stalks along an open immersion
--   * `S4.Def_RP_EtCompact_P1Clo`: S4-EtCompact, E3 (O7b): sheaves on `P¹` with zero generic stalk are acyclic
--   * `S4.Def_RP_EtCompact_P1H3`: S4-EtCompact, E4 (O7b): `H^(n+3)(P¹, F) = 0` for every sheaf `F`
--
--   **Formalization note.** One file of a library formalizing the étale cohomology of the projective line $\mathbf P^1_k = \operatorname{Proj} k[X_0, X_1]$ over an algebraically closed field $k$ with coefficients in sheaves of $\Lambda$-modules on the small étale site ($H^n = \operatorname{Ext}^n(\Lambda, -)$): $H^1(\mathbf P^1, \Lambda) = 0$, $H^2(\mathbf P^1, \Lambda) \cong \Lambda$ and $H^{n+3}(\mathbf P^1, F) = 0$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §1 (cohomology of curves) and Chapter III, §2 (Kummer theory); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Arcata », Chapter IV (cohomology of curves, Tsen's theorem)

import Mathlib
import Definitions.Def_RPLib_FX_EtP1_45

/-!
# Étale cohomology of the projective line, library file 30 of 34

Declarations of the formalization of the étale cohomology of the projective line over an algebraically
closed field (H¹ = 0, H² ≅ Λ, vanishing in degrees ≥ 3), re-hosted declaration by declaration from the
library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtCompact_P1Sky`: S4-EtCompact, E1b (O7b): `H¹` of point-supported sheaves on a union of two affines; `P¹`
* `S4.Def_RP_EtCompact_StkTr`: S4-EtCompact, E2 (O7b): stalks along an open immersion
* `S4.Def_RP_EtCompact_P1Clo`: S4-EtCompact, E3 (O7b): sheaves on `P¹` with zero generic stalk are acyclic
* `S4.Def_RP_EtCompact_P1H3`: S4-EtCompact, E4 (O7b): `H^(n+3)(P¹, F) = 0` for every sheaf `F`
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtCompact_P1Sky =====
section

/-!
# S4-EtCompact, E1b (O7b): `H¹` of point-supported sheaves on a union of two affines; `P¹`

* **`sections_surj_cover`**: for a short exact `0 → X₁ → X₂ → X₃ → 0` with `X₁` supported on closed points (Galois-trivial
  there), global sections of `X₂ → X₃` are surjective on `Y = U ∪ V` with `U`, `V`, `U ∩ V` affine;
* **`H1_eq_zero_of_cover`**: then `H¹(Y, X₁) = 0` (Cartan's argument with `0 → F → god F → Q → 0`);
* `P1.isLocallyNoetherian`; **`P1.H1_closed`**: `H¹(P¹, Z) = 0` when `Z` has zero stalk at the generic point.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open CategoryTheory Limits AlgebraicGeometry Opposite Abelian TopologicalSpace
open RamanujanPetersson.EtSheaves

noncomputable section

namespace RamanujanPetersson.EtCompact.Cech

universe u

variable {Λ : Type u} [CommRing Λ] {Y : Scheme.{u}}

/-- **`H¹ = 0` for point-supported sheaves on a union of two affines with affine intersection.** -/
theorem H1_eq_zero_of_cover [IsLocallyNoetherian Y] (F : EtSh Λ Y)
    (hF : ∀ y : Y, ¬ IsClosed ({y} : Set Y) → IsZero (Mx F y))
    (hG : ∀ y : Y, IsClosed ({y} : Set Y) → Subsingleton (Gal y))
    (U V : Y.Opens) (hUV : ∀ x : Y, x ∈ U ∨ x ∈ V) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hUVa : IsAffineOpen (U ⊓ V)) (e : H Λ F 1) : e = 0 := by
  have hT : IsTerminal (etId Y) := IsTerminal.ofUniqueHom
    (fun V => MorphismProperty.Over.homMk V.hom (Category.comp_id _))
    (fun V m => MorphismProperty.Over.Hom.ext ((Category.comp_id m.left).symm.trans (MorphismProperty.Over.w m)))
  have hE := godSC_shortExact F
  obtain ⟨x₃, rfl⟩ := Ext.covariant_sequence_exact₁ _ hE e (Ext.eq_zero_of_injective _)
    (show 0 + 1 = 0 + 1 from rfl)
  obtain ⟨a, ha⟩ := lift_unit hT (godSC Λ F).g
    (sections_surj_cover hE hF hG U V hUV hU hV hUVa) (Ext.homEquiv₀ x₃)
  have hx : x₃ = (Ext.mk₀ a).comp (Ext.mk₀ (godSC Λ F).g) (zero_add 0) := by
    rw [Ext.mk₀_comp_mk₀, ha, Ext.mk₀_homEquiv₀_apply]
  rw [hx, Ext.comp_assoc_of_second_deg_zero, hE.comp_extClass, Ext.comp_zero]

end RamanujanPetersson.EtCompact.Cech

namespace RamanujanPetersson.EtCompact.CurveHn

open RamanujanPetersson.EtCompact Polynomial

variable (k : Type) [Field k]

instance P1.isLocallyNoetherian : IsLocallyNoetherian (P1 k) := by
  have hA : IsNoetherianRing Γ(A1 k, ⊤) :=
    isNoetherianRing_of_ringEquiv _ (Scheme.ΓSpecIso (CommRingCat.of k[X])).symm.commRingCatIsoToRingEquiv
  let S : Bool → (P1 k).affineOpens := fun b =>
    cond b ⟨(chartA1 k).opensRange, isAffineOpen_opensRange _⟩ ⟨(chartA1' k).opensRange, isAffineOpen_opensRange _⟩
  refine isLocallyNoetherian_of_affine_cover (S := S) ?_ fun b => ?_
  · refine top_unique fun x _ => ?_
    rw [Opens.mem_iSup]
    rcases P1.cover k x with h | h
    · exact ⟨true, h⟩
    · exact ⟨false, h⟩
  · cases b
    · exact isNoetherianRing_of_ringEquiv _ (IsOpenImmersion.ΓIsoTop (chartA1' k)).commRingCatIsoToRingEquiv
    · exact isNoetherianRing_of_ringEquiv _ (IsOpenImmersion.ΓIsoTop (chartA1 k)).commRingCatIsoToRingEquiv

/-- **`H¹(P¹, Z) = 0`** when `Z` has zero stalk at the generic point. -/
theorem P1.H1_closed [IsAlgClosed k] {Λ : Type} [CommRing Λ] (Z : EtSh Λ (P1 k))
    (hη : IsZero (Cech.Mx Z (P1.genPt k))) (e : H Λ Z 1) : e = 0 := by
  refine Cech.H1_eq_zero_of_cover Z (fun y hy => ?_) (P1.gal_closed k) (chartA1 k).opensRange
    (chartA1' k).opensRange (P1.cover k) (isAffineOpen_opensRange _) (isAffineOpen_opensRange _) ?_ e
  · have : y = P1.genPt k := by
      by_contra h
      exact hy (P1.isClosed_of_ne_genPt k y h)
    rw [this]
    exact hη
  · rw [← P1.opensRange_chartGm]
    exact isAffineOpen_opensRange _

end RamanujanPetersson.EtCompact.CurveHn

end

end

-- ===== S4.Def_RP_EtCompact_StkTr =====
section

/-!
# S4-EtCompact, E2 (O7b): stalks along an open immersion

For an open immersion `j : U ⟶ X` and a point `t : U`:
* `mapPtIso j t`: the geometric points `geomPtAt t ≫ j` and `geomPtAt (j t)` are isomorphic;
* **`resStkIso`**: `(j^* F)_t ≅ F_(j t)`; **`lshStkIso`**: `(j_! G)_(j t) ≅ G_t` (naturally);
* `isZero_res`, `isZero_lsh_kernel`, `isZero_lsh_cokernel`: vanishing transfers along these isomorphisms;
* `isZero_cokernel_counit`: the cokernel of `j_! j^* F ⟶ F` vanishes at `j t`;
* **`pushStkIso`**: `((g ≫ j)_* M)_(j t) ≅ (g_* M)_t`, naturally in `M`; `epi_map_of_iso`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtCompact.StkTr

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact

universe u

/-- Epimorphisms transfer along an isomorphism of functors. -/
theorem epi_map_of_iso {C D : Type*} [Category C] [Category D] {Φ Ψ : C ⥤ D} (α : Φ ≅ Ψ) {A B : C}
    (f : A ⟶ B) (h : Epi (Ψ.map f)) : Epi (Φ.map f) := by
  rw [← NatIso.naturality_2 α f]
  infer_instance

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

theorem pt_map (t : U) : ((geomPtAt t).map j).pt =
    Spec.map (j.residueFieldMap t ≫ CommRingCat.ofHom (algebraMap (U.residueField t)
      (SeparableClosure (U.residueField t)))) ≫ X.fromSpecResidueField (j t) := by
  change (Spec.map (CommRingCat.ofHom (algebraMap (U.residueField t) (SeparableClosure (U.residueField t)))) ≫
    U.fromSpecResidueField t) ≫ j = _
  rw [Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← Category.assoc]
  exact congrArg (· ≫ X.fromSpecResidueField (j t)) (Spec.map_comp _ _).symm

theorem sep_map (t : U) : @Algebra.IsSeparable (X.residueField (j t)) (SeparableClosure (U.residueField t)) _ _
    (j.residueFieldMap t ≫ CommRingCat.ofHom (algebraMap (U.residueField t)
      (SeparableClosure (U.residueField t)))).hom.toAlgebra := by
  let _ : Algebra (X.residueField (j t)) (SeparableClosure (U.residueField t)) :=
    (j.residueFieldMap t ≫ CommRingCat.ofHom (algebraMap (U.residueField t)
      (SeparableClosure (U.residueField t)))).hom.toAlgebra
  refine Algebra.IsSeparable.of_equiv_equiv (A₁ := U.residueField t) (B₁ := SeparableClosure (U.residueField t))
    (asIso (j.residueFieldMap t)).symm.commRingCatIsoToRingEquiv (RingEquiv.refl _) ?_
  refine RingHom.ext fun r => ?_
  have e : (j.residueFieldMap t).hom ((inv (j.residueFieldMap t)).hom r) = r :=
    congrArg (fun f => f.hom r) (IsIso.inv_hom_id (j.residueFieldMap t))
  exact congrArg (algebraMap (U.residueField t) (SeparableClosure (U.residueField t))) e

/-- The geometric points `geomPtAt t ≫ j` and `geomPtAt (j t)` are isomorphic. -/
def mapPtIso (t : U) : ((geomPtAt t).map j).point ≅ (geomPtAt (j t)).point :=
  GPtIso.ptIso (GPtIso.overIsoGeomPtAt (j t) ((geomPtAt t).map j) _ (pt_map j t) (sep_map j t))

variable (Λ : Type u) [CommRing Λ]

/-- **`(j^* F)_t ≅ F_(j t)`**, naturally in `F`. -/
def resStkIso (t : U) : res j Λ ⋙ (geomPtAt t).stalkF Λ ≅ (geomPtAt (j t)).stalkF Λ :=
  resStalkIso j Λ (geomPtAt t) ≪≫ ptIsoSheafFiber Λ (mapPtIso j t).symm

/-- **`(j_! G)_(j t) ≅ G_t`**, naturally in `G`. -/
def lshStkIso (t : U) : lsh j Λ ⋙ (geomPtAt (j t)).stalkF Λ ≅ (geomPtAt t).stalkF Λ :=
  Functor.isoWhiskerLeft (lsh j Λ) (ptIsoSheafFiber Λ (mapPtIso j t)) ≪≫ lshStalkIso j Λ (geomPtAt t)

variable {Λ}

theorem isZero_res (F : EtSh Λ X) (t : U) (h : IsZero (stalk Λ F (j t))) :
    IsZero (stalk Λ ((res j Λ).obj F) t) :=
  h.of_iso ((resStkIso j Λ t).app F)

theorem isZero_lsh (G : EtSh Λ U) (t : U) (h : IsZero (stalk Λ G t)) :
    IsZero (stalk Λ ((lsh j Λ).obj G) (j t)) :=
  h.of_iso ((lshStkIso j Λ t).app G)

theorem isZero_lsh_kernel {G G' : EtSh Λ U} (φ : G ⟶ G') (t : U) (h : IsZero (stalk Λ (kernel φ) t)) :
    IsZero (stalk Λ (kernel ((lsh j Λ).map φ)) (j t)) :=
  (isZero_lsh j _ t h).of_iso (((geomPtAt (j t)).stalkF Λ).mapIso (PreservesKernel.iso (lsh j Λ) φ).symm)

theorem isZero_lsh_cokernel {G G' : EtSh Λ U} (φ : G ⟶ G') (t : U) (h : IsZero (stalk Λ (cokernel φ) t)) :
    IsZero (stalk Λ (cokernel ((lsh j Λ).map φ)) (j t)) :=
  (isZero_lsh j _ t h).of_iso (((geomPtAt (j t)).stalkF Λ).mapIso (PreservesCokernel.iso (lsh j Λ) φ).symm)

/-- The cokernel of the counit `j_! j^* F ⟶ F` vanishes at `j t`. -/
theorem isZero_cokernel_counit (F : EtSh Λ X) (t : U) :
    IsZero (stalk Λ (cokernel ((lshAdj j Λ).counit.app F)) (j t)) := by
  refine GPtIso.isZero_cokernel Λ (geomPtAt (j t)) _ ?_
  have h : IsIso ((((geomPtAt t).map j).point.sheafFiber (A := ModuleCat.{u} Λ)).map
      ((lshAdj j Λ).counit.app F)) := isIso_stalk_counit j Λ (geomPtAt t) F
  exact GPtIso.epi_of_ptIso Λ (mapPtIso j t).symm _ (@IsIso.epi_of_iso _ _ _ _ _ h)

variable (Λ) {W : Scheme.{u}} (g : W ⟶ U)

/-- `(g ≫ j)_* ⋙ j^* ≅ g_*`. -/
def pushResIso : push (g ≫ j) Λ ⋙ res j Λ ≅ push g Λ :=
  Functor.isoWhiskerRight (pushCompIso Λ g j).symm (res j Λ) ≪≫
    Functor.associator (push g Λ) (push j Λ) (res j Λ) ≪≫
    Functor.isoWhiskerLeft (push g Λ) (asIso (resAdj j Λ).counit) ≪≫ Functor.rightUnitor (push g Λ)

/-- **`((g ≫ j)_* M)_(j t) ≅ (g_* M)_t`**, naturally in `M`. -/
def pushStkIso (t : U) : push (g ≫ j) Λ ⋙ (geomPtAt (j t)).stalkF Λ ≅ push g Λ ⋙ (geomPtAt t).stalkF Λ :=
  Functor.isoWhiskerLeft (push (g ≫ j) Λ) (resStkIso j Λ t).symm ≪≫
    (Functor.associator (push (g ≫ j) Λ) (res j Λ) ((geomPtAt t).stalkF Λ)).symm ≪≫
    Functor.isoWhiskerRight (pushResIso j Λ g) ((geomPtAt t).stalkF Λ)

end RamanujanPetersson.EtCompact.StkTr

end

end

-- ===== S4.Def_RP_EtCompact_P1Clo =====
section

/-!
# S4-EtCompact, E3 (O7b): sheaves on `P¹` with zero generic stalk are acyclic

* `chart_hF`, **`chart_H`**: for an affine chart `f : Spec A ⟶ P¹` (`A` of finite type over `k = k̄`, dimension `≤ 1`),
  `H^(n+1)(Spec A, f^* Z) = 0` when `Z_η̄ = 0` (`Cech.H_eq_zero_of_closed` + `StkTr.isZero_res`);
* **`P1.H_closed`**: `H^(m+1)(P¹, Z) = 0` when `Z` has zero stalk at the generic point (`m = 0`: `P1.H1_closed`;
  `m ≥ 1`: Mayer-Vietoris over the two `A¹` charts and `G_m`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Polynomial

noncomputable section

namespace RamanujanPetersson.EtCompact.CurveHn

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact

variable (k : Type) [Field k] [IsAlgClosed k] {Λ : Type} [CommRing Λ]

theorem chart_hF (A : Type) [CommRing A] [IsDomain A] [Ring.KrullDimLE 1 A]
    (f : Spec (CommRingCat.of A) ⟶ P1 k) [IsOpenImmersion f] (Z : EtSh Λ (P1 k))
    (hη : IsZero (Cech.Mx Z (P1.genPt k))) (y : Spec (CommRingCat.of A))
    (hy : ¬ IsClosed ({y} : Set (Spec (CommRingCat.of A)))) : IsZero (Cech.Mx ((res f Λ).obj Z) y) := by
  obtain rfl := R1Gen.eq_genPt y hy
  refine StkTr.isZero_res f Z _ ?_
  rw [map_genPt k A f]
  exact hη

/-- **`H^(n+1)(Spec A, f^* Z) = 0`** on an affine chart when `Z_η̄ = 0`. -/
theorem chart_H (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A] [Algebra k A]
    [Algebra.FiniteType k A] (f : Spec (CommRingCat.of A) ⟶ P1 k) [IsOpenImmersion f] (Z : EtSh Λ (P1 k))
    (hη : IsZero (Cech.Mx Z (P1.genPt k))) (n : ℕ) (e : H Λ ((res f Λ).obj Z) (n + 1)) : e = 0 :=
  Cech.H_eq_zero_of_closed _ (chart_hF k A f Z hη) (fun y hy => gal_closed k A y hy) n e

end RamanujanPetersson.EtCompact.CurveHn

end

end

-- ===== S4.Def_RP_EtCompact_P1H3 =====
section

/-!
# S4-EtCompact, E4 (O7b): `H^(n+3)(P¹, F) = 0` for every sheaf `F`

`j = chartA1 : A¹ ⟶ P¹`, `g = gen k[X]` the generic point of `A¹`.
* `P1.H_of_lsh`: `0 → j_! j^* F → F → Q → 0` with `Q` point-supported (E3) reduces to `j_! j^* F`;
* `P1.lsh_H`: `j_! Y ≅ j_! j^* j_* Y ↪ j_* Y` in `H^(n+3)` (the cokernel is point-supported);
* `P1.isZero_R1_gen`, `P1.isZero_R1_qt`, **`P1.H_push_eq_zero`**: `H^(n+3)(P¹, (g ≫ j)_* N) = 0` (Leray-lite);
* **`P1.H_add_three_eq_zero_all`**: dévissage along `j_!` of the unit `G ⟶ g_* g^* G` (kernel and cokernel vanish at
  the generic point, so they are acyclic by E3).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Polynomial

noncomputable section

namespace RamanujanPetersson.EtCompact.CurveHn

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact

variable (k : Type) [Field k] [IsAlgClosed k] {Λ : Type} [CommRing Λ]

section H3

open RamanujanPetersson.CdOne RamanujanPetersson.Tsen RamanujanPetersson.EtCompact.GenFrac

/-- The generic stalk of `R¹(g ≫ j)_* N` vanishes (`g` the generic point of `A¹`, `j` the chart). -/
theorem P1.isZero_R1_gen (N : EtSh Λ (Spec ((Spec (CommRingCat.of k[X])).residueField (GenBr.genPt k[X])))) :
    IsZero (Cech.Mx (R1 (gen k[X] ≫ chartA1 k) Λ N) (P1.genPt k)) := by
  rw [← map_genPt k k[X] (chartA1 k)]
  refine GPtIso.isZero_cokernel Λ _ _
    (StkTr.epi_map_of_iso (StkTr.pushStkIso (chartA1 k) Λ (gen k[X]) (GenBr.genPt k[X])) _ ?_)
  exact GPtIso.epi_of_ptIso Λ (GPtIso.genPtIso k[X]) _ (GenStalk.epi_push (cokernel.π (Injective.ι N)))

variable (l : ℕ) [Fact l.Prime] (hl : (l : k) ≠ 0) (m : ℕ) (hΛ : ((l ^ m : ℕ) : Λ) = 0)

include hl hΛ

end H3

end RamanujanPetersson.EtCompact.CurveHn

end

end


