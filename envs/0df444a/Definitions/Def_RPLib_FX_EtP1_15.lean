-- Prove2me | Definitions.Def_RPLib_FX_EtP1_15
-- name    : RPLib_FX_EtP1_15
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T06:41:48.743663+00:00
-- url     : https://prove2.me/theorems/07fe2a3a-26fd-5112-b5a7-fa1f00e924e2
-- title:
--   Étale cohomology of the projective line, library file 15 of 34
-- statement:
--   File 15 of 34 of the étale cohomology library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtCompact_PtCd`: S4-EtCompact, part 38: `H^(n+2)` of a point vanishes when `cd ≤ 1` (CC2c)
--   * `S4.Def_RP_EtCompact_GenPt`: S4-EtCompact, part 39: `H^(n+2)` of `C₁` points and of the generic point of `A¹` (CC2d)
--   * `S4.Def_RP_EtCompact_MV`: S4-EtCompact: the Mayer-Vietoris sequence for a Zariski cover (O8c, file M1)
--   * `S4.Def_RP_EtCompact_Gm`: S4-EtCompact: the overlap of the two charts of `P^1` is `G_m` (O8c, file M3)
--   * `S4.Def_RP_Kummer_Const`: S4-Kummer, part 3: constants are unramified; `μ_N ⊆ K_U`; the curve form of Kummer theory
--   * `S4.Def_RP_EtCompact_Chart`: S4-EtCompact, part 55: affine charts with one generic point (F7d of plan v5)
--   * `S4.Def_RP_EtCompact_KumForm`: S4-EtCompact, part 56: Kummer arithmetic for the local step (F7e1 of plan v5)
--
--   **Formalization note.** One file of a library formalizing the étale cohomology of the projective line $\mathbf P^1_k = \operatorname{Proj} k[X_0, X_1]$ over an algebraically closed field $k$ with coefficients in sheaves of $\Lambda$-modules on the small étale site ($H^n = \operatorname{Ext}^n(\Lambda, -)$): $H^1(\mathbf P^1, \Lambda) = 0$, $H^2(\mathbf P^1, \Lambda) \cong \Lambda$ and $H^{n+3}(\mathbf P^1, F) = 0$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §1 (cohomology of curves) and Chapter III, §2 (Kummer theory); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Arcata », Chapter IV (cohomology of curves, Tsen's theorem)

import Mathlib
import Definitions.Def_RPLib_FX_EtP1_36

/-!
# Étale cohomology of the projective line, library file 15 of 34

Declarations of the formalization of the étale cohomology of the projective line over an algebraically
closed field (H¹ = 0, H² ≅ Λ, vanishing in degrees ≥ 3), re-hosted declaration by declaration from the
library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtCompact_PtCd`: S4-EtCompact, part 38: `H^(n+2)` of a point vanishes when `cd ≤ 1` (CC2c)
* `S4.Def_RP_EtCompact_GenPt`: S4-EtCompact, part 39: `H^(n+2)` of `C₁` points and of the generic point of `A¹` (CC2d)
* `S4.Def_RP_EtCompact_MV`: S4-EtCompact: the Mayer-Vietoris sequence for a Zariski cover (O8c, file M1)
* `S4.Def_RP_EtCompact_Gm`: S4-EtCompact: the overlap of the two charts of `P^1` is `G_m` (O8c, file M3)
* `S4.Def_RP_Kummer_Const`: S4-Kummer, part 3: constants are unramified; `μ_N ⊆ K_U`; the curve form of Kummer theory
* `S4.Def_RP_EtCompact_Chart`: S4-EtCompact, part 55: affine charts with one generic point (F7d of plan v5)
* `S4.Def_RP_EtCompact_KumForm`: S4-EtCompact, part 56: Kummer arithmetic for the local step (F7e1 of plan v5)
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtCompact_PtCd =====
section

/-!
# S4-EtCompact, part 38: `H^(n+2)` of a point vanishes when `cd ≤ 1` (CC2c)

`X ≅ Spec κ(x0)` (`IsIso (X.fromSpecResidueField x0)`), `G = Gal x0`.

* `PtH2 x0 F`: every locally constant 2-cocycle of `G` in `F_x̄` is the coboundary of a locally constant cochain;
* `coboundary_of_coker`: if `PtH2 x0 F`, every locally constant 1-cocycle in `(I/F)_x̄` (`F ↪ I` injective) is a
  coboundary (lift it to `I_x̄`, correct the lift by a cochain in `F_x̄`, use `coboundary_of_injective`);
* `h1_coker_eq_zero`: then `H¹(X, I/F) = 0` (an extension of `Λ_X` by `I/F` splits on stalks, hence as sheaves);
* **`pt_H_eq_zero`**: if `PtH2 x0 F` for all `F`, then `H^(n+2)(X, F) = 0` (dimension shifting);
* **`pt_H_eq_zero_of_hypL`**: the same when `Gal x0` satisfies `HypL ℓ` and `ℓ^k = 0` in `Λ` (`h2_lcCob`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Topology

noncomputable section

namespace RamanujanPetersson.EtCompact

open RamanujanPetersson.EtSheaves RamanujanPetersson.CdOne

universe u

variable {X : Scheme.{u}} (x0 : X) [IsIso (X.fromSpecResidueField x0)] {Λ : Type u} [CommRing Λ]

/-- **Cocycles in `(I/F)_x̄` are coboundaries** when `H²(Gal x0, F_x̄) = 0`. -/
theorem coboundary_of_coker (F : EtSh Λ X) (hF : PtH2 x0 F)
    {c : Gal x0 → stalk Λ (cokernel (Injective.ι F)) x0}
    (hc : IsCocycle (galRep Λ (cokernel (Injective.ι F)) x0) c) (hcl : IsLocallyConstant c) :
    ∃ m₀, ∀ g, c g = galRep Λ (cokernel (Injective.ι F)) x0 g m₀ - m₀ := by
  set ρQ := galRep Λ (cokernel (Injective.ι F)) x0
  set ρI := galRep Λ (Injective.under F) x0
  set ρF := galRep Λ F x0
  set ι := (((geomPtAt x0).stalkF Λ).map (Injective.ι F)).hom
  set π := (((geomPtAt x0).stalkF Λ).map (cokernel.π (Injective.ι F))).hom
  have hP := injPres_shortExact F
  have hinj : Function.Injective ι :=
    (ModuleCat.mono_iff_injective _).1 ((mono_iff_stalk Λ _).1 hP.mono_f x0)
  have hsurj : Function.Surjective π :=
    (ModuleCat.epi_iff_surjective _).1 ((epi_iff_stalk Λ _).1 hP.epi_g x0)
  have hex : LinearMap.ker π ≤ LinearMap.range ι := by
    have := (exact_iff_stalk Λ _).1 hP.exact x0
    rw [ShortComplex.moduleCat_exact_iff_ker_sub_range] at this
    exact this
  have hπι : ∀ y, π (ι y) = 0 := fun y => by
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← CategoryTheory.Functor.map_comp, cokernel.condition,
      CategoryTheory.Functor.map_zero, ModuleCat.hom_zero, LinearMap.zero_apply]
  have hιeq : ∀ g y, ι (ρF g y) = ρI g (ι y) := fun g y =>
    LinearMap.congr_fun (galRep_natural Λ (Injective.ι F) x0 g) y
  have hπeq : ∀ g y, π (ρI g y) = ρQ g (π y) := fun g y =>
    LinearMap.congr_fun (galRep_natural Λ (cokernel.π (Injective.ι F)) x0 g) y
  obtain ⟨b, hbπ, hbl⟩ : ∃ b : Gal x0 → stalk Λ (Injective.under F) x0, (∀ g, π (b g) = c g) ∧
      IsLocallyConstant b :=
    ⟨fun g => Function.surjInv hsurj (c g), fun g => Function.surjInv_eq hsurj _,
      by exact hcl.comp (Function.surjInv hsurj)⟩
  have hρI := galRep_isDiscrete x0 (Injective.under F)
  have hf2l : IsLocallyConstant fun p : Gal x0 × Gal x0 => ρI p.1 (b p.2) - b (p.1 * p.2) + b p.1 := by
    have h1 : IsLocallyConstant fun p : Gal x0 × Gal x0 => ρI p.1 (b p.2) :=
      hρI.lc_apply continuous_fst (hbl.comp_continuous continuous_snd)
    have h2 : IsLocallyConstant fun p : Gal x0 × Gal x0 => b (p.1 * p.2) := hbl.comp_continuous continuous_mul
    have h3 : IsLocallyConstant fun p : Gal x0 × Gal x0 => b p.1 := hbl.comp_continuous continuous_fst
    exact (h1.comp₂ h2 (· - ·)).comp₂ h3 (· + ·)
  have hmem : ∀ p : Gal x0 × Gal x0, ∃ y, ι y = ρI p.1 (b p.2) - b (p.1 * p.2) + b p.1 := by
    intro p
    refine LinearMap.mem_range.1 (hex (LinearMap.mem_ker.2 ?_))
    rw [map_add, map_sub, hπeq, hbπ, hbπ, hbπ, hc p.1 p.2]
    abel
  choose f' hf' using hmem
  have hf'l : IsLocallyConstant f' := by
    refine IsLocallyConstant.desc f' ι ?_ hinj
    have : (⇑ι ∘ f') = fun p : Gal x0 × Gal x0 => ρI p.1 (b p.2) - b (p.1 * p.2) + b p.1 := funext hf'
    rw [this]
    exact hf2l
  have hf'c : ∀ g h j : Gal x0, f' (g * h, j) + f' (g, h) = ρF g (f' (h, j)) + f' (g, h * j) := by
    intro g h j
    apply hinj
    rw [map_add, map_add, hιeq, hf', hf', hf', hf']
    simp only [map_add, map_sub, map_mul, Module.End.mul_apply, mul_assoc]
    abel
  obtain ⟨a, hal, ha⟩ := hF f' hf'l hf'c
  have hb'c : IsCocycle ρI (fun g => b g - ι (a g)) := by
    intro g h
    have e1 := hf' (g, h)
    rw [ha g h, map_add, map_sub, hιeq] at e1
    simp only at e1 ⊢
    rw [← sub_eq_zero, ← sub_eq_zero.2 e1]
    simp only [map_sub]
    abel
  have hb'l : IsLocallyConstant fun g => b g - ι (a g) := hbl.comp₂ (hal.comp ι) (· - ·)
  obtain ⟨m₀, hm₀⟩ := coboundary_of_injective x0 (Injective.under F) hb'c hb'l
  refine ⟨π m₀, fun g => ?_⟩
  have hm : b g - ι (a g) = ρI g m₀ - m₀ := hm₀ g
  rw [← hbπ g, ← hπeq, ← map_sub, ← hm, map_sub, hπι, sub_zero]

/-- **`H¹(X, I/F) = 0`** when `H²(Gal x0, F_x̄) = 0`. -/
theorem h1_coker_eq_zero (F : EtSh Λ X) (hF : PtH2 x0 F) (e : H Λ (cokernel (Injective.ι F)) 1) : e = 0 := by
  obtain ⟨s, hs⟩ := exists_extClass_eq e
  have hS := pbSES_shortExact s
  rw [← hs, extClass_eq_zero_iff hS]
  have hep : Epi (((geomPtAt x0).stalkF Λ).map (pbSES s).g) := (epi_iff_stalk Λ _).1 hS.epi_g x0
  obtain ⟨w, hw⟩ := (ModuleCat.epi_iff_surjective _).1 hep (oneStalk Λ x0)
  have hR := isRepExt_stalk x0 (f := (pbSES s).f) (g := (pbSES s).g) (hfg := (pbSES s).zero) hS
  have hw1 : (unitCoord Λ x0 ∘ₗ (((geomPtAt x0).stalkF Λ).map (pbSES s).g).hom) w = 1 := by
    rw [LinearMap.comp_apply]
    erw [hw]
    exact unitCoord_oneStalk Λ x0
  obtain ⟨H0, hH0, hfix⟩ := exists_open_fix Λ (pbSES s).X₂ x0 w
  have hcl : IsLocallyConstant (extCocycle hR w) := by
    refine lc_of_coset H0 hH0 _ fun g σ hσ => ?_
    have h0 : extCocycle hR w σ = 0 := hR.inj (by rw [i_extCocycle, hfix σ hσ, sub_self, map_zero])
    rw [isCocycle_extCocycle hR w g σ, h0, map_zero, add_zero]
  obtain ⟨m₀, hm₀⟩ := coboundary_of_coker x0 F hF (isCocycle_extCocycle hR w) hcl
  obtain ⟨r', hr'1, hr'2⟩ := (exists_retraction_iff _ (isCocycle_extCocycle hR w)).2 ⟨m₀, hm₀⟩
  let r₀ := r' ∘ₗ (extIso hR w hw1).toLinearMap
  have hr₀eq : ∀ σ : Gal x0, r₀ ∘ₗ galRep Λ (pbSES s).X₂ x0 σ = galRep Λ (pbSES s).X₁ x0 σ ∘ₗ r₀ := by
    intro σ
    refine LinearMap.ext fun v => ?_
    show r' (extIso hR w hw1 (galRep Λ (pbSES s).X₂ x0 σ v)) =
      galRep Λ (pbSES s).X₁ x0 σ (r' (extIso hR w hw1 v))
    rw [extIso_apply, extIso_apply, extIsoFun_equivariant, ← LinearMap.comp_apply r', hr'2, LinearMap.comp_apply]
  have hr₀i : r₀ ∘ₗ (((geomPtAt x0).stalkF Λ).map (pbSES s).f).hom = LinearMap.id := by
    refine LinearMap.ext fun m => ?_
    show r' (extIso hR w hw1 ((((geomPtAt x0).stalkF Λ).map (pbSES s).f).hom m)) = m
    rw [extIso_apply, extIsoFun_i, ← LinearMap.comp_apply r', hr'1, LinearMap.id_apply]
  refine ⟨(specField_homEquiv x0 Λ (pbSES s).X₂ (pbSES s).X₁).symm ⟨r₀, hr₀eq⟩, ?_⟩
  apply (specField_homEquiv x0 Λ (pbSES s).X₁ (pbSES s).X₁).injective
  apply Subtype.ext
  rw [specField_homEquiv_apply, specField_homEquiv_apply, CategoryTheory.Functor.map_comp, ModuleCat.hom_comp,
    CategoryTheory.Functor.map_id, ModuleCat.hom_id]
  have hr := congrArg Subtype.val
    ((specField_homEquiv x0 Λ (pbSES s).X₂ (pbSES s).X₁).apply_symm_apply ⟨r₀, hr₀eq⟩)
  rw [specField_homEquiv_apply] at hr
  rw [hr]
  exact hr₀i

/-- `PtH2` from `HypL ℓ (Gal x0)` when `ℓ^k = 0` in `Λ`. -/
theorem ptH2_of_hypL (l : ℕ) [Fact l.Prime] (hL : HypL l (Gal x0)) (k : ℕ) (hΛ : ((l ^ k : ℕ) : Λ) = 0)
    (F : EtSh Λ X) : PtH2 x0 F := fun _ hf hc =>
  h2_lcCob l hL k (galRep_isDiscrete x0 F) (fun m => by rw [← Nat.cast_smul_eq_nsmul Λ, hΛ, zero_smul]) hf hc

end RamanujanPetersson.EtCompact

end

end

-- ===== S4.Def_RP_EtCompact_GenPt =====
section

/-!
# S4-EtCompact, part 39: `H^(n+2)` of `C₁` points and of the generic point of `A¹` (CC2d)

* `isC1_of_ringEquiv`: `C₁` transfers along ring isomorphisms;
* **`pt_H_eq_zero_of_C1`**: on `X ≅ Spec κ` with `κ` a `C₁` field containing a primitive `ℓ`-th root of unity
  (`ℓ ≠ char κ`) and `ℓ^m = 0` in `Λ`: `H^(n+2)(X, F) = 0` (`hypL_gal` + `pt_H_eq_zero_of_hypL`);
* `H_ptOf_eq_zero_of_C1`: the same on `Spec κ(y)` for a point `y` with `C₁` residue field;
* `isC1_genField_polynomial`: `κ(η)` of `A¹_k = Spec k[X]` is `C₁` (Tsen, `κ(η) ≅ k(X)`), and
  **`H_genPt_eq_zero`**: `H^(n+2)(Spec κ(η), F) = 0` for `k` algebraically closed, `ℓ ≠ char k`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Polynomial

noncomputable section

namespace RamanujanPetersson.EtCompact

open RamanujanPetersson.EtSheaves RamanujanPetersson.CdOne RamanujanPetersson.Tsen

universe u

section Point

variable {X : Scheme.{u}} (x0 : X) [IsIso (X.fromSpecResidueField x0)] {Λ : Type u} [CommRing Λ]

end Point

section Generic

variable (k : Type) [Field k] [IsAlgClosed k]

theorem genConst_injective : Function.Injective (genConst k) :=
  (GenBr.fracIso k[X] (RatFunc k)).injective.comp (algebraMap k (RatFunc k)).injective

end Generic

end RamanujanPetersson.EtCompact

end

end

-- ===== S4.Def_RP_EtCompact_MV =====
section

/-!
# S4-EtCompact: the Mayer-Vietoris sequence for a Zariski cover (O8c, file M1)

* `mvS F U V`: the short complex `j_{U⊓V!}F ⟶ j_{U!}F ⊞ j_{V!}F ⟶ F`; **`mvS_shortExact`** when `U ∪ V = X`.
* `subsingleton_ext_biprod`, **`precomp_extClass_bijective`**: `Ext` out of a biproduct; the connecting map of the
  contravariant `Ext` sequence is bijective when the middle terms vanish.
* `cutExt j G n : Ext^n(j_{U!}Λ_U, G) ≃ H^n(U, G|_U)`, `cutH j n`, `cutHOpen W n`.
* **`P1.h2Equiv`**: `H^2(P^1, Λ) ≃ H^1(U ⊓ V, Λ)` for the two standard charts, when `H^1(A^1, Λ) = H^2(A^1, Λ) = 0`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Abelian TopologicalSpace

noncomputable section

namespace RamanujanPetersson.EtCompact

open RamanujanPetersson.EtSheaves

universe w v u

section ExtGen

variable {C : Type v} [Category.{w} C] [Abelian C] [HasExt.{u} C]

/-- `Ext^n(A ⊞ B, Y) = 0` when `Ext^n(A, Y) = Ext^n(B, Y) = 0`. -/
theorem subsingleton_ext_biprod {A B Y : C} {n : ℕ} (hA : Subsingleton (Ext A Y n))
    (hB : Subsingleton (Ext B Y n)) : Subsingleton (Ext (A ⊞ B) Y n) := by
  have key : ∀ z : Ext (A ⊞ B) Y n, z = 0 := fun z => by
    rw [← Ext.mk₀_id_comp z, ← biprod.total, Ext.mk₀_add, Ext.add_comp, ← Ext.mk₀_comp_mk₀_assoc,
      ← Ext.mk₀_comp_mk₀_assoc, Subsingleton.elim ((Ext.mk₀ biprod.inl).comp z (zero_add n)) 0,
      Subsingleton.elim ((Ext.mk₀ biprod.inr).comp z (zero_add n)) 0, Ext.comp_zero, Ext.comp_zero, add_zero]
  exact ⟨fun x y => (key x).trans (key y).symm⟩

end ExtGen

section MV

variable {Λ : Type u} [CommRing Λ] {X : Scheme.{u}}

/-- **The Mayer-Vietoris short complex** `j_{U⊓V!}F ⟶ j_{U!}F ⊞ j_{V!}F ⟶ F`. -/
abbrev mvS (F : EtSh Λ X) (U V : X.Opens) : ShortComplex (EtSh Λ X) :=
  ShortComplex.mk (biprod.lift (openCutLe (inf_le_left : U ⊓ V ≤ U) F)
      (-openCutLe (inf_le_right : U ⊓ V ≤ V) F))
    (biprod.desc (openCutι Λ U F) (openCutι Λ V F)) (by
      rw [biprod.lift_desc, Preadditive.neg_comp, openCutLe_comp, openCutLe_comp, add_neg_cancel])

theorem mvS_f (F : EtSh Λ X) (U V : X.Opens) :
    (mvS F U V).f = biprod.lift (openCutLe (inf_le_left : U ⊓ V ≤ U) F)
      (-openCutLe (inf_le_right : U ⊓ V ≤ V) F) := rfl

theorem mvS_g (F : EtSh Λ X) (U V : X.Opens) :
    (mvS F U V).g = biprod.desc (openCutι Λ U F) (openCutι Λ V F) := rfl

/-- **Mayer-Vietoris**: `0 ⟶ j_{U⊓V!}F ⟶ j_{U!}F ⊞ j_{V!}F ⟶ F ⟶ 0` is short exact when `U ∪ V = X`. -/
theorem mvS_shortExact {F : EtSh Λ X} {U V : X.Opens} (hUV : ∀ x : X, x ∈ U ∨ x ∈ V) :
    (mvS F U V).ShortExact := by
  have hg : Epi (mvS F U V).g := epi_biprod_desc_openCutι hUV
  have hf : Mono (mvS F U V).f := by
    have e : (mvS F U V).f ≫ biprod.fst ≫ openCutι Λ U F = openCutι Λ (U ⊓ V) F := by
      rw [mvS_f, biprod.lift_fst_assoc, openCutLe_comp]
    have : Mono ((mvS F U V).f ≫ biprod.fst ≫ openCutι Λ U F) := by rw [e]; infer_instance
    exact mono_of_mono _ (biprod.fst ≫ openCutι Λ U F)
  refine ShortComplex.ShortExact.mk' ?_ hf hg
  rw [ShortComplex.exact_iff_epi_kernel_lift]
  obtain ⟨a, ha⟩ : ∃ a, a = kernel.ι (mvS F U V).g ≫ biprod.fst := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = kernel.ι (mvS F U V).g ≫ biprod.snd := ⟨_, rfl⟩
  have hab : a ≫ openCutι Λ U F + b ≫ openCutι Λ V F = 0 := by
    have h0 : kernel.ι (mvS F U V).g ≫ (biprod.fst ≫ openCutι Λ U F + biprod.snd ≫ openCutι Λ V F) = 0 := by
      rw [← biprod.desc_eq]
      exact kernel.condition _
    rw [Preadditive.comp_add, ← Category.assoc, ← Category.assoc, ← ha, ← hb] at h0
    exact h0
  have hb' : (-b) ≫ openCutι Λ V F = a ≫ openCutι Λ U F := by
    rw [Preadditive.neg_comp, neg_eq_iff_eq_neg, eq_neg_iff_add_eq_zero, add_comm]
    exact hab
  have hq := comp_quotCutπ_inf (a ≫ openCutι Λ U F) a rfl (-b) hb'
  obtain ⟨c, hc⟩ : ∃ c : _ ⟶ openCut Λ (U ⊓ V) F, c ≫ openCutι Λ (U ⊓ V) F = a ≫ openCutι Λ U F :=
    ⟨Abelian.monoLift (openCutι Λ (U ⊓ V) F) (a ≫ openCutι Λ U F) hq, Abelian.monoLift_comp _ _ _⟩
  have hca : c ≫ openCutLe (inf_le_left : U ⊓ V ≤ U) F = a := by
    rw [← cancel_mono (openCutι Λ U F), Category.assoc, openCutLe_comp, hc]
  have hcb : c ≫ openCutLe (inf_le_right : U ⊓ V ≤ V) F = -b := by
    rw [← cancel_mono (openCutι Λ V F), Category.assoc, openCutLe_comp, hc, hb']
  have hcf : c ≫ (mvS F U V).f = kernel.ι (mvS F U V).g := by
    apply biprod.hom_ext
    · rw [Category.assoc, mvS_f, biprod.lift_fst, hca, ha]
    · rw [Category.assoc, mvS_f, biprod.lift_snd, Preadditive.comp_neg, hcb, neg_neg, hb]
  have hid : c ≫ kernel.lift (mvS F U V).g (mvS F U V).f (mvS F U V).zero = 𝟙 _ := by
    rw [← cancel_mono (kernel.ι (mvS F U V).g), Category.assoc, kernel.lift_ι, hcf, Category.id_comp]
  exact epi_of_epi_fac hid

end MV

section Cut

variable {Λ : Type u} [CommRing Λ] {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]

end Cut

section CutOpen

variable {Λ : Type u} [CommRing Λ] {X : Scheme.{u}}

end CutOpen

section ExtIface

variable {C : Type v} [Category.{w} C] [Abelian C]

variable [HasExt.{u} C]

end ExtIface

section P1

variable (K : Type u) [Field K] {Λ : Type u} [CommRing Λ]

end P1

end RamanujanPetersson.EtCompact

end

end

-- ===== S4.Def_RP_EtCompact_Gm =====
section

/-!
# S4-EtCompact: the overlap of the two charts of `P^1` is `G_m` (O8c, file M3)

* `LX k = k[X]_X`: a domain, a principal ideal ring; `Algebra (LX k) k(X)` with `IsScalarTower` and
  `IsFractionRing`; **`LX.unit_eq`**: every unit of `k[X]_X` is `c X^m` in `k(X)`.
* `chartGm k : Spec k[X]_X ⟶ P^1_k` (open immersion), **`P1.opensRange_chartGm`**: its range is the overlap
  `range chartA1 ⊓ range chartA1'`.
* **`P1.h2EquivGm`**: `H^2(P^1, Λ) ≃ H^1(G_m, Λ)` when `H^1(A^1, Λ) = H^2(A^1, Λ) = 0`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Abelian TopologicalSpace Polynomial

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace RamanujanPetersson.EtCompact

open RamanujanPetersson.EtSheaves

universe u

section LX

variable (k : Type u) [Field k]

/-- `k[X, X⁻¹] = k[X]_X`. -/
abbrev LX : Type u := Localization.Away (X : k[X])

instance LX.isDomain : IsDomain (LX k) :=
  IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors X_ne_zero)

instance LX.isPrincipalIdealRing : IsPrincipalIdealRing (LX k) where
  principal J := by
    have h := IsLocalization.map_under (Submonoid.powers (X : k[X])) (LX k) J
    rw [← Ideal.span_singleton_generator (J.under k[X]), Ideal.map_span, Set.image_singleton] at h
    exact ⟨⟨_, h.symm⟩⟩

theorem LX.isUnit_X : IsUnit (algebraMap k[X] (RatFunc k) X) :=
  isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ (IsFractionRing.injective k[X] (RatFunc k))).2 X_ne_zero)

instance LX.algebraRatFunc : Algebra (LX k) (RatFunc k) :=
  (Localization.awayLift (algebraMap k[X] (RatFunc k)) X (LX.isUnit_X k)).toAlgebra

theorem LX.algebraMap_algebraMap (p : k[X]) :
    algebraMap (LX k) (RatFunc k) (algebraMap k[X] (LX k) p) = algebraMap k[X] (RatFunc k) p :=
  IsLocalization.Away.lift_eq (hg := LX.isUnit_X k) (a := p)

theorem LX.injective : Function.Injective (algebraMap k[X] (LX k)) :=
  IsLocalization.injective (LX k) (powers_le_nonZeroDivisors_of_noZeroDivisors X_ne_zero)

end LX

section Chart

variable (k : Type u) [Field k]

/-- `G_m = Spec k[X]_X`. -/
abbrev Gm : Scheme.{u} := Spec (CommRingCat.of (LX k))

/-- `G_m ⟶ A^1 ⟶ P^1` (`t ↦ [1 : t]`). -/
def chartGm : Gm k ⟶ P1 k :=
  Spec.map (CommRingCat.ofHom (algebraMap k[X] (LX k))) ≫ chartA1 k

instance isOpenImmersion_chartGm : IsOpenImmersion (chartGm k) := by
  unfold chartGm
  have : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap k[X] (LX k)))) :=
    Scheme.isOpenImmersion_SpecMap_localizationAway (R := CommRingCat.of k[X]) X
  infer_instance

theorem chartA1_preimage_range' :
    (chartA1 k) ⁻¹ᵁ (chartA1' k).opensRange = PrimeSpectrum.basicOpen (X : k[X]) := by
  rw [P1.opensRange_chartA1', chartA1, Scheme.Hom.comp_preimage, P1.chart0,
    Proj.awayι_preimage_basicOpen _ (P1.X_mem k 0) one_pos (P1.X_mem k 1) one_pos, SpecMap_preimage_basicOpen]
  congr 1
  show awayDehom _ = _
  rw [awayDehom_mk, map_pow, dehom_X1, pow_one]

variable {Λ : Type u} [CommRing Λ]

end Chart

end RamanujanPetersson.EtCompact

end

end

-- ===== S4.Def_RP_Kummer_Const =====
section

/-!
# S4-Kummer, part 3: constants are unramified; `μ_N ⊆ K_U`; the curve form of Kummer theory

`K` of characteristic `p`, `q = p ^ e` (`e > 0`), `A` any ring with `K = Frac`-like algebra `A → K` (no hypothesis on
`A` is needed: constant extensions are unramified over every `A`).

* `constLevel K p k = K(roots of X^(p^k) - X)` is a finite Galois subextension of `K̄/K` with trivial inertia at every
  prime of the integral closure of `A` (`constLevel_mem_unramSet`): an inertia element `σ` moves a root `s` to a root,
  `σ s - s` is again a root (Frobenius is additive), hence `0` or a unit, and it lies in the prime;
* `mem_maxUnram_of_isConst`: every constant of `K̄` lies in `K_U = maxUnram A K`;
* `exists_zeta`: for `N` prime to `p` there is a primitive `N`-th root of unity `ζ ∈ K_U` which is a constant;
  `zeta_fixed`: `π₁^geo` fixes it; `frobLift_zeta`: an arithmetic Frobenius lift sends `ζ ↦ ζ ^ q`;
* `curveKummerEquiv`: `H¹(U ⊗ 𝔽̄, ZMod N) ≃ rad / (π₁^geo-fixed units)`, and `geomFrobH1_kclass`:
  `F [kchar α] = q • [kchar (φ⁻¹ α)]` for the GEOMETRIC Frobenius of `Def_RP_CurveCoh_Curve` (review R4).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Kummer

open CurveCoh Polynomial

noncomputable section

section Level

variable (A K : Type) [CommRing A] [Field K] [Algebra A K] (p : ℕ) [hp : Fact p.Prime] [CharP K p]

variable {K p}

end Level

section Zeta

variable (A K : Type) [CommRing A] [Field K] [Algebra A K] (p : ℕ) [hp : Fact p.Prime] [CharP K p]
  {e : ℕ} (he : 0 < e) (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0)

variable {A K p N}

end Zeta

section Curve

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {q N : ℕ} [NeZero N] {ζ : maxUnram A K} (hζ : IsPrimitiveRoot ζ N)

instance maxUnram_isIntegral : Algebra.IsIntegral K (maxUnram A K) := inferInstance

end Curve

end

end Kummer
end RamanujanPetersson


end

-- ===== S4.Def_RP_EtCompact_Chart =====
section

/-!
# S4-EtCompact, part 55: affine charts with one generic point (F7d of plan v5)

`A` a noetherian integrally closed domain.

* **`exists_chart`**: every point of an étale `V ⟶ Spec A` is hit by `specEt A B ⟶ V` with at most one prime of `B`
  over `(0)` (`ChartAlg.exists_chartAlg` on an affine refinement);
* `subsingleton_pull` (then `g^* Spec B` has one point), `exists_prime_le` (going-down), `nonempty_fib`, `ker_le`
  (`ker φ_a ⊆ P₀` for every fibre point `a` and every prime `P₀`), `alg_injective`;
* **`exists_chart_sc`**: for `φ : G ⟶ C` epi and `b : Λ ⟶ C`, a chart `B` at `x` with a prime `P₀` over `x` on which
  `b(1)` lifts to `G`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtCompact.Chart

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact.GenFrac RamanujanPetersson.EtCompact.LT

variable {A : Type} [CommRing A] [IsDomain A]

theorem alg_injective : Function.Injective (algebraMap A (SeparableClosure (κ0 A))) := by
  rw [IsScalarTower.algebraMap_eq A (κ0 A) (SeparableClosure (κ0 A)), RingHom.coe_comp]
  exact (algebraMap (κ0 A) _).injective.comp (IsFractionRing.injective A (κ0 A))

section B

variable {B : Type} [CommRing B] [Algebra A B] [Algebra.Etale A B]

theorem subsingleton_pull
    (huniq : ∀ P₁ P₂ : PrimeSpectrum B, P₁.asIdeal.comap (algebraMap A B) = ⊥ →
      P₂.asIdeal.comap (algebraMap A B) = ⊥ → P₁ = P₂) :
    Subsingleton ((etPull (gen A)).obj (specEt A B)).left := by
  constructor
  intro z₁ z₂
  refine SgUnit.fst_injective (GenBr.genPt A) (specEt A B).hom ?_
  have h1 := SgUnit.fst_over (GenBr.genPt A) (specEt A B).hom z₁
  have h2 := SgUnit.fst_over (GenBr.genPt A) (specEt A B).hom z₂
  exact huniq _ _ (congrArg PrimeSpectrum.asIdeal h1) (congrArg PrimeSpectrum.asIdeal h2)

/-- **Going-down**: below every prime of `B` lies a prime over `(0)`. -/
theorem exists_prime_le (P₀ : PrimeSpectrum B) :
    ∃ P : PrimeSpectrum B, P.asIdeal ≤ P₀.asIdeal ∧ P.asIdeal.comap (algebraMap A B) = ⊥ := by
  have : P₀.asIdeal.LiesOver (P₀.asIdeal.comap (algebraMap A B)) := ⟨rfl⟩
  obtain ⟨P, hP, hPp, hPl⟩ := Ideal.exists_ideal_le_liesOver_of_le (p := (⊥ : Ideal A))
    (q := P₀.asIdeal.comap (algebraMap A B)) P₀.asIdeal bot_le
  exact ⟨⟨P, hPp⟩, hP, hPl.over.symm⟩

theorem nonempty_fib (P : PrimeSpectrum B) (hP : P.asIdeal.comap (algebraMap A B) = ⊥) : Nonempty (Fib A B) := by
  have h : (specEt A B).hom P = gen A (x0 A) := by
    refine Eq.trans ?_ (Scheme.fromSpecResidueField_apply _ _).symm
    exact PrimeSpectrum.ext hP
  obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback (f := (specEt A B).hom) (g := gen A) P (x0 A) h
  exact (geomPtAt (x0 A)).exists_fiber ((etPull (gen A)).obj (specEt A B)) z (hz.trans (center_geomPtAt _).symm)

/-- `ker φ_a` lies in every prime of `B` when `B` has one prime over `(0)`. -/
theorem ker_le
    (huniq : ∀ P₁ P₂ : PrimeSpectrum B, P₁.asIdeal.comap (algebraMap A B) = ⊥ →
      P₂.asIdeal.comap (algebraMap A B) = ⊥ → P₁ = P₂) (a : Fib A B) (P₀ : PrimeSpectrum B) :
    RingHom.ker (phiB A a) ≤ P₀.asIdeal := by
  obtain ⟨P, hP, hPb⟩ := exists_prime_le (A := A) P₀
  have hkb : (RingHom.ker (phiB A a)).comap (algebraMap A B) = ⊥ := by
    ext c
    rw [Ideal.mem_comap, RingHom.mem_ker, AlgHom.commutes, Ideal.mem_bot]
    exact ⟨fun h => alg_injective (h.trans (map_zero _).symm), fun h => by rw [h, map_zero]⟩
  have heq := huniq ⟨_, RingHom.ker_isPrime _⟩ P hkb hPb
  have hk : RingHom.ker (phiB A a) = P.asIdeal := congrArg PrimeSpectrum.asIdeal heq
  rw [hk]
  exact hP

end B

variable (A) [IsIntegrallyClosed A] [IsNoetherianRing A]

/-- **Charts with one generic point.** -/
theorem exists_chart (V : (Spec (CommRingCat.of A)).Etale) (v : V.left) :
    ∃ (B : Type) (_ : CommRing B) (_ : Algebra A B) (_ : Algebra.Etale A B) (F : specEt A B ⟶ V)
      (P₀ : PrimeSpectrum B), F.left P₀ = v ∧
      ∀ P₁ P₂ : PrimeSpectrum B, P₁.asIdeal.comap (algebraMap A B) = ⊥ →
        P₂.asIdeal.comap (algebraMap A B) = ⊥ → P₁ = P₂ := by
  obtain ⟨R, _, _, _, F, r, hr⟩ := Supp.exists_affine A V v
  let r' : PrimeSpectrum R := r
  have : r'.asIdeal.IsPrime := r'.isPrime
  obtain ⟨f₀, f₁, P₀, hP₀, huniq⟩ := ChartAlg.exists_chartAlg (A := A) (R := R) r'.asIdeal
  have key : ∀ P : Ideal (Localization.Away f₁),
      ((P.comap (algebraMap (Localization.Away f₀) (Localization.Away f₁))).comap
        (algebraMap R (Localization.Away f₀))).comap (algebraMap A R) =
      P.comap (algebraMap A (Localization.Away f₁)) := by
    intro P
    rw [Ideal.comap_comap, Ideal.comap_comap,
      IsScalarTower.algebraMap_eq A (Localization.Away f₀) (Localization.Away f₁),
      IsScalarTower.algebraMap_eq A R (Localization.Away f₀)]
  refine ⟨Localization.Away f₁, inferInstance, inferInstance, inferInstance,
    specEtMap (IsScalarTower.toAlgHom A (Localization.Away f₀) (Localization.Away f₁)) ≫
      specEtMap (IsScalarTower.toAlgHom A R (Localization.Away f₀)) ≫ F, P₀, ?_, ?_⟩
  · have hq : PrimeSpectrum.comap (algebraMap R (Localization.Away f₀))
        (PrimeSpectrum.comap (algebraMap (Localization.Away f₀) (Localization.Away f₁)) P₀) = r' :=
      PrimeSpectrum.ext hP₀
    exact (congrArg (fun z => F.left z) hq).trans hr
  · intro P₁ P₂ h₁ h₂
    exact huniq P₁ P₂ ((key _).trans h₁) ((key _).trans h₂)

/-- **A chart at `x` carrying a local lift of `b(1)`.** -/
theorem exists_chart_sc {Λ : Type} [CommRing Λ] {G C : EtSh Λ (Spec (CommRingCat.of A))} (φ : G ⟶ C) [Epi φ]
    (b : unitSh Λ (Spec (CommRingCat.of A)) ⟶ C) (x : Spec (CommRingCat.of A)) :
    ∃ (B : Type) (_ : CommRing B) (_ : Algebra A B) (_ : Algebra.Etale A B) (P₀ : PrimeSpectrum B),
      PrimeSpectrum.comap (algebraMap A B) P₀ = x ∧
      Subsingleton ((etPull (gen A)).obj (specEt A B)).left ∧ Nonempty (Fib A B) ∧
      (∀ a : Fib A B, RingHom.ker (phiB A a) ≤ P₀.asIdeal) ∧
      ∃ s : G.obj.obj (op (specEt A B)), (φ.hom.app (op (specEt A B))).hom s = Supp.sc b (specEt A B) := by
  obtain ⟨V, w, hw, s, hs⟩ := Supp.exists_local_sc φ b x
  obtain ⟨B, _, _, _, F, P₀, hP, huniq⟩ := exists_chart A V w
  obtain ⟨P, -, hPb⟩ := exists_prime_le (A := A) P₀
  refine ⟨B, inferInstance, inferInstance, inferInstance, P₀, ?_, subsingleton_pull huniq, nonempty_fib P hPb,
    fun a => ker_le huniq a P₀, (G.obj.map F.op).hom s, ?_⟩
  · exact (congrArg (fun f => f P₀) (MorphismProperty.Over.w F)).symm.trans
      ((congrArg (fun z => V.hom z) hP).trans hw)
  · have h1 := congrArg (fun ψ => ψ.hom s) (φ.hom.naturality F.op)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h1
    rw [h1, hs]
    exact Supp.sc_map b F

end RamanujanPetersson.EtCompact.Chart

end

end

-- ===== S4.Def_RP_EtCompact_KumForm =====
section

/-!
# S4-EtCompact, part 56: Kummer arithmetic for the local step (F7e1 of plan v5)

`ζ` a primitive `d`-th root of unity in a field `Ω`, `σ ∈ Aut_K(Ω)`.

* `dlog_mul_of`, `dlog_pow_of` (on `d`-th roots of unity), `ratio_pow_eq_one`;
* **`root_twist_pow`**: from `t c = v π^n`, `γ^d = c`, `ϖ^d = π`: `(γ t / ϖ^n)^d = v t^(d-1)`;
* **`dlog_twist`**: `dlog(σβ/β) = dlog(σγ/γ) - n dlog(σϖ/ϖ)` for `β = γ t / ϖ^n` with `σ t = t`;
* **`sum_twist`**: on a `d`-torsion group, `∑ (a i - n i b).val • e i = ∑ (a i).val • e i - b.val • ∑ n i • e i`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace RamanujanPetersson.EtCompact.KumForm

open RamanujanPetersson.Kummer

section Dlog

variable {Ω : Type} [Field Ω] {d : ℕ} [NeZero d] {ζ : Ω} (hζ : IsPrimitiveRoot ζ d)

end Dlog

section Twist

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {d : ℕ} [NeZero d] {ζ : Ω} (hζ : IsPrimitiveRoot ζ d)

theorem ratio_pow_eq_one (σ : Ω ≃ₐ[K] Ω) {z : Ω} (hz : z ≠ 0) (h : σ (z ^ d) = z ^ d) : (σ z / z) ^ d = 1 := by
  rw [div_pow, ← map_pow, h, div_self (pow_ne_zero _ hz)]

end Twist

section Sum

variable {M : Type*} [AddCommGroup M] {d : ℕ} [NeZero d]

end Sum

end RamanujanPetersson.EtCompact.KumForm

end

end


