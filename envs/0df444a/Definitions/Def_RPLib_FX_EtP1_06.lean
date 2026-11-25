-- Prove2me | Definitions.Def_RPLib_FX_EtP1_06
-- name    : RPLib_FX_EtP1_06
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T01:32:47.411573+00:00
-- url     : https://prove2.me/theorems/b1473212-7540-42dc-88d2-134bd8a86366
-- title:
--   Étale cohomology of the projective line, library file 06 of 34
-- statement:
--   File 06 of 34 of the étale cohomology library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtCompact_FVExact`: S4-EtCompact, O9b part 3: `F_V` over one Galois cover is exact
--   * `S4.Def_RP_EtCompact_Kappa`: S4-EtCompact, O9b part 5: the extension class `κ(c) ∈ H¹(Spec A, G)` of a `π₁`-cocycle
--   * `S4.Def_RP_EtCompact_Spread`: S4-EtCompact, O9b part 6a: an extension of `Λ_X` by a lisse sheaf is lisse
--   * `S4.Def_RP_EtCompact_Bridge`: S4-EtCompact, O9b part 6: `κ` is additive, kills coboundaries and is injective on `H¹`
--   * `S4.Def_RP_EtCompact_P1Cover`: S4-EtCompact, part 33: the second chart of `P^1` and `H^1(P^1, Λ)` from `H^1(A^1, Λ)` (O8b, file 3)
--   * `S4.Def_RP_EtCompact_H1`: S4-EtCompact, O9b part 7: `H¹(Spec A, G) ≃ H¹_cont(π₁, G_η̄)` for lisse `G`
--
--   **Formalization note.** One file of a library formalizing the étale cohomology of the projective line $\mathbf P^1_k = \operatorname{Proj} k[X_0, X_1]$ over an algebraically closed field $k$ with coefficients in sheaves of $\Lambda$-modules on the small étale site ($H^n = \operatorname{Ext}^n(\Lambda, -)$): $H^1(\mathbf P^1, \Lambda) = 0$, $H^2(\mathbf P^1, \Lambda) \cong \Lambda$ and $H^{n+3}(\mathbf P^1, F) = 0$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §1 (cohomology of curves) and Chapter III, §2 (Kummer theory); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Arcata », Chapter IV (cohomology of curves, Tsen's theorem)

import Mathlib
import Definitions.Def_RPLib_FX_EtP1_05

/-!
# Étale cohomology of the projective line, library file 06 of 34

Declarations of the formalization of the étale cohomology of the projective line over an algebraically
closed field (H¹ = 0, H² ≅ Λ, vanishing in degrees ≥ 3), re-hosted declaration by declaration from the
library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtCompact_FVExact`: S4-EtCompact, O9b part 3: `F_V` over one Galois cover is exact
* `S4.Def_RP_EtCompact_Kappa`: S4-EtCompact, O9b part 5: the extension class `κ(c) ∈ H¹(Spec A, G)` of a `π₁`-cocycle
* `S4.Def_RP_EtCompact_Spread`: S4-EtCompact, O9b part 6a: an extension of `Λ_X` by a lisse sheaf is lisse
* `S4.Def_RP_EtCompact_Bridge`: S4-EtCompact, O9b part 6: `κ` is additive, kills coboundaries and is injective on `H¹`
* `S4.Def_RP_EtCompact_P1Cover`: S4-EtCompact, part 33: the second chart of `P^1` and `H^1(P^1, Λ)` from `H^1(A^1, Λ)` (O8b, file 3)
* `S4.Def_RP_EtCompact_H1`: S4-EtCompact, O9b part 7: `H¹(Spec A, G) ≃ H¹_cont(π₁, G_η̄)` for lisse `G`
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtCompact_FVExact =====
section

/-!
# S4-EtCompact, O9b part 3: `F_V` over one Galois cover is exact

For a finite Galois cover `C` of `Spec A` and equivariant maps `V₁ →ᶠ V₂ →ᵍ V₃` of `C.G`-representations:
* `FVMap_comp_eq_zero`: `g ∘ f = 0` gives `F(f) ≫ F(g) = 0`;
* **`FV_shortExact`**: if `0 → V₁ → V₂ → V₃ → 0` is exact, then `0 → F_{V₁} → F_{V₂} → F_{V₃} → 0` is a short
  exact sequence of etale sheaves (checked on every stalk: each geometric point lifts to the cover, and there the
  stalk sequence is the `V`-sequence).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits

noncomputable section

namespace RamanujanPetersson.EtCompact

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtSheaves.TorSec

attribute [local instance] GalCover.ring GalCover.dom GalCover.alg GalCover.inj GalCover.fin GalCover.grp GalCover.fG GalCover.act GalCover.gal

variable {A : Type} [CommRing A] [IsDomain A] {C : GalCover A} (Λ : Type) [CommRing Λ]
  {V₁ V₂ V₃ : Type} [AddCommGroup V₁] [Module Λ V₁] [AddCommGroup V₂] [Module Λ V₂]
  [AddCommGroup V₃] [Module Λ V₃]
  (ρ₁ : Representation Λ C.G V₁) (ρ₂ : Representation Λ C.G V₂) (ρ₃ : Representation Λ C.G V₃)
  (f : V₁ →ₗ[Λ] V₂) (g : V₂ →ₗ[Λ] V₃) (hf : ∀ σ : C.G, f ∘ₗ ρ₁ σ = ρ₂ σ ∘ₗ f)
  (hg : ∀ σ : C.G, g ∘ₗ ρ₂ σ = ρ₃ σ ∘ₗ g)

theorem FVMap_comp_eq_zero (hfg : g ∘ₗ f = 0) : FVMap Λ ρ₁ ρ₂ f hf ≫ FVMap Λ ρ₂ ρ₃ g hg = 0 := by
  refine hom_ext_stalk Λ (fun x => ?_)
  obtain ⟨l, hl⟩ := exists_lift (C := C) (geomPtAt x)
  refine ModuleCat.hom_ext (LinearMap.ext fun w => ?_)
  rw [Functor.map_comp, Functor.map_zero, ModuleCat.hom_comp, ModuleCat.hom_zero, LinearMap.zero_apply,
    LinearMap.comp_apply, ← iso_hom_inv_apply Λ (stalkFVAt Λ ρ₁ (geomPtAt x) l hl) w,
    stalkFVAt_FVMap, stalkFVAt_FVMap, ← LinearMap.comp_apply g f, hfg, LinearMap.zero_apply, map_zero]

variable (hinj : Function.Injective f) (hsurj : Function.Surjective g)
  (hex : LinearMap.range f = LinearMap.ker g)

include hinj hsurj in
/-- **`V ↦ F_V` sends short exact sequences of `C.G`-representations to short exact sequences of sheaves.** -/
theorem FV_shortExact :
    (ShortComplex.mk (FVMap Λ ρ₁ ρ₂ f hf) (FVMap Λ ρ₂ ρ₃ g hg)
      (FVMap_comp_eq_zero Λ ρ₁ ρ₂ ρ₃ f g hf hg (comp_eq_zero_of_range_eq_ker Λ f g hex))).ShortExact := by
  refine ShortComplex.ShortExact.mk' ((exact_iff_stalk Λ _).2 fun x => ?_)
    ((mono_iff_stalk Λ _).2 fun x => ?_) ((epi_iff_stalk Λ _).2 fun x => ?_)
  · obtain ⟨l, hl⟩ := exists_lift (C := C) (geomPtAt x)
    rw [ShortComplex.moduleCat_exact_iff_ker_sub_range]
    show LinearMap.ker (((geomPtAt x).stalkF Λ).map (FVMap Λ ρ₂ ρ₃ g hg)).hom ≤
      LinearMap.range (((geomPtAt x).stalkF Λ).map (FVMap Λ ρ₁ ρ₂ f hf)).hom
    intro y hy
    have hy' : ((((geomPtAt x).stalkF Λ).map (FVMap Λ ρ₂ ρ₃ g hg)).hom y) = 0 := hy
    have hgv : g ((stalkFVAt Λ ρ₂ (geomPtAt x) l hl).hom.hom y) = 0 := by
      rw [← stalkFVAt_FVMap_hom Λ ρ₂ ρ₃ g hg (geomPtAt x) l hl y, hy', map_zero]
    have hmem : (stalkFVAt Λ ρ₂ (geomPtAt x) l hl).hom.hom y ∈ LinearMap.range f := by
      rw [hex]
      exact hgv
    obtain ⟨u, hu⟩ := hmem
    refine ⟨(stalkFVAt Λ ρ₁ (geomPtAt x) l hl).inv.hom u, ?_⟩
    show (((geomPtAt x).stalkF Λ).map (FVMap Λ ρ₁ ρ₂ f hf)).hom ((stalkFVAt Λ ρ₁ (geomPtAt x) l hl).inv.hom u) = y
    rw [stalkFVAt_FVMap, hu, iso_hom_inv_apply]
  · obtain ⟨l, hl⟩ := exists_lift (C := C) (geomPtAt x)
    rw [ModuleCat.mono_iff_injective, injective_iff_map_eq_zero]
    intro y hy
    have hy' : ((((geomPtAt x).stalkF Λ).map (FVMap Λ ρ₁ ρ₂ f hf)).hom y) = 0 := hy
    have h1 : f ((stalkFVAt Λ ρ₁ (geomPtAt x) l hl).hom.hom y) = 0 := by
      rw [← stalkFVAt_FVMap_hom Λ ρ₁ ρ₂ f hf (geomPtAt x) l hl y, hy', map_zero]
    have h2 : (stalkFVAt Λ ρ₁ (geomPtAt x) l hl).hom.hom y = 0 := hinj (h1.trans (map_zero f).symm)
    rw [← iso_hom_inv_apply Λ (stalkFVAt Λ ρ₁ (geomPtAt x) l hl) y, h2, map_zero]
  · obtain ⟨l, hl⟩ := exists_lift (C := C) (geomPtAt x)
    rw [ModuleCat.epi_iff_surjective]
    intro z
    obtain ⟨u, hu⟩ := hsurj ((stalkFVAt Λ ρ₃ (geomPtAt x) l hl).hom.hom z)
    refine ⟨(stalkFVAt Λ ρ₂ (geomPtAt x) l hl).inv.hom u, ?_⟩
    show (((geomPtAt x).stalkF Λ).map (FVMap Λ ρ₂ ρ₃ g hg)).hom ((stalkFVAt Λ ρ₂ (geomPtAt x) l hl).inv.hom u) = z
    rw [stalkFVAt_FVMap, hu, iso_hom_inv_apply]

end RamanujanPetersson.EtCompact

end

end

-- ===== S4.Def_RP_EtCompact_Kappa =====
section

/-!
# S4-EtCompact, O9b part 5: the extension class `κ(c) ∈ H¹(Spec A, G)` of a `π₁`-cocycle

`A` noetherian integrally closed domain, `G` lisse on `Spec A` with fibre representation `ρ = fibRep G` of
`π₁ = Pi1 A K` on `M = G_η̄`, `c` a continuous (locally constant) 1-cocycle.
* `nonempty_realExt`: there is a short exact `0 → G → P → Λ_X → 0` with lisse `P` realizing `c` (`P = F_V` for the
  extension representation `V = M × Λ` of `extRep ρ c` over one Galois cover, `G ≅ F_M`, `Λ_X ≅ F_Λ`);
* `kappa`: its class; **`kappa_eq`**: every short exact sequence realizing `c` has class `κ(c)`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits

noncomputable section

namespace RamanujanPetersson.EtCompact

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtSheaves.GenBr RamanujanPetersson.EtSheaves.TorSec

attribute [local instance] GalCover.ring GalCover.dom GalCover.alg GalCover.inj GalCover.fin GalCover.grp GalCover.fG GalCover.act GalCover.gal

variable (A K : Type) [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  [IsIntegrallyClosed A] {Λ : Type} [CommRing Λ]

omit [IsIntegrallyClosed A] in
/-- Generic: `(φ ≫ E⁻¹)_η̄ x = u` from `φ_η̄ x = E_η̄ u`. -/
theorem gs_comp_inv_eq {U P Q : EtSh Λ (Spec (CommRingCat.of A))} (φ : P ⟶ Q) (E : U ≅ Q)
    (x : stalk Λ P (genPt A)) (u : stalk Λ U (genPt A)) (h : gs A φ x = gs A E.hom u) : gs A (φ ≫ E.inv) x = u := by
  rw [gs_comp_apply, h, gs_inv_hom_apply]

/-- The generic stalk of `Λ_X` is `Λ`. Sealed behind `Classical.choose` (with `cIso_eq`) so that the kernel never
unfolds the colimit construction when comparing terms under it. -/
def cIso : stalk Λ (unitSh Λ (Spec (CommRingCat.of A))) (genPt A) ≅ ModuleCat.of Λ Λ :=
  Classical.choose (exists_cIso A)

omit [IsIntegrallyClosed A] in
theorem cIso_eq : cIso A (Λ := Λ) = constStalkIso Λ (geomPtAt (genPt A)) (ModuleCat.of Λ Λ) :=
  Classical.choose_spec (exists_cIso A)

omit [IsIntegrallyClosed A] in
theorem oneStalk_eq : oneStalk Λ (genPt A) = (cIso A (Λ := Λ)).inv.hom (1 : Λ) := by
  rw [cIso_eq]
  rfl

variable [IsNoetherianRing A]

/-- **An extension of `Λ_X` by `G` realizing `c`**, with lisse middle term. -/
structure RealExt (G : EtSh Λ (Spec (CommRingCat.of A))) (c : Pi1 A K → stalk Λ G (genPt A)) where
  P : EtSh Λ (Spec (CommRingCat.of A))
  f : G ⟶ P
  g : P ⟶ unitSh Λ (Spec (CommRingCat.of A))
  w : stalk Λ P (genPt A)
  zero : f ≫ g = 0
  se : (ShortComplex.mk f g zero).ShortExact
  lis : IsLisse Λ P
  real : Realizes A K c f g w

variable {A K}
variable (L : IntermediateField K (AlgebraicClosure K)) (hL : L ∈ unramSet A K)

/-- The Galois action on the generic stalk of `F_Λ` (trivial representation) is trivial. -/
theorem galRep_FV_trivial (σ : Gal (genPt A))
    (y : stalk Λ (FV (coverOf A K L hL) Λ (Representation.trivial Λ (coverOf A K L hL).G Λ)) (genPt A)) :
    galRep Λ (FV (coverOf A K L hL) Λ (Representation.trivial Λ (coverOf A K L hL).G Λ)) (genPt A) σ y = y := by
  have h := stalkFVGen_galRep A K L hL Λ (Representation.trivial Λ (coverOf A K L hL).G Λ) σ y
  rw [Representation.trivial_apply] at h
  exact modIso_injective _ h

section SIso

variable {V W : Type} [AddCommGroup V] [Module Λ V] [AddCommGroup W] [Module Λ W]

theorem exists_sIso (ρ : Representation Λ (coverOf A K L hL).G V) :
    ∃ e : stalk Λ (FV (coverOf A K L hL) Λ ρ) (genPt A) ≅ ModuleCat.of Λ V,
      e = stalkFVAt Λ ρ (geomPtAt (genPt A)) (lGen A K L hL) (hlGen A K L hL) := ⟨_, rfl⟩

/-- The generic stalk of `F_V` is `V` (sealed like `cIso`; `sIso_eq`). -/
def sIso (ρ : Representation Λ (coverOf A K L hL).G V) :
    stalk Λ (FV (coverOf A K L hL) Λ ρ) (genPt A) ≅ ModuleCat.of Λ V :=
  Classical.choose (exists_sIso L hL ρ)

theorem sIso_eq (ρ : Representation Λ (coverOf A K L hL).G V) :
    sIso L hL ρ = stalkFVAt Λ ρ (geomPtAt (genPt A)) (lGen A K L hL) (hlGen A K L hL) :=
  Classical.choose_spec (exists_sIso L hL ρ)

theorem sIso_galRep (ρ : Representation Λ (coverOf A K L hL).G V) (σ : Gal (genPt A))
    (w : stalk Λ (FV (coverOf A K L hL) Λ ρ) (genPt A)) :
    (sIso L hL ρ).hom.hom (galRep Λ (FV (coverOf A K L hL) Λ ρ) (genPt A) σ w) =
      ρ (resL A K L hL (genToPi1 A K σ)) ((sIso L hL ρ).hom.hom w) := by
  rw [sIso_eq]
  exact stalkFVGen_galRep A K L hL Λ ρ σ w

theorem sIso_FVMap (ρ : Representation Λ (coverOf A K L hL).G V) (ρW : Representation Λ (coverOf A K L hL).G W)
    (f : V →ₗ[Λ] W) (hf : ∀ σ, f ∘ₗ ρ σ = ρW σ ∘ₗ f) (v : V) :
    gs A (FVMap Λ ρ ρW f hf) ((sIso L hL ρ).inv.hom v) = (sIso L hL ρW).inv.hom (f v) := by
  rw [sIso_eq, sIso_eq]
  exact stalkFVAt_FVMap Λ ρ ρW f hf (geomPtAt (genPt A)) (lGen A K L hL) (hlGen A K L hL) v

/-- `sIso_FVMap` with the value `f v` supplied, so no computation happens under the stalk isomorphism. -/
theorem sIso_FVMap' (ρ : Representation Λ (coverOf A K L hL).G V) (ρW : Representation Λ (coverOf A K L hL).G W)
    (f : V →ₗ[Λ] W) (hf : ∀ σ, f ∘ₗ ρ σ = ρW σ ∘ₗ f) (v : V) (w : W) (h : f v = w) :
    gs A (FVMap Λ ρ ρW f hf) ((sIso L hL ρ).inv.hom v) = (sIso L hL ρW).inv.hom w := by
  rw [sIso_FVMap, h]

end SIso

/-- `Λ_X ≅ F_Λ` (trivial representation), with stalk map `1 ↦ 1`. -/
theorem exists_iso_unitSh_FV :
    ∃ E : unitSh Λ (Spec (CommRingCat.of A)) ≅ FV (coverOf A K L hL) Λ (Representation.trivial Λ (coverOf A K L hL).G Λ),
      gs A E.hom (oneStalk Λ (genPt A)) = (sIso L hL (Representation.trivial Λ (coverOf A K L hL).G Λ)).inv.hom (1 : Λ) := by
  obtain ⟨E, hE⟩ := exists_iso_of_stalk A isLisse_unitSh (isLisse_FV Λ _) (cIso A ≪≫ (sIso L hL (Representation.trivial Λ (coverOf A K L hL).G Λ)).symm)
    (fun σ v => by rw [galRep_unitSh, LinearMap.id_apply, galRep_FV_trivial])
  refine ⟨E, ?_⟩
  rw [hE, oneStalk_eq]
  exact trans_symm_inv_apply _ _ _

/-- `G ≅ F_M` over a cover through which the fibre representation factors, with stalk map `sIso⁻¹`. -/
theorem exists_iso_FV {G : EtSh Λ (Spec (CommRingCat.of A))} (hG : IsLisse Λ G)
    (ρM : Representation Λ (coverOf A K L hL).G (stalk Λ G (genPt A)))
    (hρM : ∀ τ, ρM (resL A K L hL τ) = EssSurj.fibRep A K G hG τ) :
    ∃ E : G ≅ FV (coverOf A K L hL) Λ ρM, ∀ m, gs A E.hom m = (sIso L hL ρM).inv.hom m := by
  have : Module.Finite Λ (stalk Λ G (genPt A)) := hG.finite_stalkF _
  have he : ∀ (σ : Gal (genPt A)) (v : stalk Λ G (genPt A)),
      (sIso L hL ρM).symm.hom.hom (galRep Λ G (genPt A) σ v) =
        galRep Λ (FV (coverOf A K L hL) Λ ρM) (genPt A) σ ((sIso L hL ρM).symm.hom.hom v) := by
    intro σ v
    rw [Iso.symm_hom]
    have h := sIso_galRep L hL ρM σ ((sIso L hL ρM).inv.hom v)
    rw [iso_inv_hom_apply Λ (sIso L hL ρM), hρM, EssSurj.fibRep_genToPi1] at h
    rw [← h, iso_hom_inv_apply Λ (sIso L hL ρM)]
  obtain ⟨E, hE⟩ := exists_iso_of_stalk A hG (isLisse_FV Λ ρM) (sIso L hL ρM).symm he
  refine ⟨E, fun m => ?_⟩
  rw [hE, Iso.symm_hom]

variable (A K)

/-- **Every continuous `π₁`-cocycle is realized by an extension with lisse middle term.** -/
theorem nonempty_realExt {G : EtSh Λ (Spec (CommRingCat.of A))} (hG : IsLisse Λ G)
    {c : Pi1 A K → stalk Λ G (genPt A)} (hc : IsCocycle (EssSurj.fibRep A K G hG) c)
    (hcl : IsLocallyConstant c) : Nonempty (RealExt A K G c) := by
  have : Module.Finite Λ (stalk Λ G (genPt A)) := hG.finite_stalkF _
  obtain ⟨L, hL, hk⟩ := exists_resL_ker_le A K _
    (isOpen_ker_extRep _ hc (EssSurj.isOpen_ker_fibRep A K G hG) hcl)
  have hkM : (resL A K L hL).ker ≤ (EssSurj.fibRep A K G hG).ker := fun τ hτ => by
    have h := hk hτ
    rw [MonoidHom.mem_ker] at h ⊢
    refine LinearMap.ext fun m => ?_
    have h' := congrArg Prod.fst (LinearMap.congr_fun h (m, 0))
    rw [extRep_apply] at h'
    simpa using h'
  obtain ⟨ρV, hρV⟩ : ∃ ρV : Representation Λ (coverOf A K L hL).G (stalk Λ G (genPt A) × Λ),
      ∀ τ, ρV (resL A K L hL τ) = extRep (EssSurj.fibRep A K G hG) c hc τ :=
    ⟨factorRep L hL Λ _ hk, factorRep_resL L hL Λ _ hk⟩
  obtain ⟨ρM, hρM⟩ : ∃ ρM : Representation Λ (coverOf A K L hL).G (stalk Λ G (genPt A)),
      ∀ τ, ρM (resL A K L hL τ) = EssSurj.fibRep A K G hG τ :=
    ⟨factorRep L hL Λ _ hkM, factorRep_resL L hL Λ _ hkM⟩
  have hf : ∀ σ : (coverOf A K L hL).G, LinearMap.inl Λ (stalk Λ G (genPt A)) Λ ∘ₗ ρM σ =
      ρV σ ∘ₗ LinearMap.inl Λ (stalk Λ G (genPt A)) Λ := by
    intro σ
    obtain ⟨τ, rfl⟩ := resL_surjective A K L hL σ
    refine LinearMap.ext fun m => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hρM, hρV, extRep_inl]
  have hg : ∀ σ : (coverOf A K L hL).G, LinearMap.snd Λ (stalk Λ G (genPt A)) Λ ∘ₗ ρV σ =
      Representation.trivial Λ (coverOf A K L hL).G Λ σ ∘ₗ LinearMap.snd Λ (stalk Λ G (genPt A)) Λ := by
    intro σ
    obtain ⟨τ, rfl⟩ := resL_surjective A K L hL σ
    refine LinearMap.ext fun v => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hρV, extRep_snd, Representation.trivial_apply]
  have hSV := FV_shortExact Λ ρM ρV (Representation.trivial Λ (coverOf A K L hL).G Λ)
    (LinearMap.inl Λ (stalk Λ G (genPt A)) Λ) (LinearMap.snd Λ (stalk Λ G (genPt A)) Λ) hf hg
    LinearMap.inl_injective LinearMap.snd_surjective (LinearMap.range_inl Λ _ Λ)
  obtain ⟨eG, heG⟩ := exists_iso_FV L hL hG ρM hρM
  obtain ⟨eU, heU⟩ := exists_iso_unitSh_FV (A := A) (K := K) (Λ := Λ) L hL
  have hz : FVMap Λ ρM ρV (LinearMap.inl Λ (stalk Λ G (genPt A)) Λ) hf ≫
      FVMap Λ ρV (Representation.trivial Λ (coverOf A K L hL).G Λ) (LinearMap.snd Λ (stalk Λ G (genPt A)) Λ) hg = 0 :=
    FVMap_comp_eq_zero Λ ρM ρV _ _ _ hf hg (comp_eq_zero_of_range_eq_ker Λ _ _ (LinearMap.range_inl Λ _ Λ))
  refine ⟨⟨FV (coverOf A K L hL) Λ ρV, eG.hom ≫ FVMap Λ ρM ρV (LinearMap.inl Λ (stalk Λ G (genPt A)) Λ) hf,
    FVMap Λ ρV (Representation.trivial Λ (coverOf A K L hL).G Λ) (LinearMap.snd Λ (stalk Λ G (genPt A)) Λ) hg ≫
      eU.inv,
    (sIso L hL ρV).inv.hom (0, 1),
    by rw [Category.assoc, ← Category.assoc (FVMap Λ ρM ρV _ hf), hz, zero_comp, comp_zero], ?_,
    isLisse_FV Λ ρV, ⟨?_, fun σ => ?_⟩⟩⟩
  · refine ShortComplex.shortExact_of_iso ?_ hSV
    refine ShortComplex.isoMk eG.symm (Iso.refl _) eU.symm ?_ ?_
    · simp
    · simp
  · exact gs_comp_inv_eq A _ eU _ _ ((sIso_FVMap' L hL ρV _ _ hg _ (1 : Λ) rfl).trans heU.symm)
  · exact coc_aux (sIso L hL ρV) (galRep Λ (FV (coverOf A K L hL) Λ ρV) (genPt A) σ) (EssSurj.fibRep A K G hG) c hc
      (genToPi1 A K σ) (fun n => (sIso_galRep L hL ρV σ n).trans (LinearMap.congr_fun (hρV _) _)) _
      (iso_inv_hom_apply Λ (sIso L hL ρV) _) _
      (by rw [gs_comp_apply, heG, sIso_FVMap, iso_inv_hom_apply Λ (sIso L hL ρV)])

/-- **The class `κ(c) ∈ H¹(Spec A, G)` of a continuous `π₁`-cocycle `c`.** -/
def kappa {G : EtSh Λ (Spec (CommRingCat.of A))} (hG : IsLisse Λ G) (c : Pi1 A K → stalk Λ G (genPt A))
    (hc : IsCocycle (EssSurj.fibRep A K G hG) c) (hcl : IsLocallyConstant c) : H Λ G 1 :=
  (Classical.choice (nonempty_realExt A K hG hc hcl)).se.extClass

/-- **Every short exact `0 → G → P → Λ_X → 0` realizing `c` has class `κ(c)`** (`P` arbitrary). -/
theorem kappa_eq {G P : EtSh Λ (Spec (CommRingCat.of A))} (hG : IsLisse Λ G)
    {c : Pi1 A K → stalk Λ G (genPt A)} (hc : IsCocycle (EssSurj.fibRep A K G hG) c) (hcl : IsLocallyConstant c)
    {f : G ⟶ P} {g : P ⟶ unitSh Λ (Spec (CommRingCat.of A))} {hfg : f ≫ g = 0}
    (hS : (ShortComplex.mk f g hfg).ShortExact) {w : stalk Λ P (genPt A)} (h : Realizes A K c f g w) :
    (hS.extClass : H Λ G 1) = kappa A K hG c hc hcl := by
  have := extClass_comp_eq A K hG (Classical.choice (nonempty_realExt A K hG hc hcl)).lis hS
    (Classical.choice (nonempty_realExt A K hG hc hcl)).se h (Classical.choice (nonempty_realExt A K hG hc hcl)).real
    (𝟙 G) (fun τ => gs_id_apply A _)
  rw [Abelian.Ext.comp_mk₀_id] at this
  exact this

end RamanujanPetersson.EtCompact

end

end

-- ===== S4.Def_RP_EtCompact_Spread =====
section

/-!
# S4-EtCompact, O9b part 6a: an extension of `Λ_X` by a lisse sheaf is lisse

* `constantSheaf_additive'`, `IsLisse.biprod'`: lisse ⊞ lisse is lisse;
* `exists_local_lift`: near every point, `1 ∈ Λ_X` lifts along an epimorphism `g : P ⟶ Λ_X`;
* `exists_section`: such a local lift gives a section `Λ_V → P|_V` of `g|_V`;
* **`isLisse_of_ext`**: in a short exact `0 → G → P → Λ_X → 0` with `G` lisse, `P` is lisse
  (locally `P|_V ≅ G|_V ⊞ Λ_V ≅ (M ⊞ Λ)_V`).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtCompact

open RamanujanPetersson.EtSheaves

universe u

variable {X : Scheme.{u}} {Λ : Type u} [CommRing Λ]

/-- Constant sheaves preserve binary biproducts (a left adjoint preserves binary coproducts). -/
instance constantSheaf_preservesBinaryBiproducts' :
    PreservesBinaryBiproducts (constantSheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) := by
  have := (constantSheafAdj X.smallEtaleTopology (ModuleCat.{u} Λ) (terminalIsTerminal (C := X.Etale))).isLeftAdjoint
  have : PreservesColimitsOfSize.{0, 0} (constantSheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :=
    (constantSheafAdj X.smallEtaleTopology (ModuleCat.{u} Λ)
      (terminalIsTerminal (C := X.Etale))).leftAdjoint_preservesColimits
  exact preservesBinaryBiproducts_of_preservesBinaryCoproducts _

/-- Constant sheaves are additive. -/
instance constantSheaf_additive' : (constantSheaf X.smallEtaleTopology (ModuleCat.{u} Λ)).Additive :=
  Functor.additive_of_preservesBinaryBiproducts _

/-- **Lisse ⊞ lisse is lisse.** -/
theorem IsLisse.biprod' {F G : EtSh Λ X} (hF : IsLisse Λ F) (hG : IsLisse Λ G) : IsLisse Λ (F ⊞ G) := by
  intro x
  obtain ⟨U, u, hu, M, hM, ⟨e⟩⟩ := hF x
  obtain ⟨V, v, hv, N, hN, ⟨e'⟩⟩ := hG x
  obtain ⟨W, w, hw, a, b, ha, hb⟩ := exists_common_refinement U V u v (hv.trans hu.symm)
  have : PreservesBinaryBiproducts (pull W.hom Λ) := preservesBinaryBiproducts_of_preservesBiproducts _
  refine ⟨W, w, hw.trans hu, M ⊞ N, ?_, ⟨(pull W.hom Λ).mapBiprod F G ≪≫ biprod.mapIso
    ((pullCongr Λ ha).app F ≪≫ restrictLocalIso U M e a)
    ((pullCongr Λ hb).app G ≪≫ restrictLocalIso V N e' b) ≪≫
      ((constantSheaf W.left.smallEtaleTopology (ModuleCat.{u} Λ)).mapBiprod M N).symm⟩⟩
  exact Module.Finite.equiv (ModuleCat.biprodIsoProd M N).toLinearEquiv.symm

/-- Restricting a local lift of `1` keeps it a local lift of `1`. -/
theorem lift_restrict {P : EtSh Λ X} (g : P ⟶ unitSh Λ X) {V W : X.Etale} (a : V ⟶ W)
    {s : P.obj.obj (op W)} (hs : (g.hom.app (op W)).hom s = (constUnit (ModuleCat.of Λ Λ) W).hom 1) :
    (g.hom.app (op V)).hom ((P.obj.map a.op).hom s) = (constUnit (ModuleCat.of Λ Λ) V).hom 1 := by
  have h1 := congrArg (fun φ => φ.hom s) (g.hom.naturality a.op)
  have h2 := (toSheafify X.smallEtaleTopology (constPre (X := X) (ModuleCat.of Λ Λ))).naturality a.op
  change 𝟙 _ ≫ constUnit (ModuleCat.of Λ Λ) V = constUnit (ModuleCat.of Λ Λ) W ≫ (unitSh Λ X).obj.map a.op at h2
  rw [Category.id_comp] at h2
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h1
  rw [h1, hs, h2, ModuleCat.hom_comp, LinearMap.comp_apply]

/-- **Local lifts of `1`**: near every point, `1 ∈ Λ_X` lifts along an epimorphism `g : P ⟶ Λ_X`. -/
theorem exists_local_lift {P : EtSh Λ X} (g : P ⟶ unitSh Λ X) [Epi g] (x : X) :
    ∃ (W : X.Etale) (w : W.left), W.hom w = x ∧ ∃ s : P.obj.obj (op W),
      (g.hom.app (op W)).hom s = (constUnit (ModuleCat.of Λ Λ) W).hom 1 := by
  have hep : Epi (((geomPtAt x).stalkF Λ).map g) := (epi_iff_stalk Λ g).1 inferInstance x
  obtain ⟨p, hp⟩ := (ModuleCat.epi_iff_surjective _).1 hep (oneStalk Λ x)
  obtain ⟨W, b, z, rfl⟩ := (geomPtAt x).point.toPresheafFiber_jointly_surjective (P := P.obj) p
  have h1 : (((geomPtAt x).stalkF Λ).map g).hom (((geomPtAt x).point.toPresheafFiber W b P.obj).hom z) =
      ((geomPtAt x).point.toPresheafFiber W b (unitSh Λ X).obj).hom ((g.hom.app (op W)).hom z) :=
    congrArg (fun φ => φ.hom z) (GrothendieckTopology.Point.toPresheafFiber_naturality
      (Φ := (geomPtAt x).point) g.hom W b)
  have h2 := congrArg (fun φ => φ.hom (1 : Λ)) (constUnit_germ (geomPtAt x) (ModuleCat.of Λ Λ) W b)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  have h3 : (geomPtAt x).point.toPresheafFiber W b (unitSh Λ X).obj ((g.hom.app (op W)).hom z) =
      (geomPtAt x).point.toPresheafFiber W b (unitSh Λ X).obj ((constUnit (ModuleCat.of Λ Λ) W).hom 1) := by
    refine h1.symm.trans (hp.trans ?_)
    exact h2.symm
  obtain ⟨W', f, b', hb', hfz⟩ := ((geomPtAt x).point.toPresheafFiber_eq_iff' W b _ _).1 h3
  obtain ⟨w, hw⟩ := (geomPtAt x).center_mem_range b'
  refine ⟨W', w, hw.trans (center_geomPtAt x), (P.obj.map f.op).hom z, ?_⟩
  have h4 := congrArg (fun φ => φ.hom z) (g.hom.naturality f.op)
  have h5 := (toSheafify X.smallEtaleTopology (constPre (X := X) (ModuleCat.of Λ Λ))).naturality f.op
  change 𝟙 _ ≫ constUnit (ModuleCat.of Λ Λ) W' = constUnit (ModuleCat.of Λ Λ) W ≫ (unitSh Λ X).obj.map f.op at h5
  rw [Category.id_comp] at h5
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h4
  rw [h4, h5]
  exact hfz

/-- **A local lift of `1` gives a section of `g` over `V`.** -/
theorem exists_section {P : EtSh Λ X} (g : P ⟶ unitSh Λ X) (V : X.Etale) (s : P.obj.obj (op V))
    (hs : (g.hom.app (op V)).hom s = (constUnit (ModuleCat.of Λ Λ) V).hom 1) :
    ∃ β : (pull V.hom Λ).obj (unitSh Λ X) ⟶ (pull V.hom Λ).obj P, β ≫ (pull V.hom Λ).map g = 𝟙 _ := by
  obtain ⟨α, hαt⟩ : ∃ α, homConstEquiv (ModuleCat.of Λ Λ) P V α =
      ModuleCat.ofHom (LinearMap.toSpanSingleton Λ _ s) := ⟨_, LinearEquiv.apply_symm_apply _ _⟩
  have hα : α ≫ Functor.whiskerLeft (Over.forget V).op g.hom = 𝟙 _ := by
    apply (homConstEquiv (ModuleCat.of Λ Λ) (unitSh Λ X) V).injective
    rw [homConstEquiv_apply, homConstEquiv_apply]
    have h1 : homConstEquiv (ModuleCat.of Λ Λ) P V α ≫ g.hom.app (op V) = constUnit (ModuleCat.of Λ Λ) V := by
      rw [hαt]
      refine ModuleCat.hom_ext (LinearMap.ext_ring ?_)
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom, LinearMap.toSpanSingleton_apply,
        one_smul]
      exact hs
    rw [homConstEquiv_apply] at h1
    exact (Category.assoc _ _ _).symm.trans (h1.trans (Category.comp_id _).symm)
  obtain ⟨β₀, hβ₀⟩ : ∃ β₀ : (res V.hom Λ).obj (unitSh Λ X) ⟶ (res V.hom Λ).obj P,
      β₀ ≫ (res V.hom Λ).map g = 𝟙 _ :=
    ⟨homOverEquiv (unitSh Λ X) P V α, Sheaf.hom_ext (NatTrans.ext (funext fun W =>
      congrArg (fun γ => NatTrans.app γ (op ((overOf V).obj W.unop))) hα))⟩
  refine ⟨(pullIsoRes V.hom Λ).hom.app (unitSh Λ X) ≫ β₀ ≫ (pullIsoRes V.hom Λ).inv.app P, ?_⟩
  rw [Category.assoc, Category.assoc, ← (pullIsoRes V.hom Λ).inv.naturality g, ← Category.assoc β₀, hβ₀,
    Category.id_comp, Iso.hom_inv_id_app]

/-- **An extension of `Λ_X` by a lisse sheaf is lisse.** -/
theorem isLisse_of_ext {G P : EtSh Λ X} (hG : IsLisse Λ G) {f : G ⟶ P} {g : P ⟶ unitSh Λ X}
    {hfg : f ≫ g = 0} (hS : (ShortComplex.mk f g hfg).ShortExact) : IsLisse Λ P := by
  intro x
  have hepi : Epi g := hS.epi_g
  obtain ⟨W, w, hw, s, hs⟩ := exists_local_lift g x
  obtain ⟨U, u, hu, M, hM, ⟨e⟩⟩ := hG x
  obtain ⟨V, v, hv, a, b, ha, hb⟩ := exists_common_refinement W U w u (hu.trans hw.symm)
  let aX : V ⟶ W := MorphismProperty.Over.homMk a ha.symm trivial
  obtain ⟨β, hβ⟩ := exists_section g V _ (lift_restrict g aX hs)
  have : PreservesFiniteColimits (pull V.hom Λ) := Functor.preservesFiniteColimits_of_preservesHomology _
  have hS' := hS.map_of_exact (pull V.hom Λ)
  let sp := ShortComplex.Splitting.ofExactOfSection _ hS'.exact β hβ hS'.mono_f
  have : Module.Finite Λ M := hM
  refine ⟨V, v, hv.trans hw, M ⊞ ModuleCat.of Λ Λ, ?_, ⟨sp.isoBinaryBiproduct ≪≫ biprod.mapIso
    ((pullCongr Λ hb).app G ≪≫ restrictLocalIso U M e b) (pullConst Λ V.hom (ModuleCat.of Λ Λ)) ≪≫
      ((constantSheaf V.left.smallEtaleTopology (ModuleCat.{u} Λ)).mapBiprod M (ModuleCat.of Λ Λ)).symm⟩⟩
  exact Module.Finite.equiv (ModuleCat.biprodIsoProd M (ModuleCat.of Λ Λ)).toLinearEquiv.symm

end RamanujanPetersson.EtCompact

end

end

-- ===== S4.Def_RP_EtCompact_Bridge =====
section

/-!
# S4-EtCompact, O9b part 6: `κ` is additive, kills coboundaries and is injective on `H¹`

* `fibRep_natural`: stalk maps intertwine the fibre representations;
* `kappa_comp` (naturality), **`kappa_add`**, `kappa_zero`, **`kappa_coboundary`** (`κ(dm) = 0`);
* **`exists_coboundary_of_kappa_eq_zero`**: `κ(c) = 0` only for coboundaries.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits

noncomputable section

namespace RamanujanPetersson.EtCompact

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtSheaves.GenBr RamanujanPetersson.EtSheaves.TorSec

variable (A K : Type) [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  [IsIntegrallyClosed A] {Λ : Type} [CommRing Λ]

variable [IsNoetherianRing A]

/-- **Naturality of `κ`.** -/
theorem kappa_comp {G₁ G₂ : EtSh Λ (Spec (CommRingCat.of A))} (hG₁ : IsLisse Λ G₁) (hG₂ : IsLisse Λ G₂)
    {c₁ : Pi1 A K → stalk Λ G₁ (genPt A)} {c₂ : Pi1 A K → stalk Λ G₂ (genPt A)}
    (hc₁ : IsCocycle (EssSurj.fibRep A K G₁ hG₁) c₁) (hcl₁ : IsLocallyConstant c₁)
    (hc₂ : IsCocycle (EssSurj.fibRep A K G₂ hG₂) c₂) (hcl₂ : IsLocallyConstant c₂) (u : G₁ ⟶ G₂)
    (hu : ∀ τ, gs A u (c₁ τ) = c₂ τ) :
    (kappa A K hG₁ c₁ hc₁ hcl₁).comp (Abelian.Ext.mk₀ u) (add_zero 1) = kappa A K hG₂ c₂ hc₂ hcl₂ :=
  extClass_comp_eq A K hG₁ (Classical.choice (nonempty_realExt A K hG₂ hc₂ hcl₂)).lis
    (Classical.choice (nonempty_realExt A K hG₁ hc₁ hcl₁)).se (Classical.choice (nonempty_realExt A K hG₂ hc₂ hcl₂)).se
    (Classical.choice (nonempty_realExt A K hG₁ hc₁ hcl₁)).real
    (Classical.choice (nonempty_realExt A K hG₂ hc₂ hcl₂)).real u hu

end RamanujanPetersson.EtCompact

end

end

-- ===== S4.Def_RP_EtCompact_P1Cover =====
section

/-!
# S4-EtCompact, part 33: the second chart of `P^1` and `H^1(P^1, Λ)` from `H^1(A^1, Λ)` (O8b, file 3)

* `dehom' = dehom ∘ swap` (`X₁ ↦ 1`, `X₀ ↦ t`), `awayDehom' : K[X₀, X₁]_(X₁) ≃ K[t]`, the chart
  `chartA1' : A^1_K ⟶ P^1_K` (`t ↦ [t : 1]`) with range `D₊(X₁)`.
* `P1.cover`: the two charts cover `P^1`; their overlap is nonempty and connected (`P^1` irreducible).
* **`P1.subsingleton_h1`**: `H^1(A^1, Λ) = 0 ⇒ H^1(P^1, Λ) = 0` (`subsingleton_h1_of_cover`).
-/

set_option autoImplicit false

open AlgebraicGeometry MvPolynomial CategoryTheory HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace RamanujanPetersson.EtCompact

open RamanujanPetersson.EtSheaves

universe u

section Chart1

variable {K : Type u} [Field K]

/-- Dehomogenization `X₁ ↦ 1`, `X₀ ↦ t`. -/
abbrev dehom' : MvPolynomial (Fin 2) K →ₐ[K] Polynomial K := dehom.comp swapP

end Chart1

section Cover

variable (K : Type u) [Field K]

end Cover

end RamanujanPetersson.EtCompact

end

end

-- ===== S4.Def_RP_EtCompact_H1 =====
section

/-!
# S4-EtCompact, O9b part 7: `H¹(Spec A, G) ≃ H¹_cont(π₁, G_η̄)` for lisse `G`

* `isRepExt_fibRep`: the generic stalk of `0 → G → P → Λ_X → 0` (`G`, `P` lisse) is an extension of
  `π₁`-representations;
* **`exists_kappa_eq`**: `κ` is surjective (write `e` as the class of a short exact sequence, its middle term is lisse
  by `isLisse_of_ext`, its generic stalk gives the cocycle);
* `kappaZ : Z¹ →+ H¹`, with kernel the coboundaries;
* **`h1Equiv A K hG : H Λ G 1 ≃+ CurveCoh.H1 (fibRep G) ⊤`**, with `h1Equiv_symm_mk`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits

noncomputable section

namespace RamanujanPetersson.EtCompact

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtSheaves.GenBr RamanujanPetersson.EtSheaves.TorSec

variable (A K : Type) [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  [IsIntegrallyClosed A] {Λ : Type} [CommRing Λ]

/-- The generic stalk of `0 → G → P → Λ_X → 0` (`G`, `P` lisse) is an extension of `π₁`-representations. -/
theorem isRepExt_fibRep {G P : EtSh Λ (Spec (CommRingCat.of A))} (hG : IsLisse Λ G) (hP : IsLisse Λ P)
    {f : G ⟶ P} {g : P ⟶ unitSh Λ (Spec (CommRingCat.of A))} {hfg : f ≫ g = 0}
    (hS : (ShortComplex.mk f g hfg).ShortExact) :
    IsRepExt (EssSurj.fibRep A K G hG) (EssSurj.fibRep A K P hP) (gs A f)
      (unitCoord Λ (genPt A) ∘ₗ gs A g) := by
  have hR := isRepExt_stalk (genPt A) hS
  refine ⟨hR.inj, hR.exact, fun τ => LinearMap.ext fun v => fibRep_natural A K hG hP f τ v, fun τ => ?_⟩
  obtain ⟨σ, rfl⟩ := genToPi1_surjective A K τ
  rw [EssSurj.fibRep_genToPi1]
  exact hR.equiv_p σ

/-- A function that only depends on `ρ τ`, for `ρ` with open kernel, is locally constant. -/
theorem isLocallyConstant_of_rep {M : Type} [AddCommGroup M] [Module Λ M] (ρ : Representation Λ (Pi1 A K) M)
    (hρ : IsOpen (ρ.ker : Set (Pi1 A K))) {β : Type} (c : Pi1 A K → β)
    (hc : ∀ τ τ', ρ τ = ρ τ' → c τ = c τ') : IsLocallyConstant c := by
  rw [IsLocallyConstant.iff_exists_open]
  intro τ
  refine ⟨(fun σ => τ⁻¹ * σ) ⁻¹' (ρ.ker : Set (Pi1 A K)), hρ.preimage (continuous_mul_left τ⁻¹), ?_,
    fun σ hσ => hc _ _ ?_⟩
  · show τ⁻¹ * τ ∈ ρ.ker
    rw [inv_mul_cancel]
    exact one_mem _
  · have h : ρ (τ⁻¹ * σ) = 1 := MonoidHom.mem_ker.1 hσ
    calc ρ σ = ρ (τ * (τ⁻¹ * σ)) := by rw [mul_inv_cancel_left]
      _ = ρ τ * ρ (τ⁻¹ * σ) := map_mul _ _ _
      _ = ρ τ := by rw [h, mul_one]

variable [IsNoetherianRing A]

/-- **`κ` is surjective**: every class in `H¹(Spec A, G)` is `κ(c)` of a continuous `π₁`-cocycle. -/
theorem exists_kappa_eq {G : EtSh Λ (Spec (CommRingCat.of A))} (hG : IsLisse Λ G) (e : H Λ G 1) :
    ∃ (c : Pi1 A K → stalk Λ G (genPt A)) (hc : IsCocycle (EssSurj.fibRep A K G hG) c)
      (hcl : IsLocallyConstant c), kappa A K hG c hc hcl = e := by
  obtain ⟨s, hs⟩ := exists_extClass_eq e
  have hS := pbSES_shortExact s
  have hP : IsLisse Λ (pbSES s).X₂ :=
    isLisse_of_ext (f := (pbSES s).f) (g := (pbSES s).g) (hfg := (pbSES s).zero) hG hS
  have hep : Epi (((geomPtAt (genPt A)).stalkF Λ).map (pbSES s).g) :=
    (epi_iff_stalk Λ _).1 hS.epi_g (genPt A)
  obtain ⟨w, hw⟩ := (ModuleCat.epi_iff_surjective _).1 hep (oneStalk Λ (genPt A))
  have hR := isRepExt_fibRep A K hG hP (f := (pbSES s).f) (g := (pbSES s).g) (hfg := (pbSES s).zero) hS
  have hc := isCocycle_extCocycle hR w
  have hcl : IsLocallyConstant (extCocycle hR w) := by
    refine isLocallyConstant_of_rep A K _ (EssSurj.isOpen_ker_fibRep A K _ hP) _ fun τ τ' h => ?_
    apply hR.inj
    rw [i_extCocycle, i_extCocycle, h]
  refine ⟨extCocycle hR w, hc, hcl, ?_⟩
  rw [← hs]
  refine (kappa_eq A K hG hc hcl (f := (pbSES s).f) (g := (pbSES s).g) (hfg := (pbSES s).zero) hS
    (w := w) ⟨hw, fun σ => ?_⟩).symm
  rw [i_extCocycle, EssSurj.fibRep_genToPi1]

theorem kappa_congr {G : EtSh Λ (Spec (CommRingCat.of A))} (hG : IsLisse Λ G)
    {c c' : Pi1 A K → stalk Λ G (genPt A)} (hc : IsCocycle (EssSurj.fibRep A K G hG) c) (hcl : IsLocallyConstant c)
    (hc' : IsCocycle (EssSurj.fibRep A K G hG) c') (hcl' : IsLocallyConstant c') (h : c = c') :
    kappa A K hG c hc hcl = kappa A K hG c' hc' hcl' := by
  subst h
  rfl

section Z1

variable {A K} {G : EtSh Λ (Spec (CommRingCat.of A))} {hG : IsLisse Λ G}

/-- A cocycle on `↥⊤` read on `π₁`. -/
def cz (z : CurveCoh.Z1 (EssSurj.fibRep A K G hG) ⊤) (τ : Pi1 A K) : stalk Λ G (genPt A) :=
  z.1 ⟨τ, Subgroup.mem_top τ⟩

theorem isCocycle_cz (z : CurveCoh.Z1 (EssSurj.fibRep A K G hG) ⊤) :
    IsCocycle (EssSurj.fibRep A K G hG) (cz z) := fun g h =>
  ((CurveCoh.mem_Z1 _ _ _).1 z.2).2 ⟨g, Subgroup.mem_top g⟩ ⟨h, Subgroup.mem_top h⟩

end Z1

variable {G : EtSh Λ (Spec (CommRingCat.of A))} (hG : IsLisse Λ G)

end RamanujanPetersson.EtCompact

end

end


