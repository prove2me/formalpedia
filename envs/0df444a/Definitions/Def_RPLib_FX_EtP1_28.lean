-- Prove2me | Definitions.Def_RPLib_FX_EtP1_28
-- name    : RPLib_FX_EtP1_28
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T12:17:34.92938+00:00
-- url     : https://prove2.me/theorems/62b51a2c-63a5-59e3-b951-62bfe7025441
-- title:
--   Étale cohomology of the projective line, library file 28 of 34
-- statement:
--   File 28 of 34 of the étale cohomology library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtCompact_GenUnit`: S4-EtCompact, D1: the unit `F ⟶ g_* g^* F` is an isomorphism at the generic point
--   * `S4.Def_RP_EtCompact_PtSub2`: S4-EtCompact, A3: `H¹(H, (I/F)_x̄) = 0` and lifting `H`-fixed elements (`H` open in `Gal x0`)
--   * `S4.Def_RP_EtCompact_R2Gen`: S4-EtCompact, A4: `R²g_* = 0` out of a `C₁` field point (hypothesis `hR` of `R1Gen.H_push_gen_eq_zero`)
--   * `S4.Def_RP_EtCompact_P1Hn`: S4-EtCompact: `H^2(G_m, Λ) = 0` and `H^(n+3)(P^1, Λ)` from the affine charts (O8c, file M7)
--   * `S4.Def_RP_EtCompact_CurveHn`: S4-EtCompact, A5: `H^(n+3) = 0` on `A¹`, `G_m` and `P¹` over an algebraically closed field (O8c, rest)
--   * `S4.Def_RP_EtCompact_P1H3`: S4-EtCompact, E4 (O7b): `H^(n+3)(P¹, F) = 0` for every sheaf `F`
--
--   **Formalization note.** One file of a library formalizing the étale cohomology of the projective line $\mathbf P^1_k = \operatorname{Proj} k[X_0, X_1]$ over an algebraically closed field $k$ with coefficients in sheaves of $\Lambda$-modules on the small étale site ($H^n = \operatorname{Ext}^n(\Lambda, -)$): $H^1(\mathbf P^1, \Lambda) = 0$, $H^2(\mathbf P^1, \Lambda) \cong \Lambda$ and $H^{n+3}(\mathbf P^1, F) = 0$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §1 (cohomology of curves) and Chapter III, §2 (Kummer theory); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Arcata », Chapter IV (cohomology of curves, Tsen's theorem)

import Mathlib
import Definitions.Def_RPLib_FX_EtP1_43

/-!
# Étale cohomology of the projective line, library file 28 of 34

Declarations of the formalization of the étale cohomology of the projective line over an algebraically
closed field (H¹ = 0, H² ≅ Λ, vanishing in degrees ≥ 3), re-hosted declaration by declaration from the
library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtCompact_GenUnit`: S4-EtCompact, D1: the unit `F ⟶ g_* g^* F` is an isomorphism at the generic point
* `S4.Def_RP_EtCompact_PtSub2`: S4-EtCompact, A3: `H¹(H, (I/F)_x̄) = 0` and lifting `H`-fixed elements (`H` open in `Gal x0`)
* `S4.Def_RP_EtCompact_R2Gen`: S4-EtCompact, A4: `R²g_* = 0` out of a `C₁` field point (hypothesis `hR` of `R1Gen.H_push_gen_eq_zero`)
* `S4.Def_RP_EtCompact_P1Hn`: S4-EtCompact: `H^2(G_m, Λ) = 0` and `H^(n+3)(P^1, Λ)` from the affine charts (O8c, file M7)
* `S4.Def_RP_EtCompact_CurveHn`: S4-EtCompact, A5: `H^(n+3) = 0` on `A¹`, `G_m` and `P¹` over an algebraically closed field (O8c, rest)
* `S4.Def_RP_EtCompact_P1H3`: S4-EtCompact, E4 (O7b): `H^(n+3)(P¹, F) = 0` for every sheaf `F`
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtCompact_GenUnit =====
section

/-!
# S4-EtCompact, D1: the unit `F ⟶ g_* g^* F` is an isomorphism at the generic point

`A` an integrally closed domain, `g = gen A : Y = Spec κ(η) ⟶ U = Spec A`, `x̄0 = geomPtAt x0`,
`Ψ = comapPt g x̄0`.

* `eq_zero_of_germ_std`: a section over `g^*(Spec S)` (`S ⊆ Ω` standard étale with one generic prime) whose germ at
  `fibOf S` vanishes is zero (one Galois orbit on the fibre);
* **`pushFib_injective`**: the base-change map `ρ_M : (g_* M)_Ψ ⟶ M_x̄0` is injective (spread a vanishing
  neighbourhood out over `A` with `StdSub.exists_sub`);
* **`isIso_stalk_unit`**: `(η_F)_Ψ` is an isomorphism (`comapIso_hom_app`: `β_F = (η_F)_Ψ ≫ ρ_{g^*F}`);
* `isZero_stalk_kernel_unit`, `isZero_stalk_cokernel_unit`: kernel and cokernel of `η_F` vanish at `η`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtCompact.GenUnit

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact.GenFrac RamanujanPetersson.EtCompact.LT
  RamanujanPetersson.EtCompact.FibMk

variable {A : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] {Λ : Type} [CommRing Λ]

omit [IsIntegrallyClosed A] in
theorem mono_genPt {F G : EtSh Λ (Spec (CommRingCat.of A))} (φ : F ⟶ G)
    (h : Mono ((comapPt (gen A) (geomPtAt (x0 A))).sheafFiber.map φ)) :
    Mono ((geomPtAt (GenBr.genPt A)).point.sheafFiber.map φ) := by
  have w := (ptIsoSheafFiber Λ (GPtIso.genPtIso A)).hom.naturality φ
  have h1 : Mono ((comapPt (gen A) (geomPtAt (x0 A))).sheafFiber.map φ ≫
      (ptIsoSheafFiber Λ (GPtIso.genPtIso A)).hom.app G) := mono_comp _ _
  rw [w] at h1
  have e : (geomPtAt (GenBr.genPt A)).point.sheafFiber.map φ =
      inv ((ptIsoSheafFiber Λ (GPtIso.genPtIso A)).hom.app F) ≫
        ((ptIsoSheafFiber Λ (GPtIso.genPtIso A)).hom.app F ≫ (geomPtAt (GenBr.genPt A)).point.sheafFiber.map φ) := by
    rw [IsIso.inv_hom_id_assoc]
  rw [e]
  exact mono_comp _ _

/-- The kernel of `η_F` vanishes at `η`. -/
theorem isZero_stalk_kernel_unit (F : EtSh Λ (Spec (CommRingCat.of A))) :
    IsZero (stalk Λ (kernel ((pullAdj (gen A) Λ).unit.app F)) (GenBr.genPt A)) := by
  have := isIso_stalk_unit (Λ := Λ) F
  have hm := mono_genPt ((pullAdj (gen A) Λ).unit.app F) inferInstance
  have : Mono (((geomPtAt (GenBr.genPt A)).stalkF Λ).map ((pullAdj (gen A) Λ).unit.app F)) := hm
  exact (isZero_kernel_of_mono (((geomPtAt (GenBr.genPt A)).stalkF Λ).map ((pullAdj (gen A) Λ).unit.app F))).of_iso
    (PreservesKernel.iso ((geomPtAt (GenBr.genPt A)).stalkF Λ) ((pullAdj (gen A) Λ).unit.app F))

/-- The cokernel of `η_F` vanishes at `η`. -/
theorem isZero_stalk_cokernel_unit (F : EtSh Λ (Spec (CommRingCat.of A))) :
    IsZero (stalk Λ (cokernel ((pullAdj (gen A) Λ).unit.app F)) (GenBr.genPt A)) := by
  have := isIso_stalk_unit (Λ := Λ) F
  exact GPtIso.isZero_stalk_cokernel _ inferInstance

end RamanujanPetersson.EtCompact.GenUnit

end

end

-- ===== S4.Def_RP_EtCompact_PtSub2 =====
section

/-!
# S4-EtCompact, A3: `H¹(H, (I/F)_x̄) = 0` and lifting `H`-fixed elements (`H` open in `Gal x0`)

* **`coboundary_of_coker_sub`**: `H`-cocycles in `(I/F)_x̄` are coboundaries when `H²(H, F_x̄) = 0`
  (`H`-version of `PtCd.coboundary_of_coker`, using `coboundary_of_injective_sub`);
* **`lift_fixed_sub`**: an `H`-fixed element of `(I/N)_x̄` lifts to an `H`-fixed element of `I_x̄` when
  `H`-cocycles in `N_x̄` are coboundaries.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Topology

noncomputable section

namespace RamanujanPetersson.EtCompact.PtSub

open RamanujanPetersson.EtSheaves RamanujanPetersson.CdOne RamanujanPetersson.EtCompact

universe u

variable {X : Scheme.{u}} (x0 : X) [IsIso (X.fromSpecResidueField x0)] {Λ : Type u} [CommRing Λ]

/-- **`H`-cocycles in `(I/F)_x̄` are coboundaries** when `H²(H, F_x̄) = 0`. -/
theorem coboundary_of_coker_sub (F : EtSh Λ X) (H : Subgroup (Gal x0)) (hH : IsOpen (H : Set (Gal x0)))
    (hF : PtH2Sub x0 H F) {c : H → stalk Λ (cokernel (Injective.ι F)) x0}
    (hc : IsCocycle ((galRep Λ (cokernel (Injective.ι F)) x0).comp H.subtype) c) (hcl : IsLocallyConstant c) :
    ∃ m₀, ∀ g : H, c g = galRep Λ (cokernel (Injective.ι F)) x0 g m₀ - m₀ := by
  set ρQ := galRep Λ (cokernel (Injective.ι F)) x0
  set ρI := galRep Λ (Injective.under F) x0
  set ρF := galRep Λ F x0
  set ι := (((geomPtAt x0).stalkF Λ).map (Injective.ι F)).hom
  set π := (((geomPtAt x0).stalkF Λ).map (cokernel.π (Injective.ι F))).hom
  have hc' : ∀ g h : H, c (g * h) = c g + ρQ g (c h) := hc
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
  obtain ⟨b, hbπ, hbl⟩ : ∃ b : H → stalk Λ (Injective.under F) x0, (∀ g, π (b g) = c g) ∧
      IsLocallyConstant b :=
    ⟨fun g => Function.surjInv hsurj (c g), fun g => Function.surjInv_eq hsurj _,
      by exact hcl.comp (Function.surjInv hsurj)⟩
  have hρI := galRep_isDiscrete x0 (Injective.under F)
  have hf2l : IsLocallyConstant fun p : H × H => ρI p.1 (b p.2) - b (p.1 * p.2) + b p.1 := by
    have h1 : IsLocallyConstant fun p : H × H => ρI p.1 (b p.2) :=
      hρI.lc_apply (continuous_subtype_val.comp continuous_fst) (hbl.comp_continuous continuous_snd)
    have h2 : IsLocallyConstant fun p : H × H => b (p.1 * p.2) := hbl.comp_continuous continuous_mul
    have h3 : IsLocallyConstant fun p : H × H => b p.1 := hbl.comp_continuous continuous_fst
    exact (h1.comp₂ h2 (· - ·)).comp₂ h3 (· + ·)
  have hmem : ∀ p : H × H, ∃ y, ι y = ρI p.1 (b p.2) - b (p.1 * p.2) + b p.1 := by
    intro p
    refine LinearMap.mem_range.1 (hex (LinearMap.mem_ker.2 ?_))
    rw [map_add, map_sub, hπeq, hbπ, hbπ, hbπ, hc' p.1 p.2]
    abel
  choose f' hf' using hmem
  have hf'l : IsLocallyConstant f' := by
    refine IsLocallyConstant.desc f' ι ?_ hinj
    have : (⇑ι ∘ f') = fun p : H × H => ρI p.1 (b p.2) - b (p.1 * p.2) + b p.1 := funext hf'
    rw [this]
    exact hf2l
  have hf'c : ∀ g h j : H, f' (g * h, j) + f' (g, h) = ρF g (f' (h, j)) + f' (g, h * j) := by
    intro g h j
    apply hinj
    rw [map_add, map_add, hιeq, hf', hf', hf', hf']
    simp only [map_add, map_sub, Subgroup.coe_mul, map_mul, Module.End.mul_apply, mul_assoc]
    abel
  obtain ⟨a, hal, ha⟩ := hF f' hf'l hf'c
  have hb'c : IsCocycle (ρI.comp H.subtype) (fun g => b g - ι (a g)) := by
    intro g h
    have e1 := hf' (g, h)
    rw [ha g h, map_add, map_sub, hιeq] at e1
    show b (g * h) - ι (a (g * h)) = b g - ι (a g) + ρI g (b h - ι (a h))
    rw [← sub_eq_zero, ← sub_eq_zero.2 e1]
    simp only [map_sub]
    abel
  have hb'l : IsLocallyConstant fun g : H => b g - ι (a g) := hbl.comp₂ (hal.comp ι) (· - ·)
  obtain ⟨m₀, hm₀⟩ := coboundary_of_injective_sub x0 (Injective.under F) H hH hb'c hb'l
  refine ⟨π m₀, fun g => ?_⟩
  have hm : b g - ι (a g) = ρI g m₀ - m₀ := hm₀ g
  rw [← hbπ g, ← hπeq, ← map_sub, ← hm, map_sub, hπι, sub_zero]

/-- **Lifting `H`-fixed elements** through `I_x̄ → (I/N)_x̄` when `H`-cocycles in `N_x̄` are coboundaries. -/
theorem lift_fixed_sub (N : EtSh Λ X) (H : Subgroup (Gal x0))
    (hN : ∀ c : H → stalk Λ N x0, IsCocycle ((galRep Λ N x0).comp H.subtype) c → IsLocallyConstant c →
      ∃ m₀, ∀ g : H, c g = galRep Λ N x0 g m₀ - m₀)
    (y : stalk Λ (cokernel (Injective.ι N)) x0) (hy : ∀ s ∈ H, galRep Λ (cokernel (Injective.ι N)) x0 s y = y) :
    ∃ m : stalk Λ (Injective.under N) x0, (∀ s ∈ H, galRep Λ (Injective.under N) x0 s m = m) ∧
      (((geomPtAt x0).stalkF Λ).map (cokernel.π (Injective.ι N))).hom m = y := by
  set ρQ := galRep Λ (cokernel (Injective.ι N)) x0
  set ρI := galRep Λ (Injective.under N) x0
  set ρN := galRep Λ N x0
  set ι := (((geomPtAt x0).stalkF Λ).map (Injective.ι N)).hom
  set π := (((geomPtAt x0).stalkF Λ).map (cokernel.π (Injective.ι N))).hom
  have hP := injPres_shortExact N
  have hinj : Function.Injective ι :=
    (ModuleCat.mono_iff_injective _).1 ((mono_iff_stalk Λ _).1 hP.mono_f x0)
  have hsurj : Function.Surjective π :=
    (ModuleCat.epi_iff_surjective _).1 ((epi_iff_stalk Λ _).1 hP.epi_g x0)
  have hex : LinearMap.ker π ≤ LinearMap.range ι := by
    have := (exact_iff_stalk Λ _).1 hP.exact x0
    rw [ShortComplex.moduleCat_exact_iff_ker_sub_range] at this
    exact this
  have hπι : ∀ z, π (ι z) = 0 := fun z => by
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← CategoryTheory.Functor.map_comp, cokernel.condition,
      CategoryTheory.Functor.map_zero, ModuleCat.hom_zero, LinearMap.zero_apply]
  have hιeq : ∀ g z, ι (ρN g z) = ρI g (ι z) := fun g z =>
    LinearMap.congr_fun (galRep_natural Λ (Injective.ι N) x0 g) z
  have hπeq : ∀ g z, π (ρI g z) = ρQ g (π z) := fun g z =>
    LinearMap.congr_fun (galRep_natural Λ (cokernel.π (Injective.ι N)) x0 g) z
  obtain ⟨m0, hm0⟩ := hsurj y
  have hmem : ∀ s : H, ∃ z, ι z = ρI s m0 - m0 := fun s =>
    LinearMap.mem_range.1 (hex (LinearMap.mem_ker.2 (by rw [map_sub, hπeq, hm0, hy s s.2, sub_self])))
  choose c hc using hmem
  have hcl : IsLocallyConstant c := by
    refine IsLocallyConstant.desc c ι ?_ hinj
    have : (⇑ι ∘ c) = fun s : H => ρI s m0 - m0 := funext hc
    rw [this]
    exact (((galRep_isDiscrete x0 (Injective.under N)).lc_orbit m0).comp_continuous
      continuous_subtype_val).comp (· - m0)
  have hcc : IsCocycle (ρN.comp H.subtype) c := by
    intro g h
    apply hinj
    show ι (c (g * h)) = ι (c g + ρN g (c h))
    rw [map_add, hιeq, hc, hc, hc, Subgroup.coe_mul, map_mul, Module.End.mul_apply, map_sub]
    abel
  obtain ⟨n, hn⟩ := hN c hcc hcl
  refine ⟨m0 - ι n, fun s hs => ?_, by rw [map_sub, hm0, hπι, sub_zero]⟩
  have h1 : ι (c ⟨s, hs⟩) = ρI s m0 - m0 := hc ⟨s, hs⟩
  rw [hn ⟨s, hs⟩, map_sub, hιeq] at h1
  try dsimp only at h1
  have h2 : ρI s (ι n) = ι n + (ρI s m0 - m0) := by
    rw [← h1]
    abel
  rw [map_sub, h2]
  abel

end RamanujanPetersson.EtCompact.PtSub

end

end

-- ===== S4.Def_RP_EtCompact_R2Gen =====
section

/-!
# S4-EtCompact, A4: `R²g_* = 0` out of a `C₁` field point (hypothesis `hR` of `R1Gen.H_push_gen_eq_zero`)

`Y ≅ Spec κ(y0)`, `g : Y ⟶ Z` any morphism, `HypL ℓ (Gal y0)`, `ℓ^k = 0` in `Λ`.

* `exists_open_stab`, `stab`, `stab_isOpen`: stabilisers of fibre points are open subgroups of `Gal y0`;
* **`app_surjective`**: `I(W) → (I/Qt M)(W)` is surjective for every étale `W → Y` (lift the germs with
  `PtSub.lift_fixed_sub` + `PtSub.coboundary_of_coker_sub` for `H = stab a`, glue with
  `GalLift.exists_lift_of_fixed`), i.e. `H¹(W, Qt M) = 0`;
* **`isZero_R1_qt`**: `R¹g_*(Qt M) = 0` (`≅ R²g_* M`): `g_*` of `I → I/Qt M` is surjective on sections;
* **`isZero_R1_qt_of_C1`**: the same at `Spec κ(y)` for a `C₁` residue field with a primitive `ℓ`-th root of 1.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Topology

noncomputable section

namespace RamanujanPetersson.EtCompact.R2Gen

open RamanujanPetersson.EtSheaves RamanujanPetersson.CdOne RamanujanPetersson.EtCompact RamanujanPetersson.Tsen

universe u

section Stab

variable {X : Scheme.{u}} (x : X)

/-- **The stabiliser of a fibre point contains an open subgroup.** -/
theorem exists_open_stab (U : X.Etale) (a : (geomPtAt x).point.fiber.obj U) :
    ∃ H : Subgroup (Gal x), IsOpen (H : Set (Gal x)) ∧ ∀ σ ∈ H, (galAct x σ).app U a = a := by
  obtain ⟨⟨u, φ⟩, hp⟩ :=
    (Scheme.SpecToEquivOfField (geomPtAt x).Ω U.left).symm.surjective ((geomPtAt x).liftOf a).left
  have hp' : Spec.map φ ≫ U.left.fromSpecResidueField u = ((geomPtAt x).liftOf a).left := hp
  have hw : ((geomPtAt x).liftOf a).left ≫ U.hom = (geomPtAt x).pt := Over.w ((geomPtAt x).liftOf a)
  have key : (Scheme.SpecToEquivOfField (geomPtAt x).Ω X).symm
      ⟨U.hom.base u, U.hom.residueFieldMap u ≫ φ⟩ = (geomPtAt x).pt := by
    change Spec.map (U.hom.residueFieldMap u ≫ φ) ≫ X.fromSpecResidueField (U.hom.base u) = _
    rw [Spec.map_comp, Category.assoc, Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
      ← Category.assoc]
    exact (congrArg (· ≫ U.hom) hp').trans hw
  have hpt : (Scheme.SpecToEquivOfField (geomPtAt x).Ω X) (geomPtAt x).pt =
      ⟨x, CommRingCat.ofHom (algebraMap (X.residueField x) (SeparableClosure (X.residueField x)))⟩ :=
    (Scheme.SpecToEquivOfField (SeparableClosure (X.residueField x)) X).apply_symm_apply _
  have key2 : (⟨U.hom.base u, U.hom.residueFieldMap u ≫ φ⟩ :
      Σ y : X, X.residueField y ⟶ CommRingCat.of (geomPtAt x).Ω) =
      (Scheme.SpecToEquivOfField (geomPtAt x).Ω X) (geomPtAt x).pt := by
    rw [← key, Equiv.apply_symm_apply]
  obtain ⟨e, hφ⟩ := Scheme.SpecToEquivOfField_eq_iff.1 (key2.trans hpt)
  have e' : U.hom.base u = x := e
  subst e'
  have hφ' : ∀ r : X.residueField (U.hom.base u),
      φ.hom (U.hom.residueFieldMap u r) =
        algebraMap (X.residueField (U.hom.base u)) (SeparableClosure (X.residueField (U.hom.base u))) r :=
    fun r => congrArg (fun g => g.hom r) hφ
  let : Algebra (X.residueField (U.hom.base u)) (U.left.residueField u) :=
    (U.hom.residueFieldMap u).hom.toAlgebra
  have : Module.Finite (X.residueField (U.hom.base u)) (U.left.residueField u) := residueField_finite U.hom u
  let φ' : U.left.residueField u →ₐ[X.residueField (U.hom.base u)]
      SeparableClosure (X.residueField (U.hom.base u)) :=
    { toRingHom := φ.hom
      commutes' := hφ' }
  have : FiniteDimensional (X.residueField (U.hom.base u)) φ'.fieldRange :=
    LinearEquiv.finiteDimensional (AlgHom.equivFieldRange φ').toLinearEquiv
  refine ⟨φ'.fieldRange.fixingSubgroup, IntermediateField.fixingSubgroup_isOpen _, fun σ hσ => ?_⟩
  refine fiber_ext _ ?_
  rw [galAct_left]
  have hfix : ∀ t : U.left.residueField u, σ (φ.hom t) = φ.hom t := fun t =>
    (IntermediateField.mem_fixingSubgroup_iff _ σ).1 hσ (φ.hom t) ⟨t, rfl⟩
  have hc : φ ≫ CommRingCat.ofHom (σ : SeparableClosure (X.residueField (U.hom.base u)) →+*
      SeparableClosure (X.residueField (U.hom.base u))) = φ := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro t
    exact hfix t
  have hS : galSpec (U.hom.base u) σ ≫ Spec.map φ = Spec.map φ :=
    (Spec.map_comp φ _).symm.trans (congrArg Spec.map hc)
  rw [← hp']
  exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ U.left.fromSpecResidueField u) hS)

/-- The stabiliser of a fibre point. -/
def stab (U : X.Etale) (a : (geomPtAt x).point.fiber.obj U) : Subgroup (Gal x) where
  carrier := {σ | (galAct x σ).app U a = a}
  mul_mem' {σ τ} hσ hτ := by
    show (galAct x (σ * τ)).app U a = a
    rw [galAct_mul, show (galAct x τ).app U a = a from hτ, show (galAct x σ).app U a = a from hσ]
  one_mem' := galAct_one x U a
  inv_mem' {σ} hσ := by
    show (galAct x σ⁻¹).app U a = a
    conv_lhs => rw [← show (galAct x σ).app U a = a from hσ]
    rw [← galAct_mul, inv_mul_cancel, galAct_one]

theorem stab_isOpen (U : X.Etale) (a : (geomPtAt x).point.fiber.obj U) : IsOpen (stab x U a : Set (Gal x)) := by
  obtain ⟨H, hH, hHs⟩ := exists_open_stab x U a
  exact Subgroup.isOpen_mono (fun σ hσ => hHs σ hσ) hH

end Stab

section Field

variable {Y : Scheme.{u}} (y0 : Y) [IsIso (Y.fromSpecResidueField y0)] {Λ : Type u} [CommRing Λ]

/-- **`H¹(W, Qt M) = 0` for every étale `W` over a field point**: `I(W) → (I/Qt M)(W)` is surjective. -/
theorem app_surjective (l : ℕ) [Fact l.Prime] (hL : HypL l (Gal y0)) (k : ℕ) (hΛ : ((l ^ k : ℕ) : Λ) = 0)
    (M : EtSh Λ Y) (W : Y.Etale) :
    Function.Surjective ((cokernel.π (Injective.ι (Qt Λ M))).hom.app (op W)).hom := by
  intro q
  refine GalLift.exists_lift_of_fixed y0 (cokernel.π (Injective.ι (Qt Λ M))) W q fun a => ?_
  have hH := stab_isOpen y0 W a
  obtain ⟨m, hm, hmπ⟩ := PtSub.lift_fixed_sub y0 (Qt Λ M) (stab y0 W a)
    (fun c hc hcl => PtSub.coboundary_of_coker_sub y0 M (stab y0 W a) hH
      (PtSub.ptH2Sub_of_hypL y0 l hL k hΛ _ hH M) hc hcl)
    (((geomPtAt y0).point.toPresheafFiber W a (cokernel (Injective.ι (Qt Λ M))).obj).hom q)
    (fun s hs => by
      rw [← galRep_germ Λ _ y0 s W a q, show (galAct y0 s).app W a = a from hs])
  exact ⟨m, fun σ hσ => hm σ hσ, hmπ⟩

/-- **`R²g_* = 0`**: `R¹g_*(Qt M) = 0` for every `g : Y ⟶ Z` out of a field point with `HypL ℓ`. -/
theorem isZero_R1_qt {Z : Scheme.{u}} (g : Y ⟶ Z) (l : ℕ) [Fact l.Prime] (hL : HypL l (Gal y0)) (k : ℕ)
    (hΛ : ((l ^ k : ℕ) : Λ) = 0) (M : EtSh Λ Y) : IsZero (R1 g Λ (Qt Λ M)) := by
  have : Sheaf.IsLocallySurjective ((push g Λ).map (cokernel.π (Injective.ι (Qt Λ M)))) :=
    Presheaf.isLocallySurjective_of_surjective _ _ fun V =>
      app_surjective y0 l hL k hΛ M ((etPull g).obj V.unop)
  have : Epi ((push g Λ).map (cokernel.π (Injective.ι (Qt Λ M)))) :=
    (Sheaf.isLocallySurjective_iff_epi' _ _).1 this
  exact isZero_cokernel_of_epi _

end Field

/-- **`R²g_* = 0` out of `Spec κ(y)`** for a `C₁` residue field with a primitive `ℓ`-th root of unity. -/
theorem isZero_R1_qt_of_C1 {Y : Scheme.{u}} (y : Y) {Λ : Type u} [CommRing Λ] (hC1 : IsC1 (Y.residueField y))
    (l : ℕ) [Fact l.Prime] (hl : (l : Y.residueField y) ≠ 0) {ζ : Y.residueField y} (hζ : IsPrimitiveRoot ζ l)
    (m : ℕ) (hΛ : ((l ^ m : ℕ) : Λ) = 0) {Z : Scheme.{u}} (g : Spec (Y.residueField y) ⟶ Z)
    (M : EtSh Λ (Spec (Y.residueField y))) : IsZero (R1 g Λ (Qt Λ M)) := by
  let φ := (ptResidueIso y).commRingCatIsoToRingEquiv
  refine isZero_R1_qt (ptOf y) g l (hypL_gal _ (isC1_of_ringEquiv φ hC1) l ?_ (hζ.map_of_injective φ.injective))
    m hΛ M
  rw [← map_natCast φ]
  exact (_root_.map_ne_zero φ).2 hl

end RamanujanPetersson.EtCompact.R2Gen

end

end

-- ===== S4.Def_RP_EtCompact_P1Hn =====
section

/-!
# S4-EtCompact: `H^2(G_m, Λ) = 0` and `H^(n+3)(P^1, Λ)` from the affine charts (O8c, file M7)

* `LX.isC1_genField`, `LX.H_genPt_eq_zero`: the generic point of `G_m` is `C₁` (Tsen), so `H^(n+2)` vanishes there;
* **`Gm.H_two_eq_zero`**: `H^2(G_m, Λ) = 0` (`H2Pid.H_two_eq_zero_of_root` for the PID `k[X]_X`);
* `P1.hSuccEquiv`: `H^(n+1)(P^1, Λ) ≃+ H^n(G_m, Λ)` when `H^n(A^1, Λ) = H^(n+1)(A^1, Λ) = 0` (Mayer-Vietoris);
* **`P1.subsingleton_h_add_three`**: `H^(n+3)(P^1, Λ) = 0` when `H^(n+2)`, `H^(n+3)` of `A^1` and `H^(n+2)` of `G_m`
  vanish.
-/

set_option autoImplicit false

open Polynomial AlgebraicGeometry CategoryTheory

noncomputable section

namespace RamanujanPetersson.EtCompact

open RamanujanPetersson.EtSheaves RamanujanPetersson.CdOne RamanujanPetersson.Tsen

section GmH2

variable (k : Type) [Field k] [IsAlgClosed k]

/-- The constants `k → κ(η)` of `G_m`. -/
def LX.genConst : k →+* GenBr.genField (LX k) :=
  (GenBr.fracIso (LX k) (RatFunc k)).toRingHom.comp (algebraMap k (RatFunc k))

omit [IsAlgClosed k] in
theorem LX.genConst_injective : Function.Injective (LX.genConst k) :=
  (GenBr.fracIso (LX k) (RatFunc k)).injective.comp (algebraMap k (RatFunc k)).injective

/-- `κ(η)` of `G_m` is `C₁` (Tsen). -/
theorem LX.isC1_genField : IsC1 (GenBr.genField (LX k)) :=
  isC1_of_ringEquiv (GenBr.fracIso (LX k) (RatFunc k)) (isC1_ratFunc k)

/-- **`H^(n+2)(Spec κ(η), F) = 0`** at the generic point `η` of `G_m`. -/
theorem LX.H_genPt_eq_zero {Λ : Type} [CommRing Λ] (l : ℕ) [Fact l.Prime] (hl : (l : k) ≠ 0) (m : ℕ)
    (hΛ : ((l ^ m : ℕ) : Λ) = 0) (n : ℕ)
    (F : EtSh Λ (Spec ((Spec (CommRingCat.of (LX k))).residueField (GenBr.genPt (LX k))))) (e : H Λ F (n + 2)) :
    e = 0 := by
  have : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_of_ne k hl
  refine H_ptOf_eq_zero_of_C1 (GenBr.genPt (LX k)) (LX.isC1_genField k) l ?_
    (hζ.map_of_injective (LX.genConst_injective k)) m hΛ n F e
  rw [← map_natCast (LX.genConst k)]
  exact (_root_.map_ne_zero (LX.genConst k)).2 hl

/-- **`H^2(G_m, Λ) = 0`** (`k` algebraically closed, `ℓ ≠ char k`, `ℓ^m = 0` in `Λ`). -/
theorem Gm.H_two_eq_zero {Λ : Type} [CommRing Λ] (l : ℕ) [Fact l.Prime] (hl : (l : k) ≠ 0) (m : ℕ)
    (hΛ : ((l ^ m : ℕ) : Λ) = 0) (e : H Λ (unitSh Λ (Gm k)) 2) : e = 0 := by
  have : NeZero (l ^ m) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hlm : ((l ^ m : ℕ) : k) ≠ 0 := by
    rw [Nat.cast_pow]
    exact pow_ne_zero _ hl
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_of_ne k hlm
  exact H2Pid.H_two_eq_zero_of_root (LX k) (fun M e => LX.H_genPt_eq_zero k l hl m hΛ 0 M e)
    (LX.isUnit_natCast k hlm) (hζ.map_of_injective (f := (algebraMap k[X] (LX k)).comp C) ((LX.injective k).comp C_injective)) hΛ e

theorem Gm.subsingleton_h2 {Λ : Type} [CommRing Λ] (l : ℕ) [Fact l.Prime] (hl : (l : k) ≠ 0) (m : ℕ)
    (hΛ : ((l ^ m : ℕ) : Λ) = 0) : Subsingleton (H Λ (unitSh Λ (Gm k)) 2) :=
  ⟨fun a b => by rw [Gm.H_two_eq_zero k l hl m hΛ a, Gm.H_two_eq_zero k l hl m hΛ b]⟩

end GmH2

section P1Hn

variable (K : Type) [Field K] {Λ : Type} [CommRing Λ]

end P1Hn

end RamanujanPetersson.EtCompact

end

end

-- ===== S4.Def_RP_EtCompact_CurveHn =====
section

/-!
# S4-EtCompact, A5: `H^(n+3) = 0` on `A¹`, `G_m` and `P¹` over an algebraically closed field (O8c, rest)

* `gal_closed`: closed points of a finite type `k`-algebra (`k` algebraically closed) have trivial Galois groups
  (Mathlib `residueFieldIsoBase`);
* **`H_add_three_eq_zero`**: `H^(n+3)(Spec A, Λ) = 0` for a noetherian integrally closed domain of dimension `≤ 1`
  with `H²(η, -) = 0`, `R²g_* = 0` and Galois-trivial closed points (`R1Gen.H_push_gen_eq_zero` +
  `SgUnit.unitIsoPush`);
* **`A1.H_add_three_eq_zero`**, **`Gm.H_add_three_eq_zero`**: the hypotheses hold for `k[X]`, `k[X]_X` (Tsen +
  `R2Gen.isZero_R1_qt_of_C1`);
* **`P1.H_add_three_eq_zero`**: `H^(n+3)(P¹, Λ) = 0` (`P1.subsingleton_h_add_three`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Polynomial

noncomputable section

namespace RamanujanPetersson.EtCompact.CurveHn

open RamanujanPetersson.EtSheaves RamanujanPetersson.CdOne RamanujanPetersson.EtCompact RamanujanPetersson.Tsen
  RamanujanPetersson.EtCompact.GenFrac

section Closed

variable (k : Type) [Field k] [IsAlgClosed k] (A : Type) [CommRing A] [Algebra k A] [Algebra.FiniteType k A]

include k

theorem locallyOfFiniteType_spec : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k A))) :=
  (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).2 (RingHom.finiteType_algebraMap.2 inferInstance)

theorem isAlgClosed_residue (y : Spec (CommRingCat.of A)) (hy : IsClosed ({y} : Set (Spec (CommRingCat.of A)))) :
    IsAlgClosed ((Spec (CommRingCat.of A)).residueField y) := by
  have := locallyOfFiniteType_spec k A
  exact IsAlgClosed.of_ringEquiv k _
    (residueFieldIsoBase (Spec.map (CommRingCat.ofHom (algebraMap k A))) y hy).symm.commRingCatIsoToRingEquiv

end Closed

section Curves

variable (k : Type) [Field k] [IsAlgClosed k] {Λ : Type} [CommRing Λ] (l : ℕ) [Fact l.Prime] (hl : (l : k) ≠ 0)
  (m : ℕ) (hΛ : ((l ^ m : ℕ) : Λ) = 0)

include hl hΛ

omit [IsAlgClosed k] hl hΛ in
instance LX.finiteType : Algebra.FiniteType k (LX k) :=
  Algebra.FiniteType.trans (S := k[X]) inferInstance
    (IsLocalization.finiteType_of_monoid_fg (Submonoid.powers (X : k[X])) (LX k))

end Curves

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

variable (l : ℕ) [Fact l.Prime] (hl : (l : k) ≠ 0) (m : ℕ) (hΛ : ((l ^ m : ℕ) : Λ) = 0)

include hl hΛ

theorem P1.isZero_R1_qt (M : EtSh Λ (Spec ((Spec (CommRingCat.of k[X])).residueField (GenBr.genPt k[X])))) :
    IsZero (R1 (gen k[X] ≫ chartA1 k) Λ (Qt Λ M)) := by
  have : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_of_ne k hl
  refine R2Gen.isZero_R1_qt_of_C1 (GenBr.genPt k[X]) (isC1_genField_polynomial k) l ?_
    (hζ.map_of_injective (genConst_injective k)) m hΛ (gen k[X] ≫ chartA1 k) M
  rw [← map_natCast (genConst k)]
  exact (_root_.map_ne_zero (genConst k)).2 hl

end H3

end RamanujanPetersson.EtCompact.CurveHn

end

end


