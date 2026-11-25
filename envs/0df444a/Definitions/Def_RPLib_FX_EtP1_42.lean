-- Prove2me | Definitions.Def_RPLib_FX_EtP1_42
-- name    : RPLib_FX_EtP1_42
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T10:45:22.303271+00:00
-- url     : https://prove2.me/theorems/b9ecb146-eaad-5dd4-a3eb-292ad118e468
-- title:
--   Étale cohomology of the projective line, library file 42 (an extra file from a re-cut)
-- statement:
--   File 42 (an extra file from a re-cut) of the étale cohomology library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtCompact_Cartan`: S4-EtCompact: Cartan's lemma (O8c (B), file C5b)
--   * `S4.Def_RP_EtCompact_Germ`: S4-EtCompact: germs at the points `geomPtAt x` (O8c (B), file C6a)
--   * `S4.Def_RP_EtCompact_SuppFin`: S4-EtCompact: supports of sections of sheaves supported on closed points (O8c (B), file C6b)
--   * `S4.Def_RP_EtCompact_CoInd`: S4-EtCompact, A1: co-induction from an open subgroup (group layer for `R²g_* = 0`)
--
--   **Formalization note.** One file of a library formalizing the étale cohomology of the projective line $\mathbf P^1_k = \operatorname{Proj} k[X_0, X_1]$ over an algebraically closed field $k$ with coefficients in sheaves of $\Lambda$-modules on the small étale site ($H^n = \operatorname{Ext}^n(\Lambda, -)$): $H^1(\mathbf P^1, \Lambda) = 0$, $H^2(\mathbf P^1, \Lambda) \cong \Lambda$ and $H^{n+3}(\mathbf P^1, F) = 0$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §1 (cohomology of curves) and Chapter III, §2 (Kummer theory); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Arcata », Chapter IV (cohomology of curves, Tsen's theorem)

import Mathlib
import Definitions.Def_RPLib_FX_EtP1_26

/-!
# Étale cohomology of the projective line, library file 42 (extra file from a re-cut)

Declarations of the formalization of the étale cohomology of the projective line over an algebraically
closed field (H¹ = 0, H² ≅ Λ, vanishing in degrees ≥ 3), re-hosted declaration by declaration from the
library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtCompact_Cartan`: S4-EtCompact: Cartan's lemma (O8c (B), file C5b)
* `S4.Def_RP_EtCompact_Germ`: S4-EtCompact: germs at the points `geomPtAt x` (O8c (B), file C6a)
* `S4.Def_RP_EtCompact_SuppFin`: S4-EtCompact: supports of sections of sheaves supported on closed points (O8c (B), file C6b)
* `S4.Def_RP_EtCompact_CoInd`: S4-EtCompact, A1: co-induction from an open subgroup (group layer for `R²g_* = 0`)
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtCompact_Cartan =====
section

/-!
# S4-EtCompact: Cartan's lemma (O8c (B), file C5b)

**`H_eq_zero_of_cechExact`**: on an affine scheme `Y`, an etale sheaf `F` that is Cech-exact on surjective arrows
between affine etale objects (`CechExact Λ F`) has `H^(n+1)(Y, F) = 0` for all `n`.

Proof: embed `F` into the injective, Cech-exact sheaf `god Λ F`; the quotient `Q` is Cech-exact (`cechExact_X₃`), global
sections of `god Λ F → Q` are surjective (`sections_surj`), so `H¹(F) = 0`, and `H^(n+2)(F) ≅ H^(n+1)(Q)`.
-/

set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry Opposite Abelian
open RamanujanPetersson.EtSheaves

noncomputable section

namespace RamanujanPetersson.EtCompact.Cech

universe u

variable {Λ : Type u} [CommRing Λ] {Y : Scheme.{u}}

/-- Lifting global sections along `g` from surjectivity on sections over the terminal object. -/
theorem lift_unit {T : Y.Etale} (hT : IsTerminal T) {X₂ X₃ : EtSh Λ Y} (g : X₂ ⟶ X₃)
    (hs : Function.Surjective (g.hom.app (op T)).hom) (b : unitSh Λ Y ⟶ X₃) :
    ∃ a : unitSh Λ Y ⟶ X₂, a ≫ g = b := by
  let adj := constantSheafAdj Y.smallEtaleTopology (ModuleCat.{u} Λ) hT
  obtain ⟨x, hx⟩ := hs ((adj.homEquiv _ _ b).hom 1)
  refine ⟨(adj.homEquiv _ _).symm (elt x), (adj.homEquiv _ _).injective ?_⟩
  rw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]
  refine ModuleCat.hom_ext (LinearMap.ext_ring ?_)
  rw [elt_comp, elt_one]
  exact hx

theorem cokSC_shortExact {C : Type*} [Category C] [Abelian C] {A B : C} (f : A ⟶ B) [Mono f] :
    (cokSC f).ShortExact where
  exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel f)

variable (Λ) in
/-- `0 → F → god F → god F / F → 0`. -/
abbrev godSC (F : EtSh Λ Y) : ShortComplex (EtSh Λ Y) := cokSC (godι Λ F)

theorem godSC_shortExact (F : EtSh Λ Y) : (godSC Λ F).ShortExact :=
  cokSC_shortExact (godι Λ F)

theorem cechExact_god (F : EtSh Λ Y) : CechExact Λ (god Λ F) :=
  fun _ _ f _ _ hf n => god_cech_exactAt' Λ F f hf n

/-- **Cartan's lemma**: a Cech-exact etale sheaf on an affine scheme has no higher cohomology. -/
theorem H_eq_zero_of_cechExact [IsAffine Y] (n : ℕ) :
    ∀ F : EtSh Λ Y, CechExact Λ F → ∀ e : H Λ F (n + 1), e = 0 := by
  have hT : IsTerminal (etId Y) := IsTerminal.ofUniqueHom
    (fun V => MorphismProperty.Over.homMk V.hom (Category.comp_id _))
    (fun V m => MorphismProperty.Over.Hom.ext ((Category.comp_id m.left).symm.trans (MorphismProperty.Over.w m)))
  have : IsAffine (etId Y).left := inferInstanceAs (IsAffine Y)
  induction n with
  | zero =>
    intro F hF e
    have hE := godSC_shortExact F
    obtain ⟨x₃, rfl⟩ := Ext.covariant_sequence_exact₁ _ hE e (Ext.eq_zero_of_injective _)
      (show 0 + 1 = 0 + 1 from rfl)
    obtain ⟨a, ha⟩ := lift_unit hT (godSC Λ F).g (sections_surj hE hF (etId Y)) (Ext.homEquiv₀ x₃)
    have hx : x₃ = (Ext.mk₀ a).comp (Ext.mk₀ (godSC Λ F).g) (zero_add 0) := by
      rw [Ext.mk₀_comp_mk₀, ha, Ext.mk₀_homEquiv₀_apply]
    rw [hx, Ext.comp_assoc_of_second_deg_zero, hE.comp_extClass, Ext.comp_zero]
  | succ n ih =>
    intro F hF e
    have hE := godSC_shortExact F
    obtain ⟨x₃, rfl⟩ := Ext.covariant_sequence_exact₁ _ hE e (Ext.eq_zero_of_injective _)
      (show n + 1 + 1 = n + 1 + 1 from rfl)
    rw [ih _ (cechExact_X₃ hE hF (cechExact_god F)) x₃, Ext.zero_comp]

end RamanujanPetersson.EtCompact.Cech

end

end

-- ===== S4.Def_RP_EtCompact_Germ =====
section

/-!
# S4-EtCompact: germs at the points `geomPtAt x` (O8c (B), file C6a)

* `etale_lqf`: etale morphisms are locally quasi-finite.
* `exists_fib_over`, `exists_lift_fib`: fibre points over a given point, lifts of fibre points along etale arrows.
* **`fiber_eq_of_pt`**: if `Gal x` is trivial, a fibre point of `geomPtAt x` is determined by its underlying point.
* `ux F x : F ⟶ x̄_* F_x̄` (the unit of the skyscraper adjunction), `ux_π_apply` (its components are the germs),
  `pi_ext`, `ux_eq_zero_iff`, `germ_map`.
* **`eq_zero_of_germs`**: a section all of whose germs vanish is zero.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open CategoryTheory Limits AlgebraicGeometry Opposite
open RamanujanPetersson.EtSheaves

noncomputable section

namespace RamanujanPetersson.EtCompact.Cech

universe u

section Fib

variable {X : Scheme.{u}}

variable (x : X)

/-- Two fibre points over the same point are conjugate under `Gal x`. -/
theorem exists_galAct_eq_of_pt {W : X.Etale} (a a' : (geomPtAt x).point.fiber.obj W)
    (h : fpt x a = fpt x a') :
    ∃ τ : Gal x, (galAct x τ).app W a = a' := by
  obtain ⟨⟨u, φ⟩, hp⟩ :=
    (Scheme.SpecToEquivOfField (geomPtAt x).Ω W.left).symm.surjective ((geomPtAt x).liftOf a).left
  obtain ⟨⟨u', φ'⟩, hp'⟩ :=
    (Scheme.SpecToEquivOfField (geomPtAt x).Ω W.left).symm.surjective ((geomPtAt x).liftOf a').left
  have hu : fpt x a = u := by
    refine (congrArg (fun f : Spec (CommRingCat.of (geomPtAt x).Ω) ⟶ W.left =>
      f (default : Spec (CommRingCat.of (geomPtAt x).Ω))) hp.symm).trans ?_
    change (Spec.map φ ≫ W.left.fromSpecResidueField u) default = u
    rw [Scheme.Hom.comp_apply]
    exact Scheme.fromSpecResidueField_apply u _
  have hu' : fpt x a' = u' := by
    refine (congrArg (fun f : Spec (CommRingCat.of (geomPtAt x).Ω) ⟶ W.left =>
      f (default : Spec (CommRingCat.of (geomPtAt x).Ω))) hp'.symm).trans ?_
    change (Spec.map φ' ≫ W.left.fromSpecResidueField u') default = u'
    rw [Scheme.Hom.comp_apply]
    exact Scheme.fromSpecResidueField_apply u' _
  obtain rfl : u = u' := hu.symm.trans (h.trans hu')
  have hpA : Spec.map φ ≫ W.left.fromSpecResidueField u = ((geomPtAt x).liftOf a).left := hp
  have hpB : Spec.map φ' ≫ W.left.fromSpecResidueField u = ((geomPtAt x).liftOf a').left := hp'
  have hwA : ((geomPtAt x).liftOf a).left ≫ W.hom = (geomPtAt x).pt := Over.w ((geomPtAt x).liftOf a)
  have hwB : ((geomPtAt x).liftOf a').left ≫ W.hom = (geomPtAt x).pt := Over.w ((geomPtAt x).liftOf a')
  have keyA : (Scheme.SpecToEquivOfField (geomPtAt x).Ω X).symm
      ⟨W.hom.base u, W.hom.residueFieldMap u ≫ φ⟩ = (geomPtAt x).pt := by
    change Spec.map (W.hom.residueFieldMap u ≫ φ) ≫ X.fromSpecResidueField (W.hom.base u) = _
    rw [Spec.map_comp, Category.assoc, Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
      ← Category.assoc]
    exact (congrArg (· ≫ W.hom) hpA).trans hwA
  have keyB : (Scheme.SpecToEquivOfField (geomPtAt x).Ω X).symm
      ⟨W.hom.base u, W.hom.residueFieldMap u ≫ φ'⟩ = (geomPtAt x).pt := by
    change Spec.map (W.hom.residueFieldMap u ≫ φ') ≫ X.fromSpecResidueField (W.hom.base u) = _
    rw [Spec.map_comp, Category.assoc, Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
      ← Category.assoc]
    exact (congrArg (· ≫ W.hom) hpB).trans hwB
  have hpt : (Scheme.SpecToEquivOfField (geomPtAt x).Ω X) (geomPtAt x).pt =
      ⟨x, CommRingCat.ofHom (algebraMap (X.residueField x) (SeparableClosure (X.residueField x)))⟩ :=
    (Scheme.SpecToEquivOfField (SeparableClosure (X.residueField x)) X).apply_symm_apply _
  have k2A : (⟨W.hom.base u, W.hom.residueFieldMap u ≫ φ⟩ :
      Σ y : X, X.residueField y ⟶ CommRingCat.of (geomPtAt x).Ω) =
      (Scheme.SpecToEquivOfField (geomPtAt x).Ω X) (geomPtAt x).pt := by
    rw [← keyA, Equiv.apply_symm_apply]
  have k2B : (⟨W.hom.base u, W.hom.residueFieldMap u ≫ φ'⟩ :
      Σ y : X, X.residueField y ⟶ CommRingCat.of (geomPtAt x).Ω) =
      (Scheme.SpecToEquivOfField (geomPtAt x).Ω X) (geomPtAt x).pt := by
    rw [← keyB, Equiv.apply_symm_apply]
  have k3A := k2A.trans hpt
  have k3B := k2B.trans hpt
  obtain ⟨e, -⟩ := Scheme.SpecToEquivOfField_eq_iff.1 k3A
  have e' : W.hom.base u = x := e
  subst e'
  have hA : W.hom.residueFieldMap u ≫ φ = CommRingCat.ofHom (algebraMap (X.residueField (W.hom.base u))
      (SeparableClosure (X.residueField (W.hom.base u)))) := eq_of_heq (Sigma.mk.inj_iff.mp k3A).2
  have hB : W.hom.residueFieldMap u ≫ φ' = CommRingCat.ofHom (algebraMap (X.residueField (W.hom.base u))
      (SeparableClosure (X.residueField (W.hom.base u)))) := eq_of_heq (Sigma.mk.inj_iff.mp k3B).2
  let _ : Algebra (X.residueField (W.hom.base u)) (W.left.residueField u) :=
    (W.hom.residueFieldMap u).hom.toAlgebra
  let f : W.left.residueField u →ₐ[X.residueField (W.hom.base u)]
      SeparableClosure (X.residueField (W.hom.base u)) :=
    { toRingHom := φ.hom
      commutes' := fun r => congrArg (fun g => g.hom r) hA }
  let f' : W.left.residueField u →ₐ[X.residueField (W.hom.base u)]
      SeparableClosure (X.residueField (W.hom.base u)) :=
    { toRingHom := φ'.hom
      commutes' := fun r => congrArg (fun g => g.hom r) hB }
  obtain ⟨τ, hτ⟩ := FibPt.exists_conj f f'
  refine ⟨τ, fiber_ext _ ?_⟩
  rw [galAct_left, ← hpA, ← hpB]
  have hc : φ ≫ CommRingCat.ofHom (τ : SeparableClosure (X.residueField (W.hom.base u)) →+*
      SeparableClosure (X.residueField (W.hom.base u))) = φ' := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro t
    exact hτ t
  have hS : galSpec (W.hom.base u) τ ≫ Spec.map φ = Spec.map φ' :=
    (Spec.map_comp φ _).symm.trans (congrArg Spec.map hc)
  exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ W.left.fromSpecResidueField u) hS)

/-- **If `Gal x` is trivial, a fibre point is determined by its underlying point.** -/
theorem fiber_eq_of_pt [Subsingleton (Gal x)] {W : X.Etale} (a a' : (geomPtAt x).point.fiber.obj W)
    (h : fpt x a = fpt x a') : a = a' := by
  obtain ⟨τ, hτ⟩ := exists_galAct_eq_of_pt x a a' h
  rw [← hτ, Subsingleton.elim τ 1, galAct_one]

end Fib

section Germ

variable {Λ : Type u} [CommRing Λ] {Y : Scheme.{u}} (F : EtSh Λ Y)

theorem ux_π (x : Y) (T : Y.Etale) (a : (geomPtAt x).point.fiber.obj T) :
    (ux F x).hom.app (op T) ≫ Pi.π (fun _ => Mx F x) a = (geomPtAt x).point.toPresheafFiber T a F.obj :=
  ((geomPtAt x).point.skyscraperPresheafHomEquiv_app_π _ T a).trans (Category.comp_id _)

theorem ux_π_apply (x : Y) {T : Y.Etale} (a : (geomPtAt x).point.fiber.obj T) (s : F.obj.obj (op T)) :
    (Pi.π (fun _ => Mx F x) a).hom (((ux F x).hom.app (op T)).hom s) =
      ((geomPtAt x).point.toPresheafFiber T a F.obj).hom s := by
  exact congrArg (fun g => g.hom s) (ux_π F x T a)

theorem ux_eq_zero_iff (x : Y) {T : Y.Etale} (s : F.obj.obj (op T)) :
    ((ux F x).hom.app (op T)).hom s = 0 ↔
      ∀ a : (geomPtAt x).point.fiber.obj T, ((geomPtAt x).point.toPresheafFiber T a F.obj).hom s = 0 := by
  constructor
  · intro h a
    exact (ux_π_apply F x a s).symm.trans ((congrArg (Pi.π (fun _ => Mx F x) a).hom h).trans (map_zero _))
  · intro h
    exact pi_ext _ _ fun a => (ux_π_apply F x a s).trans ((h a).trans (map_zero _).symm)

/-- A germ vanishes iff the section vanishes on a neighbourhood. -/
theorem exists_nbhd_of_germ_eq_zero {T : Y.Etale} (x : Y) (a : (geomPtAt x).point.fiber.obj T)
    (s : F.obj.obj (op T)) (h : ((geomPtAt x).point.toPresheafFiber T a F.obj).hom s = 0) :
    ∃ (V : Y.Etale) (g : V ⟶ T) (b : (geomPtAt x).point.fiber.obj V),
      (geomPtAt x).point.fiber.map g b = a ∧ (F.obj.map g.op).hom s = 0 := by
  have h' : ((geomPtAt x).point.toPresheafFiber T a F.obj).hom s =
      ((geomPtAt x).point.toPresheafFiber T a F.obj).hom 0 := h.trans (map_zero _).symm
  obtain ⟨V, g, b, hb, hs⟩ := ((geomPtAt x).point.toPresheafFiber_eq_iff' T a s 0).1 h'
  refine ⟨V, g, b, hb, ?_⟩
  have hs' : (F.obj.map g.op).hom s = (F.obj.map g.op).hom 0 := hs
  rw [hs', map_zero]

/-- **A section all of whose germs vanish is zero.** -/
theorem eq_zero_of_germs {T : Y.Etale} (s : F.obj.obj (op T))
    (h : ∀ (x : Y) (a : (geomPtAt x).point.fiber.obj T),
      ((geomPtAt x).point.toPresheafFiber T a F.obj).hom s = 0) : s = 0 := by
  choose V g b hb hs using fun p : Σ x : Y, (geomPtAt x).point.fiber.obj T =>
    exists_nbhd_of_germ_eq_zero F p.1 p.2 s (h p.1 p.2)
  refine sep_of_cover F g ?_ s 0 fun p => (hs p).trans (map_zero _).symm
  rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
  refine Set.eq_univ_of_forall fun t => Set.mem_iUnion.2 ?_
  obtain ⟨a, ha⟩ := exists_fib_over T t
  refine ⟨⟨_, a⟩, fpt (T.hom t) (b ⟨_, a⟩), ?_⟩
  have e := congrArg (fun c => fpt (T.hom t) c) (hb ⟨_, a⟩)
  exact (fib_left_map _ _ _).symm.trans (e.trans ha)

/-- Sections with the same germs are equal. -/
theorem eq_of_germs {T : Y.Etale} (s s' : F.obj.obj (op T))
    (h : ∀ (x : Y) (a : (geomPtAt x).point.fiber.obj T),
      ((geomPtAt x).point.toPresheafFiber T a F.obj).hom s =
        ((geomPtAt x).point.toPresheafFiber T a F.obj).hom s') : s = s' := by
  refine sub_eq_zero.1 (eq_zero_of_germs F _ fun x a => ?_)
  rw [map_sub, h x a, sub_self]

/-- Sections whose images under all units agree are equal. -/
theorem eq_of_ux {T : Y.Etale} (s s' : F.obj.obj (op T))
    (h : ∀ x : Y, ((ux F x).hom.app (op T)).hom s = ((ux F x).hom.app (op T)).hom s') : s = s' := by
  refine eq_of_germs F s s' fun x a => ?_
  exact (ux_π_apply F x a s).symm.trans
    ((congrArg (Pi.π (fun _ => Mx F x) a).hom (h x)).trans (ux_π_apply F x a s'))

end Germ

end RamanujanPetersson.EtCompact.Cech

end

end

-- ===== S4.Def_RP_EtCompact_SuppFin =====
section

/-!
# S4-EtCompact: supports of sections of sheaves supported on closed points (O8c (B), file C6b)

* `isClosed_pt`: a point of an etale object over a closed point is closed; `finite_preimage_closed`: on a
  quasi-compact etale object only finitely many points lie over a closed point; `finite_fib` (trivial `Gal x`).
* `supp F s`: the points carrying a fibre point at which the germ of `s` is nonzero; `isClosed_supp`;
  `germ_eq_zero_of_not_mem_supp`.
* **`finite_supp`**: if the stalks of `F` vanish at non-closed points and `Y` is locally noetherian, every section
  over an affine etale object has finite support (`finite_of_isClosed_pts`: a closed set of closed points in a
  noetherian quasi-sober space is finite).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace
open RamanujanPetersson.EtSheaves

noncomputable section

namespace RamanujanPetersson.EtCompact.Cech

universe u

section Top

variable {X : Scheme.{u}}

/-- A point of an etale object over a closed point is closed. -/
theorem isClosed_pt {T : X.Etale} (t : T.left) (ht : IsClosed ({T.hom t} : Set X)) :
    IsClosed ({t} : Set T.left) := by
  have hC : IsClosed (T.hom ⁻¹' {T.hom t}) := ht.preimage T.hom.continuous
  have hD := (isDiscrete_iff_forall_mem_exists_isOpen.1 (T.hom.isDiscrete_preimage_singleton (T.hom t)))
  rw [← closure_subset_iff_isClosed]
  intro t' ht'
  have h1 : t' ∈ T.hom ⁻¹' {T.hom t} :=
    closure_minimal (Set.singleton_subset_iff.2 (show t ∈ T.hom ⁻¹' {T.hom t} from rfl)) hC ht'
  obtain ⟨U, hU, hUt⟩ := hD t' h1
  have ht'U : t' ∈ U := (hUt.symm ▸ Set.mem_singleton t' : t' ∈ U ∩ T.hom ⁻¹' {T.hom t}).1
  obtain ⟨t'', ⟨hU'', rfl⟩⟩ := mem_closure_iff.1 ht' U hU ht'U
  have : t'' ∈ U ∩ T.hom ⁻¹' {T.hom t''} := ⟨hU'', rfl⟩
  rw [hUt] at this
  exact this.symm

/-- With trivial `Gal x`, the fibre of `x̄` over a quasi-compact etale object is finite. -/
theorem finite_fib (x : X) [Subsingleton (Gal x)] (T : X.Etale) [CompactSpace T.left]
    (hx : IsClosed ({x} : Set X)) : Finite ((geomPtAt x).point.fiber.obj T) := by
  have hf := (finite_preimage_closed T x hx).to_subtype
  refine Finite.of_injective (fun a => (⟨fpt x a, fib_over x a⟩ : T.hom ⁻¹' {x})) fun a a' h => ?_
  exact fiber_eq_of_pt x a a' (congrArg Subtype.val h)

/-- A closed set of closed points in a noetherian quasi-sober space is finite. -/
theorem finite_of_isClosed_pts {Z : Type*} [TopologicalSpace Z] [NoetherianSpace Z] [QuasiSober Z] {S : Set Z}
    (hS : IsClosed S) (hpts : ∀ z ∈ S, IsClosed ({z} : Set Z)) : S.Finite := by
  obtain ⟨S', hfin, hcl, hirr, rfl⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hS
  refine Set.Finite.sUnion hfin fun t ht => ?_
  have hg := (hirr t ht).isGenericPoint_genericPoint_closure
  rw [(hcl t ht).closure_eq] at hg
  have hgs : (hirr t ht).genericPoint ∈ ⋃₀ S' := ⟨t, ht, hg.mem⟩
  rw [← hg.def, (hpts _ hgs).closure_eq]
  exact Set.finite_singleton _

end Top

section Supp

variable {Λ : Type u} [CommRing Λ] {Y : Scheme.{u}} (F : EtSh Λ Y)

theorem germ_eq_zero_of_not_mem_supp {T : Y.Etale} (s : F.obj.obj (op T)) (y : Y)
    (a : (geomPtAt y).point.fiber.obj T) (h : fpt y a ∉ supp F s) :
    ((geomPtAt y).point.toPresheafFiber T a F.obj).hom s = 0 := by
  by_contra hne
  exact h ⟨y, a, rfl, hne⟩

theorem isClosed_supp {T : Y.Etale} (s : F.obj.obj (op T)) : IsClosed (supp F s) := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro t ht
  obtain ⟨a, ha⟩ := exists_fib_over T t
  have h0 := germ_eq_zero_of_not_mem_supp F s _ a (by rw [ha]; exact ht)
  obtain ⟨V, g, b, hb, hs⟩ := exists_nbhd_of_germ_eq_zero F _ a s h0
  refine ⟨Set.range g.left, ?_, g.left.isOpenMap.isOpen_range, ⟨fpt _ b, ?_⟩⟩
  · rintro _ ⟨v, rfl⟩ ⟨y, a', ha', hne⟩
    obtain ⟨b', hb', -⟩ := exists_lift_fib g y a' v ha'.symm
    apply hne
    rw [← hb', ← germ_map, hs, map_zero]
  · exact (fib_left_map g _ b).symm.trans ((congrArg (fpt _) hb).trans ha)

/-- Points of the support lie over closed points when the stalks vanish at non-closed points. -/
theorem isClosed_of_mem_supp (hF : ∀ y : Y, ¬ IsClosed ({y} : Set Y) → IsZero (Mx F y)) {T : Y.Etale}
    (s : F.obj.obj (op T)) {t : T.left} (ht : t ∈ supp F s) : IsClosed ({T.hom t} : Set Y) := by
  obtain ⟨y, a, rfl, hne⟩ := ht
  rw [fib_over]
  by_contra h
  apply hne
  have := congrArg (fun φ => φ.hom s)
    ((hF y h).eq_of_tgt ((geomPtAt y).point.toPresheafFiber T a F.obj) 0)
  exact this

/-- **Finite support** over affine etale objects. -/
theorem finite_supp [IsLocallyNoetherian Y] (hF : ∀ y : Y, ¬ IsClosed ({y} : Set Y) → IsZero (Mx F y))
    {T : Y.Etale} [IsAffine T.left] (s : F.obj.obj (op T)) : (supp F s).Finite := by
  have : IsLocallyNoetherian ((Functor.fromPUnit Y).obj T.right) := ‹IsLocallyNoetherian Y›
  have : IsLocallyNoetherian T.left := LocallyOfFiniteType.isLocallyNoetherian T.hom
  have : IsNoetherian T.left := (isNoetherian_iff _).2 ⟨inferInstance, inferInstance⟩
  exact finite_of_isClosed_pts (isClosed_supp F s) fun t ht => isClosed_pt t (isClosed_of_mem_supp F hF s ht)

end Supp

end RamanujanPetersson.EtCompact.Cech

end

end

-- ===== S4.Def_RP_EtCompact_CoInd =====
section

/-!
# S4-EtCompact, A1: co-induction from an open subgroup (group layer for `R²g_* = 0`)

`H ≤ G` a subgroup, `σ` a representation of `H` on `X`.

* `CoInd.sub H σ = {f : G → X | f (h g) = σ h (f g)}` with `G` acting by right translation (`CoInd.rep`);
* `CoInd.unit : X → CoInd` (`H`-equivariant, `unit_equivariant`); `CoInd.map` (functorial, `map_injective`,
  `map_unit`);
* `CoInd.counit : CoInd(Res ρ) → M` for a `G`-representation `ρ` and finitely many cosets (`counit_rep`:
  `G`-equivariant; `counit_unit`: `counit ∘ unit = id`);
* `CoInd.rep_isDiscrete`: co-induction from an open subgroup of finite index preserves discreteness;
  `IsDiscreteRep.comp_subtype`: restriction to a subgroup preserves it.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace RamanujanPetersson.EtCompact.CoInd

attribute [local instance] Classical.propDecidable

variable {Λ : Type*} [CommRing Λ] {G : Type*} [Group G] (H : Subgroup G)

section Def

variable {X : Type*} [AddCommGroup X] [Module Λ X] (σ : Representation Λ H X)

/-- The co-induced module `{f : G → X | f (h g) = σ h (f g)}`. -/
def sub : Submodule Λ (G → X) where
  carrier := {f | ∀ (h : H) (g : G), f (h * g) = σ h (f g)}
  add_mem' := by
    intro f f' hf hf' h g
    simp only [Pi.add_apply]
    rw [hf h g, hf' h g, map_add]
  zero_mem' := by
    intro h g
    simp
  smul_mem' := by
    intro c f hf h g
    simp only [Pi.smul_apply]
    rw [hf h g, map_smul]

theorem mem_sub {f : G → X} : f ∈ sub H σ ↔ ∀ (h : H) (g : G), f (h * g) = σ h (f g) := Iff.rfl

theorem sub_apply (f : sub H σ) (h : H) (g : G) : (f : G → X) (h * g) = σ h ((f : G → X) g) :=
  (mem_sub H σ).1 f.2 h g

/-- Right translation `(τ f) g = f (g τ)`. -/
def act (τ : G) : sub H σ →ₗ[Λ] sub H σ where
  toFun f := ⟨fun g => (f : G → X) (g * τ), (mem_sub H σ).2 fun h g => by
    show (f : G → X) (h * g * τ) = σ h ((f : G → X) (g * τ))
    rw [mul_assoc]
    exact sub_apply H σ f h (g * τ)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- **The co-induced representation** `CoInd_H^G σ`. -/
def rep : Representation Λ G (sub H σ) where
  toFun := act H σ
  map_one' := LinearMap.ext fun f => Subtype.ext (funext fun g => by
    show (f : G → X) (g * 1) = (f : G → X) g
    rw [mul_one])
  map_mul' τ τ' := LinearMap.ext fun f => Subtype.ext (funext fun g => by
    show (f : G → X) (g * (τ * τ')) = (f : G → X) (g * τ * τ')
    rw [mul_assoc])

theorem rep_apply (τ : G) (f : sub H σ) (g : G) :
    ((rep H σ τ f : sub H σ) : G → X) g = (f : G → X) (g * τ) := rfl

theorem unitFun_mem (x : X) : unitFun H σ x ∈ sub H σ := (mem_sub H σ).2 fun h g => by
  by_cases hg : g ∈ H
  · have hhg : (h : G) * g ∈ H := H.mul_mem h.2 hg
    rw [unitFun, unitFun, dif_pos hhg, dif_pos hg]
    show σ (h * ⟨g, hg⟩) x = σ h (σ ⟨g, hg⟩ x)
    rw [map_mul, Module.End.mul_apply]
  · have hhg : (h : G) * g ∉ H := fun h' => hg (by simpa using H.mul_mem (H.inv_mem h.2) h')
    rw [unitFun, unitFun, dif_neg hhg, dif_neg hg, map_zero]

/-- The `H`-equivariant unit `X → CoInd_H^G X`. -/
def unit : X →ₗ[Λ] sub H σ where
  toFun x := ⟨unitFun H σ x, unitFun_mem H σ x⟩
  map_add' x y := Subtype.ext (funext fun g => by
    show unitFun H σ (x + y) g = unitFun H σ x g + unitFun H σ y g
    unfold unitFun
    split_ifs <;> simp)
  map_smul' c x := Subtype.ext (funext fun g => by
    show unitFun H σ (c • x) g = c • unitFun H σ x g
    unfold unitFun
    split_ifs <;> simp)

theorem unit_apply (x : X) (g : G) : ((unit H σ x : sub H σ) : G → X) g = unitFun H σ x g := rfl

theorem unit_apply_not_mem (x : X) {g : G} (hg : g ∉ H) : ((unit H σ x : sub H σ) : G → X) g = 0 :=
  dif_neg hg

theorem unit_equivariant (τ : H) (x : X) : unit H σ (σ τ x) = rep H σ (τ : G) (unit H σ x) :=
  Subtype.ext (funext fun g => by
    show unitFun H σ (σ τ x) g = unitFun H σ x (g * τ)
    by_cases hg : g ∈ H
    · have hgt : g * τ ∈ H := H.mul_mem hg τ.2
      rw [unitFun, unitFun, dif_pos hg, dif_pos hgt]
      show σ ⟨g, hg⟩ (σ τ x) = σ (⟨g, hg⟩ * τ) x
      rw [map_mul, Module.End.mul_apply]
    · have hgt : g * τ ∉ H := fun h' => hg (by simpa using H.mul_mem h' (H.inv_mem τ.2))
      rw [unitFun, unitFun, dif_neg hg, dif_neg hgt])

variable {Y : Type*} [AddCommGroup Y] [Module Λ Y] {σ} {σY : Representation Λ H Y}

/-- Functoriality of co-induction. -/
def map (φ : X →ₗ[Λ] Y) (hφ : ∀ h : H, φ ∘ₗ σ h = σY h ∘ₗ φ) : sub H σ →ₗ[Λ] sub H σY where
  toFun f := ⟨fun g => φ ((f : G → X) g), (mem_sub H σY).2 fun h g => by
    rw [sub_apply H σ f h g]
    exact LinearMap.congr_fun (hφ h) _⟩
  map_add' _ _ := Subtype.ext (funext fun _ => map_add φ _ _)
  map_smul' _ _ := Subtype.ext (funext fun _ => map_smul φ _ _)

variable (φ : X →ₗ[Λ] Y) (hφ : ∀ h : H, φ ∘ₗ σ h = σY h ∘ₗ φ)

theorem map_injective (hinj : Function.Injective φ) : Function.Injective (map H φ hφ) := fun _ _ e =>
  Subtype.ext (funext fun g => hinj (congrArg (fun F : sub H σY => (F : G → Y) g) e))

theorem map_rep (τ : G) (f : sub H σ) : map H φ hφ (rep H σ τ f) = rep H σY τ (map H φ hφ f) := rfl

theorem map_unit (x : X) : map H φ hφ (unit H σ x) = unit H σY (φ x) := Subtype.ext (funext fun g => by
  show φ (unitFun H σ x g) = unitFun H σY (φ x) g
  unfold unitFun
  split_ifs with hg
  · exact LinearMap.congr_fun (hφ ⟨g, hg⟩) x
  · exact map_zero φ)

end Def

section Counit

variable {M : Type*} [AddCommGroup M] [Module Λ M] (ρ : Representation Λ G M)

theorem inv_apply_mul (f : sub H (ρ.comp H.subtype)) (h : H) (g : G) :
    ρ (h * g)⁻¹ ((f : G → M) (h * g)) = ρ g⁻¹ ((f : G → M) g) := by
  rw [sub_apply]
  show ρ ((h : G) * g)⁻¹ (ρ (h : G) ((f : G → M) g)) = _
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_rev, inv_mul_cancel_right]

variable [Fintype (RC H)]

end Counit

section Disc

variable [TopologicalSpace G] [IsTopologicalGroup G]
variable {X : Type*} [AddCommGroup X] [Module Λ X]

end Disc

end RamanujanPetersson.EtCompact.CoInd

end

end


