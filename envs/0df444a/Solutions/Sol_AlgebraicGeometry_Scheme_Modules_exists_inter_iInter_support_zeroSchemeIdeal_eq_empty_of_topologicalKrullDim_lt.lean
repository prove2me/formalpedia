-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.exists_inter_iInter_support_zeroSchemeIdeal_eq_empty_of_topologicalKrullDim_lt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/958d4f55-0868-59f9-b144-b0b9c4e5c198

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_inter_iInter_support_zeroSchemeIdeal_eq_empty_of_topologicalKrullDim_lt

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry TopologicalSpace Opposite"

namespace P2mAvoidTop

open Set Order Topology

variable {V : Type*} [TopologicalSpace V]

theorem eq_empty_of_topologicalKrullDim_lt_zero {B : Set V}
    (h : topologicalKrullDim B < (0 : ℕ)) : B = ∅ := by
  by_contra hne
  obtain ⟨b, hb⟩ := nonempty_iff_ne_empty.mpr hne
  have : Nonempty (IrreducibleCloseds B) :=
    ⟨⟨closure {⟨b, hb⟩}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
  have h0 : (0 : WithBot ℕ∞) ≤ topologicalKrullDim B := krullDim_nonneg
  exact (lt_irrefl _) (h0.trans_lt (by simpa using h))

def liftIC {B : Set V} (t : Set V) (htB : t ⊆ B) (ht : IsIrreducible t) (htc : IsClosed t) :
    IrreducibleCloseds B where
  carrier := Subtype.val ⁻¹' t
  isIrreducible' := by
    have : (Subtype.val ⁻¹' t : Set B) = range (inclusion htB) := by
      rw [range_inclusion]; rfl
    rw [this, ← image_univ]
    haveI := Subtype.irreducibleSpace ht
    exact (IrreducibleSpace.isIrreducible_univ t).image _ (continuous_inclusion htB).continuousOn
  isClosed' := htc.preimage continuous_subtype_val

theorem topologicalKrullDim_inter_lt {B Z : Set V} (S : Finset (Set V))
    (hSc : ∀ t ∈ S, IsClosed t) (hSi : ∀ t ∈ S, IsIrreducible t) (hSB : B = ⋃₀ (S : Set (Set V)))
    (hZ : IsClosed Z) (havoid : ∀ t ∈ S, ¬ t ⊆ Z) (n : ℕ)
    (hdim : topologicalKrullDim B < (n + 1 : ℕ)) :
    topologicalKrullDim ↥(B ∩ Z) < n := by
  unfold topologicalKrullDim at hdim ⊢
  rw [Order.krullDim_lt_coe_iff]
  intro l
  have hsub : B ∩ Z ⊆ B := inter_subset_left

  let f : IrreducibleCloseds ↥(B ∩ Z) → IrreducibleCloseds B :=
    IrreducibleCloseds.map (inclusion hsub) (continuous_inclusion hsub)
  have hf : StrictMono f :=
    IrreducibleCloseds.map_strictMono_of_isInducing (IsEmbedding.inclusion hsub).isInducing
  let l' : LTSeries (IrreducibleCloseds B) := l.map f hf

  set c := l.last
  have hA : IsIrreducible (Subtype.val '' (c : Set ↥(B ∩ Z))) :=
    c.isIrreducible.image _ continuous_subtype_val.continuousOn
  have hAB : Subtype.val '' (c : Set ↥(B ∩ Z)) ⊆ B ∩ Z := Subtype.coe_image_subset _ _
  obtain ⟨t, htS, hAt⟩ : ∃ t ∈ S, Subtype.val '' (c : Set ↥(B ∩ Z)) ⊆ t :=
    isIrreducible_iff_sUnion_isClosed.mp hA S hSc (hSB ▸ hAB.trans inter_subset_left)
  have htB : t ⊆ B := hSB ▸ subset_sUnion_of_mem htS
  let T : IrreducibleCloseds B := liftIC t htB (hSi t htS) (hSc t htS)
  have hle : (f c : Set B) ⊆ (T : Set B) := by
    change closure (inclusion hsub '' (c : Set ↥(B ∩ Z))) ⊆ Subtype.val ⁻¹' t
    refine closure_minimal ?_ ((hSc t htS).preimage continuous_subtype_val)
    rintro _ ⟨y, hy, rfl⟩
    exact hAt ⟨y, hy, rfl⟩
  have hlast : l'.last < T := by
    rw [LTSeries.last_map]
    refine lt_of_le_of_ne hle fun heq => havoid t htS ?_

    have hcl : (f c : Set B) ⊆ Subtype.val ⁻¹' Z := by
      change closure (inclusion hsub '' (c : Set ↥(B ∩ Z))) ⊆ Subtype.val ⁻¹' Z
      refine closure_minimal ?_ (hZ.preimage continuous_subtype_val)
      rintro _ ⟨y, _, rfl⟩
      exact y.2.2
    intro v hv
    have hvT : (⟨v, htB hv⟩ : B) ∈ (T : Set B) := hv
    rw [← heq] at hvT
    exact hcl hvT
  have hlen := LTSeries.length_le_krullDim (l'.snoc T hlast)
  simp only [RelSeries.snoc_length, LTSeries.map_length, l'] at hlen
  have h := hlen.trans_lt hdim
  have h' : l.length + 1 < n + 1 := by exact_mod_cast h
  omega

end P2mAvoidTop

namespace P2mAvoid

p2m_open "AlgebraicGeometry.Scheme.Modules"

section scalars

variable (X : Scheme.{u})

noncomputable def unitSec (r : Γ(X, ⊤)) : (𝟙_ X.Modules).val.sections :=
  PresheafOfModules.sectionsMk (M := (𝟙_ X.Modules).val)
    (fun W => toUnitSection W.unop (X.presheaf.map (homOfLE le_top).op r))
    (by
      intro W W' f
      change toUnitSection W'.unop (X.presheaf.map f (X.presheaf.map (homOfLE le_top).op r)) = _
      rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp]
      rfl)

@[scoped simp] theorem unitSec_val (r : Γ(X, ⊤)) (W : (X.Opens)ᵒᵖ) :
    (unitSec X r).val W = toUnitSection W.unop (X.presheaf.map (homOfLE le_top).op r) := rfl

noncomputable def unitEnd (r : Γ(X, ⊤)) : 𝟙_ X.Modules ⟶ 𝟙_ X.Modules :=
  (SheafOfModules.unitHomEquiv (𝟙_ X.Modules)).symm (unitSec X r)

theorem unitHomEquiv_unitEnd (r : Γ(X, ⊤)) :
    SheafOfModules.unitHomEquiv (𝟙_ X.Modules) (unitEnd X r) = unitSec X r :=
  Equiv.apply_symm_apply _ _

theorem unitEnd_app_one (r : Γ(X, ⊤)) (W : X.Opens) :
    (unitEnd X r).app W (toUnitSection W 1) =
      toUnitSection W (X.presheaf.map (homOfLE le_top).op r) := by
  have h := congrArg (fun σ => σ.val (op W)) (unitHomEquiv_unitEnd X r)
  simp at h
  exact h

theorem unitEnd_app (r : Γ(X, ⊤)) (W : X.Opens) (m : Γ(𝟙_ X.Modules, W)) :
    (unitEnd X r).app W m =
      toUnitSection W (ofUnitSection W m * X.presheaf.map (homOfLE le_top).op r) := by
  have : m = ofUnitSection W m • toUnitSection W 1 := by
    apply ofUnitSection_injective; rw [ofUnitSection_smul]; simp
  conv_lhs => rw [this, Scheme.Modules.Hom.app_smul, unitEnd_app_one]
  apply ofUnitSection_injective
  rw [ofUnitSection_smul]
  simp

theorem unitEnd_add (r r' : Γ(X, ⊤)) : unitEnd X (r + r') = unitEnd X r + unitEnd X r' := by
  apply Scheme.Modules.hom_ext
  intro W
  ext m
  change (unitEnd X (r + r')).app W m = (unitEnd X r).app W m + (unitEnd X r').app W m
  rw [unitEnd_app, unitEnd_app, unitEnd_app]
  apply ofUnitSection_injective
  change _ = ofUnitSection W _ + ofUnitSection W _
  simp only [ofUnitSection_toUnitSection, map_add, mul_add]
  rfl

theorem unitEnd_mul (r r' : Γ(X, ⊤)) : unitEnd X (r * r') = unitEnd X r ≫ unitEnd X r' := by
  apply Scheme.Modules.hom_ext
  intro W
  ext m
  change (unitEnd X (r * r')).app W m = (unitEnd X r').app W ((unitEnd X r).app W m)
  rw [unitEnd_app, unitEnd_app, unitEnd_app]
  simp only [ofUnitSection_toUnitSection, map_mul, mul_assoc]

theorem unitEnd_one : unitEnd X 1 = 𝟙 _ := by
  apply Scheme.Modules.hom_ext
  intro W
  ext m
  change (unitEnd X 1).app W m = m
  rw [unitEnd_app]
  simp only [map_one, mul_one, toUnitSection_ofUnitSection]

theorem unitEnd_zero : unitEnd X 0 = 0 := by
  have h := unitEnd_add X 0 0
  simp only [add_zero] at h
  exact left_eq_add.mp h

noncomputable def scalar {k : Type u} [Field k] (π : X ⟶ Spec (.of k)) (a : k) :
    𝟙_ X.Modules ⟶ 𝟙_ X.Modules :=
  unitEnd X (π.appTop ((Scheme.ΓSpecIso (.of k)).inv a))

variable {k : Type u} [Field k] (π : X ⟶ Spec (.of k))

theorem scalar_add (a b : k) : scalar X π (a + b) = scalar X π a + scalar X π b := by
  simp only [scalar, map_add, unitEnd_add]

theorem scalar_mul (a b : k) : scalar X π (a * b) = scalar X π a ≫ scalar X π b := by
  simp only [scalar, map_mul, unitEnd_mul]

theorem scalar_one : scalar X π 1 = 𝟙 _ := by
  simp only [scalar, map_one, unitEnd_one]

theorem scalar_zero : scalar X π 0 = 0 := by
  simp only [scalar, map_zero, unitEnd_zero]

end scalars

section zeroScheme

variable {X : Scheme.{u}} {M : X.Modules}

theorem restrictSection_zero (U : X.Opens) :
    restrictSection (0 : 𝟙_ X.Modules ⟶ M) U = 0 := rfl

theorem restrictSection_add (s t : 𝟙_ X.Modules ⟶ M) (U : X.Opens) :
    restrictSection (s + t) U = restrictSection s U + restrictSection t U := rfl

theorem coeff_zero (U : X.Opens) (φ : M.restrict U.ι ⟶ 𝟙_ (U : Scheme.{u}).Modules) :
    coeff (0 : 𝟙_ X.Modules ⟶ M) U φ = 0 := by
  unfold coeff
  rw [restrictSection_zero, map_zero]
  exact map_zero _

theorem coeff_add (s t : 𝟙_ X.Modules ⟶ M) (U : X.Opens)
    (φ : M.restrict U.ι ⟶ 𝟙_ (U : Scheme.{u}).Modules) :
    coeff (s + t) U φ = coeff s U φ + coeff t U φ := by
  unfold coeff
  rw [restrictSection_add, map_add]
  exact map_add _ _ _

theorem coeff_unitEnd_comp (e : 𝟙_ X.Modules ⟶ 𝟙_ X.Modules) (s : 𝟙_ X.Modules ⟶ M) (U : X.Opens)
    (φ : M.restrict U.ι ⟶ 𝟙_ (U : Scheme.{u}).Modules) :
    ∃ r : Γ(X, U), coeff (e ≫ s) U φ = r * coeff s U φ := by
  set W := U.ι ''ᵁ ⊤
  set ρ : Γ(X, W) := ofUnitSection W (e.app W (toUnitSection W 1))
  refine ⟨U.topIso.hom ((U.ι.appIso ⊤).hom ρ), ?_⟩
  have h1 : restrictSection (e ≫ s) U = ((U.ι.appIso ⊤).hom ρ) • restrictSection s U := by
    unfold restrictSection
    rw [Scheme.Modules.Hom.comp_app]
    change s.app W (e.app W (toUnitSection W 1)) =
      (U.ι.appIso ⊤).inv ((U.ι.appIso ⊤).hom ρ) • s.app W (toUnitSection W 1)
    rw [Iso.hom_inv_id_apply, ← Scheme.Modules.Hom.app_smul]
    congr 1
    apply ofUnitSection_injective
    rw [ofUnitSection_smul]
    simp [ρ]
  unfold coeff
  rw [h1, Scheme.Modules.Hom.app_smul, ofUnitSection_smul, map_mul]

theorem zeroSchemeIdeal_zero : zeroSchemeIdeal (0 : 𝟙_ X.Modules ⟶ M) = ⊥ := by
  refine le_bot_iff.mp (zeroSchemeIdeal_le fun U => ?_)
  refine Ideal.span_le.mpr ?_
  rintro _ ⟨φ, rfl⟩
  simp [coeff_zero]

theorem mem_support_zeroSchemeIdeal_zero (x : X) :
    x ∈ (zeroSchemeIdeal (0 : 𝟙_ X.Modules ⟶ M)).support := by
  rw [zeroSchemeIdeal_zero, Scheme.IdealSheafData.support_bot]
  trivial

theorem zeroSchemeIdeal_unitEnd_comp_le (e : 𝟙_ X.Modules ⟶ 𝟙_ X.Modules)
    (s : 𝟙_ X.Modules ⟶ M) : zeroSchemeIdeal (e ≫ s) ≤ zeroSchemeIdeal s := by
  refine le_zeroSchemeIdeal fun J hJ => zeroSchemeIdeal_le fun U => ?_
  refine Ideal.span_le.mpr ?_
  rintro _ ⟨φ, rfl⟩
  obtain ⟨r, hr⟩ := coeff_unitEnd_comp e s U.1 φ
  rw [SetLike.mem_coe, hr]
  exact Ideal.mul_mem_left _ _ (hJ U (coeff_mem_coeffIdeal s U.1 φ))

theorem support_le_support_unitEnd_comp (e : 𝟙_ X.Modules ⟶ 𝟙_ X.Modules)
    (s : 𝟙_ X.Modules ⟶ M) :
    (zeroSchemeIdeal s).support ≤ (zeroSchemeIdeal (e ≫ s)).support :=
  Scheme.IdealSheafData.support_antitone (zeroSchemeIdeal_unitEnd_comp_le e s)

theorem zeroSchemeIdeal_add_le (hM : Scheme.Modules.IsInvertible M) (s t : 𝟙_ X.Modules ⟶ M) :
    zeroSchemeIdeal (s + t) ≤ zeroSchemeIdeal s ⊔ zeroSchemeIdeal t := by
  refine zeroSchemeIdeal_le fun U => ?_
  refine Ideal.span_le.mpr ?_
  rintro _ ⟨φ, rfl⟩
  rw [SetLike.mem_coe, coeff_add, Scheme.IdealSheafData.ideal_sup]
  exact Submodule.add_mem_sup
    ((AlgebraicGeometry.Scheme.Modules.IsInvertible.coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq
      hM s).1 U (coeff_mem_coeffIdeal s U.1 φ))
    ((AlgebraicGeometry.Scheme.Modules.IsInvertible.coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq
      hM t).1 U (coeff_mem_coeffIdeal t U.1 φ))

theorem support_inf_le_support_add (hM : Scheme.Modules.IsInvertible M)
    (s t : 𝟙_ X.Modules ⟶ M) :
    (zeroSchemeIdeal s).support ⊓ (zeroSchemeIdeal t).support ≤
      (zeroSchemeIdeal (s + t)).support := by
  rw [← Scheme.IdealSheafData.support_sup]
  exact Scheme.IdealSheafData.support_antitone (zeroSchemeIdeal_add_le hM s t)

end zeroScheme

section avoidance

variable {X : Scheme.{u}} {k : Type u} [Field k] (π : X ⟶ Spec (.of k)) {M : X.Modules}
variable {ι : Type*} [Fintype ι] (σ : ι → (𝟙_ X.Modules ⟶ M))

noncomputable def comb (c : ι → k) : 𝟙_ X.Modules ⟶ M :=
  ∑ i, scalar X π (c i) ≫ σ i

theorem comb_zero : comb π σ 0 = 0 := by
  show (∑ i, scalar X π ((0 : ι → k) i) ≫ σ i) = 0
  simp_rw [Pi.zero_apply, scalar_zero]
  exact Finset.sum_eq_zero fun i _ => Limits.zero_comp

theorem comb_add (c d : ι → k) : comb π σ (c + d) = comb π σ c + comb π σ d := by
  show (∑ i, scalar X π ((c + d) i) ≫ σ i) =
    (∑ i, scalar X π (c i) ≫ σ i) + ∑ i, scalar X π (d i) ≫ σ i
  simp_rw [Pi.add_apply, scalar_add]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => Preadditive.add_comp _ _ _ _ _ _

theorem comb_smul (a : k) (c : ι → k) : comb π σ (a • c) = scalar X π a ≫ comb π σ c := by
  show (∑ i, scalar X π ((a • c) i) ≫ σ i) = scalar X π a ≫ ∑ i, scalar X π (c i) ≫ σ i
  simp_rw [Pi.smul_apply, smul_eq_mul, scalar_mul, Category.assoc]
  rw [Preadditive.comp_sum]

theorem comb_single [DecidableEq ι] (i : ι) : comb π σ (Pi.single i 1) = σ i := by
  unfold comb
  rw [Finset.sum_eq_single i]
  · rw [Pi.single_eq_same, scalar_one, Category.id_comp]
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj, scalar_zero]
    exact Limits.zero_comp
  · intro h; exact absurd (Finset.mem_univ i) h

noncomputable def vanishingAt (hM : Scheme.Modules.IsInvertible M) (x : X) : Submodule k (ι → k) where
  carrier := {c | x ∈ (zeroSchemeIdeal (comb π σ c)).support}
  zero_mem' := by
    simp only [Set.mem_setOf_eq, comb_zero]
    exact mem_support_zeroSchemeIdeal_zero x
  add_mem' := fun {c d} hc hd => by
    simp only [Set.mem_setOf_eq, comb_add]
    exact support_inf_le_support_add hM _ _ ⟨hc, hd⟩
  smul_mem' := fun a c hc => by
    simp only [Set.mem_setOf_eq, comb_smul]
    exact support_le_support_unitEnd_comp _ _ hc

theorem mem_vanishingAt (hM : Scheme.Modules.IsInvertible M) (x : X) (c : ι → k) :
    c ∈ vanishingAt π σ hM x ↔ x ∈ (zeroSchemeIdeal (comb π σ c)).support := Iff.rfl

end avoidance

theorem exists_forall_notMem_support {X : Scheme.{u}} {k : Type u} [Field k] [Infinite k]
    (π : X ⟶ Spec (.of k)) {M : X.Modules} (hM : Scheme.Modules.IsInvertible M)
    {ι : Type*} [Finite ι] (x : ι → X) (σ : ι → (𝟙_ X.Modules ⟶ M))
    (hσ : ∀ i, x i ∉ (zeroSchemeIdeal (σ i)).support) :
    ∃ s : 𝟙_ X.Modules ⟶ M, ∀ i, x i ∉ (zeroSchemeIdeal s).support := by
  classical
  let _ := Fintype.ofFinite ι
  have hne : ∀ i, vanishingAt π σ hM (x i) ≠ ⊤ := by
    intro i h
    apply hσ i
    have : (Pi.single i 1 : ι → k) ∈ vanishingAt π σ hM (x i) := h ▸ Submodule.mem_top
    rwa [mem_vanishingAt, comb_single] at this
  obtain ⟨c, hc⟩ := Submodule.exists_forall_notMem_of_forall_ne_top _ hne
  exact ⟨comb π σ c, fun i h => hc i h⟩

theorem main {k : Type u} [Field k] [Infinite k] {V : Scheme.{u}} (π : V ⟶ Spec (.of k))
    [NoetherianSpace V] (n : ℕ) :
    ∀ (N : Fin n → V.Modules) (_hN : ∀ i, Scheme.Modules.IsInvertible (N i))
      (_hbpf : ∀ (i : Fin n) (x : V), ∃ s : 𝟙_ V.Modules ⟶ N i,
        x ∉ (Scheme.Modules.zeroSchemeIdeal s).support)
      (B : Set V) (_hB : IsClosed B) (_hdim : topologicalKrullDim B < n),
      ∃ s : ∀ i : Fin n, (𝟙_ V.Modules ⟶ N i),
        B ∩ ⋂ i, ((Scheme.Modules.zeroSchemeIdeal (s i)).support : Set V) = ∅ := by
  induction n with
  | zero =>
    intro N hN hbpf B hB hdim
    refine ⟨fun i => Fin.elim0 i, ?_⟩
    rw [P2mAvoidTop.eq_empty_of_topologicalKrullDim_lt_zero hdim, Set.empty_inter]
  | succ n ih =>
    intro N hN hbpf B hB hdim

    obtain ⟨S, hSf, hSc, hSi, hSB⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hB
    lift S to Finset (Set V) using hSf

    have hpt : ∀ t : S, ∃ x : V, x ∈ (t : Set V) := fun t => (hSi t t.2).nonempty
    choose pt hpt using hpt
    choose σ hσ using fun t : S => hbpf (Fin.last n) (pt t)
    obtain ⟨sl, hsl⟩ := exists_forall_notMem_support π (hN (Fin.last n)) pt σ hσ

    set Z : Set V := ((zeroSchemeIdeal sl).support : Set V) with hZdef
    have hZ : IsClosed Z := (zeroSchemeIdeal sl).support.isClosed
    have havoid : ∀ t ∈ S, ¬ t ⊆ Z := fun t ht h => hsl ⟨t, ht⟩ (h (hpt ⟨t, ht⟩))
    have hdim' : topologicalKrullDim ↥(B ∩ Z) < n :=
      P2mAvoidTop.topologicalKrullDim_inter_lt S hSc hSi (by simpa using hSB) hZ havoid n
        (by simpa using hdim)
    obtain ⟨s', hs'⟩ := ih (fun i => N i.castSucc) (fun i => hN _) (fun i => hbpf _)
      (B ∩ Z) (hB.inter hZ) hdim'
    refine ⟨Fin.snoc (α := fun i => 𝟙_ V.Modules ⟶ N i) s' sl, ?_⟩
    rw [Set.eq_empty_iff_forall_notMem] at hs' ⊢
    rintro x ⟨hxB, hx⟩
    rw [Set.mem_iInter] at hx
    apply hs' x
    refine ⟨⟨hxB, ?_⟩, ?_⟩
    · have h := hx (Fin.last n)
      simpa only [Fin.snoc_last] using h
    · rw [Set.mem_iInter]
      intro i
      have h := hx i.castSucc
      simpa only [Fin.snoc_castSucc] using h

end P2mAvoid
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_inter_iInter_support_zeroSchemeIdeal_eq_empty_of_topologicalKrullDim_lt.P2mAvoid"

theorem solution
    {k : Type u} [Field k] [Infinite k] {V : Scheme.{u}} (π : V ⟶ Spec (.of k)) [NoetherianSpace V]
    {n : ℕ} (N : Fin n → V.Modules) (hN : ∀ i, Scheme.Modules.IsInvertible (N i))
    (hbpf : ∀ (i : Fin n) (x : V), ∃ s : 𝟙_ V.Modules ⟶ N i, x ∉ (Scheme.Modules.zeroSchemeIdeal s).support)
    (B : Set V) (hB : IsClosed B) (hdim : topologicalKrullDim B < n) :
    ∃ s : ∀ i : Fin n, (𝟙_ V.Modules ⟶ N i),
      B ∩ ⋂ i, ((Scheme.Modules.zeroSchemeIdeal (s i)).support : Set V) = ∅ :=
  P2mAvoid.main π n N hN hbpf B hB hdim

end S_AlgebraicGeometry_Scheme_Modules_exists_inter_iInter_support_zeroSchemeIdeal_eq_empty_of_topologicalKrullDim_lt
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_inter_iInter_support_zeroSchemeIdeal_eq_empty_of_topologicalKrullDim_lt (solution)
