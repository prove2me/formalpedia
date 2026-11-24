-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_GlueApplyOfNotInFibre
-- name    : Development_AutomorphicSpectrum_Definitions_GlobalGeometry_GlueApplyOfNotInFibre
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T13:00:33.256225+00:00
-- url     : https://prove2.me/theorems/4bbe990f-a9e1-4d6d-a842-6e511bc2b438
-- title:
--   Glue Apply Of Not In Fibre
-- statement:
--   Definitions and structural lemmas for Glue Apply Of Not In Fibre, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/GlueApplyOfNotInFibre.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_ExistsGenOfIsVBOne
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_StalkClosedPointToToStalk
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CoordInhab_genPt_specializes
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CoordInhab_inChart_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CptModel_genMap_toStalk
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CptModel_half_notMem
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CptModel_isCptGen_int
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CptModel_mem_regAt_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CptModel_not_unitAt_two
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CptModel_regAt_self
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CptModel_unitAt_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CptModel_unitAt_three
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_coordTie_spec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.Ar
open AlgebraicGeometry CategoryTheory
abbrev chRing (o : Type) [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} (x : κ → Ω) (c : κ) :
    Subalgebra o Ω :=
  Algebra.adjoin o (Set.range fun j => x j / x c)
structure PModel (o : Type) [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} (x : κ → Ω) where

  X : Scheme.{0}

  ξ : Spec (CommRingCat.of Ω) ⟶ X

  s : X ⟶ Spec (CommRingCat.of o)
  hover : ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap o Ω))
  all : ∀ q : X, genPt ξ ⤳ q
  tie : CoordTie o ξ x
def PModel.ofUnimodular (o K : Type) [CommRing o] [IsDomain o] [Field K] [Algebra o K] [IsFractionRing o K]
    {κ : Type} (x : κ → o) (hx : Ideal.span (Set.range x) = ⊤) :
    PModel o (fun j => algebraMap o K (x j)) where
  X := Spec (CommRingCat.of o)
  ξ := Spec.map (CommRingCat.ofHom (algebraMap o K))
  s := 𝟙 _
  hover := Category.comp_id _
  all := CoordInhab.genPt_specializes
  tie := coordTie_spec o K x hx
def PModel.twoThree : PModel ℤ (fun j => algebraMap ℤ ℚ ((![2, 3] : Fin 2 → ℤ) j)) :=
  PModel.ofUnimodular ℤ ℚ ![2, 3] (by
    rw [Ideal.eq_top_iff_one]
    have h := Ideal.sub_mem (Ideal.span (Set.range (![2, 3] : Fin 2 → ℤ)))
      (Ideal.subset_span ⟨1, rfl⟩) (Ideal.subset_span ⟨0, rfl⟩)
    simpa using h)
variable {X X' X'' : Scheme.{0}} {Ω Ω' Ω'' : Type} [Field Ω] [Field Ω'] [Field Ω'']
  {E F : Type} [AddCommGroup E] [Module Ω E] [AddCommGroup F] [Module Ω' F]
def joinCo {κ κ' : Type} (i : Ω →+* Ω') (x : κ → Ω) (w : κ' → Ω') : κ × κ' → Ω' := fun q => i (x q.1) * w q.2
def Lat.IsCohOn {ξ : Spec (CommRingCat.of Ω) ⟶ X} (L : Lat ξ E) (T : Set (Cpt ξ)) : Prop :=
  ∀ p ∈ T, ∃ U : X.Opens, p.1 ∈ U ∧ ∃ (n : ℕ) (b : Fin n → E),
    ∀ q ∈ T, q.1 ∈ U → L q = Submodule.span (regAt ξ q) (Set.range b)
def ctrSet (o : Type) [CommRing o] [Algebra o Ω] {κ : Type} (x : κ → Ω) (i : Ω →+* Ω')
    (ξ' : Spec (CommRingCat.of Ω') ⟶ X') : Set (Cpt ξ') :=
  {p' | ∃ c, x c ≠ 0 ∧ ∀ a ∈ chRing o x c, i a ∈ regAt ξ' p'}
def IsCtrOf {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξ' : Spec (CommRingCat.of Ω') ⟶ X'} (i : Ω →+* Ω') (p : Cpt ξ)
    (p' : Cpt ξ') : Prop :=
  (∀ a ∈ regAt ξ p, i a ∈ regAt ξ' p') ∧ ∀ a ∈ regAt ξ p, unitAt ξ' p' (i a) → unitAt ξ p a
def Lat.pullLoc {ξ : Spec (CommRingCat.of Ω) ⟶ X} (L : Lat ξ E) (ξ' : Spec (CommRingCat.of Ω') ⟶ X')
    (i : Ω →+* Ω') (j : E →+ F) : Lat ξ' F := fun p' =>
  Submodule.span (regAt ξ' p') {e' | ∃ p : Cpt ξ, IsCtrOf i p p' ∧ ∃ e ∈ L p, e' = j e}
def IsExtOver (i : Ω →+* Ω') (j : E →+ F) : Prop :=
  (∀ (a : Ω) (e : E), j (a • e) = i a • j e) ∧
    ∀ (n : ℕ) (b : Fin n → E), LinearIndependent Ω b → LinearIndependent Ω' fun k => j (b k)
structure IsoAt (ξ' : Spec (CommRingCat.of Ω') ⟶ X') {ξ : Spec (CommRingCat.of Ω) ⟶ X} (f : X' ⟶ X) (i : Ω →+* Ω')
    (p : Cpt ξ) : Prop where

  existsUnique : ∃! p' : Cpt ξ', f p'.1 = p.1

  regAt_eq : ∀ p' : Cpt ξ', f p'.1 = p.1 → regAt ξ' p' = (regAt ξ p).map i

  dom : Dominates ξ' ξ f i
structure NormAt (ξ' : Spec (CommRingCat.of Ω') ⟶ X') {ξ : Spec (CommRingCat.of Ω) ⟶ X} (f : X' ⟶ X) (i : Ω →+* Ω')
    (p : Cpt ξ) : Prop where

  exists_max : ∀ p' : Cpt ξ', f p'.1 = p.1 →
    ∃ (P : Ideal (integralClosure ((regAt ξ p).map i) Ω').toSubring) (_ : P.IsMaximal),
      regAt ξ' p' = (LocalSubring.ofPrime _ P).toSubring

  existsUnique : ∀ (P : Ideal (integralClosure ((regAt ξ p).map i) Ω').toSubring) (_ : P.IsMaximal),
    ∃! p' : Cpt ξ', f p'.1 = p.1 ∧ regAt ξ' p' = (LocalSubring.ofPrime _ P).toSubring

  dom : Dominates ξ' ξ f i
def genFib (ξ : Spec (CommRingCat.of Ω) ⟶ X) : Set (Cpt ξ) := {p | ∀ n : ℕ, 0 < n → unitAt ξ p (n : Ω)}
def locFib (ξ : Spec (CommRingCat.of Ω) ⟶ X) (q : ℕ) : Set (Cpt ξ) := {p | ∀ n : ℕ, n.Coprime q → unitAt ξ p (n : Ω)}
def invFib (ξ : Spec (CommRingCat.of Ω) ⟶ X) (m : ℕ) : Set (Cpt ξ) := {p | unitAt ξ p (m : Ω)}
open Classical in

def Lat.glue {ξ : Spec (CommRingCat.of Ω) ⟶ X} (S : Finset ℕ) (L₀ : Lat ξ E) (Lq : ℕ → Lat ξ E) : Lat ξ E := fun p =>
  if h : ∃ q ∈ S, InFibre ξ q p then Lq h.choose p else L₀ p
def Lat.predualIn {ξ : Spec (CommRingCat.of Ω) ⟶ X} (L : Lat ξ (Module.Dual Ω E)) (V : Submodule Ω E) : Lat ξ E :=
  fun p =>
  { carrier := {v | v ∈ V ∧ ∀ w ∈ L p, w v ∈ regAt ξ p}
    add_mem' := fun ha hb => ⟨V.add_mem ha.1 hb.1, fun w hw => by simpa using add_mem (ha.2 w hw) (hb.2 w hw)⟩
    zero_mem' := ⟨V.zero_mem, fun w _ => by simp⟩
    smul_mem' := fun c v hv => ⟨V.smul_mem (c : Ω) hv.1, fun w hw => by
      have : w (c • v) = (c : Ω) * w v := by
        show w ((c : Ω) • v) = _
        rw [map_smul, smul_eq_mul]
      rw [this]
      exact mul_mem c.2 (hv.2 w hw)⟩ }
section API
variable {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξ' : Spec (CommRingCat.of Ω') ⟶ X'}
  {ξ'' : Spec (CommRingCat.of Ω'') ⟶ X''}
theorem IsCtrOf.refl (p : Cpt ξ) : IsCtrOf (RingHom.id Ω) p p := ⟨fun _ h => h, fun _ _ h => h⟩
theorem IsCtrOf.unitAt_iff {i : Ω →+* Ω'} {p : Cpt ξ} {p' : Cpt ξ'} (h : IsCtrOf i p p') {a : Ω}
    (ha : a ∈ regAt ξ p) : unitAt ξ' p' (i a) ↔ unitAt ξ p a :=
  ⟨h.2 a ha, fun hu => ⟨(map_ne_zero i).2 hu.1, h.1 _ hu.2.1, by rw [← map_inv₀]; exact h.1 _ hu.2.2⟩⟩
theorem IsCtrOf.unitAt_spec {R : Type} [CommRing R] {φ : R →+* Ω} (hφ : Function.Injective φ)
    (p : Cpt (CptModel.pt φ)) (a : R) : unitAt (CptModel.pt φ) p (φ a) ↔ a ∉ p.1.asIdeal := by
  constructor
  · rintro ⟨h0, -, h⟩ hc
    obtain ⟨r, s, hs, -, e⟩ := (CptModel.mem_regAt_iff φ p _).1 h
    have : s = a * r := hφ (by rw [map_mul, ← e, mul_inv_cancel_left₀ h0])
    exact hs (this ▸ Ideal.mul_mem_right _ _ hc)
  · intro hc
    have h0 : φ a ≠ 0 := (map_ne_zero_iff _ hφ).2 fun h => hc (h ▸ Ideal.zero_mem _)
    exact ⟨h0, ⟨_, CptModel.genMap_toStalk φ p a⟩,
      (CptModel.mem_regAt_iff φ p _).2 ⟨1, a, hc, h0, by rw [map_one, inv_mul_cancel₀ h0]⟩⟩
theorem IsCtrOf.unique_spec {R : Type} [CommRing R] {φ : R →+* Ω} (hφ : Function.Injective φ) {i : Ω →+* Ω'}
    {p q : Cpt (CptModel.pt φ)} {p' : Cpt ξ'} (hp : IsCtrOf i p p') (hq : IsCtrOf i q p') : p = q := by
  refine Subtype.ext (PrimeSpectrum.ext (Ideal.ext fun a => not_iff_not.1 ?_))
  exact ((IsCtrOf.unitAt_spec hφ p a).symm.trans
    ((hp.unitAt_iff ⟨_, CptModel.genMap_toStalk φ p a⟩).symm.trans
      (hq.unitAt_iff ⟨_, CptModel.genMap_toStalk φ q a⟩))).trans (IsCtrOf.unitAt_spec hφ q a)
theorem IsoAt.refl (p : Cpt ξ) : IsoAt ξ (𝟙 X) (RingHom.id Ω) p := by
  refine ⟨⟨p, rfl, fun q hq => Subtype.ext hq⟩, fun q hq => ?_, by simp [Dominates]⟩
  obtain rfl : q = p := Subtype.ext hq
  exact (Subring.map_id _).symm
theorem NormAt.isLocalRing_regAt (p : Cpt ξ) : IsLocalRing (regAt ξ p) :=
  IsLocalRing.of_surjective' (genMap ξ p).rangeRestrict (genMap ξ p).rangeRestrict_surjective
theorem NormAt.ofPrime_of_isLocalRing (A : Subring Ω) [IsLocalRing A] (P : Ideal A) (hP : P.IsMaximal) :
    (LocalSubring.ofPrime A P).toSubring = A := by
  obtain rfl := IsLocalRing.eq_maximalIdeal hP
  refine le_antisymm ?_ (LocalSubring.le_ofPrime A _)
  intro a ha
  obtain ⟨⟨u, s⟩, e⟩ := IsLocalization.surj (IsLocalRing.maximalIdeal A).primeCompl
    (⟨a, ha⟩ : (LocalSubring.ofPrime A (IsLocalRing.maximalIdeal A)).toSubring)
  have hs : IsUnit (s : A) := by
    by_contra h
    exact s.2 h
  obtain ⟨v, hv⟩ := hs.exists_right_inv
  have e' : a * ((s : A) : Ω) = (u : Ω) := congrArg Subtype.val e
  have hv' : ((s : A) : Ω) * (v : Ω) = 1 := congrArg Subtype.val hv
  have : a = (u : Ω) * v := by rw [← e', mul_assoc, hv', mul_one]
  rw [this]
  exact A.mul_mem u.2 v.2
theorem NormAt.of_unique {f : X' ⟶ X} {i : Ω →+* Ω'} {p : Cpt ξ} (hd : Dominates ξ' ξ f i) (p₀ : Cpt ξ')
    (h₀ : f p₀.1 = p.1) (hu : ∀ q : Cpt ξ', f q.1 = p.1 → q = p₀)
    (e : (integralClosure ((regAt ξ p).map i) Ω').toSubring = regAt ξ' p₀) : NormAt ξ' f i p := by
  have loc : IsLocalRing (integralClosure ((regAt ξ p).map i) Ω').toSubring := by
    rw [e]
    exact NormAt.isLocalRing_regAt p₀
  refine ⟨fun q hq => ?_, fun P hP => ⟨p₀, ⟨h₀, ((NormAt.ofPrime_of_isLocalRing _ P hP).trans e).symm⟩,
    fun q hq => hu q hq.1⟩, hd⟩
  rw [hu q hq]
  exact ⟨_, IsLocalRing.maximalIdeal.isMaximal _,
    ((NormAt.ofPrime_of_isLocalRing _ _ (IsLocalRing.maximalIdeal.isMaximal _)).trans e).symm⟩
theorem NormAt.refl (p : Cpt ξ) (h : ∀ a : Ω, IsIntegral (regAt ξ p) a → a ∈ regAt ξ p) :
    NormAt ξ (𝟙 X) (RingHom.id Ω) p := by
  refine NormAt.of_unique (by simp [Dominates]) p rfl (fun q hq => Subtype.ext hq) ?_
  rw [Subring.map_id]
  ext a
  exact ⟨h a, fun ha => isIntegral_algebraMap (x := (⟨a, ha⟩ : regAt ξ p))⟩
theorem NormAt.regAt_field (p : Cpt (CptModel.pt (RingHom.id Ω))) : regAt _ p = ⊤ :=
  eq_top_iff.2 fun a _ => ⟨_, CptModel.genMap_toStalk (RingHom.id Ω) p a⟩
theorem NormAt.dominates_field_iff (φ i : Ω →+* Ω') :
    Dominates (CptModel.pt (RingHom.id Ω')) (CptModel.pt (RingHom.id Ω)) (CptModel.pt φ) i ↔ φ = i := by
  unfold Dominates
  rw [← Spec.map_comp, ← Spec.map_comp, Spec.map_inj]
  exact ⟨fun h => congrArg CommRingCat.Hom.hom h, fun h => h ▸ rfl⟩
theorem NormAt.of_isAlgebraic [Algebra Ω Ω'] [Algebra.IsAlgebraic Ω Ω'] (p : Cpt (CptModel.pt (RingHom.id Ω))) :
    NormAt (CptModel.pt (RingHom.id Ω')) (CptModel.pt (algebraMap Ω Ω')) (algebraMap Ω Ω') p := by
  refine NormAt.of_unique ((NormAt.dominates_field_iff _ _).2 rfl) (CptModel.self _)
    (Subsingleton.elim (α := PrimeSpectrum Ω) _ _)
    (fun q _ => Subtype.ext (Subsingleton.elim (α := PrimeSpectrum Ω') _ _)) ?_
  rw [NormAt.regAt_field, NormAt.regAt_field, eq_top_iff]
  intro a _
  let g : Ω →+* (⊤ : Subring Ω).map (algebraMap Ω Ω') :=
    (algebraMap Ω Ω').codRestrict _ fun b => ⟨b, trivial, rfl⟩
  have h : IsIntegral Ω a := Algebra.IsIntegral.isIntegral a
  exact IsIntegral.map_of_comp_eq g (RingHom.id Ω') (RingHom.ext fun _ => rfl) h
theorem IsoAt.field_iff (φ i : Ω →+* Ω') (p : Cpt (CptModel.pt (RingHom.id Ω))) :
    IsoAt (CptModel.pt (RingHom.id Ω')) (CptModel.pt φ) i p ↔ φ = i ∧ Function.Surjective i := by
  constructor
  · intro h
    refine ⟨(NormAt.dominates_field_iff _ _).1 h.dom, fun a => ?_⟩
    have e := h.regAt_eq (CptModel.self _) (Subsingleton.elim (α := PrimeSpectrum Ω) _ _)
    rw [NormAt.regAt_field] at e
    obtain ⟨b, -, hb⟩ : a ∈ (regAt _ p).map i := e ▸ Subring.mem_top a
    exact ⟨b, hb⟩
  · rintro ⟨h, hs⟩
    refine ⟨⟨CptModel.self _, Subsingleton.elim (α := PrimeSpectrum Ω) _ _,
      fun q _ => Subtype.ext (Subsingleton.elim (α := PrimeSpectrum Ω') _ _)⟩, fun q _ => ?_,
      (NormAt.dominates_field_iff _ _).2 h⟩
    rw [NormAt.regAt_field, NormAt.regAt_field, eq_comm, eq_top_iff]
    intro a _
    obtain ⟨b, rfl⟩ := hs a
    exact ⟨b, trivial, rfl⟩
end API
example : InChart PModel.twoThree.ξ (fun j => algebraMap ℤ ℚ ((![2, 3] : Fin 2 → ℤ) j)) 1 CptModel.two ∧
    ¬ InChart PModel.twoThree.ξ (fun j => algebraMap ℤ ℚ ((![2, 3] : Fin 2 → ℤ) j)) 0 CptModel.two := by
  have hx : Ideal.span (Set.range (![2, 3] : Fin 2 → ℤ)) = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    have h := Ideal.sub_mem (Ideal.span (Set.range (![2, 3] : Fin 2 → ℤ)))
      (Ideal.subset_span ⟨1, rfl⟩) (Ideal.subset_span ⟨0, rfl⟩)
    simpa using h
  refine ⟨(CoordInhab.inChart_iff _ hx 1 CptModel.two).2 fun h => ?_,
    fun h => (CoordInhab.inChart_iff _ hx 0 CptModel.two).1 h (Ideal.mem_span_singleton_self _)⟩
  exact absurd (Ideal.mem_span_singleton.1 h) (by decide)
example : ¬ IsCtrOf (RingHom.id ℚ) CptModel.two (CptModel.self (CptModel.pt (algebraMap ℤ ℚ))) := fun h => by
  have e := IsCtrOf.unique_spec (IsFractionRing.injective ℤ ℚ) h (IsCtrOf.refl _)
  apply CptModel.half_notMem
  rw [e, CptModel.regAt_self CptModel.isCptGen_int]
  trivial
example (p : Cpt (CptModel.pt (RingHom.id ℝ))) :
    NormAt (CptModel.pt (RingHom.id ℂ)) (CptModel.pt (algebraMap ℝ ℂ)) (algebraMap ℝ ℂ) p ∧
      ¬ IsoAt (CptModel.pt (RingHom.id ℂ)) (CptModel.pt (algebraMap ℝ ℂ)) (algebraMap ℝ ℂ) p :=
  ⟨NormAt.of_isAlgebraic p, fun h => by
    obtain ⟨b, hb⟩ := ((IsoAt.field_iff _ _ p).1 h).2 Complex.I
    simpa using congrArg Complex.im hb⟩
example (p : Cpt (CptModel.pt (RingHom.id ℂ))) :
    IsoAt (CptModel.pt (RingHom.id ℂ)) (CptModel.pt (starRingEnd ℂ)) (starRingEnd ℂ) p ∧
      ¬ IsoAt (CptModel.pt (RingHom.id ℂ)) (CptModel.pt (starRingEnd ℂ)) (RingHom.id ℂ) p :=
  ⟨(IsoAt.field_iff _ _ p).2 ⟨rfl, fun a => ⟨starRingEnd ℂ a, Complex.conj_conj a⟩⟩, fun h => by
    have := congrArg (fun g : ℂ →+* ℂ => (g Complex.I).im) ((IsoAt.field_iff _ _ p).1 h).1
    norm_num at this⟩
example : CptModel.two ∈ invFib _ 3 ∧ CptModel.two ∉ invFib _ 2 ∧ CptModel.two ∉ locFib _ 3 ∧
    CptModel.two ∉ genFib _ :=
  ⟨by simpa [invFib] using CptModel.unitAt_three, fun h => CptModel.not_unitAt_two (by simpa [invFib] using h),
    fun h => CptModel.not_unitAt_two (by simpa using h 2 (by norm_num)),
    fun h => CptModel.not_unitAt_two (by simpa using h 2 two_pos)⟩
end GlobalTheory.CompanionTheory.Ar


