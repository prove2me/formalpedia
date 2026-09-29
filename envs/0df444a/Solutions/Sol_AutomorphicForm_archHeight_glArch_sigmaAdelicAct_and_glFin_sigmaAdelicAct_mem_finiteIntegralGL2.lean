-- Prove2me | solution 1 for AutomorphicForm.archHeight_glArch_sigmaAdelicAct_and_glFin_sigmaAdelicAct_mem_finiteIntegralGL2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/0f313984-8608-500c-ac94-0a3665960bcd

import Mathlib
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_WindowedSiegelSet
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_archHeight_glArch_sigmaAdelicAct_and_glFin_sigmaAdelicAct_mem_finiteIntegralGL2

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace R3HGT

open NumberField NumberField.InfinitePlace NumberField.AdelicLevel IsDedekindDomain
open scoped Topology

section Rigidity

variable {L : Type*} [Field L] [NumberField L]

theorem norm_map_eq_of_continuous_toComplex (u : InfinitePlace L) (h : u.Completion →+* ℂ)
    (hh : Continuous h) (y : u.Completion) : ‖h y‖ = ‖y‖ := by
  by_cases hu : u.IsReal
  ·
    set e := Completion.ringEquivRealOfIsReal hu with he
    have hesymm : Continuous e.symm := (Completion.isometryEquivRealOfIsReal hu).symm.continuous
    set k : ℝ →+* ℂ := h.comp e.symm.toRingHom with hk
    have hkc : Continuous k := hh.comp hesymm
    have hk' : k = Complex.ofRealHom := Complex.ringHom_eq_ofReal_of_continuous hkc
    have hy : h y = k (e y) := by
      simp only [hk, RingHom.coe_comp, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        Function.comp_apply, RingEquiv.symm_apply_apply]
    rw [hy, hk', Complex.ofRealHom_eq_coe, Complex.norm_real, he, Completion.ringEquivRealOfIsReal_apply]
    exact (Completion.isometry_extensionEmbeddingOfIsReal hu).norm_map_of_map_zero (map_zero _) y
  ·
    have hc : u.IsComplex := not_isReal_iff_isComplex.mp hu
    set E := Completion.ringEquivComplexOfIsComplex hc with hE
    have hEsymm : Continuous E.symm := (Completion.isometryEquivComplexOfIsComplex hc).symm.continuous
    set k : ℂ →+* ℂ := h.comp E.symm.toRingHom with hk
    have hkc : Continuous k := hh.comp hEsymm
    have hy : h y = k (E y) := by
      simp only [hk, RingHom.coe_comp, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        Function.comp_apply, RingEquiv.symm_apply_apply]
    have hnormE : ‖E y‖ = ‖y‖ := by
      rw [hE, Completion.ringEquivComplexOfIsComplex_apply]
      exact (Completion.isometry_extensionEmbedding u).norm_map_of_map_zero (map_zero _) y
    rw [hy]
    rcases Complex.ringHom_eq_id_or_conj_of_continuous hkc with hid | hconj
    · rw [hid, RingHom.id_apply, hnormE]
    · rw [hconj, Complex.norm_conj, hnormE]

theorem norm_map_eq_of_continuous {u u' : InfinitePlace L} (φ : u.Completion →+* u'.Completion)
    (hφ : Continuous φ) (y : u.Completion) : ‖φ y‖ = ‖y‖ := by
  have h1 : ‖Completion.extensionEmbedding u' (φ y)‖ = ‖φ y‖ :=
    (Completion.isometry_extensionEmbedding u').norm_map_of_map_zero (map_zero _) (φ y)
  rw [← h1]
  exact norm_map_eq_of_continuous_toComplex u ((Completion.extensionEmbedding u').comp φ)
    ((Completion.isometry_extensionEmbedding u').continuous.comp hφ) y

theorem isReal_iff_forall_sq_ne_neg_one (u : InfinitePlace L) :
    u.IsReal ↔ ∀ y : u.Completion, y ^ 2 ≠ -1 := by
  constructor
  · intro hu y hy
    have h := congrArg (Completion.ringEquivRealOfIsReal hu) hy
    rw [map_pow, map_neg, map_one] at h
    nlinarith [sq_nonneg (Completion.ringEquivRealOfIsReal hu y)]
  · intro h
    by_contra hu
    have hc : u.IsComplex := not_isReal_iff_isComplex.mp hu
    apply h ((Completion.ringEquivComplexOfIsComplex hc).symm Complex.I)
    apply (Completion.ringEquivComplexOfIsComplex hc).injective
    rw [map_pow, RingEquiv.apply_symm_apply, Complex.I_sq, map_neg, map_one]

theorem isReal_of_ringHom {u u' : InfinitePlace L} (φ : u.Completion →+* u'.Completion) (hu' : u'.IsReal) :
    u.IsReal := by
  rw [isReal_iff_forall_sq_ne_neg_one] at hu' ⊢
  intro y hy
  exact hu' (φ y) (by rw [← map_pow, hy, map_neg, map_one])

theorem norm_natCast_completion (u : InfinitePlace L) (n : ℕ) : ‖(n : u.Completion)‖ = n := by
  have h := (Completion.isometry_extensionEmbedding u).norm_map_of_map_zero (map_zero _) (n : u.Completion)
  rw [map_natCast, Complex.norm_natCast] at h
  exact h.symm

end Rigidity

section Decomposition

variable {L : Type} [Field L] [NumberField L]

private def _root_.R3HGT.inl (x : InfiniteAdeleRing L) : AdeleRing (𝓞 L) L := (x, 0)

p2m_export "R3HGT" "inl"

private def _root_.R3HGT.inr (y : FiniteAdeleRing (𝓞 L) L) : AdeleRing (𝓞 L) L := (0, y)

p2m_export "R3HGT" "inr"
@[scoped simp] theorem fst_inl (x : InfiniteAdeleRing L) : (inl x).1 = x := rfl
@[scoped simp] theorem snd_inl (x : InfiniteAdeleRing L) : (inl x).2 = 0 := rfl
@[scoped simp] theorem fst_inr (y : FiniteAdeleRing (𝓞 L) L) : (inr y).1 = 0 := rfl
@[scoped simp] theorem snd_inr (y : FiniteAdeleRing (𝓞 L) L) : (inr y).2 = y := rfl

theorem fst_mul' (a b : AdeleRing (𝓞 L) L) : (a * b).1 = a.1 * b.1 := rfl
theorem snd_mul' (a b : AdeleRing (𝓞 L) L) : (a * b).2 = a.2 * b.2 := rfl
theorem fst_add' (a b : AdeleRing (𝓞 L) L) : (a + b).1 = a.1 + b.1 := rfl
theorem snd_add' (a b : AdeleRing (𝓞 L) L) : (a + b).2 = a.2 + b.2 := rfl
theorem fst_zero' : (0 : AdeleRing (𝓞 L) L).1 = 0 := rfl
theorem snd_zero' : (0 : AdeleRing (𝓞 L) L).2 = 0 := rfl
theorem fst_one' : (1 : AdeleRing (𝓞 L) L).1 = 1 := rfl
theorem snd_one' : (1 : AdeleRing (𝓞 L) L).2 = 1 := rfl
theorem fst_natCast' (n : ℕ) : ((n : AdeleRing (𝓞 L) L)).1 = n := map_natCast (adeleArch (𝓞 L) L) n
theorem snd_natCast' (n : ℕ) : ((n : AdeleRing (𝓞 L) L)).2 = n := map_natCast (adeleFin (𝓞 L) L) n

theorem ext_ad {a b : AdeleRing (𝓞 L) L} (h1 : a.1 = b.1) (h2 : a.2 = b.2) : a = b := Prod.ext h1 h2

theorem inl_mul (x y : InfiniteAdeleRing L) : inl x * inl y = inl (x * y) :=
  ext_ad rfl (by rw [snd_mul', snd_inl, snd_inl, snd_inl, mul_zero])
theorem inl_add (x y : InfiniteAdeleRing L) : inl x + inl y = inl (x + y) :=
  ext_ad rfl (by rw [snd_add', snd_inl, snd_inl, snd_inl, add_zero])
theorem inl_zero : inl (0 : InfiniteAdeleRing L) = 0 := ext_ad rfl rfl
theorem inr_mul (x y : FiniteAdeleRing (𝓞 L) L) : inr x * inr y = inr (x * y) :=
  ext_ad (by rw [fst_mul', fst_inr, fst_inr, fst_inr, mul_zero]) rfl
theorem inr_add (x y : FiniteAdeleRing (𝓞 L) L) : inr x + inr y = inr (x + y) :=
  ext_ad (by rw [fst_add', fst_inr, fst_inr, fst_inr, add_zero]) rfl
theorem inr_zero : inr (0 : FiniteAdeleRing (𝓞 L) L) = 0 := ext_ad rfl rfl
theorem inl_add_inr (a : AdeleRing (𝓞 L) L) : inl a.1 + inr a.2 = a :=
  ext_ad (by rw [fst_add', fst_inl, fst_inr, add_zero]) (by rw [snd_add', snd_inl, snd_inr, zero_add])
theorem one_eq_inl_add_inr : (1 : AdeleRing (𝓞 L) L) = inl 1 + inr 1 :=
  ext_ad (by rw [fst_add', fst_inl, fst_inr, add_zero]; rfl) (by rw [snd_add', snd_inl, snd_inr, zero_add]; rfl)

theorem continuous_inl : Continuous (inl : InfiniteAdeleRing L → AdeleRing (𝓞 L) L) :=
  (Continuous.prodMk continuous_id continuous_const : Continuous fun x : InfiniteAdeleRing L =>
    ((x, (0 : FiniteAdeleRing (𝓞 L) L)) : InfiniteAdeleRing L × FiniteAdeleRing (𝓞 L) L))
theorem continuous_inr : Continuous (inr : FiniteAdeleRing (𝓞 L) L → AdeleRing (𝓞 L) L) :=
  (Continuous.prodMk continuous_const continuous_id : Continuous fun y : FiniteAdeleRing (𝓞 L) L =>
    (((0 : InfiniteAdeleRing L), y) : InfiniteAdeleRing L × FiniteAdeleRing (𝓞 L) L))
theorem continuous_fst' : Continuous fun a : AdeleRing (𝓞 L) L => a.1 := continuous_adeleArch (𝓞 L) L
theorem continuous_snd' : Continuous fun a : AdeleRing (𝓞 L) L => a.2 := continuous_adeleFin (𝓞 L) L

def MulCpt (a : AdeleRing (𝓞 L) L) : Prop :=
  ∃ C : Set (AdeleRing (𝓞 L) L), IsCompact C ∧ ∀ n : ℕ, (n : AdeleRing (𝓞 L) L) * a ∈ C

theorem mulCpt_map (θ : AdeleRing (𝓞 L) L ≃+* AdeleRing (𝓞 L) L) (hθ : Continuous θ)
    {a : AdeleRing (𝓞 L) L} (h : MulCpt a) : MulCpt (θ a) := by
  obtain ⟨C, hC, hn⟩ := h
  refine ⟨θ '' C, hC.image hθ, fun n => ⟨_, hn n, ?_⟩⟩
  rw [map_mul, map_natCast]

theorem isCompact_integralFiniteAdeles' : IsCompact (integralFiniteAdeles (𝓞 L) L) := by
  haveI : ∀ v : HeightOneSpectrum (𝓞 L),
      CompactSpace ((v.adicCompletionIntegers L : Set (v.adicCompletion L))) := fun v =>
    inferInstanceAs (CompactSpace (v.adicCompletionIntegers L))
  have h := isCompact_range (RestrictedProduct.isOpenEmbedding_structureMap
    (R := fun v : HeightOneSpectrum (𝓞 L) => v.adicCompletion L)
    (A := fun v : HeightOneSpectrum (𝓞 L) => (v.adicCompletionIntegers L : Set (v.adicCompletion L)))
    Fact.out).continuous
  rw [RestrictedProduct.range_structureMap] at h
  exact h

theorem natCast_apply (n : ℕ) (v : HeightOneSpectrum (𝓞 L)) :
    ((n : FiniteAdeleRing (𝓞 L) L)) v = (n : v.adicCompletion L) :=
  map_natCast (finAdeleEval (𝓞 L) L v) n

theorem natCast_mem_integralFiniteAdeles (n : ℕ) :
    ((n : FiniteAdeleRing (𝓞 L) L)) ∈ integralFiniteAdeles (𝓞 L) L := by
  intro v
  rw [natCast_apply]
  simp

theorem mulCpt_iff (a : AdeleRing (𝓞 L) L) : MulCpt a ↔ a.1 = 0 := by
  constructor
  · rintro ⟨C, hC, hn⟩
    funext w
    have hcont : Continuous fun c : AdeleRing (𝓞 L) L => c.1 w := (continuous_apply w).comp continuous_fst'
    obtain ⟨M, hM⟩ := (hC.image hcont).exists_bound_of_continuousOn continuous_id.continuousOn
    have hbound : ∀ n : ℕ, (n : ℝ) * ‖a.1 w‖ ≤ M := by
      intro n
      have h1 := hM _ ⟨_, hn n, rfl⟩
      simp only [id] at h1
      have h2 : ((n : AdeleRing (𝓞 L) L) * a).1 w = (n : w.Completion) * a.1 w := by
        rw [fst_mul', fst_natCast']; rfl
      rw [h2, norm_mul, norm_natCast_completion] at h1
      exact h1
    by_contra hne
    have hpos : 0 < ‖a.1 w‖ := norm_pos_iff.mpr hne
    obtain ⟨n, hn'⟩ := exists_nat_gt (M / ‖a.1 w‖)
    have := hbound n
    rw [div_lt_iff₀ hpos] at hn'
    linarith
  · intro ha
    refine ⟨inr '' ((fun r => r * a.2) '' integralFiniteAdeles (𝓞 L) L),
      ((isCompact_integralFiniteAdeles'.image (continuous_id.mul continuous_const)).image continuous_inr),
      fun n => ⟨(n : FiniteAdeleRing (𝓞 L) L) * a.2, ⟨_, natCast_mem_integralFiniteAdeles n, rfl⟩, ?_⟩⟩
    exact ext_ad (by rw [fst_inr, fst_mul', ha, mul_zero]) (by rw [snd_inr, snd_mul', snd_natCast'])

theorem fst_map_eq_zero (θ : AdeleRing (𝓞 L) L ≃+* AdeleRing (𝓞 L) L) (hθ : Continuous θ)
    {a : AdeleRing (𝓞 L) L} (ha : a.1 = 0) : (θ a).1 = 0 :=
  (mulCpt_iff (θ a)).mp (mulCpt_map θ hθ ((mulCpt_iff a).mpr ha))

theorem snd_eq_zero_iff (x : AdeleRing (𝓞 L) L) :
    x.2 = 0 ↔ ∀ y : AdeleRing (𝓞 L) L, y.1 = 0 → x * y = 0 := by
  constructor
  · intro hx y hy
    exact ext_ad (by rw [fst_mul', hy, mul_zero, fst_zero']) (by rw [snd_mul', hx, zero_mul, snd_zero'])
  · intro h
    have h1 := congrArg Prod.snd (h (inr 1) rfl)
    rw [snd_mul', snd_inr, mul_one] at h1
    exact h1

theorem snd_map_eq_zero (θ : AdeleRing (𝓞 L) L ≃+* AdeleRing (𝓞 L) L) (hθ' : Continuous θ.symm)
    {a : AdeleRing (𝓞 L) L} (ha : a.2 = 0) : (θ a).2 = 0 := by
  rw [snd_eq_zero_iff] at ha ⊢
  intro y hy
  have hy' : (θ.symm y).1 = 0 := fst_map_eq_zero θ.symm hθ' hy
  have := ha (θ.symm y) hy'
  rw [← θ.apply_symm_apply y, ← map_mul, this, map_zero]

variable (θ : AdeleRing (𝓞 L) L ≃+* AdeleRing (𝓞 L) L) (hθ : Continuous θ) (hθ' : Continuous θ.symm)

def thetaInf (θ : AdeleRing (𝓞 L) L ≃+* AdeleRing (𝓞 L) L) (hθ : Continuous θ) :
    InfiniteAdeleRing L →+* InfiniteAdeleRing L where
  toFun x := (θ (inl x)).1
  map_one' := by
    have h0 : (θ (inr 1)).1 = 0 := fst_map_eq_zero θ hθ rfl
    have h : (θ 1).1 = (1 : InfiniteAdeleRing L) := by rw [map_one]; rfl
    rw [one_eq_inl_add_inr, map_add, fst_add', h0, add_zero] at h
    exact h
  map_mul' x y := by
    show (θ (inl (x * y))).1 = (θ (inl x)).1 * (θ (inl y)).1
    rw [← inl_mul, map_mul, fst_mul']
  map_zero' := by
    show (θ (inl 0)).1 = 0
    rw [inl_zero, map_zero, fst_zero']
  map_add' x y := by
    show (θ (inl (x + y))).1 = (θ (inl x)).1 + (θ (inl y)).1
    rw [← inl_add, map_add, fst_add']

def thetaFin (θ : AdeleRing (𝓞 L) L ≃+* AdeleRing (𝓞 L) L) (hθ' : Continuous θ.symm) :
    FiniteAdeleRing (𝓞 L) L →+* FiniteAdeleRing (𝓞 L) L where
  toFun x := (θ (inr x)).2
  map_one' := by
    have h0 : (θ (inl 1)).2 = 0 := snd_map_eq_zero θ hθ' rfl
    have h : (θ 1).2 = (1 : FiniteAdeleRing (𝓞 L) L) := by rw [map_one]; rfl
    rw [one_eq_inl_add_inr, map_add, snd_add', h0, zero_add] at h
    exact h
  map_mul' x y := by
    show (θ (inr (x * y))).2 = (θ (inr x)).2 * (θ (inr y)).2
    rw [← inr_mul, map_mul, snd_mul']
  map_zero' := by
    show (θ (inr 0)).2 = 0
    rw [inr_zero, map_zero, snd_zero']
  map_add' x y := by
    show (θ (inr (x + y))).2 = (θ (inr x)).2 + (θ (inr y)).2
    rw [← inr_add, map_add, snd_add']

theorem thetaInf_apply (x : InfiniteAdeleRing L) : thetaInf θ hθ x = (θ (inl x)).1 := rfl

theorem thetaFin_apply (x : FiniteAdeleRing (𝓞 L) L) : thetaFin θ hθ' x = (θ (inr x)).2 := rfl

include hθ hθ' in

theorem map_fst (a : AdeleRing (𝓞 L) L) : (θ a).1 = thetaInf θ hθ a.1 := by
  conv_lhs => rw [← inl_add_inr a, map_add, fst_add']
  rw [fst_map_eq_zero θ hθ (a := inr a.2) rfl, add_zero]
  rfl

include hθ hθ' in
theorem map_snd (a : AdeleRing (𝓞 L) L) : (θ a).2 = thetaFin θ hθ' a.2 := by
  conv_lhs => rw [← inl_add_inr a, map_add, snd_add']
  rw [snd_map_eq_zero θ hθ' (a := inl a.1) rfl, zero_add]
  rfl

include hθ in
theorem continuous_thetaInf : Continuous (thetaInf θ hθ) := by
  show Continuous fun x : InfiniteAdeleRing L => (θ (inl x)).1
  exact continuous_fst'.comp (hθ.comp continuous_inl)

include hθ hθ' in
theorem continuous_thetaFin : Continuous (thetaFin θ hθ') := by
  show Continuous fun x : FiniteAdeleRing (𝓞 L) L => (θ (inr x)).2
  exact continuous_snd'.comp (hθ.comp continuous_inr)

include hθ hθ' in
theorem thetaInf_injective : Function.Injective (thetaInf θ hθ) := by
  intro x y hxy
  have h1 : (θ (inl x)).1 = (θ (inl y)).1 := hxy
  have h2 : (θ (inl x)).2 = (θ (inl y)).2 := by
    rw [snd_map_eq_zero θ hθ' (a := inl x) rfl, snd_map_eq_zero θ hθ' (a := inl y) rfl]
  have h3 : θ (inl x) = θ (inl y) := ext_ad h1 h2
  exact congrArg Prod.fst (θ.injective h3)

def PowCpt (b : FiniteAdeleRing (𝓞 L) L) : Prop :=
  ∃ C : Set (FiniteAdeleRing (𝓞 L) L), IsCompact C ∧ ∀ n : ℕ, b ^ n ∈ C

theorem pow_apply' (b : FiniteAdeleRing (𝓞 L) L) (v : HeightOneSpectrum (𝓞 L)) (n : ℕ) :
    (b ^ n) v = (b v) ^ n :=
  map_pow (finAdeleEval (𝓞 L) L v) b n

theorem powCpt_iff (b : FiniteAdeleRing (𝓞 L) L) : PowCpt b ↔ b ∈ integralFiniteAdeles (𝓞 L) L := by
  constructor
  · rintro ⟨C, hC, hn⟩ v
    have hcont : Continuous fun c : FiniteAdeleRing (𝓞 L) L => c v := continuous_finAdeleEval (𝓞 L) L v
    obtain ⟨M, hM⟩ := (hC.image hcont).exists_bound_of_continuousOn continuous_id.continuousOn
    have hbound : ∀ n : ℕ, ‖b v‖ ^ n ≤ M := by
      intro n
      have h1 := hM _ ⟨_, hn n, rfl⟩
      simp only [id] at h1
      rw [pow_apply', norm_pow] at h1
      exact h1
    have hle : ‖b v‖ ≤ 1 := by
      by_contra hlt
      push Not at hlt
      obtain ⟨n, hn'⟩ := pow_unbounded_of_one_lt M hlt
      exact absurd (hbound n) (not_le.mpr hn')
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (Valued.toNormedField.norm_le_one_iff.mp hle)
  · intro hb
    refine ⟨integralFiniteAdeles (𝓞 L) L, isCompact_integralFiniteAdeles', fun n v => ?_⟩
    rw [pow_apply']
    exact pow_mem (hb v) n

include hθ hθ' in
theorem thetaFin_mem_integral {b : FiniteAdeleRing (𝓞 L) L} (hb : b ∈ integralFiniteAdeles (𝓞 L) L) :
    thetaFin θ hθ' b ∈ integralFiniteAdeles (𝓞 L) L := by
  rw [← powCpt_iff] at hb ⊢
  obtain ⟨C, hC, hn⟩ := hb
  refine ⟨thetaFin θ hθ' '' C, hC.image (continuous_thetaFin θ hθ hθ'), fun n => ⟨_, hn n, ?_⟩⟩
  rw [map_pow]

end Decomposition

section Permutation

open scoped Classical

variable {L : Type} [Field L] [NumberField L]
variable (T : InfiniteAdeleRing L →+* InfiniteAdeleRing L) (hT : Continuous T) (hTinj : Function.Injective T)

theorem ia_add_apply (x y : InfiniteAdeleRing L) (u : InfinitePlace L) : (x + y) u = x u + y u := rfl
theorem ia_mul_apply (x y : InfiniteAdeleRing L) (u : InfinitePlace L) : (x * y) u = x u * y u := rfl
theorem ia_sub_apply (x y : InfiniteAdeleRing L) (u : InfinitePlace L) : (x - y) u = x u - y u := rfl
theorem ia_one_apply (u : InfinitePlace L) : (1 : InfiniteAdeleRing L) u = 1 := rfl
theorem ia_zero_apply (u : InfinitePlace L) : (0 : InfiniteAdeleRing L) u = 0 := rfl
theorem ia_sum_apply {ι : Type*} (s : Finset ι) (f : ι → InfiniteAdeleRing L) (u : InfinitePlace L) :
    (∑ i ∈ s, f i) u = ∑ i ∈ s, f i u :=
  map_sum (archEval L u) f s

def sing (w : InfinitePlace L) (y : w.Completion) : InfiniteAdeleRing L := Pi.single w y

theorem sing_apply_same (w : InfinitePlace L) (y : w.Completion) : sing w y w = y := by
  unfold sing; exact Pi.single_eq_same w y

theorem sing_apply_of_ne {w u : InfinitePlace L} (h : u ≠ w) (y : w.Completion) : sing w y u = 0 := by
  unfold sing; exact Pi.single_eq_of_ne h y

theorem sing_mul (w : InfinitePlace L) (y y' : w.Completion) : sing w (y * y') = sing w y * sing w y' := by
  funext u
  rw [ia_mul_apply]
  by_cases h : u = w
  · subst h; rw [sing_apply_same, sing_apply_same, sing_apply_same]
  · rw [sing_apply_of_ne h, sing_apply_of_ne h, sing_apply_of_ne h, mul_zero]

theorem sing_add (w : InfinitePlace L) (y y' : w.Completion) : sing w (y + y') = sing w y + sing w y' := by
  funext u
  rw [ia_add_apply]
  by_cases h : u = w
  · subst h; rw [sing_apply_same, sing_apply_same, sing_apply_same]
  · rw [sing_apply_of_ne h, sing_apply_of_ne h, sing_apply_of_ne h, add_zero]

theorem sing_zero (w : InfinitePlace L) : sing w (0 : w.Completion) = 0 := by
  funext u
  rw [ia_zero_apply]
  by_cases h : u = w
  · subst h; rw [sing_apply_same]
  · rw [sing_apply_of_ne h]

theorem continuous_sing (w : InfinitePlace L) : Continuous (sing w : w.Completion → InfiniteAdeleRing L) := by
  unfold sing
  exact (continuous_single w : Continuous fun y : w.Completion =>
    (Pi.single w y : ∀ u : InfinitePlace L, u.Completion))

def e (w : InfinitePlace L) : InfiniteAdeleRing L := sing w 1

theorem e_apply_same (w : InfinitePlace L) : e w w = 1 := sing_apply_same w 1

theorem e_apply_of_ne {w u : InfinitePlace L} (h : u ≠ w) : e w u = 0 := sing_apply_of_ne h 1

theorem e_mul_e_of_ne {w w' : InfinitePlace L} (h : w ≠ w') : e w * e w' = 0 := by
  funext u
  rw [ia_mul_apply, ia_zero_apply]
  by_cases hu : u = w
  · subst hu; rw [e_apply_of_ne h, mul_zero]
  · rw [e_apply_of_ne hu, zero_mul]

theorem e_mul_self (w : InfinitePlace L) : e w * e w = e w := by
  funext u
  rw [ia_mul_apply]
  by_cases hu : u = w
  · subst hu; rw [e_apply_same, mul_one]
  · rw [e_apply_of_ne hu, mul_zero]

theorem sum_e : ∑ w : InfinitePlace L, e w = 1 := by
  funext u
  rw [ia_sum_apply, ia_one_apply, Finset.sum_eq_single u (fun w _ hw => e_apply_of_ne (Ne.symm hw))
    (fun h => absurd (Finset.mem_univ u) h), e_apply_same]

theorem e_mul_eq_sing (w : InfinitePlace L) (x : InfiniteAdeleRing L) : e w * x = sing w (x w) := by
  funext u
  rw [ia_mul_apply]
  by_cases hu : u = w
  · subst hu; rw [e_apply_same, one_mul, sing_apply_same]
  · rw [e_apply_of_ne hu, zero_mul, sing_apply_of_ne hu]

theorem eq_zero_or_one_of_mul_self {F : Type*} [Field F] {x : F} (h : x * x = x) : x = 0 ∨ x = 1 := by
  have : x * (x - 1) = 0 := by rw [mul_sub, mul_one, h, sub_self]
  rcases mul_eq_zero.mp this with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (sub_eq_zero.mp h1)

theorem T_e_apply_eq_zero_or_one (w u : InfinitePlace L) : T (e w) u = 0 ∨ T (e w) u = 1 := by
  apply eq_zero_or_one_of_mul_self
  rw [← ia_mul_apply, ← map_mul, e_mul_self]

theorem existsUnique_T_e_eq_one (u : InfinitePlace L) : ∃! w : InfinitePlace L, T (e w) u = 1 := by
  have hsum : ∑ w : InfinitePlace L, T (e w) u = 1 := by
    rw [← ia_sum_apply, ← map_sum, sum_e, map_one, ia_one_apply]
  have hex : ∃ w, T (e w) u = 1 := by
    by_contra hne
    push Not at hne
    have h0 : ∀ w, T (e w) u = 0 := fun w =>
      (T_e_apply_eq_zero_or_one T w u).resolve_right (hne w)
    rw [Finset.sum_eq_zero (fun w _ => h0 w)] at hsum
    exact zero_ne_one hsum
  obtain ⟨w, hw⟩ := hex
  refine ⟨w, hw, fun w' hw' => ?_⟩
  by_contra hne
  have hprod : T (e w') * T (e w) = 0 := by rw [← map_mul, e_mul_e_of_ne hne, map_zero]
  have := congrArg (fun y : InfiniteAdeleRing L => y u) hprod
  rw [ia_mul_apply, ia_zero_apply, hw, hw', mul_one] at this
  exact one_ne_zero this

def rho (u : InfinitePlace L) : InfinitePlace L := (existsUnique_T_e_eq_one T u).choose

theorem T_e_rho (u : InfinitePlace L) : T (e (rho T u)) u = 1 := (existsUnique_T_e_eq_one T u).choose_spec.1

theorem rho_eq_of {u w : InfinitePlace L} (h : T (e w) u = 1) : rho T u = w :=
  (existsUnique_T_e_eq_one T u).unique (T_e_rho T u) h

theorem T_e_apply_of_ne {w u : InfinitePlace L} (h : rho T u ≠ w) : T (e w) u = 0 := by
  rcases T_e_apply_eq_zero_or_one T w u with h0 | h1
  · exact h0
  · exact absurd (rho_eq_of T h1) h

include hTinj in
theorem rho_bijective : Function.Bijective (rho T) := by
  have hsurj : Function.Surjective (rho T) := by
    intro w
    have hne : T (e w) ≠ 0 := by
      intro h0
      have h1 : e w = 0 := hTinj (by rw [h0, map_zero])
      have h2 := congrArg (fun y : InfiniteAdeleRing L => y w) h1
      rw [e_apply_same, ia_zero_apply] at h2
      exact one_ne_zero h2
    have hex : ∃ u, T (e w) u ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hne (funext hall)
    obtain ⟨u, hu⟩ := hex
    exact ⟨u, rho_eq_of T ((T_e_apply_eq_zero_or_one T w u).resolve_left hu)⟩
  exact ⟨Finite.injective_iff_surjective.mpr hsurj, hsurj⟩

def phi (u : InfinitePlace L) : (rho T u).Completion →+* u.Completion where
  toFun y := T (sing (rho T u) y) u
  map_one' := T_e_rho T u
  map_mul' y y' := by
    show T (sing (rho T u) (y * y')) u = T (sing (rho T u) y) u * T (sing (rho T u) y') u
    rw [sing_mul, map_mul, ia_mul_apply]
  map_zero' := by
    show T (sing (rho T u) 0) u = 0
    rw [sing_zero, map_zero, ia_zero_apply]
  map_add' y y' := by
    show T (sing (rho T u) (y + y')) u = T (sing (rho T u) y) u + T (sing (rho T u) y') u
    rw [sing_add, map_add, ia_add_apply]

theorem phi_apply (u : InfinitePlace L) (y : (rho T u).Completion) : phi T u y = T (sing (rho T u) y) u := rfl

include hT in
theorem continuous_phi (u : InfinitePlace L) : Continuous (phi T u) := by
  show Continuous fun y : (rho T u).Completion => T (sing (rho T u) y) u
  exact (continuous_archEval L u).comp (hT.comp (continuous_sing (rho T u)))

theorem T_apply (x : InfiniteAdeleRing L) (u : InfinitePlace L) : T x u = phi T u (x (rho T u)) := by
  have hsplit : x = e (rho T u) * x + (1 - e (rho T u)) * x := by ring
  have h2 : (T ((1 - e (rho T u)) * x)) u = 0 := by
    rw [map_mul, map_sub, map_one, ia_mul_apply, ia_sub_apply, ia_one_apply, T_e_rho, sub_self, zero_mul]
  conv_lhs => rw [hsplit, map_add]
  rw [ia_add_apply, h2, add_zero, e_mul_eq_sing]
  rfl

include hT in
theorem norm_phi (u : InfinitePlace L) (y : (rho T u).Completion) : ‖phi T u y‖ = ‖y‖ :=
  norm_map_eq_of_continuous (phi T u) (continuous_phi T hT u) y

include hTinj in

theorem isReal_rho_iff (u : InfinitePlace L) : (rho T u).IsReal ↔ u.IsReal := by
  have himp : ∀ u, u.IsReal → (rho T u).IsReal := fun u hu => isReal_of_ringHom (phi T u) hu
  refine ⟨fun h => ?_, himp u⟩
  set R : Finset (InfinitePlace L) := Finset.univ.filter fun u => u.IsReal with hR
  set S : Finset (InfinitePlace L) := Finset.univ.filter fun u => (rho T u).IsReal with hS
  have hRS : R ⊆ S := by
    intro u hu
    simp only [hR, hS, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
    exact himp u hu
  have hcard : S.card ≤ R.card := by
    have h1 : S.card = (S.image (rho T)).card :=
      (Finset.card_image_of_injective S (rho_bijective T hTinj).1).symm
    rw [h1]
    refine Finset.card_le_card ?_
    intro w hw
    simp only [Finset.mem_image, hS, hR, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    obtain ⟨u', hu', rfl⟩ := hw
    exact hu'
  have hEq : R = S := Finset.eq_of_subset_of_card_le hRS hcard
  have huS : u ∈ S := by simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]; exact h
  rw [← hEq] at huS
  simpa [hR] using huS

include hTinj in
theorem mult_rho (u : InfinitePlace L) : (rho T u).mult = u.mult := by
  unfold InfinitePlace.mult
  rw [if_congr (isReal_rho_iff T hTinj u) rfl rfl]

end Permutation

section Heights

open AutomorphicForm.WindowedSiegel

variable {A B : Type*} [NormedField A] [NormedField B]

theorem localHeight_map (φ : A →+* B) (hφ : ∀ y, ‖φ y‖ = ‖y‖) (g : GL (Fin 2) A) :
    localHeight (Matrix.GeneralLinearGroup.map φ g) = localHeight g := by
  unfold localHeight rowNormSq
  have hcoe : ((Matrix.GeneralLinearGroup.map φ g : GL (Fin 2) B) : Matrix (Fin 2) (Fin 2) B) =
      φ.mapMatrix (g : Matrix (Fin 2) (Fin 2) A) := rfl
  rw [hcoe, ← RingHom.map_det, hφ]
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, hφ]

end Heights

section Main

open AutomorphicForm.WindowedSiegel

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]

theorem main (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (g : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
    archHeight L (glArch (𝓞 L) L (AutomorphicForm.sigmaAdelicAct K L D σ g)) =
      archHeight L (glArch (𝓞 L) L g) ∧
    (glFin (𝓞 L) L g ∈ finiteIntegralGL2 (𝓞 L) L →
      glFin (𝓞 L) L (AutomorphicForm.sigmaAdelicAct K L D σ g) ∈ finiteIntegralGL2 (𝓞 L) L) := by
  classical

  set θ : AdeleRing (𝓞 L) L ≃+* AdeleRing (𝓞 L) L := (D.act σ : RingAut (AdeleRing (𝓞 L) L)) with hθdef
  have hθ : Continuous θ := D.continuous_act σ
  have hθ' : Continuous θ.symm := by
    have h : Continuous (D.act σ⁻¹ : RingAut (AdeleRing (𝓞 L) L)) := D.continuous_act σ⁻¹
    have heq : (θ.symm : AdeleRing (𝓞 L) L → AdeleRing (𝓞 L) L) = (D.act σ⁻¹ : RingAut (AdeleRing (𝓞 L) L)) := by
      funext a; rw [map_inv]; rfl
    rw [heq]; exact h
  have hentry : ∀ i j, ((AutomorphicForm.sigmaAdelicAct K L D σ g : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
      Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j = θ ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j) :=
    fun i j => rfl
  have hentry' : ∀ i j, (((AutomorphicForm.sigmaAdelicAct K L D σ g)⁻¹ : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
      Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j =
      θ (((g⁻¹ : AutomorphicForm.AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j) := by
    intro i j; rw [← map_inv]; rfl
  set T := thetaInf θ hθ with hTdef
  have hT : Continuous T := continuous_thetaInf θ hθ
  have hTinj : Function.Injective T := thetaInf_injective θ hθ hθ'
  refine ⟨?_, ?_⟩
  ·
    have hcomp : ∀ u : InfinitePlace L,
        archComponent L u (glArch (𝓞 L) L (AutomorphicForm.sigmaAdelicAct K L D σ g)) =
          Matrix.GeneralLinearGroup.map (phi T u) (archComponent L (rho T u) (glArch (𝓞 L) L g)) := by
      intro u
      apply Units.ext
      ext i j : 1
      show (((AutomorphicForm.sigmaAdelicAct K L D σ g : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j).1 u =
        phi T u ((((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j).1) (rho T u))
      rw [hentry, map_fst θ hθ hθ', ← hTdef, T_apply]
    unfold archHeight
    simp_rw [hcomp, localHeight_map (phi T _) (norm_phi T hT _)]

    set τ : InfinitePlace L ≃ InfinitePlace L := Equiv.ofBijective (rho T) (rho_bijective T hTinj) with hτ
    calc ∏ u : InfinitePlace L, localHeight (archComponent L (rho T u) (glArch (𝓞 L) L g)) ^ u.mult
        = ∏ u : InfinitePlace L, localHeight (archComponent L (τ u) (glArch (𝓞 L) L g)) ^ (τ u).mult := by
          refine Finset.prod_congr rfl fun u _ => ?_
          rw [show τ u = rho T u from rfl, mult_rho T hTinj u]
      _ = ∏ w : InfinitePlace L, localHeight (archComponent L w (glArch (𝓞 L) L g)) ^ w.mult :=
          Equiv.prod_comp τ (fun w => localHeight (archComponent L w (glArch (𝓞 L) L g)) ^ w.mult)
  ·
    intro hg
    rw [mem_finiteIntegralGL2_iff] at hg ⊢
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · show (((AutomorphicForm.sigmaAdelicAct K L D σ g : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j).2 ∈ integralFiniteAdeles (𝓞 L) L
      rw [hentry, map_snd θ hθ hθ']
      exact thetaFin_mem_integral θ hθ hθ' (hg.1 i j)
    · show ((((AutomorphicForm.sigmaAdelicAct K L D σ g)⁻¹ : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j).2 ∈ integralFiniteAdeles (𝓞 L) L
      rw [hentry', map_snd θ hθ hθ']
      exact thetaFin_mem_integral θ hθ hθ' (hg.2 i j)

end Main

end R3HGT
p2m_reactivate "P2MW.S_AutomorphicForm_archHeight_glArch_sigmaAdelicAct_and_glFin_sigmaAdelicAct_mem_finiteIntegralGL2.R3HGT"

end
p2m_reactivate "P2MW.S_AutomorphicForm_archHeight_glArch_sigmaAdelicAct_and_glFin_sigmaAdelicAct_mem_finiteIntegralGL2.R3HGT"

open NumberField in
theorem solution
    (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (g : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
    AutomorphicForm.WindowedSiegel.archHeight L
        (NumberField.AdelicLevel.glArch (𝓞 L) L (AutomorphicForm.sigmaAdelicAct K L D σ g)) =
      AutomorphicForm.WindowedSiegel.archHeight L (NumberField.AdelicLevel.glArch (𝓞 L) L g) ∧
    (NumberField.AdelicLevel.glFin (𝓞 L) L g ∈ NumberField.AdelicLevel.finiteIntegralGL2 (𝓞 L) L →
      NumberField.AdelicLevel.glFin (𝓞 L) L (AutomorphicForm.sigmaAdelicAct K L D σ g) ∈
        NumberField.AdelicLevel.finiteIntegralGL2 (𝓞 L) L) :=
  R3HGT.main K L D σ g

end S_AutomorphicForm_archHeight_glArch_sigmaAdelicAct_and_glFin_sigmaAdelicAct_mem_finiteIntegralGL2
end P2MW
export P2MW.S_AutomorphicForm_archHeight_glArch_sigmaAdelicAct_and_glFin_sigmaAdelicAct_mem_finiteIntegralGL2 (solution)
