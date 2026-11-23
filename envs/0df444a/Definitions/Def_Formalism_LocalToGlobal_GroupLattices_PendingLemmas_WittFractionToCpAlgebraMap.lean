-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_GroupLattices_PendingLemmas_WittFractionToCpAlgebraMap
-- name    : Formalism_LocalToGlobal_GroupLattices_PendingLemmas_WittFractionToCpAlgebraMap
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:26:35.351007+00:00
-- url     : https://prove2.me/theorems/1a8b4442-10db-47fd-b498-6d094e6ef5d2
-- title:
--   Witt Fraction To Cp Algebra Map
-- statement:
--   Definitions and structural lemmas for Witt Fraction To Cp Algebra Map, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/PendingLemmas/WittFractionToCpAlgebraMap.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_PerfectRings_IsLocalRingOfComplete
import Definitions.Def_Lemmata_FirstBlockLemmaF_Imports
import Definitions.Def_Lemmata_GeneralBFactThird_Imports
import Theorems.Thm_Bl_FirstBlockLemmaF_goal1
import Theorems.Thm_Bl_general_b_fact_third_goal1
import Theorems.Thm_Formalism_L2_G_IntCl_frac

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial IsLocalRing Filter Topology
noncomputable section
namespace Formalism.L2.G.Pend
variable (p : ℕ) [hp : Fact p.Prime]
abbrev kb : Type := AlgebraicClosure (ZMod p)
abbrev WW : Type := WittVector p (kb p)
abbrev K0 : Type := FractionRing (WW p)
def zW : ℤ_[p] →+* WW p :=
  (WittVector.map (algebraMap (ZMod p) (kb p))).comp (WittVector.equiv p).symm.toRingHom
theorem zW_injective : Function.Injective (zW p) :=
  (WittVector.map_injective _ (algebraMap (ZMod p) (kb p)).injective).comp (WittVector.equiv p).symm.injective
def zK : ℤ_[p] →+* K0 p := (algebraMap (WW p) (K0 p)).comp (zW p)
theorem zK_injective : Function.Injective (zK p) :=
  (IsFractionRing.injective (WW p) (K0 p)).comp (zW_injective p)
def qK : ℚ_[p] →+* K0 p := IsFractionRing.lift (zK_injective p)
theorem qK_alg (x : ℤ_[p]) : qK p (algebraMap ℤ_[p] ℚ_[p] x) = zK p x :=
  IsFractionRing.lift_algebraMap (zK_injective p) x
@[reducible] def algZW : Algebra ℤ_[p] (WW p) := (zW p).toAlgebra
@[reducible] def algQK : Algebra ℚ_[p] (K0 p) := (qK p).toAlgebra
attribute [local instance] algZW algQK
theorem algZK_apply (x : ℤ_[p]) : algebraMap ℤ_[p] (K0 p) x = zK p x :=
  IsScalarTower.algebraMap_apply ℤ_[p] (WW p) (K0 p) x
local instance towerZQK : IsScalarTower ℤ_[p] ℚ_[p] (K0 p) :=
  IsScalarTower.of_algebraMap_eq fun x => by
    rw [algZK_apply]
    exact (qK_alg p x).symm
theorem p_ne_zero_alt : (p : WW p) ≠ 0 := (WittVector.irreducible p).ne_zero
theorem p_ne_zero_K : (p : K0 p) ≠ 0 := by
  rw [← map_natCast (algebraMap (WW p) (K0 p))]
  exact fun h => p_ne_zero_alt p ((IsFractionRing.injective (WW p) (K0 p)) (h.trans (map_zero _).symm))
theorem integral_of_alg (b : WW p) (hb : IsAlgebraic ℚ_[p] (algebraMap (WW p) (K0 p) b)) :
    IsIntegral ℤ_[p] (algebraMap (WW p) (K0 p) b) := by
  set β := algebraMap (WW p) (K0 p) b with hβ
  by_cases h0 : β = 0
  · rw [h0]; exact isIntegral_zero
  let L : IntermediateField ℚ_[p] (K0 p) := IntermediateField.adjoin ℚ_[p] {β}
  have : FiniteDimensional ℚ_[p] L := IntermediateField.adjoin.finiteDimensional hb.isIntegral
  have hD : IsDiscreteValuationRing (integralClosure ℤ_[p] L) := IntCl.isDVR ℤ_[p] ℚ_[p] L inferInstance
  have : IsFractionRing (integralClosure ℤ_[p] L) L := IntCl.frac ℤ_[p] ℚ_[p] L
  let g : L := IntermediateField.AdjoinSimple.gen ℚ_[p] β
  have hg : (g : K0 p) = β := IntermediateField.AdjoinSimple.coe_gen ℚ_[p] β
  let ρ : integralClosure ℤ_[p] L →+* K0 p := (algebraMap L (K0 p)).comp (algebraMap (integralClosure ℤ_[p] L) L)
  have : IsScalarTower ℤ_[p] L (K0 p) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have key : ∀ c : integralClosure ℤ_[p] L, IsIntegral ℤ_[p] (ρ c) := fun c =>
    (c.2 : IsIntegral ℤ_[p] (c : L)).map (IsScalarTower.toAlgHom ℤ_[p] L (K0 p))
  rcases ValuationRing.isInteger_or_isInteger (integralClosure ℤ_[p] L) g with ⟨c, hc⟩ | ⟨c, hc⟩
  · have : ρ c = β := by rw [← hg, ← hc]; rfl
    rw [← this]; exact key c
  · have hρc : ρ c = β⁻¹ := by
      have : ρ c = algebraMap L (K0 p) (g⁻¹) := by rw [← hc]; rfl
      rw [this, map_inv₀]
      exact congrArg _ hg
    by_cases hu : IsUnit c
    · obtain ⟨u, rfl⟩ := hu
      have : ρ ((u⁻¹ : (integralClosure ℤ_[p] L)ˣ) : integralClosure ℤ_[p] L) = β := by
        rw [map_units_inv, hρc, inv_inv]
      rw [← this]; exact key _
    · exfalso
      obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (integralClosure ℤ_[p] L)
      have hp0 : ((p : ℕ) : integralClosure ℤ_[p] L) ≠ 0 := by
        intro h
        have := congrArg ρ h
        rw [map_natCast, map_zero] at this
        exact p_ne_zero_K p this
      obtain ⟨e, u, hpe⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hp0 hϖ
      have hcm : c ∈ maximalIdeal (integralClosure ℤ_[p] L) := (mem_maximalIdeal c).2 hu
      rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hcm
      obtain ⟨d, rfl⟩ := hcm
      have hz : (ϖ * d) ^ e = ((p : ℕ) : integralClosure ℤ_[p] L) * (((u⁻¹ : (integralClosure ℤ_[p] L)ˣ) :
          integralClosure ℤ_[p] L) * d ^ e) := by
        rw [hpe, mul_pow]
        calc ϖ ^ e * d ^ e = ((u : integralClosure ℤ_[p] L) * ((u⁻¹ : (integralClosure ℤ_[p] L)ˣ) :
              integralClosure ℤ_[p] L)) * (ϖ ^ e * d ^ e) := by rw [Units.mul_inv, one_mul]
          _ = _ := by ring
      have hζ : IsIntegral (WW p) (ρ (((u⁻¹ : (integralClosure ℤ_[p] L)ˣ) : integralClosure ℤ_[p] L) * d ^ e)) :=
        (key _).tower_top
      obtain ⟨z', hz'⟩ := IsIntegrallyClosed.isIntegral_iff.1 hζ
      have h1 := congrArg ρ hz
      rw [map_pow, hρc, map_mul, map_natCast, ← hz', ← map_natCast (algebraMap (WW p) (K0 p)), ← map_mul] at h1
      have h2 : algebraMap (WW p) (K0 p) (b ^ e * ((p : WW p) * z')) = 1 := by
        rw [map_mul, ← h1, map_pow, ← hβ, inv_pow, mul_inv_cancel₀ (pow_ne_zero _ h0)]
      have h3 : b ^ e * ((p : WW p) * z') = 1 :=
        IsFractionRing.injective (WW p) (K0 p) (h2.trans (map_one _).symm)
      have h4 : (p : WW p) * (b ^ e * z') = 1 := by rw [← h3]; ring
      exact (WittVector.irreducible p).not_isUnit (IsUnit.of_mul_eq_one _ h4)
theorem norm_le_one_of_root {K : Type*} [NormedField K] [IsUltrametricDist K] (P : K[X]) (hm : P.Monic)
    (hc : ∀ i, ‖P.coeff i‖ ≤ 1) (x : K) (hx : P.eval x = 0) : ‖x‖ ≤ 1 := by
  first | exact Bl.general_b_fact_third.goal1 .. | (apply Bl.general_b_fact_third.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_third.goal1 <;> assumption) | (apply @Bl.general_b_fact_third.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_third.goal1 <;> assumption) | (apply @Bl.general_b_fact_third.goal1 <;> first | assumption | infer_instance) | exact @Bl.general_b_fact_third.goal1 K ‹_› ‹_› P hm hc x hx | exact @Bl.general_b_fact_third.goal1 K ‹_› ‹_› P hm hc x | exact @Bl.general_b_fact_third.goal1 K ‹_› ‹_› P hm hc | exact @Bl.general_b_fact_third.goal1 K ‹_› ‹_› P hm | exact @Bl.general_b_fact_third.goal1 K ‹_› ‹_› P | exact @Bl.general_b_fact_third.goal1 K ‹_› ‹_› | exact @Bl.general_b_fact_third.goal1 K ‹_› | exact @Bl.general_b_fact_third.goal1 K
abbrev Kalg : IntermediateField ℚ_[p] (K0 p) := algebraicClosure ℚ_[p] (K0 p)
def phi : Kalg p →ₐ[ℚ_[p]] ℂ_[p] := IsAlgClosed.lift
theorem norm_p_C : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
  have h := PadicComplex.norm_extends' p (p : ℚ_[p])
  rw [Padic.norm_p] at h
  rw [← h]
  congr 1
  simp
theorem norm_phi_le (z : Kalg p) (b : WW p) (h : (z : K0 p) = algebraMap (WW p) (K0 p) b) : ‖phi p z‖ ≤ 1 := by
  have hi : IsIntegral ℤ_[p] (algebraMap (WW p) (K0 p) b) :=
    integral_of_alg p b (by rw [← h]; exact mem_algebraicClosure_iff.1 z.2)
  obtain ⟨P, hm, he⟩ := hi
  let f' : ℤ_[p] →+* Kalg p := (algebraMap ℚ_[p] (Kalg p)).comp (algebraMap ℤ_[p] ℚ_[p])
  let f : ℤ_[p] →+* ℂ_[p] := (algebraMap ℚ_[p] ℂ_[p]).comp (algebraMap ℤ_[p] ℚ_[p])
  have e1 : (algebraMap (Kalg p) (K0 p)).comp f' = algebraMap ℤ_[p] (K0 p) := by
    ext x
    exact (IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] (K0 p) x).symm
  have e2 : eval₂ f' z P = 0 := by
    apply (algebraMap (Kalg p) (K0 p)).injective
    rw [hom_eval₂, e1, map_zero]
    have : algebraMap (Kalg p) (K0 p) z = algebraMap (WW p) (K0 p) b := h
    rw [this]; exact he
  have e3 : ((phi p : Kalg p →+* ℂ_[p])).comp f' = f := by
    ext x
    exact (phi p).commutes _
  have e4 : eval₂ f (phi p z) P = 0 := by
    have := congrArg (phi p : Kalg p →+* ℂ_[p]) e2
    rw [hom_eval₂, e3, map_zero] at this
    exact this
  refine norm_le_one_of_root (P.map f) (hm.map f) (fun i => ?_) _ (by rw [eval_map]; exact e4)
  rw [coeff_map]
  have : ‖f (P.coeff i)‖ = ‖((P.coeff i : ℤ_[p]) : ℚ_[p])‖ := PadicComplex.norm_extends' p _
  rw [this]
  exact PadicInt.norm_le_one _
theorem norm_phi_pow (N : ℕ) (z : Kalg p) (b : WW p)
    (h : (z : K0 p) = algebraMap (WW p) (K0 p) ((p : WW p) ^ N * b)) : ‖phi p z‖ ≤ ((p : ℝ)⁻¹) ^ N := by
  have hpK : ((p : ℕ) : Kalg p) ≠ 0 := by
    intro h0
    have := congrArg (algebraMap (Kalg p) (K0 p)) h0
    rw [map_natCast, map_zero] at this
    exact p_ne_zero_K p this
  let z' : Kalg p := z * (((p : ℕ) : Kalg p) ^ N)⁻¹
  have hz : z = ((p : ℕ) : Kalg p) ^ N * z' := by
    simp only [z']
    field_simp
  have hz' : (z' : K0 p) = algebraMap (WW p) (K0 p) b := by
    have h1 : algebraMap (Kalg p) (K0 p) z = algebraMap (Kalg p) (K0 p) (((p : ℕ) : Kalg p) ^ N * z') :=
      congrArg _ hz
    rw [map_mul, map_pow, map_natCast] at h1
    have h2 : algebraMap (Kalg p) (K0 p) z = (p : K0 p) ^ N * algebraMap (WW p) (K0 p) b := by
      rw [← map_natCast (algebraMap (WW p) (K0 p)), ← map_pow, ← map_mul]; exact h
    rw [h2] at h1
    exact (mul_left_cancel₀ (pow_ne_zero N (p_ne_zero_K p)) h1).symm
  rw [hz, map_mul, map_pow, map_natCast, norm_mul, norm_pow, norm_p_C]
  exact mul_le_of_le_one_right (by positivity) (norm_phi_le p z' b hz')
theorem id_mul {R : Type*} [CommRing R] (x x' b b' π : R) :
    (x + π * b) * (x' + π * b') = x * x' + π * (b * x' + x * b' + π * b * b') := by ring
theorem id_add {R : Type*} [CommRing R] (x x' b b' π : R) :
    (x + π * b) + (x' + π * b') = x + x' + π * (b + b') := by ring
theorem id_sub {R : Type*} [CommRing R] (x b b' π : R) (N k : ℕ) :
    (x + π ^ N * b) - (x + π ^ (N + k) * b') = π ^ N * (b - π ^ k * b') := by ring
theorem id_app {R : Type*} [CommRing R] (x S c π : R) (N : ℕ) (h : x - S = π ^ (N + 1) * c) :
    S = x + π ^ N * -(π * c) := by
  have : S = x - π ^ (N + 1) * c := by rw [← h]; ring
  rw [this]; ring
def Approx (N : ℕ) (x : WW p) (z : Kalg p) : Prop :=
  ∃ b : WW p, (z : K0 p) = algebraMap (WW p) (K0 p) (x + (p : WW p) ^ N * b)
theorem exists_pow_eq (y : kb p) : ∃ q : ℕ, 1 < q ∧ y ^ q = y := by
  have hy : IsIntegral (ZMod p) y := Algebra.IsIntegral.isIntegral y
  let F := IntermediateField.adjoin (ZMod p) {y}
  have : FiniteDimensional (ZMod p) F := IntermediateField.adjoin.finiteDimensional hy
  have : Finite F := Module.finite_of_finite (ZMod p)
  have := Fintype.ofFinite F
  refine ⟨Fintype.card F, Fintype.one_lt_card, ?_⟩
  have h1 := FiniteField.pow_card (IntermediateField.AdjoinSimple.gen (ZMod p) y)
  have h2 := congrArg (Subtype.val) h1
  simpa using h2
theorem teich_mem (y : kb p) : algebraMap (WW p) (K0 p) (WittVector.teichmuller p y) ∈ Kalg p := by
  obtain ⟨q, hq, hy⟩ := exists_pow_eq p y
  rw [mem_algebraicClosure_iff]
  refine ⟨X ^ q - X, FiniteField.X_pow_card_sub_X_ne_zero _ hq, ?_⟩
  rw [map_sub, map_pow, aeval_X, ← map_pow, ← map_pow, hy, sub_self]
theorem exists_approx (x : WW p) (N : ℕ) : ∃ z, Approx p N x z := by
  obtain ⟨c, hc⟩ := WittVector.dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff x N
  set S := ∑ i ∈ Finset.Iic N, (WittVector.teichmuller p
        (((_root_.frobeniusEquiv (kb p) p).symm ^ i) (x.coeff i)) * (p : WW p) ^ i) with hS
  have hmem : algebraMap (WW p) (K0 p) S ∈ Kalg p := by
    rw [hS, map_sum]
    refine sum_mem fun i _ => ?_
    rw [map_mul, map_pow, map_natCast]
    exact mul_mem (teich_mem p _) (pow_mem (natCast_mem _ p) i)
  exact ⟨⟨_, hmem⟩, -((p : WW p) * c), congrArg (algebraMap (WW p) (K0 p)) (id_app x S c (p : WW p) N hc)⟩
theorem nadd {a b : ℂ_[p]} {c : ℝ} (ha : ‖a‖ ≤ c) (hb : ‖b‖ ≤ c) : ‖a + b‖ ≤ c :=
  (PadicComplex.isNonarchimedean p a b).trans (max_le ha hb)
theorem nsub {a b : ℂ_[p]} {c : ℝ} (ha : ‖a‖ ≤ c) (hb : ‖b‖ ≤ c) : ‖a - b‖ ≤ c := by
  first | exact Bl.FirstBlockLemmaF.goal1 .. | (apply Bl.FirstBlockLemmaF.goal1 <;> assumption) | (intros; apply Bl.FirstBlockLemmaF.goal1 <;> assumption) | (apply @Bl.FirstBlockLemmaF.goal1 <;> assumption) | (intros; apply @Bl.FirstBlockLemmaF.goal1 <;> assumption) | (apply @Bl.FirstBlockLemmaF.goal1 <;> first | assumption | infer_instance) | exact @Bl.FirstBlockLemmaF.goal1 p hp a b c ha hb | exact @Bl.FirstBlockLemmaF.goal1 p hp a b c ha | exact @Bl.FirstBlockLemmaF.goal1 p hp a b c | exact @Bl.FirstBlockLemmaF.goal1 p hp a b | exact @Bl.FirstBlockLemmaF.goal1 p hp a | exact @Bl.FirstBlockLemmaF.goal1 p hp | exact @Bl.FirstBlockLemmaF.goal1 p
theorem approx_close {N M : ℕ} (hNM : N ≤ M) {x : WW p} {z z' : Kalg p} (h : Approx p N x z)
    (h' : Approx p M x z') : ‖phi p z - phi p z'‖ ≤ ((p : ℝ)⁻¹) ^ N := by
  obtain ⟨b, hb⟩ := h
  obtain ⟨b', hb'⟩ := h'
  rw [← map_sub]
  refine norm_phi_pow p N (z - z') (b - (p : WW p) ^ (M - N) * b') ?_
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hNM
  rw [AddSubgroupClass.coe_sub, hb, hb', ← map_sub, Nat.add_sub_cancel_left]
  exact congrArg _ (id_sub x b b' (p : WW p) N k)
theorem r_lt_one : ((p : ℝ)⁻¹) < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)
theorem r_nonneg : 0 ≤ ((p : ℝ)⁻¹) := by positivity
theorem exists_lim (x : WW p) :
    ∃ y : ℂ_[p], ∀ N z, Approx p N x z → ‖y - phi p z‖ ≤ ((p : ℝ)⁻¹) ^ N := by
  choose zs hzs using fun N => exists_approx p x N
  have hc : CauchySeq fun N => phi p (zs N) :=
    cauchySeq_of_le_geometric ((p : ℝ)⁻¹) 1 (r_lt_one p) fun n => by
      rw [dist_eq_norm, one_mul]
      exact approx_close p (Nat.le_succ n) (hzs n) (hzs (n + 1))
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨y, fun N z hz => ?_⟩
  refine le_of_tendsto ((hy.sub_const (phi p z)).norm) ?_
  filter_upwards [eventually_ge_atTop N] with M hM
  rw [norm_sub_rev]
  exact approx_close p hM hz (hzs M)
def wFun (x : WW p) : ℂ_[p] := Classical.choose (exists_lim p x)
theorem wFun_spec (x : WW p) {N : ℕ} {z : Kalg p} (h : Approx p N x z) :
    ‖wFun p x - phi p z‖ ≤ ((p : ℝ)⁻¹) ^ N := Classical.choose_spec (exists_lim p x) N z h
theorem eq_of_close {a b : ℂ_[p]} (h : ∀ N : ℕ, ‖a - b‖ ≤ ((p : ℝ)⁻¹) ^ N) : a = b := by
  have h0 : ‖a - b‖ ≤ 0 :=
    ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one (r_nonneg p) (r_lt_one p)) h
  exact sub_eq_zero.1 (norm_le_zero_iff.1 h0)
theorem wFun_eq {x : WW p} {y : ℂ_[p]}
    (h : ∀ N : ℕ, ∃ z, Approx p N x z ∧ ‖y - phi p z‖ ≤ ((p : ℝ)⁻¹) ^ N) : wFun p x = y := by
  refine eq_of_close p fun N => ?_
  obtain ⟨z, hz, hy⟩ := h N
  have : wFun p x - y = (wFun p x - phi p z) - (y - phi p z) := by ring
  rw [this]
  exact nsub p (wFun_spec p x hz) hy
theorem norm_phi_approx {N : ℕ} {x : WW p} {z : Kalg p} (h : Approx p N x z) : ‖phi p z‖ ≤ 1 := by
  obtain ⟨b, hb⟩ := h
  exact norm_phi_le p z _ hb
theorem norm_wFun_le (x : WW p) : ‖wFun p x‖ ≤ 1 := by
  obtain ⟨z, hz⟩ := exists_approx p x 0
  have h1 := wFun_spec p x hz
  rw [pow_zero] at h1
  have : wFun p x = (wFun p x - phi p z) + phi p z := by ring
  rw [this]
  exact nadd p h1 (norm_phi_approx p hz)
theorem wFun_alg (x : WW p) (z : Kalg p) (h : (z : K0 p) = algebraMap (WW p) (K0 p) x) : wFun p x = phi p z :=
  wFun_eq p fun N => ⟨z, ⟨0, by rw [h, mul_zero, add_zero]⟩, by rw [sub_self, norm_zero]; positivity⟩
def wToC : WW p →+* ℂ_[p] where
  toFun := wFun p
  map_one' := by
    rw [wFun_alg p 1 1 (by rw [map_one]; rfl), map_one]
  map_zero' := by
    rw [wFun_alg p 0 0 (by rw [map_zero]; rfl), map_zero]
  map_add' := fun x x' => wFun_eq p fun N => by
    obtain ⟨z, hz⟩ := exists_approx p x N
    obtain ⟨z', hz'⟩ := exists_approx p x' N
    refine ⟨z + z', ?_, ?_⟩
    · obtain ⟨b, hb⟩ := hz
      obtain ⟨b', hb'⟩ := hz'
      refine ⟨b + b', ?_⟩
      rw [IntermediateField.coe_add, hb, hb', ← map_add]
      exact congrArg _ (id_add x x' b b' ((p : WW p) ^ N))
    · have : wFun p x + wFun p x' - phi p (z + z') = (wFun p x - phi p z) + (wFun p x' - phi p z') := by
        rw [map_add]; ring
      rw [this]
      exact nadd p (wFun_spec p x hz) (wFun_spec p x' hz')
  map_mul' := fun x x' => wFun_eq p fun N => by
    obtain ⟨z, hz⟩ := exists_approx p x N
    obtain ⟨z', hz'⟩ := exists_approx p x' N
    refine ⟨z * z', ?_, ?_⟩
    · obtain ⟨b, hb⟩ := hz
      obtain ⟨b', hb'⟩ := hz'
      refine ⟨b * x' + x * b' + (p : WW p) ^ N * b * b', ?_⟩
      rw [IntermediateField.coe_mul, hb, hb', ← map_mul]
      exact congrArg _ (id_mul x x' b b' ((p : WW p) ^ N))
    · have : wFun p x * wFun p x' - phi p (z * z') =
          wFun p x * (wFun p x' - phi p z') + (wFun p x - phi p z) * phi p z' := by
        rw [map_mul]; ring
      rw [this]
      refine nadd p ?_ ?_
      · rw [norm_mul]
        exact (mul_le_of_le_one_left (norm_nonneg _) (norm_wFun_le p x)).trans (wFun_spec p x' hz')
      · rw [norm_mul]
        exact (mul_le_of_le_one_right (norm_nonneg _) (norm_phi_approx p hz')).trans (wFun_spec p x hz)
theorem wToC_injective : Function.Injective (wToC p) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra h0
  obtain ⟨m, b, hb, rfl⟩ := WittVector.exists_eq_pow_p_mul x h0
  have hu : IsUnit b := WittVector.isUnit_of_coeff_zero_ne_zero b hb
  rw [map_mul, map_pow, map_natCast] at hx
  have hpC : (p : ℂ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  exact (mul_ne_zero (pow_ne_zero m hpC) (hu.map (wToC p)).ne_zero) hx
def k0ToC : K0 p →+* ℂ_[p] := IsFractionRing.lift (wToC_injective p)
end Formalism.L2.G.Pend


