-- Prove2me | solution 1 for AlgebraicCurve.exists_dlog_of_cartierOperator_fixed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/2a01c698-aff8-5a09-9637-8d4ce20fa8fd

import Theorems.Thm_AlgebraicCurve_exists_D_ne_zero
import Theorems.Thm_AlgebraicCurve_pDigits_existsUnique
import Mathlib.NumberTheory.Wilson
import Theorems.Thm_Derivation_add_mulLeft_pow_char
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_dlog_of_cartierOperator_fixed

set_option autoImplicit false
universe u v

open KaehlerDifferential

namespace Star2C

variable {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F]

section coord
variable [AlgebraicCurve.IsCurveOver K F]

private lemma span_D_eq_top (t : F) (hdt : D K F t ≠ 0) :
    Submodule.span F {D K F t} = ⊤ := by
  have h1 : Module.finrank F Ω[F⁄K] = 1 := AlgebraicCurve.IsCurveOver.finrank_kaehler
  exact (finrank_eq_one_iff_of_nonzero (D K F t) hdt).mp h1

private lemma exists_coeff (t : F) (hdt : D K F t ≠ 0) (ω : Ω[F⁄K]) :
    ∃ c : F, ω = c • D K F t := by
  have hmem : ω ∈ Submodule.span F {D K F t} := by
    rw [span_D_eq_top (K := K) t hdt]; exact Submodule.mem_top
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  exact ⟨c, hc.symm⟩

omit [AlgebraicCurve.IsCurveOver K F] in
private lemma coeff_unique (t : F) (hdt : D K F t ≠ 0) {c₁ c₂ : F}
    (h : c₁ • D K F t = c₂ • D K F t) : c₁ = c₂ := by
  have h0 : (c₁ - c₂) • D K F t = 0 := by rw [sub_smul, h, sub_self]
  rcases smul_eq_zero.mp h0 with h' | h'
  · exact sub_eq_zero.mp h'
  · exact absurd h' hdt

private noncomputable def dcoord (t : F) (hdt : D K F t ≠ 0) (f : F) : F :=
  Classical.choose (exists_coeff (K := K) t hdt (D K F f))

private lemma dcoord_spec (t : F) (hdt : D K F t ≠ 0) (f : F) :
    D K F f = dcoord t hdt f • D K F t :=
  Classical.choose_spec (exists_coeff (K := K) t hdt (D K F f))

private lemma dcoord_self (t : F) (hdt : D K F t ≠ 0) : dcoord t hdt t = 1 :=
  coeff_unique t hdt ((dcoord_spec t hdt t).symm.trans (one_smul F (D K F t)).symm)

private lemma dcoord_add (t : F) (hdt : D K F t ≠ 0) (f g : F) :
    dcoord t hdt (f + g) = dcoord t hdt f + dcoord t hdt g := by
  apply coeff_unique t hdt
  rw [← dcoord_spec, map_add, dcoord_spec t hdt f, dcoord_spec t hdt g, add_smul]

private lemma dcoord_smul (t : F) (hdt : D K F t ≠ 0) (k : K) (f : F) :
    dcoord t hdt (k • f) = k • dcoord t hdt f := by
  apply coeff_unique t hdt
  rw [← dcoord_spec, Derivation.map_smul, dcoord_spec t hdt f, smul_assoc]

private lemma dcoord_leibniz (t : F) (hdt : D K F t ≠ 0) (f g : F) :
    dcoord t hdt (f * g) = f * dcoord t hdt g + g * dcoord t hdt f := by
  apply coeff_unique t hdt
  rw [← dcoord_spec, Derivation.leibniz, dcoord_spec t hdt f, dcoord_spec t hdt g,
    add_smul, smul_smul, smul_smul]

private noncomputable def dcoordD (t : F) (hdt : D K F t ≠ 0) : Derivation K F F :=
  { toLinearMap :=
      { toFun := dcoord t hdt
        map_add' := dcoord_add t hdt
        map_smul' := dcoord_smul t hdt }
    map_one_eq_zero' := by
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      apply coeff_unique t hdt
      rw [← dcoord_spec, Derivation.map_one_eq_zero, zero_smul]
    leibniz' := fun f g => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul]
      rw [dcoord_leibniz t hdt f g] }

private lemma dcoordD_apply (t : F) (hdt : D K F t ≠ 0) (f : F) :
    dcoordD t hdt f = dcoord t hdt f := rfl

end coord

section digits
variable (p : ℕ) [Fact p.Prime] [CharP F p] [AlgebraicCurve.IsCurveOver K F]

omit [CharP F p] in
private lemma dtlc_app (t : F) (hdt : D K F t ≠ 0) (f : F) :
    (dcoordD (K := K) t hdt).toLinearMap f = dcoordD (K := K) t hdt f := rfl

omit [CharP F p] [AlgebraicCurve.IsCurveOver K F] in
private lemma endo_mul_app (f g : F →ₗ[K] F) (x : F) : (f * g) x = f (g x) := rfl

omit [Fact p.Prime] in
private lemma dcoord_frob (t : F) (hdt : D K F t ≠ 0) (c : F) :
    dcoordD (K := K) t hdt (c ^ p) = 0 := by
  rw [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul F, CharP.cast_eq_zero, zero_smul]

omit [CharP F p] in
private lemma dcoord_t_pow (t : F) (hdt : D K F t ≠ 0) (i : ℕ) :
    dcoordD (K := K) t hdt (t ^ i) = i • t ^ (i - 1) := by
  rw [Derivation.leibniz_pow, show dcoordD (K := K) t hdt t = 1 from dcoord_self t hdt,
    smul_eq_mul, mul_one]

omit [Fact p.Prime] in
private lemma dcoord_digit (t : F) (hdt : D K F t ≠ 0) (c : F) (i : ℕ) :
    dcoordD (K := K) t hdt (c ^ p * t ^ i) = i • (c ^ p * t ^ (i - 1)) := by
  rw [Derivation.leibniz, dcoord_frob p t hdt c, dcoord_t_pow t hdt i, smul_zero, add_zero,
    smul_comm, smul_eq_mul]

omit [Fact p.Prime] in
private lemma dcoord_iter_digit (t : F) (hdt : D K F t ≠ 0) (c : F) (i k : ℕ) :
    ((dcoordD (K := K) t hdt).toLinearMap ^ k) (c ^ p * t ^ i)
      = i.descFactorial k • (c ^ p * t ^ (i - k)) := by
  induction k generalizing i with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, endo_mul_app, dtlc_app, dcoord_digit p t hdt c i, map_nsmul, ih (i - 1),
        smul_smul]
      rcases i with _ | j
      · simp
      · rw [Nat.succ_descFactorial_succ]
        simp [Nat.succ_sub_succ]

private lemma dcoord_iter_sum (t : F) (hdt : D K F t ≠ 0) (a : Fin p → F) :
    ((dcoordD (K := K) t hdt).toLinearMap ^ (p - 1)) (∑ i : Fin p, a i ^ p * t ^ (i : ℕ))
      = (p - 1).factorial • a ⟨p - 1, Nat.sub_lt (Fact.out : p.Prime).pos one_pos⟩ ^ p := by
  have hp : p.Prime := Fact.out
  set pl : Fin p := ⟨p - 1, Nat.sub_lt hp.pos one_pos⟩ with hpl
  rw [map_sum, Finset.sum_congr rfl fun i _ => dcoord_iter_digit p t hdt (a i) (i : ℕ) (p - 1)]
  rw [Finset.sum_eq_single pl]
  · rw [show ((pl : ℕ) = p - 1) from rfl, Nat.descFactorial_self, Nat.sub_self, pow_zero,
      mul_one]
  · intro i _ hne
    have hlt : (i : ℕ) < p - 1 := by
      have h1 : (i : ℕ) < p := i.isLt
      have h2 : (i : ℕ) ≠ p - 1 := fun h => hne (Fin.ext h)
      omega
    rw [Nat.descFactorial_eq_zero_iff_lt.mpr hlt, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ pl) h

omit [Fact p.Prime] in
private lemma dcoord_iter_p_sum (t : F) (hdt : D K F t ≠ 0) (a : Fin p → F) :
    ((dcoordD (K := K) t hdt).toLinearMap ^ p) (∑ i : Fin p, a i ^ p * t ^ (i : ℕ)) = 0 := by
  rw [map_sum, Finset.sum_congr rfl fun i _ => dcoord_iter_digit p t hdt (a i) (i : ℕ) p]
  apply Finset.sum_eq_zero
  intro i _
  rw [Nat.descFactorial_eq_zero_iff_lt.mpr i.isLt, zero_smul]

private lemma factorial_cast_eq_neg_one : (((p - 1).factorial : ℕ) : F) = -1 := by
  have hw := ZMod.wilsons_lemma (p := p)
  calc ((p - 1).factorial : F)
      = ZMod.castHom (dvd_refl p) F (((p - 1).factorial : ℕ) : ZMod p) := (map_natCast _ _).symm
    _ = ZMod.castHom (dvd_refl p) F (-1) := by rw [hw]
    _ = -1 := by rw [map_neg, map_one]

end digits

section cartier
variable (p : ℕ) [Fact p.Prime] [CharP F p] [AlgebraicCurve.IsCurveOver K F]

omit [CharP F p] [AlgebraicCurve.IsCurveOver K F] in
private lemma D_natCast (n : ℕ) : D K F (n : F) = 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.cast_succ, map_add, ih, Derivation.map_one_eq_zero, add_zero]

omit [AlgebraicCurve.IsCurveOver K F] in
private lemma natCast_ne_zero_of_lt (i : ℕ) (hip : 0 < i) (hlt : i < p) : ((i : ℕ) : F) ≠ 0 := by
  have hnd : ¬ p ∣ i := Nat.not_dvd_of_pos_of_lt hip hlt
  intro h0
  apply hnd
  rw [show ((i : ℕ) : F) = ZMod.castHom (dvd_refl p) F ((i : ℕ) : ZMod p) from
    (map_natCast _ _).symm] at h0
  have hz : ((i : ℕ) : ZMod p) = 0 := by
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    exact (ZMod.castHom (dvd_refl p) F).injective (by simpa using h0)
  exact (ZMod.natCast_eq_zero_iff i p).mp hz

omit [CharP F p] [AlgebraicCurve.IsCurveOver K F] in
private lemma smul_D_exact (t : F) (i : ℕ) (hν : ((i + 1 : ℕ) : F) ≠ 0) :
    (t ^ i : F) • D K F t = D K F (((i + 1 : ℕ) : F)⁻¹ * t ^ (i + 1)) := by
  have hinv : D K F (((i + 1 : ℕ) : F)⁻¹) = 0 := by
    rw [(D K F).leibniz_of_mul_eq_one (inv_mul_cancel₀ hν), D_natCast, smul_zero]
  rw [Derivation.leibniz, hinv, smul_zero, add_zero, Derivation.leibniz_pow]
  rw [← Nat.cast_smul_eq_nsmul F, smul_smul, smul_smul]
  rw [Nat.add_sub_cancel]
  rw [inv_mul_cancel₀ hν, one_mul]

omit [AlgebraicCurve.IsCurveOver K F] in
private lemma cartier_coord (t : F) (_hdt : D K F t ≠ 0) (C : Ω[F⁄K] →+ Ω[F⁄K])
    (hsemi : ∀ (f : F) (ω : Ω[F⁄K]), C (f ^ p • ω) = f • C ω)
    (hker : ∀ f : F, C (D K F f) = 0)
    (hlog : ∀ f : F, C (f ^ (p - 1) • D K F f) = D K F f)
    (a : Fin p → F) :
    C ((∑ i : Fin p, a i ^ p * t ^ (i : ℕ)) • D K F t)
      = a ⟨p - 1, Nat.sub_lt (Fact.out : p.Prime).pos one_pos⟩ • D K F t := by
  have hp : p.Prime := Fact.out
  set pl : Fin p := ⟨p - 1, Nat.sub_lt hp.pos one_pos⟩ with hpl
  rw [Finset.sum_smul, map_sum]
  have hterm : ∀ i : Fin p, i ∈ Finset.univ →
      C ((a i ^ p * t ^ (i : ℕ)) • D K F t)
        = if i = pl then a i • D K F t else 0 := by
    intro i _
    rw [mul_smul, hsemi]
    by_cases hi : i = pl
    · rw [if_pos hi]
      have : (i : ℕ) = p - 1 := by rw [hi]
      rw [this, hlog t]
    · rw [if_neg hi]
      have hlt : (i : ℕ) + 1 < p := by
        have h1 : (i : ℕ) < p := i.isLt
        have h2 : (i : ℕ) ≠ p - 1 := fun h => hi (Fin.ext h)
        omega
      rw [smul_D_exact (K := K) t (i : ℕ)
        (natCast_ne_zero_of_lt p ((i : ℕ) + 1) (Nat.succ_pos _) hlt), hker, smul_zero]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' Finset.univ pl (fun i => a i • D K F t)]
  rw [if_pos (Finset.mem_univ pl)]

omit [Fact p.Prime] [CharP F p] [AlgebraicCurve.IsCurveOver K F] in
private lemma exists_ker_of_pow_eq_zero (τ : F →ₗ[K] F) (hτp : τ ^ p = 0) :
    ∃ h : F, h ≠ 0 ∧ τ h = 0 := by
  by_contra hno
  push Not at hno
  have hinj : Function.Injective τ := by
    rw [← LinearMap.ker_eq_bot]
    rw [LinearMap.ker_eq_bot']
    intro m hm
    by_contra hm0
    exact hno m hm0 hm
  have hiter : Function.Injective (⇑τ)^[p] := hinj.iterate p
  have h10 : (τ ^ p) (1 : F) = (τ ^ p) (0 : F) := by rw [hτp]; simp
  rw [Module.End.pow_apply, Module.End.pow_apply] at h10
  exact one_ne_zero (hiter h10)

end cartier

section main
variable [AlgebraicCurve.IsCurveOver K F]

private theorem fixed_is_dlog_main (p : ℕ) [Fact p.Prime] [CharP K p] [PerfectField K]
    (x : F) [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (hb : ∀ (d : Derivation K F F) (a : F),
        (d.toLinearMap + LinearMap.mulLeft K a) ^ p
          = d.toLinearMap ^ p + LinearMap.mulLeft K (a ^ p + (d.toLinearMap ^ (p - 1)) a))
    (C : Ω[F⁄K] →+ Ω[F⁄K])
    (hsemi : ∀ (f : F) (ω : Ω[F⁄K]), C (f ^ p • ω) = f • C ω)
    (hker : ∀ f : F, C (KaehlerDifferential.D K F f) = 0)
    (hlog : ∀ f : F, C (f ^ (p - 1) • KaehlerDifferential.D K F f) = KaehlerDifferential.D K F f)
    (w : Ω[F⁄K]) (hfix : C w = w) :
    ∃ h : F, h ≠ 0 ∧ w = h⁻¹ • KaehlerDifferential.D K F h := by
  haveI hFp : CharP F p := charP_of_injective_algebraMap (algebraMap K F).injective p
  have hp : p.Prime := Fact.out
  obtain ⟨t, hdt⟩ := AlgebraicCurve.exists_D_ne_zero (K := K) (F := F)
  obtain ⟨g, hg⟩ := exists_coeff (K := K) t hdt w
  obtain ⟨a, ha, -⟩ := AlgebraicCurve.pDigits_existsUnique p x (t := t) hdt g
  set pl : Fin p := ⟨p - 1, Nat.sub_lt hp.pos one_pos⟩ with hpl

  have hfix2 : a pl = g := by
    apply coeff_unique t hdt
    calc a pl • D K F t
        = C ((∑ i : Fin p, a i ^ p * t ^ (i : ℕ)) • D K F t) :=
          (cartier_coord p t hdt C hsemi hker hlog a).symm
      _ = C (g • D K F t) := by rw [← ha]
      _ = C w := by rw [← hg]
      _ = w := hfix
      _ = g • D K F t := hg

  have hiter : ((dcoordD (K := K) t hdt).toLinearMap ^ (p - 1)) g
      = (p - 1).factorial • a pl ^ p := by
    conv_lhs => rw [ha]
    exact dcoord_iter_sum p t hdt a
  have hc : g ^ p + ((dcoordD (K := K) t hdt).toLinearMap ^ (p - 1)) g = 0 := by
    rw [hiter, hfix2, ← Nat.cast_smul_eq_nsmul F, factorial_cast_eq_neg_one p]
    ring

  have hDp : (dcoordD (K := K) t hdt).toLinearMap ^ p = 0 := by
    ext f
    obtain ⟨af, haf, -⟩ := AlgebraicCurve.pDigits_existsUnique p x (t := t) hdt f
    rw [LinearMap.zero_apply, haf]
    exact dcoord_iter_p_sum p t hdt af

  have hscal : (-g) ^ p + ((dcoordD (K := K) t hdt).toLinearMap ^ (p - 1)) (-g) = 0 := by
    have h1 : (-g : F) ^ p = -(g ^ p) := by
      rw [neg_pow g p, neg_one_pow_char F p, neg_one_mul]
    rw [h1, map_neg, ← neg_add, hc, neg_zero]
  have hml0 : LinearMap.mulLeft K (0 : F) = 0 := by
    ext f; simp
  have hτp : ((dcoordD (K := K) t hdt).toLinearMap + LinearMap.mulLeft K (-g)) ^ p = 0 := by
    rw [hb (dcoordD (K := K) t hdt) (-g), hDp, hscal, hml0, zero_add]

  obtain ⟨h, hh0, hker2⟩ := exists_ker_of_pow_eq_zero p _ hτp
  refine ⟨h, hh0, ?_⟩
  have hdh : dcoord t hdt h = g * h := by
    have h3 := hker2
    rw [LinearMap.add_apply, dtlc_app] at h3
    have h2 : dcoordD (K := K) t hdt h + (-g) * h = 0 := h3
    rw [dcoordD_apply] at h2
    have h4 : dcoord t hdt h - g * h = 0 := by rw [sub_eq_add_neg, ← neg_mul]; exact h2
    exact eq_of_sub_eq_zero h4
  have hDh : KaehlerDifferential.D K F h = (g * h) • KaehlerDifferential.D K F t := by
    rw [dcoord_spec t hdt h, hdh]
  calc w = (h⁻¹ * h) • w := by rw [inv_mul_cancel₀ hh0, one_smul]
    _ = h⁻¹ • (h • w) := mul_smul _ _ _
    _ = h⁻¹ • KaehlerDifferential.D K F h := by
        rw [hg, hDh, smul_smul, smul_smul, smul_smul]
        congr 1
        ring

end main

end Star2C

theorem solution {K : Type u} {F : Type v}
    [Field K] [Field F] [Algebra K F] [AlgebraicCurve.IsCurveOver K F] (p : ℕ)
    [Fact p.Prime] [CharP K p] [PerfectField K] (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (C : Ω[F⁄K] →+ Ω[F⁄K])
    (hsemi : ∀ (f : F) (ω : Ω[F⁄K]), C (f ^ p • ω) = f • C ω)
    (hker : ∀ f : F, C (KaehlerDifferential.D K F f) = 0)
    (hlog : ∀ f : F, C (f ^ (p - 1) • KaehlerDifferential.D K F f) = KaehlerDifferential.D K F f)
    (w : Ω[F⁄K]) (hfix : C w = w) :
    ∃ h : F, h ≠ 0 ∧ w = h⁻¹ • KaehlerDifferential.D K F h := by
  haveI : CharP F p := charP_of_injective_algebraMap (algebraMap K F).injective p
  exact Star2C.fixed_is_dlog_main p x
    (fun d a => Derivation.add_mulLeft_pow_char p d a) C hsemi hker hlog w hfix

end S_AlgebraicCurve_exists_dlog_of_cartierOperator_fixed
end P2MW
export P2MW.S_AlgebraicCurve_exists_dlog_of_cartierOperator_fixed (solution)
