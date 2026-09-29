-- Prove2me | solution 1 for AutomorphicForm.measure_setOf_integral_valuation_det_eq_geom_sum_absNorm_mul_measure_localIntegralSet
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/5123f213-a40d-5666-bb58-849f1babe302

import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_AutomorphicForm_measure_setOf_integral_valuation_det_eq_geom_sum_absNorm_mul_measure_localIntegralSet

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory NumberField IsDedekindDomain
open scoped Pointwise

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "localIntegralSet one_mem_localIntegralSet isOpen_localIntegralSet localGLBorel borelSpace_localGLBorel"
namespace LocalDetShell
p2m_open "AutomorphicForm"

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

local notation "𝕂" => HeightOneSpectrum.adicCompletion K v
local notation "𝓸" => HeightOneSpectrum.adicCompletionIntegers K v

def unif : 𝕂 := ((HeightOneSpectrum.valuation_exists_uniformizer K v).choose : K)

theorem v_unif : Valued.v (unif K v) = WithZero.exp (-1 : ℤ) := by
  unfold unif
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact (HeightOneSpectrum.valuation_exists_uniformizer K v).choose_spec

theorem unif_ne_zero : unif K v ≠ 0 := by
  intro h
  have := v_unif K v
  rw [h, map_zero] at this
  exact WithZero.zero_ne_coe this

theorem v_unif_pow (n : ℕ) : Valued.v (unif K v ^ n) = WithZero.exp (-(n : ℤ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, map_mul, ih, v_unif, ← WithZero.exp_add]
    congr 1
    push_cast
    ring

theorem unif_pow_ne_zero (n : ℕ) : unif K v ^ n ≠ 0 := pow_ne_zero _ (unif_ne_zero K v)

theorem unif_mem : unif K v ∈ 𝓸 := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, v_unif, ← WithZero.exp_zero,
    WithZero.exp_le_exp]
  norm_num

theorem unif_pow_mem (n : ℕ) : unif K v ^ n ∈ 𝓸 := pow_mem (unif_mem K v) n

theorem exists_v_eq_exp_neg {x : 𝕂} (hx : x ∈ 𝓸) (hx0 : x ≠ 0) :
    ∃ n : ℕ, Valued.v x = WithZero.exp (-(n : ℤ)) := by
  have hv0 : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx0
  have hle : Valued.v x ≤ 1 := hx
  rw [← WithZero.exp_log hv0] at hle ⊢
  rw [← WithZero.exp_zero, WithZero.exp_le_exp] at hle
  refine ⟨(-(WithZero.log (Valued.v x))).toNat, ?_⟩
  congr 1
  rw [Int.toNat_of_nonneg (by linarith)]
  ring

theorem div_mem_of_v_le {x y : 𝕂} (hxy : Valued.v y ≤ Valued.v x) (hx0 : x ≠ 0) :
    y / x ∈ 𝓸 := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀]
  have hv0 : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx0
  exact div_le_one_of_le₀ hxy zero_le'

theorem mem_of_v_eq_one {u : 𝕂} (hu : Valued.v u = 1) : u ∈ 𝓸 := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, hu]

theorem inv_mem_of_v_eq_one {u : 𝕂} (hu : Valued.v u = 1) : u⁻¹ ∈ 𝓸 := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hu, inv_one]

theorem div_unif_mem_of_v_lt_one {m : 𝕂} (hm : Valued.v m < 1) : m / unif K v ∈ 𝓸 := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀, v_unif]
  by_cases hm0 : m = 0
  · simp [hm0]
  have hv0 : Valued.v m ≠ 0 := (Valuation.ne_zero_iff _).mpr hm0
  rw [← WithZero.exp_log hv0] at hm ⊢
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hm
  rw [← WithZero.exp_sub, ← WithZero.exp_zero, WithZero.exp_le_exp]
  omega

theorem v_unif_pow_div {x : 𝕂} {n : ℕ} (hx : Valued.v x = WithZero.exp (-(n : ℤ))) :
    Valued.v (unif K v ^ n / x) = 1 := by
  have hx0 : x ≠ 0 := by
    intro h; rw [h, map_zero] at hx; exact WithZero.zero_ne_coe hx
  rw [map_div₀, v_unif_pow, hx, div_self]
  exact WithZero.coe_ne_zero

def MInt (M : Matrix (Fin 2) (Fin 2) 𝕂) : Prop := ∀ i j, M i j ∈ 𝓸

theorem mInt_mul {M N : Matrix (Fin 2) (Fin 2) 𝕂} (hM : MInt K v M) (hN : MInt K v N) :
    MInt K v (M * N) := by
  intro i j
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun l _ => mul_mem (hM i l) (hN l j)

theorem mInt_one : MInt K v (1 : Matrix (Fin 2) (Fin 2) 𝕂) := by
  intro i j
  by_cases h : i = j
  · subst h; rw [Matrix.one_apply_eq]; exact one_mem _
  · rw [Matrix.one_apply_ne h]; exact zero_mem _

theorem mInt_of {a b c d : 𝕂} (ha : a ∈ 𝓸) (hb : b ∈ 𝓸) (hc : c ∈ 𝓸) (hd : d ∈ 𝓸) :
    MInt K v !![a, b; c, d] := by
  intro i j
  fin_cases i <;> fin_cases j <;> simpa

theorem det_mem_of_mInt {M : Matrix (Fin 2) (Fin 2) 𝕂} (hM : MInt K v M) : M.det ∈ 𝓸 := by
  rw [Matrix.det_fin_two]
  exact sub_mem (mul_mem (hM 0 0) (hM 1 1)) (mul_mem (hM 0 1) (hM 1 0))

def unitGrp : Subgroup (GL (Fin 2) 𝕂) where
  carrier := AutomorphicForm.localIntegralSet K v
  mul_mem' := by
    intro g h hg hh
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul]; exact mInt_mul K v hg.1 hh.1
    · rw [mul_inv_rev, Units.val_mul]; exact mInt_mul K v hh.2 hg.2
  one_mem' := AutomorphicForm.one_mem_localIntegralSet K v
  inv_mem' := by
    intro g hg
    exact ⟨hg.2, by rw [inv_inv]; exact hg.1⟩

theorem coe_unitGrp : (unitGrp K v : Set (GL (Fin 2) 𝕂)) = AutomorphicForm.localIntegralSet K v :=
  rfl

theorem mem_unitGrp_iff' (g : GL (Fin 2) 𝕂) :
    g ∈ unitGrp K v ↔ MInt K v (g : Matrix (Fin 2) (Fin 2) 𝕂) ∧
      MInt K v ((g⁻¹ : GL (Fin 2) 𝕂) : Matrix (Fin 2) (Fin 2) 𝕂) :=
  Iff.rfl

def vdet (g : GL (Fin 2) 𝕂) : WithZero (Multiplicative ℤ) :=
  Valued.v ((Matrix.GeneralLinearGroup.det g : (𝕂)ˣ) : 𝕂)

theorem vdet_eq (g : GL (Fin 2) 𝕂) : vdet K v g = Valued.v (g : Matrix (Fin 2) (Fin 2) 𝕂).det := by
  rw [vdet, Matrix.GeneralLinearGroup.val_det_apply]

theorem vdet_mul (g h : GL (Fin 2) 𝕂) : vdet K v (g * h) = vdet K v g * vdet K v h := by
  simp only [vdet, map_mul, Units.val_mul]

theorem vdet_ne_zero (g : GL (Fin 2) 𝕂) : vdet K v g ≠ 0 :=
  (Valuation.ne_zero_iff _).mpr (Matrix.GeneralLinearGroup.det g).ne_zero

theorem mem_unitGrp_iff (g : GL (Fin 2) 𝕂) :
    g ∈ unitGrp K v ↔ MInt K v (g : Matrix (Fin 2) (Fin 2) 𝕂) ∧ vdet K v g = 1 := by
  constructor
  · rintro ⟨hg, hginv⟩
    refine ⟨hg, ?_⟩
    have h1 : vdet K v g ≤ 1 := by rw [vdet_eq]; exact det_mem_of_mInt K v hg
    have h2 : vdet K v g⁻¹ ≤ 1 := by rw [vdet_eq]; exact det_mem_of_mInt K v hginv
    have h12 : vdet K v g * vdet K v g⁻¹ = 1 := by
      rw [← vdet_mul, mul_inv_cancel, vdet, map_one, Units.val_one, map_one]
    refine le_antisymm h1 ?_
    calc (1 : WithZero (Multiplicative ℤ)) = vdet K v g * vdet K v g⁻¹ := h12.symm
      _ ≤ vdet K v g * 1 := mul_le_mul_right h2 _
      _ = vdet K v g := mul_one _
  · rintro ⟨hg, hdet⟩
    refine ⟨hg, ?_⟩
    rw [vdet_eq] at hdet
    have hinv : ((g⁻¹ : GL (Fin 2) 𝕂) : Matrix (Fin 2) (Fin 2) 𝕂) =
        ((g : Matrix (Fin 2) (Fin 2) 𝕂).det)⁻¹ • (g : Matrix (Fin 2) (Fin 2) 𝕂).adjugate := by
      rw [Matrix.coe_units_inv, Matrix.inv_def, Ring.inverse_eq_inv']
    rw [hinv]
    intro i j
    rw [Matrix.smul_apply, smul_eq_mul]
    refine mul_mem (inv_mem_of_v_eq_one K v hdet) ?_
    rw [Matrix.eta_fin_two (g : Matrix (Fin 2) (Fin 2) 𝕂), Matrix.adjugate_fin_two_of]
    fin_cases i <;> fin_cases j
    · simpa using hg 1 1
    · simpa using neg_mem (hg 0 1)
    · simpa using neg_mem (hg 1 0)
    · simpa using hg 0 0

def shell (k : ℕ) : Set (GL (Fin 2) 𝕂) :=
  {g | (∀ i j, (g : Matrix (Fin 2) (Fin 2) 𝕂) i j ∈ 𝓸) ∧
    Valued.v ((Matrix.GeneralLinearGroup.det g : (𝕂)ˣ) : 𝕂) = WithZero.exp (-(k : ℤ))}

theorem mem_shell_iff {k : ℕ} {g : GL (Fin 2) 𝕂} :
    g ∈ shell K v k ↔ MInt K v (g : Matrix (Fin 2) (Fin 2) 𝕂) ∧ vdet K v g = WithZero.exp (-(k : ℤ)) :=
  Iff.rfl

def gl (a b c d : 𝕂) (h : a * d - b * c ≠ 0) : GL (Fin 2) 𝕂 :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, b; c, d] (by rwa [Matrix.det_fin_two_of])

@[scoped simp] theorem coe_gl (a b c d : 𝕂) (h : a * d - b * c ≠ 0) :
    (gl K v a b c d h : Matrix (Fin 2) (Fin 2) 𝕂) = !![a, b; c, d] := rfl

theorem vdet_gl (a b c d : 𝕂) (h : a * d - b * c ≠ 0) :
    vdet K v (gl K v a b c d h) = Valued.v (a * d - b * c) := by
  rw [vdet_eq, coe_gl, Matrix.det_fin_two_of]

def lowRep (a : ℕ) (c : 𝕂) (d : ℕ) : GL (Fin 2) 𝕂 :=
  gl K v (unif K v ^ a) 0 c (unif K v ^ d) (by
    rw [zero_mul, sub_zero]; exact mul_ne_zero (unif_pow_ne_zero K v a) (unif_pow_ne_zero K v d))

theorem coe_lowRep (a : ℕ) (c : 𝕂) (d : ℕ) :
    (lowRep K v a c d : Matrix (Fin 2) (Fin 2) 𝕂) = !![unif K v ^ a, 0; c, unif K v ^ d] := rfl

theorem vdet_lowRep (a : ℕ) (c : 𝕂) (d : ℕ) :
    vdet K v (lowRep K v a c d) = WithZero.exp (-((a + d : ℕ) : ℤ)) := by
  rw [lowRep, vdet_gl, zero_mul, sub_zero, map_mul, v_unif_pow, v_unif_pow, ← WithZero.exp_add]
  congr 1; push_cast; ring

theorem mInt_lowRep (a : ℕ) {c : 𝕂} (hc : c ∈ 𝓸) (d : ℕ) :
    MInt K v (lowRep K v a c d : Matrix (Fin 2) (Fin 2) 𝕂) := by
  rw [coe_lowRep]
  exact mInt_of K v (unif_pow_mem K v a) (zero_mem _) hc (unif_pow_mem K v d)

def lowUni (r : 𝕂) : GL (Fin 2) 𝕂 := gl K v 1 0 r 1 (by norm_num)

theorem lowUni_mem {r : 𝕂} (hr : r ∈ 𝓸) : lowUni K v r ∈ unitGrp K v := by
  rw [mem_unitGrp_iff]
  refine ⟨?_, ?_⟩
  · rw [lowUni, coe_gl]; exact mInt_of K v (one_mem _) (zero_mem _) hr (one_mem _)
  · rw [lowUni, vdet_gl]; norm_num

theorem lowRep_mul_lowUni (a : ℕ) (c : 𝕂) (d : ℕ) (r : 𝕂) :
    lowRep K v a c d * lowUni K v r = lowRep K v a (c + unif K v ^ d * r) d := by
  refine Units.ext ?_
  rw [Units.val_mul, coe_lowRep, coe_lowRep, lowUni, coe_gl]
  ext i j : 1
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem coe_eta (g : GL (Fin 2) 𝕂) :
    (g : Matrix (Fin 2) (Fin 2) 𝕂) =
      !![(g : Matrix (Fin 2) (Fin 2) 𝕂) 0 0, (g : Matrix (Fin 2) (Fin 2) 𝕂) 0 1;
        (g : Matrix (Fin 2) (Fin 2) 𝕂) 1 0, (g : Matrix (Fin 2) (Fin 2) 𝕂) 1 1] :=
  Matrix.eta_fin_two _

theorem exists_lowRep_of_le {k : ℕ} {g : GL (Fin 2) 𝕂} (hg : g ∈ shell K v k)
    (hle : Valued.v ((g : Matrix (Fin 2) (Fin 2) 𝕂) 0 1) ≤ Valued.v ((g : Matrix (Fin 2) (Fin 2) 𝕂) 0 0)) :
    ∃ (a d : ℕ) (c : 𝕂) (u : GL (Fin 2) 𝕂), a + d = k ∧ c ∈ 𝓸 ∧ u ∈ unitGrp K v ∧
      g * u = lowRep K v a c d := by
  obtain ⟨hint, hdet⟩ := (mem_shell_iff K v).mp hg
  set x := (g : Matrix (Fin 2) (Fin 2) 𝕂) 0 0 with hx
  set y := (g : Matrix (Fin 2) (Fin 2) 𝕂) 0 1 with hy
  set z := (g : Matrix (Fin 2) (Fin 2) 𝕂) 1 0 with hz
  set w := (g : Matrix (Fin 2) (Fin 2) 𝕂) 1 1 with hw
  have hgm : (g : Matrix (Fin 2) (Fin 2) 𝕂) = !![x, y; z, w] := coe_eta K v g
  have hdet' : Valued.v (x * w - y * z) = WithZero.exp (-(k : ℤ)) := by
    rw [vdet_eq, hgm, Matrix.det_fin_two_of] at hdet; exact hdet

  have hx0 : x ≠ 0 := by
    intro h0
    have hy0 : y = 0 := by
      rw [h0, map_zero, le_zero_iff] at hle
      exact (Valuation.zero_iff _).mp hle
    rw [h0, hy0, zero_mul, zero_mul, sub_zero, map_zero] at hdet'
    exact WithZero.zero_ne_coe hdet'

  have hq : -y / x ∈ 𝓸 := by
    have : Valued.v (-y) ≤ Valued.v x := by rwa [Valuation.map_neg]
    exact div_mem_of_v_le K v this hx0
  set u₁ : GL (Fin 2) 𝕂 := gl K v 1 (-y / x) 0 1 (by norm_num) with hu₁
  have hu₁mem : u₁ ∈ unitGrp K v := by
    rw [mem_unitGrp_iff]
    refine ⟨?_, ?_⟩
    · rw [hu₁, coe_gl]; exact mInt_of K v (one_mem _) hq (zero_mem _) (one_mem _)
    · rw [hu₁, vdet_gl]; norm_num
  set w' := z * (-y / x) + w with hw'
  have hgu₁ : ((g * u₁ : GL (Fin 2) 𝕂) : Matrix (Fin 2) (Fin 2) 𝕂) = !![x, 0; z, w'] := by
    rw [Units.val_mul, hgm, hu₁, coe_gl]
    ext i j : 1
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hw']
    field_simp
    ring

  have hxw' : Valued.v (x * w') = WithZero.exp (-(k : ℤ)) := by
    have : x * w' = x * w - y * z := by rw [hw']; field_simp; ring
    rw [this]; exact hdet'
  have hw'0 : w' ≠ 0 := by
    intro h0; rw [h0, mul_zero, map_zero] at hxw'; exact WithZero.zero_ne_coe hxw'
  have hzmem : z ∈ 𝓸 := hint 1 0
  have hw'mem : w' ∈ 𝓸 := by
    rw [hw']; exact add_mem (mul_mem hzmem hq) (hint 1 1)
  obtain ⟨a, ha⟩ := exists_v_eq_exp_neg K v (hint 0 0) hx0
  obtain ⟨d, hd⟩ := exists_v_eq_exp_neg K v hw'mem hw'0
  have had : a + d = k := by
    rw [map_mul, ha, hd, ← WithZero.exp_add] at hxw'
    have := WithZero.exp_injective hxw'
    omega

  set p := unif K v ^ a / x with hp
  set r := unif K v ^ d / w' with hr
  have hvp : Valued.v p = 1 := v_unif_pow_div K v ha
  have hvr : Valued.v r = 1 := v_unif_pow_div K v hd
  have hp0 : p ≠ 0 := by intro h; rw [h, map_zero] at hvp; exact zero_ne_one hvp
  have hr0 : r ≠ 0 := by intro h; rw [h, map_zero] at hvr; exact zero_ne_one hvr
  set u₂ : GL (Fin 2) 𝕂 := gl K v p 0 0 r (by rw [zero_mul, sub_zero]; exact mul_ne_zero hp0 hr0)
    with hu₂
  have hu₂mem : u₂ ∈ unitGrp K v := by
    rw [mem_unitGrp_iff]
    refine ⟨?_, ?_⟩
    · rw [hu₂, coe_gl]
      exact mInt_of K v (mem_of_v_eq_one K v hvp) (zero_mem _) (zero_mem _) (mem_of_v_eq_one K v hvr)
    · rw [hu₂, vdet_gl, zero_mul, sub_zero, map_mul, hvp, hvr, mul_one]
  refine ⟨a, d, z * p, u₁ * u₂, had, mul_mem hzmem (mem_of_v_eq_one K v hvp),
    mul_mem hu₁mem hu₂mem, ?_⟩
  refine Units.ext ?_
  rw [← mul_assoc, Units.val_mul, hgu₁, hu₂, coe_gl, coe_lowRep]
  have hxp : x * p = unif K v ^ a := by rw [hp]; field_simp
  have hwr : w' * r = unif K v ^ d := by rw [hr]; field_simp
  ext i j : 1
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hxp, hwr]

def swapCol : GL (Fin 2) 𝕂 := gl K v 0 1 1 0 (by norm_num)

theorem swapCol_mem : swapCol K v ∈ unitGrp K v := by
  rw [mem_unitGrp_iff]
  refine ⟨?_, ?_⟩
  · rw [swapCol, coe_gl]; exact mInt_of K v (zero_mem _) (one_mem _) (one_mem _) (zero_mem _)
  · rw [swapCol, vdet_gl]; norm_num

theorem exists_lowRep {k : ℕ} {g : GL (Fin 2) 𝕂} (hg : g ∈ shell K v k) :
    ∃ (a d : ℕ) (c : 𝕂) (u : GL (Fin 2) 𝕂), a + d = k ∧ c ∈ 𝓸 ∧ u ∈ unitGrp K v ∧
      g * u = lowRep K v a c d := by
  rcases le_or_gt (Valued.v ((g : Matrix (Fin 2) (Fin 2) 𝕂) 0 1))
      (Valued.v ((g : Matrix (Fin 2) (Fin 2) 𝕂) 0 0)) with hle | hlt
  · exact exists_lowRep_of_le K v hg hle
  ·
    obtain ⟨hint, hdet⟩ := (mem_shell_iff K v).mp hg
    have hgs : ((g * swapCol K v : GL (Fin 2) 𝕂) : Matrix (Fin 2) (Fin 2) 𝕂) =
        !![(g : Matrix (Fin 2) (Fin 2) 𝕂) 0 1, (g : Matrix (Fin 2) (Fin 2) 𝕂) 0 0;
          (g : Matrix (Fin 2) (Fin 2) 𝕂) 1 1, (g : Matrix (Fin 2) (Fin 2) 𝕂) 1 0] := by
      rw [Units.val_mul, coe_eta K v g, swapCol, coe_gl]
      ext i j : 1
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    have hg' : g * swapCol K v ∈ shell K v k := by
      rw [mem_shell_iff]
      refine ⟨?_, ?_⟩
      · rw [hgs]; exact mInt_of K v (hint 0 1) (hint 0 0) (hint 1 1) (hint 1 0)
      · rw [vdet_mul, hdet, ((mem_unitGrp_iff K v _).mp (swapCol_mem K v)).2, mul_one]
    have hle' : Valued.v (((g * swapCol K v : GL (Fin 2) 𝕂) : Matrix (Fin 2) (Fin 2) 𝕂) 0 1) ≤
        Valued.v (((g * swapCol K v : GL (Fin 2) 𝕂) : Matrix (Fin 2) (Fin 2) 𝕂) 0 0) := by
      rw [hgs]; simpa using hlt.le
    obtain ⟨a, d, c, u, had, hc, hu, hgu⟩ := exists_lowRep_of_le K v hg' hle'
    exact ⟨a, d, c, swapCol K v * u, had, hc, mul_mem (swapCol_mem K v) hu, by rw [← mul_assoc, hgu]⟩

abbrev κ : Type := IsLocalRing.ResidueField 𝓸

@[reducible] def instFintypeκ : Fintype (κ K v) := Fintype.ofFinite _

attribute [local instance] instFintypeκ

def sec (t : κ K v) : 𝓸 := Function.surjInv (IsLocalRing.residue_surjective) t

theorem residue_sec (t : κ K v) : IsLocalRing.residue 𝓸 (sec K v t) = t :=
  Function.surjInv_eq _ _

def digits : (d : ℕ) → (Fin d → κ K v) → 𝕂
  | 0, _ => 0
  | d + 1, t => (sec K v (t 0) : 𝕂) + unif K v * digits d (Fin.tail t)

theorem digits_zero (t : Fin 0 → κ K v) : digits K v 0 t = 0 := rfl

theorem digits_succ (d : ℕ) (t : Fin (d + 1) → κ K v) :
    digits K v (d + 1) t = (sec K v (t 0) : 𝕂) + unif K v * digits K v d (Fin.tail t) := rfl

theorem digits_mem (d : ℕ) (t : Fin d → κ K v) : digits K v d t ∈ 𝓸 := by
  induction d with
  | zero => exact zero_mem _
  | succ d ih =>
    rw [digits_succ]
    exact add_mem (sec K v (t 0)).2 (mul_mem (unif_mem K v) (ih _))

theorem sub_div_unif_mem_of_residue_eq {c c' : 𝓸}
    (h : IsLocalRing.residue 𝓸 c = IsLocalRing.residue 𝓸 c') :
    ((c : 𝕂) - c') / unif K v ∈ 𝓸 := by
  refine div_unif_mem_of_v_lt_one K v ?_
  have hmem : c - c' ∈ IsLocalRing.maximalIdeal 𝓸 := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, h, sub_self]
  have := (NumberField.AdelicHaar.mem_maximalIdeal_iff_valued_lt_one (𝓞 K) K v (c - c')).mp hmem
  simpa using this

theorem residue_eq_of_sub_eq_unif_mul {c c' : 𝓸} {m : 𝕂} (hm : m ∈ 𝓸)
    (h : (c : 𝕂) - c' = unif K v * m) :
    IsLocalRing.residue 𝓸 c = IsLocalRing.residue 𝓸 c' := by
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
    NumberField.AdelicHaar.mem_maximalIdeal_iff_valued_lt_one]
  have hcoe : ((c - c' : 𝓸) : 𝕂) = unif K v * m := by simpa using h
  rw [hcoe, map_mul, v_unif]
  have hm1 : Valued.v m ≤ 1 := hm
  calc WithZero.exp (-1 : ℤ) * Valued.v m ≤ WithZero.exp (-1 : ℤ) * 1 := mul_le_mul_right hm1 _
    _ < 1 := by rw [mul_one, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num

theorem exists_digits (d : ℕ) {c : 𝕂} (hc : c ∈ 𝓸) :
    ∃ (t : Fin d → κ K v) (r : 𝕂), r ∈ 𝓸 ∧ c = digits K v d t + unif K v ^ d * r := by
  induction d generalizing c with
  | zero => exact ⟨fun i => i.elim0, c, hc, by rw [digits_zero, pow_zero, one_mul, zero_add]⟩
  | succ d ih =>

    set t₀ : κ K v := IsLocalRing.residue 𝓸 ⟨c, hc⟩ with ht₀
    have hres : IsLocalRing.residue 𝓸 ⟨c, hc⟩ = IsLocalRing.residue 𝓸 (sec K v t₀) := by
      rw [residue_sec]
    have hdiv := sub_div_unif_mem_of_residue_eq K v hres
    obtain ⟨t, r, hr, hcr⟩ := ih hdiv
    refine ⟨Fin.cons t₀ t, r, hr, ?_⟩
    rw [digits_succ, Fin.cons_zero, Fin.tail_cons]
    have h0 := unif_ne_zero K v
    have hcs : c - (sec K v t₀ : 𝕂) = unif K v * (digits K v d t + unif K v ^ d * r) := by
      rw [← hcr]
      field_simp
    linear_combination hcs

theorem digits_injective (d : ℕ) {t t' : Fin d → κ K v} {r r' : 𝕂} (hr : r ∈ 𝓸) (hr' : r' ∈ 𝓸)
    (h : digits K v d t + unif K v ^ d * r = digits K v d t' + unif K v ^ d * r') : t = t' := by
  induction d generalizing r r' with
  | zero => exact funext fun i => i.elim0
  | succ d ih =>
    rw [digits_succ, digits_succ] at h

    have hlow : ((sec K v (t 0) : 𝓸) : 𝕂) - (sec K v (t' 0) : 𝓸) =
        unif K v * (digits K v d (Fin.tail t') + unif K v ^ d * r' -
          (digits K v d (Fin.tail t) + unif K v ^ d * r)) := by
      linear_combination h
    have hm : digits K v d (Fin.tail t') + unif K v ^ d * r' -
        (digits K v d (Fin.tail t) + unif K v ^ d * r) ∈ 𝓸 :=
      sub_mem (add_mem (digits_mem K v _ _) (mul_mem (unif_pow_mem K v _) hr'))
        (add_mem (digits_mem K v _ _) (mul_mem (unif_pow_mem K v _) hr))
    have ht0 : t 0 = t' 0 := by
      have := residue_eq_of_sub_eq_unif_mul K v hm hlow
      rwa [residue_sec, residue_sec] at this

    have htail : digits K v d (Fin.tail t) + unif K v ^ d * r =
        digits K v d (Fin.tail t') + unif K v ^ d * r' := by
      rw [ht0] at h
      have h0 := unif_ne_zero K v
      have h'' : unif K v * (digits K v d (Fin.tail t) + unif K v ^ d * r) =
          unif K v * (digits K v d (Fin.tail t') + unif K v ^ d * r') := by
        linear_combination h
      exact mul_left_cancel₀ h0 h''
    have htt := ih hr hr' htail
    rw [← Fin.cons_self_tail t, ← Fin.cons_self_tail t', ht0, htt]

abbrev Idx (k : ℕ) : Type := Σ d : Fin (k + 1), (Fin d → κ K v)

def rep (k : ℕ) (i : Idx K v k) : GL (Fin 2) 𝕂 :=
  lowRep K v (k - i.1) (digits K v i.1 i.2) i.1

theorem rep_mem_shell (k : ℕ) (i : Idx K v k) : rep K v k i ∈ shell K v k := by
  rw [mem_shell_iff, rep]
  refine ⟨mInt_lowRep K v _ (digits_mem K v _ _) _, ?_⟩
  rw [vdet_lowRep]
  congr 2
  have := i.1.isLt
  push_cast
  omega

theorem mul_mem_shell {k : ℕ} {g u : GL (Fin 2) 𝕂} (hg : g ∈ shell K v k) (hu : u ∈ unitGrp K v) :
    g * u ∈ shell K v k := by
  rw [mem_shell_iff] at hg ⊢
  rw [mem_unitGrp_iff] at hu
  refine ⟨?_, ?_⟩
  · rw [Units.val_mul]; exact mInt_mul K v hg.1 hu.1
  · rw [vdet_mul, hg.2, hu.2, mul_one]

theorem smul_subset_shell (k : ℕ) (i : Idx K v k) :
    rep K v k i • (unitGrp K v : Set (GL (Fin 2) 𝕂)) ⊆ shell K v k := by
  intro x hx
  obtain ⟨u, hu, rfl⟩ := Set.mem_smul_set.mp hx
  exact mul_mem_shell K v (rep_mem_shell K v k i) hu

theorem exists_mem_smul (k : ℕ) {g : GL (Fin 2) 𝕂} (hg : g ∈ shell K v k) :
    ∃ i : Idx K v k, g ∈ rep K v k i • (unitGrp K v : Set (GL (Fin 2) 𝕂)) := by
  obtain ⟨a, d, c, u, had, hc, hu, hgu⟩ := exists_lowRep K v hg
  obtain ⟨t, r, hr, hcr⟩ := exists_digits K v d hc
  have hdlt : d < k + 1 := by omega
  refine ⟨⟨⟨d, hdlt⟩, t⟩, ?_⟩
  rw [Set.mem_smul_set]
  refine ⟨lowUni K v r * u⁻¹, mul_mem (lowUni_mem K v hr) (inv_mem hu), ?_⟩
  rw [smul_eq_mul, ← mul_assoc, rep]
  show lowRep K v (k - d) (digits K v d t) d * lowUni K v r * u⁻¹ = g
  rw [lowRep_mul_lowUni, ← hcr, show k - d = a by omega, ← hgu, mul_inv_cancel_right]

theorem eq_of_rep_mul_eq (k : ℕ) (i j : Idx K v k) (M : GL (Fin 2) 𝕂)
    (hM : MInt K v (M : Matrix (Fin 2) (Fin 2) 𝕂)) (h : rep K v k i * M = rep K v k j) : i = j := by
  obtain ⟨⟨d, hd⟩, t⟩ := i
  obtain ⟨⟨d', hd'⟩, t'⟩ := j
  simp only [rep] at h

  have hmat := congrArg (fun g : GL (Fin 2) 𝕂 => (g : Matrix (Fin 2) (Fin 2) 𝕂)) h
  simp only [Units.val_mul, coe_lowRep] at hmat
  rw [coe_eta K v M] at hmat
  set m00 := (M : Matrix (Fin 2) (Fin 2) 𝕂) 0 0
  set m01 := (M : Matrix (Fin 2) (Fin 2) 𝕂) 0 1
  set m10 := (M : Matrix (Fin 2) (Fin 2) 𝕂) 1 0
  set m11 := (M : Matrix (Fin 2) (Fin 2) 𝕂) 1 1
  have e00 : unif K v ^ (k - d) * m00 = unif K v ^ (k - d') := by
    have := congrFun (congrFun hmat 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have e01 : unif K v ^ (k - d) * m01 = 0 := by
    have := congrFun (congrFun hmat 0) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have e10 : digits K v d t * m00 + unif K v ^ d * m10 = digits K v d' t' := by
    have := congrFun (congrFun hmat 1) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have e11 : digits K v d t * m01 + unif K v ^ d * m11 = unif K v ^ d' := by
    have := congrFun (congrFun hmat 1) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have h0 := unif_ne_zero K v
  have hm01 : m01 = 0 := (mul_eq_zero.mp e01).resolve_left (unif_pow_ne_zero K v _)

  have hkd : k - d ≤ k - d' := by
    have hv := congrArg Valued.v e00
    rw [map_mul, v_unif_pow, v_unif_pow] at hv
    have hle : Valued.v m00 ≤ 1 := hM 0 0
    have : WithZero.exp (-((k - d' : ℕ) : ℤ)) ≤ WithZero.exp (-((k - d : ℕ) : ℤ)) := by
      rw [← hv]
      calc WithZero.exp (-((k - d : ℕ) : ℤ)) * Valued.v m00
          ≤ WithZero.exp (-((k - d : ℕ) : ℤ)) * 1 := mul_le_mul_right hle _
        _ = _ := mul_one _
    rw [WithZero.exp_le_exp] at this
    omega
  have hdd : d ≤ d' := by
    rw [hm01, mul_zero, zero_add] at e11
    have hv := congrArg Valued.v e11
    rw [map_mul, v_unif_pow, v_unif_pow] at hv
    have hle : Valued.v m11 ≤ 1 := hM 1 1
    have : WithZero.exp (-(d' : ℤ)) ≤ WithZero.exp (-(d : ℤ)) := by
      rw [← hv]
      calc WithZero.exp (-(d : ℤ)) * Valued.v m11
          ≤ WithZero.exp (-(d : ℤ)) * 1 := mul_le_mul_right hle _
        _ = _ := mul_one _
    rw [WithZero.exp_le_exp] at this
    omega
  have hdeq : d = d' := by omega
  subst hdeq

  have hm00 : m00 = 1 := by
    have : unif K v ^ (k - d) * m00 = unif K v ^ (k - d) * 1 := by rw [mul_one]; exact e00
    exact mul_left_cancel₀ (unif_pow_ne_zero K v _) this
  rw [hm00, mul_one] at e10
  have htt : t = t' := by
    refine digits_injective K v d (hM 1 0) (zero_mem _) ?_
    rw [mul_zero, add_zero]
    exact e10
  subst htt
  rfl

theorem pairwiseDisjoint_smul (k : ℕ) :
    (Set.univ : Set (Idx K v k)).PairwiseDisjoint
      fun i => rep K v k i • (unitGrp K v : Set (GL (Fin 2) 𝕂)) := by
  intro i _ j _ hij
  refine Set.disjoint_left.mpr fun x hxi hxj => hij ?_
  obtain ⟨u, hu, rfl⟩ := Set.mem_smul_set.mp hxi
  obtain ⟨u', hu', hx⟩ := Set.mem_smul_set.mp hxj

  have hM : rep K v k i * (u * u'⁻¹) = rep K v k j := by
    rw [← mul_assoc, ← smul_eq_mul (rep K v k i) u, ← hx, smul_eq_mul, mul_inv_cancel_right]
  have hmem : u * u'⁻¹ ∈ unitGrp K v := mul_mem hu (inv_mem hu')
  exact eq_of_rep_mul_eq K v k i j _ ((mem_unitGrp_iff K v _).mp hmem).1 hM

theorem shell_eq_iUnion (k : ℕ) :
    shell K v k = ⋃ i ∈ (Finset.univ : Finset (Idx K v k)),
      rep K v k i • (unitGrp K v : Set (GL (Fin 2) 𝕂)) := by
  ext g
  simp only [Finset.mem_univ, Set.iUnion_true, Set.mem_iUnion]
  exact ⟨fun hg => exists_mem_smul K v k hg, fun ⟨i, hi⟩ => smul_subset_shell K v k i hi⟩

theorem card_κ : Nat.card (κ K v) = Ideal.absNorm v.asIdeal := by

  let f : 𝓞 K ⧸ v.asIdeal →+* κ K v :=
    Ideal.Quotient.lift v.asIdeal
      ((IsLocalRing.residue 𝓸).comp (algebraMap (𝓞 K) 𝓸))
      (fun a ha => NumberField.AdelicHaar.residue_algebraMap_eq_zero_of_mem (𝓞 K) K v ha)
  have hsurj : Function.Surjective f := by
    intro z
    obtain ⟨a, ha⟩ := NumberField.AdelicHaar.residue_algebraMap_surjective (𝓞 K) K v z
    exact ⟨Ideal.Quotient.mk _ a, ha⟩
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro q hq
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
    rw [Ideal.Quotient.eq_zero_iff_mem]
    have hq' : IsLocalRing.residue 𝓸 (algebraMap (𝓞 K) 𝓸 a) = 0 := hq
    rw [IsLocalRing.residue_eq_zero_iff,
      NumberField.AdelicHaar.mem_maximalIdeal_iff_valued_lt_one] at hq'
    rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := K)]
    rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact hq'
  rw [← Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩), Ideal.absNorm_apply,
    Submodule.cardQuot_apply]

theorem fintype_card_κ : Fintype.card (κ K v) = Ideal.absNorm v.asIdeal := by
  rw [← Nat.card_eq_fintype_card, card_κ]

theorem card_Idx (k : ℕ) :
    Fintype.card (Idx K v k) = ∑ i ∈ Finset.range (k + 1), Ideal.absNorm v.asIdeal ^ i := by
  classical
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fun, Fintype.card_fin, fintype_card_κ]
  exact Fin.sum_univ_eq_sum_range (fun i => Ideal.absNorm v.asIdeal ^ i) (k + 1)

theorem measure_shell
    (μ : @Measure (GL (Fin 2) 𝕂) (AutomorphicForm.localGLBorel K v))
    (hμ : @Measure.IsMulLeftInvariant (GL (Fin 2) 𝕂) (AutomorphicForm.localGLBorel K v) _ μ)
    (k : ℕ) :
    μ (shell K v k) =
      (∑ i ∈ Finset.range (k + 1), ((Ideal.absNorm v.asIdeal : ℕ) : ENNReal) ^ i) *
        μ (AutomorphicForm.localIntegralSet K v) := by
  classical
  letI := AutomorphicForm.localGLBorel K v
  haveI := AutomorphicForm.borelSpace_localGLBorel K v
  haveI : MeasurableMul (GL (Fin 2) 𝕂) := inferInstance
  haveI := hμ
  have hU : MeasurableSet (unitGrp K v : Set (GL (Fin 2) 𝕂)) :=
    (AutomorphicForm.isOpen_localIntegralSet K v).measurableSet
  rw [shell_eq_iUnion, measure_biUnion_finset (by rw [Finset.coe_univ]; exact pairwiseDisjoint_smul K v k)
    (fun i _ => HeckeIntegralSeam.measurableSet_smul_coe hU (rep K v k i))]
  simp only [HeckeIntegralSeam.measure_smul_coe μ]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_Idx]
  push_cast
  rfl

end AutomorphicForm.LocalDetShell
p2m_reactivate "P2MW.S_AutomorphicForm_measure_setOf_integral_valuation_det_eq_geom_sum_absNorm_mul_measure_localIntegralSet.AutomorphicForm P2MW.S_AutomorphicForm_measure_setOf_integral_valuation_det_eq_geom_sum_absNorm_mul_measure_localIntegralSet.AutomorphicForm.LocalDetShell"
p2m_reactivate "P2MW.S_AutomorphicForm_measure_setOf_integral_valuation_det_eq_geom_sum_absNorm_mul_measure_localIntegralSet.AutomorphicForm"

end
p2m_reactivate "P2MW.S_AutomorphicForm_measure_setOf_integral_valuation_det_eq_geom_sum_absNorm_mul_measure_localIntegralSet.AutomorphicForm P2MW.S_AutomorphicForm_measure_setOf_integral_valuation_det_eq_geom_sum_absNorm_mul_measure_localIntegralSet.AutomorphicForm.LocalDetShell"

open MeasureTheory NumberField IsDedekindDomain in

theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (μ : @Measure (GL (Fin 2) (v.adicCompletion K)) (AutomorphicForm.localGLBorel K v))
    (hμ : @Measure.IsMulLeftInvariant (GL (Fin 2) (v.adicCompletion K))
      (AutomorphicForm.localGLBorel K v) _ μ)
    (k : ℕ) :
    μ {g : GL (Fin 2) (v.adicCompletion K) |
        (∀ i j, (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j ∈ v.adicCompletionIntegers K) ∧
          Valued.v ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion K)ˣ) : v.adicCompletion K) =
            WithZero.exp (-(k : ℤ))} =
      (∑ i ∈ Finset.range (k + 1), ((Ideal.absNorm v.asIdeal : ℕ) : ENNReal) ^ i) *
        μ (AutomorphicForm.localIntegralSet K v) :=
  AutomorphicForm.LocalDetShell.measure_shell K v μ hμ k

end S_AutomorphicForm_measure_setOf_integral_valuation_det_eq_geom_sum_absNorm_mul_measure_localIntegralSet
end P2MW
export P2MW.S_AutomorphicForm_measure_setOf_integral_valuation_det_eq_geom_sum_absNorm_mul_measure_localIntegralSet (solution)
