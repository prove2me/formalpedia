-- Prove2me | Definitions.Def_RPLib_S1_LiUnit
-- name    : RPLib_S1_LiUnit
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-13T05:40:54.128211+00:00
-- url     : https://prove2.me/theorems/237d3150-568e-4263-8d5c-9233fa912c76
-- title:
--   The bound $|a_p| \le p^{(k-1)/2}$ for newforms at primes dividing the level
-- statement:
--   Let $f$ be a newform of level $M$, weight $k$ and nebentypus $\chi$, and $p \mid M$ a prime. If $\chi$ is not defined modulo $M/p$, then $U_p$ is $p^{(k-1)/2}$ times a unitary operator on $S_k(M,\chi)$, so $|a_p(f)| = p^{(k-1)/2}$. In all cases $$|a_p(f)| \le p^{(k-1)/2}.$$ This is the Ramanujan-Petersson bound at the primes dividing the level.
--
--   **Formalization note.** This file is a library module of a formalization of the Ramanujan-Petersson conjecture for holomorphic cusp forms on $\Gamma_1(M)$. It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   W.-C. W. Li, Newforms and functional equations, Math. Ann. 212 (1975) 285-315, doi:10.1007/BF01344468, Theorem 3

import Mathlib
import Definitions.Def_RPLib_S1_Adjoint
import Definitions.Def_RPLib_S1_LiTrace

set_option autoImplicit false

/-! # S1-LI-UNIT: Li's bad-prime bound `|a_p| = p^((k-1)/2)` when `χ` is not defined mod `M/p` (U_p is p^((k-1)/2) times a unitary map), and the combined bound `norm_coeff_prime_le_all` used by N2. -/

open MeasureTheory Set Matrix Matrix.SpecialLinearGroup UpperHalfPlane ModularGroup ModularForm
open scoped MatrixGroups Modular Pointwise ComplexConjugate

noncomputable section

namespace RP.LiUnit

open RP.FundDomain RP.Petersson RP.Adjoint
open RamanujanPetersson RamanujanPetersson.Diamond RamanujanPetersson.Hecke CongruenceSubgroup

/-- `M(j,v) = repU p j * [[p,0],[p L v,1]] = [[p(1 + L j v), j],[p^2 L v, p]]` (level `M = p L`). -/
def mJV (p L j v : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![p * (1 + L * j * v), j; p ^ 2 * L * v, p]

/-- The connecting matrix `X` with `X * M(j,v) = M(j',v')`. -/
def xMat (p L j v j' v' q : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![1 + L * j' * (v' - v), q; p * L * (v' - v), 1 + L * j * (v - v')]

theorem repU_mul_delta (p L : ℕ) (j : ℕ) (v : ℤ) :
    repU p j * !![(p : ℤ), 0; (p : ℤ) * L * v, 1] = mJV p L j v := by
  ext i k
  fin_cases i <;> fin_cases k <;> simp [repU, mJV, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem xMat_mul (p L j v j' v' q : ℤ) (hq : p * q = j' - j + L * j * j' * (v - v')) :
    xMat p L j v j' v' q * mJV p L j v = mJV p L j' v' := by
  ext i k
  fin_cases i <;> fin_cases k <;> simp [xMat, mJV, Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | ring1 | linear_combination hq | linear_combination (p * L * v) * hq

theorem xMat_det (p L j v j' v' q : ℤ) (hq : p * q = j' - j + L * j * j' * (v - v')) :
    (xMat p L j v j' v' q).det = 1 := by
  rw [xMat, Matrix.det_fin_two_of]
  linear_combination (-(L * (v' - v))) * hq


theorem mJV_det (p L j v : ℤ) : (mJV p L j v).det = p ^ 2 := by
  rw [mJV, Matrix.det_fin_two_of]; ring

/-! ### Step 1: the adjoint of `U_p` for `p ∣ M` -/

instance neZero_of_fact_prime {p : ℕ} [hp : Fact p.Prime] : NeZero p := ⟨hp.out.ne_zero⟩

section Step1

variable {M p : ℕ} [hp : Fact p.Prime]

/-- `δ_v = [[p, 0], [M v, 1]]`. -/
def deltaM (M p : ℕ) (v : ZMod p) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![(p : ℤ), 0; (M : ℤ) * (v.val : ℤ), 1]

omit hp in
lemma det_deltaM (v : ZMod p) : (deltaM M p v).det = p := by
  rw [deltaM, Matrix.det_fin_two_of]; ring

lemma det_deltaM_ne (v : ZMod p) : (deltaM M p v).det ≠ 0 := by
  rw [det_deltaM]; exact_mod_cast hp.out.ne_zero

/-- `[[1, 0], [M v, 1]] ∈ Γ₁(M)`. -/
def lowerM (M p : ℕ) (v : ZMod p) : SL(2, ℤ) :=
  ⟨!![1, 0; (M : ℤ) * (v.val : ℤ), 1], by rw [Matrix.det_fin_two_of]; ring⟩

omit hp in
lemma lowerM_mem (v : ZMod p) : lowerM M p v ∈ Gamma1 M :=
  mem_Gamma1_of _ (by simp [lowerM]) (by simp [lowerM])

omit hp in
lemma deltaM_eq_mul (v : ZMod p) :
    deltaM M p v = diagP p * ((lowerM M p v : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
  ext i l
  fin_cases i <;> fin_cases l <;> simp [deltaM, diagP, lowerM, Matrix.mul_apply, Fin.sum_univ_two]

lemma hexU (hpM : p ∣ M) :
    ∀ γ ∈ (Gamma1 M : Subgroup (GL (Fin 2) ℝ)), ∃ r : Fin p,
      ∃ δ ∈ (Gamma1 M : Subgroup (GL (Fin 2) ℝ)),
        alphaP p * γ = δ * toGL (repU p r) (det_repU_ne r) := by
  rintro _ ⟨γ, hγ, rfl⟩
  have hA := isDelta_repU0_mul (p := p) hγ
  obtain ⟨j, hj, hc⟩ := exists_condU hA.1 (not_condInf_of_dvd hpM hA)
  obtain ⟨δ, hδ, he⟩ := factor_U hA hc
  refine ⟨⟨j, hj⟩, mapGL ℝ δ, ⟨δ, hδ, rfl⟩, ?_⟩
  rw [alphaP, toGL_mul_mapGL, mapGL_mul_toGL]
  exact toGL_congr _ _ he.symm

lemma huniqU :
    ∀ r s : Fin p, ∀ δ ∈ (Gamma1 M : Subgroup (GL (Fin 2) ℝ)),
      toGL (repU p r) (det_repU_ne r) = δ * toGL (repU p s) (det_repU_ne s) → r = s := by
  rintro r s _ ⟨δ, -, rfl⟩ h
  rw [mapGL_mul_toGL] at h
  have he := Hecke.toGL_injective _ _ _ _ h
  have h1 : CondU p (repU p r) r := by
    have := condU_of_mul (p := p) 1 r
    rwa [Matrix.one_mul] at this
  have h2 : CondU p (repU p r) s := by
    rw [he]; exact condU_of_mul _ s
  exact Fin.ext (condU_unique (det_repU p r) r.2 s.2 h1 h2)

lemma hmemU :
    ∀ r : Fin p, ∃ γ ∈ (Gamma1 M : Subgroup (GL (Fin 2) ℝ)),
      ∃ δ ∈ (Gamma1 M : Subgroup (GL (Fin 2) ℝ)),
        toGL (repU p r) (det_repU_ne r) = δ * alphaP p * γ := fun r =>
  ⟨_, ⟨_, gammaT_mem (M := M) ((r : ℕ) : ℤ), rfl⟩, 1, Subgroup.one_mem _, by
    rw [one_mul, alphaP, toGL_mul_mapGL]; exact toGL_congr _ _ (repU_eq_mul (p := p) r)⟩

lemma hexD (hpM : p ∣ M) :
    ∀ γ ∈ (Gamma1 M : Subgroup (GL (Fin 2) ℝ)), ∃ r : ZMod p,
      ∃ δ ∈ (Gamma1 M : Subgroup (GL (Fin 2) ℝ)),
        alphaD p * γ = δ * toGL (deltaM M p r) (det_deltaM_ne r) := by
  rintro _ ⟨γ, hγ, rfl⟩
  obtain ⟨h00, h11, h10⟩ := (Gamma1_mem M γ).1 hγ
  obtain ⟨c1, hc1⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h10
  have hd : ((γ 1 1 : ℤ) : ZMod p) = 1 := by
    have := congrArg (ZMod.castHom hpM (ZMod p)) h11
    rwa [map_intCast, map_one] at this
  have hq : (p : ℤ) ∣ c1 - γ 1 1 * (((c1 : ZMod p).val : ℕ) : ℤ) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hd, ZMod.natCast_zmod_val, one_mul, sub_self]
  obtain ⟨q, hq⟩ := hq
  have hdet := Matrix.SpecialLinearGroup.det_coe γ
  rw [Matrix.det_fin_two] at hdet
  set v : ZMod p := (c1 : ZMod p) with hv
  let δ : SL(2, ℤ) := ⟨!![γ 0 0 - γ 0 1 * M * (v.val : ℤ), p * γ 0 1; M * q, γ 1 1], by
    rw [Matrix.det_fin_two_of]
    linear_combination hdet + γ 0 1 * hc1 + γ 0 1 * (M : ℤ) * hq⟩
  have hδ : δ ∈ Gamma1 M := mem_Gamma1_of δ (by simpa [δ] using h00) (by simp [δ])
  refine ⟨v, mapGL ℝ δ, ⟨δ, hδ, rfl⟩, ?_⟩
  rw [alphaD, toGL_mul_mapGL, mapGL_mul_toGL]
  apply toGL_congr
  ext i l
  fin_cases i <;> fin_cases l <;>
    simp [δ, diagP, deltaM, Matrix.mul_apply, Fin.sum_univ_two, -ZMod.natCast_val] <;>
    first | ring1 | linear_combination hc1 + (M : ℤ) * hq | linear_combination -hc1 - (M : ℤ) * hq

lemma huniqD [NeZero M] :
    ∀ r s : ZMod p, ∀ δ ∈ (Gamma1 M : Subgroup (GL (Fin 2) ℝ)),
      toGL (deltaM M p r) (det_deltaM_ne r) = δ * toGL (deltaM M p s) (det_deltaM_ne s) →
        r = s := by
  rintro r s _ ⟨δ, hδ, rfl⟩ h
  rw [mapGL_mul_toGL] at h
  have he := Hecke.toGL_injective _ _ _ _ h
  obtain ⟨-, -, h10⟩ := (Gamma1_mem M δ).1 hδ
  obtain ⟨t, ht⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h10
  have e11 : (1 : ℤ) = δ 1 1 := by
    have := congrFun (congrFun he 1) 1
    simpa [deltaM, Matrix.mul_apply, Fin.sum_univ_two] using this
  have e10 : (M : ℤ) * (r.val : ℤ) = δ 1 0 * p + δ 1 1 * ((M : ℤ) * (s.val : ℤ)) := by
    have := congrFun (congrFun he 1) 0
    simpa [deltaM, Matrix.mul_apply, Fin.sum_univ_two] using this
  have hM0 : (M : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne M
  have key : (r.val : ℤ) = p * t + s.val := by
    apply mul_left_cancel₀ hM0
    rw [ht, ← e11] at e10
    linear_combination e10
  have := congrArg (fun z : ℤ => (z : ZMod p)) key
  simpa using this

lemma hmemD :
    ∀ r : ZMod p, ∃ γ ∈ (Gamma1 M : Subgroup (GL (Fin 2) ℝ)),
      ∃ δ ∈ (Gamma1 M : Subgroup (GL (Fin 2) ℝ)),
        toGL (deltaM M p r) (det_deltaM_ne r) = δ * alphaD p * γ := fun r =>
  ⟨_, ⟨_, lowerM_mem r, rfl⟩, 1, Subgroup.one_mem _, by
    rw [one_mul, alphaD, toGL_mul_mapGL]; exact toGL_congr _ _ (deltaM_eq_mul r)⟩

variable [NeZero M]

/-- `U_p f = Σ_{q ∈ Γ₁/(Γ₁ ∩ α⁻¹Γ₁α)} f ∣ α q⁻¹` for `p ∣ M`. -/
theorem heckeFun_eq_sum_out_dvd (k : ℤ) (hpM : p ∣ M)
    [Fintype (CosetQ (Gamma1 M) (interConj (Gamma1 M) (alphaP p)))] (f : S1 M k) :
    heckeFun p k f = ∑ q : CosetQ (Gamma1 M) (interConj (Gamma1 M) (alphaP p)),
      ⇑f ∣[k] (alphaP p * (q.out : GL (Fin 2) ℝ)⁻¹) := by
  rw [heckeFun_eq_sum_dvd k hpM]
  exact (sum_slash_out_eq (alphaP p) (fun j : Fin p => toGL (repU p j) (det_repU_ne j))
    (hexU hpM) huniqU hmemU k ⇑f (fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ hγ)).symm

/-- `Σ_{q} g ∣ α' q⁻¹ = Σ_{v mod p} g ∣ [[p, 0], [M v, 1]]` for `p ∣ M`. -/
theorem sum_out_alphaD_eq_dvd (k : ℤ) (hpM : p ∣ M)
    [Fintype (CosetQ (Gamma1 M) (interConj (Gamma1 M) (alphaD p)))] (g : S1 M k) :
    ∑ q : CosetQ (Gamma1 M) (interConj (Gamma1 M) (alphaD p)),
      ⇑g ∣[k] (alphaD p * (q.out : GL (Fin 2) ℝ)⁻¹) =
      ∑ v : ZMod p, ⇑g ∣[k] toGL (deltaM M p v) (det_deltaM_ne v) :=
  sum_slash_out_eq (alphaD p) (fun v : ZMod p => toGL (deltaM M p v) (det_deltaM_ne v))
    (hexD hpM) huniqD hmemD k ⇑g (fun γ hγ => SlashInvariantFormClass.slash_action_eq g γ hγ)

/-- **Adjoint of `U_p`** (`p ∣ M`): `⟪U_p f, g⟫ = ⟪f, Σ_v g ∣ [[p, 0], [M v, 1]]⟫`. -/
theorem peterssonInner_heckeT_dvd (k : ℤ) (hpM : p ∣ M) (f g : S1 M k) :
    peterssonInner (Gamma1 M) k (heckeT p k f) g =
      peterssonInner (Gamma1 M) k f
        (∑ v : ZMod p, ⇑g ∣[k] toGL (deltaM M p v) (det_deltaM_ne v)) := by
  haveI := finiteIndex_interConj_alphaP (M := M) (p := p)
  haveI := finiteIndex_interConj_alphaD (M := M) (p := p)
  haveI := isFiniteRelIndex_coe (Γ := Gamma1 M) (Γ' := interConj (Gamma1 M) (alphaP p))
  haveI := isFiniteRelIndex_coe (Γ := Gamma1 M) (Γ' := interConj (Gamma1 M) (alphaD p))
  let _ : Fintype (CosetQ (Gamma1 M) (interConj (Gamma1 M) (alphaP p))) := Fintype.ofFinite _
  let _ : Fintype (CosetQ (Gamma1 M) (interConj (Gamma1 M) (alphaD p))) := Fintype.ofFinite _
  haveI : (ConjAct.toConjAct (alphaP p)⁻¹ • G1 M).IsArithmetic := isArithmetic_conj_toGL _ _
  haveI : (ConjAct.toConjAct (alphaD p)⁻¹ • G1 M).IsArithmetic := isArithmetic_conj_toGL _ _
  have hf : ∀ γ ∈ (Gamma1 M : Subgroup (GL (Fin 2) ℝ)), ⇑f ∣[k] γ = ⇑f :=
    fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ hγ
  have hg : ∀ γ ∈ (Gamma1 M : Subgroup (GL (Fin 2) ℝ)), ⇑g ∣[k] γ = ⇑g :=
    fun γ hγ => SlashInvariantFormClass.slash_action_eq g γ hγ
  have s1 : peterssonInner (Gamma1 M) k g (heckeT p k f) =
      peterssonInner (interConj (Gamma1 M) (alphaP p)) k g (⇑f ∣[k] alphaP p) := by
    have h := peterssonInner_sum_slash (interConj_le (Gamma1 M) (alphaP p))
      (neg_one_mem_interConj _) g (CuspForm.translate f (alphaP p))
      (fun γ hγ => slash_interConj_eq hf (alphaP p) hγ)
    rw [coe_heckeT, heckeFun_eq_sum_out_dvd k hpM f]
    simp only [SlashAction.slash_mul]
    exact h
  have s2 : peterssonInner (interConj (Gamma1 M) (alphaD p)) k f (⇑g ∣[k] alphaD p) =
      peterssonInner (Gamma1 M) k f
        (∑ v : ZMod p, ⇑g ∣[k] toGL (deltaM M p v) (det_deltaM_ne v)) := by
    have h := peterssonInner_sum_slash (interConj_le (Gamma1 M) (alphaD p))
      (neg_one_mem_interConj _) f (CuspForm.translate g (alphaD p))
      (fun γ hγ => slash_interConj_eq hg (alphaD p) hγ)
    rw [← sum_out_alphaD_eq_dvd k hpM g]
    simp only [SlashAction.slash_mul]
    exact h.symm
  calc peterssonInner (Gamma1 M) k (heckeT p k f) g
      = conj (peterssonInner (Gamma1 M) k g (heckeT p k f)) :=
        (peterssonInner_conj_symm _ _ _).symm
    _ = conj (peterssonInner (interConj (Gamma1 M) (alphaP p)) k g (⇑f ∣[k] alphaP p)) := by
        rw [s1]
    _ = peterssonInner (interConj (Gamma1 M) (alphaP p)) k (⇑f ∣[k] alphaP p) g :=
        peterssonInner_conj_symm _ _ _
    _ = peterssonInner (interConj (Gamma1 M) (alphaD p)) k f (⇑g ∣[k] alphaD p) :=
        peterssonInner_slash_adj (alphaP p) (alphaD p) alphaP_det_pos alphaD_adj
          (fun δ hδ => slash_Gamma1 k f hδ) (fun δ hδ => slash_Gamma1 k g hδ)
    _ = _ := s2

end Step1

/-! ### Step 2: `U_p^* U_p = p^(k-1)` on `S_k(pL, χ)` when `χ` is not defined mod `L` -/

section Step2

variable {p L : ℕ} [hp : Fact p.Prime]

lemma mJV_det_ne (j v : ℤ) : (mJV p L j v).det ≠ 0 := by
  rw [mJV_det]; exact pow_ne_zero 2 (by exact_mod_cast hp.out.ne_zero)

omit hp in
lemma repU_mul_deltaM (j : ℕ) (v : ZMod p) :
    repU p j * deltaM (p * L) p v = mJV p L j v.val := by
  ext i l
  fin_cases i <;> fin_cases l <;> simp [repU, deltaM, mJV, Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring1

lemma toGL_det_val (A : Matrix (Fin 2) (Fin 2) ℤ) (hA : A.det ≠ 0) :
    (toGL A hA).det.val = (A.det : ℝ) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, Matrix.det_fin_two]
  simp only [toGL_apply]
  push_cast
  ring

lemma mJV_det_pos (j v : ℤ) : 0 < (toGL (mJV p L j v) (mJV_det_ne j v)).det.val := by
  rw [toGL_det_val, mJV_det]
  have : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  push_cast
  positivity

lemma sum_fin_eq_sum_zmod {α : Type*} [AddCommMonoid α] (F : ℕ → α) :
    ∑ j : Fin p, F j = ∑ j : ZMod p, F j.val := by
  rcases p with _ | m
  · exact absurd hp.out Nat.not_prime_zero
  · rfl

variable {k : ℤ}

lemma slash_repU_deltaM (h : S1 (p * L) k) (j : ℕ) (v : ZMod p) :
    (⇑h ∣[k] toGL (repU p j) (det_repU_ne j)) ∣[k] toGL (deltaM (p * L) p v) (det_deltaM_ne v) =
      ⇑h ∣[k] toGL (mJV p L j v.val) (mJV_det_ne _ _) := by
  rw [← SlashAction.slash_mul, ← toGL_mul _ _ (det_repU_ne j) (det_deltaM_ne v)
    (by rw [Matrix.det_mul]; exact mul_ne_zero (det_repU_ne j) (det_deltaM_ne v))]
  rw [toGL_congr _ (mJV_det_ne (L := L) _ _) (repU_mul_deltaM j v)]

/-- The `j = 0` terms: `M(0, v) = p · [[1, 0], [p L v, 1]]`. -/
lemma slash_mJV_zero (h : S1 (p * L) k) (j v : ℤ) (hj : j = 0) :
    ⇑h ∣[k] toGL (mJV p L j v) (mJV_det_ne j v) = ((p : ℂ) ^ (k - 2)) • ⇑h := by
  subst hj
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  let low : SL(2, ℤ) := ⟨!![1, 0; (p : ℤ) * L * v, 1], by rw [Matrix.det_fin_two_of]; ring⟩
  have hlow : low ∈ Gamma1 (p * L) :=
    mem_Gamma1_of _ (by simp [low]) (by
      show (((p : ℤ) * L * v : ℤ) : ZMod (p * L)) = 0
      push_cast
      rw [← Nat.cast_mul, ZMod.natCast_self, zero_mul])
  have he : toGL (mJV p L 0 v) (mJV_det_ne 0 v) =
      mapGL ℝ low * Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (p : ℝ) hp0) := by
    rw [← toGL_SL low (det_SL_ne low)]
    refine Matrix.GeneralLinearGroup.ext fun i l => ?_
    rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.mul_diagonal, toGL_apply, toGL_apply]
    fin_cases i <;> fin_cases l <;> simp [mJV, low] <;> ring1
  have hl : ⇑h ∣[k] mapGL ℝ low = ⇑h := slash_Gamma1 k h hlow
  rw [he, SlashAction.slash_mul, hl, slash_scalar k _ (by simpa using hp.out.pos)]
  simp

theorem slash_mJV_twist {χ : DirichletCharacter ℂ (p * L)} {h : S1 (p * L) k}
    (hh : h ∈ chiSubspace k χ) (j v j' v' q : ℤ)
    (hq : (p : ℤ) * q = j' - j + L * j * j' * (v - v')) :
    ⇑h ∣[k] toGL (mJV p L j' v') (mJV_det_ne j' v') =
      χ (((1 + L * j * (v - v') : ℤ) : ZMod (p * L))) •
        (⇑h ∣[k] toGL (mJV p L j v) (mJV_det_ne j v)) := by
  let X : SL(2, ℤ) := ⟨xMat p L j v j' v' q, xMat_det p L j v j' v' q hq⟩
  have hX : X ∈ Gamma0 (p * L) := by
    rw [Gamma0_mem]
    show (((p : ℤ) * L * (v' - v) : ℤ) : ZMod (p * L)) = 0
    push_cast
    rw [← Nat.cast_mul, ZMod.natCast_self, zero_mul]
  have he : toGL (mJV p L j' v') (mJV_det_ne j' v') = mapGL ℝ X * toGL (mJV p L j v) (mJV_det_ne j v) := by
    rw [mapGL_mul_toGL]
    exact toGL_congr _ _ (xMat_mul p L j v j' v' q hq).symm
  have h1 : ⇑h ∣[k] mapGL ℝ X = χ (((X 1 1 : ℤ)) : ZMod (p * L)) • ⇑h := hh X hX
  rw [he, SlashAction.slash_mul, h1, smul_slash_of_det_pos k _ (mJV_det_pos j v)]
  rfl

end Step2


/-! ### Step 2 (main): the `j ≠ 0` terms cancel -/

section Step2Main

variable {p L : ℕ} [hp : Fact p.Prime] {k : ℤ}

lemma zmod_key1 (j v τ ℓ c : ZMod p) (hcdef : c = 1 + ℓ * τ) (hj : j ≠ 0) (hc : c ≠ 0) :
    j * c⁻¹ - j + ℓ * j * (j * c⁻¹) * (v - (v - τ * j⁻¹)) = 0 := by
  have e1 : j * j⁻¹ = 1 := mul_inv_cancel₀ hj
  have e2 : c * c⁻¹ = 1 := mul_inv_cancel₀ hc
  subst hcdef
  linear_combination j * e2 + ℓ * τ * j * (1 + ℓ * τ)⁻¹ * e1

lemma zmod_key2 (j v τ : ZMod p) (hj : j ≠ 0) : τ - j * (v - (v - τ * j⁻¹)) = 0 := by
  have e1 : j * j⁻¹ = 1 := mul_inv_cancel₀ hj
  linear_combination (-τ) * e1

/-- `σ(j, v) = (j c⁻¹, v - τ j⁻¹)`. -/
def sigmaPerm (c τ : ZMod p) (hc : c ≠ 0) : ZMod p × ZMod p ≃ ZMod p × ZMod p where
  toFun x := (x.1 * c⁻¹, x.2 - τ * x.1⁻¹)
  invFun y := (y.1 * c, y.2 + τ * (y.1 * c)⁻¹)
  left_inv x := by
    ext
    · simp [hc]
    · simp [hc]
  right_inv y := by
    ext
    · simp [hc]
    · simp [hc]

/-- `T(j, v) = h ∣ M(j, v)`. -/
def termT (k : ℤ) (h : S1 (p * L) k) (j v : ZMod p) : ℍ → ℂ :=
  ⇑h ∣[k] toGL (mJV p L j.val v.val) (mJV_det_ne _ _)

/-- `G(j, v) = [j ≠ 0] T(j, v)`. -/
def termG (k : ℤ) (h : S1 (p * L) k) (x : ZMod p × ZMod p) : ℍ → ℂ :=
  if x.1 = 0 then 0 else termT k h x.1 x.2

theorem sum_termT_zero (h : S1 (p * L) k) :
    ∑ v : ZMod p, termT k h 0 v = ((p : ℂ) ^ (k - 1)) • ⇑h := by
  have h1 : ∀ v : ZMod p, termT k h 0 v = ((p : ℂ) ^ (k - 2)) • ⇑h :=
    fun v => slash_mJV_zero h _ _ (by simp)
  simp only [h1, Finset.sum_const, Finset.card_univ, ZMod.card, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  congr 1
  rw [← zpow_one_add₀ (by exact_mod_cast hp.out.ne_zero : (p : ℂ) ≠ 0)]
  congr 1
  ring

variable [NeZero (p * L)]

theorem sum_termG_eq_zero {χ : DirichletCharacter ℂ (p * L)} {h : S1 (p * L) k}
    (hh : h ∈ chiSubspace k χ) (t : ℤ) (u : (ZMod (p * L))ˣ)
    (hu : ((1 + L * t : ℤ) : ZMod (p * L)) = u) (hχu : χ (u : ZMod (p * L)) ≠ 1) :
    ∑ x : ZMod p × ZMod p, termG k h x = 0 := by
  have hpM : p ∣ p * L := dvd_mul_right p L
  obtain ⟨c, hcdef⟩ : ∃ c : ZMod p, c = 1 + (L : ZMod p) * (t : ZMod p) := ⟨_, rfl⟩
  have hc : c ≠ 0 := by
    have hu' := (Units.isUnit u).map (ZMod.castHom hpM (ZMod p))
    rw [← hu, map_intCast] at hu'
    push_cast at hu'
    rw [hcdef]
    exact hu'.ne_zero
  have hGσ : ∀ x, termG k h (sigmaPerm c (t : ZMod p) hc x) = χ (u : ZMod (p * L)) • termG k h x := by
    rintro ⟨j, v⟩
    by_cases hj : j = 0
    · subst hj
      simp [termG, sigmaPerm]
    · have hj' : j * c⁻¹ ≠ 0 := mul_ne_zero hj (inv_ne_zero hc)
      show termG k h (j * c⁻¹, v - (t : ZMod p) * j⁻¹) = _
      simp only [termG]
      rw [if_neg hj', if_neg hj]
      have hdiv : (p : ℤ) ∣ (((j * c⁻¹).val : ℤ) - (j.val : ℤ) +
          (L : ℤ) * (j.val : ℤ) * ((j * c⁻¹).val : ℤ) * ((v.val : ℤ) - ((v - (t : ZMod p) * j⁻¹).val : ℤ))) := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        simp only [Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val]
        linear_combination zmod_key1 j v (t : ZMod p) (L : ZMod p) c hcdef hj hc
      obtain ⟨q, hq⟩ := hdiv
      have hX11 : (((1 + (L : ℤ) * (j.val : ℤ) * ((v.val : ℤ) - ((v - (t : ZMod p) * j⁻¹).val : ℤ)) : ℤ))
          : ZMod (p * L)) = u := by
        rw [← hu, ZMod.intCast_eq_intCast_iff_dvd_sub]
        have h2 : (p : ℤ) ∣ t - (j.val : ℤ) * ((v.val : ℤ) - ((v - (t : ZMod p) * j⁻¹).val : ℤ)) := by
          rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
          simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val]
          linear_combination zmod_key2 j v (t : ZMod p) hj
        obtain ⟨r, hr⟩ := h2
        exact ⟨r, by push_cast; linear_combination (L : ℤ) * hr⟩
      unfold termT
      rw [slash_mJV_twist hh _ _ _ _ q hq.symm, hX11]
  have hsum := Equiv.sum_comp (sigmaPerm c (t : ZMod p) hc) (termG k h)
  simp only [hGσ, ← Finset.smul_sum] at hsum
  have h0 : (χ (u : ZMod (p * L)) - 1) • ∑ x, termG k h x = 0 := by
    rw [sub_smul, one_smul, hsum, sub_self]
  exact (smul_eq_zero.1 h0).resolve_left (sub_ne_zero.2 hχu)

/-- **Step 2**: `Σ_v (U_p h) ∣ [[p, 0], [pL v, 1]] = p^(k-1) h` on `S_k(pL, χ)` when `χ(u) ≠ 1` for some
`u ≡ 1 mod L`. -/
theorem sum_heckeFun_deltaM {χ : DirichletCharacter ℂ (p * L)} {h : S1 (p * L) k}
    (hh : h ∈ chiSubspace k χ) (t : ℤ) (u : (ZMod (p * L))ˣ)
    (hu : ((1 + L * t : ℤ) : ZMod (p * L)) = u) (hχu : χ (u : ZMod (p * L)) ≠ 1) :
    ∑ v : ZMod p, heckeFun p k h ∣[k] toGL (deltaM (p * L) p v) (det_deltaM_ne v) =
      ((p : ℂ) ^ (k - 1)) • ⇑h := by
  have hpM : p ∣ p * L := dvd_mul_right p L
  have hterm : ∀ v : ZMod p, heckeFun p k h ∣[k] toGL (deltaM (p * L) p v) (det_deltaM_ne v) =
      ∑ j : ZMod p, termT k h j v := by
    intro v
    rw [heckeFun_eq_sum_dvd k hpM h, SlashAction.sum_slash]
    refine (Finset.sum_congr rfl fun (j : Fin p) _ => slash_repU_deltaM h (j : ℕ) v).trans ?_
    exact sum_fin_eq_sum_zmod (fun n : ℕ => ⇑h ∣[k] toGL (mJV p L (n : ℤ) v.val) (mJV_det_ne _ _))
  have hsplit : ∀ j v : ZMod p, termT k h j v = (if j = 0 then termT k h j v else 0) + termG k h (j, v) := by
    intro j v
    by_cases hj : j = 0 <;> simp [termG, hj]
  simp only [hterm]
  rw [Finset.sum_comm]
  calc ∑ j : ZMod p, ∑ v : ZMod p, termT k h j v
      = ∑ j : ZMod p, ∑ v : ZMod p, ((if j = 0 then termT k h j v else 0) + termG k h (j, v)) :=
        Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun v _ => hsplit j v
    _ = ∑ j : ZMod p, ∑ v : ZMod p, (if j = 0 then termT k h j v else 0) +
          ∑ x : ZMod p × ZMod p, termG k h x := by
        rw [Fintype.sum_prod_type]
        simp only [Finset.sum_add_distrib]
    _ = ∑ v : ZMod p, termT k h 0 v + 0 := by
        congr 1
        · rw [Fintype.sum_eq_single 0 (fun j hj => by simp [hj])]
          simp
        · exact sum_termG_eq_zero hh t u hu hχu
    _ = _ := by rw [add_zero, sum_termT_zero]

end Step2Main

/-! ### Step 3: `|a_p| = p^((k-1)/2)` when `χ` is not defined mod `M/p` -/

theorem norm_coeff_prime_eq_of_not_factorsThrough {M p : ℕ} [NeZero M] [hp : Fact p.Prime]
    (hpM : p ∣ M) {k : ℤ} {χ : DirichletCharacter ℂ M} (hχ : ¬ χ.FactorsThrough (M / p))
    {F : S1 M k} (hF : RP.Newforms.IsNewform χ F) :
    ‖(qExpansion 1 F).coeff p‖ = (p : ℝ) ^ (((k : ℝ) - 1) / 2) := by
  obtain ⟨L, rfl⟩ := hpM
  have hpM : p ∣ p * L := dvd_mul_right p L
  have hL : p * L / p = L := Nat.mul_div_cancel_left L hp.out.pos
  rw [hL] at hχ
  have hLd : L ∣ p * L := dvd_mul_left L p
  rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap hLd] at hχ
  obtain ⟨u, hu1, hu2⟩ := SetLike.not_le_iff_exists.1 hχ
  have hχu : χ (u : ZMod (p * L)) ≠ 1 := by
    intro h1
    apply hu2
    rw [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one]
    exact h1
  have hUu : ((((u : ZMod (p * L)).val : ℤ)) : ZMod (p * L)) = u := by
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  have hu1' : (ZMod.castHom hLd (ZMod L)) (u : ZMod (p * L)) = 1 := by
    have h2 := congrArg Units.val ((MonoidHom.mem_ker).1 hu1)
    rw [ZMod.unitsMap_def, Units.coe_map, Units.val_one] at h2
    exact h2
  rw [← hUu, map_intCast] at hu1'
  have hUL : (L : ℤ) ∣ ((u : ZMod (p * L)).val : ℤ) - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, hu1', Int.cast_one, sub_self]
  obtain ⟨t, ht⟩ := hUL
  have hu : ((1 + L * t : ℤ) : ZMod (p * L)) = u := by
    rw [← hUu]
    congr 1
    linear_combination -ht
  set a := (qExpansion 1 F).coeff p with ha
  have hU : heckeT p k F = a • F := hF.heckeT_eq_of_dvd p hpM
  have key : conj a * (a * peterssonInner (Gamma1 (p * L)) k F F) =
      (p : ℂ) ^ (k - 1) * peterssonInner (Gamma1 (p * L)) k F F := by
    have h1 := peterssonInner_heckeT_dvd k hpM F (heckeT p k F)
    have h2 : (∑ v : ZMod p, ⇑(heckeT p k F) ∣[k] toGL (deltaM (p * L) p v) (det_deltaM_ne v)) =
        ((p : ℂ) ^ (k - 1)) • ⇑F := sum_heckeFun_deltaM hF.mem_chi t u hu hχu
    rw [h2, ← FunLike.coe_smul, peterssonInner_smul_right, hU, peterssonInner_smul_left,
      peterssonInner_smul_right] at h1
    exact h1
  have hI : peterssonInner (Gamma1 (p * L)) k F F ≠ 0 := by
    intro h0
    have hF0 := eq_zero_of_peterssonInner_self_eq_zero F h0
    have h1 := hF.coeff_one
    have h00 := coeff_smul_Gamma1 k (0 : ℂ) (0 : S1 (p * L) k) 1
    rw [zero_smul, zero_mul] at h00
    rw [hF0, h00] at h1
    exact zero_ne_one h1
  have h3 : conj a * a = (p : ℂ) ^ (k - 1) := by
    have h4 : (conj a * a - (p : ℂ) ^ (k - 1)) * peterssonInner (Gamma1 (p * L)) k F F = 0 := by
      linear_combination key
    exact sub_eq_zero.1 ((mul_eq_zero.1 h4).resolve_right hI)
  rw [Complex.conj_mul'] at h3
  have hpos : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have h4 : ‖a‖ ^ 2 = (p : ℝ) ^ (k - 1) := by
    apply Complex.ofReal_injective
    push_cast
    exact h3
  have h5 : ((p : ℝ) ^ (((k : ℝ) - 1) / 2)) ^ 2 = (p : ℝ) ^ (k - 1) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hpos.le, ← Real.rpow_intCast]
    congr 1
    push_cast
    ring
  exact (pow_left_inj₀ (norm_nonneg _) (Real.rpow_nonneg hpos.le _) two_ne_zero).1 (h4.trans h5.symm)

/-! ### Step 4: the bad-prime bound used by N2 -/

/-- **Li's bad-prime bound**: for every newform `F` of level `M`, character `χ`, and prime `p ∣ M`,
`‖a_p(F)‖ ≤ p^((k-1)/2)`. -/
theorem norm_coeff_prime_le_all {M p : ℕ} [NeZero M] [Fact p.Prime] (hpM : p ∣ M) {k : ℤ}
    {χ : DirichletCharacter ℂ M} {F : S1 M k} (hF : RP.Newforms.IsNewform χ F) :
    ‖(qExpansion 1 F).coeff p‖ ≤ (p : ℝ) ^ (((k : ℝ) - 1) / 2) := by
  by_cases hχ : χ.FactorsThrough (M / p)
  · exact RP.LiTrace.norm_coeff_prime_le hpM hχ hF
  · exact (norm_coeff_prime_eq_of_not_factorsThrough hpM hχ hF).le

end RP.LiUnit


