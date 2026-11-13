-- Prove2me | Definitions.Def_RPLib_S1_MainLemma
-- name    : RPLib_S1_MainLemma
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-13T05:23:06.177801+00:00
-- url     : https://prove2.me/theorems/87a1b809-ef49-449c-9c3b-931c35bd1f53
-- title:
--   The Main Lemma of Atkin-Lehner-Li theory on $\Gamma_1(N)$
-- statement:
--   If $f \in S_k(\Gamma_1(N))$ satisfies $a_n(f) = 0$ for all $n$ coprime to $N$, then $$f = \sum_{p \mid N} \iota_p\, g_p, \qquad g_p \in S_k(\Gamma_1(N/p)).$$ If moreover $f \in S_k(N,\chi)$, the $g_p$ can be chosen with nebentypus inducing $\chi$, and $g_p = 0$ when $\chi$ is not defined modulo $N/p$. This is the key input for multiplicity one and the theory of newforms.
--
--   **Formalization note.** This file is a library module of a formalization of the Ramanujan-Petersson conjecture for holomorphic cusp forms on $\Gamma_1(M)$. It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   F. Diamond and J. Shurman, A First Course in Modular Forms, GTM 228, Springer 2005, doi:10.1007/978-0-387-27226-9, Theorem 5.7.1; A. O. L. Atkin and J. Lehner, Hecke operators on Gamma_0(m), Math. Ann. 185 (1970) 134-160, doi:10.1007/BF01359701

import Mathlib
import Definitions.Def_RPLib_S1_MainLemmaAlg
import Definitions.Def_RPLib_S1_MainLemmaA
import Definitions.Def_RPLib_S1_QExp
import Definitions.Def_RPLib_S1_FinDim
import Definitions.Def_RPLib_S1_Diamond

/-!
# S1-MAINLEMMA-B: the Atkin-Lehner-Li Main Lemma on `Γ₁(N)` (Diamond-Shurman Thm 5.7.1)

Petersson-free proof (Carlton's representation-theoretic argument): the finite group `SL(2,ℤ)/Γ(N)` acts on
`S_k(D⁻¹Γ(N)D)`, `D = diag(N,1)`; the coefficient projections `a_n ↦ [p ∣ n] a_n` are averages over cyclic
subgroups, and the kernel-of-product lemma `MainLemmaB.mem_iSup_of_avg` (Def_RPLib_S1_MainLemmaAlg) splits `f`;
each piece descends by `MainLemmaA.exists_descent`.

Main results (namespace `RamanujanPetersson.MainLemma`):
* `mainLemma`: `f ∈ S_k(Γ₁(N))`, `a_n(f) = 0` for `(n, N) = 1` ⇒ `f = Σ_{p ∣ N} ι_p(g_p)`, `g_p ∈ S_k(Γ₁(N/p))`;
* `mainLemma_mem_iSup`: the same as membership in `⨆ p ∈ N.primeFactors, range (iotaP N p k)`;
* `mainLemma_chi`, `mainLemma_chi_exists`: the `χ`-version (`g_p ∈ S_k(N/p, ψ)` with `ψ.changeLevel = χ`,
  `g_p = 0` when `χ` does not factor through level `N/p`).
-/

open UpperHalfPlane ModularForm CongruenceSubgroup ConjAct
open scoped Real MatrixGroups Pointwise InnerProductSpace
open RamanujanPetersson.Level RamanujanPetersson.MainLemmaA RamanujanPetersson.MainLemmaB

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.MainLemma

section setup

variable (N : ℕ) [NeZero N]

/-- `H = Γ₁(N) ∩ Γ₀(N²)`, which equals `D⁻¹ Γ(N) D` for `D = diag(N, 1)`. -/
def HZ : Subgroup SL(2, ℤ) := Gamma1 N ⊓ Gamma0 (N * N)

instance : (HZ N).FiniteIndex := by unfold HZ; infer_instance

/-- `H` inside `GL(2, ℝ)`. -/
abbrev HG : Subgroup (GL (Fin 2) ℝ) := ((HZ N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

/-- `D⁻¹ γ D`. -/
def cj (γ : SL(2, ℤ)) : GL (Fin 2) ℝ := (dg N)⁻¹ * Matrix.SpecialLinearGroup.mapGL ℝ γ * dg N

lemma cj_one : cj N 1 = 1 := by simp [cj]

lemma cj_mul (a b : SL(2, ℤ)) : cj N (a * b) = cj N a * cj N b := by
  simp only [cj, map_mul]
  group

lemma cj_det (γ : SL(2, ℤ)) : (cj N γ).det = 1 := by
  simp only [cj, map_mul, map_inv, Matrix.SpecialLinearGroup.det_mapGL, mul_one, inv_mul_cancel]

lemma cj_det_pos (γ : SL(2, ℤ)) : 0 < (cj N γ).det.val := by
  rw [cj_det]
  exact one_pos

lemma conj_of_mem_HZ {h : SL(2, ℤ)} (hh : h ∈ HZ N) :
    ∃ h' ∈ Gamma N, Matrix.SpecialLinearGroup.mapGL ℝ h' =
      dg N * Matrix.SpecialLinearGroup.mapGL ℝ h * (dg N)⁻¹ := by
  obtain ⟨h1, h0⟩ := Subgroup.mem_inf.mp hh
  rw [Gamma1_mem] at h1
  rw [Gamma0_mem] at h0
  obtain ⟨c', hc', hc'N⟩ :=
    exists_eq_mul_of_zmod_eq_zero (d := N) (L := N) (M := N * N) dvd_rfl h0
  obtain ⟨y, hy00, hy01, hy10, hy11, hy⟩ := exists_conj_dg N h hc'
  refine ⟨y, ?_, hy⟩
  rw [Gamma_mem, hy00, hy01, hy10, hy11]
  exact ⟨h1.1, by push_cast; simp, hc'N, h1.2.1⟩

lemma exists_conj_dg_inv (x : SL(2, ℤ)) {b' : ℤ} (hb : x 0 1 = N * b') :
    ∃ y : SL(2, ℤ), y 0 0 = x 0 0 ∧ y 0 1 = b' ∧ y 1 0 = N * x 1 0 ∧ y 1 1 = x 1 1 ∧
      Matrix.SpecialLinearGroup.mapGL ℝ y = cj N x := by
  have hdet := det_eq x
  let y : SL(2, ℤ) := ⟨!![x 0 0, b'; (N : ℤ) * x 1 0, x 1 1], by
    rw [Matrix.det_fin_two_of]
    rw [hb] at hdet
    linear_combination hdet⟩
  have hy00 : y 0 0 = x 0 0 := rfl
  have hy01 : y 0 1 = b' := rfl
  have hy10 : y 1 0 = N * x 1 0 := rfl
  have hy11 : y 1 1 = x 1 1 := rfl
  refine ⟨y, hy00, hy01, hy10, hy11, ?_⟩
  have key : dg N * Matrix.SpecialLinearGroup.mapGL ℝ y =
      Matrix.SpecialLinearGroup.mapGL ℝ x * dg N := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.SpecialLinearGroup.mapGL_coe_matrix, dg_val, Matrix.mul_apply,
        Fin.sum_univ_two, hy00, hy01, hy10, hy11, hb]
    all_goals ring
  rw [cj, mul_assoc, ← key, ← mul_assoc, inv_mul_cancel, one_mul]

lemma conj_mem_HZ {x : SL(2, ℤ)} (hx : x ∈ Gamma N) :
    ∃ y ∈ HZ N, Matrix.SpecialLinearGroup.mapGL ℝ y = cj N x := by
  rw [Gamma_mem] at hx
  obtain ⟨h00, h01, h10, h11⟩ := hx
  obtain ⟨b', hb'⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h01
  obtain ⟨c', hc'⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h10
  obtain ⟨y, hy00, -, hy10, hy11, hy⟩ := exists_conj_dg_inv N x hb'
  refine ⟨y, Subgroup.mem_inf.mpr ⟨?_, ?_⟩, hy⟩
  · rw [Gamma1_mem, hy00, hy11, hy10]
    exact ⟨h00, h11, by push_cast; simp⟩
  · rw [Gamma0_mem, hy10, hc', ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact ⟨c', by push_cast; ring⟩

lemma HG_le_conj (γ : SL(2, ℤ)) : HG N ≤ toConjAct (cj N γ)⁻¹ • HG N := by
  rintro _ ⟨h, hh, rfl⟩
  rw [map_inv, Subgroup.mem_inv_pointwise_smul_iff, toConjAct_smul]
  obtain ⟨h', hh', e1⟩ := conj_of_mem_HZ N hh
  obtain ⟨y, hy, e2⟩ := conj_mem_HZ N ((Gamma_normal N).conj_mem _ hh' γ)
  refine ⟨y, hy, ?_⟩
  rw [e2]
  simp only [cj, map_mul, map_inv, e1]
  group

omit [NeZero N] in
lemma HG_le_G1 : HG N ≤ G1 N := by
  rintro _ ⟨h, hh, rfl⟩
  exact ⟨h, (Subgroup.mem_inf.mp hh).1, rfl⟩

omit [NeZero N] in
lemma T_mem_HZ : ModularGroup.T ∈ HZ N := by
  refine Subgroup.mem_inf.mpr ⟨T_mem_Gamma1 N, ?_⟩
  rw [Gamma0_mem]
  simp [ModularGroup.T]

lemma one_mem_strictPeriods_HG : (1 : ℝ) ∈ (HG N).strictPeriods :=
  QExp.one_mem_strictPeriods_of_T_mem (T_mem_HZ N)

variable (k : ℤ)

/-- Slash by `D⁻¹ γ D` on `S_k(H)`. -/
def slashC (γ : SL(2, ℤ)) (F : CuspForm (HG N) k) : CuspForm (HG N) k :=
  let F2 := CuspForm.translate F (cj N γ)
  { toFun := F2
    slash_action_eq' := fun j hj =>
      SlashInvariantFormClass.slash_action_eq F2 j (HG_le_conj N γ hj)
    holo' := CuspFormClass.holo F2
    zero_at_cusps' := fun hc => CuspFormClass.zero_at_cusps F2 (hc.mono (HG_le_conj N γ)) }

lemma coe_slashC (γ : SL(2, ℤ)) (F : CuspForm (HG N) k) :
    ⇑(slashC N k γ F) = ⇑F ∣[k] cj N γ := rfl

/-- `slashC` as a linear map. -/
def slashL (γ : SL(2, ℤ)) : CuspForm (HG N) k →ₗ[ℂ] CuspForm (HG N) k where
  toFun := slashC N k γ
  map_add' F G := DFunLike.coe_injective (by
    simp only [coe_slashC, FunLike.coe_add, SlashAction.add_slash])
  map_smul' c F := DFunLike.coe_injective (by
    simp only [coe_slashC, FunLike.coe_smul, RingHom.id_apply, ModularForm.smul_slash, σ,
      if_pos (cj_det_pos N γ), ContinuousAlgEquiv.refl_apply])

/-- `γ ↦ (F ↦ F ∣ D⁻¹ γ⁻¹ D)`, a homomorphism. -/
def act0 : SL(2, ℤ) →* Module.End ℂ (CuspForm (HG N) k) where
  toFun γ := slashL N k γ⁻¹
  map_one' := LinearMap.ext fun F => DFunLike.coe_injective (by
    show ⇑F ∣[k] cj N 1⁻¹ = ⇑F
    rw [inv_one, cj_one, SlashAction.slash_one])
  map_mul' γ δ := LinearMap.ext fun F => DFunLike.coe_injective (by
    show ⇑F ∣[k] cj N (γ * δ)⁻¹ = (⇑F ∣[k] cj N δ⁻¹) ∣[k] cj N γ⁻¹
    rw [mul_inv_rev, cj_mul, SlashAction.slash_mul])

instance gammaNormal : (Gamma N).Normal := Gamma_normal N

/-- The action of `SL(2,ℤ)/Γ(N)` on `S_k(H)`. -/
def act : SL(2, ℤ) ⧸ Gamma N →* Module.End ℂ (CuspForm (HG N) k) :=
  QuotientGroup.lift (Gamma N) (act0 N k) (fun γ hγ => by
    rw [MonoidHom.mem_ker]
    obtain ⟨y, hy, e⟩ := conj_mem_HZ N (inv_mem hγ)
    refine LinearMap.ext fun F => DFunLike.coe_injective ?_
    show ⇑F ∣[k] cj N γ⁻¹ = ⇑F
    rw [← e]
    exact SlashInvariantFormClass.slash_action_eq F _ ⟨y, hy, rfl⟩)

lemma coe_act_mk (γ : SL(2, ℤ)) (F : CuspForm (HG N) k) :
    ⇑(act N k (γ : SL(2, ℤ) ⧸ Gamma N) F) = ⇑F ∣[k] cj N γ⁻¹ := rfl

/-! ### Lower unipotents -/

/-- `[[1, 0], [c, 1]]`. -/
def Lz (c : ℤ) : SL(2, ℤ) := ⟨!![1, 0; c, 1], by simp [Matrix.det_fin_two_of]⟩

@[simp] lemma Lz_00 (c : ℤ) : Lz c 0 0 = 1 := rfl
@[simp] lemma Lz_01 (c : ℤ) : Lz c 0 1 = 0 := rfl
@[simp] lemma Lz_10 (c : ℤ) : Lz c 1 0 = c := rfl
@[simp] lemma Lz_11 (c : ℤ) : Lz c 1 1 = 1 := rfl

omit [NeZero N] in
lemma Lz_add (a b : ℤ) : Lz (a + b) = Lz a * Lz b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Lz_00, Lz_01, Lz_10, Lz_11, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

omit [NeZero N] in
lemma Lz_zero : Lz 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Lz_00, Lz_01, Lz_10, Lz_11, Matrix.SpecialLinearGroup.coe_mul]

omit [NeZero N] in
lemma Lz_neg (a : ℤ) : Lz (-a) = (Lz a)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← Lz_add, neg_add_cancel, Lz_zero]

omit [NeZero N] in
lemma Lz_zpow (c z : ℤ) : Lz c ^ z = Lz (z * c) := by
  induction z using Int.induction_on with
  | zero => simp [Lz_zero]
  | succ n ih => rw [zpow_add_one, ih, ← Lz_add]; ring_nf
  | pred n ih => rw [zpow_sub_one, ih, ← Lz_neg, ← Lz_add]; ring_nf

lemma cj_Lz (c : ℤ) : cj N (Lz c) = Matrix.SpecialLinearGroup.mapGL ℝ (Lz (N * c)) := by
  have key : dg N * Matrix.SpecialLinearGroup.mapGL ℝ (Lz (N * c)) =
      Matrix.SpecialLinearGroup.mapGL ℝ (Lz c) * dg N := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.SpecialLinearGroup.mapGL_coe_matrix, dg_val, Matrix.mul_apply,
        Fin.sum_univ_two, Lz_00, Lz_01, Lz_10, Lz_11, Matrix.SpecialLinearGroup.coe_mul]
    all_goals ring
  rw [cj, mul_assoc, ← key, ← mul_assoc, inv_mul_cancel, one_mul]

lemma Lz_mul_mem_Gamma1 (c : ℤ) : Lz (N * c) ∈ Gamma1 N := by
  rw [Gamma1_mem]
  simp [Lz_00, Lz_01, Lz_10, Lz_11, Matrix.SpecialLinearGroup.coe_mul]

/-! ### Upper unipotents -/

lemma T_zpow_00 (m : ℤ) : (ModularGroup.T ^ m) 0 0 = 1 := by
  show (ModularGroup.T ^ m).1 0 0 = 1
  rw [ModularGroup.coe_T_zpow]; rfl
lemma T_zpow_01 (m : ℤ) : (ModularGroup.T ^ m) 0 1 = m := by
  show (ModularGroup.T ^ m).1 0 1 = m
  rw [ModularGroup.coe_T_zpow]; rfl
lemma T_zpow_10 (m : ℤ) : (ModularGroup.T ^ m) 1 0 = 0 := by
  show (ModularGroup.T ^ m).1 1 0 = 0
  rw [ModularGroup.coe_T_zpow]; rfl
lemma T_zpow_11 (m : ℤ) : (ModularGroup.T ^ m) 1 1 = 1 := by
  show (ModularGroup.T ^ m).1 1 1 = 1
  rw [ModularGroup.coe_T_zpow]; rfl

lemma cj_T_zpow (m : ℤ) (had : (1 : ℝ) * 1 ≠ 0) :
    cj N (ModularGroup.T ^ m) = QExp.upperTri 1 ((m : ℝ) / N) 1 had := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have key : dg N * QExp.upperTri 1 ((m : ℝ) / N) 1 had =
      Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.T ^ m) * dg N := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.SpecialLinearGroup.mapGL_coe_matrix, dg_val, QExp.upperTri_val,
        Matrix.mul_apply, Fin.sum_univ_two, -map_zpow, T_zpow_00, T_zpow_01, T_zpow_10, T_zpow_11]
    all_goals field_simp
  rw [cj, mul_assoc, ← key, ← mul_assoc, inv_mul_cancel, one_mul]

lemma act_T_apply (m : ℤ) (had : (1 : ℝ) * 1 ≠ 0) (F : CuspForm (HG N) k) (τ : ℍ) :
    act N k ((ModularGroup.T ^ (-m) : SL(2, ℤ)) : SL(2, ℤ) ⧸ Gamma N) F τ =
      F (QExp.upperTri 1 ((m : ℝ) / N) 1 had • τ) := by
  rw [coe_act_mk, ← zpow_neg, neg_neg, cj_T_zpow N m had, QExp.slash_translate_eq]

/-- `Lz c` and `T^m` commute modulo `Γ(N)` when `N ∣ c m`. -/
lemma commute_Lz_T {c m : ℤ} (h : (N : ℤ) ∣ c * m) :
    Commute ((Lz c : SL(2, ℤ)) : SL(2, ℤ) ⧸ Gamma N)
      ((ModularGroup.T ^ m : SL(2, ℤ)) : SL(2, ℤ) ⧸ Gamma N) := by
  show ((Lz c * ModularGroup.T ^ m : SL(2, ℤ)) : SL(2, ℤ) ⧸ Gamma N) =
    ((ModularGroup.T ^ m * Lz c : SL(2, ℤ)) : SL(2, ℤ) ⧸ Gamma N)
  rw [QuotientGroup.eq, Gamma_mem']
  rw [map_mul, map_inv, inv_mul_eq_one]
  have hcm : ((c : ZMod N) * (m : ZMod N)) = 0 := by
    rw [← Int.cast_mul, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact h
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.map_apply_coe, Lz_00, Lz_01, Lz_10, Lz_11, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
      -map_zpow, T_zpow_00, T_zpow_01, T_zpow_10, T_zpow_11]
  all_goals linear_combination hcm

end setup

/-! ### Coefficient projections -/

section coeff

variable (N : ℕ) [NeZero N] (k : ℤ)

noncomputable instance finQuot : Fintype (SL(2, ℤ) ⧸ Gamma N) := Fintype.ofFinite _

noncomputable instance finSub (X : Subgroup (SL(2, ℤ) ⧸ Gamma N)) : Fintype X := Fintype.ofFinite _

/-- The `n`-th width-1 coefficient as a linear functional on `S_k(H)`. -/
def coeffL (n : ℕ) : CuspForm (HG N) k →ₗ[ℂ] ℂ :=
  (PowerSeries.coeff (R := ℂ) n).comp
    (QExp.qExpansionLinearMap one_pos (one_mem_strictPeriods_HG N) k)

lemma coeffL_apply (n : ℕ) (F : CuspForm (HG N) k) :
    coeffL N k n F = (qExpansion 1 F).coeff n := rfl

lemma coeff_act_T (m : ℤ) (F : CuspForm (HG N) k) (n : ℕ) :
    coeffL N k n (act N k ((ModularGroup.T ^ (-m) : SL(2, ℤ)) : SL(2, ℤ) ⧸ Gamma N) F) =
      Complex.exp (2 * π * Complex.I * n * (((m : ℝ) / N : ℝ) : ℂ)) * coeffL N k n F := by
  have had : (1 : ℝ) * 1 ≠ 0 := by norm_num
  rw [coeffL_apply, coeffL_apply, coe_act_mk, ← zpow_neg, neg_neg, cj_T_zpow N m had]
  exact QExp.qExpansion_coeff_slash_translate F (one_mem_strictPeriods_HG N) _ had n

/-- `u_p = T^{-(N/p)}` modulo `Γ(N)`. -/
def uP (p : ℕ) : SL(2, ℤ) ⧸ Gamma N :=
  ((ModularGroup.T ^ (-((N / p : ℕ) : ℤ)) : SL(2, ℤ)) : SL(2, ℤ) ⧸ Gamma N)

lemma uP_zpow (p : ℕ) (z : ℤ) :
    uP N p ^ z =
      ((ModularGroup.T ^ (-(((N / p : ℕ) : ℤ) * z)) : SL(2, ℤ)) : SL(2, ℤ) ⧸ Gamma N) := by
  rw [uP, ← QuotientGroup.mk_zpow, ← zpow_mul, neg_mul]

lemma coeff_uP_zpow {p : ℕ} (hp : p.Prime) (hpN : p ∣ N) (z : ℤ) (F : CuspForm (HG N) k)
    (n : ℕ) :
    coeffL N k n (act N k (uP N p ^ z) F) =
      Complex.exp (2 * π * Complex.I * ((n : ℂ) * z / p)) * coeffL N k n F := by
  rw [uP_zpow, coeff_act_T]
  congr 2
  obtain ⟨m', hm'⟩ := hpN
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hm0 : (m' : ℂ) ≠ 0 := by
    have : m' ≠ 0 := by
      rintro rfl
      exact NeZero.ne N (by simpa using hm')
    exact Nat.cast_ne_zero.mpr this
  have hdiv : N / p = m' := by rw [hm', Nat.mul_div_cancel_left _ hp.pos]
  have hN : (N : ℂ) = p * m' := by rw [hm']; push_cast; ring
  rw [hdiv]
  push_cast
  rw [hN]
  first
    | (field_simp; ring)
    | field_simp

/-- A linear functional constant on an orbit is unchanged by the average. -/
lemma functional_avg {E G : Type*} [AddCommGroup E] [Module ℂ E] [Group G]
    (σ : G →* Module.End ℂ E) (X : Subgroup G) [Fintype X] (φ : E →ₗ[ℂ] ℂ) (v : E)
    (h : ∀ x ∈ X, φ (σ x v) = φ v) : φ (avg σ X v) = φ v := by
  rw [avg, LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum,
    Finset.sum_congr rfl (fun (x : X) _ => h (x : G) x.2), Finset.sum_const, Finset.card_univ,
    ← Nat.card_eq_fintype_card, nsmul_eq_mul, smul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ (natCard_ne_zero X), one_mul]

/-- The coefficient projection `Q_p` = average over `⟨u_p⟩`. -/
abbrev Q (p : ℕ) : Module.End ℂ (CuspForm (HG N) k) :=
  avg (act N k) (Subgroup.zpowers (uP N p))

lemma coeff_Q {p : ℕ} (hp : p.Prime) (hpN : p ∣ N) (F : CuspForm (HG N) k) (n : ℕ) :
    coeffL N k n (Q N k p F) = if p ∣ n then coeffL N k n F else 0 := by
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  split_ifs with hpn
  · refine functional_avg _ _ _ _ (fun x hx => ?_)
    obtain ⟨z, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [coeff_uP_zpow N k hp hpN]
    obtain ⟨n', rfl⟩ := hpn
    have harg : 2 * π * Complex.I * (((p * n' : ℕ) : ℂ) * z / p) =
        ((n' * z : ℤ) : ℂ) * (2 * π * Complex.I) := by
      push_cast
      first
        | (field_simp; ring)
        | field_simp
    rw [harg, Complex.exp_int_mul_two_pi_mul_I, one_mul]
  · have hfix : act N k (uP N p) (Q N k p F) = Q N k p F := by
      show (act N k (uP N p) * avg (act N k) (Subgroup.zpowers (uP N p))) F = _
      rw [mul_avg _ (Subgroup.mem_zpowers _)]
    have h1 := congrArg (coeffL N k n) hfix
    have h2 := coeff_uP_zpow N k hp hpN 1 (Q N k p F) n
    rw [zpow_one] at h2
    rw [h2] at h1
    have hζ : Complex.exp (2 * π * Complex.I * ((n : ℂ) * ((1 : ℤ) : ℂ) / p)) ≠ 1 := by
      intro h
      obtain ⟨K, hK⟩ := Complex.exp_eq_one_iff.mp h
      have hnK : (n : ℂ) = K * p := by
        push_cast at hK
        field_simp at hK
        linear_combination hK
      have hnK' : (n : ℤ) = K * p := by exact_mod_cast hnK
      exact hpn (Int.natCast_dvd_natCast.mp ⟨K, by rw [hnK']; ring⟩)
    have : (Complex.exp (2 * π * Complex.I * ((n : ℂ) * ((1 : ℤ) : ℂ) / p)) - 1) *
        coeffL N k n (Q N k p F) = 0 := by
      rw [sub_mul, one_mul, h1, sub_self]
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hζ)

lemma coeff_prod (l : List ℕ) (hl : ∀ p ∈ l, p.Prime ∧ p ∣ N) (F : CuspForm (HG N) k) (n : ℕ) :
    coeffL N k n ((l.map fun p => 1 - Q N k p).prod F) =
      if ∀ p ∈ l, ¬ p ∣ n then coeffL N k n F else 0 := by
  induction l with
  | nil => simp
  | cons p l ih =>
    have hp := hl p (by simp)
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply, LinearMap.sub_apply,
      Module.End.one_apply, map_sub, coeff_Q N k hp.1 hp.2,
      ih (fun q hq => hl q (List.mem_cons_of_mem _ hq))]
    by_cases hpn : p ∣ n
    · simp [hpn]
    · simp [hpn]

lemma prod_Q_restrict_eq_zero (f : CuspForm (G1 N) k)
    (hf : ∀ n : ℕ, Nat.Coprime n N → (qExpansion 1 f).coeff n = 0) :
    (N.primeFactors.toList.map fun p => 1 - Q N k p).prod (restrictCF (HG_le_G1 N) f) = 0 := by
  refine QExp.cuspForm_eq_zero_of_coeff one_pos (one_mem_strictPeriods_HG N) _ (fun n => ?_)
  rw [← coeffL_apply, coeff_prod N k _ (fun p hp => by
    rw [Finset.mem_toList, Nat.mem_primeFactors] at hp
    exact ⟨hp.1, hp.2.1⟩)]
  split_ifs with h
  · rw [coeffL_apply]
    refine hf n (Nat.coprime_of_dvd fun q hq hqn hqN => ?_)
    exact h q (Finset.mem_toList.mpr (Nat.mem_primeFactors.mpr ⟨hq, hqN, NeZero.ne N⟩)) hqn
  · rfl

end coeff

/-! ### Assembly -/

section assembly

variable (N : ℕ) [NeZero N] (k : ℤ)

/-- The Bezout cofactor `c_i = ∏_{q ∈ s \ {i}} q`, `s` the prime factors of `N`. -/
def cB (i : ℕ) : ℤ := ∏ j ∈ N.primeFactors \ {i}, (j : ℤ)

/-- `b_i = L(c_i)` modulo `Γ(N)`. -/
def bP (i : ℕ) : SL(2, ℤ) ⧸ Gamma N := ((Lz (cB N i) : SL(2, ℤ)) : SL(2, ℤ) ⧸ Gamma N)

lemma bP_zpow (i : ℕ) (z : ℤ) :
    bP N i ^ z = ((Lz (z * cB N i) : SL(2, ℤ)) : SL(2, ℤ) ⧸ Gamma N) := by
  rw [bP, ← QuotientGroup.mk_zpow, Lz_zpow]

lemma commute_mk_Lz (a b : ℤ) :
    Commute ((Lz a : SL(2, ℤ)) : SL(2, ℤ) ⧸ Gamma N) ((Lz b : SL(2, ℤ)) : SL(2, ℤ) ⧸ Gamma N) := by
  have h : Commute (Lz a) (Lz b) := by
    show Lz a * Lz b = Lz b * Lz a
    rw [← Lz_add, ← Lz_add, add_comm]
  exact h.map (QuotientGroup.mk' (Gamma N))

lemma commute_uP (p q : ℕ) : Commute (uP N p) (uP N q) := by
  have h : Commute (ModularGroup.T ^ (-((N / p : ℕ) : ℤ)))
      (ModularGroup.T ^ (-((N / q : ℕ) : ℤ))) :=
    Commute.zpow_zpow_self _ _ _
  exact h.map (QuotientGroup.mk' (Gamma N))

lemma commute_bP_uP {i j : ℕ} (hj : j ∈ N.primeFactors) (hij : i ≠ j) :
    Commute (bP N i) (uP N j) := by
  unfold bP uP
  refine commute_Lz_T N ?_
  have h1 : (j : ℤ) ∣ cB N i :=
    Finset.dvd_prod_of_mem _ (Finset.mem_sdiff.mpr ⟨hj, by simpa using hij.symm⟩)
  have h2 : (j : ℤ) * ((N / j : ℕ) : ℤ) = N := by
    rw [Nat.mem_primeFactors] at hj
    exact_mod_cast Nat.mul_div_cancel' hj.2.1
  obtain ⟨t, ht⟩ := h1
  exact ⟨-t, by rw [ht, ← h2]; ring⟩

lemma act_Lz_restrict (f : CuspForm (G1 N) k) (e : ℤ) :
    act N k ((Lz e : SL(2, ℤ)) : SL(2, ℤ) ⧸ Gamma N) (restrictCF (HG_le_G1 N) f) =
      restrictCF (HG_le_G1 N) f := by
  refine DFunLike.coe_injective ?_
  rw [coe_act_mk, coe_restrictCF, ← Lz_neg, cj_Lz]
  exact SlashInvariantFormClass.slash_action_eq f _ ⟨Lz (N * -e), Lz_mul_mem_Gamma1 N _, rfl⟩

omit [NeZero N] in
lemma Lz_mul_entries (c : ℤ) (γ : SL(2, ℤ)) :
    (Lz c * γ) 0 0 = γ 0 0 ∧ (Lz c * γ) 0 1 = γ 0 1 ∧ (Lz c * γ) 1 0 = c * γ 0 0 + γ 1 0 ∧
      (Lz c * γ) 1 1 = c * γ 0 1 + γ 1 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (simp [Lz_00, Lz_01, Lz_10, Lz_11, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_two]; try ring)

/-- A form fixed by every `L(e)` (mod `Γ(N)`) is `Γ(N)`-invariant. -/
lemma slash_eq_of_Lz_fixed (y : CuspForm (HG N) k)
    (hL : ∀ e : ℤ, act N k ((Lz e : SL(2, ℤ)) : SL(2, ℤ) ⧸ Gamma N) y = y) :
    ∀ γ ∈ Gamma N, ⇑y ∣[k] γ = ⇑y := by
  intro γ hγ
  have hγ' := hγ
  rw [Gamma_mem] at hγ'
  obtain ⟨h00, -, h10, h11⟩ := hγ'
  obtain ⟨c', hc'⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h10
  obtain ⟨a', ha'⟩ : (N : ℤ) ∣ γ 0 0 - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [h00, sub_self]
  obtain ⟨d00, -, d10, d11⟩ := Lz_mul_entries (-(N * c')) γ
  have hδH : Lz (-(N * c')) * γ ∈ HZ N := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [Gamma1_mem, d00, d11, d10]
      refine ⟨h00, ?_, ?_⟩
      · push_cast
        simp [h11]
      · rw [hc']
        push_cast
        simp
    · rw [Gamma0_mem, d10, ZMod.intCast_zmod_eq_zero_iff_dvd]
      refine ⟨-(c' * a'), ?_⟩
      rw [hc']
      push_cast
      linear_combination (-((N : ℤ) * c')) * ha'
  have hγeq : γ = Lz (N * c') * (Lz (-(N * c')) * γ) := by
    rw [← mul_assoc, ← Lz_add, add_neg_cancel, Lz_zero, one_mul]
  have hfix : ⇑y ∣[k] (Lz (N * c')) = ⇑y := by
    have := congrArg (fun F : CuspForm (HG N) k => ⇑F) (hL (-c'))
    simp only [coe_act_mk, ← Lz_neg, neg_neg, cj_Lz] at this
    first
      | exact this
      | (rw [ModularForm.SL_slash]; exact this)
  rw [hγeq, SlashAction.slash_mul, hfix]
  exact SlashInvariantFormClass.slash_action_eq y _ ⟨_, hδH, rfl⟩

lemma translate_of_uP_fixed {p : ℕ} (hp : p.Prime) (hpN : p ∣ N) (y : CuspForm (HG N) k)
    (hT : act N k (uP N p) y = y) (τ : ℍ) : y (((p : ℝ)⁻¹) +ᵥ τ) = y τ := by
  have had : (1 : ℝ) * 1 ≠ 0 := by norm_num
  have h := act_T_apply N k ((N / p : ℕ) : ℤ) had y τ
  rw [show ((ModularGroup.T ^ (-((N / p : ℕ) : ℤ)) : SL(2, ℤ)) : SL(2, ℤ) ⧸ Gamma N) = uP N p
    from rfl, hT] at h
  rw [h]
  congr 1
  apply UpperHalfPlane.ext
  rw [QExp.upperTri_translate_smul, UpperHalfPlane.coe_vadd]
  obtain ⟨m', hm'⟩ := hpN
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hm0 : (m' : ℂ) ≠ 0 := by
    have : m' ≠ 0 := by
      rintro rfl
      exact NeZero.ne N (by simpa using hm')
    exact Nat.cast_ne_zero.mpr this
  have hdiv : N / p = m' := by rw [hm', Nat.mul_div_cancel_left _ hp.pos]
  have hN : (N : ℂ) = p * m' := by rw [hm']; push_cast; ring
  rw [hdiv]
  push_cast
  rw [hN]
  first
    | (field_simp; ring)
    | field_simp

end assembly

/-- `ι_p : S_k(Γ₁(N/p)) → S_k(Γ₁(N))` when `p` is a prime divisor of `N`, and `0` otherwise. -/
def iotaP (N p : ℕ) (k : ℤ) : CuspForm (G1 (N / p)) k →ₗ[ℂ] CuspForm (G1 N) k :=
  if hp : p.Prime ∧ p ∣ N then
    haveI : NeZero p := ⟨hp.1.ne_zero⟩
    iotaCF p (mul_div_dvd_self hp.2) k
  else 0

lemma iotaP_eq (N : ℕ) (k : ℤ) {p : ℕ} [NeZero p] (hp : p.Prime) (hpN : p ∣ N) :
    iotaP N p k = iotaCF p (mul_div_dvd_self hpN) k := by
  rw [iotaP, dif_pos ⟨hp, hpN⟩]

lemma iotaP_apply (N : ℕ) (k : ℤ) {p : ℕ} [NeZero p] (hp : p.Prime) (hpN : p ∣ N)
    (g : CuspForm (G1 (N / p)) k) (τ : ℍ) : iotaP N p k g τ = g (dg p • τ) := by
  rw [iotaP_eq N k hp hpN, iotaCF_apply]

lemma iotaP_not (N : ℕ) (k : ℤ) {p : ℕ} (hp : ¬ (p.Prime ∧ p ∣ N)) : iotaP N p k = 0 := by
  rw [iotaP, dif_neg hp]

lemma sum_apply' {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} {ι : Type*} (s : Finset ι)
    (F : ι → CuspForm Γ k) (τ : ℍ) : (∑ i ∈ s, F i) τ = ∑ i ∈ s, F i τ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, CuspForm.add_apply, ih]

section main

variable (N : ℕ) [NeZero N] (k : ℤ)

lemma exists_iotaP_eq {p : ℕ} (hp : p.Prime) (hpN : p ∣ N) (y : CuspForm (HG N) k)
    (hL : ∀ e : ℤ, act N k ((Lz e : SL(2, ℤ)) : SL(2, ℤ) ⧸ Gamma N) y = y)
    (hT : act N k (uP N p) y = y) :
    ∃ g : CuspForm (G1 (N / p)) k, ∀ τ, iotaP N p k g τ = y τ := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : NeZero (N / p) :=
    ⟨(Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N)) hpN) hp.pos).ne'⟩
  have hinv : ∀ γ ∈ Gamma (p * (N / p)), ⇑y ∣[k] γ = ⇑y := by
    rw [Nat.mul_div_cancel' hpN]
    exact slash_eq_of_Lz_fixed N k y hL
  obtain ⟨g, hg⟩ := exists_descent p (N / p) hp y hinv (translate_of_uP_fixed N k hp hpN y hT)
  refine ⟨g, fun τ => ?_⟩
  rw [iotaP_apply N k hp hpN, hg, inv_smul_smul]

lemma Lz_fixed_of_bezout (y : CuspForm (HG N) k)
    (h : ∀ j ∈ N.primeFactors, ∀ z : ℤ,
      act N k ((Lz (z * cB N j) : SL(2, ℤ)) : SL(2, ℤ) ⧸ Gamma N) y = y)
    (hne : N.primeFactors.Nonempty) (e : ℤ) :
    act N k ((Lz e : SL(2, ℤ)) : SL(2, ℤ) ⧸ Gamma N) y = y := by
  classical
  have hcop : Pairwise (Function.onFun IsCoprime fun i : N.primeFactors => (fun j : ℕ => (j : ℤ)) i) := by
    rintro ⟨i, hi⟩ ⟨j, hj⟩ hij
    simp only [Function.onFun]
    rw [Nat.isCoprime_iff_coprime]
    rw [Nat.mem_primeFactors] at hi hj
    exact (Nat.coprime_primes hi.1 hj.1).mpr (fun h => hij (Subtype.ext h))
  obtain ⟨μ, hμ⟩ := (exists_sum_eq_one_iff_pairwise_coprime (s := fun j : ℕ => (j : ℤ)) hne).mpr hcop
  have hsum1 : ∑ j ∈ N.primeFactors, μ j * cB N j = 1 := hμ
  have hfixAdd : ∀ a b : ℤ, act N k ((Lz a : SL(2, ℤ)) : SL(2, ℤ) ⧸ Gamma N) y = y →
      act N k ((Lz b : SL(2, ℤ)) : SL(2, ℤ) ⧸ Gamma N) y = y →
      act N k ((Lz (a + b) : SL(2, ℤ)) : SL(2, ℤ) ⧸ Gamma N) y = y := by
    intro a b ha hb
    rw [Lz_add, QuotientGroup.mk_mul, map_mul, Module.End.mul_apply, hb, ha]
  have hsum : ∀ t : Finset ℕ, t ⊆ N.primeFactors →
      act N k ((Lz (∑ j ∈ t, e * μ j * cB N j) : SL(2, ℤ)) : SL(2, ℤ) ⧸ Gamma N) y = y := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro _
      rw [Finset.sum_empty, Lz_zero, QuotientGroup.mk_one, map_one, Module.End.one_apply]
    | insert a t ha ih =>
      intro hsub
      rw [Finset.sum_insert ha]
      exact hfixAdd _ _ (h a (hsub (Finset.mem_insert_self _ _)) _)
        (ih (fun x hx => hsub (Finset.mem_insert_of_mem hx)))
  have he : ∑ j ∈ N.primeFactors, e * μ j * cB N j = e := by
    calc ∑ j ∈ N.primeFactors, e * μ j * cB N j = e * ∑ j ∈ N.primeFactors, μ j * cB N j := by
          rw [Finset.mul_sum]
          simp_rw [mul_assoc]
      _ = e := by rw [hsum1, mul_one]
  have := hsum N.primeFactors subset_rfl
  rwa [he] at this

/-- **Atkin-Lehner-Li Main Lemma (Diamond-Shurman Thm 5.7.1).** If `f ∈ S_k(Γ₁(N))` has
`a_n(f) = 0` for every `n` coprime to `N`, then `f = Σ_{p ∣ N prime} ι_p(g_p)` with
`g_p ∈ S_k(Γ₁(N/p))`. -/
theorem mainLemma (f : CuspForm (G1 N) k)
    (hf : ∀ n : ℕ, Nat.Coprime n N → (qExpansion 1 f).coeff n = 0) :
    ∃ g : (p : ℕ) → CuspForm (G1 (N / p)) k, f = ∑ p ∈ N.primeFactors, iotaP N p k (g p) := by
  classical
  haveI : FiniteDimensional ℂ (CuspForm (HG N) k) := FinDim.finiteDimensional_cuspForm_SL (HZ N) k
  have hsP : ∀ i ∈ N.primeFactors.toList, i.Prime ∧ i ∣ N := fun i hi => by
    rw [Finset.mem_toList, Nat.mem_primeFactors] at hi
    exact ⟨hi.1, hi.2.1⟩
  have hc : ∀ i ∈ N.primeFactors.toList, ∀ j ∈ N.primeFactors.toList, i ≠ j →
      (∀ a ∈ Subgroup.zpowers (bP N i), ∀ b ∈ Subgroup.zpowers (bP N j), Commute a b) ∧
      (∀ a ∈ Subgroup.zpowers (bP N i), ∀ b ∈ Subgroup.zpowers (uP N j), Commute a b) ∧
      (∀ a ∈ Subgroup.zpowers (uP N i), ∀ b ∈ Subgroup.zpowers (uP N j), Commute a b) := by
    intro i _ j hj hij
    refine ⟨zpowers_commute (commute_mk_Lz N _ _),
      zpowers_commute (commute_bP_uP N (Finset.mem_toList.mp hj) hij),
      zpowers_commute (commute_uP N i j)⟩
  have hx0 : ∀ i ∈ N.primeFactors.toList, ∀ g ∈ Subgroup.zpowers (bP N i),
      act N k g (restrictCF (HG_le_G1 N) f) = restrictCF (HG_le_G1 N) f := by
    intro i _ g hg
    obtain ⟨z, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    rw [bP_zpow]
    exact act_Lz_restrict N k f _
  have h0 : (N.primeFactors.toList.map fun i =>
      1 - avg (act N k) (Subgroup.zpowers (uP N i))).prod (restrictCF (HG_le_G1 N) f) = 0 :=
    prod_Q_restrict_eq_zero N k f hf
  have hmem := mem_iSup_of_avg (act N k) N.primeFactors.toList (Finset.nodup_toList _)
    (fun i => Subgroup.zpowers (bP N i)) (fun i => Subgroup.zpowers (uP N i)) hc
    (restrictCF (HG_le_G1 N) f) hx0 h0
  simp only [Finset.mem_toList] at hmem
  obtain ⟨μ, hμ⟩ := (Submodule.mem_iSup_finset_iff_exists_sum _ _).mp hmem
  have key : ∀ p, ∃ g : CuspForm (G1 (N / p)) k, p ∈ N.primeFactors →
      ∀ τ, iotaP N p k g τ = (μ p : CuspForm (HG N) k) τ := by
    intro p
    by_cases hp : p ∈ N.primeFactors
    · obtain ⟨hP, hQ⟩ := mem_Wsp.mp (μ p).2
      have hpP := hsP p (Finset.mem_toList.mpr hp)
      have hfixj : ∀ j ∈ N.primeFactors, ∀ z : ℤ,
          act N k ((Lz (z * cB N j) : SL(2, ℤ)) : SL(2, ℤ) ⧸ Gamma N) (μ p : CuspForm (HG N) k) =
            (μ p : CuspForm (HG N) k) := by
        intro j hj z
        rw [← bP_zpow]
        exact apply_eq_of_avg (act N k) (hP j (Finset.mem_toList.mpr hj))
          (Subgroup.zpow_mem_zpowers _ z)
      obtain ⟨g, hg⟩ := exists_iotaP_eq N k hpP.1 hpP.2 (μ p : CuspForm (HG N) k)
        (Lz_fixed_of_bezout N k _ hfixj ⟨p, hp⟩)
        (apply_eq_of_avg (act N k) hQ (Subgroup.mem_zpowers _))
      exact ⟨g, fun _ => hg⟩
    · exact ⟨0, fun h => absurd h hp⟩
  choose g hg using key
  refine ⟨g, CuspForm.ext fun τ => ?_⟩
  have hfx : f τ = restrictCF (HG_le_G1 N) f τ := rfl
  rw [hfx, ← hμ, sum_apply', sum_apply']
  exact Finset.sum_congr rfl fun p hp => (hg p hp τ).symm

end main

/-! ### Range form and the `χ`-version -/

section chi

variable (N : ℕ) [NeZero N] (k : ℤ)

/-- Range form of the Main Lemma: `f` lies in the old space `Σ_{p ∣ N} ι_p(S_k(Γ₁(N/p)))`. -/
theorem mainLemma_mem_iSup (f : CuspForm (G1 N) k)
    (hf : ∀ n : ℕ, Nat.Coprime n N → (qExpansion 1 f).coeff n = 0) :
    f ∈ ⨆ p ∈ N.primeFactors, LinearMap.range (iotaP N p k) := by
  obtain ⟨g, hg⟩ := mainLemma N k f hf
  rw [hg]
  exact Submodule.sum_mem _ fun p hp =>
    Submodule.mem_iSup_of_mem p (Submodule.mem_iSup_of_mem hp (LinearMap.mem_range_self _ _))

omit [NeZero N] in
lemma div_ne_zero_of_mem_primeFactors {p : ℕ} (hp : p ∈ N.primeFactors) : N / p ≠ 0 := by
  rw [Nat.mem_primeFactors] at hp
  exact (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hp.2.2) hp.2.1) hp.1.pos).ne'

omit [NeZero N] in
lemma div_dvd_of_mem_primeFactors {p : ℕ} (hp : p ∈ N.primeFactors) : N / p ∣ N :=
  Nat.div_dvd_of_dvd (Nat.dvd_of_mem_primeFactors hp)

omit [NeZero N] in
/-- `ι_p` sends `S_k(N/p, ψ)` into `S_k(N, ψ.changeLevel)`. -/
lemma iotaP_mem_chiSubspace {p : ℕ} (hp : p ∈ N.primeFactors) (ψ : DirichletCharacter ℂ (N / p))
    {g : CuspForm (G1 (N / p)) k} (hg : g ∈ Diamond.chiSubspace k ψ) :
    iotaP N p k g ∈ Diamond.chiSubspace k
      (DirichletCharacter.changeLevel (div_dvd_of_mem_primeFactors N hp) ψ) := by
  have hpP := Nat.mem_primeFactors.mp hp
  haveI : NeZero p := ⟨hpP.1.ne_zero⟩
  rw [iotaP_eq N k hpP.1 hpP.2.1]
  exact (Diamond.mem_chiSubspace_iff k _ _).2
    (iotaCF_nebentypus p (mul_div_dvd_self hpP.2.1) ψ g ((Diamond.mem_chiSubspace_iff k ψ g).1 hg))

open Classical in
/-- The part of `g ∈ S_k(Γ₁(N/p))` lying in the character spaces `S_k(N/p, ψ)` with
`ψ.changeLevel = χ` (there is at most one such `ψ`; the sum is `0` when there is none). -/
def chiPart (χ : DirichletCharacter ℂ N) {p : ℕ} (hp : p ∈ N.primeFactors)
    (g : CuspForm (G1 (N / p)) k) : CuspForm (G1 (N / p)) k :=
  haveI : NeZero (N / p) := ⟨div_ne_zero_of_mem_primeFactors N hp⟩
  ∑ ψ : DirichletCharacter ℂ (N / p),
    if DirichletCharacter.changeLevel (div_dvd_of_mem_primeFactors N hp) ψ = χ then
      Diamond.proj k ψ g else 0

lemma chiPart_mem (χ : DirichletCharacter ℂ N) {p : ℕ} (hp : p ∈ N.primeFactors)
    (g : CuspForm (G1 (N / p)) k) (ψ0 : DirichletCharacter ℂ (N / p))
    (h0 : DirichletCharacter.changeLevel (div_dvd_of_mem_primeFactors N hp) ψ0 = χ) :
    chiPart N k χ hp g ∈ Diamond.chiSubspace k ψ0 := by
  haveI : NeZero (N / p) := ⟨div_ne_zero_of_mem_primeFactors N hp⟩
  have e : chiPart N k χ hp g = Diamond.proj k ψ0 g := by
    rw [chiPart, Finset.sum_eq_single ψ0]
    · rw [if_pos h0]
    · intro ψ _ hne
      rw [if_neg]
      intro h
      exact hne (DirichletCharacter.changeLevel_injective _ (h.trans h0.symm))
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [e]
  exact Diamond.proj_mem k ψ0 g

lemma chiPart_eq_zero (χ : DirichletCharacter ℂ N) {p : ℕ} (hp : p ∈ N.primeFactors)
    (g : CuspForm (G1 (N / p)) k)
    (h : ∀ ψ : DirichletCharacter ℂ (N / p),
      DirichletCharacter.changeLevel (div_dvd_of_mem_primeFactors N hp) ψ ≠ χ) :
    chiPart N k χ hp g = 0 := by
  rw [chiPart]
  exact Finset.sum_eq_zero fun ψ _ => if_neg (h ψ)

/-- `e_χ ∘ ι_p = ι_p ∘ (Σ_{ψ.changeLevel = χ} e_ψ)`. -/
lemma proj_iotaP (χ : DirichletCharacter ℂ N) {p : ℕ} (hp : p ∈ N.primeFactors)
    (g : CuspForm (G1 (N / p)) k) :
    Diamond.proj k χ (iotaP N p k g) = iotaP N p k (chiPart N k χ hp g) := by
  haveI : NeZero (N / p) := ⟨div_ne_zero_of_mem_primeFactors N hp⟩
  conv_lhs => rw [← Diamond.sum_proj k g]
  rw [chiPart]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun ψ _ => ?_
  have hmem := iotaP_mem_chiSubspace N k hp ψ (Diamond.proj_mem k ψ g)
  split_ifs with h
  · rw [← h]
    exact Diamond.proj_eq_self k hmem
  · rw [map_zero]
    exact Diamond.proj_eq_zero k (fun e => h e.symm) hmem

/-- **Main Lemma, `χ`-version.** If `f ∈ S_k(N, χ)` has `a_n(f) = 0` for every `n` coprime to `N`,
then `f = Σ_{p ∣ N prime} ι_p(g_p)` where each `g_p` lies in `S_k(N/p, ψ)` for the character `ψ`
mod `N/p` with `ψ.changeLevel = χ` (when `χ` factors through level `N/p`), and `g_p = 0` when no
such `ψ` exists. -/
theorem mainLemma_chi (χ : DirichletCharacter ℂ N) (f : CuspForm (G1 N) k)
    (hχ : f ∈ Diamond.chiSubspace k χ)
    (hf : ∀ n : ℕ, Nat.Coprime n N → (qExpansion 1 f).coeff n = 0) :
    ∃ g : (p : ℕ) → CuspForm (G1 (N / p)) k,
      f = ∑ p ∈ N.primeFactors, iotaP N p k (g p) ∧
      (∀ p (hp : p ∈ N.primeFactors) (ψ : DirichletCharacter ℂ (N / p)),
        DirichletCharacter.changeLevel (div_dvd_of_mem_primeFactors N hp) ψ = χ →
          g p ∈ Diamond.chiSubspace k ψ) ∧
      (∀ p (hp : p ∈ N.primeFactors),
        (∀ ψ : DirichletCharacter ℂ (N / p),
          DirichletCharacter.changeLevel (div_dvd_of_mem_primeFactors N hp) ψ ≠ χ) → g p = 0) := by
  classical
  obtain ⟨g, hg⟩ := mainLemma N k f hf
  refine ⟨fun p => if hp : p ∈ N.primeFactors then chiPart N k χ hp (g p) else 0, ?_, ?_, ?_⟩
  · calc f = Diamond.proj k χ f := (Diamond.proj_eq_self k hχ).symm
      _ = ∑ p ∈ N.primeFactors, Diamond.proj k χ (iotaP N p k (g p)) := by
          conv_lhs => rw [hg]
          rw [map_sum]
      _ = ∑ p ∈ N.primeFactors, iotaP N p k
            (if hp : p ∈ N.primeFactors then chiPart N k χ hp (g p) else 0) :=
          Finset.sum_congr rfl fun p hp => by rw [dif_pos hp, proj_iotaP N k χ hp]
  · intro p hp ψ h
    dsimp only
    rw [dif_pos hp]
    exact chiPart_mem N k χ hp (g p) ψ h
  · intro p hp h
    dsimp only
    rw [dif_pos hp]
    exact chiPart_eq_zero N k χ hp (g p) h

/-- `χ`-version, range form: `f ∈ S_k(N, χ)` with `a_n(f) = 0` for `(n, N) = 1` is a sum of
`ι_p(g_p)` with `g_p ∈ S_k(N/p, ψ_p)`, `ψ_p.changeLevel = χ`, over the primes `p ∣ N` for which
such a `ψ_p` exists. -/
theorem mainLemma_chi_exists (χ : DirichletCharacter ℂ N) (f : CuspForm (G1 N) k)
    (hχ : f ∈ Diamond.chiSubspace k χ)
    (hf : ∀ n : ℕ, Nat.Coprime n N → (qExpansion 1 f).coeff n = 0) :
    ∃ g : (p : ℕ) → CuspForm (G1 (N / p)) k,
      f = ∑ p ∈ N.primeFactors, iotaP N p k (g p) ∧
      ∀ p (hp : p ∈ N.primeFactors), g p = 0 ∨ ∃ ψ : DirichletCharacter ℂ (N / p),
        DirichletCharacter.changeLevel (div_dvd_of_mem_primeFactors N hp) ψ = χ ∧
          g p ∈ Diamond.chiSubspace k ψ := by
  obtain ⟨g, hsum, hmem, hzero⟩ := mainLemma_chi N k χ f hχ hf
  refine ⟨g, hsum, fun p hp => ?_⟩
  by_cases hex : ∃ ψ : DirichletCharacter ℂ (N / p),
      DirichletCharacter.changeLevel (div_dvd_of_mem_primeFactors N hp) ψ = χ
  · obtain ⟨ψ, hψ⟩ := hex
    exact Or.inr ⟨ψ, hψ, hmem p hp ψ hψ⟩
  · exact Or.inl (hzero p hp fun ψ hψ => hex ⟨ψ, hψ⟩)

end chi

end RamanujanPetersson.MainLemma


