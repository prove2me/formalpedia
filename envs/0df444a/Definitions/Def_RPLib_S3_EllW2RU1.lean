-- Prove2me | Definitions.Def_RPLib_S3_EllW2RU1
-- name    : RPLib_S3_EllW2RU1
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T12:27:24.297915+00:00
-- url     : https://prove2.me/theorems/6ebc63b8-18f1-4b14-bbfd-e84eff1a7944
-- title:
--   The Eichler-Selberg trace formula in weight two: translates in a half-open strip and coprime pairs
-- statement:
--   Translates in a half-open strip and coprime pairs.
--
--   * `stripH Y = {w : -1/2 ≤ re w < 1/2, Y ≤ im w}` (half-open: every `T`-orbit meets it once).
--   * `tsum_SL_strip`: `#{γ ∈ SL(2, ℤ) : γ z ∈ S_Y} = #{(c, d) coprime : Y |c z + d|² ≤ im z}`.
--   * `tsum_SL_toPSL`: `Σ_{γ ∈ SL(2, ℤ)} f(±γ) = 2 Σ_{g ∈ PSL(2, ℤ)} f(g)`.
--   * `two_mul_tsum_PSL_strip`: `2 #{g ∈ PSL(2, ℤ) : g z ∈ S_Y} = #{(c, d) coprime : ...}`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224; H. Iwaniec, Spectral Methods of Automorphic Forms, 2nd ed., Graduate Studies in Mathematics 53, AMS 2002, Chapter 2

import Mathlib
import Definitions.Def_RPLib_S1_FundDomain

/-!
# S3-ES-Wt2 (RU1): translates in a half-open strip and coprime pairs

* `stripH Y = {w : -1/2 ≤ re w < 1/2, Y ≤ im w}` (half-open: every `T`-orbit meets it once).
* `tsum_SL_strip`: `#{γ ∈ SL(2, ℤ) : γ z ∈ S_Y} = #{(c, d) coprime : Y |c z + d|² ≤ im z}`.
* `tsum_SL_toPSL`: `Σ_{γ ∈ SL(2, ℤ)} f(±γ) = 2 Σ_{g ∈ PSL(2, ℤ)} f(g)`.
* `two_mul_tsum_PSL_strip`: `2 #{g ∈ PSL(2, ℤ) : g z ∈ S_Y} = #{(c, d) coprime : ...}`.
-/

set_option autoImplicit false

open UpperHalfPlane ModularGroup Matrix Matrix.SpecialLinearGroup RP.FundDomain
open scoped MatrixGroups ENNReal

noncomputable section

namespace RamanujanPetersson.EllW2

/-- The half-open strip `S_Y = {w : -1/2 ≤ re w < 1/2, Y ≤ im w}`. -/
def stripH (Y : ℝ) : Set ℍ := {w | -(1 / 2 : ℝ) ≤ w.re ∧ w.re < 1 / 2 ∧ Y ≤ w.im}

/-- The bottom row `(c, d)` of `γ ∈ SL(2, ℤ)`. -/
def brow (γ : SL(2, ℤ)) : ℤ × ℤ :=
  ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0, (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1)

/-- `1` on coprime pairs `(c, d)` with `Y |c z + d|² ≤ im z`, else `0`. -/
def cpInd (Y : ℝ) (z : ℍ) (p : ℤ × ℤ) : ℝ≥0∞ :=
  if IsCoprime p.1 p.2 ∧ Y * Complex.normSq ((p.1 : ℂ) * (z : ℂ) + p.2) ≤ z.im then 1 else 0

lemma brow_T_zpow_mul (k : ℤ) (γ : SL(2, ℤ)) : brow (T ^ k * γ) = brow γ := by
  unfold brow
  simp

lemma eq_T_zpow_mul_of_brow {γ γ' : SL(2, ℤ)} (h : brow γ = brow γ') :
    ∃ k : ℤ, γ = T ^ k * γ' := by
  have h1 : (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = (γ' : Matrix (Fin 2) (Fin 2) ℤ) 1 0 :=
    congrArg Prod.fst h
  have h2 : (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = (γ' : Matrix (Fin 2) (Fin 2) ℤ) 1 1 :=
    congrArg Prod.snd h
  have hd' := γ'.det_coe
  rw [det_fin_two] at hd'
  obtain ⟨g, hg⟩ : ∃ g : SL(2, ℤ), g = γ * γ'⁻¹ := ⟨_, rfl⟩
  have hmat : (g : Matrix (Fin 2) (Fin 2) ℤ) =
      (γ : Matrix (Fin 2) (Fin 2) ℤ) * adjugate (γ' : Matrix (Fin 2) (Fin 2) ℤ) := by
    rw [hg, coe_mul, coe_inv]
  have hc : (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0 := by
    rw [hmat, adjugate_fin_two]
    simp [Matrix.mul_apply, Fin.sum_univ_two, h1, h2]
    (try ring)
  have hd : (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = 1 := by
    rw [hmat, adjugate_fin_two]
    simp [Matrix.mul_apply, Fin.sum_univ_two, h1, h2]
    linear_combination hd'
  have ha : (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = 1 := by
    have := g.det_coe
    rw [det_fin_two, hc, hd] at this
    linarith
  have hgT : g = T ^ ((g : Matrix (Fin 2) (Fin 2) ℤ) 0 1) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [coe_T_zpow, ha, hc, hd, show (1 : Fin (0 + 2)) = (1 : Fin 2) from rfl]
  refine ⟨(g : Matrix (Fin 2) (Fin 2) ℤ) 0 1, ?_⟩
  rw [← hgT, hg, inv_mul_cancel_right]

lemma im_smul_brow (γ : SL(2, ℤ)) (z : ℍ) :
    (γ • z).im = z.im / Complex.normSq (((brow γ).1 : ℂ) * (z : ℂ) + (brow γ).2) := by
  have h := ModularGroup.im_smul_eq_div_normSq γ z
  rw [ModularGroup.denom_apply] at h
  exact h

/-- The fibre of the bottom-row map over `p` meets `S_Y` in `cpInd Y z p` points. -/
lemma tsum_fiber_brow (Y : ℝ) (z : ℍ) (p : ℤ × ℤ) :
    ∑' γ : brow ⁻¹' {p}, (stripH Y).indicator 1 ((γ : SL(2, ℤ)) • z) = cpInd Y z p := by
  by_cases hp : IsCoprime p.1 p.2
  swap
  · rw [cpInd, if_neg (fun h => hp h.1)]
    refine ENNReal.tsum_eq_zero.2 fun γ => ?_
    exfalso
    have hγ : brow (γ : SL(2, ℤ)) = p := γ.2
    have h := bottom_row_coprime (γ : SL(2, ℤ))
    exact hp (hγ ▸ h)
  have hmem : ![p.1, p.2] ∈ {cd : Fin 2 → ℤ | IsCoprime (cd 0) (cd 1)} := by simpa using hp
  obtain ⟨γ0, -, hγ0⟩ := bottom_row_surj (R := ℤ) hmem
  have e0 : (γ0 : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = p.1 := by simpa using congrFun hγ0 0
  have e1 : (γ0 : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = p.2 := by simpa using congrFun hγ0 1
  have hb0 : brow γ0 = p := Prod.ext e0 e1
  obtain ⟨N, hN⟩ : ∃ N : ℝ, Complex.normSq ((p.1 : ℂ) * (z : ℂ) + p.2) = N := ⟨_, rfl⟩
  have him : ∀ γ : SL(2, ℤ), brow γ = p → (γ • z).im = z.im / N := by
    intro γ hγ; rw [im_smul_brow, hγ, hN]
  have hN0 : 0 ≤ N := hN ▸ Complex.normSq_nonneg _
  have hNpos : 0 < N := by
    have h := (γ0 • z).im_pos
    rw [him γ0 hb0] at h
    rcases hN0.lt_or_eq with h' | h'
    · exact h'
    · rw [← h', div_zero] at h; exact absurd h (lt_irrefl 0)
  rw [cpInd, hN]
  by_cases hY : Y * N ≤ z.im
  swap
  · rw [if_neg (fun h => hY h.2)]
    refine ENNReal.tsum_eq_zero.2 fun γ => Set.indicator_of_notMem ?_ _
    intro hγ
    have h3 := hγ.2.2
    rw [him γ γ.2, le_div_iff₀ hNpos] at h3
    exact hY h3
  rw [if_pos ⟨hp, hY⟩]
  obtain ⟨k, hk⟩ : ∃ k : ℤ, k = -⌊(γ0 • z).re + 1 / 2⌋ := ⟨_, rfl⟩
  have hb1 : brow (T ^ k * γ0) = p := by rw [brow_T_zpow_mul, hb0]
  have hre1 : ((T ^ k * γ0) • z).re = (γ0 • z).re + k := by rw [mul_smul, re_T_zpow_smul]
  have hfl1 := Int.floor_le ((γ0 • z).re + 1 / 2)
  have hfl2 := Int.lt_floor_add_one ((γ0 • z).re + 1 / 2)
  have hkR : (k : ℝ) = -(⌊(γ0 • z).re + 1 / 2⌋ : ℝ) := by rw [hk]; push_cast; ring
  have hm1 : (T ^ k * γ0) • z ∈ stripH Y := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hre1, hkR]; linarith
    · rw [hre1, hkR]; linarith
    · rw [him _ hb1, le_div_iff₀ hNpos]; exact hY
  rw [tsum_eq_single (⟨T ^ k * γ0, hb1⟩ : brow ⁻¹' {p})]
  · exact Set.indicator_of_mem hm1 _
  · intro γ hne
    refine Set.indicator_of_notMem (fun hγ => hne ?_) _
    have hγp : brow (γ : SL(2, ℤ)) = p := γ.2
    obtain ⟨j, hj⟩ := eq_T_zpow_mul_of_brow (hγp.trans hb1.symm)
    have hrej : ((γ : SL(2, ℤ)) • z).re = ((T ^ k * γ0) • z).re + j := by
      rw [hj, mul_smul, re_T_zpow_smul]
    have hA := hγ.1
    have hB := hγ.2.1
    have hC := hm1.1
    have hD := hm1.2.1
    have hj1 : (j : ℝ) < 1 := by linarith
    have hj2 : (-1 : ℝ) < j := by linarith
    have hj0 : j = 0 := by
      have h1 : j < 1 := by exact_mod_cast hj1
      have h2 : -1 < j := by exact_mod_cast hj2
      omega
    apply Subtype.ext
    rw [hj, hj0, zpow_zero, one_mul]

/-- **`#{γ ∈ SL(2, ℤ) : γ z ∈ S_Y} = #{(c, d) coprime : Y |c z + d|² ≤ im z}`.** -/
theorem tsum_SL_strip (Y : ℝ) (z : ℍ) :
    ∑' γ : SL(2, ℤ), (stripH Y).indicator 1 (γ • z) = ∑' p : ℤ × ℤ, cpInd Y z p :=
  (ENNReal.tsum_fiberwise (fun γ : SL(2, ℤ) => (stripH Y).indicator 1 (γ • z)) brow).symm.trans
    (tsum_congr fun p => tsum_fiber_brow Y z p)

/-- The projection `SL(2, ℤ) → PSL(2, ℤ)`. -/
def toPSL (γ : SL(2, ℤ)) : PSL2Z := ⟨toPGLR γ, toPGLR_mem_PSL2Z γ⟩

lemma ne_neg_SL (γ : SL(2, ℤ)) : γ ≠ -γ := by
  intro h
  have hij : ∀ i j, (γ : Matrix (Fin 2) (Fin 2) ℤ) i j = 0 := by
    intro i j
    have := congrArg (fun A : SL(2, ℤ) => (A : Matrix (Fin 2) (Fin 2) ℤ) i j) h
    simp only [coe_neg, Matrix.neg_apply] at this
    omega
  have hd := γ.det_coe
  rw [det_fin_two, hij 0 0, hij 1 1, hij 0 1] at hd
  simp at hd

/-- **`Σ_{γ ∈ SL(2, ℤ)} f(±γ) = 2 Σ_{g ∈ PSL(2, ℤ)} f(g)`.** -/
theorem tsum_SL_toPSL (f : PSL2Z → ℝ≥0∞) :
    ∑' γ : SL(2, ℤ), f (toPSL γ) = 2 * ∑' g : PSL2Z, f g := by
  have key : ∀ g : PSL2Z, ∑' b : toPSL ⁻¹' {g}, f (toPSL b) = 2 * f g := by
    intro g
    obtain ⟨γ0, hγ0⟩ := mem_PSL2Z.1 g.2
    have hfib : toPSL ⁻¹' {g} = (({γ0, -γ0} : Finset SL(2, ℤ)) : Set SL(2, ℤ)) := by
      ext γ
      rw [Set.mem_preimage, Set.mem_singleton_iff, Finset.coe_insert, Finset.coe_singleton,
        Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · intro h
        refine (toPGLR_eq_toPGLR_iff γ γ0).1 ?_
        rw [hγ0]; exact congrArg Subtype.val h
      · rintro (h | h)
        · rw [h]; exact Subtype.ext hγ0
        · rw [h]; exact Subtype.ext ((toPGLR_neg γ0).trans hγ0)
    have hconst : ∀ b : toPSL ⁻¹' {g}, f (toPSL b) = f g := fun b => congrArg f b.2
    calc ∑' b : toPSL ⁻¹' {g}, f (toPSL b) = ∑' _b : toPSL ⁻¹' {g}, f g := tsum_congr hconst
      _ = ∑' _b : (({γ0, -γ0} : Finset SL(2, ℤ)) : Set SL(2, ℤ)), f g := by rw [hfib]
      _ = ∑ _b ∈ ({γ0, -γ0} : Finset SL(2, ℤ)), f g := Finset.tsum_subtype' _ (fun _ => f g)
      _ = 2 * f g := by rw [Finset.sum_pair (ne_neg_SL γ0), two_mul]
  rw [← ENNReal.tsum_mul_left]
  exact (ENNReal.tsum_fiberwise (fun γ => f (toPSL γ)) toPSL).symm.trans (tsum_congr key)

/-- **`2 #{g ∈ PSL(2, ℤ) : g z ∈ S_Y} = #{(c, d) coprime : Y |c z + d|² ≤ im z}`.** -/
theorem two_mul_tsum_PSL_strip (Y : ℝ) (z : ℍ) :
    2 * ∑' g : PSL2Z, (stripH Y).indicator 1 ((g : PGL(2, ℝ)) • z) =
      ∑' p : ℤ × ℤ, cpInd Y z p := by
  rw [← tsum_SL_strip]
  refine (tsum_SL_toPSL (fun g : PSL2Z => (stripH Y).indicator 1 ((g : PGL(2, ℝ)) • z))).symm.trans ?_
  refine tsum_congr fun γ => ?_
  show (stripH Y).indicator 1 (toPGLR γ • z) = (stripH Y).indicator 1 (γ • z)
  rw [toPGLR_smul]

end RamanujanPetersson.EllW2


