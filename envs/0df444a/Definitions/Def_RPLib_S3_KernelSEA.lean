-- Prove2me | Definitions.Def_RPLib_S3_KernelSEA
-- name    : RPLib_S3_KernelSEA
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T12:47:58.623268+00:00
-- url     : https://prove2.me/theorems/506a6375-9386-454d-8ed2-3e92f3e04621
-- title:
--   The Eichler-Selberg trace formula in weight two: Δ-reduction of `omegaS` to the `Γ(M)` kernel, KEY 2 and the limit `Omega`
-- statement:
--   Δ-reduction of `omegaS` to the `Γ(M)` kernel, KEY 2 and the limit `Omega`.
--
--   * `denW h w = h00 + h10 w`, `natPt h w = (h01 + h11 w)/(h00 + h10 w)`; `Q_mul_left`, `ratQ_mul_left`,
--     `termG_mul_left`: `termG s z w (h g) = (denW h w)^-2 termG s z (natPt h w) g`.
--   * `KGs` (the sum over Mathlib's `CongruenceSubgroup.Gamma M`), `KG_eq_KGs`; KEY 2 `KGs_slash`, `K0_slash` (`ρ ∈ SL(2,ℤ)`).
--   * `phiT : ZMod M × CongruenceSubgroup.Gamma M → Gamma1 M` bijective; `omegaS_eq_sum`:
--     `omegaS M 2 n u s z w = Σ_x (denW (hX x) w)^-2 KGs M s z (natPt (hX x) w)`.
--   * `Omega M n u z w`, `tendsto_omegaS` (`s → 0+`), `Omega_slash`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224; F. Diamond and J. Shurman, A First Course in Modular Forms, GTM 228, Springer 2005, Chapter 5

import Mathlib
import Definitions.Def_RPLib_S3_KernelSDG

/-!
# S3-ES-Wt2, part KS_E (A): Δ-reduction of `omegaS` to the `Γ(M)` kernel, KEY 2 and the limit `Omega`

* `denW h w = h00 + h10 w`, `natPt h w = (h01 + h11 w)/(h00 + h10 w)`; `Q_mul_left`, `ratQ_mul_left`,
  `termG_mul_left`: `termG s z w (h g) = (denW h w)^-2 termG s z (natPt h w) g`.
* `KGs` (the sum over Mathlib's `CongruenceSubgroup.Gamma M`), `KG_eq_KGs`; KEY 2 `KGs_slash`, `K0_slash` (`ρ ∈ SL(2,ℤ)`).
* `phiT : ZMod M × CongruenceSubgroup.Gamma M → Gamma1 M` bijective; `omegaS_eq_sum`:
  `omegaS M 2 n u s z w = Σ_x (denW (hX x) w)^-2 KGs M s z (natPt (hX x) w)`.
* `Omega M n u z w`, `tendsto_omegaS` (`s → 0+`), `Omega_slash`.
-/

open Complex Filter Topology UpperHalfPlane ModularForm CongruenceSubgroup
open scoped MatrixGroups

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.KernelSD

open RamanujanPetersson.Kernel RamanujanPetersson.KernelS RamanujanPetersson.GSA

/-! ### The left factorisation `Q(h g; z, w) = (h00 + h10 w) Q(g; z, h♮ w)` -/

/-- `h00 + h10 w`. -/
def denW (h : Matrix (Fin 2) (Fin 2) ℤ) (w : ℂ) : ℂ := (h 0 0 : ℂ) + (h 1 0 : ℂ) * w

/-- `h♮ w = (h01 + h11 w) / (h00 + h10 w)`. -/
def natPt (h : Matrix (Fin 2) (Fin 2) ℤ) (w : ℂ) : ℂ := ((h 0 1 : ℂ) + (h 1 1 : ℂ) * w) / denW h w

lemma denW_ne_zero {h : Matrix (Fin 2) (Fin 2) ℤ} (hdet : h.det ≠ 0) {w : ℂ} (hv : 0 < w.im) :
    denW h w ≠ 0 := by
  intro h0
  have him : (denW h w).im = (h 1 0 : ℝ) * w.im := by
    simp only [denW, Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im]; ring
  have hre : (denW h w).re = (h 0 0 : ℝ) + (h 1 0 : ℝ) * w.re := by
    simp only [denW, Complex.add_re, Complex.mul_re, Complex.intCast_re, Complex.intCast_im]; ring
  rw [h0, Complex.zero_im] at him
  rw [h0, Complex.zero_re] at hre
  have h10 : (h 1 0 : ℝ) = 0 := by
    rcases mul_eq_zero.1 him.symm with h' | h'
    · exact h'
    · exact absurd h' hv.ne'
  have h00 : (h 0 0 : ℝ) = 0 := by rw [h10, zero_mul, add_zero] at hre; exact hre.symm
  apply hdet
  have h10' : h 1 0 = 0 := by exact_mod_cast h10
  have h00' : h 0 0 = 0 := by exact_mod_cast h00
  rw [det_eq, h00', h10']; ring

lemma im_natPt (h : Matrix (Fin 2) (Fin 2) ℤ) (w : ℂ) :
    (natPt h w).im = (h.det : ℝ) * w.im / Complex.normSq (denW h w) := by
  rw [natPt, Complex.div_im, det_eq]
  simp only [denW, Complex.add_im, Complex.add_re, Complex.mul_im, Complex.mul_re, Complex.intCast_re,
    Complex.intCast_im]
  push_cast
  ring

lemma im_natPt_pos {h : Matrix (Fin 2) (Fin 2) ℤ} (hdet : 0 < h.det) {w : ℂ} (hv : 0 < w.im) :
    0 < (natPt h w).im := by
  rw [im_natPt]
  have hD := denW_ne_zero hdet.ne' hv
  have h1 : (0 : ℝ) < h.det := by exact_mod_cast hdet
  exact div_pos (mul_pos h1 hv) (Complex.normSq_pos.2 hD)

lemma Q_mul_left (h g : Matrix (Fin 2) (Fin 2) ℤ) (z w : ℂ) (hD : denW h w ≠ 0) :
    Q (h * g) z w = denW h w * Q g z (natPt h w) := by
  have key : denW h w * natPt h w = (h 0 1 : ℂ) + (h 1 1 : ℂ) * w := by
    rw [natPt, mul_div_cancel₀ _ hD]
  have key2 : denW h w = (h 0 0 : ℂ) + (h 1 0 : ℂ) * w := rfl
  simp only [Q, Matrix.mul_apply, Fin.sum_univ_two]
  push_cast
  linear_combination (-((g 1 0 : ℂ) * z + (g 1 1 : ℂ))) * key + (-((g 0 0 : ℂ) * z + (g 0 1 : ℂ))) * key2

lemma ratQ_mul_left {h : Matrix (Fin 2) (Fin 2) ℤ} (hdet : h.det ≠ 0) (g : Matrix (Fin 2) (Fin 2) ℤ)
    (z : ℂ) {w : ℂ} (hv : 0 < w.im) : ratQ (h * g) z w = ratQ g z (natPt h w) := by
  have hD := denW_ne_zero hdet hv
  rw [ratQ, ratQ, Q_mul_left h g z w hD, im_natPt, Matrix.det_mul, norm_mul, mul_pow,
    ← Complex.normSq_eq_norm_sq (denW h w)]
  push_cast
  ring

lemma termG_mul_left {h : Matrix (Fin 2) (Fin 2) ℤ} (hdet : h.det ≠ 0) (g : Matrix (Fin 2) (Fin 2) ℤ)
    (s : ℝ) (z : ℂ) {w : ℂ} (hv : 0 < w.im) :
    termG s z w (h * g) = (denW h w ^ 2)⁻¹ * termG s z (natPt h w) g := by
  rw [termG, termG, Q_mul_left h g z w (denW_ne_zero hdet hv), ratQ_mul_left hdet g z hv, mul_pow, mul_inv]
  ring

/-! ### `KG` over Mathlib's `CongruenceSubgroup.Gamma M` -/

lemma zmod_zero_iff (M : ℕ) (a : ℤ) : (a : ZMod M) = 0 ↔ (M : ℤ) ∣ a :=
  ZMod.intCast_zmod_eq_zero_iff_dvd a M

/-- `GamSet M ≃ Γ(M)`. -/
def gamEquiv (M : ℕ) : GamSet M ≃ CongruenceSubgroup.Gamma M where
  toFun g := ⟨⟨g.1, g.2.1⟩, Gamma_mem.2 ⟨(zmod_eq_one_iff M _).2 g.2.2.1, (zmod_zero_iff M _).2 g.2.2.2.1,
    (zmod_zero_iff M _).2 g.2.2.2.2.1, (zmod_eq_one_iff M _).2 g.2.2.2.2.2⟩⟩
  invFun γ := ⟨(γ : SL(2, ℤ)).1, (γ : SL(2, ℤ)).2, by
    obtain ⟨h1, h2, h3, h4⟩ := Gamma_mem.1 γ.2
    exact ⟨(zmod_eq_one_iff M _).1 h1, (zmod_zero_iff M _).1 h2, (zmod_zero_iff M _).1 h3,
      (zmod_eq_one_iff M _).1 h4⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- `KG` as a sum over `Γ(M) ≤ SL(2, ℤ)`. -/
def KGs (M : ℕ) (s : ℝ) (z w : ℂ) : ℂ :=
  ∑' γ : CongruenceSubgroup.Gamma M, termG s z w ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)

lemma KG_eq_KGs (M : ℕ) (s : ℝ) (z w : ℂ) : KG M s z w = KGs M s z w := by
  unfold KG KGs
  exact (gamEquiv M).tsum_eq (fun γ : CongruenceSubgroup.Gamma M => termG s z w ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ))

lemma summable_KGs (M : ℕ) {s : ℝ} (hs : 0 < s) {z w : ℂ} (hy : 0 < z.im) (hv : 0 < w.im) :
    Summable fun γ : CongruenceSubgroup.Gamma M => termG s z w ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
  have h : Summable fun g : GamSet M => termG s z w g.1 := (summable_norm_KG M hs hy hv).of_norm
  exact (gamEquiv M).summable_iff.1 h

/-! ### KEY 2: `KG(ρ τ, w) j(ρ, τ)^-2 = (ρ00 + ρ10 w)^-2 KG(τ, ρ♮ w)` -/

/-- Conjugation `γ ↦ ρ⁻¹ γ ρ` on the normal subgroup `Γ(M)`. -/
def conjG (M : ℕ) (ρ : SL(2, ℤ)) : CongruenceSubgroup.Gamma M ≃ CongruenceSubgroup.Gamma M where
  toFun γ := ⟨ρ⁻¹ * γ * ρ, by simpa using (Gamma_normal M).conj_mem γ γ.2 ρ⁻¹⟩
  invFun γ := ⟨ρ * γ * ρ⁻¹, (Gamma_normal M).conj_mem γ γ.2 ρ⟩
  left_inv γ := Subtype.ext (by simp [mul_assoc])
  right_inv γ := Subtype.ext (by simp [mul_assoc])

lemma termG_slash (g : Matrix (Fin 2) (Fin 2) ℤ) (ρ : SL(2, ℤ)) (τ : ℍ) (w : ℂ) (s : ℝ) :
    termG s ((ρ • τ : ℍ) : ℂ) w g * denom ρ τ ^ (-((2 : ℕ) : ℤ)) =
      termG s τ w (g * (ρ : Matrix (Fin 2) (Fin 2) ℤ)) :=
  termS_slash g ρ τ w 2 s

lemma det_SL_ne (ρ : SL(2, ℤ)) : (ρ : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
  rw [ρ.2]; exact one_ne_zero

theorem KGs_slash (M : ℕ) (s : ℝ) (ρ : SL(2, ℤ)) (τ : ℍ) {w : ℂ} (hv : 0 < w.im) :
    KGs M s ((ρ • τ : ℍ) : ℂ) w * denom ρ τ ^ (-((2 : ℕ) : ℤ)) =
      (denW (ρ : Matrix (Fin 2) (Fin 2) ℤ) w ^ 2)⁻¹ * KGs M s τ (natPt (ρ : Matrix (Fin 2) (Fin 2) ℤ) w) := by
  unfold KGs
  calc (∑' γ : CongruenceSubgroup.Gamma M, termG s ((ρ • τ : ℍ) : ℂ) w ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) *
        denom ρ τ ^ (-((2 : ℕ) : ℤ))
      = ∑' γ : CongruenceSubgroup.Gamma M, termG s ((ρ • τ : ℍ) : ℂ) w ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
          denom ρ τ ^ (-((2 : ℕ) : ℤ)) := tsum_mul_right.symm
    _ = ∑' γ : CongruenceSubgroup.Gamma M, termG s τ w (((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
          (ρ : Matrix (Fin 2) (Fin 2) ℤ)) := tsum_congr (fun γ => termG_slash _ ρ τ w s)
    _ = ∑' γ : CongruenceSubgroup.Gamma M, termG s τ w ((ρ : Matrix (Fin 2) (Fin 2) ℤ) *
          (((conjG M ρ γ : CongruenceSubgroup.Gamma M) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) := by
        refine tsum_congr (fun γ => ?_)
        have e : ((γ : SL(2, ℤ)) * ρ : SL(2, ℤ)) = ρ * ((conjG M ρ γ : CongruenceSubgroup.Gamma M) : SL(2, ℤ)) := by
          simp [conjG, mul_assoc]
        rw [← Matrix.SpecialLinearGroup.coe_mul, e, Matrix.SpecialLinearGroup.coe_mul]
    _ = ∑' γ : CongruenceSubgroup.Gamma M, termG s τ w ((ρ : Matrix (Fin 2) (Fin 2) ℤ) *
          ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) :=
        (conjG M ρ).tsum_eq (fun γ : CongruenceSubgroup.Gamma M => termG s τ w ((ρ : Matrix (Fin 2) (Fin 2) ℤ) *
          ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)))
    _ = ∑' γ : CongruenceSubgroup.Gamma M, (denW (ρ : Matrix (Fin 2) (Fin 2) ℤ) w ^ 2)⁻¹ *
          termG s τ (natPt (ρ : Matrix (Fin 2) (Fin 2) ℤ) w) ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) :=
        tsum_congr (fun γ => termG_mul_left (det_SL_ne ρ) _ s τ hv)
    _ = _ := tsum_mul_left

lemma im_natPt_SL_pos (ρ : SL(2, ℤ)) {w : ℂ} (hv : 0 < w.im) :
    0 < (natPt (ρ : Matrix (Fin 2) (Fin 2) ℤ) w).im :=
  im_natPt_pos (by rw [ρ.2]; exact one_pos) hv

theorem K0_slash {M : ℕ} [NeZero M] (hM : 3 ≤ M) (ρ : SL(2, ℤ)) (τ : ℍ) {w : ℂ} (hv : 0 < w.im) :
    K0 M ((ρ • τ : ℍ) : ℂ) w * denom ρ τ ^ (-((2 : ℕ) : ℤ)) =
      (denW (ρ : Matrix (Fin 2) (Fin 2) ℤ) w ^ 2)⁻¹ * K0 M τ (natPt (ρ : Matrix (Fin 2) (Fin 2) ℤ) w) := by
  have h1 := (tendsto_KG hM (ρ • τ).im_pos hv).mul_const (denom ρ τ ^ (-((2 : ℕ) : ℤ)))
  have h2 := (tendsto_KG hM τ.im_pos (im_natPt_SL_pos ρ hv)).const_mul
    ((denW (ρ : Matrix (Fin 2) (Fin 2) ℤ) w ^ 2)⁻¹)
  have e : (fun s => KG M s ((ρ • τ : ℍ) : ℂ) w * denom ρ τ ^ (-((2 : ℕ) : ℤ))) =
      fun s => (denW (ρ : Matrix (Fin 2) (Fin 2) ℤ) w ^ 2)⁻¹ *
        KG M s τ (natPt (ρ : Matrix (Fin 2) (Fin 2) ℤ) w) := by
    funext s
    rw [KG_eq_KGs, KG_eq_KGs]
    exact KGs_slash M s ρ τ hv
  rw [e] at h1
  exact tendsto_nhds_unique h1 h2

/-! ### `Γ₁(M) = ⊔_{b mod M} T^b Γ(M)` -/

lemma T_mul_00 (b : ℤ) (g : SL(2, ℤ)) : (ModularGroup.T ^ b * g) 0 0 = g 0 0 + b * g 1 0 := by
  simp [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_zpow, Matrix.mul_apply, Fin.sum_univ_two]

lemma T_mul_01 (b : ℤ) (g : SL(2, ℤ)) : (ModularGroup.T ^ b * g) 0 1 = g 0 1 + b * g 1 1 := by
  simp [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_zpow, Matrix.mul_apply, Fin.sum_univ_two]

lemma T_mul_10 (b : ℤ) (g : SL(2, ℤ)) : (ModularGroup.T ^ b * g) 1 0 = g 1 0 := by
  simp [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_zpow, Matrix.mul_apply, Fin.sum_univ_two]

lemma T_mul_11 (b : ℤ) (g : SL(2, ℤ)) : (ModularGroup.T ^ b * g) 1 1 = g 1 1 := by
  simp [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_zpow, Matrix.mul_apply, Fin.sum_univ_two]

lemma phiT_mem {M : ℕ} (b : ℤ) (g : CongruenceSubgroup.Gamma M) : ModularGroup.T ^ b * (g : SL(2, ℤ)) ∈ Gamma1 M := by
  obtain ⟨h00, -, h10, h11⟩ := Gamma_mem.1 g.2
  rw [Gamma1_mem]
  refine ⟨?_, ?_, ?_⟩
  · rw [T_mul_00]; push_cast; rw [h00, h10]; ring
  · rw [T_mul_11]; exact h11
  · rw [T_mul_10]; exact h10

/-- `(b, g) ↦ T^b g`. -/
def phiT (M : ℕ) [NeZero M] (p : ZMod M × CongruenceSubgroup.Gamma M) : Gamma1 M :=
  ⟨ModularGroup.T ^ ((p.1.val : ℕ) : ℤ) * (p.2 : SL(2, ℤ)), phiT_mem _ _⟩

lemma phiT_bijective (M : ℕ) [NeZero M] : Function.Bijective (phiT M) := by
  constructor
  · rintro ⟨b, g⟩ ⟨b', g'⟩ h
    have hv := congrArg (fun x : Gamma1 M => (x : SL(2, ℤ))) h
    simp only [phiT] at hv
    have h01 := congrArg (fun A : SL(2, ℤ) => ((A 0 1 : ℤ) : ZMod M)) hv
    simp only [T_mul_01] at h01
    push_cast at h01
    obtain ⟨-, g01, -, g11⟩ := Gamma_mem.1 g.2
    obtain ⟨-, g01', -, g11'⟩ := Gamma_mem.1 g'.2
    rw [g01, g11, g01', g11', ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at h01
    have hb : b = b' := by simpa using h01
    subst hb
    have hg : (g : SL(2, ℤ)) = g' := mul_left_cancel hv
    exact Prod.ext rfl (Subtype.ext hg)
  · intro γ
    obtain ⟨c00, c11, c10⟩ := (Gamma1_mem M γ).1 γ.2
    set b : ZMod M := (((γ : SL(2, ℤ)) 0 1 : ℤ) : ZMod M) with hb
    have hmem : ModularGroup.T ^ (-((b.val : ℕ) : ℤ)) * (γ : SL(2, ℤ)) ∈ CongruenceSubgroup.Gamma M := by
      rw [Gamma_mem]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [T_mul_00]; push_cast; rw [c00, c10]; ring
      · rw [T_mul_01]; push_cast; rw [ZMod.natCast_zmod_val, c11, ← hb]; ring
      · rw [T_mul_10]; exact c10
      · rw [T_mul_11]; exact c11
    refine ⟨(b, ⟨_, hmem⟩), Subtype.ext ?_⟩
    show ModularGroup.T ^ ((b.val : ℕ) : ℤ) * (ModularGroup.T ^ (-((b.val : ℕ) : ℤ)) * (γ : SL(2, ℤ))) = γ
    rw [← mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, one_mul]

/-! ### The Δ-reduction -/

variable {M : ℕ} [NeZero M]

/-- `h_x = α_i T^b` for `x = (i, b)`. -/
def hX (n : ℕ) (u : (ZMod M)ˣ) (x : HNFIdx n × ZMod M) : Matrix (Fin 2) (Fin 2) ℤ :=
  alphaHNF n u x.1 * ((ModularGroup.T ^ ((x.2.val : ℕ) : ℤ) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)

lemma det_hX {n : ℕ} (hnM : n.Coprime M) (u : (ZMod M)ˣ) (x : HNFIdx n × ZMod M) :
    (hX n u x).det = n := by
  rw [hX, Matrix.det_mul, (mem_DeltaSet.1 (alphaHNF_mem hnM u x.1)).1, Matrix.SpecialLinearGroup.det_coe,
    mul_one]

lemma det_hX_pos {n : ℕ} (hn : 0 < n) (hnM : n.Coprime M) (u : (ZMod M)ˣ) (x : HNFIdx n × ZMod M) :
    0 < (hX n u x).det := by
  rw [det_hX hnM]; exact_mod_cast hn

set_option maxHeartbeats 400000 in
theorem omegaS_eq_sum {n : ℕ} (hn : 0 < n) (hnM : n.Coprime M) (u : (ZMod M)ˣ) {s : ℝ} (hs : 0 < s)
    {z w : ℂ} (hy : 0 < z.im) (hv : 0 < w.im) :
    omegaS M 2 n (u : ZMod M) s z w =
      ∑ x : HNFIdx n × ZMod M, (denW (hX n u x) w ^ 2)⁻¹ * KGs M s z (natPt (hX n u x) w) := by
  have hσ : 1 < ((2 : ℕ) : ℝ) / 2 + s := by norm_num; linarith
  have hF : Summable (fun g : DeltaSet M n (u : ZMod M) => termG s z w g.1) :=
    summable_omegaS M 2 (by exact_mod_cast hn) _ hσ hy hv
  let e1 : Gamma1 M × HNFIdx n ≃ DeltaSet M n (u : ZMod M) :=
    Equiv.ofBijective _ (repMap_HNF_bijective hn hnM u)
  let e2 : (ZMod M × CongruenceSubgroup.Gamma M) × HNFIdx n ≃ Gamma1 M × HNFIdx n :=
    Equiv.prodCongr (Equiv.ofBijective _ (phiT_bijective M)) (Equiv.refl _)
  let e3 : (HNFIdx n × ZMod M) × CongruenceSubgroup.Gamma M ≃
      (ZMod M × CongruenceSubgroup.Gamma M) × HNFIdx n :=
    ⟨fun p => ((p.1.2, p.2), p.1.1), fun q => ((q.2, q.1.1), q.1.2), fun _ => rfl, fun _ => rfl⟩
  let E := e3.trans (e2.trans e1)
  have hE : ∀ p : (HNFIdx n × ZMod M) × CongruenceSubgroup.Gamma M,
      termG s z w (E p).1 = termG s z w (hX n u p.1 * ((p.2 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) := by
    rintro ⟨⟨i, b⟩, g⟩
    show termG s z w (alphaHNF n u i * ((ModularGroup.T ^ ((b.val : ℕ) : ℤ) * (g : SL(2, ℤ)) : SL(2, ℤ)) :
      Matrix (Fin 2) (Fin 2) ℤ)) = _
    rw [Matrix.SpecialLinearGroup.coe_mul, hX, mul_assoc]
  have hS : Summable (fun p => termG s z w (E p).1) := E.summable_iff.2 hF
  have h0 : omegaS M 2 n (u : ZMod M) s z w = ∑' p, termG s z w (E p).1 :=
    (E.tsum_eq (fun g : DeltaSet M n (u : ZMod M) => termG s z w g.1)).symm
  rw [h0, hS.tsum_prod, tsum_fintype]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  have hdet : (hX n u x).det ≠ 0 := (det_hX_pos hn hnM u x).ne'
  rw [KGs, ← tsum_mul_left]
  refine tsum_congr (fun g => ?_)
  rw [hE (x, g)]
  exact termG_mul_left hdet _ s z hv

/-! ### The limit `Omega` -/

/-- `Ω(z, w) = Σ_x (denW (h_x) w)^-2 K0(z, h_x♮ w)`, the `s → 0+` limit of `omegaS`. -/
def Omega (M : ℕ) [NeZero M] (n : ℕ) (u : (ZMod M)ˣ) (z w : ℂ) : ℂ :=
  ∑ x : HNFIdx n × ZMod M, (denW (hX n u x) w ^ 2)⁻¹ * K0 M z (natPt (hX n u x) w)

theorem tendsto_omegaS (hM : 3 ≤ M) {n : ℕ} (hn : 0 < n) (hnM : n.Coprime M) (u : (ZMod M)ˣ) {z w : ℂ}
    (hy : 0 < z.im) (hv : 0 < w.im) :
    Tendsto (fun s => omegaS M 2 n (u : ZMod M) s z w) (𝓝[>] 0) (𝓝 (Omega M n u z w)) := by
  have hsum : Tendsto (fun s => ∑ x : HNFIdx n × ZMod M, (denW (hX n u x) w ^ 2)⁻¹ *
      KGs M s z (natPt (hX n u x) w)) (𝓝[>] 0) (𝓝 (Omega M n u z w)) := by
    refine tendsto_finsetSum _ (fun x _ => Tendsto.const_mul _ ?_)
    have hv' := im_natPt_pos (det_hX_pos hn hnM u x) hv
    exact (tendsto_KG hM hy hv').congr (fun s => KG_eq_KGs M s z _)
  refine hsum.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact (omegaS_eq_sum hn hnM u hs hy hv).symm

theorem Omega_slash (hM : 3 ≤ M) {n : ℕ} (hn : 0 < n) (hnM : n.Coprime M) (u : (ZMod M)ˣ) (ρ : SL(2, ℤ))
    (τ : ℍ) {w : ℂ} (hv : 0 < w.im) :
    Omega M n u ((ρ • τ : ℍ) : ℂ) w * denom ρ τ ^ (-((2 : ℕ) : ℤ)) =
      ∑ x : HNFIdx n × ZMod M, (denW (hX n u x) w ^ 2)⁻¹ *
        ((denW (ρ : Matrix (Fin 2) (Fin 2) ℤ) (natPt (hX n u x) w) ^ 2)⁻¹ *
          K0 M τ (natPt (ρ : Matrix (Fin 2) (Fin 2) ℤ) (natPt (hX n u x) w))) := by
  rw [Omega, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [mul_assoc, K0_slash hM ρ τ (im_natPt_pos (det_hX_pos hn hnM u x) hv)]

end RamanujanPetersson.KernelSD


