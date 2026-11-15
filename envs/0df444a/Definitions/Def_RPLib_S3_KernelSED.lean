-- Prove2me | Definitions.Def_RPLib_S3_KernelSED
-- name    : RPLib_S3_KernelSED
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T13:00:25.686611+00:00
-- url     : https://prove2.me/theorems/04b02516-bc44-47fd-91fe-23888bacb5a4
-- title:
--   The Eichler-Selberg trace formula in weight two: `Ω` is the reproducing kernel of `T_n ⟨δ⟩` on `S_2(Γ₁(M))`
-- statement:
--   `Ω` is the reproducing kernel of `T_n ⟨δ⟩` on `S_2(Γ₁(M))`.
--
--   * `tendsto_bergmanConstS`: `C_k(s) → C_k(0) = bergmanConst k` as `s → 0+`.
--   * **`reproducing0`**: `(T_n ⟨δ⟩ f)(z) = n C_2⁻¹ ⟪Ω(·, -conj z), f⟫` (limit `s → 0+` of `reproducingS`).
--   * **`Hdiag_eq_Omega`**: `Hdiag z = n C_2⁻¹ conj(Ω(z, -conj z)) y²` (orthonormal expansion of `Ω(·, -conj z) ∈ S_2`).
--   * **`trace_eq_integral_Omega`**: `Tr(T_n ⟨δ⟩ | S_2(Γ₁(M))) = n C_2⁻¹ ∫_{fdom} conj(Ω(z, -conj z)) y²`.
--   * `integrableOn_Hdiag`, `integrableOn_Omega_diag`: the integrands are integrable on `fdom Γ₁(M)`.
--   * `projS_eq`: `projS_s z = conj(C_2(s) / C_2) Ω(z, -conj z)`; `tendsto_defect`: `ω_s(z, -conj z) - projS_s z → 0`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224; F. Diamond and J. Shurman, A First Course in Modular Forms, GTM 228, Springer 2005, Chapter 5

import Mathlib
import Definitions.Def_RPLib_S3_KernelSEC

/-!
# S3-ES-Wt2, part KS_E (D): `Ω` is the reproducing kernel of `T_n ⟨δ⟩` on `S_2(Γ₁(M))`

* `tendsto_bergmanConstS`: `C_k(s) → C_k(0) = bergmanConst k` as `s → 0+`.
* **`reproducing0`**: `(T_n ⟨δ⟩ f)(z) = n C_2⁻¹ ⟪Ω(·, -conj z), f⟫` (limit `s → 0+` of `reproducingS`).
* **`Hdiag_eq_Omega`**: `Hdiag z = n C_2⁻¹ conj(Ω(z, -conj z)) y²` (orthonormal expansion of `Ω(·, -conj z) ∈ S_2`).
* **`trace_eq_integral_Omega`**: `Tr(T_n ⟨δ⟩ | S_2(Γ₁(M))) = n C_2⁻¹ ∫_{fdom} conj(Ω(z, -conj z)) y²`.
* `integrableOn_Hdiag`, `integrableOn_Omega_diag`: the integrands are integrable on `fdom Γ₁(M)`.
* `projS_eq`: `projS_s z = conj(C_2(s) / C_2) Ω(z, -conj z)`; `tendsto_defect`: `ω_s(z, -conj z) - projS_s z → 0`.
-/

open Complex Filter Topology UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups Manifold ComplexConjugate

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.KernelSD

open RP.FundDomain RP.Petersson RamanujanPetersson.Kernel RamanujanPetersson.KernelS
  RamanujanPetersson.Bergman RamanujanPetersson.BergmanS RamanujanPetersson.Hecke
open RamanujanPetersson.HeckeAlgebra (heckeTn)
open RamanujanPetersson.Diamond (diamond)

lemma tendsto_bergmanConstS {k : ℕ} (hk : 2 ≤ k) :
    Tendsto (fun s : ℝ => bergmanConstS k s) (𝓝[>] 0) (𝓝 (bergmanConst k)) := by
  rw [← bergmanConstS_zero]
  refine (ContinuousAt.tendsto ?_).mono_left nhdsWithin_le_nhds
  unfold bergmanConstS
  have h4 : ContinuousAt (fun s : ℝ => (((4 : ℝ) ^ s : ℝ) : ℂ)) 0 :=
    Complex.continuous_ofReal.continuousAt.comp (Real.continuousAt_const_rpow (by norm_num))
  have hlin : ContinuousAt (fun s : ℝ => ((k : ℂ) - 1 + (s : ℂ))) 0 :=
    continuousAt_const.add Complex.continuous_ofReal.continuousAt
  refine ContinuousAt.div continuousAt_const ((hlin.mul continuousAt_const).mul h4) ?_
  have h1 : ((k : ℂ) - 1 + ((0 : ℝ) : ℂ)) ≠ 0 := by
    rw [Complex.ofReal_zero, add_zero, sub_ne_zero]
    exact_mod_cast (by omega : k ≠ 1)
  have h3 : (((4 : ℝ) ^ (0 : ℝ) : ℝ) : ℂ) ≠ 0 := by simp
  exact mul_ne_zero (mul_ne_zero h1 (pow_ne_zero _ two_ne_zero)) h3

variable {M : ℕ} [NeZero M]

/-- **`Ω` reproduces `T_n ⟨δ⟩` on `S_2(Γ₁(M))`.** -/
theorem reproducing0 (hM : 3 ≤ M) {n : ℕ} (hn : 0 < n) (hnM : n.Coprime M) (δ : (ZMod M)ˣ)
    (f : RamanujanPetersson.Diamond.S1 M ((2 : ℕ) : ℤ)) (z : ℍ) :
    ((heckeTn ((2 : ℕ) : ℤ) n * diamond ((2 : ℕ) : ℤ) δ :
        Module.End ℂ (RamanujanPetersson.Diamond.S1 M ((2 : ℕ) : ℤ))) f) z =
      (n : ℂ) ^ (2 - 1) * (bergmanConst 2)⁻¹ *
        peterssonInner (Gamma1 M) ((2 : ℕ) : ℤ) (OmegaH M n (unitOf M n * δ) (-conj (z : ℂ))) f := by
  have hlim : Tendsto (fun s : ℝ => (n : ℂ) ^ (2 - 1) * (bergmanConstS 2 s)⁻¹ *
      peterssonInner (Gamma1 M) ((2 : ℕ) : ℤ)
        (omegaSH M 2 n ((unitOf M n * δ : (ZMod M)ˣ) : ZMod M) s (-conj (z : ℂ))) f) (𝓝[>] 0)
      (𝓝 ((n : ℂ) ^ (2 - 1) * (bergmanConst 2)⁻¹ *
        peterssonInner (Gamma1 M) ((2 : ℕ) : ℤ) (OmegaH M n (unitOf M n * δ) (-conj (z : ℂ))) f)) :=
    (tendsto_const_nhds.mul ((tendsto_bergmanConstS le_rfl).inv₀ (bergmanConst_ne_zero le_rfl))).mul
      (tendsto_peterssonInner hM hn hnM (unitOf M n * δ) f z)
  have hev : (fun _ : ℝ => ((heckeTn ((2 : ℕ) : ℤ) n * diamond ((2 : ℕ) : ℤ) δ :
        Module.End ℂ (RamanujanPetersson.Diamond.S1 M ((2 : ℕ) : ℤ))) f) z) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun s : ℝ => (n : ℂ) ^ (2 - 1) * (bergmanConstS 2 s)⁻¹ *
        peterssonInner (Gamma1 M) ((2 : ℕ) : ℤ)
          (omegaSH M 2 n ((unitOf M n * δ : (ZMod M)ˣ) : ZMod M) s (-conj (z : ℂ))) f) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs' : (0 : ℝ) < s := hs
    have hσ : 1 < ((2 : ℕ) : ℝ) / 2 + s := by push_cast; linarith
    exact reproducingS hM le_rfl hσ hn hnM δ f z
  exact tendsto_nhds_unique (tendsto_const_nhds.congr' hev) hlim

/-- **`Hdiag z = n C_2⁻¹ conj(Ω(z, -conj z)) y²`.** -/
theorem Hdiag_eq_Omega (hM : 3 ≤ M) {n : ℕ} (hn : 0 < n) (hnM : n.Coprime M) (δ : (ZMod M)ˣ) (z : ℍ) :
    Hdiag M 2 n δ z = (n : ℂ) ^ (2 - 1) * (bergmanConst 2)⁻¹ *
      (conj (Omega M n (unitOf M n * δ) (z : ℂ) (-conj (z : ℂ))) * ((z.im : ℂ) ^ 2)) := by
  have := finiteDimensional_PS (M := M) ((2 : ℕ) : ℤ)
  have hv : 0 < (-conj (z : ℂ)).im := by simpa using z.im_pos
  let b := onb M ((2 : ℕ) : ℤ)
  let ω : PeterssonSpace (Gamma1 M) ((2 : ℕ) : ℤ) :=
    PeterssonSpace.ofCuspForm (OmegaCF hM hn hnM (unitOf M n * δ) (-conj (z : ℂ)) hv)
  have hrep := congrArg (evalE M ((2 : ℕ) : ℤ) z) (b.sum_repr' ω)
  rw [map_sum] at hrep
  simp only [map_smul, smul_eq_mul] at hrep
  have hω : evalE M ((2 : ℕ) : ℤ) z ω = Omega M n (unitOf M n * δ) (z : ℂ) (-conj (z : ℂ)) := rfl
  have hT : ∀ j, ((heckeTn ((2 : ℕ) : ℤ) n * diamond ((2 : ℕ) : ℤ) δ :
        Module.End ℂ (RamanujanPetersson.Diamond.S1 M ((2 : ℕ) : ℤ))) (bj M 2 j)) z =
      (n : ℂ) ^ (2 - 1) * (bergmanConst 2)⁻¹ * conj (inner ℂ (b j) ω) := by
    intro j
    rw [reproducing0 hM hn hnM δ (bj M 2 j) z]
    congr 1
    rw [← peterssonInner_conj_symm]
    all_goals rfl
  have hb : ∀ j, bj M 2 j z = evalE M ((2 : ℕ) : ℤ) z (b j) := fun j => rfl
  simp only [Hdiag, hT, hb]
  rw [← hω, ← hrep]
  simp only [map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- `Hdiag` is integrable on `fdom Γ₁(M)` (a finite sum of Petersson products of cusp forms). -/
theorem integrableOn_Hdiag (k n : ℕ) (δ : (ZMod M)ˣ) :
    IntegrableOn (Hdiag M k n δ) (fdom (Gamma1 M)) := by
  have e : Hdiag M k n δ = fun z => ∑ j, petersson (k : ℤ) (bj M k j)
      ((heckeTn (k : ℤ) n * diamond (k : ℤ) δ :
        Module.End ℂ (RamanujanPetersson.Diamond.S1 M (k : ℤ))) (bj M k j)) z := by
    funext z
    simp only [Hdiag, petersson_nat]
  rw [e]
  exact integrable_finsetSum _ (fun j _ => integrableOn_petersson _ _)

/-- **`Tr(T_n ⟨δ⟩ | S_2(Γ₁(M))) = n C_2⁻¹ ∫_{fdom} conj(Ω(z, -conj z)) y²`.** -/
theorem trace_eq_integral_Omega (hM : 3 ≤ M) {n : ℕ} (hn : 0 < n) (hnM : n.Coprime M) (δ : (ZMod M)ˣ) :
    LinearMap.trace ℂ (RamanujanPetersson.Diamond.S1 M ((2 : ℕ) : ℤ))
        (heckeTn ((2 : ℕ) : ℤ) n * diamond ((2 : ℕ) : ℤ) δ) =
      (n : ℂ) ^ (2 - 1) * (bergmanConst 2)⁻¹ *
        ∫ z in fdom (Gamma1 M), conj (Omega M n (unitOf M n * δ) (z : ℂ) (-conj (z : ℂ))) *
          ((z.im : ℂ) ^ 2) := by
  rw [trace_eq_integral_Hdiag 2 n δ]
  simp_rw [Hdiag_eq_Omega hM hn hnM δ]
  exact integral_const_mul _ _

/-- The `Ω`-diagonal is integrable on `fdom Γ₁(M)`. -/
theorem integrableOn_Omega_diag (hM : 3 ≤ M) {n : ℕ} (hn : 0 < n) (hnM : n.Coprime M) (δ : (ZMod M)ˣ) :
    IntegrableOn (fun z : ℍ => conj (Omega M n (unitOf M n * δ) (z : ℂ) (-conj (z : ℂ))) *
      ((z.im : ℂ) ^ 2)) (fdom (Gamma1 M)) := by
  have hc : (n : ℂ) ^ (2 - 1) * (bergmanConst 2)⁻¹ ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.2 hn.ne')) (inv_ne_zero (bergmanConst_ne_zero le_rfl))
  have e : (fun z : ℍ => conj (Omega M n (unitOf M n * δ) (z : ℂ) (-conj (z : ℂ))) * ((z.im : ℂ) ^ 2)) =
      fun z => ((n : ℂ) ^ (2 - 1) * (bergmanConst 2)⁻¹)⁻¹ * Hdiag M 2 n δ z := by
    funext z
    rw [Hdiag_eq_Omega hM hn hnM δ, inv_mul_cancel_left₀ hc]
  rw [e]
  exact (integrableOn_Hdiag 2 n δ).const_mul _

/-- **Closed form of the projection**: `projS_s z = conj(C_2(s) / C_2) Ω(z, -conj z)` (`s > 0`). -/
theorem projS_eq (hM : 3 ≤ M) {n : ℕ} (hn : 0 < n) (hnM : n.Coprime M) (δ : (ZMod M)ˣ) {s : ℝ} (hs : 0 < s)
    (z : ℍ) :
    projS M 2 n δ s z = conj (bergmanConstS 2 s / bergmanConst 2) *
      Omega M n (unitOf M n * δ) (z : ℂ) (-conj (z : ℂ)) := by
  have hσ : 1 < ((2 : ℕ) : ℝ) / 2 + s := by push_cast; linarith
  have h1 := Hdiag_eq_projS hM le_rfl hσ hn hnM δ z
  rw [Hdiag_eq_Omega hM hn hnM δ z] at h1
  have hCs : bergmanConstS 2 s ≠ 0 := bergmanConstS_ne_zero (by push_cast; linarith)
  have hn0 : (n : ℂ) ^ (2 - 1) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hn.ne')
  have hy : ((z.im : ℂ) ^ 2) ≠ 0 := pow_ne_zero _ (Complex.ofReal_ne_zero.2 z.im_pos.ne')
  have hK : (n : ℂ) ^ (2 - 1) * (bergmanConstS 2 s)⁻¹ * ((z.im : ℂ) ^ 2) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hn0 (inv_ne_zero hCs)) hy
  have h2 : conj (projS M 2 n δ s z) = bergmanConstS 2 s / bergmanConst 2 *
      conj (Omega M n (unitOf M n * δ) (z : ℂ) (-conj (z : ℂ))) := by
    refine mul_left_cancel₀ hK ?_
    calc _ = (n : ℂ) ^ (2 - 1) * (bergmanConstS 2 s)⁻¹ * conj (projS M 2 n δ s z) * ((z.im : ℂ) ^ 2) := by
          ring
      _ = (n : ℂ) ^ (2 - 1) * (bergmanConst 2)⁻¹ *
            (conj (Omega M n (unitOf M n * δ) (z : ℂ) (-conj (z : ℂ))) * ((z.im : ℂ) ^ 2)) := h1.symm
      _ = (n : ℂ) ^ (2 - 1) * ((bergmanConstS 2 s)⁻¹ * bergmanConstS 2 s) * (bergmanConst 2)⁻¹ *
            conj (Omega M n (unitOf M n * δ) (z : ℂ) (-conj (z : ℂ))) * ((z.im : ℂ) ^ 2) := by
          rw [inv_mul_cancel₀ hCs]; ring
      _ = _ := by rw [div_eq_mul_inv]; ring
  have h3 := congrArg conj h2
  rw [Complex.conj_conj, map_mul, Complex.conj_conj] at h3
  exact h3

/-- **The projection defect tends to `0`**: `ω_s(z, -conj z) - projS_s z → 0` as `s → 0+`. -/
theorem tendsto_defect (hM : 3 ≤ M) {n : ℕ} (hn : 0 < n) (hnM : n.Coprime M) (δ : (ZMod M)ˣ) (z : ℍ) :
    Tendsto (fun s => omegaS M 2 n ((unitOf M n * δ : (ZMod M)ˣ) : ZMod M) s (z : ℂ) (-conj (z : ℂ)) -
      projS M 2 n δ s z) (𝓝[>] 0) (𝓝 0) := by
  have hW : 0 < (-conj (z : ℂ)).im := by simpa using z.im_pos
  have hO := tendsto_omegaS (z := (z : ℂ)) hM hn hnM (unitOf M n * δ) z.im_pos hW
  have hC : Tendsto (fun s : ℝ => conj (bergmanConstS 2 s / bergmanConst 2) *
      Omega M n (unitOf M n * δ) (z : ℂ) (-conj (z : ℂ))) (𝓝[>] 0)
      (𝓝 (conj (bergmanConst 2 / bergmanConst 2) * Omega M n (unitOf M n * δ) (z : ℂ) (-conj (z : ℂ)))) :=
    (((Complex.continuous_conj.tendsto _).comp
      ((tendsto_bergmanConstS le_rfl).div_const _))).mul_const _
  rw [div_self (bergmanConst_ne_zero le_rfl), map_one, one_mul] at hC
  have h := hO.sub hC
  rw [sub_self] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [projS_eq hM hn hnM δ hs z]

end RamanujanPetersson.KernelSD


