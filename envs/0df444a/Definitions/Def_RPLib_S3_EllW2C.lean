-- Prove2me | Definitions.Def_RPLib_S3_EllW2C
-- name    : RPLib_S3_EllW2C
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T13:03:31.974484+00:00
-- url     : https://prove2.me/theorems/ef222980-dcf7-4485-9b6b-7b74d6f2996c
-- title:
--   The Eichler-Selberg trace formula in weight two: the weight-two trace minus its scalar and elliptic terms
-- statement:
--   The weight-two trace minus its scalar and elliptic terms.
--
--   * `tendsto_diagS`: the regularised diagonal tends to the diagonal of `Ω` as `s → 0+`.
--   * `restPart0`: `conj Ω(z, -z̄) y² - scalPart - ellPart` at `k = 2` (the hyperbolic + parabolic remainder).
--   * `tendsto_restPartS_ae`: `restPartS_s → restPart0` for a.e. `z` in the fundamental domain.
--   * `integrableOn_restPart0`, **`trace_wt2_split`**:
--     `Tr(T_n ⟨δ⟩ | S_2(Γ₁(M))) = index · scalTrace + ellG1 + n C_2⁻¹ ∫_{Γ₁(M)\ℍ} restPart0`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224

import Mathlib
import Definitions.Def_RPLib_S3_EllW2B
import Definitions.Def_RPLib_S3_KernelSED

/-!
# S3-ES-Wt2 (O5, part C): the weight-two trace minus its scalar and elliptic terms

* `tendsto_diagS`: the regularised diagonal tends to the diagonal of `Ω` as `s → 0+`.
* `restPart0`: `conj Ω(z, -z̄) y² - scalPart - ellPart` at `k = 2` (the hyperbolic + parabolic remainder).
* `tendsto_restPartS_ae`: `restPartS_s → restPart0` for a.e. `z` in the fundamental domain.
* `integrableOn_restPart0`, **`trace_wt2_split`**:
  `Tr(T_n ⟨δ⟩ | S_2(Γ₁(M))) = index · scalTrace + ellG1 + n C_2⁻¹ ∫_{Γ₁(M)\ℍ} restPart0`.
-/

open MeasureTheory Metric Set Filter Complex UpperHalfPlane CongruenceSubgroup
open scoped Real ComplexConjugate NNReal ENNReal Manifold MatrixGroups Topology

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EllW2

open RamanujanPetersson.Bergman RamanujanPetersson.Kernel RP.FundDomain RP.Petersson
  RamanujanPetersson.EllTerm
open RamanujanPetersson.HeckeAlgebra (heckeTn)
open RamanujanPetersson.Diamond (diamond)

variable {M : ℕ}

theorem tendsto_diagS [NeZero M] (hM : 3 ≤ M) {n : ℕ} (hn : 0 < n) (hnM : n.Coprime M) (u : (ZMod M)ˣ)
    (z : ℍ) :
    Tendsto (fun s => conj (KernelS.omegaS M 2 n (u : ZMod M) s z (-conj (z : ℂ))) * ((z.im : ℂ) ^ 2))
      (𝓝[>] 0) (𝓝 (conj (KernelSD.Omega M n u z (-conj (z : ℂ))) * ((z.im : ℂ) ^ 2))) := by
  have hv : 0 < (-conj (z : ℂ)).im := by simpa using z.im_pos
  exact ((Complex.continuous_conj.tendsto _).comp
    (KernelSD.tendsto_omegaS hM hn hnM u (z := (z : ℂ)) z.im_pos hv)).mul_const _

/-- The weight-two hyperbolic + parabolic remainder of the diagonal. -/
def restPart0 (M : ℕ) [NeZero M] (n : ℕ) (δ : (ZMod M)ˣ) (z : ℍ) : ℂ :=
  conj (KernelSD.Omega M n (unitOf M n * δ) (z : ℂ) (-conj (z : ℂ))) * ((z.im : ℂ) ^ 2) -
    scalPart 2 M n ((unitOf M n * δ : (ZMod M)ˣ) : ZMod M) z -
      ellPart 2 M n ((unitOf M n * δ : (ZMod M)ˣ) : ZMod M) z

theorem tendsto_scalPartS (M : ℕ) (δ' : ZMod M) {n : ℕ} (hn : 0 < n) (z : ℍ) :
    Tendsto (fun s : ℝ => scalPartS 2 M n δ' s z) (𝓝[>] 0) (𝓝 (scalPart 2 M n δ' z)) := by
  have h1 : Tendsto (fun s : ℝ => (1 / 4 : ℝ) ^ s) (𝓝 0) (𝓝 1) := by
    have := (Real.continuousAt_const_rpow (b := 0) (by norm_num : (1 / 4 : ℝ) ≠ 0)).tendsto
    rwa [Real.rpow_zero] at this
  have h2 := (((Complex.continuous_ofReal.tendsto 1).comp h1).mono_left
    (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))).const_mul (scalVal 2 M n δ')
  have h3 : Tendsto (fun s : ℝ => scalVal 2 M n δ' * (((1 / 4 : ℝ) ^ s : ℝ) : ℂ)) (𝓝[>] 0)
      (𝓝 (scalVal 2 M n δ' * ((1 : ℝ) : ℂ))) := h2
  rw [Complex.ofReal_one, mul_one] at h3
  rw [scalPart_eq 2 M δ' hn z]
  exact h3.congr fun s => (scalPartS_eq 2 M δ' hn s z).symm

theorem tendsto_restPartS_ae [NeZero M] (hM : 3 ≤ M) {n : ℕ} (hn : 0 < n) (hnM : n.Coprime M)
    (δ : (ZMod M)ˣ) :
    ∀ᵐ z ∂(volume.restrict (fdom (Gamma1 M))),
      Tendsto (fun s => restPartS 2 M n ((unitOf M n * δ : (ZMod M)ˣ) : ZMod M) s z) (𝓝[>] 0)
        (𝓝 (restPart0 M n δ z)) := by
  filter_upwards [tendsto_ellPartS_ae hM 0 ((unitOf M n * δ : (ZMod M)ˣ) : ZMod M) hn] with z hz
  have hz' : Tendsto (fun s => ellPartS 2 M n ((unitOf M n * δ : (ZMod M)ˣ) : ZMod M) s z) (𝓝[>] 0)
      (𝓝 (ellPart 2 M n ((unitOf M n * δ : (ZMod M)ˣ) : ZMod M) z)) := hz
  have hD := tendsto_diagS hM hn hnM (unitOf M n * δ) z
  have hS := tendsto_scalPartS M ((unitOf M n * δ : (ZMod M)ˣ) : ZMod M) hn z
  have hev : (fun s => conj (KernelS.omegaS M 2 n ((unitOf M n * δ : (ZMod M)ˣ) : ZMod M) s z
      (-conj (z : ℂ))) * ((z.im : ℂ) ^ 2) - scalPartS 2 M n ((unitOf M n * δ : (ZMod M)ˣ) : ZMod M) s z -
      ellPartS 2 M n ((unitOf M n * δ : (ZMod M)ˣ) : ZMod M) s z) =ᶠ[𝓝[>] 0]
      fun s => restPartS 2 M n ((unitOf M n * δ : (ZMod M)ˣ) : ZMod M) s z := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have h0 : (0 : ℝ) < s := hs
    have hσ : 1 < ((2 : ℕ) : ℝ) / 2 + s := by norm_num; linarith
    rw [diagS_split hσ (n := (n : ℤ)) (by exact_mod_cast hn) _ z]
    ring
  rw [restPart0]
  exact ((hD.sub hS).sub hz').congr' hev

theorem integrableOn_restPart0 [NeZero M] (hM : 3 ≤ M) {n : ℕ} (hn : 0 < n) (hnM : n.Coprime M)
    (δ : (ZMod M)ˣ) : IntegrableOn (restPart0 M n δ) (fdom (Gamma1 M)) :=
  ((KernelSD.integrableOn_Omega_diag hM hn hnM δ).sub (scal_trace_term' (k := 2) le_rfl hn hnM δ).1).sub
    (ell_trace_term' hM (k := 2) le_rfl hn hnM δ).1

/-- **The weight-two trace minus the scalar and elliptic terms** is the integral of the remainder. -/
theorem trace_wt2_split [NeZero M] (hM : 3 ≤ M) {n : ℕ} (hn : 0 < n) (hnM : n.Coprime M) (δ : (ZMod M)ˣ) :
    LinearMap.trace ℂ (RamanujanPetersson.Diamond.S1 M ((2 : ℕ) : ℤ))
        (heckeTn ((2 : ℕ) : ℤ) n * diamond ((2 : ℕ) : ℤ) δ) =
      ((pmSL (Gamma1 M)).index : ℂ) * scalTrace M 2 n (δ : ZMod M) + ((S3.ellG1 M 2 n (δ : ZMod M) : ℚ) : ℂ) +
        (n : ℂ) ^ (2 - 1) * (bergmanConst 2)⁻¹ * ∫ z in fdom (Gamma1 M), restPart0 M n δ z := by
  obtain ⟨hSi, hSv⟩ := scal_trace_term' (M := M) (k := 2) le_rfl hn hnM δ
  obtain ⟨hEi, hEv⟩ := ell_trace_term' hM (k := 2) le_rfl hn hnM δ
  have hR := integrableOn_restPart0 hM hn hnM δ
  have e : (fun z : ℍ => conj (KernelSD.Omega M n (unitOf M n * δ) (z : ℂ) (-conj (z : ℂ))) *
      ((z.im : ℂ) ^ 2)) = fun z => scalPart 2 M n ((unitOf M n * δ : (ZMod M)ˣ) : ZMod M) z +
        ellPart 2 M n ((unitOf M n * δ : (ZMod M)ˣ) : ZMod M) z + restPart0 M n δ z := by
    funext z
    rw [restPart0]
    ring
  have hSE : IntegrableOn (fun z => scalPart 2 M n ((unitOf M n * δ : (ZMod M)ˣ) : ZMod M) z +
      ellPart 2 M n ((unitOf M n * δ : (ZMod M)ˣ) : ZMod M) z) (fdom (Gamma1 M)) := hSi.add hEi
  rw [KernelSD.trace_eq_integral_Omega hM hn hnM δ, e, integral_add hSE hR,
    integral_add hSi hEi, mul_add, mul_add, hSv, hEv]

end RamanujanPetersson.EllW2


