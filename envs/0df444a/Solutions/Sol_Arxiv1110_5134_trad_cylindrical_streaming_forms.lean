-- Prove2me | solution 1 for Arxiv1110_5134.trad_cylindrical_streaming_forms
-- status  : ACCEPTED   (prove)
-- author  : @fl-39
-- created : 2026-11-25T08:37:09.786863+00:00
-- url     : https://prove2.me/submissions/bc4c187b-77ad-442f-b975-5b754ad54ae2

import Mathlib
import Definitions.Def_Arxiv1110_5134_Basic

open MeasureTheory Filter Topology Arxiv1110_5134
open scoped Matrix

private lemma differentiableAt_update (q : Vec3) (i : Fin 3) :
    DifferentiableAt ℝ (fun r => Function.update q i r) (q i) := by
  rw [differentiableAt_pi]
  intro j
  by_cases hij : j = i
  · subst hij
    simpa [Function.update_self] using (differentiableAt_id (x := q j))
  · simpa [Function.update_of_ne hij] using (differentiableAt_const (c := q j) (x := q i))

private lemma pd_inv_sq_smul (n : Vec3 → ℝ) (F : Vec3 → Stokes) (q : Vec3) (i : Fin 3)
    (hn : 0 < n q) (hnd : DifferentiableAt ℝ n q) (hFq : DifferentiableAt ℝ F q) :
    n q ^ 2 • pd (fun y => (n y ^ 2)⁻¹ • F y) i q =
      pd F i q - (2 / n q * pd n i q) • F q := by
  have hupd := differentiableAt_update q i
  have hupd_eq : Function.update q i (q i) = q := Function.update_eq_self i q
  have hnd' : DifferentiableAt ℝ n (Function.update q i (q i)) := by rwa [hupd_eq]
  have hFq' : DifferentiableAt ℝ F (Function.update q i (q i)) := by rwa [hupd_eq]
  have hni : DifferentiableAt ℝ (fun r => n (Function.update q i r)) (q i) := hnd'.comp (q i) hupd
  have hFi : DifferentiableAt ℝ (fun r => F (Function.update q i r)) (q i) := hFq'.comp (q i) hupd
  have hn_ne : n q ≠ 0 := hn.ne'
  have hn2 : n q ^ 2 ≠ 0 := pow_ne_zero 2 hn_ne
  have hinv := (hni.hasDerivAt.pow 2).inv (by simpa [hupd_eq] using hn2)
  have hprod := hinv.smul hFi.hasDerivAt
  have hd : deriv (fun r => (n (Function.update q i r) ^ 2)⁻¹ • F (Function.update q i r)) (q i) =
      (n (Function.update q i (q i)) ^ 2)⁻¹ • deriv (fun r => F (Function.update q i r)) (q i) +
      (-(↑2 * n (Function.update q i (q i)) ^ (2 - 1) * deriv (fun r => n (Function.update q i r)) (q i)) /
        (n (Function.update q i (q i)) ^ 2) ^ 2) • F (Function.update q i (q i)) := hprod.deriv
  unfold pd
  rw [hd]
  simp only [hupd_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one]
  ext k
  simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
  field_simp [hn_ne]
  ring

private lemma angularCons_eq_angularStream_sub (g : Vec3) (F : Vec3 → ℝ → ℝ → Stokes)
    (q : Vec3) (θ φ : ℝ)
    (hFθ : DifferentiableAt ℝ (fun θ' => F q θ' φ) θ)
    (hFφ : DifferentiableAt ℝ (fun φ' => F q θ φ') φ)
    (hθ : Real.sin θ ≠ 0) :
    angularCons g F q θ φ =
      angularStream g F q θ φ - (2 * (dirVec θ φ ⬝ᵥ g)) • F q θ φ := by
  let A : ℝ → ℝ := fun θ' => (Real.cos θ' • dirVec θ' φ - polarAxis) ⬝ᵥ g
  let B : ℝ → ℝ := fun φ' => auxS1 φ' ⬝ᵥ g
  have hA_eq : A = fun θ' =>
      Real.cos θ' * Real.sin θ' * Real.cos φ * g 0 +
      Real.cos θ' * Real.sin θ' * Real.sin φ * g 1 +
      (Real.cos θ' * Real.cos θ' - 1) * g 2 := by
    ext θ'
    simp [A, dirVec, polarAxis, dotProduct, Fin.sum_univ_three]
    ring
  have hB_eq : B = fun φ' => -Real.sin φ' * g 0 + Real.cos φ' * g 1 := by
    ext φ'
    simp [B, auxS1, dotProduct, Fin.sum_univ_three]
  have hcs : HasDerivAt (fun θ' => Real.cos θ' * Real.sin θ')
      ((-Real.sin θ) * Real.sin θ + Real.cos θ * Real.cos θ) θ :=
    (Real.hasDerivAt_cos θ).mul (Real.hasDerivAt_sin θ)
  have hcc : HasDerivAt (fun θ' => Real.cos θ' * Real.cos θ' - 1)
      ((-Real.sin θ) * Real.cos θ + Real.cos θ * (-Real.sin θ) - 0) θ :=
    ((Real.hasDerivAt_cos θ).mul (Real.hasDerivAt_cos θ)).sub (hasDerivAt_const θ 1)
  have hA : HasDerivAt A
      (((-Real.sin θ) * Real.sin θ + Real.cos θ * Real.cos θ) * Real.cos φ * g 0 +
       ((-Real.sin θ) * Real.sin θ + Real.cos θ * Real.cos θ) * Real.sin φ * g 1 +
       ((-Real.sin θ) * Real.cos θ + Real.cos θ * (-Real.sin θ) - 0) * g 2) θ := by
    rw [hA_eq]
    exact (((hcs.mul_const (Real.cos φ)).mul_const (g 0)).add
      ((hcs.mul_const (Real.sin φ)).mul_const (g 1))).add
      (hcc.mul_const (g 2))
  have hB : HasDerivAt B (-(Real.cos φ) * g 0 + (-Real.sin φ) * g 1) φ := by
    rw [hB_eq]
    exact ((Real.hasDerivAt_sin φ).neg.mul_const (g 0)).add
      ((Real.hasDerivAt_cos φ).mul_const (g 1))
  have hAF := hA.smul hFθ.hasDerivAt
  have hBF := hB.smul hFφ.hasDerivAt
  have hdAF : deriv (fun θ' => A θ' • F q θ' φ) θ =
      A θ • deriv (fun θ' => F q θ' φ) θ +
      (((-Real.sin θ) * Real.sin θ + Real.cos θ * Real.cos θ) * Real.cos φ * g 0 +
       ((-Real.sin θ) * Real.sin θ + Real.cos θ * Real.cos θ) * Real.sin φ * g 1 +
       ((-Real.sin θ) * Real.cos θ + Real.cos θ * (-Real.sin θ) - 0) * g 2) • F q θ φ := hAF.deriv
  have hdBF : deriv (fun φ' => B φ' • F q θ φ') φ =
      B φ • deriv (fun φ' => F q θ φ') φ +
      (-(Real.cos φ) * g 0 + (-Real.sin φ) * g 1) • F q θ φ := hBF.deriv
  unfold angularCons angularStream dTheta dPhi
  change (Real.sin θ)⁻¹ • (deriv (fun θ' => A θ' • F q θ' φ) θ +
      deriv (fun φ' => B φ' • F q θ φ') φ) =
    (Real.sin θ)⁻¹ • (A θ • deriv (fun θ' => F q θ' φ) θ +
      B φ • deriv (fun φ' => F q θ φ') φ) - (2 * (dirVec θ φ ⬝ᵥ g)) • F q θ φ
  rw [hdAF, hdBF]
  have hcos2 : Real.cos θ * Real.cos θ = 1 - Real.sin θ * Real.sin θ := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  ext k
  simp [A, B, dirVec, auxS1, polarAxis, dotProduct, Fin.sum_univ_three]
  rw [hcos2]
  field_simp [hθ]
  ring

theorem solution (n : Vec3 → ℝ) (F : Vec3 → ℝ → ℝ → Stokes)
    (q : Vec3) (θ φ : ℝ) (hρ : 0 < q 0) (hn : 0 < n q) (hnd : DifferentiableAt ℝ n q)
    (hFq : DifferentiableAt ℝ (fun y => F y θ φ) q)
    (hFθ : DifferentiableAt ℝ (fun θ' => F q θ' φ) θ)
    (hFφ : DifferentiableAt ℝ (fun φ' => F q θ φ') φ) (hθ : Real.sin θ ≠ 0) :
    n q ^ 2 • tradCylStream n (fun y θ' φ' => (n y ^ 2)⁻¹ • F y θ' φ') q θ φ =
      dirDot θ φ (tradCylGrad (fun y => F y θ φ) q) -
        (Real.sin θ * Real.sin φ / q 0) • dPhi F q θ φ +
        angularStream ((n q)⁻¹ • tradCylGrad n q) F q θ φ -
        (2 * (dirVec θ φ ⬝ᵥ ((n q)⁻¹ • tradCylGrad n q))) • F q θ φ ∧
    n q ^ 2 • tradCylStream n (fun y θ' φ' => (n y ^ 2)⁻¹ • F y θ' φ') q θ φ =
      (Real.sin θ * Real.cos φ) • ((q 0)⁻¹ • pd (fun y => y 0 • F y θ φ) 0 q) +
        (Real.sin θ * Real.sin φ) • ((q 0)⁻¹ • pd (fun y => F y θ φ) 1 q) +
        Real.cos θ • pd (fun y => F y θ φ) 2 q -
        (q 0)⁻¹ • deriv (fun φ' => (Real.sin θ * Real.sin φ') • F q θ φ') φ +
        angularCons ((n q)⁻¹ • tradCylGrad n q) F q θ φ := by
  have hn_ne : n q ≠ 0 := hn.ne'
  have hn2 : n q ^ 2 ≠ 0 := pow_ne_zero 2 hn_ne
  have hρ_ne : q 0 ≠ 0 := hρ.ne'
  have hpd : ∀ i : Fin 3,
      n q ^ 2 • pd (fun y => (n y ^ 2)⁻¹ • F y θ φ) i q =
      pd (fun y => F y θ φ) i q - (2 / n q * pd n i q) • F q θ φ :=
    fun i => pd_inv_sq_smul n (fun y => F y θ φ) q i hn hnd hFq
  have hdθ : deriv (fun θ' => (n q ^ 2)⁻¹ • F q θ' φ) θ =
      (n q ^ 2)⁻¹ • deriv (fun θ' => F q θ' φ) θ :=
    ((hFθ.hasDerivAt).const_smul (n q ^ 2)⁻¹).deriv
  have hdφ : deriv (fun φ' => (n q ^ 2)⁻¹ • F q θ φ') φ =
      (n q ^ 2)⁻¹ • deriv (fun φ' => F q θ φ') φ :=
    ((hFφ.hasDerivAt).const_smul (n q ^ 2)⁻¹).deriv
  have hspatial :
      n q ^ 2 • dirDot θ φ (tradCylGrad (fun y => (n y ^ 2)⁻¹ • F y θ φ) q) =
      dirDot θ φ (tradCylGrad (fun y => F y θ φ) q) -
        (2 * (dirVec θ φ ⬝ᵥ ((n q)⁻¹ • tradCylGrad n q))) • F q θ φ := by
    set F' : Vec3 → Stokes := fun y => (n y ^ 2)⁻¹ • F y θ φ
    have h0 := hpd 0
    have h1' := hpd 1
    have h2 := hpd 2
    ext k
    have h0k := congr_fun h0 k
    have h1k := congr_fun h1' k
    have h2k := congr_fun h2 k
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at h0k h1k h2k
    have h0k' : n q ^ 3 * pd F' 0 q k = n q * pd (fun y => F y θ φ) 0 q k - 2 * pd n 0 q * F q θ φ k := by
      field_simp [hn_ne] at h0k; linarith
    have h1k' : n q ^ 3 * pd F' 1 q k = n q * pd (fun y => F y θ φ) 1 q k - 2 * pd n 1 q * F q θ φ k := by
      field_simp [hn_ne] at h1k; linarith
    have h2k' : n q ^ 3 * pd F' 2 q k = n q * pd (fun y => F y θ φ) 2 q k - 2 * pd n 2 q * F q θ φ k := by
      field_simp [hn_ne] at h2k; linarith
    simp [dirDot, tradCylGrad, dirVec, dotProduct, Fin.sum_univ_three]
    field_simp [hn_ne, hρ_ne]
    linear_combination
      (Real.sin θ * Real.cos φ * q 0) * h0k' +
      (Real.sin θ * Real.sin φ) * h1k' +
      (Real.cos θ * q 0) * h2k'
  have hang_scale :
      n q ^ 2 • angularStream ((n q)⁻¹ • tradCylGrad n q)
          (fun y θ' φ' => (n y ^ 2)⁻¹ • F y θ' φ') q θ φ =
      angularStream ((n q)⁻¹ • tradCylGrad n q) F q θ φ := by
    unfold angularStream dTheta dPhi
    rw [hdθ, hdφ]
    ext k
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    field_simp [hn2]
  have hdφ_scale :
      n q ^ 2 • ((Real.sin θ * Real.sin φ / q 0) •
          dPhi (fun y θ' φ' => (n y ^ 2)⁻¹ • F y θ' φ') q θ φ) =
      (Real.sin θ * Real.sin φ / q 0) • dPhi F q θ φ := by
    unfold dPhi
    rw [hdφ]
    ext k
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp [hn2]
  have h1 :
      n q ^ 2 • tradCylStream n (fun y θ' φ' => (n y ^ 2)⁻¹ • F y θ' φ') q θ φ =
      dirDot θ φ (tradCylGrad (fun y => F y θ φ) q) -
        (Real.sin θ * Real.sin φ / q 0) • dPhi F q θ φ +
        angularStream ((n q)⁻¹ • tradCylGrad n q) F q θ φ -
        (2 * (dirVec θ φ ⬝ᵥ ((n q)⁻¹ • tradCylGrad n q))) • F q θ φ := by
    unfold tradCylStream
    rw [smul_add, smul_sub, hspatial, hdφ_scale, hang_scale]
    abel
  refine ⟨h1, ?_⟩
  rw [h1]
  have hang := angularCons_eq_angularStream_sub ((n q)⁻¹ • tradCylGrad n q) F q θ φ hFθ hFφ hθ
  have hupd0 := differentiableAt_update q 0
  have hupd0_eq : Function.update q 0 (q 0) = q := Function.update_eq_self 0 q
  have hFq0 : DifferentiableAt ℝ (fun y => F y θ φ) (Function.update q 0 (q 0)) := by rwa [hupd0_eq]
  have hF0 : DifferentiableAt ℝ (fun r => F (Function.update q 0 r) θ φ) (q 0) := hFq0.comp (q 0) hupd0
  have hpd0 : pd (fun y => y 0 • F y θ φ) 0 q = F q θ φ + q 0 • pd (fun y => F y θ φ) 0 q := by
    have hp := (hasDerivAt_id (q 0)).smul hF0.hasDerivAt
    have hd : deriv (fun r => r • F (Function.update q 0 r) θ φ) (q 0) =
        q 0 • deriv (fun r => F (Function.update q 0 r) θ φ) (q 0) +
        (1 : ℝ) • F (Function.update q 0 (q 0)) θ φ := hp.deriv
    unfold pd
    have hfun : (fun r => Function.update q 0 r 0 • F (Function.update q 0 r) θ φ) =
        (fun r => r • F (Function.update q 0 r) θ φ) := by
      ext r k
      simp [Function.update_self]
    rw [hfun, hd, hupd0_eq, one_smul, add_comm]
  have hdφ_cons :
      deriv (fun φ' => (Real.sin θ * Real.sin φ') • F q θ φ') φ =
      (Real.sin θ * Real.cos φ) • F q θ φ + (Real.sin θ * Real.sin φ) • dPhi F q θ φ := by
    have hcoeff : HasDerivAt (fun φ' => Real.sin θ * Real.sin φ') (Real.sin θ * Real.cos φ) φ :=
      (Real.hasDerivAt_sin φ).const_mul (Real.sin θ)
    have hp := hcoeff.smul hFφ.hasDerivAt
    have hd : deriv (fun φ' => (Real.sin θ * Real.sin φ') • F q θ φ') φ =
        (Real.sin θ * Real.sin φ) • deriv (fun φ' => F q θ φ') φ +
        (Real.sin θ * Real.cos φ) • F q θ φ := hp.deriv
    unfold dPhi
    rw [hd, add_comm]
  rw [hang, hpd0, hdφ_cons]
  ext k
  simp [dirDot, tradCylGrad, dirVec, Fin.sum_univ_three]
  field_simp [hρ_ne]
  ring
