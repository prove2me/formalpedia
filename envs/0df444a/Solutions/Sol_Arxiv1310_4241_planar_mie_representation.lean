-- Prove2me | solution 1 for Arxiv1310_4241.planar_mie_representation
-- status  : ACCEPTED   (prove)
-- author  : @fl-39
-- created : 2026-11-25T19:21:24.673648+00:00
-- url     : https://prove2.me/submissions/b775e2fa-500a-4fe5-adad-dfe3bc8f9572

import Mathlib
import Definitions.Def_Arxiv1310_4241_Basic

open MeasureTheory Filter Topology Arxiv1310_4241

private lemma isOpen_upperHalfSpace : IsOpen upperHalfSpace :=
  isOpen_lt continuous_const (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).continuous

private lemma contDiffAt_pd {n : ℕ} {f : Space → ℂ} {p : Space} (i : Fin 3)
    (hf : ContDiffAt ℝ (n + 1 : ℕ) f p) :
    ContDiffAt ℝ n (pd i f) p := by
  have h1 : ContDiffAt ℝ n (fderiv ℝ f) p := hf.fderiv_right (by norm_cast)
  have h2 : ContDiffAt ℝ n (fun L : Space →L[ℝ] ℂ => L (EuclideanSpace.single i (1 : ℝ))) (fderiv ℝ f p) :=
    (ContinuousLinearMap.apply ℝ ℂ (EuclideanSpace.single i (1 : ℝ))).contDiff.contDiffAt
  exact h2.comp p h1

private lemma differentiableAt_pd {f : Space → ℂ} {p : Space} (i : Fin 3)
    (hf : ContDiffAt ℝ (2 : ℕ) f p) :
    DifferentiableAt ℝ (pd i f) p :=
  (contDiffAt_pd (n := 1) i hf).differentiableAt (by norm_num)

private lemma pd_congr_nhds {f g : Space → ℂ} {p : Space} (i : Fin 3) (h : f =ᶠ[𝓝 p] g) :
    pd i f p = pd i g p := by
  simp only [pd, h.fderiv_eq]

private lemma pd_add {f g : Space → ℂ} {p : Space} {i : Fin 3}
    (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g p) :
    pd i (fun q => f q + g q) p = pd i f p + pd i g p := by
  simp [pd, fderiv_fun_add hf hg]

private lemma pd_sub {f g : Space → ℂ} {p : Space} {i : Fin 3}
    (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g p) :
    pd i (fun q => f q - g q) p = pd i f p - pd i g p := by
  simp [pd, fderiv_fun_sub hf hg]

private lemma pd_neg {f : Space → ℂ} {p : Space} (i : Fin 3) :
    pd i (fun q => -f q) p = -pd i f p := by
  simp [pd, fderiv_fun_neg]

private lemma pd_const_mul {f : Space → ℂ} {p : Space} (i : Fin 3) (c : ℂ)
    (hf : DifferentiableAt ℝ f p) :
    pd i (fun q => c * f q) p = c * pd i f p := by
  have h : HasFDerivAt (fun q => c * f q) (c • fderiv ℝ f p) p :=
    hf.hasFDerivAt.const_mul c
  rw [pd, h.fderiv]
  simp [pd]

private lemma pd_zero (i : Fin 3) (p : Space) : pd i (fun _ => (0 : ℂ)) p = 0 := by
  simp [pd]

private lemma pd_comm {f : Space → ℂ} {p : Space} (i j : Fin 3)
    (hf : ContDiffAt ℝ (2 : ℕ) f p) :
    pd i (pd j f) p = pd j (pd i f) p := by
  have hfd : DifferentiableAt ℝ (fderiv ℝ f) p :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have heq : ∀ k : Fin 3, pd i (pd k f) p =
      (fderiv ℝ (fderiv ℝ f) p (EuclideanSpace.single i 1)) (EuclideanSpace.single k 1) := by
    intro k
    have hcomp : HasFDerivAt (pd k f)
        ((ContinuousLinearMap.apply ℝ ℂ (EuclideanSpace.single k (1 : ℝ))).comp
          (fderiv ℝ (fderiv ℝ f) p)) p :=
      (ContinuousLinearMap.apply ℝ ℂ (EuclideanSpace.single k (1 : ℝ))).hasFDerivAt.comp p
        hfd.hasFDerivAt
    rw [pd, hcomp.fderiv]
    rfl
  have heq' : ∀ k : Fin 3, pd j (pd k f) p =
      (fderiv ℝ (fderiv ℝ f) p (EuclideanSpace.single j 1)) (EuclideanSpace.single k 1) := by
    intro k
    have hcomp : HasFDerivAt (pd k f)
        ((ContinuousLinearMap.apply ℝ ℂ (EuclideanSpace.single k (1 : ℝ))).comp
          (fderiv ℝ (fderiv ℝ f) p)) p :=
      (ContinuousLinearMap.apply ℝ ℂ (EuclideanSpace.single k (1 : ℝ))).hasFDerivAt.comp p
        hfd.hasFDerivAt
    rw [pd, hcomp.fderiv]
    rfl
  rw [heq j, heq' i]
  exact (hf.isSymmSndFDerivAt (by norm_num)).eq (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)

private lemma curl_zhatField (u : Space → ℂ) (p : Space) :
    curl (zhatField u) p = ![pd 1 u p, -pd 0 u p, 0] := by
  ext i
  fin_cases i
  · simp [curl, zhatField, pd_zero]
  · simp [curl, zhatField, pd_zero]
  · simp [curl, zhatField, pd_zero]

private lemma curl_curl_zhatField (u : Space → ℂ) (p : Space) :
    curl (curl (zhatField u)) p =
      ![pd 2 (pd 0 u) p, pd 2 (pd 1 u) p, -(pd 0 (pd 0 u) p + pd 1 (pd 1 u) p)] := by
  have hcz : curl (zhatField u) = fun q => ![pd 1 u q, -pd 0 u q, 0] := by
    ext q i; exact congrFun (curl_zhatField u q) i
  rw [hcz]
  ext i
  fin_cases i
  · simp [curl, pd_zero, pd_neg]
  · simp [curl, pd_zero]
  · simp [curl, pd_neg]; ring

private lemma differentiableAt_curl_zhatField {u : Space → ℂ} {p : Space}
    (hu : ContDiffAt ℝ (2 : ℕ) u p) :
    DifferentiableAt ℝ (curl (zhatField u)) p := by
  rw [differentiableAt_pi]
  intro i
  have hcz : (fun q => curl (zhatField u) q i) = fun q => (![pd 1 u q, -pd 0 u q, 0] : Fin 3 → ℂ) i := by
    ext q; exact congrFun (curl_zhatField u q) i
  rw [hcz]
  fin_cases i
  · exact differentiableAt_pd 1 hu
  · exact (differentiableAt_pd 0 hu).neg
  · exact differentiableAt_const 0

private lemma differentiableAt_curl_curl_zhatField {u : Space → ℂ} {p : Space}
    (hu : ContDiffAt ℝ (3 : ℕ) u p) :
    DifferentiableAt ℝ (curl (curl (zhatField u))) p := by
  rw [differentiableAt_pi]
  intro i
  have hcc : (fun q => curl (curl (zhatField u)) q i) =
      fun q => (![pd 2 (pd 0 u) q, pd 2 (pd 1 u) q, -(pd 0 (pd 0 u) q + pd 1 (pd 1 u) q)] : Fin 3 → ℂ) i := by
    ext q; exact congrFun (curl_curl_zhatField u q) i
  rw [hcc]
  fin_cases i
  · exact differentiableAt_pd 2 (contDiffAt_pd (n := 2) 0 hu)
  · exact differentiableAt_pd 2 (contDiffAt_pd (n := 2) 1 hu)
  · exact ((differentiableAt_pd 0 (contDiffAt_pd (n := 2) 0 hu)).add
      (differentiableAt_pd 1 (contDiffAt_pd (n := 2) 1 hu))).neg

private lemma curl_add {F G : Space → Fin 3 → ℂ} {p : Space}
    (hF : DifferentiableAt ℝ F p) (hG : DifferentiableAt ℝ G p) :
    curl (fun q => F q + G q) p = curl F p + curl G p := by
  have hFc : ∀ i, DifferentiableAt ℝ (fun q => F q i) p := (differentiableAt_pi.mp hF)
  have hGc : ∀ i, DifferentiableAt ℝ (fun q => G q i) p := (differentiableAt_pi.mp hG)
  ext i
  fin_cases i <;> simp [curl, pd_add (hFc _) (hGc _)] <;> ring

private lemma curl_sub {F G : Space → Fin 3 → ℂ} {p : Space}
    (hF : DifferentiableAt ℝ F p) (hG : DifferentiableAt ℝ G p) :
    curl (fun q => F q - G q) p = curl F p - curl G p := by
  have hFc : ∀ i, DifferentiableAt ℝ (fun q => F q i) p := (differentiableAt_pi.mp hF)
  have hGc : ∀ i, DifferentiableAt ℝ (fun q => G q i) p := (differentiableAt_pi.mp hG)
  ext i
  fin_cases i <;> simp [curl, pd_sub (hFc _) (hGc _)] <;> ring

private lemma curl_smul {F : Space → Fin 3 → ℂ} {p : Space} (c : ℂ)
    (hF : DifferentiableAt ℝ F p) :
    curl (fun q => c • F q) p = c • curl F p := by
  have hFc : ∀ i, DifferentiableAt ℝ (fun q => F q i) p := (differentiableAt_pi.mp hF)
  ext i
  fin_cases i <;> simp [curl, pd_const_mul _ c (hFc _)] <;> ring

private lemma div_add {F G : Space → Fin 3 → ℂ} {p : Space}
    (hF : DifferentiableAt ℝ F p) (hG : DifferentiableAt ℝ G p) :
    divergence (fun q => F q + G q) p = divergence F p + divergence G p := by
  have hFc : ∀ i, DifferentiableAt ℝ (fun q => F q i) p := (differentiableAt_pi.mp hF)
  have hGc : ∀ i, DifferentiableAt ℝ (fun q => G q i) p := (differentiableAt_pi.mp hG)
  simp only [divergence, Pi.add_apply, pd_add (hFc _) (hGc _)]
  ring

private lemma div_sub {F G : Space → Fin 3 → ℂ} {p : Space}
    (hF : DifferentiableAt ℝ F p) (hG : DifferentiableAt ℝ G p) :
    divergence (fun q => F q - G q) p = divergence F p - divergence G p := by
  have hFc : ∀ i, DifferentiableAt ℝ (fun q => F q i) p := (differentiableAt_pi.mp hF)
  have hGc : ∀ i, DifferentiableAt ℝ (fun q => G q i) p := (differentiableAt_pi.mp hG)
  simp only [divergence, Pi.sub_apply, pd_sub (hFc _) (hGc _)]
  ring

private lemma div_smul {F : Space → Fin 3 → ℂ} {p : Space} (c : ℂ)
    (hF : DifferentiableAt ℝ F p) :
    divergence (fun q => c • F q) p = c * divergence F p := by
  have hFc : ∀ i, DifferentiableAt ℝ (fun q => F q i) p := (differentiableAt_pi.mp hF)
  simp only [divergence, Pi.smul_apply, smul_eq_mul, pd_const_mul _ c (hFc _)]
  ring

private lemma div_curl_zhatField {u : Space → ℂ} {p : Space}
    (hu : ContDiffAt ℝ (2 : ℕ) u p) :
    divergence (curl (zhatField u)) p = 0 := by
  have hcz : curl (zhatField u) = fun q => ![pd 1 u q, -pd 0 u q, 0] := by
    ext q i; exact congrFun (curl_zhatField u q) i
  rw [hcz]
  simp only [divergence, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, pd_neg, pd_zero, add_zero]
  rw [pd_comm 0 1 hu]
  ring

private lemma div_curl_curl_zhatField {u : Space → ℂ}
    (hu : ContDiffOn ℝ 3 u upperHalfSpace) {p : Space} (hp : p ∈ upperHalfSpace) :
    divergence (curl (curl (zhatField u))) p = 0 := by
  have hcc : curl (curl (zhatField u)) =
      fun q => ![pd 2 (pd 0 u) q, pd 2 (pd 1 u) q, -(pd 0 (pd 0 u) q + pd 1 (pd 1 u) q)] := by
    ext q i; exact congrFun (curl_curl_zhatField u q) i
  rw [hcc]
  have hup : ContDiffAt ℝ (3 : ℕ) u p := hu.contDiffAt (isOpen_upperHalfSpace.mem_nhds hp)
  have hu00 : DifferentiableAt ℝ (pd 0 (pd 0 u)) p := differentiableAt_pd 0 (contDiffAt_pd (n := 2) 0 hup)
  have hu11 : DifferentiableAt ℝ (pd 1 (pd 1 u)) p := differentiableAt_pd 1 (contDiffAt_pd (n := 2) 1 hup)
  simp only [divergence, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, pd_neg, pd_add hu00 hu11]
  have hcomm_nhds : ∀ i j : Fin 3, pd i (pd j u) =ᶠ[𝓝 p] pd j (pd i u) := by
    intro i j
    filter_upwards [isOpen_upperHalfSpace.mem_nhds hp] with q hq
    exact pd_comm i j ((hu.contDiffAt (isOpen_upperHalfSpace.mem_nhds hq)).of_le (by norm_num))
  have h020 : pd 0 (pd 2 (pd 0 u)) p = pd 2 (pd 0 (pd 0 u)) p := by
    rw [pd_congr_nhds 0 (hcomm_nhds 2 0), pd_comm 0 0 (contDiffAt_pd (n := 2) 2 hup)]
    -- wait: pd 0 (pd 0 (pd 2 u)) p = pd 2 (pd 0 (pd 0 u)) p
    have h1 : pd 0 (pd 0 (pd 2 u)) p = pd 0 (pd 2 (pd 0 u)) p :=
      pd_congr_nhds 0 (hcomm_nhds 0 2)
    have h2 : pd 2 (pd 0 (pd 0 u)) p = pd 0 (pd 2 (pd 0 u)) p :=
      pd_comm 2 0 (contDiffAt_pd (n := 2) 0 hup)
    rw [h2]
    exact h1
  have h121 : pd 1 (pd 2 (pd 1 u)) p = pd 2 (pd 1 (pd 1 u)) p :=
    (pd_comm 2 1 (contDiffAt_pd (n := 2) 1 hup)).symm
  rw [h020, h121]
  ring

private lemma curl_curl_curl_zhatField {k : ℂ} {u : Space → ℂ}
    (hu : ContDiffOn ℝ 3 u upperHalfSpace) (hHu : IsHelmholtzOn k upperHalfSpace u)
    {p : Space} (hp : p ∈ upperHalfSpace) :
    curl (curl (curl (zhatField u))) p = k ^ 2 • curl (zhatField u) p := by
  have hcc : curl (curl (zhatField u)) =
      fun q => ![pd 2 (pd 0 u) q, pd 2 (pd 1 u) q, -(pd 0 (pd 0 u) q + pd 1 (pd 1 u) q)] := by
    ext q i; exact congrFun (curl_curl_zhatField u q) i
  rw [hcc, curl_zhatField]
  have hup : ContDiffAt ℝ (3 : ℕ) u p := hu.contDiffAt (isOpen_upperHalfSpace.mem_nhds hp)
  have hu00 : DifferentiableAt ℝ (pd 0 (pd 0 u)) p := differentiableAt_pd 0 (contDiffAt_pd (n := 2) 0 hup)
  have hu11 : DifferentiableAt ℝ (pd 1 (pd 1 u)) p := differentiableAt_pd 1 (contDiffAt_pd (n := 2) 1 hup)
  have hu22 : DifferentiableAt ℝ (pd 2 (pd 2 u)) p := differentiableAt_pd 2 (contDiffAt_pd (n := 2) 2 hup)
  have hcomm_nhds : ∀ i j : Fin 3, pd i (pd j u) =ᶠ[𝓝 p] pd j (pd i u) := by
    intro i j
    filter_upwards [isOpen_upperHalfSpace.mem_nhds hp] with q hq
    exact pd_comm i j ((hu.contDiffAt (isOpen_upperHalfSpace.mem_nhds hq)).of_le (by norm_num))
  have hlap_eq : laplacian u =ᶠ[𝓝 p] fun q => -(k ^ 2) * u q := by
    filter_upwards [isOpen_upperHalfSpace.mem_nhds hp] with q hq
    have := hHu q hq
    linear_combination this
  have hpd_lap : ∀ j : Fin 3, pd j (laplacian u) p = -(k ^ 2) * pd j u p := by
    intro j
    rw [pd_congr_nhds j hlap_eq, pd_const_mul j _ (hup.differentiableAt (by norm_num))]
  have hlap_expand : ∀ j : Fin 3,
      pd j (laplacian u) p = pd j (pd 0 (pd 0 u)) p + pd j (pd 1 (pd 1 u)) p + pd j (pd 2 (pd 2 u)) p := by
    intro j
    unfold laplacian
    rw [pd_add (hu00.fun_add hu11) hu22, pd_add hu00 hu11]
  ext i
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, curl, Pi.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      pd_neg, pd_add hu00 hu11]
    have hswap : pd 2 (pd 2 (pd 1 u)) p = pd 1 (pd 2 (pd 2 u)) p := by
      rw [pd_congr_nhds 2 (hcomm_nhds 2 1), pd_comm 2 1 (contDiffAt_pd (n := 2) 2 hup)]
    rw [hswap]
    have h1 := hpd_lap 1
    rw [hlap_expand 1] at h1
    linear_combination -h1
  · simp only [Fin.mk_one, Fin.isValue, curl, Pi.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      pd_neg, pd_add hu00 hu11]
    have hswap : pd 2 (pd 2 (pd 0 u)) p = pd 0 (pd 2 (pd 2 u)) p := by
      rw [pd_congr_nhds 2 (hcomm_nhds 2 0), pd_comm 2 0 (contDiffAt_pd (n := 2) 2 hup)]
    rw [hswap]
    have h0 := hpd_lap 0
    rw [hlap_expand 0] at h0
    linear_combination h0
  · simp only [Fin.reduceFinMk, Fin.isValue, curl, Pi.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      mul_zero]
    rw [pd_congr_nhds 0 (hcomm_nhds 2 1), pd_congr_nhds 1 (hcomm_nhds 2 0),
      pd_comm 0 1 (contDiffAt_pd (n := 2) 2 hup), sub_self]

private lemma wavenumber_sq (ω : ℝ) (ε μ : ℂ) :
    (wavenumber ω ε μ) ^ 2 = (ω : ℂ) ^ 2 * ε * μ := by
  rw [wavenumber, mul_pow]
  have hsq : ((ε * μ) ^ (1 / 2 : ℂ)) ^ 2 = ε * μ := by
    by_cases h : ε * μ = 0
    · simp [h]
    · rw [sq, ← Complex.cpow_add _ _ h]; norm_num
  rw [hsq]
  ring

theorem solution (ω : ℝ) (ε μ : ℂ)
    (hk : IsCausalWavenumber (wavenumber ω ε μ)) (u v : Space → ℂ)
    (hu : ContDiffOn ℝ 3 u upperHalfSpace) (hv : ContDiffOn ℝ 3 v upperHalfSpace)
    (hHu : IsHelmholtzOn (wavenumber ω ε μ) upperHalfSpace u)
    (hHv : IsHelmholtzOn (wavenumber ω ε μ) upperHalfSpace v) :
    IsSourceFreeMaxwellOn ω ε μ upperHalfSpace (mieE ω μ u v) (mieH ω ε u v) ∧
    ∀ p ∈ upperHalfSpace, mieE ω μ u v p 2 = -transverseLaplacian u p ∧
      mieH ω ε u v p 2 = -transverseLaplacian v p := by
  have hk2 : (wavenumber ω ε μ) ^ 2 = (Complex.I * ω * μ) * (-(Complex.I * ω * ε)) := by
    rw [wavenumber_sq]
    ring_nf; simp [Complex.I_sq]
  constructor
  · intro p hp
    have hup : ContDiffAt ℝ (3 : ℕ) u p := hu.contDiffAt (isOpen_upperHalfSpace.mem_nhds hp)
    have hvp : ContDiffAt ℝ (3 : ℕ) v p := hv.contDiffAt (isOpen_upperHalfSpace.mem_nhds hp)
    have hcu : DifferentiableAt ℝ (curl (zhatField u)) p :=
      differentiableAt_curl_zhatField (hup.of_le (by norm_num))
    have hcv : DifferentiableAt ℝ (curl (zhatField v)) p :=
      differentiableAt_curl_zhatField (hvp.of_le (by norm_num))
    have hccu : DifferentiableAt ℝ (curl (curl (zhatField u))) p :=
      differentiableAt_curl_curl_zhatField hup
    have hccv : DifferentiableAt ℝ (curl (curl (zhatField v))) p :=
      differentiableAt_curl_curl_zhatField hvp
    have hscv : DifferentiableAt ℝ (fun q => (Complex.I * ω * μ) • curl (zhatField v) q) p :=
      DifferentiableAt.fun_const_smul hcv _
    have hscu : DifferentiableAt ℝ (fun q => (Complex.I * ω * ε) • curl (zhatField u) q) p :=
      DifferentiableAt.fun_const_smul hcu _
    refine ⟨hccu.fun_add hscv, hccv.fun_sub hscu, ?_, ?_, ?_, ?_⟩
    · -- curl E = iωμ H
      unfold mieE mieH
      rw [curl_add hccu hscv, curl_smul _ hcv,
        curl_curl_curl_zhatField hu hHu hp, hk2]
      ext i
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    · -- curl H = -iωε E
      unfold mieE mieH
      rw [curl_sub hccv hscu, curl_smul _ hcu,
        curl_curl_curl_zhatField hv hHv hp, hk2]
      ext i
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    · -- div E = 0
      unfold mieE
      rw [div_add hccu hscv, div_smul _ hcv,
        div_curl_curl_zhatField hu hp, div_curl_zhatField (hvp.of_le (by norm_num))]
      ring
    · -- div H = 0
      unfold mieH
      rw [div_sub hccv hscu, div_smul _ hcu,
        div_curl_curl_zhatField hv hp, div_curl_zhatField (hup.of_le (by norm_num))]
      ring
  · intro p _hp
    constructor
    · simp only [mieE, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [curl_curl_zhatField, curl_zhatField]
      simp [transverseLaplacian]
    · simp only [mieH, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [curl_curl_zhatField, curl_zhatField]
      simp [transverseLaplacian]
