-- Prove2me | solution 1 for Arxiv1310_4241.two_layer_system_low_frequency_decoupling
-- status  : ACCEPTED   (prove)
-- author  : @fl-39
-- created : 2026-11-25T19:37:55.944391+00:00
-- url     : https://prove2.me/submissions/c0706c0a-2672-4a59-b67b-8ab796ec8517

import Mathlib
import Definitions.Def_Arxiv1310_4241_Basic
import Theorems.Thm_Arxiv1310_4241_two_layer_boundary_operators

open MeasureTheory Filter Topology Arxiv1310_4241

private lemma sommerfeldRoot_zero (ξ η : ℝ) :
    sommerfeldRoot 0 ξ η = (Real.sqrt (ξ ^ 2 + η ^ 2) : ℂ) := by
  unfold sommerfeldRoot
  have hnn : 0 ≤ ξ ^ 2 + η ^ 2 := by positivity
  have hz : (ξ : ℂ) ^ 2 + (η : ℂ) ^ 2 - (0 : ℂ) ^ 2 = ((ξ ^ 2 + η ^ 2 : ℝ) : ℂ) := by
    push_cast; ring
  rw [hz]
  have hnot : ¬((((ξ ^ 2 + η ^ 2 : ℝ) : ℂ)).im = 0 ∧ (((ξ ^ 2 + η ^ 2 : ℝ) : ℂ)).re < 0) := by
    simp only [Complex.ofReal_im, Complex.ofReal_re, true_and, not_lt]
    exact hnn
  rw [if_neg hnot, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_cpow hnn]
  norm_cast
  rw [Real.sqrt_eq_rpow]

private lemma continuousAt_sommerfeldRoot_zero (ε μ : ℂ) (ξ η : ℝ) (hρ : 0 < ξ ^ 2 + η ^ 2) :
    ContinuousAt (fun ω : ℝ => sommerfeldRoot (wavenumber ω ε μ) ξ η) 0 := by
  let f : ℝ → ℂ := fun ω => (ξ : ℂ) ^ 2 + (η : ℂ) ^ 2 - (wavenumber ω ε μ) ^ 2
  have hf_cont : Continuous f := by unfold f wavenumber; fun_prop
  have hf0 : f 0 = ((ξ ^ 2 + η ^ 2 : ℝ) : ℂ) := by simp [f, wavenumber]
  have hre0 : 0 < (f 0).re := by rw [hf0, Complex.ofReal_re]; exact hρ
  have hcpow_cont : ContinuousAt (fun z : ℂ => z ^ (1 / 2 : ℂ)) (f 0) := by
    have hlog : ContinuousAt Complex.log (f 0) := (Complex.hasDerivAt_log (Or.inl hre0)).continuousAt
    have hcont : ContinuousAt (fun z : ℂ => Complex.exp (Complex.log z * (1 / 2 : ℂ))) (f 0) :=
      Complex.continuous_exp.continuousAt.comp (hlog.mul continuousAt_const)
    have hf0_ne : f 0 ≠ 0 := by intro h; rw [h, Complex.zero_re] at hre0; exact lt_irrefl 0 hre0
    have hev0 : ∀ᶠ z in 𝓝 (f 0), z ≠ 0 := continuousAt_id.eventually_ne hf0_ne
    exact hcont.congr (hev0.mono fun z hz => (Complex.cpow_def_of_ne_zero hz _).symm)
  have hcomp : ContinuousAt (fun ω : ℝ => (f ω) ^ (1 / 2 : ℂ)) 0 :=
    hcpow_cont.comp hf_cont.continuousAt
  have hev : (fun ω : ℝ => sommerfeldRoot (wavenumber ω ε μ) ξ η) =ᶠ[𝓝 (0 : ℝ)]
      fun ω : ℝ => (f ω) ^ (1 / 2 : ℂ) := by
    have hre_ev : ∀ᶠ ω in 𝓝 (0 : ℝ), 0 < (f ω).re :=
      (Complex.continuous_re.comp hf_cont).continuousAt.eventually (Ioi_mem_nhds hre0)
    filter_upwards [hre_ev] with ω hω
    unfold sommerfeldRoot
    have hnot : ¬(((f ω).im = 0) ∧ (f ω).re < 0) := fun h => not_lt_of_gt hω h.2
    exact if_neg hnot
  exact hcomp.congr hev.symm

private lemma continuousAt_ghat_zero (ε μ : ℂ) (ξ η : ℝ) (hρ : 0 < ξ ^ 2 + η ^ 2) :
    ContinuousAt (fun ω : ℝ => ghat (wavenumber ω ε μ) ξ η 0) 0 := by
  have hβ := continuousAt_sommerfeldRoot_zero ε μ ξ η hρ
  have hβ0 : sommerfeldRoot (wavenumber 0 ε μ) ξ η ≠ 0 := by
    simp only [wavenumber, Complex.ofReal_zero, zero_mul, sommerfeldRoot_zero]
    exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hρ).ne'
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hden0 : 8 * (Real.pi : ℂ) ^ 2 * sommerfeldRoot (wavenumber 0 ε μ) ξ η ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hπ)) hβ0
  have hfn : (fun ω : ℝ => ghat (wavenumber ω ε μ) ξ η 0) =
      fun ω : ℝ => 1 / (8 * (Real.pi : ℂ) ^ 2 * sommerfeldRoot (wavenumber ω ε μ) ξ η) := by
    ext ω; simp [ghat]
  rw [hfn]
  exact continuousAt_const.div (continuousAt_const.mul hβ) hden0

private lemma continuousAt_matrix_of_entries {m n : Type*} [Fintype m] [Fintype n]
    {f : ℝ → Matrix m n ℂ} {x : ℝ}
    (h : ∀ i j, ContinuousAt (fun ω => f ω i j) x) :
    ContinuousAt f x :=
  tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => h i j

private lemma continuous_matrix_entry {m n : Type*} (i : m) (j : n) :
    Continuous (fun M : Matrix m n ℂ => M i j) :=
  (continuous_apply j).comp (continuous_apply i)

private lemma continuous_matrix_det_local {n : Type*} [Fintype n] [DecidableEq n] :
    Continuous (Matrix.det : Matrix n n ℂ → ℂ) := by
  have hfun : (Matrix.det : Matrix n n ℂ → ℂ) =
      fun M => ∑ σ : Equiv.Perm n, (Equiv.Perm.sign σ : ℤ) • ∏ i : n, M (σ i) i := by
    ext M; exact Matrix.det_apply M
  rw [hfun]
  exact continuous_finsetSum _ fun σ _ =>
    (continuous_const_smul (Equiv.Perm.sign σ : ℤ)).comp
      (continuous_finset_prod _ fun i _ => continuous_matrix_entry (σ i) i)

theorem solution (ε0 μ0 ε1 μ1 : ℝ) (hε0 : 0 < ε0)
    (hμ0 : 0 < μ0) (hε1 : 0 < ε1) (hμ1 : 0 < μ1) (ξ η : ℝ) (hξη : (ξ, η) ≠ (0, 0)) :
    ∃ A₁₁ A₁₂ A₂₁ A₂₂ : ℝ → Matrix (Fin 2) (Fin 2) ℂ,
      (∀ ω : ℝ, 0 < ω → twoLayerSystem ω ε0 μ0 ε1 μ1 ξ η =
        Matrix.fromBlocks (A₁₁ ω) ((ω : ℂ) • A₁₂ ω) ((ω : ℂ) • A₂₁ ω) (A₂₂ ω)) ∧
      ContinuousWithinAt A₁₁ (Set.Ici 0) 0 ∧ ContinuousWithinAt A₁₂ (Set.Ici 0) 0 ∧
      ContinuousWithinAt A₂₁ (Set.Ici 0) 0 ∧ ContinuousWithinAt A₂₂ (Set.Ici 0) 0 ∧
      IsUnit (A₁₁ 0).det ∧ IsUnit (A₂₂ 0).det ∧
      (∀ᶠ ω in 𝓝[>] (0 : ℝ), IsUnit (twoLayerSystem ω ε0 μ0 ε1 μ1 ξ η).det) ∧
      ∀ b : Fin 2 ⊕ Fin 2 → ℂ,
        Tendsto (fun ω : ℝ => Matrix.mulVec (twoLayerSystem ω ε0 μ0 ε1 μ1 ξ η)⁻¹ b) (𝓝[>] 0)
          (𝓝 (Matrix.mulVec (Matrix.fromBlocks (A₁₁ 0)⁻¹ 0 0 (A₂₂ 0)⁻¹) b)) := by
  have hρ2_real : (0 : ℝ) < ξ ^ 2 + η ^ 2 := by
    by_contra h
    push Not at h
    exact hξη (Prod.ext (by nlinarith [sq_nonneg ξ, sq_nonneg η]) (by nlinarith [sq_nonneg ξ, sq_nonneg η]))
  have hρ_pos : 0 < Real.sqrt (ξ ^ 2 + η ^ 2) := Real.sqrt_pos.mpr hρ2_real
  set k0 : ℝ → ℂ := fun ω => wavenumber ω ε0 μ0
  set k1 : ℝ → ℂ := fun ω => wavenumber ω ε1 μ1
  set β0 : ℝ → ℂ := fun ω => sommerfeldRoot (k0 ω) ξ η
  set β1 : ℝ → ℂ := fun ω => sommerfeldRoot (k1 ω) ξ η
  set g0 : ℂ := ghat 0 ξ η 0
  set gk0 : ℝ → ℂ := fun ω => ghat (k0 ω) ξ η 0
  set gk1 : ℝ → ℂ := fun ω => ghat (k1 ω) ξ η 0
  let B₁₁ : ℝ → Matrix (Fin 2) (Fin 2) ℂ := fun ω =>
    ![![(Real.sqrt μ0 : ℂ) * g0 * gk0 ω * ((ξ : ℂ) ^ 2 + (η : ℂ) ^ 2 - (k0 ω) ^ 2),
        -((Real.sqrt μ1 : ℂ) * g0 * gk1 ω * ((ξ : ℂ) ^ 2 + (η : ℂ) ^ 2 - (k1 ω) ^ 2))],
      ![(ε0 : ℂ) * (Real.sqrt μ0 : ℂ) * gk0 ω * β0 ω,
        (ε1 : ℂ) * (Real.sqrt μ1 : ℂ) * gk1 ω * β1 ω]]
  let B₁₂ : ℝ → Matrix (Fin 2) (Fin 2) ℂ := fun ω =>
    ![![-((Real.sqrt μ1 : ℂ) * g0 * gk1 ω * (Complex.I * (μ0 : ℂ) * (Real.sqrt (ε0 / μ1) : ℂ) * β1 ω)),
        (Real.sqrt μ0 : ℂ) * g0 * gk0 ω * (Complex.I * (μ1 : ℂ) * (Real.sqrt (ε1 / μ0) : ℂ) * β0 ω)],
      ![(ε1 : ℂ) * (Real.sqrt μ1 : ℂ) * gk1 ω * (Complex.I * (μ0 : ℂ) * (Real.sqrt (ε0 / μ1) : ℂ)),
        (ε0 : ℂ) * (Real.sqrt μ0 : ℂ) * gk0 ω * (Complex.I * (μ1 : ℂ) * (Real.sqrt (ε1 / μ0) : ℂ))]]
  let B₂₁ : ℝ → Matrix (Fin 2) (Fin 2) ℂ := fun ω =>
    ![![(Real.sqrt ε1 : ℂ) * g0 * gk1 ω * (Complex.I * (ε0 : ℂ) * (Real.sqrt (μ0 / ε1) : ℂ) * β1 ω),
        -((Real.sqrt ε0 : ℂ) * g0 * gk0 ω * (Complex.I * (ε1 : ℂ) * (Real.sqrt (μ1 / ε0) : ℂ) * β0 ω))],
      ![-((μ1 : ℂ) * (Real.sqrt ε1 : ℂ) * gk1 ω * (Complex.I * (ε0 : ℂ) * (Real.sqrt (μ0 / ε1) : ℂ))),
        -((μ0 : ℂ) * (Real.sqrt ε0 : ℂ) * gk0 ω * (Complex.I * (ε1 : ℂ) * (Real.sqrt (μ1 / ε0) : ℂ)))]]
  let B₂₂ : ℝ → Matrix (Fin 2) (Fin 2) ℂ := fun ω =>
    ![![(Real.sqrt ε0 : ℂ) * g0 * gk0 ω * ((ξ : ℂ) ^ 2 + (η : ℂ) ^ 2 - (k0 ω) ^ 2),
        -((Real.sqrt ε1 : ℂ) * g0 * gk1 ω * ((ξ : ℂ) ^ 2 + (η : ℂ) ^ 2 - (k1 ω) ^ 2))],
      ![(μ0 : ℂ) * (Real.sqrt ε0 : ℂ) * gk0 ω * β0 ω,
        (μ1 : ℂ) * (Real.sqrt ε1 : ℂ) * gk1 ω * β1 ω]]
  let A₁₁ : ℝ → Matrix (Fin 2) (Fin 2) ℂ := fun ω =>
    if 0 < ω ∧ (β0 ω = 0 ∨ β1 ω = 0) then (twoLayerSystem ω ε0 μ0 ε1 μ1 ξ η).toBlocks₁₁ else B₁₁ ω
  let A₁₂ : ℝ → Matrix (Fin 2) (Fin 2) ℂ := fun ω =>
    if 0 < ω ∧ (β0 ω = 0 ∨ β1 ω = 0) then (ω : ℂ)⁻¹ • (twoLayerSystem ω ε0 μ0 ε1 μ1 ξ η).toBlocks₁₂ else B₁₂ ω
  let A₂₁ : ℝ → Matrix (Fin 2) (Fin 2) ℂ := fun ω =>
    if 0 < ω ∧ (β0 ω = 0 ∨ β1 ω = 0) then (ω : ℂ)⁻¹ • (twoLayerSystem ω ε0 μ0 ε1 μ1 ξ η).toBlocks₂₁ else B₂₁ ω
  let A₂₂ : ℝ → Matrix (Fin 2) (Fin 2) ℂ := fun ω =>
    if 0 < ω ∧ (β0 ω = 0 ∨ β1 ω = 0) then (twoLayerSystem ω ε0 μ0 ε1 μ1 ξ η).toBlocks₂₂ else B₂₂ ω
  have hmatch : ∀ ω : ℝ, 0 < ω → β0 ω ≠ 0 → β1 ω ≠ 0 →
      twoLayerSystem ω ε0 μ0 ε1 μ1 ξ η =
        Matrix.fromBlocks (B₁₁ ω) ((ω : ℂ) • B₁₂ ω) ((ω : ℂ) • B₂₁ ω) (B₂₂ ω) := by
    intro ω hω hβ0 hβ1
    ext i j
    have hM11 : ∀ r0 r1 q0 q1 : ℂ,
        twoLayerJumps ω ε0 μ0 ε1 μ1 ξ η (Sum.elim ![r0, r1] ![q0, q1]) (pt 0 0 0) =
          Sum.elim
            ![(Real.sqrt μ0 : ℂ) * g0 * gk0 ω *
                (((ξ : ℂ) ^ 2 + (η : ℂ) ^ 2 - (k0 ω) ^ 2) * r0 +
                  Complex.I * ω * μ1 * (Real.sqrt (ε1 / μ0) : ℂ) * β0 ω * q1) -
              (Real.sqrt μ1 : ℂ) * g0 * gk1 ω *
                (((ξ : ℂ) ^ 2 + (η : ℂ) ^ 2 - (k1 ω) ^ 2) * r1 +
                  Complex.I * ω * μ0 * (Real.sqrt (ε0 / μ1) : ℂ) * β1 ω * q0),
              (ε0 : ℂ) * (Real.sqrt μ0 : ℂ) * gk0 ω *
                (β0 ω * r0 + Complex.I * ω * μ1 * (Real.sqrt (ε1 / μ0) : ℂ) * q1) +
              (ε1 : ℂ) * (Real.sqrt μ1 : ℂ) * gk1 ω *
                (β1 ω * r1 + Complex.I * ω * μ0 * (Real.sqrt (ε0 / μ1) : ℂ) * q0)]
            ![(Real.sqrt ε0 : ℂ) * g0 * gk0 ω *
                (((ξ : ℂ) ^ 2 + (η : ℂ) ^ 2 - (k0 ω) ^ 2) * q0 -
                  Complex.I * ω * ε1 * (Real.sqrt (μ1 / ε0) : ℂ) * β0 ω * r1) -
              (Real.sqrt ε1 : ℂ) * g0 * gk1 ω *
                (((ξ : ℂ) ^ 2 + (η : ℂ) ^ 2 - (k1 ω) ^ 2) * q1 -
                  Complex.I * ω * ε0 * (Real.sqrt (μ0 / ε1) : ℂ) * β1 ω * r0),
              (μ0 : ℂ) * (Real.sqrt ε0 : ℂ) * gk0 ω *
                (β0 ω * q0 - Complex.I * ω * ε1 * (Real.sqrt (μ1 / ε0) : ℂ) * r1) +
              (μ1 : ℂ) * (Real.sqrt ε1 : ℂ) * gk1 ω *
                (β1 ω * q1 - Complex.I * ω * ε0 * (Real.sqrt (μ0 / ε1) : ℂ) * r0)] := by
      intro r0 r1 q0 q1
      have h := two_layer_boundary_operators ω ε0 μ0 ε1 μ1 hω hε0 hμ0 hε1 hμ1
        (k0 ω) (k1 ω) (β0 ω) (β1 ω) rfl rfl ξ η hξη rfl rfl hβ0 hβ1 r0 r1 q0 q1 0 0
      have hpw : planeWave ξ η 0 0 = 1 := by simp [planeWave]
      rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
      simp only [hpw, mul_one] at h1 h2 h3 h4 h5 h6 h7 h8
      ext idx
      rcases idx with a | a <;> fin_cases a
      · simp [twoLayerJumps, h1, h2, g0, gk0, gk1]
      · simp [twoLayerJumps, h5, h6, gk0, gk1]
      · simp [twoLayerJumps, h3, h4, g0, gk0, gk1]
      · simp [twoLayerJumps, h7, h8, gk0, gk1]
    have hs : ∀ j : Fin 2 ⊕ Fin 2, Pi.single j (1 : ℂ) =
        Sum.elim ![(Pi.single (M := fun _ => ℂ) j (1 : ℂ) (.inl 0)), (Pi.single (M := fun _ => ℂ) j (1 : ℂ) (.inl 1))]
                 ![(Pi.single (M := fun _ => ℂ) j (1 : ℂ) (.inr 0)), (Pi.single (M := fun _ => ℂ) j (1 : ℂ) (.inr 1))] := by
      intro j; ext x; rcases x with a | a <;> fin_cases a <;> simp
    rw [twoLayerSystem, hs j, hM11]
    rcases i with a | a <;> rcases j with b | b <;> fin_cases a <;> fin_cases b <;>
      simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
        Matrix.fromBlocks_apply₂₂, Matrix.smul_apply, smul_eq_mul] <;>
      simp [B₁₁, B₁₂, B₂₁, B₂₂] <;> ring
  have hsys : ∀ ω : ℝ, 0 < ω → twoLayerSystem ω ε0 μ0 ε1 μ1 ξ η =
      Matrix.fromBlocks (A₁₁ ω) ((ω : ℂ) • A₁₂ ω) ((ω : ℂ) • A₂₁ ω) (A₂₂ ω) := by
    intro ω hω
    by_cases hdeg : β0 ω = 0 ∨ β1 ω = 0
    · have hc : 0 < ω ∧ (β0 ω = 0 ∨ β1 ω = 0) := ⟨hω, hdeg⟩
      have hωc : (ω : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hω.ne'
      simp only [A₁₁, A₁₂, A₂₁, A₂₂, if_pos hc, smul_smul, mul_inv_cancel₀ hωc, one_smul,
        Matrix.fromBlocks_toBlocks]
    · push Not at hdeg
      have hc : ¬(0 < ω ∧ (β0 ω = 0 ∨ β1 ω = 0)) := fun h => by
        rcases h.2 with h0 | h1
        · exact hdeg.1 h0
        · exact hdeg.2 h1
      simp only [A₁₁, A₁₂, A₂₁, A₂₂, if_neg hc]
      exact hmatch ω hω hdeg.1 hdeg.2
  have hk0_cont : ContinuousAt k0 0 := by unfold k0 wavenumber; fun_prop
  have hk1_cont : ContinuousAt k1 0 := by unfold k1 wavenumber; fun_prop
  have hβ0_cont : ContinuousAt β0 0 := continuousAt_sommerfeldRoot_zero ε0 μ0 ξ η hρ2_real
  have hβ1_cont : ContinuousAt β1 0 := continuousAt_sommerfeldRoot_zero ε1 μ1 ξ η hρ2_real
  have hgk0_cont : ContinuousAt gk0 0 := continuousAt_ghat_zero ε0 μ0 ξ η hρ2_real
  have hgk1_cont : ContinuousAt gk1 0 := continuousAt_ghat_zero ε1 μ1 ξ η hρ2_real
  have hβ0_0 : β0 0 = (Real.sqrt (ξ ^ 2 + η ^ 2) : ℂ) := by
    simp [β0, k0, wavenumber, sommerfeldRoot_zero]
  have hβ1_0 : β1 0 = (Real.sqrt (ξ ^ 2 + η ^ 2) : ℂ) := by
    simp [β1, k1, wavenumber, sommerfeldRoot_zero]
  have hρ_ne : (Real.sqrt (ξ ^ 2 + η ^ 2) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hρ_pos.ne'
  have hev_nz : ∀ᶠ ω in 𝓝 (0 : ℝ), β0 ω ≠ 0 ∧ β1 ω ≠ 0 :=
    (hβ0_cont.eventually_ne (by rw [hβ0_0]; exact hρ_ne)).and
      (hβ1_cont.eventually_ne (by rw [hβ1_0]; exact hρ_ne))
  have hA11_eq : A₁₁ =ᶠ[𝓝 0] B₁₁ := hev_nz.mono fun ω ⟨h0, h1⟩ => by simp [A₁₁, h0, h1]
  have hA12_eq : A₁₂ =ᶠ[𝓝 0] B₁₂ := hev_nz.mono fun ω ⟨h0, h1⟩ => by simp [A₁₂, h0, h1]
  have hA21_eq : A₂₁ =ᶠ[𝓝 0] B₂₁ := hev_nz.mono fun ω ⟨h0, h1⟩ => by simp [A₂₁, h0, h1]
  have hA22_eq : A₂₂ =ᶠ[𝓝 0] B₂₂ := hev_nz.mono fun ω ⟨h0, h1⟩ => by simp [A₂₂, h0, h1]
  have hB11_cont : ContinuousAt B₁₁ 0 := by
    apply continuousAt_matrix_of_entries; intro i j; fin_cases i <;> fin_cases j <;>
      dsimp [B₁₁] <;> fun_prop (disch := assumption)
  have hB12_cont : ContinuousAt B₁₂ 0 := by
    apply continuousAt_matrix_of_entries; intro i j; fin_cases i <;> fin_cases j <;>
      dsimp [B₁₂] <;> fun_prop (disch := assumption)
  have hB21_cont : ContinuousAt B₂₁ 0 := by
    apply continuousAt_matrix_of_entries; intro i j; fin_cases i <;> fin_cases j <;>
      dsimp [B₂₁] <;> fun_prop (disch := assumption)
  have hB22_cont : ContinuousAt B₂₂ 0 := by
    apply continuousAt_matrix_of_entries; intro i j; fin_cases i <;> fin_cases j <;>
      dsimp [B₂₂] <;> fun_prop (disch := assumption)
  have hA11_cont : ContinuousAt A₁₁ 0 := hB11_cont.congr hA11_eq.symm
  have hA12_cont : ContinuousAt A₁₂ 0 := hB12_cont.congr hA12_eq.symm
  have hA21_cont : ContinuousAt A₂₁ 0 := hB21_cont.congr hA21_eq.symm
  have hA22_cont : ContinuousAt A₂₂ 0 := hB22_cont.congr hA22_eq.symm
  have hA11_0 : A₁₁ 0 = B₁₁ 0 := by simp [A₁₁]
  have hA22_0 : A₂₂ 0 = B₂₂ 0 := by simp [A₂₂]
  have hg0_ne : g0 ≠ 0 := by
    have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    simp only [g0, ghat, abs_zero, Complex.ofReal_zero, mul_zero, Complex.exp_zero, sommerfeldRoot_zero]
    exact one_div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hπ)) hρ_ne)
  have hρ2_ne : (ξ : ℂ) ^ 2 + (η : ℂ) ^ 2 ≠ 0 := by
    have : ((ξ ^ 2 + η ^ 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hρ2_real.ne'
    simpa using this
  have hdet11 : IsUnit (A₁₁ 0).det := by
    rw [hA11_0, Matrix.det_fin_two]
    have hk00 : k0 0 = 0 := by simp [k0, wavenumber]
    have hk10 : k1 0 = 0 := by simp [k1, wavenumber]
    have hgk00 : gk0 0 = g0 := by simp [gk0, hk00, g0]
    have hgk10 : gk1 0 = g0 := by simp [gk1, hk10, g0]
    simp only [B₁₁, Matrix.cons_val_zero, Matrix.cons_val_one,
      hk00, hk10, hgk00, hgk10, hβ0_0, hβ1_0, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, sub_zero]
    have hfact :
        (Real.sqrt μ0 : ℂ) * g0 * g0 * ((ξ : ℂ) ^ 2 + (η : ℂ) ^ 2) *
            ((ε1 : ℂ) * (Real.sqrt μ1 : ℂ) * g0 * (Real.sqrt (ξ ^ 2 + η ^ 2) : ℂ)) -
          -((Real.sqrt μ1 : ℂ) * g0 * g0 * ((ξ : ℂ) ^ 2 + (η : ℂ) ^ 2)) *
            ((ε0 : ℂ) * (Real.sqrt μ0 : ℂ) * g0 * (Real.sqrt (ξ ^ 2 + η ^ 2) : ℂ)) =
        (Real.sqrt μ0 : ℂ) * (Real.sqrt μ1 : ℂ) * g0 ^ 3 * ((ξ : ℂ) ^ 2 + (η : ℂ) ^ 2) *
          (Real.sqrt (ξ ^ 2 + η ^ 2) : ℂ) * ((ε0 : ℂ) + (ε1 : ℂ)) := by ring
    rw [hfact, isUnit_iff_ne_zero]
    have hμ0_ne : (Real.sqrt μ0 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hμ0).ne'
    have hμ1_ne : (Real.sqrt μ1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hμ1).ne'
    have hεsum : (ε0 : ℂ) + (ε1 : ℂ) ≠ 0 := by
      have : ((ε0 + ε1 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (add_pos hε0 hε1).ne'
      simpa using this
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hμ0_ne hμ1_ne)
      (pow_ne_zero 3 hg0_ne)) hρ2_ne) hρ_ne) hεsum
  have hdet22 : IsUnit (A₂₂ 0).det := by
    rw [hA22_0, Matrix.det_fin_two]
    have hk00 : k0 0 = 0 := by simp [k0, wavenumber]
    have hk10 : k1 0 = 0 := by simp [k1, wavenumber]
    have hgk00 : gk0 0 = g0 := by simp [gk0, hk00, g0]
    have hgk10 : gk1 0 = g0 := by simp [gk1, hk10, g0]
    simp only [B₂₂, Matrix.cons_val_zero, Matrix.cons_val_one,
      hk00, hk10, hgk00, hgk10, hβ0_0, hβ1_0, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, sub_zero]
    have hfact :
        (Real.sqrt ε0 : ℂ) * g0 * g0 * ((ξ : ℂ) ^ 2 + (η : ℂ) ^ 2) *
            ((μ1 : ℂ) * (Real.sqrt ε1 : ℂ) * g0 * (Real.sqrt (ξ ^ 2 + η ^ 2) : ℂ)) -
          -((Real.sqrt ε1 : ℂ) * g0 * g0 * ((ξ : ℂ) ^ 2 + (η : ℂ) ^ 2)) *
            ((μ0 : ℂ) * (Real.sqrt ε0 : ℂ) * g0 * (Real.sqrt (ξ ^ 2 + η ^ 2) : ℂ)) =
        (Real.sqrt ε0 : ℂ) * (Real.sqrt ε1 : ℂ) * g0 ^ 3 * ((ξ : ℂ) ^ 2 + (η : ℂ) ^ 2) *
          (Real.sqrt (ξ ^ 2 + η ^ 2) : ℂ) * ((μ0 : ℂ) + (μ1 : ℂ)) := by ring
    rw [hfact, isUnit_iff_ne_zero]
    have hε0_ne : (Real.sqrt ε0 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hε0).ne'
    have hε1_ne : (Real.sqrt ε1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hε1).ne'
    have hμsum : (μ0 : ℂ) + (μ1 : ℂ) ≠ 0 := by
      have : ((μ0 + μ1 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (add_pos hμ0 hμ1).ne'
      simpa using this
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hε0_ne hε1_ne)
      (pow_ne_zero 3 hg0_ne)) hρ2_ne) hρ_ne) hμsum
  let M0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ := Matrix.fromBlocks (A₁₁ 0) 0 0 (A₂₂ 0)
  have hM_tendsto : Tendsto (fun ω : ℝ => twoLayerSystem ω ε0 μ0 ε1 μ1 ξ η) (𝓝[>] 0) (𝓝 M0) := by
    let F : ℝ → Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ := fun ω =>
      Matrix.fromBlocks (A₁₁ ω) ((ω : ℂ) • A₁₂ ω) ((ω : ℂ) • A₂₁ ω) (A₂₂ ω)
    have hF_eq : (fun ω : ℝ => twoLayerSystem ω ε0 μ0 ε1 μ1 ξ η) =ᶠ[𝓝[>] 0] F := by
      filter_upwards [self_mem_nhdsWithin] with ω hω
      exact hsys ω hω
    have hF_cont : ContinuousAt F 0 := by
      apply continuousAt_matrix_of_entries
      intro i j
      have hω_cont : ContinuousAt (fun ω : ℝ => (ω : ℂ)) 0 := Complex.continuous_ofReal.continuousAt
      rcases i with a | a <;> rcases j with b | b <;> dsimp [F, Matrix.fromBlocks]
      · exact (continuous_matrix_entry a b).continuousAt.comp hA11_cont
      · exact hω_cont.mul ((continuous_matrix_entry a b).continuousAt.comp hA12_cont)
      · exact hω_cont.mul ((continuous_matrix_entry a b).continuousAt.comp hA21_cont)
      · exact (continuous_matrix_entry a b).continuousAt.comp hA22_cont
    have hF0 : F 0 = M0 := by
      ext i j; rcases i with a | a <;> rcases j with b | b <;> simp [F, M0, Matrix.fromBlocks]
    rw [← hF0]
    exact (hF_cont.tendsto.mono_left nhdsWithin_le_nhds).congr' hF_eq.symm
  have hM0_det : IsUnit M0.det := by
    rw [Matrix.det_fromBlocks_zero₂₁]
    exact hdet11.mul hdet22
  have hdet_cont : Continuous (Matrix.det : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ → ℂ) :=
    continuous_matrix_det_local
  have hdet_tendsto : Tendsto (fun ω : ℝ => (twoLayerSystem ω ε0 μ0 ε1 μ1 ξ η).det) (𝓝[>] 0) (𝓝 M0.det) :=
    hdet_cont.continuousAt.tendsto.comp hM_tendsto
  have hev_unit : ∀ᶠ ω in 𝓝[>] (0 : ℝ), IsUnit (twoLayerSystem ω ε0 μ0 ε1 μ1 ξ η).det := by
    have hne : ∀ᶠ ω in 𝓝[>] (0 : ℝ), (twoLayerSystem ω ε0 μ0 ε1 μ1 ξ η).det ≠ 0 :=
      hdet_tendsto.eventually_ne (isUnit_iff_ne_zero.mp hM0_det)
    exact hne.mono fun _ h => isUnit_iff_ne_zero.mpr h
  have hM0_inv : M0⁻¹ = Matrix.fromBlocks (A₁₁ 0)⁻¹ 0 0 (A₂₂ 0)⁻¹ := by
    have hmul : M0 * Matrix.fromBlocks (A₁₁ 0)⁻¹ 0 0 (A₂₂ 0)⁻¹ = 1 := by
      simp only [M0, Matrix.fromBlocks_multiply, mul_zero, zero_mul, add_zero, zero_add,
        Matrix.mul_nonsing_inv _ hdet11, Matrix.mul_nonsing_inv _ hdet22, Matrix.fromBlocks_one]
    exact Matrix.inv_eq_right_inv hmul
  have hinv_tendsto : Tendsto (fun ω : ℝ => (twoLayerSystem ω ε0 μ0 ε1 μ1 ξ η)⁻¹) (𝓝[>] 0) (𝓝 M0⁻¹) := by
    have hadj_cont : Continuous (Matrix.adjugate : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ → _) := by
      refine continuous_pi fun i => continuous_pi fun j => ?_
      simp only [Matrix.adjugate_apply]
      exact continuous_matrix_det_local.comp (continuous_pi fun r => continuous_pi fun c => by
        by_cases h : r = j
        · simp only [Matrix.updateRow_apply, h, ↓reduceIte]; exact continuous_const
        · simp only [Matrix.updateRow_apply, h, ↓reduceIte]; exact continuous_matrix_entry r c)
    have hinv_eq : ∀ M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ,
        M⁻¹ = M.det⁻¹ • M.adjugate := fun M => by
      rw [Matrix.inv_def, Ring.inverse_eq_inv']
    have hdet_inv : Tendsto (fun ω : ℝ => (twoLayerSystem ω ε0 μ0 ε1 μ1 ξ η).det⁻¹)
        (𝓝[>] 0) (𝓝 M0.det⁻¹) :=
      hdet_tendsto.inv₀ (isUnit_iff_ne_zero.mp hM0_det)
    have hadj_lim : Tendsto (fun ω : ℝ => (twoLayerSystem ω ε0 μ0 ε1 μ1 ξ η).adjugate)
        (𝓝[>] 0) (𝓝 M0.adjugate) :=
      hadj_cont.continuousAt.tendsto.comp hM_tendsto
    simpa [hinv_eq] using hdet_inv.smul hadj_lim
  refine ⟨A₁₁, A₁₂, A₂₁, A₂₂, hsys,
    hA11_cont.continuousWithinAt, hA12_cont.continuousWithinAt,
    hA21_cont.continuousWithinAt, hA22_cont.continuousWithinAt,
    hdet11, hdet22, hev_unit, ?_⟩
  intro b
  rw [← hM0_inv]
  have hmv : Continuous (fun M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ => Matrix.mulVec M b) :=
    continuous_pi fun i => by
      simp only [Matrix.mulVec, dotProduct]
      exact continuous_finset_sum _ fun j _ =>
        (continuous_matrix_entry i j).mul continuous_const
  exact hmv.continuousAt.tendsto.comp hinv_tendsto
