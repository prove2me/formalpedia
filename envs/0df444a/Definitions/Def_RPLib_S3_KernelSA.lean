-- Prove2me | Definitions.Def_RPLib_S3_KernelSA
-- name    : RPLib_S3_KernelSA
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T12:28:15.923056+00:00
-- url     : https://prove2.me/theorems/6078afa8-d442-47de-9a34-5e19fde0702b
-- title:
--   The Eichler-Selberg trace formula in weight two: the Hecke-trick kernel `ω_s` and its per-matrix Bergman step
-- statement:
--   The Hecke-trick kernel `ω_s` and its per-matrix Bergman step.
--
--   `ratQ g z w = det g · Im z · Im w / |Q(g; z, w)|^2` and
--   `ω_s(z, w) = Σ_{g ∈ Δ^{(δ')}_n(M)} Q(g; z, w)^(-k) ratQ(g; z, w)^s`.
--   For `w ∈ ℍ`, `ratQ g z (-conj w) = ratio z (adj g · w)` (the invariant point-pair ratio of `BergmanS`), so the
--   per-matrix unfolded integrand is `(a - c w)^(-k) · integrandS k s f (adj g · w)` and `BergmanS` evaluates it.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224; F. Diamond and J. Shurman, A First Course in Modular Forms, GTM 228, Springer 2005, Chapter 5

import Mathlib
import Definitions.Def_RPLib_S3_KernelB1
import Definitions.Def_RPLib_S3_BergmanS

/-!
# S3-ES-Wt2 (O2, part A): the Hecke-trick kernel `ω_s` and its per-matrix Bergman step

`ratQ g z w = det g · Im z · Im w / |Q(g; z, w)|^2` and
`ω_s(z, w) = Σ_{g ∈ Δ^{(δ')}_n(M)} Q(g; z, w)^(-k) ratQ(g; z, w)^s`.
For `w ∈ ℍ`, `ratQ g z (-conj w) = ratio z (adj g · w)` (the invariant point-pair ratio of `BergmanS`), so the
per-matrix unfolded integrand is `(a - c w)^(-k) · integrandS k s f (adj g · w)` and `BergmanS` evaluates it.
-/

open Filter Complex UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups Topology Manifold ComplexConjugate

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.KernelS

open RP.FundDomain RP.Petersson RamanujanPetersson.Diamond RamanujanPetersson.Hecke
  RamanujanPetersson.Kernel RamanujanPetersson.Bergman RamanujanPetersson.BergmanS

/-- `det g · Im z · Im w / |Q(g; z, w)|^2`. -/
def ratQ (g : Matrix (Fin 2) (Fin 2) ℤ) (z w : ℂ) : ℝ := (g.det : ℝ) * z.im * w.im / ‖Q g z w‖ ^ 2

/-- The Hecke-trick kernel `ω_s(z, w) = Σ_g Q(g; z, w)^(-k) ratQ(g; z, w)^s`. -/
def omegaS (M k : ℕ) (n : ℤ) (δ' : ZMod M) (s : ℝ) (z w : ℂ) : ℂ :=
  ∑' g : DeltaSet M n δ', (Q g.1 z w ^ k)⁻¹ * ((ratQ g.1 z w ^ s : ℝ) : ℂ)

/-- `Im(adj g · w) |a - c w|^2 = det g · Im w`. -/
lemma im_adjPt_mul {g : Matrix (Fin 2) (Fin 2) ℤ} (h : 0 < g.det) (w : ℍ) :
    (adjPt g w : ℂ).im * normSq ((g 0 0 : ℂ) - (g 1 0 : ℂ) * w) = (g.det : ℝ) * (w : ℂ).im := by
  have hD := denom_adj_ne h w
  set D : ℂ := (g 0 0 : ℂ) - (g 1 0 : ℂ) * w with hD_def
  have hA : (adjPt g w : ℂ) * D = (g 1 1 : ℂ) * w - (g 0 1 : ℂ) := by
    rw [coe_adjPt h w, div_mul_cancel₀ _ hD]
  have e1 : (adjPt g w : ℂ).im * normSq D = ((adjPt g w : ℂ) * D * conj D).im := by
    rw [mul_assoc, Complex.mul_conj, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [e1, hA, hD_def, det_eq]
  simp only [Complex.mul_im, Complex.mul_re, Complex.sub_im, Complex.sub_re, Complex.conj_re,
    Complex.conj_im, Complex.intCast_re, Complex.intCast_im]
  push_cast
  ring

/-- **The ratio is the invariant point-pair ratio**: `ratQ g z (-conj w) = ratio z (adj g · w)`. -/
lemma ratQ_negConj {g : Matrix (Fin 2) (Fin 2) ℤ} (h : 0 < g.det) (z w : ℍ) :
    ratQ g z (-conj (w : ℂ)) = ratio (z : ℂ) (adjPt g w : ℂ) := by
  have hD := denom_adj_ne h w
  set D : ℂ := (g 0 0 : ℂ) - (g 1 0 : ℂ) * w with hD_def
  have hQ : Q g z (-conj (w : ℂ)) = conj D * ((z : ℂ) - conj (adjPt g w : ℂ)) := by
    rw [Q_negConj g z w hD, coe_adjPt h w]
  have hN : 0 < normSq D := Complex.normSq_pos.mpr hD
  have hIm := im_adjPt_mul h w
  rw [ratQ, ratio, hQ, norm_mul, Complex.norm_conj, mul_pow, ← Complex.normSq_eq_norm_sq D]
  have hv : (-conj (w : ℂ)).im = (w : ℂ).im := by simp
  rw [← hD_def] at hIm
  rw [hv, mul_right_comm ((g.det : ℤ) : ℝ), ← hIm]
  have hz0 : ‖(z : ℂ) - conj (adjPt g w : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr (coe_sub_conj_ne_zero z _)
  field_simp

/-- The unfolded integrand for one matrix (Hecke-trick version). -/
def PhiAS (k : ℕ) (s : ℝ) (g : Matrix (Fin 2) (Fin 2) ℤ) (f : ℍ → ℂ) (w : ℍ) (z : ℍ) : ℂ :=
  conj ((Q g z (-conj (w : ℂ)) ^ k)⁻¹) * ((ratQ g z (-conj (w : ℂ)) ^ s : ℝ) : ℂ) * f z * ((z.im : ℂ) ^ k)

lemma PhiAS_eq (k : ℕ) (s : ℝ) {g : Matrix (Fin 2) (Fin 2) ℤ} (h : 0 < g.det) (f : ℍ → ℂ) (w : ℍ) (z : ℍ) :
    PhiAS k s g f w z = ((((g 0 0 : ℂ) - (g 1 0 : ℂ) * w) ^ k)⁻¹) * integrandS k s f (adjPt g w) z := by
  have e0 := PhiA_eq k h f w z
  rw [PhiA] at e0
  rw [PhiAS, integrandS, ratQ_negConj h z w]
  linear_combination ((ratio (z : ℂ) (adjPt g w : ℂ) ^ s : ℝ) : ℂ) * e0

/-- **The Bergman step** (Hecke-trick version, `k ≥ 2`, `k/2 + s > 1`). -/
theorem integral_termS {M k : ℕ} [NeZero M] (hk : 2 ≤ k) {s : ℝ} (hσ : 1 < (k : ℝ) / 2 + s) (f : S1 M k)
    {g : Matrix (Fin 2) (Fin 2) ℤ} (h : 0 < g.det) (w : ℍ) :
    Integrable (PhiAS k s g f w) ∧ ∫ z, PhiAS k s g f w z =
      ((((g 0 0 : ℂ) - (g 1 0 : ℂ) * w) ^ k)⁻¹) * (bergmanConstS k s * f (adjPt g w)) := by
  obtain ⟨C, hC⟩ := CuspFormClass.exists_bound f
  have hC' : ∀ z : ℍ, ‖f z‖ ≤ C / z.im ^ ((k : ℝ) / 2) := fun z => by
    have hz := hC z
    rwa [Int.cast_natCast] at hz
  have hholo : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (f : ℍ → ℂ) := CuspFormClass.holo f
  have hfun : PhiAS k s g f w = fun z => ((((g 0 0 : ℂ) - (g 1 0 : ℂ) * w) ^ k)⁻¹) *
      integrandS k s f (adjPt g w) z := by
    funext z; exact PhiAS_eq k s h f w z
  rw [hfun]
  refine ⟨(integrable_integrandS_of_bound hσ hholo.continuous (adjPt g w) hC').const_mul _, ?_⟩
  rw [integral_const_mul, bergman_reproducing_s_of_bound hk hσ hholo (adjPt g w) hC']

end RamanujanPetersson.KernelS


