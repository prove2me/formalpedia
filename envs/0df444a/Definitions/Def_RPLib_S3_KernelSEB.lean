-- Prove2me | Definitions.Def_RPLib_S3_KernelSEB
-- name    : RPLib_S3_KernelSEB
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T12:53:26.875401+00:00
-- url     : https://prove2.me/theorems/68daa3af-0c16-4d04-a3e3-7120cb572a66
-- title:
--   The Eichler-Selberg trace formula in weight two: `Ω(·, w) ∈ S_2(Γ₁(M))`
-- statement:
--   `Ω(·, w) ∈ S_2(Γ₁(M))`.
--
--   * `OmegaH M n u w : ℍ → ℂ`, `Omega_slash_Gamma1` (the `s → 0+` limit of `omegaSH_slash_Gamma1`).
--   * `differentiableOn_Omega`, `mdifferentiable_OmegaH`.
--   * `tendsto_K0_atImInfty`, `isZeroAtImInfty_OmegaH_slash` (from `Omega_slash` and `norm_K0_le`).
--   * `OmegaCF : CuspForm Γ₁(M) 2`, `coe_OmegaCF`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224; F. Diamond and J. Shurman, A First Course in Modular Forms, GTM 228, Springer 2005, Chapter 5

import Mathlib
import Definitions.Def_RPLib_S3_KernelSEA

/-!
# S3-ES-Wt2, part KS_E (B): `Ω(·, w) ∈ S_2(Γ₁(M))`

* `OmegaH M n u w : ℍ → ℂ`, `Omega_slash_Gamma1` (the `s → 0+` limit of `omegaSH_slash_Gamma1`).
* `differentiableOn_Omega`, `mdifferentiable_OmegaH`.
* `tendsto_K0_atImInfty`, `isZeroAtImInfty_OmegaH_slash` (from `Omega_slash` and `norm_K0_le`).
* `OmegaCF : CuspForm Γ₁(M) 2`, `coe_OmegaCF`.
-/

open Complex Filter Topology UpperHalfPlane ModularForm CongruenceSubgroup
open scoped MatrixGroups Manifold

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.KernelSD

open RamanujanPetersson.Kernel RamanujanPetersson.KernelS RamanujanPetersson.GSA

variable {M : ℕ} [NeZero M]

/-- `Ω(·, w)` as a function on `ℍ`. -/
def OmegaH (M : ℕ) [NeZero M] (n : ℕ) (u : (ZMod M)ˣ) (w : ℂ) : ℍ → ℂ := fun τ => Omega M n u τ w

/-- **`Γ₁(M)`-invariance of `Ω(·, w)` in weight 2**, the `s → 0+` limit of `omegaSH_slash_Gamma1`. -/
theorem Omega_slash_Gamma1 (hM : 3 ≤ M) {n : ℕ} (hn : 0 < n) (hnM : n.Coprime M) (u : (ZMod M)ˣ)
    {w : ℂ} (hv : 0 < w.im) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma1 M) :
    OmegaH M n u w ∣[((2 : ℕ) : ℤ)] γ = OmegaH M n u w := by
  funext τ
  rw [SL_slash_apply]
  have h1 := (tendsto_omegaS hM hn hnM u (γ • τ).im_pos hv).mul_const (denom γ τ ^ (-((2 : ℕ) : ℤ)))
  have h2 := tendsto_omegaS hM hn hnM u τ.im_pos hv
  have e : ∀ s : ℝ, omegaS M 2 n (u : ZMod M) s ((γ • τ : ℍ) : ℂ) w * denom γ τ ^ (-((2 : ℕ) : ℤ)) =
      omegaS M 2 n (u : ZMod M) s τ w := by
    intro s
    have := congrFun (omegaSH_slash_Gamma1 M 2 (n : ℤ) (u : ZMod M) s w hγ) τ
    rw [SL_slash_apply] at this
    exact this
  exact tendsto_nhds_unique (h1.congr e) h2

theorem differentiableOn_Omega {n : ℕ} (hn : 0 < n) (hnM : n.Coprime M) (u : (ZMod M)ˣ) {w : ℂ}
    (hv : 0 < w.im) : DifferentiableOn ℂ (fun z => Omega M n u z w) UHP := by
  unfold Omega
  apply DifferentiableOn.fun_sum
  intro x _
  exact (differentiableOn_K0 M (im_natPt_pos (det_hX_pos hn hnM u x) hv)).const_mul _

theorem mdifferentiable_OmegaH {n : ℕ} (hn : 0 < n) (hnM : n.Coprime M) (u : (ZMod M)ˣ) {w : ℂ}
    (hv : 0 < w.im) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (OmegaH M n u w) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  refine (differentiableOn_Omega hn hnM u hv).congr (fun z hz => ?_)
  rw [Function.comp_apply, ofComplex_apply_of_im_pos hz]
  rfl

theorem tendsto_K0_atImInfty {w : ℂ} (hv : 0 < w.im) :
    Tendsto (fun τ : ℍ => K0 M τ w) atImInfty (𝓝 0) := by
  refine squeeze_zero_norm' (a := fun τ : ℍ => CKG M 1 w.im * (τ : ℂ).im ^ (-(1 / 2) : ℝ)) ?_ ?_
  · rw [Filter.Eventually, atImInfty_mem]
    exact ⟨1, fun τ hτ => norm_K0_le one_pos hτ hv⟩
  · have h1 : Tendsto (fun τ : ℍ => (τ : ℂ).im) atImInfty atTop := tendsto_comap
    have h2 := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp h1).const_mul
      (CKG M 1 w.im)
    rw [mul_zero] at h2
    exact h2

theorem isZeroAtImInfty_OmegaH_slash (hM : 3 ≤ M) {n : ℕ} (hn : 0 < n) (hnM : n.Coprime M)
    (u : (ZMod M)ˣ) {w : ℂ} (hv : 0 < w.im) (γ : SL(2, ℤ)) :
    IsZeroAtImInfty (OmegaH M n u w ∣[((2 : ℕ) : ℤ)] γ) := by
  have e : (OmegaH M n u w ∣[((2 : ℕ) : ℤ)] γ) = fun τ : ℍ => ∑ x : HNFIdx n × ZMod M,
      (denW (hX n u x) w ^ 2)⁻¹ * ((denW (γ : Matrix (Fin 2) (Fin 2) ℤ) (natPt (hX n u x) w) ^ 2)⁻¹ *
        K0 M τ (natPt (γ : Matrix (Fin 2) (Fin 2) ℤ) (natPt (hX n u x) w))) := by
    funext τ
    rw [SL_slash_apply]
    exact Omega_slash hM hn hnM u γ τ hv
  rw [e]
  unfold IsZeroAtImInfty ZeroAtFilter
  have hx : ∀ x ∈ (Finset.univ : Finset (HNFIdx n × ZMod M)), Tendsto (fun τ : ℍ =>
      (denW (hX n u x) w ^ 2)⁻¹ * ((denW (γ : Matrix (Fin 2) (Fin 2) ℤ) (natPt (hX n u x) w) ^ 2)⁻¹ *
        K0 M τ (natPt (γ : Matrix (Fin 2) (Fin 2) ℤ) (natPt (hX n u x) w)))) atImInfty (𝓝 0) := by
    intro x _
    have := ((tendsto_K0_atImInfty (M := M)
      (im_natPt_SL_pos γ (im_natPt_pos (det_hX_pos hn hnM u x) hv))).const_mul
        ((denW (γ : Matrix (Fin 2) (Fin 2) ℤ) (natPt (hX n u x) w) ^ 2)⁻¹)).const_mul
          ((denW (hX n u x) w ^ 2)⁻¹)
    rw [mul_zero, mul_zero] at this
    exact this
  have h := tendsto_finsetSum _ hx
  rw [Finset.sum_const_zero] at h
  exact h

/-- **`Ω(·, w) ∈ S_2(Γ₁(M))`** for `Im w > 0`, `n > 0`, `(n, M) = 1`, `M ≥ 3`. -/
def OmegaCF (hM : 3 ≤ M) {n : ℕ} (hn : 0 < n) (hnM : n.Coprime M) (u : (ZMod M)ˣ) (w : ℂ)
    (hv : 0 < w.im) :
    CuspForm ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ((2 : ℕ) : ℤ) where
  toFun := OmegaH M n u w
  slash_action_eq' γ hγ := by
    obtain ⟨γ₀, hγ₀, rfl⟩ := hγ
    have := Omega_slash_Gamma1 hM hn hnM u hv hγ₀
    rw [SL_slash] at this
    exact this
  holo' := mdifferentiable_OmegaH hn hnM u hv
  zero_at_cusps' hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isZeroAt_iff_forall_SL2Z hc]
    intro γ _
    exact isZeroAtImInfty_OmegaH_slash hM hn hnM u hv γ

@[simp] lemma coe_OmegaCF (hM : 3 ≤ M) {n : ℕ} (hn : 0 < n) (hnM : n.Coprime M) (u : (ZMod M)ˣ)
    (w : ℂ) (hv : 0 < w.im) : ⇑(OmegaCF hM hn hnM u w hv) = OmegaH M n u w := rfl

end RamanujanPetersson.KernelSD


