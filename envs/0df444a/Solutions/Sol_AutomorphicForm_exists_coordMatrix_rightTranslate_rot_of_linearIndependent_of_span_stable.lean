-- Prove2me | solution 1 for AutomorphicForm.exists_coordMatrix_rightTranslate_rot_of_linearIndependent_of_span_stable
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/ddb38619-5263-50fd-b577-340a6688d423

import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_coordMatrix_rightTranslate_rot_of_linearIndependent_of_span_stable

set_option autoImplicit false

open NumberField AutomorphicForm NumberField.InfinitePlace NumberField.InfinitePlace.Completion

namespace Ws50KTC

variable {G : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exists_finsupp_dual (x : ι → G → ℂ) (hli : LinearIndependent ℂ x) (i : ι) :
    ∃ c : G →₀ ℂ, ∀ i' : ι, (∑ g ∈ c.support, c g * x i' g) = if i' = i then 1 else 0 := by
  classical
  let Ψ : (G →₀ ℂ) →ₗ[ℂ] (ι → ℂ) := Finsupp.linearCombination ℂ (fun g : G => fun i' : ι => x i' g)
  have hΨ : ∀ (c : G →₀ ℂ) (i' : ι), Ψ c i' = ∑ g ∈ c.support, c g * x i' g := by
    intro c i'
    simp only [Ψ, Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hΨ1 : ∀ g : G, Ψ (Finsupp.single g 1) = fun i' => x i' g := by
    intro g
    simp only [Ψ, Finsupp.linearCombination_single, one_smul]
  have hsurj : Function.Surjective Ψ := by
    rw [← LinearMap.range_eq_top]
    by_contra hne
    obtain ⟨f, hf0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    apply hf0
    set d : ι → ℂ := fun i' => f (fun j => if i' = j then 1 else 0) with hd
    have hg : ∀ g : G, ∑ i', x i' g * d i' = 0 := by
      intro g
      have hmem : Ψ (Finsupp.single g 1) ∈ LinearMap.ker f := hle (LinearMap.mem_range_self Ψ _)
      rw [LinearMap.mem_ker, hΨ1, LinearMap.pi_apply_eq_sum_univ f] at hmem
      simpa only [smul_eq_mul] using hmem
    have hzero : ∑ i', d i' • x i' = 0 := by
      funext g
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      rw [← hg g]
      exact Finset.sum_congr rfl fun i' _ => mul_comm _ _
    have hd0 := Fintype.linearIndependent_iff.1 hli d hzero
    apply LinearMap.ext
    intro v
    rw [LinearMap.pi_apply_eq_sum_univ f v, LinearMap.zero_apply]
    refine Finset.sum_eq_zero fun i' _ => ?_
    have := hd0 i'
    simp only [hd] at this
    rw [this, smul_zero]
  obtain ⟨c, hc⟩ := hsurj (Pi.single i 1)
  refine ⟨c, fun i' => ?_⟩
  rw [← hΨ, hc, Pi.single_apply]

theorem engine [Monoid G] (x : ι → G → ℂ) (hli : LinearIndependent ℂ x) (k : ℝ → G) (hk0 : k 0 = 1)
    (M : ι → ι → ℂ)
    (hspan : ∀ (p : ι) (s : ℝ), (fun g => x p (g * k s)) ∈ Submodule.span ℂ (Set.range x))
    (hder : ∀ (p : ι) (g : G), HasDerivAt (fun s : ℝ => x p (g * k s)) (∑ p', M p' p * x p' g) 0) :
    ∃ E : ℝ → Matrix ι ι ℂ, E 0 = 1 ∧ (∀ i j, HasDerivAt (fun s => E s i j) (M i j) 0) ∧
      ∀ (p : ι) (s : ℝ) (g : G), x p (g * k s) = ∑ p', E s p' p * x p' g := by
  classical
  set W : Submodule ℂ (G → ℂ) := Submodule.span ℂ (Set.range x) with hW
  let b : Module.Basis ι ℂ W := Module.Basis.span hli
  have hb : ∀ i, ((b i : W) : G → ℂ) = x i := fun i => by
    show ((Module.Basis.span hli i : W) : G → ℂ) = x i
    rw [Module.Basis.span_apply]

  have hexpand : ∀ (w : W) (g : G), (w : G → ℂ) g = ∑ i, b.repr w i * x i g := by
    intro w g
    have h := congrArg (fun v : W => (v : G → ℂ) g) (b.sum_repr w)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hb] at h
    exact h.symm

  have hmemc : ∀ c : ι → ℂ, (∑ i, c i • x i) ∈ W :=
    fun c => Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hcoord : ∀ (c : ι → ℂ) (i : ι), b.repr ⟨∑ i, c i • x i, hmemc c⟩ i = c i := by
    intro c i
    have h1 : (⟨∑ i, c i • x i, hmemc c⟩ : W) = ∑ i, c i • b i := by
      apply Subtype.ext
      simp only [Submodule.coe_sum, Submodule.coe_smul, hb]
    rw [h1, ← Module.Basis.equivFun_symm_apply, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]

  let E : ℝ → Matrix ι ι ℂ := fun s p' p => b.repr ⟨fun g => x p (g * k s), hspan p s⟩ p'
  have hE : ∀ (p : ι) (s : ℝ) (g : G), x p (g * k s) = ∑ p', E s p' p * x p' g :=
    fun p s g => hexpand ⟨_, hspan p s⟩ g
  have hE0 : E 0 = 1 := by
    ext i j
    have hxj : (fun g => x j (g * k 0)) = ∑ q, (if q = j then (1 : ℂ) else 0) • x q := by
      simp only [hk0, mul_one, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have h1 : (⟨fun g => x j (g * k 0), hspan j 0⟩ : W) = ⟨_, hmemc fun q => if q = j then (1 : ℂ) else 0⟩ :=
      Subtype.ext hxj
    show b.repr ⟨fun g => x j (g * k 0), hspan j 0⟩ i = (1 : Matrix ι ι ℂ) i j
    rw [h1, hcoord, Matrix.one_apply]
  have hE' : ∀ i j, HasDerivAt (fun s => E s i j) (M i j) 0 := by
    intro i j
    obtain ⟨c, hc⟩ := exists_finsupp_dual x hli i

    have hrep : ∀ w : W, b.repr w i = ∑ g ∈ c.support, c g * (w : G → ℂ) g := by
      intro w
      have h1 : (∑ g ∈ c.support, c g * (w : G → ℂ) g) = ∑ i', b.repr w i' * ∑ g ∈ c.support, c g * x i' g := by
        simp only [hexpand w, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun g _ => by ring
      rw [h1]
      simp only [hc, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have hfun : (fun s => E s i j) = ∑ g ∈ c.support, fun s => c g * x j (g * k s) := by
      funext s
      rw [Finset.sum_apply]
      exact hrep ⟨fun g => x j (g * k s), hspan j s⟩
    rw [hfun]
    have h1 : HasDerivAt (∑ g ∈ c.support, fun s => c g * x j (g * k s))
        (∑ g ∈ c.support, c g * ∑ p', M p' j * x p' g) 0 :=
      HasDerivAt.sum fun g _ => (hder j g).const_mul (c g)
    have h2 : (∑ g ∈ c.support, c g * ∑ p', M p' j * x p' g) = M i j := by
      have h3 := hrep ⟨_, hmemc fun p' => M p' j⟩
      rw [hcoord] at h3
      rw [h3]
      refine Finset.sum_congr rfl fun g _ => ?_
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact h2 ▸ h1
  exact ⟨E, hE0, hE', hE⟩

end Ws50KTC

theorem solution
    (F : Type) [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsComplex)
    (n : ℕ) (x : Fin (n + 1) → (AdelicGL2 (𝓞 F) F → ℂ)) (hli : LinearIndependent ℂ x)
    (hR : ∀ (p : Fin (n + 1)) (s : ℝ),
      (fun g => x p (g * archComplexLiftAt hw
        !![(Real.cos s : ℂ), -(Real.sin s : ℂ); (Real.sin s : ℂ), (Real.cos s : ℂ)])) ∈ Submodule.span ℂ (Set.range x))
    (hS : ∀ (p : Fin (n + 1)) (s : ℝ),
      (fun g => x p (g * archComplexLiftAt hw
        !![(Real.cos s : ℂ), (Real.sin s : ℂ) * Complex.I; (Real.sin s : ℂ) * Complex.I, (Real.cos s : ℂ)])) ∈
          Submodule.span ℂ (Set.range x))
    (hR' : ∀ (p : Fin (n + 1)) (g : AdelicGL2 (𝓞 F) F),
      HasDerivAt (fun s : ℝ => x p (g * archComplexLiftAt hw
        !![(Real.cos s : ℂ), -(Real.sin s : ℂ); (Real.sin s : ℂ), (Real.cos s : ℂ)]))
        (∑ p' : Fin (n + 1),
          (if (p' : ℕ) = p + 1 then 1 else if (p : ℕ) = p' + 1 then -((p : ℂ) * ((n : ℂ) + 1 - p)) else 0) * x p' g) 0)
    (hS' : ∀ (p : Fin (n + 1)) (g : AdelicGL2 (𝓞 F) F),
      HasDerivAt (fun s : ℝ => x p (g * archComplexLiftAt hw
        !![(Real.cos s : ℂ), (Real.sin s : ℂ) * Complex.I; (Real.sin s : ℂ) * Complex.I, (Real.cos s : ℂ)]))
        (∑ p' : Fin (n + 1),
          (if (p' : ℕ) = p + 1 then Complex.I else if (p : ℕ) = p' + 1 then Complex.I * ((p : ℂ) * ((n : ℂ) + 1 - p)) else 0) *
            x p' g) 0) :
    ∃ E₁ E₂ : ℝ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
      E₁ 0 = 1 ∧ E₂ 0 = 1 ∧
      (∀ i j : Fin (n + 1), HasDerivAt (fun s : ℝ => E₁ s i j)
        (if (i : ℕ) = j + 1 then 1 else if (j : ℕ) = i + 1 then -((j : ℂ) * ((n : ℂ) + 1 - j)) else 0) 0) ∧
      (∀ i j : Fin (n + 1), HasDerivAt (fun s : ℝ => E₂ s i j)
        (if (i : ℕ) = j + 1 then Complex.I else if (j : ℕ) = i + 1 then Complex.I * ((j : ℂ) * ((n : ℂ) + 1 - j)) else 0) 0) ∧
      (∀ (p : Fin (n + 1)) (s : ℝ) (g : AdelicGL2 (𝓞 F) F),
        x p (g * archComplexLiftAt hw !![(Real.cos s : ℂ), -(Real.sin s : ℂ); (Real.sin s : ℂ), (Real.cos s : ℂ)]) =
          ∑ p' : Fin (n + 1), E₁ s p' p * x p' g) ∧
      (∀ (p : Fin (n + 1)) (s : ℝ) (g : AdelicGL2 (𝓞 F) F),
        x p (g * archComplexLiftAt hw
          !![(Real.cos s : ℂ), (Real.sin s : ℂ) * Complex.I; (Real.sin s : ℂ) * Complex.I, (Real.cos s : ℂ)]) =
          ∑ p' : Fin (n + 1), E₂ s p' p * x p' g) := by
  classical
  have hR0 : archComplexLiftAt hw
      !![(Real.cos (0 : ℝ) : ℂ), -(Real.sin (0 : ℝ) : ℂ); (Real.sin (0 : ℝ) : ℂ), (Real.cos (0 : ℝ) : ℂ)] = 1 := by
    unfold archComplexLiftAt
    split_ifs with h
    · rw [show Matrix.GeneralLinearGroup.mkOfDetNeZero _ h = 1 from Units.ext (by
        ext i j
        fin_cases i <;> fin_cases j <;> simp)]
      exact map_one _
    · rfl
  have hS0 : archComplexLiftAt hw
      !![(Real.cos (0 : ℝ) : ℂ), (Real.sin (0 : ℝ) : ℂ) * Complex.I; (Real.sin (0 : ℝ) : ℂ) * Complex.I, (Real.cos (0 : ℝ) : ℂ)] = 1 := by
    unfold archComplexLiftAt
    split_ifs with h
    · rw [show Matrix.GeneralLinearGroup.mkOfDetNeZero _ h = 1 from Units.ext (by
        ext i j
        fin_cases i <;> fin_cases j <;> simp)]
      exact map_one _
    · rfl
  obtain ⟨E₁, h10, h1d, h1e⟩ := Ws50KTC.engine x hli
    (fun s => archComplexLiftAt hw !![(Real.cos s : ℂ), -(Real.sin s : ℂ); (Real.sin s : ℂ), (Real.cos s : ℂ)]) hR0
    (fun i j => if (i : ℕ) = j + 1 then 1 else if (j : ℕ) = i + 1 then -((j : ℂ) * ((n : ℂ) + 1 - j)) else 0) hR hR'
  obtain ⟨E₂, h20, h2d, h2e⟩ := Ws50KTC.engine x hli
    (fun s => archComplexLiftAt hw
      !![(Real.cos s : ℂ), (Real.sin s : ℂ) * Complex.I; (Real.sin s : ℂ) * Complex.I, (Real.cos s : ℂ)]) hS0
    (fun i j => if (i : ℕ) = j + 1 then Complex.I else if (j : ℕ) = i + 1 then Complex.I * ((j : ℂ) * ((n : ℂ) + 1 - j)) else 0)
    hS hS'
  exact ⟨E₁, E₂, h10, h20, h1d, h2d, h1e, h2e⟩

end S_AutomorphicForm_exists_coordMatrix_rightTranslate_rot_of_linearIndependent_of_span_stable
end P2MW
export P2MW.S_AutomorphicForm_exists_coordMatrix_rightTranslate_rot_of_linearIndependent_of_span_stable (solution)
