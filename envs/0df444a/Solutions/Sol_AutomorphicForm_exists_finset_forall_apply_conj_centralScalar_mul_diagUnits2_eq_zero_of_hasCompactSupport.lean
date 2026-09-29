-- Prove2me | solution 1 for AutomorphicForm.exists_finset_forall_apply_conj_centralScalar_mul_diagUnits2_eq_zero_of_hasCompactSupport
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/a4a4e2f9-354e-5769-963c-a94dbc13134f

import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Mathlib.Topology.Algebra.Support
import Theorems.Thm_NumberField_AdeleRing_finite_setOf_algebraMap_mem_of_isCompact
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_finset_forall_apply_conj_centralScalar_mul_diagUnits2_eq_zero_of_hasCompactSupport

set_option autoImplicit false

open NumberField IsDedekindDomain
open LanglandsTunnell.CubicInduction (diagUnits2)

theorem solution
    (K : Type) [Field K] [NumberField K]
    (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f) :
    ∃ U : Finset Kˣ, ∀ u : Kˣ, (u : K) ≠ 1 → u ∉ U →
      ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (x : GL (Fin 2) (AdeleRing (𝓞 K) K)),
        f (x⁻¹ * (AutomorphicForm.centralScalar (𝓞 K) K z *
          diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1) * x) = 0  := by
  classical

  let φ : GL (Fin 2) (AdeleRing (𝓞 K) K) → AdeleRing (𝓞 K) K := fun g =>
    Matrix.trace (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) ^ 2 *
      Matrix.det ((g⁻¹ : GL (Fin 2) (AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))
  have hφc : Continuous φ :=
    ((Units.continuous_val.matrix_trace).pow 2).mul (Units.continuous_coe_inv.matrix_det)
  have hdet : ∀ a b : GL (Fin 2) (AdeleRing (𝓞 K) K),
      Matrix.det ((a * b : GL (Fin 2) (AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) =
        Matrix.det (a : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) * Matrix.det (b : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) :=
    fun a b => by rw [Units.val_mul, Matrix.det_mul]
  have hdet1 : ∀ x : GL (Fin 2) (AdeleRing (𝓞 K) K),
      Matrix.det ((x⁻¹ : GL (Fin 2) (AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) *
        Matrix.det (x : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) = 1 :=
    fun x => by rw [← hdet, inv_mul_cancel, Units.val_one, Matrix.det_one]
  have hφconj : ∀ x g : GL (Fin 2) (AdeleRing (𝓞 K) K), φ (x⁻¹ * g * x) = φ g := by
    intro x g
    have h1 : Matrix.trace ((x⁻¹ * g * x : GL (Fin 2) (AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) =
        Matrix.trace (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) := by
      rw [Units.val_mul, Units.val_mul, Matrix.trace_mul_cycle, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.one_mul]
    have h2 : Matrix.det (((x⁻¹ * g * x)⁻¹ : GL (Fin 2) (AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) =
        Matrix.det ((g⁻¹ : GL (Fin 2) (AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) := by
      rw [show (x⁻¹ * g * x)⁻¹ = x⁻¹ * g⁻¹ * x by group, hdet, hdet]
      calc Matrix.det ((x⁻¹ : GL (Fin 2) (AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) *
            Matrix.det ((g⁻¹ : GL (Fin 2) (AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) *
            Matrix.det (x : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))
          = Matrix.det ((g⁻¹ : GL (Fin 2) (AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) *
            (Matrix.det ((x⁻¹ : GL (Fin 2) (AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) *
              Matrix.det (x : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))) := by ring
        _ = _ := by rw [hdet1, mul_one]
    simp only [φ, h1, h2]

  have hval : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (u : Kˣ),
      φ (AutomorphicForm.centralScalar (𝓞 K) K z *
          diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1) =
        algebraMap K (AdeleRing (𝓞 K) K) (((u : K) + 1) ^ 2 * ((u⁻¹ : Kˣ) : K)) := by
    intro z u
    set a : (AdeleRing (𝓞 K) K)ˣ := Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u with ha
    set γ := AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 a 1 with hγd
    have hz : ∀ i j : Fin 2, ((AutomorphicForm.centralScalar (𝓞 K) K z : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j = if i = j then (z : AdeleRing (𝓞 K) K) else 0 := by
      intro i j; change Matrix.scalar (Fin 2) _ i j = _; rw [Matrix.scalar_apply, Matrix.diagonal_apply]
    have hd : ∀ i j : Fin 2, ((diagUnits2 a 1 : GL (Fin 2) (AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j =
        (!![(a : AdeleRing (𝓞 K) K), 0; 0, 1] : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j := fun _ _ => rfl
    have hγ : ∀ i j : Fin 2, ((γ : GL (Fin 2) (AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j =
        (!![(z : AdeleRing (𝓞 K) K) * (a : AdeleRing (𝓞 K) K), 0; 0, (z : AdeleRing (𝓞 K) K)] :
          Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j := by
      intro i j
      rw [hγd, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
      simp only [hz, hd]
      fin_cases i <;> fin_cases j <;> simp

    have hdetγ : Matrix.GeneralLinearGroup.det γ = z * z * a := by
      apply Units.ext
      rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, hγ, hγ, hγ, hγ]
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        Matrix.head_cons, Units.val_mul]
      ring
    have hdetinv : Matrix.det ((γ⁻¹ : GL (Fin 2) (AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) =
        ((a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) *
          (((z⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) * ((z⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)) := by
      rw [← Matrix.GeneralLinearGroup.val_det_apply, map_inv, hdetγ]
      push_cast
      simp only [mul_inv_rev, Units.val_mul]
    have htr : Matrix.trace ((γ : GL (Fin 2) (AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) =
        (z : AdeleRing (𝓞 K) K) * (a : AdeleRing (𝓞 K) K) + (z : AdeleRing (𝓞 K) K) := by
      rw [Matrix.trace_fin_two, hγ, hγ]; simp
    show Matrix.trace ((γ : GL (Fin 2) (AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) ^ 2 *
      Matrix.det ((γ⁻¹ : GL (Fin 2) (AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) = _
    rw [htr, hdetinv]
    have hz1 : (z : AdeleRing (𝓞 K) K) * ((z⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) = 1 := Units.mul_inv z
    have hau : (a : AdeleRing (𝓞 K) K) = algebraMap K (AdeleRing (𝓞 K) K) (u : K) := rfl
    have hau' : ((a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) = algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K) := by
      rw [ha, ← map_inv]; rfl
    rw [map_mul, map_pow, map_add, map_one, ← hau, ← hau']
    have e : ((z : AdeleRing (𝓞 K) K) * (a : AdeleRing (𝓞 K) K) + (z : AdeleRing (𝓞 K) K)) ^ 2 *
        (((a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) *
          (((z⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) * ((z⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K))) =
        ((a : AdeleRing (𝓞 K) K) + 1) ^ 2 * ((a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) *
          ((z : AdeleRing (𝓞 K) K) * ((z⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)) ^ 2 := by ring
    rw [e, hz1, one_pow, mul_one]

  set C := φ '' tsupport f with hC
  have hCc : IsCompact C := hfc.image hφc
  have hfin := NumberField.AdeleRing.finite_setOf_algebraMap_mem_of_isCompact K hCc

  let kf : Kˣ → K := fun u => ((u : K) + 1) ^ 2 * ((u⁻¹ : Kˣ) : K)
  have hfib : ∀ k : K, {u : Kˣ | kf u = k}.Finite := by
    intro k
    have hp : (Polynomial.X ^ 2 + Polynomial.C (2 - k) * Polynomial.X + 1 : Polynomial K) ≠ 0 := by
      intro h
      have := congrArg (fun p : Polynomial K => p.coeff 0) h
      simp at this
    have hR : ((Polynomial.X ^ 2 + Polynomial.C (2 - k) * Polynomial.X + 1 : Polynomial K).roots.toFinset :
        Set K).Finite := Finset.finite_toSet _
    refine (hR.preimage (Set.injOn_of_injective (fun a b h => Units.ext h))).subset ?_
    intro u hu
    simp only [Set.mem_setOf_eq] at hu
    simp only [Set.mem_preimage, Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hp,
      Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_one]
    have hu0 : (u : K) ≠ 0 := u.ne_zero
    have hk : ((u : K) + 1) ^ 2 = k * (u : K) := by
      have := congrArg (fun t => t * (u : K)) hu
      simpa [kf, mul_assoc, Units.inv_mul, hu0] using this
    linear_combination hk
  set SU : Set Kˣ := {u | kf u ∈ {k : K | algebraMap K (AdeleRing (𝓞 K) K) k ∈ C}} with hSU
  have hSUfin : SU.Finite := by
    refine (hfin.biUnion fun k _ => hfib k).subset ?_
    intro u hu
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
    exact ⟨kf u, hu, rfl⟩
  refine ⟨hSUfin.toFinset, fun u _ huU z x => ?_⟩
  by_contra hne
  have hmem : x⁻¹ * (AutomorphicForm.centralScalar (𝓞 K) K z *
      diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1) * x ∈ tsupport f :=
    subset_tsupport _ hne
  have hC' : algebraMap K (AdeleRing (𝓞 K) K) (kf u) ∈ C := by
    rw [← hval z u, ← hφconj x]
    exact ⟨_, hmem, rfl⟩
  exact huU (hSUfin.mem_toFinset.mpr hC')

end S_AutomorphicForm_exists_finset_forall_apply_conj_centralScalar_mul_diagUnits2_eq_zero_of_hasCompactSupport
end P2MW
export P2MW.S_AutomorphicForm_exists_finset_forall_apply_conj_centralScalar_mul_diagUnits2_eq_zero_of_hasCompactSupport (solution)
