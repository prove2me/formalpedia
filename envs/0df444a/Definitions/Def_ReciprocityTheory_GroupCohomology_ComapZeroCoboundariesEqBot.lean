-- Prove2me | Definitions.Def_ReciprocityTheory_GroupCohomology_ComapZeroCoboundariesEqBot
-- name    : ReciprocityTheory_GroupCohomology_ComapZeroCoboundariesEqBot
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:05:27.366819+00:00
-- url     : https://prove2.me/theorems/725fb76a-1d97-4be9-976c-a9a5b92a563d
-- title:
--   Comap Zero Coboundaries Eq Bot
-- statement:
--   Definitions and structural lemmas for Comap Zero Coboundaries Eq Bot, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/ComapZeroCoboundariesEqBot.lean

import Definitions.Def_ReciprocityTheory_GroupCohomology_ContinuousContractNth
import Theorems.Thm_ReciprocityTheory_Gal_mem_riemannRochSpace_iff_regularAt_everywhere

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.Coh
open ReciprocityTheory.Gal Cx
noncomputable section
universe u
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
namespace LowDeg
section Dn
variable {M : Type u} [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [ContinuousConstSMul R M] (rho : Representation R G M)
theorem dn_zero_apply (f : (Fin 0 → G) → M) (v : Fin 1 → G) :
    dn rho 0 f v = rho (v 0) (f ![]) - f ![] := by
  have hs : (fun i : Fin 0 => v i.succ) = ![] := Subsingleton.elim _ _
  have hc : (Fin.contractNth 0 (· * ·) v : Fin 0 → G) = ![] := Subsingleton.elim _ _
  show rho (v 0) (f fun i => v i.succ) + ∑ j : Fin 1, (-1 : R) ^ ((j : ℕ) + 1) •
    f (Fin.contractNth j (· * ·) v) = _
  rw [Fin.sum_univ_one, hs, hc]
  simp only [Fin.val_zero, zero_add, pow_one, neg_one_smul]
  rw [sub_eq_add_neg]
theorem dn_one_apply (f : (Fin 1 → G) → M) (v : Fin 2 → G) :
    dn rho 1 f v = rho (v 0) (f ![v 1]) - f ![v 0 * v 1] + f ![v 0] := by
  have hs : (fun i : Fin 1 => v i.succ) = ![v 1] := by
    funext k; fin_cases k; rfl
  have h0 : (Fin.contractNth 0 (· * ·) v : Fin 1 → G) = ![v 0 * v 1] := by
    funext k; fin_cases k; first | rfl | simp [Fin.contractNth]
  have h1 : (Fin.contractNth 1 (· * ·) v : Fin 1 → G) = ![v 0] := by
    funext k; fin_cases k; first | rfl | simp [Fin.contractNth]
  show rho (v 0) (f fun i => v i.succ) + ∑ j : Fin 2, (-1 : R) ^ ((j : ℕ) + 1) •
    f (Fin.contractNth j (· * ·) v) = _
  rw [Fin.sum_univ_two, hs, h0, h1]
  norm_num <;> abel
theorem dn_two_apply (f : (Fin 2 → G) → M) (v : Fin 3 → G) :
    dn rho 2 f v = rho (v 0) (f ![v 1, v 2]) - f ![v 0 * v 1, v 2] + f ![v 0, v 1 * v 2] -
      f ![v 0, v 1] := by
  have hs : (fun i : Fin 2 => v i.succ) = ![v 1, v 2] := by
    funext k; fin_cases k <;> rfl
  have h0 : (Fin.contractNth 0 (· * ·) v : Fin 2 → G) = ![v 0 * v 1, v 2] := by
    funext k; fin_cases k <;> first | rfl | simp [Fin.contractNth]
  have h1 : (Fin.contractNth 1 (· * ·) v : Fin 2 → G) = ![v 0, v 1 * v 2] := by
    funext k; fin_cases k <;> first | rfl | simp [Fin.contractNth]
  have h2 : (Fin.contractNth 2 (· * ·) v : Fin 2 → G) = ![v 0, v 1] := by
    funext k; fin_cases k <;> first | rfl | simp [Fin.contractNth]
  show rho (v 0) (f fun i => v i.succ) + ∑ j : Fin 3, (-1 : R) ^ ((j : ℕ) + 1) •
    f (Fin.contractNth j (· * ·) v) = _
  rw [Fin.sum_univ_three, hs, h0, h1, h2]
  norm_num <;> abel
end Dn
variable (M : TRep R G)
theorem coch_d_val (n : ℕ) (x : M.coch.X n) : (M.coch.d n x).1 = dn M.rho n x.1 := rfl
theorem dn_eq_zero {n : ℕ} {x : M.coch.X n} (hx : M.coch.d n x = 0) : dn M.rho n x.1 = 0 := by
  rw [← coch_d_val]
  exact congrArg Subtype.val hx
theorem coch_d_eq_zero {n : ℕ} {x : M.coch.X n} (h : dn M.rho n x.1 = 0) : M.coch.d n x = 0 := Subtype.ext h
def zEquiv (n : ℕ) : M.coch.Z n ≃ₗ[R] Zn M.rho n where
  toFun x := ⟨x.1.1, x.1.2, LinearMap.mem_ker.2 (dn_eq_zero M (LinearMap.mem_ker.1 x.2))⟩
  invFun z := ⟨⟨z.1, z.2.1⟩, LinearMap.mem_ker.2 (coch_d_eq_zero M (x := ⟨z.1, z.2.1⟩) (LinearMap.mem_ker.1 z.2.2))⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl
theorem map_zEquiv (n : ℕ) :
    ((M.coch.B n).comap (M.coch.Z n).subtype).map (zEquiv M n : M.coch.Z n →ₗ[R] Zn M.rho n) =
      (Bn M.rho n).comap (Zn M.rho n).subtype := by
  ext z
  constructor
  · intro hz
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hz
    have hy' : ((y : M.coch.X n)) ∈ M.coch.B n := Submodule.mem_comap.1 hy
    refine Submodule.mem_comap.2 ?_
    show (y : M.coch.X n).1 ∈ Bn M.rho n
    cases n with
    | zero =>
      have h0 : (y : M.coch.X 0) = 0 :=
        (Submodule.mem_bot R).1 (show (y : M.coch.X 0) ∈ (⊥ : Submodule R (M.coch.X 0)) from hy')
      show (y : M.coch.X 0).1 ∈ (⊥ : Submodule R ((Fin 0 → G) → M.V))
      rw [h0]
      first | exact Submodule.zero_mem _ | simp
    | succ k =>
      obtain ⟨w, hw⟩ := LinearMap.mem_range.1
        (show (y : M.coch.X (k + 1)) ∈ LinearMap.range (M.coch.d k) from hy')
      show (y : M.coch.X (k + 1)).1 ∈ (Cn M.rho k).map (dn M.rho k)
      refine Submodule.mem_map.2 ⟨w.1, w.2, ?_⟩
      rw [← coch_d_val, hw]
  · intro hz
    have hz' : ((z : (Fin n → G) → M.V)) ∈ Bn M.rho n := Submodule.mem_comap.1 hz
    refine Submodule.mem_map.2
      ⟨(zEquiv M n).symm z, Submodule.mem_comap.2 ?_, (zEquiv M n).apply_symm_apply z⟩
    show (((zEquiv M n).symm z : M.coch.Z n) : M.coch.X n) ∈ M.coch.B n
    cases n with
    | zero =>
      have h0 : ((z : (Fin 0 → G) → M.V)) = 0 := (Submodule.mem_bot R).1
        (show ((z : (Fin 0 → G) → M.V)) ∈ (⊥ : Submodule R ((Fin 0 → G) → M.V)) from hz')
      show (((zEquiv M 0).symm z : M.coch.Z 0) : M.coch.X 0) ∈ (⊥ : Submodule R (M.coch.X 0))
      exact (Submodule.mem_bot R).2 (Subtype.ext h0)
    | succ k =>
      obtain ⟨w, hw, e⟩ := Submodule.mem_map.1
        (show ((z : (Fin (k + 1) → G) → M.V)) ∈ (Cn M.rho k).map (dn M.rho k) from hz')
      show (((zEquiv M (k + 1)).symm z : M.coch.Z (k + 1)) : M.coch.X (k + 1)) ∈
        LinearMap.range (M.coch.d k)
      exact LinearMap.mem_range.2 ⟨⟨w, hw⟩, Subtype.ext ((coch_d_val M k ⟨w, hw⟩).trans e)⟩
def hEquiv (n : ℕ) : M.H n ≃ₗ[R] Hn M.rho n :=
  Submodule.Quotient.equiv _ _ (zEquiv M n) (map_zEquiv M n)
def zeroCocyclesEquivInvariants : M.coch.Z 0 ≃ₗ[R] H0 M.rho where
  toFun x := ⟨x.1.1 ![], (mem_riemannRochSpace_iff_regularAt_everywhere _ _).2 fun g => by
    have h := congrFun (dn_eq_zero M (LinearMap.mem_ker.1 x.2)) ![g]
    rw [dn_zero_apply] at h
    exact sub_eq_zero.1 h⟩
  invFun m := ⟨⟨fun _ => m.1, continuous_const⟩, LinearMap.mem_ker.2
    (coch_d_eq_zero M (x := ⟨fun _ => m.1, continuous_const⟩) (funext fun v => by
      rw [dn_zero_apply, (mem_riemannRochSpace_iff_regularAt_everywhere _ _).1 m.2, sub_self]; rfl))⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv x := Subtype.ext (Subtype.ext (funext fun v => by
    show x.1.1 ![] = x.1.1 v
    rw [Subsingleton.elim v ![]]))
  right_inv _ := rfl
theorem comap_zeroCoboundaries_eq_bot : (M.coch.B 0).comap (M.coch.Z 0).subtype = ⊥ := by
  show (⊥ : Submodule R (M.coch.X 0)).comap (M.coch.Z 0).subtype = ⊥
  rw [Submodule.comap_bot, Submodule.ker_subtype]
def cohomZeroEquivContinuous : M.H 0 ≃ₗ[R] H0 M.rho :=
  (Submodule.quotEquivOfEqBot _ (comap_zeroCoboundaries_eq_bot M)).trans (zeroCocyclesEquivInvariants M)
def oneCocyclesEquivFunctions : M.coch.Z 1 ≃ₗ[R] Z1 M.rho where
  toFun x := ⟨fun g => x.1.1 ![g], x.1.2.comp (continuous_id.matrixVecCons continuous_const),
    fun g h => by
      have e := congrFun (dn_eq_zero M (LinearMap.mem_ker.1 x.2)) ![g, h]
      rw [dn_one_apply] at e
      show x.1.1 ![g * h] = x.1.1 ![g] + M.rho g (x.1.1 ![h])
      have e' : M.rho g (x.1.1 ![h]) - x.1.1 ![g * h] + x.1.1 ![g] = 0 := e
      rw [← sub_eq_zero, ← neg_eq_zero, ← e']
      abel⟩
  invFun f := ⟨⟨fun v => f.1 (v 0), f.2.1.comp (continuous_apply 0)⟩, LinearMap.mem_ker.2
    (coch_d_eq_zero M (x := ⟨fun v => f.1 (v 0), f.2.1.comp (continuous_apply 0)⟩) (funext fun v => by
      rw [dn_one_apply]
      simp only [Matrix.cons_val_zero, Pi.zero_apply]
      rw [f.2.2]
      abel))⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv x := Subtype.ext (Subtype.ext (funext fun v => by
    show x.1.1 ![v 0] = x.1.1 v
    rw [show ![v 0] = v from by funext i; fin_cases i; rfl]))
  right_inv _ := rfl
theorem map_z1Equiv :
    ((M.coch.B 1).comap (M.coch.Z 1).subtype).map (oneCocyclesEquivFunctions M : M.coch.Z 1 →ₗ[R] Z1 M.rho) =
      (B1 M.rho).comap (Z1 M.rho).subtype := by
  ext z
  constructor
  · intro hz
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hz
    obtain ⟨w, hw⟩ := LinearMap.mem_range.1
      (show (y : M.coch.X 1) ∈ LinearMap.range (M.coch.d 0) from Submodule.mem_comap.1 hy)
    refine Submodule.mem_comap.2 (LinearMap.mem_range.2 ⟨w.1 ![], funext fun g => ?_⟩)
    show M.rho g (w.1 ![]) - w.1 ![] = (y : M.coch.X 1).1 ![g]
    rw [← hw, coch_d_val, dn_zero_apply] <;> rfl
  · intro hz
    obtain ⟨m, hm⟩ := LinearMap.mem_range.1
      (show (z : G → M.V) ∈ LinearMap.range (d0 M.rho) from Submodule.mem_comap.1 hz)
    refine Submodule.mem_map.2 ⟨(oneCocyclesEquivFunctions M).symm z, Submodule.mem_comap.2
      (LinearMap.mem_range.2 ⟨⟨fun _ => m, continuous_const⟩, Subtype.ext (funext fun v => ?_)⟩),
      (oneCocyclesEquivFunctions M).apply_symm_apply z⟩
    show dn M.rho 0 (fun _ => m) v = (z : G → M.V) (v 0)
    rw [dn_zero_apply, ← hm] <;> rfl
def h1EquivOfOrderTwo : M.H 1 ≃ₗ[R] H1 M.rho :=
  Submodule.Quotient.equiv _ _ (oneCocyclesEquivFunctions M) (map_z1Equiv M)
def twoCocyclesEquivFunctions : M.coch.Z 2 ≃ₗ[R] Z2 M.rho where
  toFun x := ⟨fun p => x.1.1 ![p.1, p.2],
    x.1.2.comp (continuous_fst.matrixVecCons (continuous_snd.matrixVecCons continuous_const)),
    fun g h k => by
      have e := congrFun (dn_eq_zero M (LinearMap.mem_ker.1 x.2)) ![g, h, k]
      rw [dn_two_apply] at e
      exact e⟩
  invFun f := ⟨⟨fun v => f.1 (v 0, v 1), f.2.1.comp ((continuous_apply 0).prodMk (continuous_apply 1))⟩,
    LinearMap.mem_ker.2 (coch_d_eq_zero M
      (x := ⟨fun v => f.1 (v 0, v 1), f.2.1.comp ((continuous_apply 0).prodMk (continuous_apply 1))⟩)
      (funext fun v => by
        rw [dn_two_apply]
        exact f.2.2 (v 0) (v 1) (v 2)))⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv x := Subtype.ext (Subtype.ext (funext fun v => by
    show x.1.1 ![v 0, v 1] = x.1.1 v
    rw [show ![v 0, v 1] = v from by funext i; fin_cases i <;> rfl]))
  right_inv _ := rfl
theorem map_z2Equiv :
    ((M.coch.B 2).comap (M.coch.Z 2).subtype).map (twoCocyclesEquivFunctions M : M.coch.Z 2 →ₗ[R] Z2 M.rho) =
      (B2 M.rho).comap (Z2 M.rho).subtype := by
  ext z
  constructor
  · intro hz
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hz
    obtain ⟨w, hw⟩ := LinearMap.mem_range.1
      (show (y : M.coch.X 2) ∈ LinearMap.range (M.coch.d 1) from Submodule.mem_comap.1 hy)
    refine Submodule.mem_comap.2 (Submodule.mem_map.2 ⟨fun g => w.1 ![g],
      (show Continuous w.1 from w.2).comp (continuous_id.matrixVecCons continuous_const),
      funext fun p => ?_⟩)
    show M.rho p.1 (w.1 ![p.2]) - w.1 ![p.1 * p.2] + w.1 ![p.1] = (y : M.coch.X 2).1 ![p.1, p.2]
    rw [← hw, coch_d_val, dn_one_apply] <;> rfl
  · intro hz
    obtain ⟨c, hc, hcz⟩ := Submodule.mem_map.1
      (show (z : G × G → M.V) ∈ (contMaps R M.V G).map (d1 M.rho) from Submodule.mem_comap.1 hz)
    refine Submodule.mem_map.2 ⟨(twoCocyclesEquivFunctions M).symm z, Submodule.mem_comap.2
      (LinearMap.mem_range.2 ⟨⟨fun v => c (v 0), (show Continuous c from hc).comp (continuous_apply 0)⟩,
        Subtype.ext (funext fun v => ?_)⟩),
      (twoCocyclesEquivFunctions M).apply_symm_apply z⟩
    show dn M.rho 1 (fun v => c (v 0)) v = (z : G × G → M.V) (v 0, v 1)
    rw [dn_one_apply, ← hcz] <;> rfl
def h2EquivOfOrderTwo : M.H 2 ≃ₗ[R] H2 M.rho :=
  Submodule.Quotient.equiv _ _ (twoCocyclesEquivFunctions M) (map_z2Equiv M)
variable {G' : Type u} [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G'] {M' : TRep R G'}
end LowDeg
end
end ReciprocityTheory.Coh


