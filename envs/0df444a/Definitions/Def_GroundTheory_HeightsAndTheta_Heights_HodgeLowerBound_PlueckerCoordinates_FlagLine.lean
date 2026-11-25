-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_PlueckerCoordinates_FlagLine
-- name    : GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_PlueckerCoordinates_FlagLine
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T08:16:38.438081+00:00
-- url     : https://prove2.me/theorems/0cab88f2-6511-40aa-9a2b-5ebc14c3ba57
-- title:
--   Flag Line
-- statement:
--   Definitions and structural lemmas for Flag Line, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/PlueckerCoordinates/FlagLine.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_PlueckerCoordinates_IsPlueckerCoord
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree.LineFlag
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.LowerBoundFree.Line
open scoped Matrix
abbrev DL : ComponentDataHodge zeroSystem Unit Unit (PBlk 2) Ω (fun _ => Fin 2 → Ω) := lineDataHodgeZero
def lineM : Unit → Fin DL.N → ℕ
  | _, ⟨0, _⟩ => 2
  | _, ⟨1, _⟩ => 1
  | _, ⟨_ + 2, _⟩ => 0
def lineGen : ∀ (τ : Unit) (i : Fin DL.N), Fin (lineM τ i) →
    ((Fin 2 → Ω) [⋀^Fin ((i : ℕ) + 1)]→ₗ[Ω] Ω)
  | _, ⟨0, _⟩ => fun m => AlternatingMap.ofSubsingleton Ω (Fin 2 → Ω) Ω (0 : Fin 1) (LinearMap.proj m)
  | _, ⟨1, _⟩ => fun _ => (Pi.basisFun Ω (Fin 2)).det
  | _, ⟨_ + 2, _⟩ => fun m => m.elim0
theorem twistFactor_zero (c : (k : Unit) → PBlk 2 k) : twistFactor DL.y c 0 = 1 := by
  simp [twistFactor]
theorem altFin1_apply (φ : (Fin 2 → Ω) [⋀^Fin 1]→ₗ[Ω] Ω) (v : Fin 1 → Fin 2 → Ω) :
    φ v = ∑ m, v 0 m * φ (fun _ => Pi.basisFun Ω (Fin 2) m) := by
  set ψ := (AlternatingMap.ofSubsingleton Ω (Fin 2 → Ω) Ω (0 : Fin 1)).symm φ
  have hψ : ∀ w, φ (fun _ => w) = ψ w := fun w => by
    conv_lhs => rw [← (AlternatingMap.ofSubsingleton Ω (Fin 2 → Ω) Ω (0 : Fin 1)).apply_symm_apply φ]
    rfl
  have hv : v = fun _ => v 0 := funext fun a => by rw [Subsingleton.elim a 0]
  rw [hv, hψ]
  simp only [hψ]
  conv_lhs => rw [← (Pi.basisFun Ω (Fin 2)).sum_repr (v 0)]
  simp [map_smul, smul_eq_mul]
theorem altFin1_eq (φ : (Fin 2 → Ω) [⋀^Fin 1]→ₗ[Ω] Ω) :
    φ = ∑ m : Fin 2, φ (fun _ => Pi.basisFun Ω (Fin 2) m) •
      AlternatingMap.ofSubsingleton Ω (Fin 2 → Ω) Ω (0 : Fin 1) (LinearMap.proj m) := by
  ext v
  rw [altFin1_apply, Fin.sum_univ_two, Fin.sum_univ_two, AlternatingMap.add_apply,
    AlternatingMap.smul_apply, AlternatingMap.smul_apply]
  simp [smul_eq_mul, mul_comm]
theorem lat_line (c : (k : Unit) → PBlk 2 k) (e : Fin 2 → Ω) :
    e ∈ (DL.W ()).lat c ↔ ∀ q, e q ∈ chartRing ℤ (segreCoord yLine) c :=
  mem_trivLat
theorem det_mem (c : (k : Unit) → PBlk 2 k) (e : Fin 2 → Fin 2 → Ω)
    (he : ∀ a q, e a q ∈ chartRing ℤ (segreCoord yLine) c) :
    (Pi.basisFun Ω (Fin 2)).det e ∈ chartRing ℤ (segreCoord yLine) c := by
  rw [Module.Basis.det_apply, Matrix.det_fin_two]
  simp only [Module.Basis.toMatrix_apply, Pi.basisFun_repr]
  exact sub_mem (mul_mem (he _ _) (he _ _)) (mul_mem (he _ _) (he _ _))
theorem basis_mem (c : (k : Unit) → PBlk 2 k) (m : Fin 2) :
    Pi.basisFun Ω (Fin 2) m ∈ (DL.W ()).lat c := by
  rw [lat_line]
  intro q
  simp only [Pi.basisFun_apply, Pi.single_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _
def linePlueckerData : PlueckerData DL where
  b := 0
  M := lineM
  M_ge := by
    rintro _ ⟨_ | _ | n, hi⟩
    · show Nat.choose 2 (0 + 1) ≤ 2
      decide
    · show Nat.choose 2 (0 + 1 + 1) ≤ 1
      decide
    · exact absurd hi (by show ¬ (n + 2 < 2); omega)
  gen := lineGen
  global := by
    rintro _ ⟨_ | _ | n, hi⟩ m c _ e he
    · rw [twistFactor_zero, mul_one]
      show e 0 m ∈ chartRing ℤ (segreCoord yLine) c
      exact (lat_line c (e 0)).1 (he 0) m
    · rw [twistFactor_zero, mul_one]
      exact det_mem c e fun a => (lat_line c (e a)).1 (he a)
    · exact absurd hi (by show ¬ (n + 2 < 2); omega)
  generates := by
    rintro _ ⟨_ | _ | n, hi⟩ c _ φ hφ
    · refine ⟨fun m => φ (fun _ => Pi.basisFun Ω (Fin 2) m), fun m => ?_, altFin1_eq φ⟩
      have := hφ (fun _ => Pi.basisFun Ω (Fin 2) m) fun _ => basis_mem c m
      rwa [twistFactor_zero, mul_one] at this
    · refine ⟨fun _ => φ (Pi.basisFun Ω (Fin 2)), fun _ => ?_, ?_⟩
      · have := hφ (Pi.basisFun Ω (Fin 2)) fun a => basis_mem c a
        rwa [twistFactor_zero, mul_one] at this
      · show φ = ∑ m : Fin 1, φ (Pi.basisFun Ω (Fin 2)) • (Pi.basisFun Ω (Fin 2)).det
        rw [Fin.sum_univ_one]
        exact φ.eq_smul_basis_det (Pi.basisFun Ω (Fin 2))
    · exact absurd hi (by show ¬ (n + 2 < 2); omega)
abbrev PL : PlueckerData DL := linePlueckerData
def detInt (q : Fin 2 → Fin 2) : ℤ := (Matrix.of fun p a => if q a = p then (1 : ℤ) else 0).det
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree.LineFlag


