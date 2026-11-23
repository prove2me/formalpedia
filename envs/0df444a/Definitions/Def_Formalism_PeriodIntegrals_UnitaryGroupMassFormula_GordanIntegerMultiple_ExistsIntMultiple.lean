-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GordanIntegerMultiple_ExistsIntMultiple
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GordanIntegerMultiple_ExistsIntMultiple
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:25:34.777334+00:00
-- url     : https://prove2.me/theorems/f4068025-b638-4c83-ad9e-4c6ee8e0de3e
-- title:
--   Exists Int Multiple
-- statement:
--   Definitions and structural lemmas for Exists Int Multiple, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GordanIntegerMultiple/ExistsIntMultiple.lean

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_GordanCones
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
namespace GordanGenProof
open Finset
def gcone {n : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Fin n → ℚ) : Set (Fin n → ℚ) :=
  {x | ∃ c : ι → ℚ, (∀ i ∈ s, 0 ≤ c i) ∧ x = ∑ i ∈ s, c i • f i}
def hcone {n : ℕ} {ι : Type*} (A : Finset ι) (f : ι → Fin n → ℚ) : Set (Fin n → ℚ) :=
  {x | ∀ a ∈ A, 0 ≤ f a ⬝ᵥ x}
def fmSet {n : ℕ} (P : Finset ((Fin n → ℚ) × ℚ)) : Finset (Fin n → ℚ) :=
  (P.filter (fun p => p.2 = 0)).image Prod.fst ∪
    ((P.filter (fun p => 0 < p.2)) ×ˢ (P.filter (fun p => p.2 < 0))).image
      (fun pq => pq.1.2 • pq.2.1 - pq.2.2 • pq.1.1)
def stdIneq (n : ℕ) : Finset (Fin n → ℚ) :=
  (Finset.univ.image fun i : Fin n => (Pi.single i 1 : Fin n → ℚ)) ∪
    (Finset.univ.image fun i : Fin n => -(Pi.single i 1 : Fin n → ℚ))
theorem exists_int_multiple {n : ℕ} (v : Fin n → ℚ) :
    ∃ N : ℚ, 0 < N ∧ ∃ z : Fin n → ℤ, GordanCones.toQ z = N • v := by
  classical
  have hden : ∀ q : ℚ, 0 < q.den := fun q => q.den_pos
  have key : ∀ q : ℚ, q * (q.den : ℚ) = (q.num : ℚ) := fun q => Rat.mul_den_eq_num q
  refine ⟨∏ j, ((v j).den : ℚ), Finset.prod_pos fun j _ => by exact_mod_cast hden (v j),
    fun i => (v i).num * ∏ j ∈ Finset.univ.erase i, ((v j).den : ℤ), ?_⟩
  funext i
  show ((((v i).num * ∏ j ∈ Finset.univ.erase i, ((v j).den : ℤ) : ℤ)) : ℚ) =
    (∏ j, ((v j).den : ℚ)) * v i
  rw [← Finset.mul_prod_erase Finset.univ (fun j => ((v j).den : ℚ)) (Finset.mem_univ i)]
  push_cast
  rw [← key (v i)]
  ring
noncomputable def intOf {n : ℕ} (v : Fin n → ℚ) : Fin n → ℤ :=
  (exists_int_multiple v).choose_spec.2.choose
noncomputable def mulOf {n : ℕ} (v : Fin n → ℚ) : ℚ :=
  (exists_int_multiple v).choose
end GordanGenProof


