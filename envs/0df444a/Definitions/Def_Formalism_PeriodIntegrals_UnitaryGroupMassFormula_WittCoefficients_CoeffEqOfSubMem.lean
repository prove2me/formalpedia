-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittCoefficients_CoeffEqOfSubMem
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittCoefficients_CoeffEqOfSubMem
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:23:51.471387+00:00
-- url     : https://prove2.me/theorems/e629065e-122b-40f1-9758-c2b2e656ca25
-- title:
--   Coeff Eq Of Sub Mem
-- statement:
--   Definitions and structural lemmas for Coeff Eq Of Sub Mem, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WittCoefficients/CoeffEqOfSubMem.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ArtSch
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace PI.ArtSch.WittLiftWork
open WittVector
variable {p : ℕ} [hp : Fact p.Prime] {k : Type} [CommRing k]
noncomputable abbrev I (n : ℕ) : Ideal (WittVector p k) := RingHom.ker (WittVector.truncate (p := p) (R := k) n)
theorem mem_I {n : ℕ} {x : WittVector p k} : x ∈ I n ↔ ∀ i < n, x.coeff i = 0 := by
  first
    | exact WittVector.mem_ker_truncate x
    | exact WittVector.mem_ker_truncate
    | rw [RingHom.mem_ker]
      constructor
      · intro h i hi
        have h' := congrArg (TruncatedWittVector.coeff ⟨i, hi⟩) h
        simpa [WittVector.coeff_truncate] using h'
      · intro h
        refine TruncatedWittVector.ext fun i => ?_
        simpa [WittVector.coeff_truncate] using h i i.2
theorem I_zero (x : WittVector p k) : x ∈ I 0 :=
  mem_I.2 fun i hi => absurd hi (Nat.not_lt_zero i)
theorem sub_coeff_zero' (a c : WittVector p k) : (a - c).coeff 0 = a.coeff 0 - c.coeff 0 := by
  have h := WittVector.add_coeff_zero (a - c) c
  rw [sub_add_cancel] at h
  rw [h]
  ring
theorem iter_sub (n : ℕ) (a b : WittVector p k) :
    verschiebung^[n] (a - b) = verschiebung^[n] a - verschiebung^[n] b := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply', ih, map_sub]
theorem map_iter (f : k →+* k) (n : ℕ) (a : WittVector p k) :
    WittVector.map f (verschiebung^[n] a) = verschiebung^[n] (WittVector.map f a) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
    exact WittVector.map_verschiebung f _
theorem iter_coeff_lt (n : ℕ) (a : WittVector p k) : ∀ i < n, (verschiebung^[n] a).coeff i = 0 := by
  induction n with
  | zero => intro i hi; exact absurd hi (Nat.not_lt_zero i)
  | succ n ih =>
    intro i hi
    rw [Function.iterate_succ_apply']
    cases i with
    | zero => exact WittVector.verschiebung_coeff_zero _
    | succ j => exact (WittVector.verschiebung_coeff_succ _ j).trans (ih j (by omega))
theorem coeff_iterate_verschiebung_add (n : ℕ) (a : WittVector p k) (i : ℕ) :
    (verschiebung^[n] a).coeff (i + n) = a.coeff i := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (WittVector.verschiebung_coeff_succ (verschiebung^[n] a) (i + n)).trans (ih i)
theorem iter_coeff_self (n : ℕ) (a : WittVector p k) : (verschiebung^[n] a).coeff n = a.coeff 0 := by
  have h := coeff_iterate_verschiebung_add n a 0
  rwa [Nat.zero_add] at h
theorem iterate_verschiebung_mem_I (n : ℕ) (a : WittVector p k) : verschiebung^[n] a ∈ I n :=
  mem_I.2 (iter_coeff_lt n a)
section
variable [CharP k p]
noncomputable def δ (x : WittVector p k) : WittVector p k := WittVector.map (frobenius k p) x - x
theorem δ_add (a b : WittVector p k) : δ (a + b) = δ a + δ b := by
  show WittVector.map (frobenius k p) (a + b) - (a + b) =
    (WittVector.map (frobenius k p) a - a) + (WittVector.map (frobenius k p) b - b)
  rw [map_add]
  abel
theorem δ_iter (n : ℕ) (a : WittVector p k) : δ (verschiebung^[n] a) = verschiebung^[n] (δ a) := by
  show WittVector.map (frobenius k p) (verschiebung^[n] a) - verschiebung^[n] a =
    verschiebung^[n] (WittVector.map (frobenius k p) a - a)
  rw [map_iter, iter_sub]
theorem eq_iterate_verschiebung_mk_shift {n : ℕ} {z : WittVector p k} (hz : z ∈ I n) :
    z = verschiebung^[n] (WittVector.mk p fun i => z.coeff (i + n)) := by
  refine WittVector.ext fun i => ?_
  rcases Nat.lt_or_ge i n with hi | hi
  · rw [mem_I.1 hz i hi, iter_coeff_lt n _ i hi]
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + n := ⟨i - n, by omega⟩
    exact (coeff_iterate_verschiebung_add n (WittVector.mk p fun i => z.coeff (i + n)) j).symm
theorem coeff_sub_of_mem_I {n : ℕ} {x y : WittVector p k} (hx : x ∈ I n) (hy : y ∈ I n) :
    (x - y).coeff n = x.coeff n - y.coeff n := by
  obtain ⟨x', hx'⟩ : ∃ x', x = verschiebung^[n] x' := ⟨_, eq_iterate_verschiebung_mk_shift hx⟩
  obtain ⟨y', hy'⟩ : ∃ y', y = verschiebung^[n] y' := ⟨_, eq_iterate_verschiebung_mk_shift hy⟩
  subst hx' hy'
  rw [← iter_sub]
  simp only [iter_coeff_self]
  exact sub_coeff_zero' x' y'
theorem δ_teich_coeff_zero (b : k) : (δ (teichmuller p b)).coeff 0 = b ^ p - b := by
  show (WittVector.map (frobenius k p) (teichmuller p b) - teichmuller p b).coeff 0 = b ^ p - b
  rw [sub_coeff_zero', WittVector.map_coeff]
  rw [WittVector.teichmuller_coeff_zero, frobenius_def]
variable (hAS : ∀ a : k, ∃ y : k, y ^ p - y = a)
include hAS
theorem step {n : ℕ} (r : WittVector p k) (hr : r ∈ I n) :
    ∃ b : k, r - δ (verschiebung^[n] (teichmuller p b)) ∈ I (n + 1) := by
  obtain ⟨b, hb⟩ := hAS (r.coeff n)
  refine ⟨b, ?_⟩
  have hs : δ (verschiebung^[n] (teichmuller p b)) ∈ I n := by
    rw [δ_iter]
    exact iterate_verschiebung_mem_I n _
  have hsn : (δ (verschiebung^[n] (teichmuller p b))).coeff n = r.coeff n := by
    rw [δ_iter, iter_coeff_self,
      δ_teich_coeff_zero, hb]
  refine mem_I.2 fun i hi => ?_
  rcases Nat.lt_or_ge i n with h | h
  · exact mem_I.1 (Ideal.sub_mem _ hr hs) i h
  · obtain rfl : i = n := by omega
    rw [coeff_sub_of_mem_I hr hs, hsn, sub_self]
noncomputable def seq (x : WittVector p k) : (n : ℕ) → {y : WittVector p k // x - δ y ∈ I n}
  | 0 => ⟨0, I_zero _⟩
  | n + 1 => ⟨(seq x n).1 + verschiebung^[n]
      (teichmuller p (Classical.choose (step hAS (x - δ (seq x n).1) (seq x n).2))), by
        rw [δ_add, ← sub_sub]
        exact Classical.choose_spec (step hAS (x - δ (seq x n).1) (seq x n).2)⟩
noncomputable def lim (x : WittVector p k) : WittVector p k :=
  WittVector.mk p (fun i => (seq hAS x (i + 1)).1.coeff i)
end
end PI.ArtSch.WittLiftWork


