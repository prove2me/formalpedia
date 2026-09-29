-- Prove2me | Definitions.Def_KServer_chunk_saturate
-- name    : KServer_chunk_saturate
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-01T12:09:53.984856+00:00
-- url     : https://prove2.me/theorems/42bedddf-529c-4b15-a317-ebda00c1d6b2
-- title:
--   Saturated-event summation and stopped conditional expectations
-- statement:
--   Summation engines over a chunk system's filtration: the expected total size; constancy of a stopping time on the atoms of its own stopping level; the inequality form of the fiberwise summation engine (two random variables whose conditional averages compare on every time-$h$ atom compare in weighted sum over every $\mathcal F_h$-saturated event); and the identity $\sum_\omega P(\omega)\,\mathbb E[f \mid \mathcal F_{\sigma(\omega)}](\omega) = \mathbb E[f]$ for stopping times $\sigma$ — the tower property sampled at a stopping time. These are the reusable working parts of the chunk-combining and stage constructions in the BCR induction.
-- source:
--   S. Bubeck, C. Coester, Y. Rabani, 'The randomized k-server conjecture is false!', STOC 2023, Lemma 15 machinery.

import Mathlib
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b
import Definitions.Def_KServer_chunk_cond
import Definitions.Def_KServer_chunk_stopping

set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace KServer

namespace ChunkSystemB

variable {X : Type*} [MetricSpace X] {s t : X} {cA cB T pe : ℝ} {mL : ℕ}
variable (C : ChunkSystemB X s t cA cB T pe mL)

/-- The expected total size. -/
noncomputable def expTotal : ℝ := ∑ ω, C.P ω * C.totalSize ω

/-- A stopping time is constant on the atoms of its own stopping level. -/
theorem stopping_const {σ : C.Ω → ℕ} (hσ : C.IsStopping σ) {ω ω' : C.Ω}
    (hh : C.hist (σ ω) ω' = C.hist (σ ω) ω) : σ ω' = σ ω := by
  have h1 : σ ω' ≤ σ ω := (hσ (σ ω) ω ω' hh.symm).mp (le_refl _)
  rcases Nat.lt_or_ge (σ ω') (σ ω) with hlt | hge
  · exfalso
    have h2 := (hσ (σ ω') ω ω'
      (C.href (σ ω') (σ ω) (le_of_lt hlt) ω' ω hh).symm).mpr (le_refl _)
    omega
  · omega

/-- Inequality version of the saturated-set summation engine. -/
theorem sum_saturated_le (h : ℕ) (B : Finset C.Ω)
    (hsat : ∀ ω ∈ B, ∀ ω', C.hist h ω' = C.hist h ω → ω' ∈ B)
    (f g : C.Ω → ℝ)
    (hfg : ∀ ω ∈ B, ∑ ω' ∈ C.atom h ω, C.P ω' * f ω'
      ≤ ∑ ω' ∈ C.atom h ω, C.P ω' * g ω') :
    ∑ ω ∈ B, C.P ω * f ω ≤ ∑ ω ∈ B, C.P ω * g ω := by
  classical
  have hfib := Finset.sum_fiberwise_of_maps_to
    (s := B) (t := B.image (C.hist h)) (g := C.hist h)
    (fun ω hm => Finset.mem_image_of_mem _ hm) (fun ω => C.P ω * f ω)
  have hfib' := Finset.sum_fiberwise_of_maps_to
    (s := B) (t := B.image (C.hist h)) (g := C.hist h)
    (fun ω hm => Finset.mem_image_of_mem _ hm) (fun ω => C.P ω * g ω)
  rw [← hfib, ← hfib']
  refine Finset.sum_le_sum fun b hb => ?_
  obtain ⟨ω₁, hω₁, hb1⟩ := Finset.mem_image.mp hb
  have hfiber : B.filter (fun ω => C.hist h ω = b) = C.atom h ω₁ := by
    ext ω
    simp only [Finset.mem_filter, C.mem_atom]
    constructor
    · rintro ⟨_, hωb⟩
      rw [hωb, hb1]
    · intro hω
      exact ⟨hsat ω₁ hω₁ ω hω, by rw [hω, hb1]⟩
  rw [hfiber]
  exact hfg ω₁ hω₁

/-- Summing `P · condExp f (σ ·)` at a stopping time over everything
recovers the plain weighted sum. -/
theorem sum_stopped_condExp {σ : C.Ω → ℕ} (hσ : C.IsStopping σ) (f : C.Ω → ℝ) :
    ∑ ω, C.P ω * C.condExp f (σ ω) ω = ∑ ω, C.P ω * f ω := by
  classical
  have hfib := Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset C.Ω))
    (t := Finset.univ.image (fun ω => Nat.pair (σ ω) (C.hist (σ ω) ω)))
    (g := fun ω => Nat.pair (σ ω) (C.hist (σ ω) ω))
    (fun ω hm => Finset.mem_image_of_mem _ hm)
    (fun ω => C.P ω * C.condExp f (σ ω) ω)
  have hfib' := Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset C.Ω))
    (t := Finset.univ.image (fun ω => Nat.pair (σ ω) (C.hist (σ ω) ω)))
    (g := fun ω => Nat.pair (σ ω) (C.hist (σ ω) ω))
    (fun ω hm => Finset.mem_image_of_mem _ hm)
    (fun ω => C.P ω * f ω)
  rw [← hfib, ← hfib']
  refine Finset.sum_congr rfl fun b hb => ?_
  obtain ⟨ω₁, _, hb1⟩ := Finset.mem_image.mp hb
  have hfiber : Finset.univ.filter
        (fun ω => Nat.pair (σ ω) (C.hist (σ ω) ω) = b)
      = C.atom (σ ω₁) ω₁ := by
    ext ω
    simp only [Finset.mem_filter, C.mem_atom, Finset.mem_univ, true_and]
    constructor
    · intro hω
      rw [← hb1] at hω
      obtain ⟨he, hh⟩ := Nat.pair_eq_pair.mp hω
      rw [he] at hh
      exact hh
    · intro hω
      have hσc : σ ω = σ ω₁ := stopping_const C hσ hω
      rw [← hb1, hσc, hω]
  rw [hfiber]
  have hconst : ∀ ω ∈ C.atom (σ ω₁) ω₁,
      C.condExp f (σ ω) ω = C.condExp f (σ ω₁) ω := by
    intro ω hm
    rw [C.mem_atom] at hm
    rw [stopping_const C hσ hm]
  rw [Finset.sum_congr rfl fun ω hm => by rw [hconst ω hm]]
  exact C.sum_atom_mul_condExp f (σ ω₁) ω₁


end ChunkSystemB

end KServer


