-- Prove2me | Definitions.Def_KServer_prophecyS
-- name    : KServer_prophecyS
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-02T01:36:48.784794+00:00
-- url     : https://prove2.me/theorems/c43d96a2-9630-48df-8313-6deb448d8c0b
-- title:
--   Start-measurable fractional-tiling prophecy bound
-- statement:
--   The start-measurable fractional-tiling prophecy bound. ProphecyBoundS PE holds when, for every finite family of depth windows [aa i, bb i) with tail cuts jj i >= bb i and every family of nonnegative weights, each measurable in the history at its own window start, whose total weight at each single depth is at most one, the weighted sum over the family of the expected squared Doob increments of the tail masses is at most PE. Own-start measurability is precisely what a filtration reveals at the moment a window opens; it makes every weighted cross term inside a window die by the tower property (sq_sum_orth_w, weighted orthogonality of martingale increments), so the invariant passes through block regroupings with no loss, and it matches what the race filtration reveals about each component path at a component window start. The bound weakens in the constant (mono) and recovers the plain partitioned prophecy bound with unit weights on a monotone partition (toPlain).
-- source:
--   Bartal-Chrobak-Rasala lower bound program: prophecy energy

import Mathlib
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b
import Definitions.Def_KServer_chunk_cond
import Definitions.Def_KServer_chunk_stopping
import Definitions.Def_KServer_chunk_var
import Definitions.Def_KServer_sturdy
import Definitions.Def_KServer_prophecy
import Definitions.Def_KServer_prophecy2

set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 1600000

namespace KServer

namespace ChunkSystemB

variable {X : Type*} [MetricSpace X] {s t : X}
variable {cLo cHi total price : ℝ} {mLo : ℕ}
variable {C : ChunkSystemB X s t cLo cHi total price mLo}

/-- **Start-measurable fractional-tiling prophecy bound**: for every
finite family of depth windows `[aa i, bb i)` with tail cuts
`jj i ≥ bb i`, and every family of nonnegative weights — each
measurable in the history at *its own window start* — whose total
weight at each single depth is at most one, the weighted prophecy
energy of the family is at most `PE`.  Own-start measurability is
exactly what a filtration reveals at the moment a window opens; it is
the form of the invariant that passes through block regroupings with
no loss (weighted orthogonality holds inside every cell) and through
races (the race filtration at a window start reveals each component
path precisely up to the component window start). -/
def ProphecyBoundS (C : ChunkSystemB X s t cLo cHi total price mLo)
    (PE : ℝ) : Prop :=
  ∀ (N : ℕ) (aa bb jj : Fin N → ℕ) (W : Fin N → C.Ω → ℝ),
    (∀ i (ω : C.Ω), 0 ≤ W i ω) →
    (∀ i (ω ω' : C.Ω), C.hist (aa i) ω' = C.hist (aa i) ω → W i ω' = W i ω) →
    (∀ i, bb i ≤ jj i) →
    (∀ (h : ℕ) (ω : C.Ω),
      ∑ i ∈ Finset.univ.filter (fun i => aa i ≤ h ∧ h < bb i), W i ω ≤ 1) →
    ∑ i, ∑ h ∈ Finset.Ico (aa i) (bb i),
      ∑ ω, C.P ω * W i ω * (C.dinc (C.tailSum (jj i)) h ω) ^ 2 ≤ PE

/-- The start-measurable tiling bound weakens in the constant. -/
theorem ProphecyBoundS.mono {PE PE' : ℝ}
    (h : C.ProphecyBoundS PE) (hPE : PE ≤ PE') :
    C.ProphecyBoundS PE' :=
  fun N aa bb jj W hW0 hWm hbj htile =>
    le_trans (h N aa bb jj W hW0 hWm hbj htile) hPE

/-- The tiling bound recovers the plain prophecy bound: a monotone
partition is a fractional tiling with unit weights. -/
theorem ProphecyBoundS.toPlain {PE : ℝ}
    (h : C.ProphecyBoundS PE) : C.ProphecyBound PE := by
  intro K e he0 hem heK
  have hmono : Monotone e := monotone_nat_of_le_succ hem
  have h1 := h K (fun i => e i.1) (fun i => e (i.1 + 1))
    (fun i => e (i.1 + 1)) (fun _ _ => (1 : ℝ))
    (fun _ _ => by norm_num)
    (fun _ _ _ _ => rfl)
    (fun i => le_refl _)
    (fun hd ω => by
      have hcard : (Finset.univ.filter
          (fun i : Fin K => e i.1 ≤ hd ∧ hd < e (i.1 + 1))).card ≤ 1 := by
        refine Finset.card_le_one.mpr fun a ha b hb => ?_
        simp only [Finset.mem_filter] at ha hb
        by_contra hab
        rcases Nat.lt_or_ge a.1 b.1 with hlt | hge
        · have : e (a.1 + 1) ≤ e b.1 := hmono hlt
          omega
        · have hlt' : b.1 < a.1 := by
            rcases Nat.lt_or_ge b.1 a.1 with h' | h'
            · exact h'
            · exact absurd (Fin.ext (by omega)) hab
          have : e (b.1 + 1) ≤ e a.1 := hmono hlt'
          omega
      rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      exact_mod_cast hcard)
  refine le_trans (le_of_eq ?_) h1
  rw [Finset.sum_range fun k => ∑ h' ∈ Finset.Ico (e k) (e (k + 1)),
    ∑ ω, C.P ω * (C.dinc (C.tailSum (e (k + 1))) h' ω) ^ 2]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun h' _ => ?_
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [mul_one]

/-- **Weighted orthogonality of martingale increments**: a weight
measurable at a depth `a` at or before every index in the set factors
through the square of a sum of increments, since every weighted cross
term dies by the tower property at the later index. -/
theorem sq_sum_orth_w (U : C.Ω → ℝ) (W : ℕ → C.Ω → ℝ)
    (sset : Finset ℕ) (a : ℕ)
    (ha : ∀ h ∈ sset, a ≤ h)
    (hU : ∀ ω ω' : C.Ω, C.hist a ω' = C.hist a ω → U ω' = U ω)
    (hmeas : ∀ h ∈ sset, ∀ ω ω' : C.Ω,
      C.hist (h + 1) ω' = C.hist (h + 1) ω → W h ω' = W h ω)
    (hzero : ∀ h ∈ sset, ∀ ω, C.condExp (W h) h ω = 0) :
    ∑ ω, C.P ω * (U ω * (∑ h ∈ sset, W h ω) ^ 2)
      = ∑ h ∈ sset, ∑ ω, C.P ω * (U ω * W h ω ^ 2) := by
  have hcross : ∀ h ∈ sset, ∀ h' ∈ sset, h < h' →
      ∑ ω, C.P ω * (U ω * (W h ω * W h' ω)) = 0 := by
    intro h hm h' hm' hlt
    have hu : ∀ ω ω' : C.Ω, C.hist h' ω' = C.hist h' ω →
        U ω' * W h ω' = U ω * W h ω := fun ω ω' hh => by
      rw [hU ω ω' (C.href a h' (ha h' hm') ω' ω hh),
        hmeas h hm ω ω' (C.href (h + 1) h' (by omega) ω' ω hh)]
    have h1 : ∑ ω, C.P ω * (U ω * (W h ω * W h' ω))
        = ∑ ω, C.P ω * ((fun ω' => U ω' * W h ω') ω * W h' ω) :=
      Finset.sum_congr rfl fun ω _ => by ring
    rw [h1, sum_P_mul_condExp h' (fun ω' => U ω' * W h ω') (W h') hu]
    refine Finset.sum_eq_zero fun ω _ => ?_
    rw [hzero h' hm' ω, mul_zero, mul_zero]
  have hexp : ∑ ω, C.P ω * (U ω * (∑ h ∈ sset, W h ω) ^ 2)
      = ∑ h ∈ sset, ∑ h' ∈ sset,
          ∑ ω, C.P ω * (U ω * (W h ω * W h' ω)) := by
    have h1 : ∀ ω : C.Ω, C.P ω * (U ω * (∑ h ∈ sset, W h ω) ^ 2)
        = ∑ h ∈ sset, ∑ h' ∈ sset,
            C.P ω * (U ω * (W h ω * W h' ω)) := by
      intro ω
      rw [pow_two, Finset.sum_mul_sum]
      rw [show ∑ h ∈ sset, ∑ h' ∈ sset,
          C.P ω * (U ω * (W h ω * W h' ω))
          = ∑ h ∈ sset, C.P ω * (U ω
              * ∑ h' ∈ sset, (W h ω * W h' ω)) from
        Finset.sum_congr rfl fun h _ => by
          rw [Finset.mul_sum, Finset.mul_sum]]
      rw [show ∑ h ∈ sset, C.P ω * (U ω * ∑ h' ∈ sset, W h ω * W h' ω)
          = C.P ω * (U ω * ∑ h ∈ sset, ∑ h' ∈ sset, W h ω * W h' ω) from by
        rw [Finset.mul_sum, Finset.mul_sum]]
    rw [Finset.sum_congr rfl fun ω _ => h1 ω, Finset.sum_comm]
    exact Finset.sum_congr rfl fun h _ => Finset.sum_comm
  rw [hexp]
  refine Finset.sum_congr rfl fun h hm => ?_
  rw [Finset.sum_eq_single h]
  · refine Finset.sum_congr rfl fun ω _ => ?_
    rw [pow_two]
  · intro h' hm' hne
    rcases Nat.lt_or_ge h h' with hlt | hge
    · exact hcross h hm h' hm' hlt
    · have hlt' : h' < h := by omega
      rw [← hcross h' hm' h hm hlt']
      exact Finset.sum_congr rfl fun ω _ => by ring
  · intro hc
    exact absurd hm hc

end ChunkSystemB

end KServer


