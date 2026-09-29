-- Prove2me | Definitions.Def_KServer_prophecyF
-- name    : KServer_prophecyF
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-02T01:30:18.977594+00:00
-- url     : https://prove2.me/theorems/418e8b83-b089-4f93-a794-a08c0a9003da
-- title:
--   Fractional-tiling prophecy bound
-- statement:
--   The fractional-tiling prophecy bound. ProphecyBoundF kappa_sh PE is the strongest form of the partitioned prophecy energy invariant: for every finite family of depth windows [aa i, bb i) with tail cuts jj i >= bb i, and every family of nonnegative weights measurable in the depth-kappa_sh history whose total weight at each single depth is at most one, the weighted sum over the family of the expected squared Doob increments of the tail masses (cut at jj i, over depths in the window) is at most PE. It weakens in the constant (mono), descends to smaller shift depths (anti), and recovers the plain partitioned prophecy bound by taking a monotone partition with unit weights (toPlain), since the cells of a monotone partition are pairwise disjoint and hence a fractional tiling.
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

/-- **Fractional-tiling prophecy bound**: for every finite family of
depth windows `[aa i, bb i)` with tail cuts `jj i ≥ bb i`, and every
family of nonnegative weights measurable in the depth-`κsh` history
whose total weight at each single depth is at most one, the weighted
prophecy energy of the family is at most `PE`.  This subsumes the plain
partition form (disjoint cells, unit weights) and the adapted-shift
form (a shift mixture is a fractional tiling), and additionally covers
window families that straddle each other, as arise when the survivor
phase of a race shifts the side windows by the consumed coin count. -/
def ProphecyBoundF (C : ChunkSystemB X s t cLo cHi total price mLo)
    (κsh : ℕ) (PE : ℝ) : Prop :=
  ∀ (N : ℕ) (aa bb jj : Fin N → ℕ) (W : Fin N → C.Ω → ℝ),
    (∀ i (ω : C.Ω), 0 ≤ W i ω) →
    (∀ i (ω ω' : C.Ω), C.hist κsh ω' = C.hist κsh ω → W i ω' = W i ω) →
    (∀ i, bb i ≤ jj i) →
    (∀ (h : ℕ) (ω : C.Ω),
      ∑ i ∈ Finset.univ.filter (fun i => aa i ≤ h ∧ h < bb i), W i ω ≤ 1) →
    ∑ i, ∑ h ∈ Finset.Ico (aa i) (bb i),
      ∑ ω, C.P ω * W i ω * (C.dinc (C.tailSum (jj i)) h ω) ^ 2 ≤ PE

/-- The fractional-tiling bound weakens in the constant. -/
theorem ProphecyBoundF.mono {κsh : ℕ} {PE PE' : ℝ}
    (h : C.ProphecyBoundF κsh PE) (hPE : PE ≤ PE') :
    C.ProphecyBoundF κsh PE' :=
  fun N aa bb jj W hW0 hWm hbj htile =>
    le_trans (h N aa bb jj W hW0 hWm hbj htile) hPE

/-- The fractional-tiling bound descends to smaller shift depths. -/
theorem ProphecyBoundF.anti {κsh κsh' : ℕ} {PE : ℝ}
    (hk : κsh' ≤ κsh) (h : C.ProphecyBoundF κsh PE) :
    C.ProphecyBoundF κsh' PE := by
  intro N aa bb jj W hW0 hWm hbj htile
  exact h N aa bb jj W hW0
    (fun i ω ω' hh => hWm i ω ω' (C.href κsh' κsh hk ω' ω hh))
    hbj htile

/-- The fractional-tiling bound recovers the plain prophecy bound: a
monotone partition is a fractional tiling with unit weights. -/
theorem ProphecyBoundF.toPlain {κsh : ℕ} {PE : ℝ}
    (h : C.ProphecyBoundF κsh PE) : C.ProphecyBound PE := by
  intro K e he0 hem heK
  have hmono : Monotone e := monotone_nat_of_le_succ hem
  have h1 := h K (fun i => e i.1) (fun i => e (i.1 + 1))
    (fun i => e (i.1 + 1)) (fun _ _ => (1 : ℝ))
    (fun _ _ => by norm_num)
    (fun _ _ _ _ => rfl)
    (fun i => le_refl _)
    (fun hd ω => by
      -- the cells of a monotone partition are pairwise disjoint
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

end ChunkSystemB

end KServer


