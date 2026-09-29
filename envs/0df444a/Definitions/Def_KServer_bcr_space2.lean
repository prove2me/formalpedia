-- Prove2me | Definitions.Def_KServer_bcr_space2
-- name    : KServer_bcr_space2
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-01T13:01:16.743627+00:00
-- url     : https://prove2.me/theorems/47e9f910-148f-4458-8e82-39627f8b5cd3
-- title:
--   The corrected BCR space family via theta gluings
-- statement:
--   The corrected Bubeck–Coester–Rabani space family: level $0$ is the path of $\beta+1$ equally spaced points with marked endpoints; level $w+1$ is the **theta gluing** of two three-copy paths of level $w$ — two paths of three copies sharing both endpoints, which is the cycle of six copies with orientations $(+,+,+,-,-,-)$ used in BCR's construction (both first thirds are $s$-anchored at the new start, as the stage-1 union argument requires). The marked points of level $w$ are at distance $\beta\cdot 3^w$ and the level has at most $(\beta+1)\cdot 6^w$ points. This supersedes the uniformly oriented cyclic family for the lower-bound construction.
-- source:
--   S. Bubeck, C. Coester, Y. Rabani, 'The randomized k-server conjecture is false!', STOC 2023, Section 4.

import Mathlib
import Definitions.Def_KServer_chunk_system
import Definitions.Def_KServer_cycle_glue
import Definitions.Def_KServer_bcr_space
import Definitions.Def_KServer_glue2

set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace KServer

/-- The corrected BCR space family: level `0` is the path of `β + 1` points;
level `w + 1` is the **theta gluing** of two three-copy paths of level `w`
(two paths of three copies sharing both endpoints), which is BCR's cycle of
six copies with orientations `(+,+,+,−,−,−)`. -/
noncomputable def bcrLevel2 (β : ℕ) (hβ : 0 < β) : ℕ → BCRLevel
  | 0 =>
    { carrier := Fin (β + 1)
      metric := pathMetric β
      fin := inferInstance
      dec := inferInstance
      s := 0
      t := Fin.last β
      hst := by
        intro h
        have := congrArg Fin.val h
        simp [Fin.last] at this
        omega }
  | (w + 1) =>
    let L := bcrLevel2 β hβ w
    { carrier := ThetaChain.Step L.s L.t L.hst
      metric := ThetaChain.stepMetric L.s L.t L.hst
      fin := inferInstance
      dec := inferInstance
      s := ThetaChain.stepS L.s L.t L.hst
      t := ThetaChain.stepT L.s L.t L.hst
      hst := ThetaChain.stepS_ne_stepT L.s L.t L.hst }

/-- The marked points of level `w` are at distance `β · 3^w`. -/
theorem bcrLevel2_dist_st (β : ℕ) (hβ : 0 < β) (w : ℕ) :
    dist (bcrLevel2 β hβ w).s (bcrLevel2 β hβ w).t = β * 3 ^ w := by
  induction w with
  | zero =>
    letI := pathMetric β
    show dist (0 : Fin (β + 1)) (Fin.last β) = (β : ℝ) * 3 ^ 0
    have h : dist (0 : Fin (β + 1)) (Fin.last β)
        = |((0 : Fin (β + 1)).val : ℝ) - ((Fin.last β).val : ℝ)| := rfl
    rw [h]
    simp [Fin.last]
  | succ w ih =>
    set L := bcrLevel2 β hβ w with hL
    letI := L.metric
    letI := ThetaChain.stepMetric L.s L.t L.hst
    have h1 := ThetaChain.dist_stepS_stepT L.s L.t L.hst
    show dist (ThetaChain.stepS L.s L.t L.hst) (ThetaChain.stepT L.s L.t L.hst)
      = (β : ℝ) * 3 ^ (w + 1)
    rw [h1, ih]
    ring

/-- Cardinality: level `w` has at most `(β + 1) · 6 ^ w` points. -/
theorem bcrLevel2_card_le (β : ℕ) (hβ : 0 < β) (w : ℕ) :
    Fintype.card (bcrLevel2 β hβ w).carrier ≤ (β + 1) * 6 ^ w := by
  induction w with
  | zero =>
    show Fintype.card (Fin (β + 1)) ≤ (β + 1) * 6 ^ 0
    simp
  | succ w ih =>
    set L := bcrLevel2 β hβ w with hL
    show Fintype.card (ThetaChain.Step L.s L.t L.hst) ≤ (β + 1) * 6 ^ (w + 1)
    have h2 : Fintype.card {y : L.carrier // y ≠ L.s} ≤ Fintype.card L.carrier :=
      Fintype.card_subtype_le _
    have h3 := Fintype.card_subtype_le
      (fun u : Chain3Point L.carrier L.s L.t =>
        u ≠ Chain3.start L.s L.t ∧ u ≠ Chain3.stop L.s L.t L.hst)
    have h4 : Fintype.card (Chain3Point L.carrier L.s L.t)
        = Fintype.card L.carrier + Fintype.card {y : L.carrier // y ≠ L.s}
          + Fintype.card {y : L.carrier // y ≠ L.s} := by
      unfold Chain3Point Chain2Point
      rw [Fintype.card_sum, Fintype.card_sum]
    have h5 : Fintype.card (ThetaChain.Step L.s L.t L.hst)
        = Fintype.card (Chain3Point L.carrier L.s L.t)
          + Fintype.card {u : Chain3Point L.carrier L.s L.t //
              u ≠ Chain3.start L.s L.t ∧ u ≠ Chain3.stop L.s L.t L.hst} := by
      unfold ThetaChain.Step ThetaPoint
      rw [Fintype.card_sum]
    have h6 : Fintype.card L.carrier ≤ (β + 1) * 6 ^ w := ih
    have h7 : (β + 1) * 6 ^ (w + 1) = 6 * ((β + 1) * 6 ^ w) := by ring
    omega

end KServer


