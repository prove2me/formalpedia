-- Prove2me | Definitions.Def_KServer_bcr_space
-- name    : KServer_bcr_space
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-01T09:51:16.650014+00:00
-- url     : https://prove2.me/theorems/85acc7f5-4c9d-4472-8982-bca392ff4249
-- title:
--   The BCR space family: iterated six-copy cycles over a path
-- statement:
--   The **Bubeck–Coester–Rabani space family** (STOC 2023, Section 4): level $0$ is the path of $\beta + 1$ equally spaced points with marked endpoints; level $w+1$ is the cycle of **six** copies of level $w$ (via the cyclic gluing `Def_KServer_cycle_glue`), with the new marked points $s_{w+1}, t_{w+1}$ at antipodal junctions — the start of copy $0$ and the start of copy $3$ — so that the space decomposes into a left path and a right path of three copies each between them.
--
--   Two accompanying facts: $d(s_w, t_w) = \beta \cdot 3^w$ (`bcrLevel_dist_st`, both ways around the cycle cost $3D$), and $|\mathcal{M}_w| \le (\beta+1) \cdot 6^w$ (`bcrLevel_card_le`).
--
--   ## Role
--
--   These are the metric spaces on which the randomized $k$-server lower bound $\Omega(\log^2 k)$ is established: with $n = |\mathcal{M}_w|$ points, $\log n = \Theta(w)$, and the chunked induction of BCR's Lemma 6 forces every randomized MSS algorithm to have competitive ratio $\ge \alpha w^2 = \Omega(\log^2 n)$.
--
--   ## Formalization note
--
--   Each level is a bundled `BCRLevel` (carrier, metric, finiteness, marked points), so the recursion over `w` is an ordinary definition; the marked points of the base are $0$ and `Fin.last β`.
-- source:
--   S. Bubeck, C. Coester, Y. Rabani, 'The randomized k-server conjecture is false!', STOC 2023, Section 4.

import Mathlib
import Definitions.Def_KServer_chunk_system
import Definitions.Def_KServer_cycle_glue

namespace KServer

/-- A level of the BCR construction: a finite metric space with two distinct
marked points. -/
structure BCRLevel where
  carrier : Type
  metric : MetricSpace carrier
  fin : Fintype carrier
  dec : DecidableEq carrier
  s : carrier
  t : carrier
  hst : s ≠ t

attribute [instance] BCRLevel.metric BCRLevel.fin BCRLevel.dec

/-- The BCR space family: level `0` is the path of `β + 1` points; level `w + 1`
is the cycle of six copies of level `w`, with the marked points at antipodal
junctions. -/
noncomputable def bcrLevel (β : ℕ) (hβ : 0 < β) : ℕ → BCRLevel
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
    let L := bcrLevel β hβ w
    { carrier := CyclePoint L.carrier L.t 6
      metric := cycleMetric L.carrier L.s L.t 6 (by norm_num)
      fin := inferInstance
      dec := inferInstance
      s := cyclePt 0 L.s L.hst
      t := cyclePt 3 L.s L.hst
      hst := by
        intro h
        have := congrArg Prod.fst h
        simp only [cyclePt] at this
        exact absurd this (by decide) }

/-- The distance between the marked points is `β · 3^w`. -/
theorem bcrLevel_dist_st (β : ℕ) (hβ : 0 < β) (w : ℕ) :
    dist (bcrLevel β hβ w).s (bcrLevel β hβ w).t = β * 3 ^ w := by
  induction w with
  | zero =>
    letI := pathMetric β
    show dist (0 : Fin (β + 1)) (Fin.last β) = (β : ℝ) * 3 ^ 0
    have h : dist (0 : Fin (β + 1)) (Fin.last β)
        = |((0 : Fin (β + 1)).val : ℝ) - ((Fin.last β).val : ℝ)| := rfl
    rw [h]
    simp [Fin.last]
  | succ w ih =>
    set L := bcrLevel β hβ w with hL
    letI := L.metric
    show cycleDist L.s L.t (cyclePt 0 L.s L.hst) (cyclePt 3 L.s L.hst) = (β : ℝ) * 3 ^ (w + 1)
    have h03 : (0 : Fin 6) ≠ 3 := by decide
    rw [cycleDist_cross L.s L.t 0 3 h03 L.s L.s L.hst L.hst]
    have hval : (((3 - 0 : Fin 6)).val : ℝ) = 3 := by norm_num
    rw [hval]
    have hss : dist L.s L.s = 0 := dist_self _
    have hts : dist L.t L.s = dist L.s L.t := dist_comm _ _
    rw [hss, hts, ih]
    push_cast
    rw [show (β : ℝ) * 3 ^ w + ((3 : ℝ) - 1) * ((β : ℝ) * 3 ^ w) + 0
        = 3 * ((β : ℝ) * 3 ^ w) from by ring,
      show (0 : ℝ) + ((6 : ℝ) - 3 - 1) * ((β : ℝ) * 3 ^ w) + (β : ℝ) * 3 ^ w
        = 3 * ((β : ℝ) * 3 ^ w) from by ring, min_self]
    ring

/-- Cardinality bound: level `w` has at most `(β + 1) · 6^w` points. -/
theorem bcrLevel_card_le (β : ℕ) (hβ : 0 < β) (w : ℕ) :
    Fintype.card (bcrLevel β hβ w).carrier ≤ (β + 1) * 6 ^ w := by
  induction w with
  | zero =>
    show Fintype.card (Fin (β + 1)) ≤ (β + 1) * 6 ^ 0
    simp
  | succ w ih =>
    show Fintype.card (CyclePoint (bcrLevel β hβ w).carrier (bcrLevel β hβ w).t 6)
      ≤ (β + 1) * 6 ^ (w + 1)
    rw [card_cyclePoint]
    have h1 : Fintype.card (bcrLevel β hβ w).carrier - 1 ≤ (β + 1) * 6 ^ w := by omega
    calc 6 * (Fintype.card (bcrLevel β hβ w).carrier - 1) ≤ 6 * ((β + 1) * 6 ^ w) := by omega
      _ = (β + 1) * 6 ^ (w + 1) := by ring

end KServer


