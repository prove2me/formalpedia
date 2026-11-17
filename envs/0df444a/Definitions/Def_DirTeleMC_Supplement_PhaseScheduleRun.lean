-- Prove2me | Definitions.Def_DirTeleMC_Supplement_PhaseScheduleRun
-- name    : DirTeleMC_Supplement_PhaseScheduleRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:42:11.399415+00:00
-- url     : https://prove2.me/theorems/543b66cf-dc29-40f9-9c11-3555900c533d
-- title:
--   The phase schedule of the pieces
-- statement:
--   Given the pieces of LEVELSEP with their depths, let $\ell_d(u)$ be the number of arcs of pieces of depth $d$ that leave the root $r$ and have tail $u$ in $G$, and $\ell^{\max}_d=\max_u\ell_d(u)$. The **phase schedule** consists of one phase for each level $d=0,1,\dots$ that has an instance, in increasing order; phase $d$ lasts
--   $$\ell^{\max}_d+\theta+\sigma-2$$
--   rounds. In phase $d$,
--
--   1. in each of the first $\ell^{\max}_d$ rounds, every vertex $u$ calls one of the heads of its arcs leaving $r$ in the pieces of depth $d$, until it has called all of them;
--   2. every vertex $v\ne r$ of a piece of depth $d$ calls, in every round of the phase after the round in which it is informed, one of its children in that piece that it has not called yet, as long as one exists.
--
--   This is the candidate schedule that LPSEP compares with the fallback.
--
--   **Formalization Note** The orders in which vertices call are free choices; calls that would fall after the end of their phase are not made.
-- source:
--   S. Kamali, S.-M. Seyed-Javadi, Approximation Algorithms for Directed Telephone Multicast, arXiv:2610.27422 (manuscript sha256 e56edddf…), Definition C.5, p.40 (PDF p.41)

import Mathlib
import Definitions.Def_DirTeleMC_Schedule
import Definitions.Def_DirTeleMC_Supplement_LevelSepRun

namespace DirTeleMC.Supplement

open DirTeleMC

variable (C : LSCtx)

/-- The per-level load `ℓ_d(u)` (Definition C.5, p.40): the number of arcs of pieces of depth `d` that leave `r` and
have G-tail `u`. -/
noncomputable def levelLoad (pcs : List (Piece C.I.n)) (d : ℕ) (u : Fin C.I.n) : ℕ := by
  classical
  exact ((pcs.filter fun pc => pc.depth = d).map fun pc =>
    if u ∈ pc.R then (pc.SW.filter fun v => pc.par v = u).card else 0).sum

/-- The length of phase `d` (Definition C.5, p.40): `ℓ^max_d + θ + σ − 2`, with `ℓ^max_d = max_u ℓ_d(u)`. -/
noncomputable def phaseLen (pcs : List (Piece C.I.n)) (d : ℕ) : ℕ :=
  Finset.univ.sup (levelLoad C pcs d) + C.θ + C.sigma - 2

/-- The number of rounds before phase `d`: the sum of the lengths of the phases `0, …, d − 1`. -/
noncomputable def phaseStart (pcs : List (Piece C.I.n)) (d : ℕ) : ℕ :=
  ∑ d' ∈ Finset.range d, phaseLen C pcs d'

/-- The number of levels that have an instance: one more than the largest depth of a piece (every instance has a
piece). -/
def numLevels (pcs : List (Piece C.I.n)) : ℕ :=
  (pcs.map fun pc => pc.depth + 1).foldr max 0

/-- The round in which the head `v` of an arc of the `i`-th piece is called, computed down `f` levels of the piece:
an arc leaving `r` with G-tail `u` is called in round `start_d + 1 + j` if it is the `j`-th (from `0`) in the order
`ordR d u` of the arcs of `u` into the pieces of depth `d`; an internal arc `(w, v)` is called in the round after
`w` is called plus the position of `v` in the order `ordW i w` of the children of `w` in the piece. -/
noncomputable def callTime (pcs : List (Piece C.I.n)) (ordR : ℕ → Fin C.I.n → List (ℕ × Fin C.I.n))
    (ordW : ℕ → Fin C.I.n → List (Fin C.I.n)) : ℕ → ℕ → Fin C.I.n → ℕ
  | 0, _, _ => 0
  | f + 1, i, v => by
    classical
    exact match pcs[i]? with
      | none => 0
      | some pc =>
        if pc.par v ∈ pc.R then phaseStart C pcs pc.depth + (ordR pc.depth (pc.par v)).idxOf (i, v) + 1
        else callTime pcs ordR ordW f i (pc.par v) + (ordW i (pc.par v)).idxOf v + 1

/-- **The phase schedule** of the pieces (Definition C.5, p.40).
Kamali, Seyed-Javadi, *Approximation Algorithms for Directed Telephone Multicast*, arXiv:2610.27422
(manuscript sha256 e56edddf…): "The phase schedule consists of consecutive phases, one for each level d = 0, 1, . . .
that has an instance, in increasing order of d; phase d lasts ℓ^max_d + θ + σ − 2 rounds. In phase d, (i) in each of
the first ℓ^max_d rounds, every vertex u of G calls one of the heads of the arcs that leave r with G-tail u in the
pieces of depth d, until it has called all of them, and (ii) every vertex v ≠ r of a piece of depth d calls, in every
round of the phase after the round in which it is informed, one of its children in that piece that it has not
called yet, as long as one exists."

`PhaseScheduleRun C pcs Y`: for some order `ordR d u` of the arcs leaving `r` with G-tail `u` in the pieces of depth `d`
(as pairs `(i, v)`: piece index and head) and some order `ordW i w` of the children of every vertex `w` of the `i`-th
piece, `Y` has one round for every round of the phases, and round `j + 1` consists of the calls `(par v, v)` whose
call round (`callTime`) is `j + 1` and lies in the phase of the piece.

**Formalization Note.** Calls that would fall after the end of their phase are not made (the source's "as long as one
exists" within the phase). The calls within a round are listed by piece index and then by vertex; their order inside a
round has no meaning. The orders `ordR`, `ordW` are free choices of the run. -/
noncomputable def PhaseScheduleRun (pcs : List (Piece C.I.n)) (Y : Schedule C.I.n) : Prop := by
  classical
  exact ∃ (ordR : ℕ → Fin C.I.n → List (ℕ × Fin C.I.n)) (ordW : ℕ → Fin C.I.n → List (Fin C.I.n)),
    (∀ d u, (ordR d u).Nodup ∧ ∀ q : ℕ × Fin C.I.n, q ∈ ordR d u ↔
      ∃ pc, pcs[q.1]? = some pc ∧ pc.depth = d ∧ q.2 ∈ pc.SW ∧ pc.par q.2 = u ∧ u ∈ pc.R) ∧
    (∀ i pc, pcs[i]? = some pc → ∀ w ∈ pc.SW, (ordW i w).Nodup ∧
      ∀ v, v ∈ ordW i w ↔ v ∈ pc.SW ∧ pc.par v = w) ∧
    Y = (List.range (phaseStart C pcs (numLevels C pcs))).map fun j =>
      (List.range pcs.length).flatMap fun i =>
        match pcs[i]? with
        | none => []
        | some pc =>
          ((List.finRange C.I.n).filter fun v => v ∈ pc.SW ∧
              callTime C pcs ordR ordW (C.I.n + 1) i v = j + 1 ∧
              callTime C pcs ordR ordW (C.I.n + 1) i v ≤ phaseStart C pcs pc.depth + phaseLen C pcs pc.depth).map
            fun v => (pc.par v, v)

end DirTeleMC.Supplement


