-- Prove2me | Definitions.Def_ClickomaniaNPC_ThreeColor_Play
-- name    : ClickomaniaNPC_ThreeColor_Play
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T03:29:24.683109+00:00
-- url     : https://prove2.me/theorems/f4f1a89a-c135-4c65-9132-1bcd20a28289
-- title:
--   Clickomania legal clicks, settling, column shifting and solvability
-- statement:
--   Deleting a finite set of cell coordinates acts simultaneously on the current board: each column retains exactly the cells outside the set, in its original bottom-to-top order, and then all empty columns are discarded, preserving left-to-right order. This implements vertical settling followed by column shifting.
--
--   A legal move selects a present cell and its entire maximal monochromatic component, requires the component to have at least two cells, and replaces the board by the result of this deletion. No new group is automatically removed. A board is solvable exactly when some finite sequence of legal moves, possibly empty, reaches a board with no blocks. Lists of empty columns count as empty terminal boards.
--
--   The deletion function is total even on an arbitrary finite coordinate set; only the legal-move predicate requires that set to be a whole nonsingleton group. Solvability depends on actual game operations, not on a reduction or any complexity assertion.
-- source:
--   Biedl, Demaine, Demaine, Fleischer, Jacobsen and Munro, The Complexity of Clickomania, arXiv:cs/0107031v1 (21 July 2001), section 1, p. 1; section 4, Theorem 15, p. 11. https://arxiv.org/abs/cs/0107031v1

import Definitions.Def_ClickomaniaNPC_ThreeColor_Grid

namespace ClickomaniaNPC.ThreeColor

/-- Simultaneously delete the indicated original coordinates, preserving vertical
survivor order, then discard empty columns while preserving horizontal order. -/
def eraseGroup (B : Board) (G : Finset Cell) : Board :=
  (B.mapIdx fun x col =>
    (col.zipIdx.filter fun cy => (x, cy.2) ∉ G).map Prod.fst).filter
      (fun col => !col.isEmpty)

/-- A click removes a whole component of at least two cells. Newly formed groups
remain in the result until a subsequent click. -/
def LegalMove (B B' : Board) : Prop :=
  ∃ p G, IsGroup B p G ∧ 2 ≤ G.card ∧ B' = eraseGroup B G

/-- A finite legal play, possibly empty, removes every block. The terminal test
also recognizes a list of empty columns as having no blocks. -/
def Solvable (B : Board) : Prop :=
  ∃ B', Relation.ReflTransGen LegalMove B B' ∧ B'.flatten = []

end ClickomaniaNPC.ThreeColor


