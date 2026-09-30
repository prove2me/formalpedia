-- Prove2me | Definitions.Def_SeymourMFMC_Binary_Q6
-- name    : SeymourMFMC_Binary_Q6
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T01:20:26.432984+00:00
-- url     : https://prove2.me/theorems/63b39487-e9eb-4fb9-8f62-fbf10cbedddb
-- title:
--   The clutter Q₆ = {{1,3,5},{1,4,6},{2,3,6},{2,4,5}}
-- statement:
--   The clutter $Q_6$ on the six elements $\{1, \dots, 6\}$ is
--
--   $$
--   Q_6 = \{\{1,3,5\}, \{1,4,6\}, \{2,3,6\}, \{2,4,5\}\}.
--   $$
--
--   It is the collection of triangles of $K_4$ (edges labelled $1, \dots, 6$), a binary clutter which has the weak max-flow min-cut property but is not Mengerian. It is the single excluded minor in the paper's main theorem.
--
--   **Formalization Note** The ground set is `Fin 6`, and the paper's element $k$ is `k - 1`; so $Q_6$ is `{{0,2,4}, {0,3,5}, {1,2,5}, {1,3,4}}`.
-- source:
--   Seymour, The Matroids with the Max-Flow Min-Cut Property, J. Combin. Theory Ser. B 23 (1977), p. 192, Section 1

import Mathlib

namespace SeymourMFMC.Binary

/-- The clutter `Q₆ = {{1,3,5}, {1,4,6}, {2,3,6}, {2,4,5}}` of Seymour 1977, p. 192, on the ground
set `Fin 6`, with the paper's elements `1, …, 6` shifted down by one to `0, …, 5`. -/
def Q6 : Finset (Finset (Fin 6)) :=
  {{0, 2, 4}, {0, 3, 5}, {1, 2, 5}, {1, 3, 4}}

end SeymourMFMC.Binary


