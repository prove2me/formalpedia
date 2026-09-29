-- Prove2me | Definitions.Def_Grunbaum2003_reconstructionIncidenceCode
-- name    : Grunbaum2003_reconstructionIncidenceCode
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T07:04:42.875609+00:00
-- url     : https://prove2.me/theorems/afe1ecd8-4ef4-4caa-9761-98e9fd04d1d6
-- title:
--   Binary vertex-incidence table encoding
-- statement:
--   A labelled face-incidence table is encoded as self-delimiting dimension, vertex-count, and row-count headers followed by the dense Boolean incidence rows.
-- source:
--   Expression-essential incidence encoding for Branko Grünbaum, Convex Polytopes, 2nd ed. (Springer, 2003), §12.4 algorithmic reconstruction, printed p. 234a / PDF p. 277; source.pdf SHA-256 070befaa8c47f043ef9da1df0705910480eb692f044d1843c9f048f3e61fecac.

import Definitions.Def_Grunbaum2003_containmentBitBlock
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Bits

set_option autoImplicit false

namespace Grunbaum2003

/-- Dense binary vertex-incidence table, with self-delimiting binary headers
for dimension, number of vertices, and number of rows. Vertex labels are
the column indices; no real coordinates enter the algorithm's input. -/
def reconstructionIncidenceCode (d n : ℕ) (rows : List (Finset (Fin n))) :
    List Bool :=
  containmentBitBlock d.bits ++ containmentBitBlock n.bits ++
    containmentBitBlock rows.length.bits ++
      (rows.map (fun F => List.ofFn (fun i : Fin n => decide (i ∈ F)))).flatten

end Grunbaum2003


