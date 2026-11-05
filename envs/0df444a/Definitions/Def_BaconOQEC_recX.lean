-- Prove2me | Definitions.Def_BaconOQEC_recX
-- name    : BaconOQEC_recX
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:24:11.682208+00:00
-- url     : https://prove2.me/theorems/ef5496ca-ba97-4252-862a-98cb746c7229
-- title:
--   X-correction on row $i_0$
-- statement:
--   The $X$-part of the recovery is the analogue of (24) "with the role of the rows and columns reversed". The $S^Z$-syndrome reads $e_j(a)\oplus e_{j+1}(a)$. The decoder turns it into $e''$, and an $X$ is applied on site $(i_0,j)$ for every column $j$ with $e''_j = 1$, for a freely chosen row $i_0$. This is the $X$-part (bit matrix) of that Pauli operator: $e''_j$ in row $i_0$, $0$ elsewhere.
--
--   **Formalization Note** It depends only on the syndrome and on $i_0$, never on the error.
-- source:
--   D. Bacon, Operator Quantum Error Correcting Subsystems for Self-Correcting Quantum Memories, arXiv:quant-ph/0506023v4, §IV.C, p.8

import Mathlib
import Definitions.Def_BaconOQEC_Bits
import Definitions.Def_BaconOQEC_repDecode

namespace BaconOQEC

/-- Bacon, *Operator Quantum Error Correcting Subsystems for Self-Correcting Quantum Memories*,
arXiv:quant-ph/0506023v4, §IV.C, p.8: the `X`-part of the recovery, the analogue of (24) "for Pauli
X errors (with the role of the rows and columns reversed)": from the `S^Z`-syndrome `s^Z = s.2`
(which reads `e_j(a) ⊕ e_{j+1}(a)`, (23)) decode `e″ = repDecode s^Z` and apply `X` on site `(i₀, j)`
for every column `j` with `e″_j = 1`. As the `a`-matrix of a Pauli operator, it is `e″_j` in row `i₀`
and `0` elsewhere.

**Formalization Note.** It depends only on the syndrome `s` and the free row `i₀`, never on the
error. Indices 0-based, `n = m + 1`; syndrome bit `0` is eigenvalue `+1`. -/
def recX {m : ℕ} (s : (Fin m → ZMod 2) × (Fin m → ZMod 2)) (i0 : Fin (m + 1)) : Bits m :=
  fun i j => if i = i0 then repDecode s.2 j else 0

end BaconOQEC


