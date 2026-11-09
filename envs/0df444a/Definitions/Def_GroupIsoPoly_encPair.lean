-- Prove2me | Definitions.Def_GroupIsoPoly_encPair
-- name    : GroupIsoPoly_encPair
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:49:47.93749+00:00
-- url     : https://prove2.me/theorems/f4bceabb-a5a0-49ea-a4a2-2a4131f8bc38
-- title:
--   Cayley tables of labelled groups and their binary code
-- statement:
--   Let $G$ be a finite group of order $N$ and let $e_G:G\to\{0,\dots,N-1\}$ be a bijection (a **labelling**). The **Cayley table** of $(G,e_G)$ is the $N\times N$ table
--   $$
--   t_G(i,j)=e_G\big(e_G^{-1}(i)\,e_G^{-1}(j)\big),\qquad 0\le i,j<N .
--   $$
--   The **binary code** of a pair of tables $t_G,t_H$ of the same order $N$ is the self-delimiting code of $N$, followed by the $N^2$ entries of $t_G$ in row-major order and then those of $t_H$, each entry written with the same self-delimiting code. Its length is $\Theta(N^2\log N)$.
--
--   This is the input of the Cayley-table group isomorphism problem: an algorithm sees only the two tables, never the groups themselves, and every labelling of a group gives a valid input.
--
--   **Formalization Note** Numbers use the published `ExponomialAssortment.FPTAS.encodeNat` (bit length in unary, a separator, then the bits). `cayley eG` is the table, `encTable` the code of one table, `encPair` the code of the pair. The code is never padded, so time polynomial in $N$ is time polynomial in the input length.
-- source:
--   Qiao, Zhang, Testing isomorphism of finite groups in time polynomial in the group order, preprint, Nov. 3, 2026 (held version sha256 eb9a3355…), Theorem 1.1, p.1 (PDF p.5)

import Mathlib
import Definitions.Def_ExponomialAssortment_FPTAS_Machine

set_option autoImplicit false

namespace GroupIsoPoly

open ExponomialAssortment.FPTAS (encodeNat)

/-- **The Cayley table of a labelled finite group.**

Qiao, Zhang, *Testing isomorphism of finite groups in time polynomial in the group order*, preprint,
Nov. 3, 2026 (held version sha256 eb9a3355…), Theorem 1.1, p.1 (PDF p.5): "Let G and H be two finite
groups of order N, given by their Cayley (multiplication) tables."

A labelling `eG : G ≃ Fin N` names the elements of `G` by `0, …, N-1`; the table entry in row `i`,
column `j` is the label of the product of the elements labelled `i` and `j`.

**Formalization Note.** The algorithm sees only the table, never the group as a Lean object; the
statements quantify over every group and every labelling. -/
def cayley {G : Type*} [Group G] {N : ℕ} (eG : G ≃ Fin N) : Fin N → Fin N → Fin N :=
  fun i j => eG (eG.symm i * eG.symm j)

/-- The binary code of an `N × N` table with entries in `Fin N`: its `N²` entries in row-major order,
each written with the self-delimiting code `encodeNat`. -/
def encTable (N : ℕ) (t : Fin N → Fin N → Fin N) : List Bool :=
  (List.ofFn fun i : Fin N => (List.ofFn fun j : Fin N => encodeNat (t i j : ℕ)).flatten).flatten

/-- **The binary input of group isomorphism given by Cayley tables.**

Qiao, Zhang, preprint, Nov. 3, 2026 (held version sha256 eb9a3355…), Theorem 1.1, p.1 (PDF p.5).

The code of a pair of tables is the code of the order `N`, then the row-major entries of the first
table, then those of the second.

**Formalization Note.** Numbers are written with the published
`ExponomialAssortment.FPTAS.encodeNat` (bit length in unary, a separator, then the bits), so the
input has length `Θ(N² log N)` and is never padded; time polynomial in `N` is time polynomial in the
input length. -/
def encPair (N : ℕ) (tG tH : Fin N → Fin N → Fin N) : List Bool :=
  encodeNat N ++ encTable N tG ++ encTable N tH

end GroupIsoPoly


