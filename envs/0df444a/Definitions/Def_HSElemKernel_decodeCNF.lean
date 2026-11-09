-- Prove2me | Definitions.Def_HSElemKernel_decodeCNF
-- name    : HSElemKernel_decodeCNF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:23:11.144916+00:00
-- url     : https://prove2.me/theorems/56938a33-cb3c-44f3-99f4-cee7af7ca8fe
-- title:
--   Strict decoder of CNF codes
-- statement:
--   The **CNF decoder** reads a list $[\,N, M\,] \mathbin{+\!\!+} \mathrm{blocks}$ as the CNF formula with variables $x_0, \dots, x_{N-1}$ and the $M$ decoded clauses (a block is a width followed by that many literal codes, $2v + b$ standing for $x_v$ if $b = 1$ and $\neg x_v$ if $b = 0$). It rejects malformed lists, leftover entries, and literal codes at least $2N$. It inverts the code of CNF formulas, and the CNF output of the randomized encoding (Lemma 2.2) is read through it.
-- source:
--   Sheng–Xiao, A Near-Linear Element-Kernel for d-Hitting Set, arXiv:2609.06512 (held version, sha256 aca9c70e…), Section 3.3, p.7

import Mathlib
import Definitions.Def_MainResults

namespace HSElemKernel

/-- Decode `M` clause blocks `|C| :: literal codes` over `N` variables; `none` on a malformed
list, a literal code `≥ 2N`, or leftover entries. (Helper of `decodeCNF`.) -/
def decodeClauses (N : ℕ) : ℕ → List ℕ → Option (MainResults.CNF N)
  | 0, [] => some []
  | 0, _ :: _ => none
  | _ + 1, [] => none
  | M + 1, len :: rest =>
      match (rest.take len).mapM
          (fun x => if h : x / 2 < N then some ((⟨x / 2, h⟩ : Fin N), x % 2 == 1) else none) with
      | none => none
      | some lits =>
          if lits.length = len then
            (decodeClauses N M (rest.drop len)).map (fun tail => lits :: tail)
          else none

/-- The strict decoder of CNF codes (Sheng–Xiao, arXiv:2609.06512, held version sha256
aca9c70e…, Section 3.3, p.7): `[N, M] ++ blocks` decodes to the formula with `N` variables and the
`M` decoded clauses, and to `none` when the list is malformed. It inverts `cnfCode`; the CNF
output of an algorithm is read through it. -/
def decodeCNF : List ℕ → Option (Σ N : ℕ, MainResults.CNF N)
  | N :: M :: rest => (decodeClauses N M rest).map (fun φ => ⟨N, φ⟩)
  | _ => none

end HSElemKernel


