-- Prove2me | Definitions.Def_HSElemKernel_decodeInst
-- name    : HSElemKernel_decodeInst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:23:47.507235+00:00
-- url     : https://prove2.me/theorems/2d705ad0-7fc5-447d-87fc-e89c9c31c781
-- title:
--   Strict decoder of instance codes
-- statement:
--   The **instance decoder** reads a list $[\,n, m, k\,] \mathbin{+\!\!+} \mathrm{blocks}$ of natural numbers as the instance with universe $\{0, \dots, n-1\}$, parameter $k$, and family the set of the $m$ decoded blocks (each block is a length followed by that many elements). It rejects the list (returns *none*) when it is malformed or has leftover entries, an element is at least $n$, a block repeats an element, two blocks give the same set, or the number of blocks is not $m$.
--
--   It is the fixed, computable inverse of the code relation `IsInstCode`: the output of every kernel in the mission is read through it, never through a decoder chosen by the algorithm.
-- source:
--   Sheng–Xiao, A Near-Linear Element-Kernel for d-Hitting Set, arXiv:2609.06512 (held version, sha256 aca9c70e…), Section 3, p.6

import Mathlib
import Definitions.Def_HSElemKernel_HSInstance

namespace HSElemKernel

/-- Decode `m` blocks `|A| :: elements of A` over the universe `Fin n`; `none` on a malformed
list, an element `≥ n`, a repeated element in a block, or leftover entries. (Helper of
`decodeInst`.) -/
def decodeBlocks (n : ℕ) : ℕ → List ℕ → Option (List (List (Fin n)))
  | 0, [] => some []
  | 0, _ :: _ => none
  | _ + 1, [] => none
  | m + 1, len :: rest =>
      match (rest.take len).mapM
          (fun x => if h : x < n then some (⟨x, h⟩ : Fin n) else none) with
      | none => none
      | some elems =>
          if elems.length = len ∧ elems.Nodup then
            (decodeBlocks n m (rest.drop len)).map (fun tail => elems :: tail)
          else none

/-- The strict decoder of instance codes (Sheng–Xiao, arXiv:2609.06512, held version sha256
aca9c70e…, Section 3, p.6): `[n, m, k] ++ blocks` decodes to `(Fin n, S, k)` where `S` is the set
of the `m` decoded blocks, and to `none` when the list is malformed, an element is `≥ n`, a block
repeats an element, two blocks give the same set, or the number of blocks is not `m`.

**Formalization Note** It is the fixed, computable inverse of `IsInstCode`: every code of an
instance decodes to that instance, and the kernel's output is read through this decoder, never
through one chosen by the algorithm. -/
def decodeInst : List ℕ → Option HSInstance
  | n :: m :: k :: rest =>
      match decodeBlocks n m rest with
      | none => none
      | some L =>
          if (L.map List.toFinset).Nodup then
            some ⟨n, (L.map List.toFinset).toFinset, k⟩
          else none
  | _ => none

end HSElemKernel


