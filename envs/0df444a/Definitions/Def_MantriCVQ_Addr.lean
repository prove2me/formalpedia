-- Prove2me | Definitions.Def_MantriCVQ_Addr
-- name    : MantriCVQ_Addr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:08:42.332833+00:00
-- url     : https://prove2.me/theorems/e1ee3913-49fe-4aad-8d2a-c19a17d4c673
-- title:
--   Leaf addresses of a recursive tree
-- statement:
--   A leaf of a tree is addressed by the path from the root: at a node of dimension $m$, one bit says whether to descend into a code child ($0$) or a data child ($1$), and $m$ bits give the index of the child. This module gives the typed addresses, their flat bit strings ($w0x$ is the code child $x$ and $w1y$ the data child $y$ of the node $w$), and their length $\sum_i(m_i+1)$, Eq. (4.3).
-- source:
--   Mantri, Classical Verification of Quantum Computation Beyond the Polynomial Hierarchy, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), §4.1, p. 16 (PDF p. 18)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Complexity

open QAlgorithms.Complexity

namespace MantriCVQ

/-- The addresses of the leaves of a tree whose nodes on each root-to-leaf path have the listed
dimensions, from the top down (Mantri, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), §4.1, p. 16 (PDF
p. 18)): at a node of dimension `m`, one bit says whether to descend into a code child (`false`) or a
data child (`true`), and `m` bits give the index of the child. The list `[]` is a single leaf. -/
def Addr : List ℕ → Type
  | [] => Unit
  | m :: ms => Bool × Bits m × Addr ms

instance instFintypeAddr : ∀ ms : List ℕ, Fintype (Addr ms)
  | [] => inferInstanceAs (Fintype Unit)
  | m :: ms =>
    letI := instFintypeAddr ms
    inferInstanceAs (Fintype (Bool × Bits m × Addr ms))

instance instDecidableEqAddr : ∀ ms : List ℕ, DecidableEq (Addr ms)
  | [] => inferInstanceAs (DecidableEq Unit)
  | m :: ms =>
    letI := instDecidableEqAddr ms
    inferInstanceAs (DecidableEq (Bool × Bits m × Addr ms))

/-- The address as a flat bit string (§4.1, p. 16; §5.1, p. 18: "`w0x` is the code child `x` and `w1y`
the data child `y` of the node with address `w`"). -/
def Addr.toStr : (ms : List ℕ) → Addr ms → Str
  | [], _ => []
  | _ :: ms, (b, x, a) => b :: (List.ofFn x ++ Addr.toStr ms a)

/-- The length of an address, `a(n) = ∑_i (m_i + 1)` (Eq. (4.3), p. 16). -/
def addrLen (ms : List ℕ) : ℕ := (ms.map fun m => m + 1).sum

end MantriCVQ


