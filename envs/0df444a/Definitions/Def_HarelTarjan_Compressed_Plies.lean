-- Prove2me | Definitions.Def_HarelTarjan_Compressed_Plies
-- name    : HarelTarjan_Compressed_Plies
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T14:52:20.547056+00:00
-- url     : https://prove2.me/theorems/9daa2789-cba6-44b3-a498-f3d7dd3d2113
-- title:
--   The three plies of the compressed tree, cut at ranks $\lfloor \lg^{(3)} n\rfloor$ and $\lfloor \lg^{(2)} n\rfloor$
-- statement:
--   The division of the compressed tree $C$ into three plies (§4, p. 344 of Harel and Tarjan).
--
--   Let $n$ be the number of vertices, and let $\lg^{(i)}$ be the $i$-fold iterate of $\lg = \log_2$ (footnote 3: $f^{(0)}(x) = x$, $f^{(i+1)}(x) = f(f^{(i)}(x))$).
--
--   1. **Ply three** consists of all vertices with rank $\lfloor \lg^{(2)} n \rfloor$ or greater.
--   2. **Ply two** consists of all vertices with rank between $\lfloor \lg^{(3)} n\rfloor$ and $\lfloor \lg^{(2)} n \rfloor - 1$ inclusive.
--   3. **Ply one** consists of all vertices with rank less than $\lfloor \lg^{(3)} n \rfloor$.
--
--   The plies are the three levels at which the depth problem on $C$ is solved by different representations.
--
--   **Formalization Note** The thresholds are computed with iterated natural-number logarithms, $\lfloor \lg^{(2)} n\rfloor$ as `Nat.log 2 (Nat.log 2 n)` and $\lfloor \lg^{(3)} n\rfloor$ as `Nat.log 2 (Nat.log 2 (Nat.log 2 n))`. Since $\lfloor \lg \lfloor y \rfloor \rfloor = \lfloor \lg y \rfloor$ for real $y \ge 1$, these equal the real floors for $n \ge 2$ and $n \ge 4$ respectively; for smaller $n$ the real iterated logarithm is undefined or negative and the paper does not use the plies. The page prints the upper end of ply two as "$\lfloor \lg^{(2)}\rfloor - 1$" without its argument; it is read as $\lfloor \lg^{(2)} n \rfloor - 1$, and ply two is encoded as $\lfloor\lg^{(3)} n\rfloor \le \mathrm{rank} < \lfloor\lg^{(2)} n\rfloor$ to avoid natural-number subtraction.
-- source:
--   Harel, Tarjan, Fast Algorithms for Finding Nearest Common Ancestors, SIAM J. Comput. 13 (1984), p. 344, §4 (the three plies) and footnote 3

import Mathlib
import Definitions.Def_HarelTarjan_Compressed_RootedTree
import Definitions.Def_HarelTarjan_Compressed_HeavyPath
import Definitions.Def_HarelTarjan_Compressed_CompressedTree

namespace HarelTarjan.Compressed

/-- The threshold `⌊lg⁽²⁾ n⌋ = ⌊lg lg n⌋`, computed as `Nat.log 2 (Nat.log 2 n)`. For `n ≥ 2` this
equals `⌊log₂ (log₂ n)⌋` with real logarithms, because `⌊lg ⌊y⌋⌋ = ⌊lg y⌋` for `y ≥ 1`. -/
def L2 (n : ℕ) : ℕ := Nat.log 2 (Nat.log 2 n)

/-- The threshold `⌊lg⁽³⁾ n⌋ = ⌊lg lg lg n⌋`, computed as `Nat.log 2 (Nat.log 2 (Nat.log 2 n))`.
For `n ≥ 4` this equals `⌊log₂ (log₂ (log₂ n))⌋` with real logarithms. -/
def L3 (n : ℕ) : ℕ := Nat.log 2 (Nat.log 2 (Nat.log 2 n))

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Ply three (§4, p. 344): the vertices of rank `⌊lg⁽²⁾ n⌋` or greater, where `n = |V|`. -/
noncomputable def ply3 (T : RootedTree V) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => L2 (Fintype.card V) ≤ rank T v)

/-- Ply two (§4, p. 344): the vertices with rank between `⌊lg⁽³⁾ n⌋` and `⌊lg⁽²⁾ n⌋ − 1`
inclusive, where `n = |V|`. -/
noncomputable def ply2 (T : RootedTree V) : Finset V := by
  classical
  exact Finset.univ.filter
    (fun v => L3 (Fintype.card V) ≤ rank T v ∧ rank T v < L2 (Fintype.card V))

/-- Ply one (§4, p. 344): the vertices of rank less than `⌊lg⁽³⁾ n⌋`, where `n = |V|`. -/
noncomputable def ply1 (T : RootedTree V) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => rank T v < L3 (Fintype.card V))

end HarelTarjan.Compressed


