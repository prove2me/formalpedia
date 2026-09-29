-- Prove2me | Definitions.Def_HarelTarjan_Compressed_CompressedTree
-- name    : HarelTarjan_Compressed_CompressedTree
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T14:51:18.583047+00:00
-- url     : https://prove2.me/theorems/f04e406b-5c42-4885-b280-20674b8c7562
-- title:
--   The compressed tree $C$: parent $p_C(v) = \mathrm{apex}(p_T(v))$, sizes $\mathrm{size}_C(v)$ and ranks
-- statement:
--   The compressed tree of §4 of Harel and Tarjan (pp. 343–344).
--
--   Let $T$ be a rooted tree with root $r$. The **compressed tree** $C$ representing $T$ has the same vertices and root, and its edges are
--   $$\{\, v \to \mathrm{apex}(p_T(v)) \;:\; v \text{ a vertex of } T \text{ other than } r \,\}.$$
--   Write $p_C(v) = \mathrm{apex}(p_T(v))$ for the parent of $v \ne r$ in $C$. A vertex $w$ is an ancestor of $v$ in $C$ if $p_C^i(v) = w$ for some $i \ge 0$, and $\mathrm{size}_C(v)$ is the number of descendants of $v$ in $C$, including $v$.
--
--   The **rank** of a vertex is
--   $$\mathrm{rank}(v) = \lfloor \lg \mathrm{size}_C(v) \rfloor .$$
--
--   Ranks are what the plies of $C$ are cut by; the size doubling along the edges of $C$ is what makes them informative.
--
--   **Formalization Note** As for $T$, $p_C$ is made total by $p_C(r) = r$. The rank is `Nat.log 2 (size_C v)`, which equals $\lfloor \log_2 \mathrm{size}_C(v) \rfloor$ exactly because $\mathrm{size}_C(v) \ge 1$.
-- source:
--   Harel, Tarjan, Fast Algorithms for Finding Nearest Common Ancestors, SIAM J. Comput. 13 (1984), p. 343, §4 (compressed tree); p. 344 (size_C, rank)

import Mathlib
import Definitions.Def_HarelTarjan_Compressed_RootedTree
import Definitions.Def_HarelTarjan_Compressed_HeavyPath

namespace HarelTarjan.Compressed

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The parent map `p_C` of the compressed tree `C` (§4, p. 343), whose edges are
`{v → apex(p_T(v)) | v is a vertex of T other than r}`. The root `r` of `T` is the root of `C`;
as for `T`, the convention `p_C(r) = r` makes the map total. -/
noncomputable def pC (T : RootedTree V) (v : V) : V :=
  if v = T.root then T.root else apex T (T.parent v)

/-- `IsAncestorC T w v`: `p_Cⁱ(v) = w` for some `i ≥ 0`, i.e. `v` is a descendant of `w` in `C`. -/
def IsAncestorC (T : RootedTree V) (w v : V) : Prop := ∃ i : ℕ, (pC T)^[i] v = w

/-- `size_C(v)`: the number of descendants of `v` in `C`, including `v` itself (§4, p. 344). -/
noncomputable def sizeC (T : RootedTree V) (v : V) : ℕ := by
  classical
  exact (Finset.univ.filter (fun u => IsAncestorC T v u)).card

/-- `rank(v) = ⌊lg(size_C(v))⌋` (§4, p. 344). Since `size_C(v) ≥ 1`, `Nat.log 2 (size_C(v))` is
exactly the floor of the base-2 logarithm. -/
noncomputable def rank (T : RootedTree V) (v : V) : ℕ := Nat.log 2 (sizeC T v)

end HarelTarjan.Compressed


