-- Prove2me | Definitions.Def_ToricMemory_TorusSAP
-- name    : ToricMemory_TorusSAP
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:21:41.575764+00:00
-- url     : https://prove2.me/theorems/4c115b85-9434-4b8b-94b4-6babc24eae78
-- title:
--   Rooted self-avoiding polygons on the spacetime torus and $n_{\rm SAP}(H,V)$
-- statement:
--   A **rooted self-avoiding polygon** of length $n\ge1$ on the spacetime torus, starting at the site $s$, is a closed walk through $n$ oriented links $\ell_0,\dots,\ell_{n-1}$ that
--
--   1. starts at $s$ and returns to $s$, consecutive links meeting,
--   2. uses $n$ pairwise distinct links, and
--   3. visits $n$ pairwise distinct sites (all but the return to $s$).
--
--   Its link set is a cycle. $n_{\rm SAP}(H,V)$ is the number of such polygons starting at $s$ with $H$ horizontal and $V$ vertical links, each orientation counted separately.
--
--   These counts are the combinatorial input of the union bound (54)–(55).
--
--   **Formalization Note** A walk is a list of (link, orientation) pairs, which is unambiguous even where two links join the same pair of sites. On a small torus ($L\le2$ or $T\le2$) the count includes self-loops ($n=1$) and closed walks over two parallel links ($n=2$).
-- source:
--   Dennis, Kitaev, Landahl & Preskill, Topological quantum memory, arXiv:quant-ph/0110143v1, Sec. V B, p. 19 ("If n_SAP(H, V) denotes the number of SAP's with (H, V) links and a specified starting site")

import Mathlib
import Definitions.Def_ToricMemory_Lattice

open Finset

namespace ToricMemory

/-- The site where an oriented link `(ℓ, b)` is entered: `src ℓ` if `b` (traversed forward),
`tgt ℓ` otherwise. -/
def stepStart {L T : ℕ} (x : Link L T × Bool) : Site L T := if x.2 then src x.1 else tgt x.1

/-- The site where an oriented link `(ℓ, b)` is left: `tgt ℓ` if `b`, `src ℓ` otherwise. -/
def stepEnd {L T : ℕ} (x : Link L T × Bool) : Site L T := if x.2 then tgt x.1 else src x.1

/-- `w` is a rooted **self-avoiding polygon** (closed self-avoiding walk) of length `n` on the
spacetime torus, starting and ending at the site `s` (arXiv:quant-ph/0110143v1, Sec. V B,
p. 19): a closed walk through the oriented links `w 0, …, w (n−1)` that starts at `s`, in which
consecutive links meet, which returns to `s`, uses `n ≥ 1` pairwise distinct links, and visits
pairwise distinct sites except for the return to `s`.

**Formalization Note** On a small torus (`L ≤ 2` or `T ≤ 2`) this includes self-loops
(`n = 1`) and closed walks over two parallel links (`n = 2`). -/
def IsTorusSAP {L T : ℕ} (s : Site L T) {n : ℕ} (w : Fin n → Link L T × Bool) : Prop :=
  1 ≤ n ∧
  (∀ i : Fin n, i.val = 0 → stepStart (w i) = s) ∧
  (∀ i j : Fin n, j.val = i.val + 1 → stepEnd (w i) = stepStart (w j)) ∧
  (∀ i : Fin n, i.val + 1 = n → stepEnd (w i) = s) ∧
  Function.Injective (fun i => (w i).1) ∧
  Function.Injective (fun i => stepStart (w i))

/-- The set of links of a walk. -/
def linkSet {L T : ℕ} {n : ℕ} (w : Fin n → Link L T × Bool) : Finset (Link L T) :=
  Finset.univ.image fun i => (w i).1

open Classical in
/-- `n_SAP(H, V)` with starting site `s` (arXiv:quant-ph/0110143v1, Sec. V B, p. 19): the
number of rooted self-avoiding polygons on the spacetime torus starting at `s` with `H`
horizontal and `V` vertical links, each orientation counted separately. -/
noncomputable def sapTorus (L T : ℕ) [NeZero L] [NeZero T] (s : Site L T) (H V : ℕ) : ℕ :=
  (Finset.univ.filter fun w : Fin (H + V) → Link L T × Bool =>
    IsTorusSAP s w ∧ (Finset.univ.filter fun i => IsHorizontal (w i).1).card = H).card

end ToricMemory


