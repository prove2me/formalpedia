-- Prove2me | Definitions.Def_RWCuckoo_Threshold_Expansion
-- name    : RWCuckoo_Threshold_Expansion
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T17:32:07.899802+00:00
-- url     : https://prove2.me/theorems/b1de345d-ab59-4563-8423-1d7d38b0299d
-- title:
--   Neighbourhoods N(A), paths to a set, U_t, structured sets, and the groups S^(j)_0 with their weights and retained groups (§6.1, §6.3, §7)
-- statement:
--   Fix hashes and a matching $M$ of the first $m$ keys. For a set $A$ of cells (§6.1, p. 22)
--   $$N(A)=\{M(x): x\in[m],\ h_i(x)\in A\text{ for some }i\in[d]\},$$
--   the occupied cells whose keys have a hash in $A$; $N^i$ is $N$ applied $i$ times, $N^0(A)=A$. A **path of length $\ell$** from $v_0$ to $A$ is a sequence of cells $v_0,\dots,v_\ell$ with $v_\ell\in A$ such that for $j<\ell$ the cell $v_j$ is occupied and its key has a hash at $v_{j+1}$.
--
--   **§7 (p. 30).** With $S_0=E$ the empty cells and $S_i=N(S_{i-1})$, $U_t=M([m])\setminus S_t$ is the set of occupied cells with no path of length at most $t$ to $E$.
--
--   **§6.3 (p. 24).** A set $S$ is **structured with root set $R$** if $S=R\cup N^t(R)$ for some $t\ge0$.
--
--   **Groups (§6.1, p. 23).** For a set $F$ of fresh probes, let $f(x)$ be the number of fresh probes of key $x$. Group $j\ge0$ is the set $S^{(j)}_0$ of cells $M(x)$ of keys with $2^j\le f(x)\le 2^{j+1}-1$; its weight is $2^j|S^{(j)}_0|$; $L$ is the number of nonempty groups, and a group is **retained** if its weight is at least a $1/(2L)$ fraction of the total weight.
--
--   **Formalization Note** Sets of cells are `Finset (Fin n)`. A path of length $\ell$ is a function `Fin (ℓ + 1) → Fin n`. Groups $j>d$ are empty (a key has at most $d$ fresh probes), so the total weight and $L$ are computed over $j\le d$. A retained group is required to be nonempty; this only excludes the degenerate case of total weight $0$, where the paper's ratio is undefined.
-- source:
--   Hu, Kuszmaul, Liang, Random-Walk Cuckoo Hashing is Efficient up to the Critical Load Threshold, STOC 2027 submission (manuscript sha256 1fcebf33…), pp. 22–24 (§6.1, §6.3), p. 30 (§7)

import Mathlib
import Definitions.Def_RWCuckoo_Threshold_FrozenWalk

namespace RWCuckoo.Threshold

variable {m d n : ℕ} {h : Hashes m d n}

open Classical in
/-- The neighbourhood `N(A) = {M(x) : x ∈ [m], h_i(x) ∈ A for some i ∈ [d]}` (§6.1, p. 22): the
occupied cells whose keys have a hash in `A`. -/
noncomputable def Matching.nbhd (M : Matching h) (A : Finset (Fin n)) : Finset (Fin n) :=
  (Finset.univ.filter fun x => ∃ i, h x i ∈ A).image M.cell

/-- `N^i(A)`, `N` applied `i` times, with `N^0(A) = A`. -/
noncomputable def Matching.nbhdIter (M : Matching h) (i : ℕ) (A : Finset (Fin n)) :
    Finset (Fin n) :=
  M.nbhd^[i] A

/-- A path of length `ℓ` from `p 0` to the set `A` (§6.1, p. 22): a sequence of cells
`p 0, …, p ℓ` with `p ℓ ∈ A` such that for `j < ℓ` the cell `p j` is occupied and its key has a
hash at `p (j + 1)`. -/
def Matching.IsPathTo (M : Matching h) {ℓ : ℕ} (p : Fin (ℓ + 1) → Fin n) (A : Finset (Fin n)) :
    Prop :=
  p (Fin.last ℓ) ∈ A ∧ ∀ j : Fin ℓ, ∃ x i, M.cell x = p j.castSucc ∧ h x i = p j.succ

/-- `U_t = M([m]) \ S_t` (§7, p. 30), with `S_0 = E` and `S_i = N(S_{i−1})`: the occupied cells
with no path of length at most `t` to the empty cells. -/
noncomputable def Matching.farCells (M : Matching h) (t : ℕ) : Finset (Fin n) :=
  M.occupied \ M.nbhdIter t M.empty

/-- A structured set with root set `R` (§6.3, p. 24): `S = R ∪ N^t(R)` for some `t ≥ 0`. -/
def Matching.IsStructured (M : Matching h) (S R : Finset (Fin n)) : Prop :=
  ∃ t : ℕ, S = R ∪ M.nbhdIter t R

open Classical in
/-- The number of fresh probes of key `x`: `|{i : (x, i) ∈ F}|`. -/
noncomputable def freshCount (F : Finset (Fin m × Fin d)) (x : Fin m) : ℕ :=
  (Finset.univ.filter fun i : Fin d => (x, i) ∈ F).card

open Classical in
/-- Group `j` (§6.1, p. 23): `S^(j)_0`, the cells whose keys have between `2^j` and `2^{j+1} − 1`
fresh probes. -/
noncomputable def groupCells (M : Matching h) (F : Finset (Fin m × Fin d)) (j : ℕ) :
    Finset (Fin n) :=
  (Finset.univ.filter fun x => 2 ^ j ≤ freshCount F x ∧ freshCount F x < 2 ^ (j + 1)).image M.cell

/-- The weight `2^j |S^(j)_0|` of group `j`. -/
noncomputable def groupWeight (M : Matching h) (F : Finset (Fin m × Fin d)) (j : ℕ) : ℕ :=
  2 ^ j * (groupCells M F j).card

/-- The total weight of all groups (groups `j > d` are empty since a key has at most `d` fresh
probes). -/
noncomputable def totalWeight (M : Matching h) (F : Finset (Fin m × Fin d)) : ℕ :=
  ∑ j ∈ Finset.range (d + 1), groupWeight M F j

open Classical in
/-- `L`, the number of nonempty groups. -/
noncomputable def numGroups (M : Matching h) (F : Finset (Fin m × Fin d)) : ℕ :=
  ((Finset.range (d + 1)).filter fun j => (groupCells M F j).Nonempty).card

/-- A retained group (§6.1, p. 23): a nonempty group whose weight is at least a `1/(2L)` fraction
of the total weight. -/
def IsRetained (M : Matching h) (F : Finset (Fin m × Fin d)) (j : ℕ) : Prop :=
  (groupCells M F j).Nonempty ∧
    (totalWeight M F : ℝ) ≤ 2 * (numGroups M F : ℝ) * (groupWeight M F j : ℝ)

end RWCuckoo.Threshold


