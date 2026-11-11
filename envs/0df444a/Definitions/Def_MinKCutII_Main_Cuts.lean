-- Prove2me | Definitions.Def_MinKCutII_Main_Cuts
-- name    : MinKCutII_Main_Cuts
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T03:38:50.262439+00:00
-- url     : https://prove2.me/theorems/18a6e59e-5674-4c47-b683-81ed197e28d8
-- title:
--   Cuts, rooted cuts, U-light/small/medium cuts (Definition 2), crossing cuts, Venn atoms (Definition 35), shores
-- statement:
--   A **cut** is a set $S$ with $\emptyset\ne S\subsetneq V$, identified with the bipartition $(S,V\setminus S)$. For a fixed root $r\in V$ the **rooted cut** is the side not containing $r$: a nonempty $S$ with $r\notin S$.
--
--   **Definition 2.** For an integer $k\ge 3$ and $U>0$, a cut $S$ is $U$-light if $c_G(S)\le 2U/k$, $U$-small if $c_G(S)\le U/(k-1)$, and $U$-medium if
--   $$\frac{U}{k-1}<c_G(S)\le\frac{2U}{k}.$$
--   Two cuts $A,S$ **cross** when all four regions $A\cap S$, $A\setminus S$, $S\setminus A$, $V\setminus(A\cup S)$ are nonempty.
--
--   **Definition 35.** For sets $S_0,\dots,S_{j-1}$, the Venn atoms $\mathrm{At}(S_0,\dots,S_{j-1})$ are the nonempty sets $\bigcap_i X_i$ with $X_i\in\{S_i,V\setminus S_i\}$, i.e. the classes of vertices with the same membership signature; $|\mathrm{At}|$ is the number of distinct signatures. A labelling is constant on atoms when its partition is a coarsening of the atom partition. The **shore** of a cut is its smaller side; its size is $\min(|S|,|V|-|S|)$.
--
--   **Formalization Note.** Families are sequences `S : ℕ → Finset V` of which the first `j` are used; $k$ is cast to $\mathbb R$ in $U/(k-1)$ and $2U/k$.
-- source:
--   Vaughn, Faster Minimum k-Cut II: Improved Randomized and Deterministic Algorithms for Weighted Graphs, arXiv:2609.27797 (version of November 1, 2026, sha256 b01b5a6f…), p. 6, §2 (Sets, cuts, and partitions; Definition 2); p. 25, Definition 35

import Mathlib
import Definitions.Def_MinKCutII_Main_KCut

set_option autoImplicit false

open CombOpt.MinCut

namespace MinKCutII.Main

/-!
# Cuts, rooted cuts, cut-value regimes (Definition 2), crossing, Venn atoms (Definition 35), shores

Vaughn, *Faster Minimum k-Cut II*, arXiv:2609.27797 (version of November 1, 2026, sha256
b01b5a6f…), §2 p. 6 (sets, cuts, Definition 2) and §4.1 p. 25 (Definition 35).

* A **cut** is a set `S` with `∅ ≠ S ⊊ V`, identified with the bipartition `(S, V \ S)`; a
  **rooted cut** for the root `r` is a nonempty `S` with `r ∉ S` (the rooted orientation of a cut,
  "the unique side not containing r").
* Definition 2 (p. 6), for an integer `k ≥ 3` and `U > 0`: `S` is `U`-light if
  `c_G(S) ≤ 2U/k`, `U`-small if `c_G(S) ≤ U/(k − 1)`, `U`-medium if
  `U/(k − 1) < c_G(S) ≤ 2U/k`. (`k` is cast to `ℝ`, so `k − 1` is real subtraction.)
* Two cuts `A, S` **cross** (as bipartitions) when all four sets `A ∩ S`, `A \ S`, `S \ A`,
  `V \ (A ∪ S)` are nonempty.
* Venn atoms (Definition 35): for cuts `S_0, …, S_{j−1}` (a sequence `S : ℕ → Finset V`, of which
  the first `j` are used), the atoms are the nonempty classes of the relation "same membership in
  every `S_i`, `i < j`"; `numAtoms S j = |At(S_0, …, S_{j−1})|` is the number of distinct
  membership signatures. A labelling is constant on atoms when vertices of one atom get one label
  (equivalently, the partition is a coarsening of the atom partition).
* The **shore** of a cut is its smaller side; only its size `min(|S|, |V| − |S|)` is used.
-/

/-- `S` is a cut: `∅ ≠ S ⊊ V`. -/
def IsCut {V : Type*} [Fintype V] (S : Finset V) : Prop :=
  S.Nonempty ∧ S ≠ Finset.univ

/-- `S` is a rooted cut for the root `r`: nonempty and not containing `r`. -/
def IsRootedCut {V : Type*} (r : V) (S : Finset V) : Prop :=
  S.Nonempty ∧ r ∉ S

/-- `U`-light (Definition 2): `c_G(S) ≤ 2U/k`. -/
def IsULight {V E : Type*} [Fintype E] (G : CapGraph V E) (k : ℕ) (U : ℝ) (S : Finset V) :
    Prop :=
  cutVal G S ≤ 2 * U / k

/-- `U`-small (Definition 2): `c_G(S) ≤ U/(k − 1)`. -/
def IsUSmall {V E : Type*} [Fintype E] (G : CapGraph V E) (k : ℕ) (U : ℝ) (S : Finset V) :
    Prop :=
  cutVal G S ≤ U / ((k : ℝ) - 1)

/-- `U`-medium (Definition 2): `U/(k − 1) < c_G(S) ≤ 2U/k`. -/
def IsUMedium {V E : Type*} [Fintype E] (G : CapGraph V E) (k : ℕ) (U : ℝ) (S : Finset V) :
    Prop :=
  U / ((k : ℝ) - 1) < cutVal G S ∧ cutVal G S ≤ 2 * U / k

/-- The cuts `(A, V \ A)` and `(S, V \ S)` cross: all four Venn regions are nonempty. -/
def CutsCross {V : Type*} [Fintype V] [DecidableEq V] (A S : Finset V) : Prop :=
  (A ∩ S).Nonempty ∧ (A \ S).Nonempty ∧ (S \ A).Nonempty ∧ (Finset.univ \ (A ∪ S)).Nonempty

/-- The membership signature of `v` with respect to `S_0, …, S_{j−1}`. -/
def signature {V : Type*} [DecidableEq V] (S : ℕ → Finset V) (j : ℕ) (v : V) : Fin j → Bool :=
  fun i => decide (v ∈ S i)

/-- `|At(S_0, …, S_{j−1})|`: the number of nonempty Venn atoms of the first `j` sets. -/
def numAtoms {V : Type*} [Fintype V] [DecidableEq V] (S : ℕ → Finset V) (j : ℕ) : ℕ :=
  (Finset.univ.image (signature S j)).card

/-- The labelling `f` is constant on every Venn atom of `S_0, …, S_{j−1}`: its partition is a
coarsening of the atom partition. -/
def AtomConstant {V : Type*} {k : ℕ} (S : ℕ → Finset V) (j : ℕ) (f : V → Fin k) : Prop :=
  ∀ x y : V, (∀ i : Fin j, (x ∈ S i ↔ y ∈ S i)) → f x = f y

/-- The size of the shore (the smaller side) of the cut `(S, V \ S)`. -/
def shoreSize {V : Type*} [Fintype V] (S : Finset V) : ℕ :=
  min S.card (Fintype.card V - S.card)

end MinKCutII.Main


