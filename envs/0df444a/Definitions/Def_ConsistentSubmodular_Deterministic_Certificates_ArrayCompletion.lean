-- Prove2me | Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_ArrayCompletion
-- name    : ConsistentSubmodular_Deterministic_Certificates_ArrayCompletion
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:09:36.974725+00:00
-- url     : https://prove2.me/theorems/fb30c29a-3144-45c2-abe1-aca08c1b2fd6
-- title:
--   Triangular length arrays and their finite atomization into an atomic profile
-- statement:
--   Indices range over $\{0,\dots,m\}$.
--
--   - `TriangularArray m`: a real array $\ell_{i,j}$, $i,j\in\{0,\dots,m\}$, such that $\ell_{i,j}\ge0$; $\ell_{i,j}=0$ whenever $j<i$ (triangularity); $\sum_j\ell_{0,j}=1$ (normalization); and for all $i,t$ the tail sums are dominated, $\sum_{j\ge t}\ell_{i,j}\le\sum_{j\ge t}\ell_{t,j}$.
--   - `TriangularArray.coverage` $j$: for each column $j$, a chosen finite weighted nested coverage realization (`MaximumCoverage`) of the nonnegative vector $(\ell_{i,j})_i$. Such a realization consists of finitely many atoms $a$ with positive weights $w_a$ and nonempty label sets $\Lambda_a$ of indices of positive entry, closed upward in the sense that if $\ell_{i,j}\le\ell_{i',j}$ and $i\in\Lambda_a$ then $i'\in\Lambda_a$, and such that for every index set $I$, $\max_{i\in I}\ell_{i,j}=\sum_a w_a\,[\Lambda_a\cap I\ne\emptyset]$ (with the empty maximum equal to $0$). The choice is made by the existence theorem for such realizations.
--   - `TriangularArray.AtomIndex`: the type of pairs $(j,a)$ with $j$ a column and $a$ an atom of the realization of column $j$.
--   - `TriangularArray.atomEquiv`: a chosen bijection of this finite type with $\{0,\dots,N-1\}$, where $N$ is its cardinality.
--   - `TriangularArray.toAtomic`: the atomic profile with $N$ atoms in which the atom $(j,a)$ has pool $j$, label set $\Lambda_a$ and weight $w_a$ of column $j$. Triangularity of the array gives that every label $i\in\Lambda$ satisfies $i\le$ pool; for positive-weight atoms of pool $m$ the terminal label $m$ belongs to $\Lambda$ because the last column is maximal at the terminal index.
--
--   The file also proves that the tail sum at the last column equals the entry $\ell_{i,m}$ and that $\ell_{i,m}\le\ell_{m,m}$.
--
--   This construction turns the length array extracted from a compatible profile into the finite atomic profile on which the finite checkpoint theorem is applied in the proof of Theorem 7.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/ArrayCompletion.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_FiniteMaxCoverage
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_AtomicFacts

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

structure TriangularArray (m : ℕ) where
  length : Fin (m + 1) → Fin (m + 1) → ℝ
  nonnegative : ∀ i j, 0 ≤ length i j
  triangular : ∀ i j, j < i → length i j = 0
  initial : (∑ j, length 0 j) = 1
  dominated : ∀ i t,
    (∑ j, if t ≤ j then length i j else 0) ≤
      ∑ j, if t ≤ j then length t j else 0

namespace TriangularArray

variable {m : ℕ} (M : TriangularArray m)

def coverage (j : Fin (m + 1)) : MaximumCoverage (fun i => M.length i j) :=
  Classical.choice (exists_maximumCoverage (fun i => M.length i j) (fun i => M.nonnegative i j))

abbrev AtomIndex := (j : Fin (m + 1)) × Fin (M.coverage j).atomCount

def atomEquiv : M.AtomIndex ≃ Fin (Fintype.card M.AtomIndex) := Fintype.equivFin _

theorem tail_last (i : Fin (m + 1)) :
    (∑ j, if Fin.last m ≤ j then M.length i j else 0) = M.length i (Fin.last m) := by
  rw [Finset.sum_eq_single (Fin.last m)]
  · simp
  · intro j _ hj
    have hn : ¬Fin.last m ≤ j := by
      intro h
      exact hj (le_antisymm (Fin.le_last j) h)
    simp [hn]
  · simp

theorem terminal_maximum (i : Fin (m + 1)) :
    M.length i (Fin.last m) ≤ M.length (Fin.last m) (Fin.last m) := by
  have h := M.dominated i (Fin.last m)
  simpa only [M.tail_last] using h

def toAtomic : AtomicProfile m (Fintype.card M.AtomIndex) where
  pool a := (M.atomEquiv.symm a).1
  labels a := (M.coverage (M.atomEquiv.symm a).1).labels (M.atomEquiv.symm a).2
  weight a := (M.coverage (M.atomEquiv.symm a).1).weight (M.atomEquiv.symm a).2
  weight_nonnegative a := ((M.coverage _).weight_positive _).le
  labels_nonempty a := (M.coverage _).labels_nonempty _
  triangular a i hi := by
    have hp := (M.coverage _).labels_positive _ i hi
    by_contra h
    have hz := M.triangular i (M.atomEquiv.symm a).1 (lt_of_not_ge h)
    rw [hz] at hp
    exact (lt_irrefl 0) hp
  terminal a _ hpool := by
    obtain ⟨i, hi⟩ := (M.coverage (M.atomEquiv.symm a).1).labels_nonempty (M.atomEquiv.symm a).2
    apply (M.coverage (M.atomEquiv.symm a).1).labels_upward (M.atomEquiv.symm a).2 i (Fin.last m) ?_ hi
    rw [hpool]
    exact M.terminal_maximum i

end TriangularArray

end ConsistentSubmodular

end


