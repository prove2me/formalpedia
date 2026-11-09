-- Prove2me | Definitions.Def_ChvatalOneHard398_SAT_Geometry
-- name    : ChvatalOneHard398_SAT_Geometry
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:38:01.797478+00:00
-- url     : https://prove2.me/theorems/e8233018-2b6d-4af1-b8d6-9d01fbade1b6
-- title:
--   Lattices, integer hulls, and the bounded distance decoding promise
-- statement:
--   For a real matrix $B$ with $n$ rows and columns, write $L(B)$ for the integer span of its columns in Euclidean space. A lattice basis is nonsingular. The distance and decoding factor are
--
--   $$\operatorname{dist}(t,L)=\inf_{v\in L}\|v-t\|_2,\qquad \alpha(n)=\frac1{4n^{5/2}}.$$
--
--   The raw decoding input consists of a dimension $n$, a rational square matrix $B$, and a rational vector $t$. Its promise requires $n>0$, nonsingularity, and distance at most $\alpha(n)\lambda_1(L(B))$. A correct output is the list of coordinates of a rational vector in $L(B)$ attaining this distance. The congruence lattice is the Euclidean image of $\{y\in\mathbb Z^m:D\mid(Hy)_i\text{ for all }i\}$.
--
--   Rank at most one means $P'=P_I$, using the published closure and hull. The hereditary version requires this identity for every rational subpolyhedron. Integral points and integral affine lifts are also defined here. These definitions supply the shared geometry of all twelve statements.
--
--   **Formalization Note** EuclideanSpace carries the Euclidean norm. Polyhedra remain sets of real coordinate functions. The infimum defining distance has a nonempty, nonnegative indexing set because every generated subgroup contains zero. The shortest-vector infimum is used only on full-rank, positive-dimensional promised lattices, or in the harmless zero-dimensional case of Lemma 23.
-- source:
--   Alberto Del Pia, 0/1 integer programming over polytopes of Chvátal rank one is as hard as lattice problems, STOC 2027 submission #398 (October 2026), p.8, §2, Lattices and Lattice problems (BDD continued on p.9); p.3, Chvátal closure; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/398.pdf

import Mathlib
import Definitions.Def_CombOpt_ChvatalRank_chvatalClosure
import Definitions.Def_CombOpt_ChvatalRank_integerHull
import Definitions.Def_CombOpt_ChvatalRank_IsRationalPolyhedron
import Definitions.Def_RegevLWE_SmoothingLB_Lattice
import Definitions.Def_RegevLWE_GaussConv_Lattice

namespace ChvatalOneHard398.SAT
open scoped BigOperators
open CombOpt.ChvatalRank

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

def rankOne {n : ℕ} (P : Set (Fin n → ℝ)) : Prop :=
  chvatalClosure P = integerHull P

def hereditaryRankOne {n : ℕ} (P : Set (Fin n → ℝ)) : Prop :=
  ∀ R : Set (Fin n → ℝ), IsRationalPolyhedron R → R ⊆ P → rankOne R

def integralPoints {n : ℕ} (P : Set (Fin n → ℝ)) :=
  {x : Fin n → ℝ // x ∈ P ∧ IsIntegralVector x}

/-- Column-generated lattice, without a rank assumption in the data. -/
noncomputable def lattice {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) : Submodule ℤ (E n) :=
  Submodule.span ℤ (Set.range fun j : Fin n =>
    (WithLp.toLp 2 (fun i : Fin n => B i j) : E n))

noncomputable def qLattice {n : ℕ} (B : Matrix (Fin n) (Fin n) ℚ) : Submodule ℤ (E n) :=
  lattice (fun i j => (B i j : ℝ))

noncomputable def zLattice {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) : Submodule ℤ (E n) :=
  lattice (fun i j => (B i j : ℝ))

noncomputable def qVec {n : ℕ} (t : Fin n → ℚ) : E n :=
  WithLp.toLp 2 (fun i => (t i : ℝ))

noncomputable def zVec {n : ℕ} (t : Fin n → ℤ) : E n :=
  WithLp.toLp 2 (fun i => (t i : ℝ))

noncomputable def latticeDist {n : ℕ} (L : Submodule ℤ (E n)) (t : E n) : ℝ :=
  sInf {r : ℝ | ∃ v ∈ L, ‖v - t‖ = r}

/-- The integer congruence kernel; its cast is used as a Euclidean lattice. -/
def congruenceKernel {m r : ℕ} (D : ℕ) (H : Matrix (Fin r) (Fin m) ℤ) :
    AddSubgroup (Fin m → ℤ) where
  carrier := {y | ∀ i, (D : ℤ) ∣ ∑ j, H i j * y j}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb i
    simpa [mul_add, Finset.sum_add_distrib] using dvd_add (ha i) (hb i)
  neg_mem' := by
    intro a ha i
    simpa using dvd_neg.mpr (ha i)

noncomputable def congruenceLattice {m r : ℕ} (D : ℕ)
    (H : Matrix (Fin r) (Fin m) ℤ) : Submodule ℤ (E m) :=
  Submodule.span ℤ (zVec '' (congruenceKernel D H : Set (Fin m → ℤ)))

noncomputable def affineLift {n k : ℕ} (A : Matrix (Fin k) (Fin n) ℤ)
    (b : Fin k → ℤ) (x : Fin n → ℝ) : Fin (n + k) → ℝ :=
  Fin.append x (fun i => (∑ j, (A i j : ℝ) * x j) + b i)

structure BDDInput where
  n : ℕ
  basis : Matrix (Fin n) (Fin n) ℚ
  target : Fin n → ℚ

noncomputable def bddFactor (n : ℕ) : ℝ := 1 / (4 * (n : ℝ) ^ (5 / 2 : ℝ))

noncomputable def BDDPromise (x : BDDInput) : Prop :=
  0 < x.n ∧ x.basis.det ≠ 0 ∧
  latticeDist (qLattice x.basis) (qVec x.target) ≤
    bddFactor x.n * RegevLWE.SmoothingLB.lambda1 (qLattice x.basis)

/-- A rational output with exactly the input dimension; no output is decoded by truncation. -/
noncomputable def BDDCorrect (x : BDDInput) (v : List ℚ) : Prop :=
  ∃ w : Fin x.n → ℚ, v = List.ofFn w ∧ qVec w ∈ qLattice x.basis ∧
    ‖qVec w - qVec x.target‖ = latticeDist (qLattice x.basis) (qVec x.target)

end ChvatalOneHard398.SAT


