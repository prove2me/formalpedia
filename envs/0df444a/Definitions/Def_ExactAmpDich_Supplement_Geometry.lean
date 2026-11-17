-- Prove2me | Definitions.Def_ExactAmpDich_Supplement_Geometry
-- name    : ExactAmpDich_Supplement_Geometry
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:21:43.713773+00:00
-- url     : https://prove2.me/theorems/dae4edf9-08d2-4358-945a-5481fac12cce
-- title:
--   The product group $\mathcal U=\prod_j U(2^{k_j})$, the families $\mathcal M,\mathcal P,\mathcal D,\mathcal E$, semialgebraic dimension and normalized Haar measure
-- statement:
--   Fix $m$ gates on $k_1,\dots,k_m\ge1$ qubits and let $\mathcal U=\prod_{j=1}^m U(2^{k_j})$ be the group of gate tuples, with the product of the matrix topologies and the Borel $\sigma$-algebra. A tuple gives the library $(G_1,\dots,G_m)$.
--
--   1. $\mathcal M$: tuples of monomial gates; $\mathcal P$: tuples of product-preserving gates; $\mathcal D$: tuples admitting a common diagonal Clifford frame with any complex phase; $\mathcal E=\mathcal M\cup\mathcal P\cup\mathcal D$.
--   2. A tuple is identified with the point of $\mathbb R^{2\sum_j4^{k_j}}$ listing the real and imaginary parts of all entries. The **real semialgebraic dimension** of $S\subseteq\mathbb R^N$ is the largest $d$ such that some linear map $\mathbb R^N\to\mathbb R^d$ sends $S$ onto a set with nonempty interior.
--   3. A measure on $\mathcal U$ is a **normalized Haar measure** if it is a left-invariant Borel probability measure.
--
--   **Formalization Note** For semialgebraic sets the projection characterization agrees with the usual dimension (Bochnak–Coste–Roy, *Real Algebraic Geometry*, §2.8). On a compact group the normalized Haar measure is unique, so a statement about every such measure is a statement about it.
-- source:
--   Liu–Meng, A Dichotomy for Exact Quantum Circuit Amplitudes, STOC 2027 submission (held manuscript, sha256 40ad9c68…), App. J.1, p.73 (PDF p.74)

import Mathlib
import Definitions.Def_ExactAmpDich_QTract

set_option autoImplicit false

namespace ExactAmpDich.Supplement

open QAlgorithms

/-- The ambient group `U = ∏_{j=1}^m U(2^{k_j})` of gate tuples with prescribed sizes. Liu–Meng,
*A Dichotomy for Exact Quantum Circuit Amplitudes*, STOC 2027 submission (held manuscript, sha256
40ad9c68…), App. J.1, p.73 (PDF p.74): "Fix the numbers of qubits k1, . . . , km ≥ 1 on which the
m ≥ 1 gates act, and put U = ∏ U(2^{kj})". It carries the product of the subspace topologies and
the product group structure. -/
abbrev UT {m : ℕ} (k : Fin m → ℕ) : Type := (j : Fin m) → Matrix.unitaryGroup (Qubits (k j)) ℂ

/-- Borel σ-algebra on `U`. -/
noncomputable instance instMeasurableSpaceUT {m : ℕ} (k : Fin m → ℕ) : MeasurableSpace (UT k) := borel _

instance instBorelSpaceUT {m : ℕ} (k : Fin m → ℕ) : BorelSpace (UT k) := ⟨rfl⟩

/-- `μ` is the **normalized Haar measure** on the compact group `U`: a left-invariant Borel
probability measure (unique on a compact group). Liu–Meng, App. J.1, p.73: "normalized Haar
measure on the ambient product group U". -/
def IsNormalizedHaar {m : ℕ} {k : Fin m → ℕ} (μ : MeasureTheory.Measure (UT k)) : Prop :=
  MeasureTheory.IsProbabilityMeasure μ ∧ μ.IsMulLeftInvariant

/-- The library with gates `G₁, …, G_m`. -/
def tupleLib {m : ℕ} (k : Fin m → ℕ) (hk : ∀ j, 1 ≤ k j) (G : UT k) : Library where
  t := m
  k := k
  one_le_k := hk
  U j := (G j : Matrix (Qubits (k j)) (Qubits (k j)) ℂ)

/-- `M`: the all-monomial tuples. Liu–Meng, App. J.1, p.73. -/
def setM {m : ℕ} (k : Fin m → ℕ) : Set (UT k) :=
  {G | ∀ j, IsMonomial (G j : Matrix (Qubits (k j)) (Qubits (k j)) ℂ)}

/-- `P`: the all-product-preserving tuples. -/
def setP {m : ℕ} (k : Fin m → ℕ) : Set (UT k) :=
  {G | ∀ j, PreservesProduct (G j : Matrix (Qubits (k j)) (Qubits (k j)) ℂ)}

/-- `D`: the tuples admitting a common diagonal Clifford frame, allowing arbitrary phases
(the complex-phase `DC`). -/
def setD {m : ℕ} (k : Fin m → ℕ) (hk : ∀ j, 1 ≤ k j) : Set (UT k) := {G | DC (tupleLib k hk G)}

/-- `E = M ∪ P ∪ D`. Liu–Meng, App. J.1, p.73: "set E = M ∪ P ∪ D. Its points are the three
structural families of Theorem 1.1." -/
def setE {m : ℕ} (k : Fin m → ℕ) (hk : ∀ j, 1 ≤ k j) : Set (UT k) := setM k ∪ setP k ∪ setD k hk

/-- The real coordinates of a gate tuple: the real and imaginary parts of all entries, embedding
`U` in `ℝ^{2 Σ_j 4^{k_j}}`. -/
noncomputable def realize {m : ℕ} (k : Fin m → ℕ) (G : UT k) :
    (Σ j : Fin m, Qubits (k j) × Qubits (k j) × Bool) → ℝ
  | ⟨j, y, x, b⟩ => if b then ((G j : Matrix (Qubits (k j)) (Qubits (k j)) ℂ) y x).im
      else ((G j : Matrix (Qubits (k j)) (Qubits (k j)) ℂ) y x).re

/-- **Real semialgebraic dimension** of a set `S ⊆ ℝ^ι`: the largest `d` such that some linear map
`ℝ^ι → ℝ^d` sends `S` onto a set with nonempty interior. Liu–Meng, App. J.1, p.73: "We use real
semialgebraic dimension for these sets".

**Formalization Note.** For a semialgebraic set this is its dimension (Bochnak–Coste–Roy, *Real
Algebraic Geometry*, §2.8: a cylindrical decomposition exhibits a cell of top dimension `d` as a
graph over an open subset of `d` coordinates, and linear images do not raise dimension). The sets
`M, P, D` of Theorem J.1 are semialgebraic. The empty set gets `0`. -/
noncomputable def saDim {ι : Type} [Fintype ι] (S : Set (ι → ℝ)) : ℕ :=
  sSup {d | ∃ f : (ι → ℝ) →ₗ[ℝ] (Fin d → ℝ), (interior (f '' S)).Nonempty}

end ExactAmpDich.Supplement


