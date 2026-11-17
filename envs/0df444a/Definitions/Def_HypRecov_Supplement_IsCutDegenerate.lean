-- Prove2me | Definitions.Def_HypRecov_Supplement_IsCutDegenerate
-- name    : HypRecov_Supplement_IsCutDegenerate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T03:22:53.51272+00:00
-- url     : https://prove2.me/theorems/6dd02033-50f1-47ef-9cef-224fbc18bed4
-- title:
--   $d$-cut-degenerate hypergraphs, complete observations, and sparse integer projections
-- statement:
--   For a simple hypergraph $H=(V,E)$ and $U\subseteq V$, the induced hypergraph $H[U]$ retains exactly the edges contained in $U$. The hypergraph is **$d$-cut-degenerate** if every $U$ with $|U|\ge2$ has a nonempty proper subset $S\subset U$ satisfying
--   $$\operatorname{cut}_{H[U]}(S)\le d.$$
--
--   This module also records the complete multiplicity-preserving $q$-observation, the projection $W_{q,r}z$ of a signed integer vector on the $r$-subsets, its support and magnitude promises, and exact determination predicates used by the supplement's upper and lower bounds.
--
--   **Formalization Note** Vertices are `Fin n`; simple hypergraphs and vertex subsets are `Finset`s. Integer vectors are total functions that are required to vanish away from the $r$-uniform slice.
-- source:
--   Zhang, Chen, Shen, Hypergraph Recovery from Anonymous Projection Streams, STOC 2027 submission (manuscript sha256 719dcfff4dc2eba2d8c5a3c51679a08cfb11f076546dea963c6376a2b9da2c82), Theorem 3.4, p.7 (PDF p.8); Section 8, p.20 (PDF p.21); Theorem 9.1, p.22 (PDF p.23)

import Mathlib
import Definitions.Def_HypRecov_crisp
import Definitions.Def_HypRecov_IsValidStream
import Definitions.Def_HypRecov_qid
import Definitions.Def_HypRecov_encNat

set_option autoImplicit false

namespace HypRecov.Supplement

open Classical

/-- A simple hypergraph is `r`-uniform.  Simplicity is built into the `Finset` representation. -/
def IsUniform {n : ℕ} (r : ℕ) (E : Finset (Finset (Fin n))) : Prop :=
  ∀ e ∈ E, e.card = r

/-- Two simple hypergraphs have the same complete multiplicity-preserving `q`-observation. -/
def SameObservation {n : ℕ} (q : ℕ) (E F : Finset (Finset (Fin n))) : Prop :=
  ∀ A : Finset (Fin n), A.card = q →
    (E.filter (fun e => A ⊆ e)).card = (F.filter (fun e => A ⊆ e)).card

/-- Observation order `q` determines the `k`-crisp edge family for every simple `r`-uniform
hypergraph on the fixed vertex set `Fin n`. -/
def DeterminesCrisp (n r k q : ℕ) : Prop :=
  ∀ E F : Finset (Finset (Fin n)), IsUniform r E → IsUniform r F →
    SameObservation q E F → HypRecov.crisp E k = HypRecov.crisp F k

/-- The induced hypergraph `H[U]`, retaining exactly the original edges contained in `U`. -/
def induced {n : ℕ} (E : Finset (Finset (Fin n))) (U : Finset (Fin n)) :
    Finset (Finset (Fin n)) :=
  E.filter (fun e => e ⊆ U)

/-- **`d`-cut-degeneracy.** Zhang, Chen, Shen, *Hypergraph Recovery from Anonymous Projection
Streams*, STOC 2027 submission (manuscript sha256 719dcfff…), §8, p.20 (PDF p.21): for every
`U ⊆ V` with at least two vertices there is a nonempty proper `S ⊂ U` whose boundary in the
induced hypergraph `H[U]` has size at most `d`.

**Formalization Note.** `S ⊂ U` is represented by `S ⊆ U`, `S.Nonempty`, and `S ≠ U`. -/
def IsCutDegenerate {n : ℕ} (E : Finset (Finset (Fin n))) (d : ℕ) : Prop :=
  ∀ U : Finset (Fin n), 2 ≤ U.card →
    ∃ S : Finset (Fin n), S.Nonempty ∧ S ⊆ U ∧ S ≠ U ∧ HypRecov.cut (induced E U) S ≤ d

/-- Observation order `q` determines the complete edge set throughout the class of simple
`r`-uniform `d`-cut-degenerate hypergraphs. -/
def DeterminesCutDegenerate (n r d q : ℕ) : Prop :=
  ∀ E F : Finset (Finset (Fin n)), IsUniform r E → IsUniform r F →
    IsCutDegenerate E d → IsCutDegenerate F d → SameObservation q E F → E = F

/-- The complete integer projection `W_{q,r} z` of an integer vector indexed by `r`-subsets. -/
def intProjection {n : ℕ} (r q : ℕ) (z : Finset (Fin n) → ℤ)
    (A : Finset (Fin n)) : ℤ :=
  ∑ e ∈ (Finset.univ.filter (fun e : Finset (Fin n) => e.card = r ∧ A ⊆ e)), z e

/-- The nonzero `r`-set coordinates of an integer vector. -/
def intSupport {n : ℕ} (r : ℕ) (z : Finset (Fin n) → ℤ) :
    Finset (Finset (Fin n)) :=
  Finset.univ.filter (fun e => e.card = r ∧ z e ≠ 0)

/-- An integer vector on the `r`-subsets is `K`-sparse and bounded in magnitude by `W`.
Coordinates away from the `r`-uniform slice are zero. -/
def IsSparseBounded {n : ℕ} (r K W : ℕ) (z : Finset (Fin n) → ℤ) : Prop :=
  (∀ e : Finset (Fin n), e.card ≠ r → z e = 0) ∧
    (intSupport r z).card ≤ K ∧ ∀ e : Finset (Fin n), z e ≤ W ∧ -z e ≤ W

/-- A stream whose terminal vector is the complete integer projection `W_{q,r}z`.  Prefix counts
and increments are unrestricted signed integers. -/
def IsValidVectorStream {n : ℕ} (r q : ℕ) (z : Finset (Fin n) → ℤ)
    (sigma : List (Finset (Fin n) × ℤ)) : Prop :=
  (∀ u ∈ sigma, u.1.card = q) ∧
    ∀ A : Finset (Fin n), A.card = q → HypRecov.net sigma A = intProjection r q z A

/-- The floor-logarithmic sparse-recovery order `min{r, 1 + floor(log₂ K)}`. -/
def sparseOrder (r K : ℕ) : ℕ := min r (1 + Nat.log 2 K)

/-- The extra 2-adic precision `max_{0 ≤ h ≤ q} nu₂((r-h choose q-h))`. -/
def projectionPrecision (r q : ℕ) : ℕ :=
  (Finset.range (q + 1)).sup (fun h => padicValNat 2 ((r - h).choose (q - h)))

/-- Observation order `q` determines every `K`-sparse integer vector on the `r`-uniform slice. -/
def DeterminesSparseInteger (n r K q : ℕ) : Prop :=
  ∀ z z' : Finset (Fin n) → ℤ,
    IsSparseBounded r K 1 z → IsSparseBounded r K 1 z' →
    (∀ e, z e = 0 ∨ z e = 1) → (∀ e, z' e = 0 ∨ z' e = 1) →
    (∀ A : Finset (Fin n), A.card = q → intProjection r q z A = intProjection r q z' A) →
    z = z'

/-- A duplicate-free binary encoding of an integer vector by its nonzero `r`-set coordinates and
their signed values. -/
noncomputable def encIntegerVector {n : ℕ} (r : ℕ) (z : Finset (Fin n) → ℤ) : List Bool :=
  ((List.ofFn fun i => (Fintype.equivFin (Finset (Fin n))).symm i).filter
      (fun e => e ∈ intSupport r z)).flatMap
      (fun e => true :: (HypRecov.encSet e ++ HypRecov.encInt (z e))) ++ [false]

end HypRecov.Supplement


