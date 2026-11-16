-- Prove2me | Definitions.Def_ParallelMatroidBasis_Main_Supplement_Classes
-- name    : ParallelMatroidBasis_Main_Supplement_Classes
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:00:16.610701+00:00
-- url     : https://prove2.me/theorems/479913ad-201b-437b-a596-e6f8070a9f9e
-- title:
--   Linear matroids (§1) and partition matroids (Definition C.1)
-- statement:
--   Let $M$ be a matroid whose ground set is $[n]=\{1,\dots,n\}$.
--
--   1. $M$ is **linear** if there are a field $\mathbb F$, an integer $k$ and vectors $v_1,\dots,v_n\in\mathbb F^k$ such that a set $S\subseteq[n]$ is independent in $M$ if and only if the family $(v_i)_{i\in S}$ is linearly independent over $\mathbb F$ (PDF p.4). A repeated vector is a dependent pair.
--   2. $M$ is a **partition matroid** (Definition C.1, PDF p.38) if $[n]$ is partitioned into pairwise disjoint parts $A_1,\dots,A_m$ with integer budgets $0\le b_i\le|A_i|$, and
--   $$S\in\mathcal I\iff |S\cap A_i|\le b_i\ \text{ for every } i\in[m].$$
--
--   Linear matroids are the class for which Theorem 1.3 gives a deterministic algorithm and Claim D.1 counts; partition matroids are the class of Theorem C.7, which contains the lower-bound instances of Karp, Upfal and Wigderson.
--
--   **Formalization Note** Linearity reuses the published `RandDelMatroid.Indep.IsRepresentableOver` (columns $v : [n]\to\mathbb F^k$, independence $\Leftrightarrow$ `LinearIndepOn`) with an existential field `F : Type`; finite fields are included and no finiteness is required. The partition-matroid predicate includes ground set $[n]$ and allows empty parts (whose budget is then $0$), which impose no constraint and do not change the class.
-- source:
--   Aaron Putterman, Sanjeev Khanna, Junkai Song, STOC 2027 submission #589 (October 2026), A Near-Optimal Parallel Algorithm for Finding Matroid Bases, PDF sha256 71ee2ac010ac681077fc3191139efe918fa4a9b8c6dad648fac2ec33016764d6, linear matroids: §1, p.2 (PDF p.4); partition matroids: Definition C.1, p.36 (PDF p.38)

import Mathlib
import Definitions.Def_RandDelMatroid_Indep_Regular

noncomputable section
open Classical

namespace ParallelMatroidBasis.Main.Supplement

/-! # Linear matroids and partition matroids
(Putterman–Khanna–Song, STOC 2027 submission #589: linear matroids, §1, PDF p.4 (printed p.2);
partition matroids, Definition C.1, PDF p.38 (printed p.36)) -/

/-- A matroid on `Fin n` is **linear** if there is a field `F` and vectors `v₁, …, vₙ` in some
`F^k` such that a set `S` of elements is independent exactly when the vectors `vᵢ, i ∈ S` are
linearly independent (as a family, so a repeated vector is dependent). The field is arbitrary;
finite fields are included. -/
def IsLinearMatroid {n : ℕ} (M : Matroid (Fin n)) : Prop :=
  ∃ (F : Type) (_ : Field F), RandDelMatroid.Indep.IsRepresentableOver M F

/-- Definition C.1. A matroid `M` with ground set `Fin n` is a **partition matroid** if the ground
set is partitioned into pairwise disjoint parts `A₁, …, A_m` with budgets `0 ≤ bᵢ ≤ |Aᵢ|`, and a set
`S` is independent iff `|S ∩ Aᵢ| ≤ bᵢ` for every `i`. (Empty parts, necessarily with budget `0`,
are allowed; they impose no constraint.) -/
def IsPartitionMatroid {n : ℕ} (M : Matroid (Fin n)) : Prop :=
  M.E = Set.univ ∧
    ∃ (m : ℕ) (A : Fin m → Finset (Fin n)) (b : Fin m → ℕ),
      (∀ i j, i ≠ j → Disjoint (A i) (A j)) ∧
      (∀ x : Fin n, ∃ i, x ∈ A i) ∧
      (∀ i, b i ≤ (A i).card) ∧
      ∀ S : Finset (Fin n), M.Indep (↑S : Set (Fin n)) ↔ ∀ i, (S ∩ A i).card ≤ b i

end ParallelMatroidBasis.Main.Supplement


