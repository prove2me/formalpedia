-- Prove2me | Definitions.Def_TriFormQ_affSubspaces
-- name    : TriFormQ_affSubspaces
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:45:57.134138+00:00
-- url     : https://prove2.me/theorems/3457d3da-be64-4659-9e73-82c76c9d0483
-- title:
--   The set of $d$-dimensional affine subspaces of $\mathbb F_q^n$
-- statement:
--   For a finite field $\mathbb F_q$ and integers $n,d$, let $\mathcal H_d$ be the finite set of affine subspaces $H\subseteq\mathbb F_q^n$ that are nonempty and whose direction has dimension exactly $d$. A **uniformly random affine $d$-dimensional subspace** is a uniform element of $\mathcal H_d$.
--
--   This is the sample space of Lemmas 6 and 10.
--
--   **Formalization Note** Uniform over subspaces of dimension exactly $d$. The construction $v_0+\mathrm{span}\{v_1,\dots,v_d\}$ from $d+1$ uniform vectors (§5.2.1) can produce a subspace of smaller dimension and is not the distribution Lemma 6 is about. The module also records the structural instance that there are finitely many affine subspaces.
-- source:
--   Grigorescu–Juba–Wimmer–Xie, Optimal Quantum Query Bounds for Identifying Classes of 3-Tensors, STOC 2027 submission (manuscript sha256 c56b0365…), Lemma 6, p.23 (PDF p.26); Lemma 10, p.27 (PDF p.30)

import Definitions.Def_TriFormQ_TriForm

namespace TriFormQ

/-- There are finitely many affine subspaces of the finite space `𝔽ⁿ` (structural instance for
`affSubspaces`). -/
instance finite_affineSubspace {F : Type} [Field F] [Fintype F] {n : ℕ} :
    Finite (AffineSubspace F (Vec F n)) :=
  Finite.of_injective (fun H : AffineSubspace F (Vec F n) => (H : Set (Vec F n)))
    SetLike.coe_injective

/-- Grigorescu–Juba–Wimmer–Xie, *Optimal Quantum Query Bounds for Identifying Classes of
3-Tensors*, STOC 2027 submission (manuscript sha256 c56b0365…), Lemma 6, p.23 (PDF p.26) and
Lemma 10, p.27 (PDF p.30): the sample space of "a uniformly random affine d-dimensional subspace
of 𝔽_q^n", the finite set of nonempty affine subspaces whose direction has dimension `d`.

**Formalization Note.** A random affine `d`-dimensional subspace is uniform on this Finset; the
paper's construction `v₀ + span{v₁, …, v_d}` from `d + 1` uniform vectors (§5.2.1, p.23) can have
dimension below `d`, which is not the subspace Lemma 6 and Lemma 10 are about. -/
noncomputable def affSubspaces (F : Type) [Field F] [Fintype F] (n d : ℕ) :
    Finset (AffineSubspace F (Vec F n)) :=
  (Set.toFinite {H : AffineSubspace F (Vec F n) |
    (H : Set (Vec F n)).Nonempty ∧ Module.finrank F H.direction = d}).toFinset

end TriFormQ


