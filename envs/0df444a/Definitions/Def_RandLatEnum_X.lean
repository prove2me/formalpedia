-- Prove2me | Definitions.Def_RandLatEnum_X
-- name    : RandLatEnum_X
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:12:40.905871+00:00
-- url     : https://prove2.me/theorems/406853fd-9dad-4a8c-91c9-b3d36f455254
-- title:
--   The space $X_n=\mathrm{SL}_n(\mathbb R)/\mathrm{SL}_n(\mathbb Z)$ of unimodular lattices
-- statement:
--   The **space of unimodular lattices** is the quotient
--   $$
--   X_n=\mathrm{SL}_n(\mathbb R)/\mathrm{SL}_n(\mathbb Z)
--   $$
--   of the group of real $n\times n$ matrices of determinant one by the subgroup of integer matrices of determinant one. A coset $B\,\mathrm{SL}_n(\mathbb Z)$ is identified with the lattice $B\mathbb Z^n$ spanned by the columns of $B$: right multiplication by an integral unimodular matrix is a change of column basis and does not change the lattice. $X_n$ carries the quotient topology, the Borel $\sigma$-algebra of that topology, and the left action $g\cdot B\,\mathrm{SL}_n(\mathbb Z)=gB\,\mathrm{SL}_n(\mathbb Z)$ of $\mathrm{SL}_n(\mathbb R)$, which moves the lattice by the linear map $g$.
--
--   This is the probability space of the whole mission: a Haar-random lattice is a random point of $X_n$.
--
--   **Formalization Note** $\mathrm{SL}_n(\mathbb Z)$ is the image of the ring map $\mathbb Z\to\mathbb R$ on special linear groups; $X_n$ is the type of left cosets, with the quotient of the subspace topology of $\mathrm{SL}_n(\mathbb R)$ inside the matrices, its Borel $\sigma$-algebra and Mathlib's action on left cosets.
-- source:
--   Laarhoven, Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices, arXiv:2610.15265 (held version, sha256 8fa7a08a…), §2.1, p.14

import Mathlib

namespace RandLatEnum

open MeasureTheory

/-- The space `X_n = SL_n(ℝ)/SL_n(ℤ)` of unimodular lattices in `ℝⁿ` (Laarhoven, *Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices*, arXiv:2610.15265 (held version, sha256 8fa7a08a…), §2.1, p.14:
"The quotient Xn = SLn(R)/SLn(Z) is the space of unimodular lattices").

**Formalization Note.** `SL_n(ℤ)` enters as the image of the ring map `ℤ → ℝ` on special linear
groups, and `X n` is the type of left cosets `g · SL_n(ℤ)`. A coset is identified with the lattice
spanned by the columns of any representative (`latticeOf`); right multiplication by `SL_n(ℤ)` is a
change of column basis. `X n` carries the quotient topology of the subspace topology of
`SL_n(ℝ) ⊆ Matrix`, the **Borel** σ-algebra of that topology, and the left action of `SL_n(ℝ)`. -/
def X (n : ℕ) : Type :=
  Matrix.SpecialLinearGroup (Fin n) ℝ ⧸
    (Matrix.SpecialLinearGroup.map (n := Fin n) (Int.castRingHom ℝ)).range

/-- The quotient topology on `X n`. -/
instance (n : ℕ) : TopologicalSpace (X n) := inferInstanceAs (TopologicalSpace (_ ⧸ _))

/-- The left action of `SL_n(ℝ)` on `X n` by `g • (h · SL_n(ℤ)) = (g h) · SL_n(ℤ)`. -/
instance (n : ℕ) : MulAction (Matrix.SpecialLinearGroup (Fin n) ℝ) (X n) :=
  inferInstanceAs (MulAction _ (_ ⧸ _))

/-- The Borel σ-algebra of the quotient topology. -/
instance (n : ℕ) : MeasurableSpace (X n) := borel (X n)

instance (n : ℕ) : BorelSpace (X n) := ⟨rfl⟩

end RandLatEnum


