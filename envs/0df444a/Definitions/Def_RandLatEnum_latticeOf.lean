-- Prove2me | Definitions.Def_RandLatEnum_latticeOf
-- name    : RandLatEnum_latticeOf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:13:44.392757+00:00
-- url     : https://prove2.me/theorems/7d6e5ddc-ed24-4bb8-ac07-7588ab71083c
-- title:
--   The lattice $L=B\mathbb Z^n$ of a point of $X_n$
-- statement:
--   For a point $x=B\,\mathrm{SL}_n(\mathbb Z)$ of $X_n$ with representative $B\in\mathrm{SL}_n(\mathbb R)$, the associated **unimodular lattice** is
--   $$
--   L=B\mathbb Z^n=\{Bz : z\in\mathbb Z^n\}\subset\mathbb R^n,
--   $$
--   the set of integer combinations of the columns $b_1,\dots,b_n$ of $B$. It has covolume $\det L=|\det B|=1$.
--
--   Every lattice quantity of the mission (minimum, bases, enumeration trees, sublattices, Gaussian mass) is read off this lattice.
--
--   **Formalization Note** The representative is chosen with `Quotient.out`; two representatives differ by a right factor in $\mathrm{SL}_n(\mathbb Z)$ and span the same lattice, so nothing depends on the choice. The lattice is the published `KannanLattice.Core.lattice` ($\mathbb Z$-span) of the columns, as a $\mathbb Z$-submodule of $\mathbb R^n$.
-- source:
--   Laarhoven, Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices, arXiv:2610.15265 (held version, sha256 8fa7a08a…), §2.1, p.14

import Mathlib
import Definitions.Def_KannanLattice_Core_Lattice
import Definitions.Def_RandLatEnum_X

namespace RandLatEnum

/-- The unimodular lattice `L = Bℤⁿ ⊂ ℝⁿ` of a point of `X_n` (Laarhoven, *Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices*, arXiv:2610.15265 (held version, sha256 8fa7a08a…), §2.1, p.14:
"A full-rank lattice is L = BZⁿ ⊂ Rⁿ … The quotient Xn = SLn(R)/SLn(Z) is the space of unimodular
lattices"): the `ℤ`-span (`KannanLattice.Core.lattice`) of the columns of a representative
`B ∈ SL_n(ℝ)` of the coset.

**Formalization Note.** The representative is `Quotient.out`. Two representatives differ by a
right factor in `SL_n(ℤ)`, an integral unimodular change of columns, so they span the same lattice;
every quantity of the mission is a function of the lattice only. -/
noncomputable def latticeOf {n : ℕ} (x : X n) : Submodule ℤ (EuclideanSpace ℝ (Fin n)) :=
  KannanLattice.Core.lattice (fun i : Fin n => WithLp.toLp 2 (fun j : Fin n =>
    ((Quotient.out x : Matrix.SpecialLinearGroup (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) j i))

end RandLatEnum


