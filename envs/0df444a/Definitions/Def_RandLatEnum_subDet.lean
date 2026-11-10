-- Prove2me | Definitions.Def_RandLatEnum_subDet
-- name    : RandLatEnum_subDet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:14:13.140571+00:00
-- url     : https://prove2.me/theorems/570003f0-af41-44bc-b9ad-604b8ff25267
-- title:
--   Determinant of a sublattice (covolume in its span)
-- statement:
--   For a sublattice $M$ of rank $r$, $\det M$ is its **covolume in its own span**: for any basis $(c_1,\dots,c_r)$ of $M$,
--   $$
--   \det M=\prod_{i=1}^{r}\|c_i^*\|=\sqrt{\det\bigl(\langle c_i,c_j\rangle\bigr)_{i,j}} ,
--   $$
--   which does not depend on the basis. For the prefix sublattice $M_k$ of a basis $B$, $\det M_k=e^{P_k(B)}$.
--
--   **Formalization Note** A basis is a linearly independent family of $\operatorname{rank}M$ vectors whose $\mathbb Z$-span is $M$, chosen by `Classical.choose`, and the covolume is the published `latticeDet` (product of Gram–Schmidt lengths). Every sublattice of a lattice has such a basis; for a subgroup that is not a lattice the value is the junk $0$, which never occurs in the mission.
-- source:
--   Laarhoven, Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices, arXiv:2610.15265 (held version, sha256 8fa7a08a…), §2.1, p.14; (3.2), p.17

import Mathlib
import Definitions.Def_KannanLattice_Core_Lattice

namespace RandLatEnum

open Classical in
/-- The determinant `det M` of a sublattice, its covolume in its own span (Laarhoven, *Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices*, arXiv:2610.15265 (held version, sha256 8fa7a08a…), §2.1, p.14: "For a
sublattice M, det M is its covolume in its span"): the product of the Gram–Schmidt lengths
(`KannanLattice.Core.latticeDet`, equal to `√det Gram`) of a basis of `M`.

**Formalization Note.** A basis is a linearly independent family `b` of `rank M` vectors whose
`ℤ`-span is `M`, chosen by `Classical.choose`; the covolume does not depend on the choice. Every
sublattice of a lattice has such a basis; for a subgroup that is not a lattice the value is the
junk `0`, which never occurs in the mission (all `M` are sublattices of a lattice). -/
noncomputable def subDet {k : ℕ} (M : Submodule ℤ (EuclideanSpace ℝ (Fin k))) : ℝ :=
  if h : ∃ b : Fin (Module.finrank ℤ M) → EuclideanSpace ℝ (Fin k),
      LinearIndependent ℝ b ∧ KannanLattice.Core.lattice b = M
  then KannanLattice.Core.latticeDet h.choose else 0

end RandLatEnum


