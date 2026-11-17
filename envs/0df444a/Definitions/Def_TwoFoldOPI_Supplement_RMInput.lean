-- Prove2me | Definitions.Def_TwoFoldOPI_Supplement_RMInput
-- name    : TwoFoldOPI_Supplement_RMInput
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:55:41.497149+00:00
-- url     : https://prove2.me/theorems/1a03d864-9e74-4a98-86a5-74b8c09718d0
-- title:
--   Instances of $\mathrm{RMSyndrome}_{q,\rho,c}(v)$ and $\mathrm{RMSupp}_{q,\rho,c}(v)$ as algorithm input
-- statement:
--   An instance of the Reed–Muller problems is given to an algorithm as the explicit field $\mathbb F_q$, the number $v$ of variables, the number $m$ of points, and the points $p_1,\dots,p_m\in\mathbb F_q^v$ of $S$ in the order of the columns of $B$.
--
--   The encoding writes the field presentation, $v$ and $m$ in self-delimiting binary, and the coordinates of the points in the fixed bit layout of field elements; the size parameter is $m+v+q$.
--
--   **Formalization Note** The rows of $B$ are determined by $(q,v,\lfloor\rho v\rfloor)$ and are not part of the input.
-- source:
--   Ragavan, Shutty, Quantum Algorithms for OPI Variants Beyond Locality and Classical Decodability, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §6, Definitions 6.1–6.2, p. 36; §5.2, Computational conventions, p. 26

import Mathlib
import Definitions.Def_TwoFoldOPI_elemBits

namespace TwoFoldOPI

namespace Supplement

open QAlgorithms

/-- **Instances of `RMSyndrome_{q,ρ,c}(v)` and `RMSupp_{q,ρ,c}(v)` as algorithm input.**
Ragavan, Shutty, *Quantum Algorithms for OPI Variants Beyond Locality and Classical
Decodability*, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §6, Definitions 6.1–6.2, p.36: "Sample a uniformly random subset S ⊆ F_q^v of size m. …
Let B ∈ F_q^{n×m} have rows indexed by monomials … and columns indexed by the points of S";
§5.2, "Computational conventions", p.26 ("an explicitly represented finite field").

An instance is the field presentation `F`, the number of variables `v`, the number of points
`m` and the points `pts 0, …, pts (m−1) ∈ F^v` of `S` (the columns of `B`, in this order).
`encode` writes `F` (`fieldEncode`), `v` and `m` in self-delimiting binary, and then the
points, coordinate by coordinate, each coordinate by `elemBits`. `scale = m + v + q`.

**Formalization Note.** The module holds the input type with its encoding and size, as one unit.
The rows of `B` are determined by `(q, v, ⌊ρv⌋)` and are not part of the input. -/
structure RMInput where
  /-- The field. -/
  F : AvgCaseTI.FieldPres
  /-- The number of variables. -/
  v : ℕ
  /-- The number of points. -/
  m : ℕ
  /-- The points of `S`, in column order. -/
  pts : Fin m → Fin v → F.F

/-- The bit encoding of an instance. -/
noncomputable def RMInput.encode (x : RMInput) : List Bool :=
  fieldEncode x.F ++ LocalHamiltonian.encBin x.v ++ LocalHamiltonian.encBin x.m ++
    (List.ofFn fun j : Fin x.m =>
      (List.ofFn fun i : Fin x.v => List.ofFn (elemBits x.F (x.pts j i))).flatten).flatten

/-- The size parameter `m + v + q`. -/
def RMInput.scale (x : RMInput) : ℕ := x.m + x.v + x.F.q

end Supplement

end TwoFoldOPI


