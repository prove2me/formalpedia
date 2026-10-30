-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartI_ch13_ch13Partitions
-- name    : RamanujanLostNotebook_PartI_ch13_ch13Partitions
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-11T10:22:27.81149+00:00
-- url     : https://prove2.me/theorems/26773efe-d74c-4228-b37b-829979317184
-- title:
--   Ramanujan's Lost Notebook Part I, Ch. 13: ch13Partitions
-- statement:
--   Multiplicity tuples (k_1,...,k_j) of partitions of j. The empty tuple for j=0
--   is included. Every multiplicity is bounded by j; the finite encoding loses no tuple.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part I, Springer 2005, Chapter 13.

import Mathlib

noncomputable section

namespace RamanujanLostNotebook.PartI

/-- Multiplicity tuples (k_1,...,k_j) of partitions of j. The empty tuple for j=0
is included. Every multiplicity is bounded by j; the finite encoding loses no tuple. -/
def ch13Partitions (j : ℕ) : Finset (Fin j → Fin (j + 1)) :=
  Finset.univ.filter (fun t => (∑ i : Fin j, (i.val + 1) * (t i).val) = j)

end RamanujanLostNotebook.PartI

end


