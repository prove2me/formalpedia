-- Prove2me | Definitions.Def_AgnosticTNS_encMat
-- name    : AgnosticTNS_encMat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:34:37.079197+00:00
-- url     : https://prove2.me/theorems/9170b881-76c3-4661-831e-42a1fc4dea1d
-- title:
--   Binary description of a Gaussian-rational matrix
-- statement:
--   A matrix with Gaussian-rational entries is described by all its entries in a fixed enumeration of the index pairs.
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Lemma 3.9, p.26

import Mathlib
import Definitions.Def_AgnosticTNS_encC

namespace AgnosticTNS

/-- **The binary description of a matrix with Gaussian-rational entries**, for the classical
output of Lemma 3.9, p.26 ("a classical description of a density operator") (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)): all entries,
in the order of the fixed enumeration `Fintype.equivFin` of `ι × ι`. -/
noncomputable def encMat {ι : Type} [Fintype ι] (M : Matrix ι ι ℂ) : QAlgorithms.Complexity.Str :=
  ((List.finRange (Fintype.card (ι × ι))).map fun t =>
    let a := (Fintype.equivFin (ι × ι)).symm t
    encC (M a.1 a.2)).flatten

end AgnosticTNS


