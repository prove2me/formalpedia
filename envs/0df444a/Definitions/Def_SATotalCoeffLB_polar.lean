-- Prove2me | Definitions.Def_SATotalCoeffLB_polar
-- name    : SATotalCoeffLB_polar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:18:55.029986+00:00
-- url     : https://prove2.me/theorems/51d77080-f359-4096-af77-d43fa9eb3144
-- title:
--   Polar matrix $B_a$ of a quadratic form
-- statement:
--   For $a = \sum_{i<j} a_{ij}\bar x_i \bar x_j \in Q_n$, the **polar matrix** $B_a \in \mathbb F_2^{n\times n}$ is the symmetric matrix with zero diagonal and
--
--   $$
--   (B_a)_{ij} = (B_a)_{ji} = a_{ij} \quad (i < j).
--   $$
--
--   It satisfies $a(\bar x + \bar x') + a(\bar x) + a(\bar x') = \bar x^{\mathsf T} B_a \bar x'$.
-- source:
--   Chen–Jin, Non-signaling PCPs as Algebraic Proofs, and Total Coefficients Lower Bounds for Sherali–Adams, STOC 2027 submission (manuscript sha256 da19ece6…9d9178), Definition 3, p.51

import Mathlib
import Definitions.Def_SATotalCoeffLB_QForm

namespace SATotalCoeffLB

/-- **The polar matrix `B_a`** of a quadratic form `a ∈ Q_n` (Definition 3, p.51, of Chen–Jin, *Non-signaling PCPs as Algebraic Proofs, and Total Coefficients Lower Bounds for
Sherali–Adams*, STOC 2027 submission manuscript
(sha256 da19ece6898e20b159d01408327de710d69219772cc1f088c80301a6679d9178)): the
symmetric matrix in `F₂^{n×n}` with zero diagonal and `(B_a)_ij = (B_a)_ji = a_ij` for `i < j`. -/
def polar {n : ℕ} (a : QForm n) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  fun i j => if h : i < j then a ⟨(i, j), h⟩ else if h' : j < i then a ⟨(j, i), h'⟩ else 0

end SATotalCoeffLB


