-- Prove2me | Definitions.Def_SATotalCoeffLB_monomial
-- name    : SATotalCoeffLB_monomial
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:17:56.342678+00:00
-- url     : https://prove2.me/theorems/276ded4d-796c-47c0-8d8c-9dec97a6c244
-- title:
--   Multilinear monomial $\prod_{v\in S} v$
-- statement:
--   For a finite set $S \subseteq V$ of variables, the multilinear monomial is
--
--   $$
--   \prod_{v \in S} v, \qquad \text{i.e. } x \mapsto \prod_{v \in S} (-1)^{x_v}.
--   $$
--
--   The empty set gives the constant $1$. These monomials are the basis in which the coefficients and the coefficient norm $\|f\|_1$ are measured.
-- source:
--   Chen–Jin, Non-signaling PCPs as Algebraic Proofs, and Total Coefficients Lower Bounds for Sherali–Adams, STOC 2027 submission (manuscript sha256 da19ece6…9d9178), p.24 (Coefficient Norm), p.52 (monomials X^αY^b)

import Mathlib
import Definitions.Def_SATotalCoeffLB_var

namespace SATotalCoeffLB

/-- **The multilinear monomial** `∏_{v ∈ S} v` of a finite set of variables `S` (the monomials of
the Boolean quotient ring, pp.9, 24, 52, of Chen–Jin, *Non-signaling PCPs as Algebraic Proofs, and Total Coefficients Lower Bounds for
Sherali–Adams*, STOC 2027 submission manuscript
(sha256 da19ece6898e20b159d01408327de710d69219772cc1f088c80301a6679d9178)). The empty set gives the constant `1`. -/
noncomputable def monomial {V : Type*} (S : Finset V) : CubeFn V := fun x => ∏ v ∈ S, var v x

end SATotalCoeffLB


