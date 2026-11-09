-- Prove2me | Definitions.Def_SATotalCoeffLB_CubeFn
-- name    : SATotalCoeffLB_CubeFn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:15:54.968779+00:00
-- url     : https://prove2.me/theorems/4a5bbed5-bff3-403a-971c-e49f4fb8ca3b
-- title:
--   The Boolean quotient ring $\mathbb R[V]/\langle y^2-1 : y\in V\rangle$ as functions on the cube
-- statement:
--   For a finite set of variables $V$, the **Boolean quotient ring** is $\mathbb R[V]/\langle y^2 - 1 : y \in V\rangle$: polynomials in the variables of $V$ in which every variable squares to $1$. Every element has a unique multilinear representative, and it is determined by its values on the $\pm 1$ cube.
--
--   Here an element is a real-valued function on bit vectors $x \in \mathbb F_2^V$. The bit vector $x$ stands for the $\pm 1$ assignment giving the variable $v$ the value $(-1)^{x_v}$; this is the paper's $\{\pm1\}$ encoding, in which Boolean $0$ is $+1$ and Boolean $1$ is $-1$. Sums and products are taken pointwise.
--
--   **Formalization Note** For finite $V$ the evaluation map from the quotient ring to functions on the cube is a ring isomorphism (the $2^{|V|}$ multilinear monomials are a basis of both). So an identity in the quotient ring is an equality of functions, and a polynomial "nonnegative on the cube" is a nonnegative function.
-- source:
--   Chen–Jin, Non-signaling PCPs as Algebraic Proofs, and Total Coefficients Lower Bounds for Sherali–Adams, STOC 2027 submission (manuscript sha256 da19ece6…9d9178), p.9 (Theorem 3), p.23 (the {±1} encoding), p.24 (Level-k Sherali–Adams), Section 9, p.48

import Mathlib

namespace SATotalCoeffLB

/-- **The Boolean quotient ring `ℝ[V]/⟨y² − 1 : y ∈ V⟩`**, modelled as the real functions on the
Boolean cube (p.9, p.24, p.48), from Chen–Jin, *Non-signaling PCPs as Algebraic Proofs, and Total Coefficients Lower Bounds for
Sherali–Adams*, STOC 2027 submission manuscript
(sha256 da19ece6898e20b159d01408327de710d69219772cc1f088c80301a6679d9178).

A point of the cube is a bit vector `x : V → ZMod 2`; it stands for the `±1` assignment giving
variable `v` the value `(-1)^{x v}` (the paper's `{±1}` encoding, p.23: Boolean 0 is `+1`, Boolean 1
is `-1`). Addition and multiplication are pointwise.

**Formalization Note** For a finite variable set `V` the multilinear monomials form a basis of both
the quotient ring and the function space, and evaluation on the cube is a ring isomorphism between
them. So an identity "in the Boolean quotient ring" is exactly an equality of functions here, and
every element has a unique multilinear representative (recovered by `coeff`). -/
abbrev CubeFn (V : Type*) : Type _ := (V → ZMod 2) → ℝ

end SATotalCoeffLB


