-- Prove2me | Definitions.Def_AffDisp4n_State
-- name    : AffDisp4n_State
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:57:41.773366+00:00
-- url     : https://prove2.me/theorems/3a444d73-6002-424e-870d-46e2d345a28f
-- title:
--   State of gate elimination: $\Phi$, the pairs $P$, and a fair semi-circuit
-- statement:
--   A **state** of gate elimination for inputs in $\mathbb F_2^n$ consists of the following data.
--
--   1. The map $\Phi(u) = b + L u$ from $m$ **parameters** $u \in \mathbb F_2^m$ to inputs, with $b \in \mathbb F_2^n$ and $L \in \mathbb F_2^{n \times m}$.
--   2. A set $P$ of pairs of parameters.
--   3. A **fair semi-circuit** on the parameters. It has an **affine system** $A v = N u + c$ of $r$ equations in the parameters and $r$ **auxiliary variables** $v$: $A \in \mathbb F_2^{r \times r}$ is the auxiliary matrix, $N \in \mathbb F_2^{r \times m}$ the parameter matrix and $c \in \mathbb F_2^r$ the constant terms. It also has an **acyclic part**, an ordinary circuit whose gate inputs are constants, parameters, auxiliary variables or earlier gates. Its output is a constant or a literal of a parameter, an auxiliary variable or a gate.
--
--   Parameters that the circuit no longer reads stay in $\Phi$.
--
--   **Formalization Note** The invariants are a separate predicate (`State.Valid`), and a state records no history. Parameters are indexed by `Fin m` and auxiliary variables by `Fin r`.
-- source:
--   Mishra, Santhanam, An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits, STOC 2027 submission (manuscript sha256 6bc3ff9d…fd96), §2.2–§2.4, pp.13–16

import Mathlib
import Definitions.Def_AffDisp4n_Src
import Definitions.Def_AffDisp4n_Acyclic

namespace AffDisp4n

/-- A **state of gate elimination** for inputs `𝔽₂ⁿ` (Mishra–Santhanam, *An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits*, STOC 2027 submission (manuscript sha256 6bc3ff9d…), §2.2–§2.4, pp.13–16): the injective map
`Φ(u) = b + L u` from the `m` parameters to the inputs (display (1), p.13), the set `P` of pairs of
parameters, and the current **fair semi-circuit** on the parameters (§2.3, pp.13–14). The fair
semi-circuit consists of
1. the affine system `A v = N u + c` of `r` equations in the parameters `u` and `r` auxiliary variables
   `v`, with auxiliary matrix `A`, parameter matrix `N` and constant vector `c`;
2. the acyclic part `circ`, an ordinary circuit whose gate inputs are constants, parameters (`inl`),
   auxiliary variables (`inr`) or earlier gates;
3. the output of `circ`: a constant or a literal of a parameter, an auxiliary variable, or a gate.

**Formalization Note** The invariants (injectivity of `Φ`, disjointness of the pairs, invertibility of
`A`, at most three nonconstant terms per equation, and `C(u) = C₀(Φ(u))` on `Z(P)`) are the separate
predicate `State.Valid`. A state records no history. Parameters are `Fin m` and auxiliary variables
`Fin r`; parameters that the circuit no longer reads stay in `Φ` (§2.4, p.16). -/
structure State (n : ℕ) where
  /-- the number of parameters -/
  m : ℕ
  /-- the number of equations, which is also the number of auxiliary variables -/
  r : ℕ
  /-- the translation part of `Φ` -/
  b : Fin n → ZMod 2
  /-- the linear part of `Φ` -/
  L : Matrix (Fin n) (Fin m) (ZMod 2)
  /-- the set of pairs of parameters -/
  P : Finset (Sym2 (Fin m))
  /-- the auxiliary matrix -/
  A : Matrix (Fin r) (Fin r) (ZMod 2)
  /-- the parameter matrix -/
  N : Matrix (Fin r) (Fin m) (ZMod 2)
  /-- the constant terms -/
  c : Fin r → ZMod 2
  /-- the acyclic part with its output; inputs are parameters `inl` and auxiliary variables `inr` -/
  circ : Acyclic (Fin m ⊕ Fin r)

end AffDisp4n


