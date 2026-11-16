-- Prove2me | Definitions.Def_BorderD4_Supplement_IsHomogeneousCircuit
-- name    : BorderD4_Supplement_IsHomogeneousCircuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:00:24.31126+00:00
-- url     : https://prove2.me/theorems/44f32213-cf54-42ab-a12d-ffd585fe8b79
-- title:
--   Homogeneous $\Sigma^{[k]}\Pi\Sigma\Pi^{[\delta]}$ circuits
-- statement:
--   A $\Sigma^{[k]}\Pi\Sigma\Pi^{[\delta]}$ circuit over a ring $R$ (the published model `BorderD4.SPSP`) is **homogeneous** if every gate computes a polynomial that is homogeneous in $x$. Concretely, with addition gates computing $q_m=\sum_b a_{m,b}x^{\beta_b}$ and product gates computing $\prod_m q_m^{e_{i,m}}$, the circuit is homogeneous when
--
--   1. every $q_m$ is homogeneous;
--   2. every product $\prod_m q_m^{e_{i,m}}$, and its scalar multiple $T_i=c_i\prod_m q_m^{e_{i,m}}$ on the wire to the output, is homogeneous;
--   3. the output $\sum_i T_i$ is homogeneous.
--
--   The bottom gates compute monomials, which are always homogeneous. The predicate is the hypothesis of the second clauses of Theorems 3.1 and 4.16.
--
--   **Formalization Note** The zero polynomial is homogeneous of every degree. Over $R=F((\varepsilon))$ homogeneity is in $x$ only.
-- source:
--   A. Dey, P. Dutta, Z. Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), Definition 2.11, p.33

import Mathlib
import Definitions.Def_BorderD4_SPSP
set_option autoImplicit false

open MvPolynomial

namespace BorderD4.Supplement

/-- A `Σ^[k]ΠΣΠ^[δ]` circuit is **homogeneous**: every gate computes a polynomial that is homogeneous in `x`.
Source: Dey, Dutta, Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), Definition 2.11, p.33 ("The circuit is homogeneous if every gate computes a polynomial that is homogeneous in x").

The gates of a `BorderD4.SPSP` circuit, from the bottom: the bottom product gates compute monomials, which are
always homogeneous; the addition gates compute `q_m = C.bottomPoly m`; the product gates compute
`∏_m q_m ^ e_{i,m}`, which reach the output with the scalar `topc i` (`C.gate i`); the output computes `C.eval`.
Each of these is required to be homogeneous of some degree.

**Formalization Note** The zero polynomial is homogeneous of every degree. Over `R = F((ε))` homogeneity is in the
variables `x` only, the coefficients being arbitrary Laurent series, as in Theorem 4.16. The condition on `C.gate i`
follows from the one on the product gate, and is listed for the wire with its scalar. -/
def IsHomogeneousCircuit {R σ : Type*} [CommRing R] {k δ : ℕ} (C : SPSP R σ k δ) : Prop :=
  (∀ m, ∃ e : ℕ, (C.bottomPoly m).IsHomogeneous e) ∧
  (∀ i, ∃ e : ℕ, (∏ m, C.bottomPoly m ^ C.exp i m).IsHomogeneous e) ∧
  (∀ i, ∃ e : ℕ, (C.gate i).IsHomogeneous e) ∧
  ∃ e : ℕ, C.eval.IsHomogeneous e

end BorderD4.Supplement


