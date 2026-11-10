-- Prove2me | Definitions.Def_QThermalClassical_restrictTouching
-- name    : QThermalClassical_restrictTouching
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:11:29.805011+00:00
-- url     : https://prove2.me/theorems/565c8f59-0a26-4f56-97a2-06af0d00e407
-- title:
--   Restrictions $H(S)$, $H_{(K)}$, $H^{(S)}_{(K)}$
-- statement:
--   For a Pauli Hamiltonian $H=\sum_a\lambda_aP_a$ and site sets $S,K$:
--   1. $H(S)=\sum_{a:\,\mathrm{supp}(P_a)\subseteq S}\lambda_aP_a$, the terms contained in $S$ (eq. (47));
--   2. $H_{(K)}=\sum_{a:\,\mathrm{supp}(P_a)\cap K\neq\emptyset}\lambda_aP_a$, the terms touching $K$ (eqs. (15), (48));
--   3. $H^{(S)}_{(K)}=\sum_{a:\,\mathrm{supp}(P_a)\subseteq S,\ \mathrm{supp}(P_a)\cap K\neq\emptyset}\lambda_aP_a$, the terms contained in $S$ and touching $K$ (eq. (83)).
--
--   With $K=\mathrm{supp}(P_{a^*})$ these are the paper's $H_{(a^*)}$ and $H^{(S)}_{(a^*)}$; item 3 is also the paper's convention for a partially pinned label $a^*\notin A(S)$ (p.26).
--
--   **Formalization Note** The restrictions act on coefficient functions (zero on the words not selected).
-- source:
--   J. Cotler, H. Putterman, A. Zlokapa, When quantum thermal states look classical, arXiv:2607.28536 (held version, sha256 7491d0b2…), §3, eqs. (47)–(48), p.19; eq. (83), p.25; p.26

import Mathlib
import Definitions.Def_QThermalClassical_pauliOp

set_option autoImplicit false

namespace QThermalClassical

variable {Q : Type} [Fintype Q] [DecidableEq Q]

/-- `H(S)`, eq. (47): the terms of `H` contained in the site set `S`, as a coefficient
function (zero on every other word). -/
def restrictIn (c : PauliWord Q → ℝ) (S : Finset Q) : PauliWord Q → ℝ :=
  fun P => if pauliSupport P ⊆ S then c P else 0

/-- `H_{(K)}`, eqs. (15) and (48): the terms of `H` touching the site set `K`. With
`K = supp(P_{a*})` this is `H_{(a*)}`. -/
def touching (c : PauliWord Q → ℝ) (K : Finset Q) : PauliWord Q → ℝ :=
  fun P => if (pauliSupport P ∩ K).Nonempty then c P else 0

/-- `H^{(S)}_{(K)}`, eq. (83) and the partial-pinning convention of p.26: the terms of `H`
contained in `S` and touching `K`. With `K = supp(P_{a*})` this is `H^{(S)}_{(a*)}`, whether or
not `a*` itself lies in `A(S)`.

Source: J. Cotler, H. Putterman, A. Zlokapa, *When quantum thermal states look classical*,
arXiv:2607.28536 (held version, sha256 7491d0b2…), §3, eqs. (47)–(48), p.19; eq. (83), p.25;
p.26.

**Formalization Note.** Restrictions act on coefficient functions; the operator is
`ham (restrictTouching c S K)`. The paper's `a ∩ a* ≠ ∅` is
`supp(P_a) ∩ supp(P_{a*}) ≠ ∅`. -/
def restrictTouching (c : PauliWord Q → ℝ) (S K : Finset Q) : PauliWord Q → ℝ :=
  fun P => if pauliSupport P ⊆ S ∧ (pauliSupport P ∩ K).Nonempty then c P else 0

end QThermalClassical


