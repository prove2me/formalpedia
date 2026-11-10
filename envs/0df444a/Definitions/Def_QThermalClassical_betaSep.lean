-- Prove2me | Definitions.Def_QThermalClassical_betaSep
-- name    : QThermalClassical_betaSep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:12:55.426057+00:00
-- url     : https://prove2.me/theorems/cb0b5450-8aa1-4342-babc-d57ba3c3b11e
-- title:
--   Death-of-entanglement temperature $\beta_{\mathrm{sep}}$ of the $(s,k)$-long-range class
-- statement:
--   For the family $F=\{F_n\}$ of $(s,k)$-long-range Pauli Hamiltonians on $n$ qubits, the **death-of-entanglement temperature** is (Definition 2.2, eq. (9))
--   $$
--   \beta_{\mathrm{sep}}=\sup\left\{r\ge0:\ \rho_\beta(H)\in\mathrm{Sep}_n\ \text{for all } n,\ H\in F_n,\ 0\le\beta\le r\right\}.
--   $$
--   It is the largest inverse temperature up to which every Gibbs state of the class is fully separable.
--
--   **Formalization Note** The supremum is the real `sSup`, which returns $0$ on a set that is unbounded above; every statement about $\beta_{\mathrm{sep}}$ must show the set is bounded (Theorem 1(a) does, through its entangled witnesses). The set contains $0$. The register size runs over all $n\in\mathbb N$; the case $n=0$ adds nothing, since there the only Hamiltonian is $0$ and its Gibbs state is the $1\times1$ identity.
-- source:
--   J. Cotler, H. Putterman, A. Zlokapa, When quantum thermal states look classical, arXiv:2607.28536 (held version, sha256 7491d0b2…), Definition 2.2, eq. (9), p.11; Definition 2.3, p.12

import Mathlib
import Definitions.Def_QThermalClassical_ham
import Definitions.Def_QThermalClassical_gibbs
import Definitions.Def_QThermalClassical_IsSeparable
import Definitions.Def_QThermalClassical_IsLongRangePauli

set_option autoImplicit false

namespace QThermalClassical

/-- The death-of-entanglement temperature of the family of `(s, k)`-long-range Pauli
Hamiltonians, eq. (9):
`β_sep = sup {r ≥ 0 : ρ_β(H) ∈ Sep_n for all n, H ∈ F_n, 0 ≤ β ≤ r}`,
with `F_n` the `(s, k)`-long-range Pauli Hamiltonians on `n` qubits.

Source: J. Cotler, H. Putterman, A. Zlokapa, *When quantum thermal states look classical*,
arXiv:2607.28536 (held version, sha256 7491d0b2…), Definition 2.2, eq. (9), p.11, with the
family of Definition 2.3, p.12.

**Formalization Note.** The supremum is the real `sSup`. The set always contains `0`
(`ρ_0 = I/2^n` is a product state); where it is unbounded above `sSup` is the junk value `0`,
so every statement about `betaSep` must also show the set is bounded (for `k ≥ 2` this follows
from the entangled witnesses of Theorem 1(a)). The register size ranges over all `n : ℕ`; the
paper's `n ≥ 1` gives the same set, because on `0` qubits the only Hamiltonian is `0` and its
Gibbs state is the `1 × 1` identity. -/
noncomputable def betaSep (s k : ℝ) : ℝ :=
  sSup {r : ℝ | 0 ≤ r ∧ ∀ (n : ℕ) (c : PauliWord (Fin n) → ℝ), IsLongRangePauli s k c →
    ∀ β : ℝ, 0 ≤ β → β ≤ r → IsSeparable (gibbs (ham c) β)}

end QThermalClassical


