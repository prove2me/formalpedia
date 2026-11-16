-- Prove2me | Definitions.Def_QThermalClassical_Supplement_betaSepLI
-- name    : QThermalClassical_Supplement_betaSepLI
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:34:27.889963+00:00
-- url     : https://prove2.me/theorems/8bd783cc-df68-428f-a401-772b548c5730
-- title:
--   $\beta_{\mathrm{sep}}$ of the $(\mathfrak d,k)$-low-intersection family
-- statement:
--   The death-of-entanglement temperature (9) of the family $\mathcal F_{\mathfrak d,k}$ of $(\mathfrak d,k)$-low-intersection Pauli Hamiltonians:
--   $$
--   \beta_{\mathrm{sep}}(\mathcal F_{\mathfrak d,k})=\sup\{r\ge0:\ \rho_\beta(H)\in\mathrm{Sep}_n\ \text{for all } n,\ H\in\mathcal F_{\mathfrak d,k}\text{ on } n \text{ qubits},\ 0\le\beta\le r\}.
--   $$
--
--   It is the quantity bounded in Theorem 1(b).
--
--   **Formalization Note** The real supremum, which takes the value $0$ on an unbounded set; statements about it must force boundedness (a positive lower bound does). The register size ranges over all $n\in\mathbb N$.
-- source:
--   J. Cotler, H. Putterman, A. Zlokapa, When quantum thermal states look classical, arXiv:2607.28536 (held version, sha256 7491d0b2…), Definition 2.2, eq. (9), p.11, with Definition 2.4, p.12

import Mathlib
import Definitions.Def_QThermalClassical_ham
import Definitions.Def_QThermalClassical_gibbs
import Definitions.Def_QThermalClassical_IsSeparable
import Definitions.Def_QThermalClassical_Supplement_IsLowIntersectionPauli

set_option autoImplicit false

namespace QThermalClassical.Supplement

/-- The death-of-entanglement temperature (9) of the family of `(d, k)`-low-intersection Pauli
Hamiltonians:
`β_sep = sup {r ≥ 0 : ρ_β(H) ∈ Sep_n for all n, H ∈ F_n, 0 ≤ β ≤ r}`, with `F_n` the
`(d, k)`-low-intersection Pauli Hamiltonians on `n` qubits.

Source: J. Cotler, H. Putterman, A. Zlokapa, *When quantum thermal states look classical*,
arXiv:2607.28536 (held version, sha256 7491d0b2…), Definition 2.2, eq. (9), p.11, with the family of Definition 2.4, p.12.

**Formalization Note.** Same conventions as the published `QThermalClassical.betaSep`: the
real `sSup`, which is the junk value `0` when the set is unbounded above, so every statement
about `betaSepLI` must also force boundedness (a positive lower bound does). -/
noncomputable def betaSepLI (d k : ℝ) : ℝ :=
  sSup {r : ℝ | 0 ≤ r ∧ ∀ (n : ℕ) (c : PauliWord (Fin n) → ℝ), IsLowIntersectionPauli d k c →
    ∀ β : ℝ, 0 ≤ β → β ≤ r → IsSeparable (gibbs (ham c) β)}

end QThermalClassical.Supplement


