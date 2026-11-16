-- Prove2me | Definitions.Def_QThermalClassical_Supplement_betaStab
-- name    : QThermalClassical_Supplement_betaStab
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:38:23.177029+00:00
-- url     : https://prove2.me/theorems/dbfc5b5c-5265-4b03-8a18-fc5f8442747c
-- title:
--   $\beta_{\mathrm{stab}}(s,k;\epsilon)$
-- statement:
--   The death-of-magic temperature (10) of the family of $(s,k)$-long-range Pauli Hamiltonians that are $\epsilon$-close to commuting:
--   $$
--   \beta_{\mathrm{stab}}(s,k;\epsilon)=\sup\{r\ge0:\ \rho_\beta(H)\in\mathrm{STAB}_n\ \text{for all } n,\ H \text{ in the family},\ 0\le\beta\le r\}.
--   $$
--
--   **Formalization Note** The set is a separate definition; the real supremum takes the value $0$ on an unbounded set, so upper bounds are stated for every element of the set as well.
-- source:
--   J. Cotler, H. Putterman, A. Zlokapa, When quantum thermal states look classical, arXiv:2607.28536 (held version, sha256 7491d0b2…), Definition 2.2, eq. (10), p.11; Definition 2.3, p.12; Definition 2.6, p.16

import Mathlib
import Definitions.Def_QThermalClassical_gibbs
import Definitions.Def_QThermalClassical_IsLongRangePauli
import Definitions.Def_QThermalClassical_Supplement_STAB
import Definitions.Def_QThermalClassical_Supplement_epsClose

set_option autoImplicit false

namespace QThermalClassical.Supplement

/-- The set in (10) for the family of `(s, k)`-long-range Pauli Hamiltonians that are
`ε`-close to commuting: the `r ≥ 0` such that `ρ_β(H) ∈ STAB_n` for all `n`, all such `H` on
`n` qubits and all `0 ≤ β ≤ r`.

Source: J. Cotler, H. Putterman, A. Zlokapa, *When quantum thermal states look classical*,
arXiv:2607.28536 (held version, sha256 7491d0b2…), Definition 2.2, eq. (10), p.11, with Definition 2.3, p.12, and Definition 2.6,
p.16. -/
def betaStabSet (s k ε : ℝ) : Set ℝ :=
  {r : ℝ | 0 ≤ r ∧ ∀ (n : ℕ) (c : PauliWord (Fin n) → ℝ), IsLongRangePauli s k c →
    epsClose c ≤ ε → ∀ β : ℝ, 0 ≤ β → β ≤ r → gibbs (ham c) β ∈ STAB}

/-- The death-of-magic temperature `β_stab(s, k; ε)` (eq. (10)): the supremum of
`betaStabSet s k ε`.

Source: J. Cotler, H. Putterman, A. Zlokapa, *When quantum thermal states look classical*,
arXiv:2607.28536 (held version, sha256 7491d0b2…), Definition 2.2, eq. (10), p.11.

**Formalization Note.** The real `sSup`, the junk value `0` when the set is unbounded above;
statements about `betaStab` also bound every element of `betaStabSet`. -/
noncomputable def betaStab (s k ε : ℝ) : ℝ := sSup (betaStabSet s k ε)

end QThermalClassical.Supplement


