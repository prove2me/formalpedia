-- Prove2me | Definitions.Def_QThermalClassical_Supplement_weightedStrength
-- name    : QThermalClassical_Supplement_weightedStrength
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:34:59.18422+00:00
-- url     : https://prove2.me/theorems/8eca197e-1c24-4652-8ba7-b47ee0a04714
-- title:
--   Weighted on-site strength $\sum_{P\ni x}|c_P|\,w(|\mathrm{supp}\,P|)$
-- statement:
--   For a weight $w:\mathbb N\to\mathbb R$, a Pauli Hamiltonian $H=\sum_P c_PP$ and a qubit $x$,
--   $$
--   \sum_{P:\ x\in\mathrm{supp}\,P}|c_P|\,w(|\mathrm{supp}\,P|).
--   $$
--   Its maximum over $x$ is the quantity in (14) (with $w(j)=e^{\gamma j}$), (27) and (434).
--
--   **Formalization Note** In (434) the paper writes $\|h_a\|$ for the term $h_a=c_aP_a$; Pauli strings have operator norm $1$, so $\|h_a\|=|c_a|$.
-- source:
--   J. Cotler, H. Putterman, A. Zlokapa, When quantum thermal states look classical, arXiv:2607.28536 (held version, sha256 7491d0b2…), eq. (14), p.12; eq. (27), p.14; eq. (434), p.88

import Mathlib
import Definitions.Def_QThermalClassical_pauliOp

set_option autoImplicit false

namespace QThermalClassical.Supplement

open Classical in
/-- The weighted on-site strength at qubit `x` of `H = Σ_P c_P P` with weight `w`:
`Σ_{P : x ∈ supp P} |c_P| w(|supp P|)`, the quantity inside the maximum of eqs. (14), (27)
and (434).

Source: J. Cotler, H. Putterman, A. Zlokapa, *When quantum thermal states look classical*,
arXiv:2607.28536 (held version, sha256 7491d0b2…), eq. (14), p.12; eq. (27), p.14; eq. (434), p.88.

**Formalization Note.** In (434) the paper writes `‖h_a‖` for the term `h_a = c_a P_a`; a
Pauli string has operator norm `1`, so `‖h_a‖ = |c_a|`. Words with `c P = 0` contribute
nothing. -/
noncomputable def weightedStrength {Q : Type} [Fintype Q] [DecidableEq Q] (w : ℕ → ℝ)
    (c : PauliWord Q → ℝ) (x : Q) : ℝ :=
  ∑ P ∈ Finset.univ.filter (fun P : PauliWord Q => x ∈ pauliSupport P),
    |c P| * w (pauliSupport P).card

end QThermalClassical.Supplement


