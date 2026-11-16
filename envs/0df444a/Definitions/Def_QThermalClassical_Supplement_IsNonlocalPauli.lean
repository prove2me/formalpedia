-- Prove2me | Definitions.Def_QThermalClassical_Supplement_IsNonlocalPauli
-- name    : QThermalClassical_Supplement_IsNonlocalPauli
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:35:30.310557+00:00
-- url     : https://prove2.me/theorems/629b12aa-86f4-4504-b0a8-ad4ad2182f62
-- title:
--   $(s,\gamma)$-nonlocal Pauli Hamiltonians
-- statement:
--   For $s,\gamma>0$, a Pauli Hamiltonian $H=\sum_Pc_PP$ (no identity term) is **$(s,\gamma)$-nonlocal** (Definition 2.5) if
--   $$
--   \max_{x\in[n]}\sum_{P:\ x\in\mathrm{supp}\,P}|c_P|\,e^{\gamma|\mathrm{supp}\,P|}\le s .
--   $$
--   Terms of arbitrary weight are allowed, with coefficients decaying exponentially in their support size.
--
--   **Formalization Note** The maximum over $x$ is a bound for every $x$; positivity of $s,\gamma$ is stated in each theorem.
-- source:
--   J. Cotler, H. Putterman, A. Zlokapa, When quantum thermal states look classical, arXiv:2607.28536 (held version, sha256 7491d0b2…), §2.1, eq. (5), p.11; Definition 2.5, eq. (14), p.12

import Mathlib
import Definitions.Def_QThermalClassical_Supplement_weightedStrength

set_option autoImplicit false

namespace QThermalClassical.Supplement

/-- `H = Σ_P c_P P` is an `(s, γ)`-nonlocal Pauli Hamiltonian (Definition 2.5, eq. (14)): it
is a Pauli Hamiltonian in the sense of eq. (5) (no identity term) and every qubit `x` satisfies
`Σ_{P : x ∈ supp P} |c_P| e^{γ |supp P|} ≤ s`. There is no bound on the support sizes.

Source: J. Cotler, H. Putterman, A. Zlokapa, *When quantum thermal states look classical*,
arXiv:2607.28536 (held version, sha256 7491d0b2…), §2.1, eq. (5), p.11, and Definition 2.5, eq. (14), p.12.

**Formalization Note.** The maximum over `x ∈ [n]` is a `∀ x`; the positivity `s, γ > 0`
is stated in each theorem. -/
def IsNonlocalPauli {Q : Type} [Fintype Q] [DecidableEq Q] (s γ : ℝ)
    (c : PauliWord Q → ℝ) : Prop :=
  c (fun _ => 0) = 0 ∧
  ∀ x : Q, weightedStrength (fun j => Real.exp (γ * j)) c x ≤ s

end QThermalClassical.Supplement


