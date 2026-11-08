-- Prove2me | Definitions.Def_SingleInteraction_xyHam
-- name    : SingleInteraction_xyHam
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:55:34.140227+00:00
-- url     : https://prove2.me/theorems/fa0c8ddc-b6fa-4e5f-b447-316e0567354a
-- title:
--   Weighted XY Hamiltonian $\sum_j\alpha_jK_{u_jv_j}$
-- statement:
--   For a list of terms $(u_j,v_j,\alpha_j)$ on $n$ qubits, the weighted XY Hamiltonian
--
--   $$H=\sum_j\alpha_j\,K_{u_jv_j},\qquad K_{uv}=X_uX_v+Y_uY_v.$$
--
--   Terms may repeat. With unit weights it is the occurrence Hamiltonian $K=\sum_eK_{u_ev_e}$ of Lemma 61.
-- source:
--   Hecker, The Complexity of Single-Interaction Hamiltonians, arXiv:2609.39592 (held version, sha256 19ddc444…), §2.3.5, p.25; §5.1.1, p.55

import Mathlib
import Definitions.Def_SingleInteraction_xyInteraction
import Definitions.Def_SingleInteraction_tupleTerm

namespace SingleInteraction

/-- The weighted XY Hamiltonian `Σ_j α_j K_{u_j v_j}` on `n` qubits, `K_{uv} = X_uX_v + Y_uY_v`
(Hecker, *The Complexity of Single-Interaction Hamiltonians*, arXiv:2609.39592 (held version, sha256 19ddc444…), §2.3.5, p.25, weighted `S`-Hamiltonian `H = Σ_i α_i s^{(j_i)}_{V_i}` with `S = {X⊗X + Y⊗Y}`;
§5.1.1, p.55, `H^wt_XY = Σ_j α_j K_{u_j v_j}`).

**Formalization Note** A term is a triple `(u, v, α)`: the interaction `X⊗X + Y⊗Y` applied to the ordered
pair `(u, v)` (via `tupleTerm`) with weight `α`. Terms may repeat. -/
noncomputable def xyHam (n : ℕ) (terms : List (ℕ × ℕ × ℝ)) :
    Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  (terms.map fun t => ((t.2.2 : ℝ) : ℂ) • tupleTerm n 2 xyInteraction [t.1, t.2.1]).sum

end SingleInteraction


