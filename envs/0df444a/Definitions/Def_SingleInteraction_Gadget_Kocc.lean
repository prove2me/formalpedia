-- Prove2me | Definitions.Def_SingleInteraction_Gadget_Kocc
-- name    : SingleInteraction_Gadget_Kocc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:55:20.307048+00:00
-- url     : https://prove2.me/theorems/767b81a1-b7f4-42ea-8e23-5f1d7a10b4a2
-- title:
--   The target XY occurrence Hamiltonian $K$
-- statement:
--   For a gadget, $K=\sum_{e=1}^MK_{u_ev_e}$ with $K_{uv}=X_uX_v+Y_uY_v$, the XY occurrence Hamiltonian on the $n$ work qubits that the gadget simulates. It is also lifted to the work and mediator registers (identity on the mediators), which identifies the zero-defect subspace with the work register in eq. (35).
-- source:
--   Hecker, The Complexity of Single-Interaction Hamiltonians, arXiv:2609.39592 (held version, sha256 19ddc444…), Lemma 61, p.55; §5.1.4, p.61

import Mathlib
import Definitions.Def_SingleInteraction_Gadget
import Definitions.Def_SingleInteraction_onTuple
import Definitions.Def_SingleInteraction_xyInteraction

namespace SingleInteraction

namespace Gadget

/-- The target XY occurrence Hamiltonian `K = Σ_{e=1}^M K_{u_e v_e}`, `K_{uv} = X_uX_v + Y_uY_v`, on the `n`
work qubits (Hecker, *The Complexity of Single-Interaction Hamiltonians*, arXiv:2609.39592 (held version, sha256 19ddc444…), Lemma 61, p.55; §5.1.2, p.56). -/
noncomputable def Kocc (G : Gadget) : Matrix (Fin G.n → Fin 2) (Fin G.n → Fin 2) ℂ :=
  ∑ e : Fin G.M, onTuple xyInteraction ![(G.occ e).1, (G.occ e).2]

/-- The same `K` acting on the work qubits of the work and mediator register (identity on the
mediators), used to identify the zero-defect subspace with the work register (Hecker, *The Complexity of Single-Interaction Hamiltonians*, arXiv:2609.39592 (held version, sha256 19ddc444…), §5.1.4, p.61,
eq. (35)). -/
noncomputable def Klift (G : Gadget) : Matrix (G.VS → Fin 2) (G.VS → Fin 2) ℂ :=
  ∑ e : Fin G.M, onTuple xyInteraction ![(Sum.inl (G.occ e).1 : G.VS), Sum.inl (G.occ e).2]

end Gadget

end SingleInteraction


