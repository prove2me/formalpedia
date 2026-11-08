-- Prove2me | Definitions.Def_SingleInteraction_Gadget_Fexact
-- name    : SingleInteraction_Gadget_Fexact
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:58:48.345734+00:00
-- url     : https://prove2.me/theorems/28446b49-95d3-48c2-8f3b-ef69c5b1fe39
-- title:
--   Exact effective Hamiltonian $F(E)$
-- statement:
--   In the chosen valid core sector, with $E=\lambda_{\min}(H_{\mathrm{sim}})$ there, $B=PVQ$ and $H_Q=QH_{\mathrm{sim}}Q|_Q$,
--
--   $$F(E)=-B\,(H_Q-EI_Q)^{-1}B^\dagger,$$
--
--   the energy-dependent effective Hamiltonian obtained by eliminating the excited subspace from the ground-state eigenvalue equation. The inverse is taken on the range of $Q$.
-- source:
--   Hecker, The Complexity of Single-Interaction Hamiltonians, arXiv:2609.39592 (held version, sha256 19ddc444…), §5.1.6, p.63

import Mathlib
import Definitions.Def_SingleInteraction_Gadget_H2eff
import Definitions.Def_SYKEdge_MatrixNorms

namespace SingleInteraction

namespace Gadget

/-- `E = λmin(H_sim)` in the chosen valid core sector (Hecker, *The Complexity of Single-Interaction Hamiltonians*, arXiv:2609.39592 (held version, sha256 19ddc444…), §5.1.6, p.63: "Let `E = λmin(Hsim)` in the
chosen valid core sector").

**Formalization Note** `SYKEdge.lamMin` is the published infimum of `re ⟨v, A v⟩` over unit vectors; `A` is
Hermitian here, so it is the least eigenvalue. -/
noncomputable def Eval (G : Gadget) : ℝ := SYKEdge.lamMin G.Hsimv

/-- The exact energy-dependent effective Hamiltonian `F(E) = −B(H_Q − E I_Q)^{−1}B†`, `B = PVQ`,
`H_Q = QH_simQ|_Q` (Hecker, *The Complexity of Single-Interaction Hamiltonians*, arXiv:2609.39592 (held version, sha256 19ddc444…), §5.1.6, p.63), in the chosen valid core sector.

**Formalization Note** `(H_Q − E I_Q)^{−1}` is `invOn Qexc (Hsimv − E I)`, the inverse of
`Q(Hsimv − E I)Q` on ran `Q`; `B† = QVP` since `V` is Hermitian. -/
noncomputable def Fexact (G : Gadget) (E : ℝ) : Matrix (G.VS → Fin 2) (G.VS → Fin 2) ℂ :=
  -(G.Pzero * G.Vv * G.Qexc *
      invOn G.Qexc (G.Hsimv - ((E : ℝ) : ℂ) • (1 : Matrix (G.VS → Fin 2) (G.VS → Fin 2) ℂ)) *
      G.Qexc * G.Vv * G.Pzero)

end Gadget

end SingleInteraction


