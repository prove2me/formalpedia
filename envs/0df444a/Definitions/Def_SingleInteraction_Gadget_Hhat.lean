-- Prove2me | Definitions.Def_SingleInteraction_Gadget_Hhat
-- name    : SingleInteraction_Gadget_Hhat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:55:17.621206+00:00
-- url     : https://prove2.me/theorems/bc6db46c-b7ae-4e77-89d1-6b32886519c5
-- title:
--   The physical Hamiltonian $\hat H=H_{\mathrm{core}}+H_{\mathrm{anchor}}+V$ of eq. (31)
-- statement:
--   For a gadget, with $h$ the interaction of eq. (30),
--
--   $$H_{\mathrm{core}}=\sum_{x\in\mathcal A}\sum_{y\in\mathcal B}(h_{x,y}+h_{y,x}),\qquad H_{\mathrm{anchor}}=\sum_{c\in\mathcal C}\sum_{x\in\Gamma(c)}(h_{c,x}+h_{x,c}),\qquad V=\sum_{c\in\mathcal C}(h_{u(c),c}+h_{c,v(c)}),$$
--
--   and $\hat H=H_{\mathrm{core}}+H_{\mathrm{anchor}}+V$, where $u(c),v(c)$ are the endpoints of the occurrence of mediator $c$. $\hat H$ is an unweighted sum of copies of $h$ on pairwise distinct ordered pairs of physical qubits, an $\mathrm{SIH}_2$ Hamiltonian.
--
--   **Formalization Note** Every term is an application of $h$ itself; the identities $h_{x,y}+h_{y,x}=2Z_xZ_y$ are consequences, not definitions.
-- source:
--   Hecker, The Complexity of Single-Interaction Hamiltonians, arXiv:2609.39592 (held version, sha256 19ddc444…), §5.1.2, pp.56–57, eq. (31)

import Mathlib
import Definitions.Def_SingleInteraction_Gadget
import Definitions.Def_SingleInteraction_onTuple
import Definitions.Def_SingleInteraction_hSIH

namespace SingleInteraction

namespace Gadget

/-- `H_core = Σ_{x∈𝒜} Σ_{y∈ℬ} (h_{x,y} + h_{y,x})` (Hecker, *The Complexity of Single-Interaction Hamiltonians*, arXiv:2609.39592 (held version, sha256 19ddc444…), §5.1.2, p.56). -/
noncomputable def Hcore (G : Gadget) : Matrix (G.Qb → Fin 2) (G.Qb → Fin 2) ℂ :=
  ∑ x : Fin G.S, ∑ y : Fin G.S,
    (onTuple hSIH ![G.coreA x, G.coreB y] + onTuple hSIH ![G.coreB y, G.coreA x])

/-- `H_anchor = Σ_{c∈𝒞} Σ_{x∈Γ(c)} (h_{c,x} + h_{x,c})` (Hecker, *The Complexity of Single-Interaction Hamiltonians*, arXiv:2609.39592 (held version, sha256 19ddc444…), §5.1.2, p.57). -/
noncomputable def Hanchor (G : Gadget) : Matrix (G.Qb → Fin 2) (G.Qb → Fin 2) ℂ :=
  ∑ c : G.Med, ∑ x ∈ G.Γ c,
    (onTuple hSIH ![G.med c, G.anchor c x] + onTuple hSIH ![G.anchor c x, G.med c])

/-- The active edges `V = Σ_{c∈𝒞} (h_{u(c),c} + h_{c,v(c)})` (Hecker, *The Complexity of Single-Interaction Hamiltonians*, arXiv:2609.39592 (held version, sha256 19ddc444…), §5.1.2, p.57). -/
noncomputable def Vact (G : Gadget) : Matrix (G.Qb → Fin 2) (G.Qb → Fin 2) ℂ :=
  ∑ c : G.Med,
    (onTuple hSIH ![G.work (G.u c), G.med c] + onTuple hSIH ![G.med c, G.work (G.v c)])

/-- The physical Hamiltonian `Ĥ = H_core + H_anchor + V` of eq. (31) (Hecker, *The Complexity of Single-Interaction Hamiltonians*, arXiv:2609.39592 (held version, sha256 19ddc444…), §5.1.2, p.57), an
unweighted sum of applications of the fixed interaction `h = Z⊗Z + X⊗Y − Y⊗X` of eq. (30) to ordered
pairs of physical qubits.

**Formalization Note** Every term is `onTuple hSIH ![p, q] = h_{p,q}` (first tensor factor on `p`); the
identities `h_{x,y} + h_{y,x} = 2Z_xZ_y` (p.56) are consequences, not definitions. `Hcore`, `Hanchor`,
`Vact` are the three components. -/
noncomputable def Hhat (G : Gadget) : Matrix (G.Qb → Fin 2) (G.Qb → Fin 2) ℂ :=
  G.Hcore + G.Hanchor + G.Vact

end Gadget

end SingleInteraction


