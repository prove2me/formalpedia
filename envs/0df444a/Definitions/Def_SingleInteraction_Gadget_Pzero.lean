-- Prove2me | Definitions.Def_SingleInteraction_Gadget_Pzero
-- name    : SingleInteraction_Gadget_Pzero
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:55:04.612202+00:00
-- url     : https://prove2.me/theorems/f6a553b6-7642-4b7d-a734-f567f5911072
-- title:
--   Defect projectors, defect number and the zero-defect projector $P$
-- statement:
--   In the chosen valid sector each mediator $c$ has a preferred bit $b_c$: $1$ if $c$ is anchored to $\mathcal A$, $0$ if anchored to $\mathcal B$. On the work and mediator registers,
--
--   $$\Pi^c=(|1-b_c\rangle\langle1-b_c|)_c,\qquad\mathcal N=\sum_{c\in\mathcal C}\Pi^c,\qquad P=I_{\mathrm{work}}\otimes|\Omega\rangle\langle\Omega|,\qquad Q=I-P,$$
--
--   where $|\Omega\rangle=\bigotimes_c|b_c\rangle_c$. $P$ projects onto the zero-defect subspace and $Q$ onto states with at least one mediator defect.
-- source:
--   Hecker, The Complexity of Single-Interaction Hamiltonians, arXiv:2609.39592 (held version, sha256 19ddc444…), §5.1.3, pp.58–59

import Mathlib
import Definitions.Def_SingleInteraction_Gadget

namespace SingleInteraction

namespace Gadget

/-- The preferred bit `b_c` of mediator `c` in the chosen valid sector `|0⟩^{⊗S}_𝒜 |1⟩^{⊗S}_ℬ`: `1` if `c` is
anchored to `𝒜`, `0` if anchored to `ℬ` (Hecker, *The Complexity of Single-Interaction Hamiltonians*, arXiv:2609.39592 (held version, sha256 19ddc444…), §5.1.3, p.58). -/
def bpref (G : Gadget) (c : G.Med) : Fin 2 := if c.2.1 then 1 else 0

/-- The defect projector `Π^c = (|1 − b_c⟩⟨1 − b_c|)_c` of mediator `c` on the work and mediator register
(Hecker, *The Complexity of Single-Interaction Hamiltonians*, arXiv:2609.39592 (held version, sha256 19ddc444…), §5.1.3, p.59). -/
def Pi (G : Gadget) (c : G.Med) : Matrix (G.VS → Fin 2) (G.VS → Fin 2) ℂ :=
  Matrix.diagonal fun t => if t (Sum.inr c) = G.bpref c then 0 else 1

/-- The mediator-defect number operator `𝒩 = Σ_{c∈𝒞} Π^c` (Hecker, *The Complexity of Single-Interaction Hamiltonians*, arXiv:2609.39592 (held version, sha256 19ddc444…), §5.1.3, p.59). -/
def Ncount (G : Gadget) : Matrix (G.VS → Fin 2) (G.VS → Fin 2) ℂ :=
  ∑ c : G.Med, G.Pi c

/-- `P = I_work ⊗ |Ω⟩⟨Ω|`, with `|Ω⟩ = ⊗_c |b_c⟩_c` the state with every mediator in its preferred state:
the projector onto the zero-defect subspace of the work and mediator register (Hecker, *The Complexity of Single-Interaction Hamiltonians*, arXiv:2609.39592 (held version, sha256 19ddc444…), §5.1.3, p.59).

**Formalization Note** `P` is diagonal: `1` on basis states whose mediator bits are all preferred, `0`
otherwise; `Qexc = 1 − P` is `Q = I − P`. -/
def Pzero (G : Gadget) : Matrix (G.VS → Fin 2) (G.VS → Fin 2) ℂ :=
  Matrix.diagonal fun t => if ∀ c : G.Med, t (Sum.inr c) = G.bpref c then 1 else 0

/-- `Q = I − P`, the projector onto states with at least one mediator defect (Hecker, *The Complexity of Single-Interaction Hamiltonians*, arXiv:2609.39592 (held version, sha256 19ddc444…), §5.1.3, p.59). -/
def Qexc (G : Gadget) : Matrix (G.VS → Fin 2) (G.VS → Fin 2) ℂ :=
  1 - G.Pzero

end Gadget

end SingleInteraction


