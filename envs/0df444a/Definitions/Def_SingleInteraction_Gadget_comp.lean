-- Prove2me | Definitions.Def_SingleInteraction_Gadget_comp
-- name    : SingleInteraction_Gadget_comp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:55:14.246196+00:00
-- url     : https://prove2.me/theorems/8767bc49-57a9-47f3-a232-eb8f2189f93b
-- title:
--   Restriction to a core sector
-- statement:
--   A core configuration is a computational-basis state $z$ of the $2S$ core qubits. The isometry $\iota_z$ sends a basis state of the work and mediator qubits to the same state with the core placed in $z$, and an operator $A$ on all physical qubits restricts to the sector $z$ as
--
--   $$A|_z=\iota_z^\dagger A\,\iota_z,$$
--
--   an operator on the work and mediator registers. The valid configurations are $|0\rangle^{\otimes S}_{\mathcal A}|1\rangle^{\otimes S}_{\mathcal B}$ (the chosen one) and $|1\rangle^{\otimes S}_{\mathcal A}|0\rangle^{\otimes S}_{\mathcal B}$; every other configuration is incorrect.
--
--   **Formalization Note** That $\hat H$ commutes with the core $Z$ operators, so that $A|_z$ is a diagonal block, is a consequence to be proved.
-- source:
--   Hecker, The Complexity of Single-Interaction Hamiltonians, arXiv:2609.39592 (held version, sha256 19ddc444…), §5.1.3, pp.58–59

import Mathlib
import Definitions.Def_SingleInteraction_Gadget

namespace SingleInteraction

namespace Gadget

/-- A computational-basis configuration `z ∈ {0,1}^{𝒜∪ℬ}` of the core (`Sum.inl` = `𝒜`, `Sum.inr` = `ℬ`). -/
abbrev CoreConfig (G : Gadget) : Type := Fin G.S ⊕ Fin G.S → Fin 2

/-- The basis state of all physical qubits obtained from a basis state `t` of the work and mediator
qubits by placing the core in configuration `z`. -/
def insertCore (G : Gadget) (z : G.CoreConfig) (t : G.VS → Fin 2) : G.Qb → Fin 2 :=
  Sum.elim (fun i => t (Sum.inl i)) (Sum.elim z (fun c => t (Sum.inr c)))

/-- The isometry `ι_z : |t⟩ ↦ |t⟩ ⊗ |z⟩_core` from the work and mediator register into the full register. -/
def iso (G : Gadget) (z : G.CoreConfig) : Matrix (G.Qb → Fin 2) (G.VS → Fin 2) ℂ :=
  fun s t => if s = G.insertCore z t then 1 else 0

/-- The valid core configuration `|0⟩^{⊗S}_𝒜 |1⟩^{⊗S}_ℬ` chosen in the analysis (Hecker, *The Complexity of Single-Interaction Hamiltonians*, arXiv:2609.39592 (held version, sha256 19ddc444…), §5.1.3, p.58). -/
def zval (G : Gadget) : G.CoreConfig := Sum.elim (fun _ => 0) (fun _ => 1)

/-- The other valid core configuration `|1⟩^{⊗S}_𝒜 |0⟩^{⊗S}_ℬ` (Hecker, *The Complexity of Single-Interaction Hamiltonians*, arXiv:2609.39592 (held version, sha256 19ddc444…), §5.1.3, p.58). -/
def zval' (G : Gadget) : G.CoreConfig := Sum.elim (fun _ => 1) (fun _ => 0)

/-- The restriction of an operator on all physical qubits to the core sector `z`: `ι_z† A ι_z`, an operator
on the work and mediator register (Hecker, *The Complexity of Single-Interaction Hamiltonians*, arXiv:2609.39592 (held version, sha256 19ddc444…), §5.1.3, p.59: "Henceforth, we restrict our analysis to this
sector, with the core qubits fixed to `|0⟩^{⊗S}_𝒜 |1⟩^{⊗S}_ℬ`. All subsequent operators are understood as
acting on the work and mediator registers"; eq. (33), "`Hsim|incorrect`").

**Formalization Note** `ι_z` inserts the fixed core bits `z`. For an operator commuting with every core
`Z` (as `Ĥ` does, p.58), `comp z A` is its block on the sector `z`; this is a consequence to be proved,
not assumed. -/
def comp (G : Gadget) (z : G.CoreConfig) (A : Matrix (G.Qb → Fin 2) (G.Qb → Fin 2) ℂ) :
    Matrix (G.VS → Fin 2) (G.VS → Fin 2) ℂ :=
  Matrix.conjTranspose (G.iso z) * A * G.iso z

end Gadget

end SingleInteraction


