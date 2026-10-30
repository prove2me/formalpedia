-- Prove2me | Definitions.Def_LindenReversibility_erBC
-- name    : LindenReversibility_erBC
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:18:56.101841+00:00
-- url     : https://prove2.me/theorems/acf4a206-064b-465a-82af-1d2db4eb8064
-- title:
--   Bob–Claire relative entropy of entanglement $E_r(BC) = E_r(\mathrm{Tr}_A|\psi\rangle\langle\psi|)$
-- statement:
--   For a pure state $\psi$ of the joint system $\mathbb C^A\otimes(\mathbb C^B\otimes\mathbb C^C)$, let $\rho^{BC} = \operatorname{Tr}_A|\psi\rangle\langle\psi|$ be Bob and Claire's reduced state. Then
--
--   $$
--   E_r(BC) = E_r(\rho^{BC}),
--   $$
--
--   the relative entropy of entanglement (11) of the Bob–Claire state.
-- source:
--   Linden, Popescu, Schumacher, Westmoreland, Reversibility of local transformations of multiparticle entanglement, arXiv:quant-ph/9912039v1, eqs. (11), (22), pp.3–4

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_LindenReversibility_relEntEnt

open scoped ENNReal

namespace LindenReversibility

/-- Linden, Popescu, Schumacher, Westmoreland, arXiv:quant-ph/9912039v1, eqs. (11), (22),
pp.3–4: `E_r(BC)`, the relative entropy of entanglement of Bob and Claire's joint state
`ρ^{BC} = Tr_A |ψ⟩⟨ψ|` of a (normalized) joint pure state `ψ`.

**Formalization Note.** Alice is the first factor `A` of `A × (B × C)`;
`QAlgorithms.traceLeft` traces out the first factor. -/
noncomputable def erBC {A B C : Type*} [Fintype A] [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype C] [DecidableEq C] [Nonempty C] (ψ : EuclideanSpace ℂ (A × (B × C))) : ℝ≥0∞ :=
  relEntEnt (QAlgorithms.traceLeft (QAlgorithms.pureDensity ψ))

end LindenReversibility


