-- Prove2me | Definitions.Def_CondEntanglement_csValues
-- name    : CondEntanglement_csValues
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T16:04:31.579817+00:00
-- url     : https://prove2.me/theorems/48fb8ee5-df72-4580-b860-f879b6798634
-- title:
--   The value set of $C_S$: increments of all extensions
-- statement:
--   Let $\rho$ be an $n$-party state on $A_1\cdots A_n$. The value set of $C_S$ at $\rho$ is
--
--   $$
--   \mathcal V(\rho)=\bigl\{\,S_n(A_1A_1':\cdots:A_nA_n')_\omega-S_n(A_1':\cdots:A_n')_\omega\;:\;\omega \text{ a state on } A_1A_1'\cdots A_nA_n',\ \operatorname{Tr}_{A_1'\cdots A_n'}\omega=\rho\,\bigr\},
--   $$
--
--   the primed systems $A_i'$ ranging over all finite dimensions $d_i\ge1$, with no common bound. These are the numbers whose infimum is $C_S(\rho)$ (p.4); the extensions are those of Definition 1 (p.1), "all states satisfying the equation $\operatorname{Tr}_{A'B'}\rho_{AA'BB'}=\rho_{AB}$", with one primed system per party.
--
--   **Formalization Note** The primed system of party $i$ is `Fin (d i)` with `0 < d i`, every finite system up to relabeling. The state $\omega$ is any positive semidefinite trace-one matrix (`QAlgorithms.IsDensityMatrix`); no purity, product or classicality restriction. The trace over the primed systems is the published `unprimedMarginal`, and the increment is `CondEntanglement.dualIncrement`.
-- source:
--   Yang–Horodecki–Wang, Conditional Entanglement, arXiv:quant-ph/0701149v3, definition of C_S, p.4; Definition 1 and the sentence after (1), p.1

import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P33
import Definitions.Def_CondEntanglement_dualIncrement

open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P33

namespace CondEntanglement

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Yang–Horodecki–Wang, *Conditional Entanglement*, arXiv:quant-ph/0701149v3, p.4: the set over
which the infimum defining `C_S` is taken,
"C_S = inf{Sₙ(A₁A′₁ : · · · : AₙA′ₙ) − Sₙ(A′₁ : · · · : A′ₙ)}", the infimum being, as for
Definition 1 (p.1), "taken over all extensions of ρ_{A₁⋯Aₙ}, i.e., over all states satisfying the
equation Tr_{A′₁⋯A′ₙ} ρ_{A₁A′₁⋯AₙA′ₙ} = ρ_{A₁⋯Aₙ}", with one primed register `A′ᵢ` per party.

A real `v` belongs to the set when there are positive dimensions `dᵢ` of the primed registers and
a density matrix `ω` on `∏ᵢ (Dᵢ × Fin dᵢ)` whose unprimed marginal is `ρ` and with
`v = dualIncrement ω`.

**Formalization Note.** Every finite primed register is, up to relabeling, some `Fin dᵢ` with
`0 < dᵢ`; the dimensions are arbitrary and have no common cap. `ω` is any density matrix
(`QAlgorithms.IsDensityMatrix`: positive semidefinite, trace one); no purity, product or
classicality restriction is imposed. The trace over `A′₁⋯A′ₙ` is the published
`unprimedMarginal`. No factor `1/2` appears, as on p.4. -/
def csValues {n : ℕ} {D : Fin n → Type} [∀ i, Fintype (D i)]
    (ρ : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) : Set ℝ :=
  {v | ∃ d : Fin n → ℕ, (∀ i, 0 < d i) ∧
    ∃ ω : Matrix (RegisterBasis (fun i => D i × Fin (d i)))
        (RegisterBasis (fun i => D i × Fin (d i))) ℂ,
      IsDensityMatrix ω ∧ unprimedMarginal ω = ρ ∧ v = dualIncrement ω}

end CondEntanglement


