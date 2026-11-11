-- Prove2me | Definitions.Def_SybilClinch_TwoSidedOutcome
-- name    : SybilClinch_TwoSidedOutcome
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:45:27.972251+00:00
-- url     : https://prove2.me/theorems/11460d7d-d4fc-46d4-8597-b53408cbd6b3
-- title:
--   Outcome of the two-sided AMM clinching mechanism
-- statement:
--   On a reported profile, ineligible identities receive zero, and:
--
--   1. if $D_Y\ge D_X$ (sell-$Y$ dominant, $M=D_X$), every eligible sell-$X$ identity gets $S_{X,i}=r_i$, $R_{Y,i}=p_0r_i$, and the eligible sell-$Y$ identities get $(S_{Y,i},R_{X,i})=(y_i,x_i)$ from a completed run of the dominant auction on $\widetilde C_M$;
--   2. if $D_Y<D_X$ (sell-$X$ dominant, $M=D_Y$), every eligible sell-$Y$ identity pays $q_i$ and receives $q_i/p_0$, and the eligible sell-$X$ identities get $R_{Y,i}=x^{\rm rev}_i$, $S_{X,i}=y^{\rm rev}_i$ from a completed run of the reverse auction on $\widetilde C^{\rm rev}_M$.
--
--   All transfers are settled simultaneously, so minority proceeds cannot finance another order.
--
--   **Formalization Note** The mechanism is a relation: an outcome is any outcome of a completed run.
-- source:
--   Zhang, Li, Shi, Zhang, Xia, Han, Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design, arXiv:2610.36629 (held copy sha256 93c5d05b…), §5.1–§5.2, pp.25–27 (PDF pp.27–29)

import Mathlib
import Definitions.Def_SybilClinch_domYProfile
import Definitions.Def_SybilClinch_domXProfile
import Definitions.Def_SybilClinch_domYMech
import Definitions.Def_SybilClinch_domXMech
import Definitions.Def_SybilClinch_IsRun
import Definitions.Def_SybilClinch_Fill

set_option autoImplicit false

open Filter Topology Set

namespace SybilClinch

/-- Zhang, Li, Shi, Zhang, Xia, Han, *Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design*, arXiv:2610.36629 (held copy sha256 93c5d05b…), §5.1–§5.2, printed pp.25–27 (PDF pp.27–29): `f` is an outcome of the two-sided AMM
clinching mechanism on the reported profile `(ids, rep)`.

Ineligible identities receive zero. If `D_Y ≥ D_X` (sell-`Y` dominant; ties designate sell-`X` as
the minority), each eligible sell-`X` identity gets `S_{X,i} = rᵢ`, `R_{Y,i} = p₀rᵢ`, and the
eligible sell-`Y` identities get `(S_{Y,i}, R_{X,i}) = (yᵢ, xᵢ)` from a completed run of the
dominant auction on `C̃_M`, `M = D_X`. If `D_Y < D_X`, each eligible sell-`Y` identity pays `qᵢ`
and receives `qᵢ/p₀`, and the eligible sell-`X` identities get `R_{Y,i} = x^rev_i`,
`S_{X,i} = y^rev_i` from a completed run of the reverse auction on `C̃^rev_M`, `M = D_Y`.

**Formalization Note.** The mechanism is relational: `f` ranges over the outcomes of all completed
runs. Settlement (rule 3) is simultaneous, so minority proceeds cannot finance other orders. -/
noncomputable def TwoSidedOutcome (A : AdmissibleAMM) (ids : Finset ℕ) (rep : ℕ → Report)
    (f : ℕ → Fill) : Prop :=
  (∀ i, i ∉ eligY A ids rep → i ∉ eligX A ids rep → f i = ⟨0, 0⟩) ∧
  (demandX A ids rep ≤ demandY A ids rep →
    (∀ i ∈ eligX A ids rep, f i = ⟨(rep i).bud, A.p0 * (rep i).bud⟩) ∧
    ∃ R : Run, IsRun (domYMech A ids rep) (domYProfile A ids rep) R ∧
      ∀ i ∈ eligY A ids rep, f i = ⟨R.pay (domYMech A ids rep) i R.pf, R.x i R.pf⟩) ∧
  (demandY A ids rep < demandX A ids rep →
    (∀ i ∈ eligY A ids rep, f i = ⟨(rep i).bud, (rep i).bud / A.p0⟩) ∧
    ∃ R : Run, IsRun (domXMech A ids rep) (domXProfile A ids rep) R ∧
      ∀ i ∈ eligX A ids rep, f i = ⟨R.pay (domXMech A ids rep) i R.pf, R.x i R.pf⟩)

end SybilClinch


