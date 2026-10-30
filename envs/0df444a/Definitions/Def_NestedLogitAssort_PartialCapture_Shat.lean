-- Prove2me | Definitions.Def_NestedLogitAssort_PartialCapture_Shat
-- name    : NestedLogitAssort_PartialCapture_Shat
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:43:52.07297+00:00
-- url     : https://prove2.me/theorems/4efbfd24-2c19-458d-9160-a815731c7772
-- title:
--   Candidate assortment $\hat S_i(\epsilon_i)$
-- statement:
--   For a nest $i$ and a capacity $\epsilon$,
--
--   $$
--   \hat S_i(\epsilon)=\{j\in N:\hat z_{ij}(\epsilon)=1\},
--   $$
--
--   the products taken fully by the greedy solution of the continuous knapsack (11); the (at most one) fractional product is left out.
-- source:
--   Davis, Gallego & Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, revised manuscript of June 18, 2013, p. 24 (unnumbered)

import Mathlib
import Definitions.Def_NestedLogitAssort_PartialCapture_zhat

namespace NestedLogitAssort.PartialCapture

/-- **The assortment `Ŝ_i(ϵ_i)`.**
Davis, Gallego & Topaloglu, *Assortment Optimization under Variants of the Nested Logit Model*,
revised manuscript of June 18, 2013, p. 24 (unnumbered): "`Ŝ_i(ϵ_i) = {j ∈ N : ẑ_{ij}(ϵ_i) = 1}`, which includes only the strictly
positive and integer-valued components of `ẑ_i(ϵ_i)`." -/
noncomputable def Shat {M : Type*} {n : ℕ} (I : Instance M n) (i : M) (ε : ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun j => zhat I i ε j = 1)

end NestedLogitAssort.PartialCapture


