-- Prove2me | Definitions.Def_FairVaccineReserves_DA_Preferences
-- name    : FairVaccineReserves_DA_Preferences
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T14:53:34.932934+00:00
-- url     : https://prove2.me/theorems/027d516c-0734-4865-ab65-44970a3eb496
-- title:
--   Compatible artificial preference profiles
-- statement:
--   An artificial preference profile assigns each patient $i$ a full strict linear order $\succ_i$ on all categories together with $\varnothing$. A profile is compatible with the reserve system if
--
--   $$\forall i,c,\quad c\succ_i\varnothing\ \Longleftrightarrow\ i\pi_c\varnothing.$$
--
--   All orders of eligible categories may vary independently across patients. Ineligible categories lie below the outside option and retain arbitrary relative ranks. These preferences are auxiliary orders, not preferences over the physically identical medical units. The definition imposes no condition on the outcome of an algorithm.
--
--   **Formalization Note** Each full order is represented by a rank bijection on `Option (Fin m)`, with smaller ranks better; compatibility is a separate predicate.
-- source:
--   Pathak, Sönmez, Ünver and Yenmez, arXiv:2008.00374v3 (1 July 2023; draft May 2023), https://arxiv.org/abs/2008.00374v3, §3.5, printed/PDF pp. 17–18

import Definitions.Def_FairVaccineReserves_DA_Model

namespace FairVaccineReserves.DA

/-- Full artificial strict orders, including all categories below the outside option. -/
abbrev PreferenceProfile (n m : ℕ) :=
  Fin n → (Option (Fin m) ≃ Fin (m + 1))

/-- Section 3.5: exactly the eligible categories are ranked above unassignment. -/
def ReserveSystem.Compatible {n m : ℕ} (R : ReserveSystem n m)
    (P : PreferenceProfile n m) : Prop :=
  ∀ i c, (P i (some c) < P i none) ↔ R.Eligible i c

end FairVaccineReserves.DA


