-- Prove2me | Definitions.Def_FairFacilityLoc_medianMechanism
-- name    : FairFacilityLoc_medianMechanism
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:13:16.533299+00:00
-- url     : https://prove2.me/theorems/e273c37d-6621-4863-9974-13fd5fc9b70b
-- title:
--   The coordinate-wise median of the reports of $G_h$
-- statement:
--   In each coordinate, the lower median of the reports of the members of $G_h$, where $h$ is the smallest index with $A_h=\max_jA_j$. Following §2.2 it is written through the cut rule: a set $S$ is winning exactly when $|S\cap G_h|\ge|G_h\setminus S|$.
--
--   **Formalization Note** Proposition 3.29 carries a clause identifying this output with the lower median of the reports of $G_h$. The mechanism is defined in every dimension.
-- source:
--   Yan, Zhou, Fair and Strategyproof Facility Location in Euclidean Space, manuscript (sha256 642a1268…), §2.2, p.16 (PDF p.18); Proposition 3.29, p.50 (PDF p.52)

import Mathlib
import Definitions.Def_FairFacilityLoc_Mechanism
import Definitions.Def_FairFacilityLoc_cutOutput
import Definitions.Def_FairFacilityLoc_heaviestGroup

namespace FairFacilityLoc

/-- **Winning sets of the median of `G_h`** (Yan, Zhou, manuscript, sha256 642a1268…, §2.2, p.16, PDF p.18):
`S` is winning exactly when `|S ∩ G_h| ≥ |G_h ∖ S|`. -/
def IsMedianWinning {n m : ℕ} (G : GroupStructure n m) (S : Finset (Fin n)) : Prop :=
  (G.G (heaviestGroup G) \ S).card ≤ (S ∩ G.G (heaviestGroup G)).card

/-- **The coordinate-wise median of the reports of `G_h`** (§2.2, p.16, PDF p.18; Proposition 3.29, p.50,
PDF p.52), with the lower median for an even number of reports, written through the cut rule as in §2.2.

**Formalization Note.** Proposition 3.29 carries a clause that identifies this output as the median. It is
defined in every dimension, because Proposition 3.29 is stated in every dimension. -/
noncomputable def medianMechanism (d : ℕ) : Mechanism d :=
  fun G x => cutOutput (fun _ S => IsMedianWinning G S) x

end FairFacilityLoc


