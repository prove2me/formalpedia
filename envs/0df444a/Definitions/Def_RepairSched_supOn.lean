-- Prove2me | Definitions.Def_RepairSched_supOn
-- name    : RepairSched_supOn
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:45:08.931277+00:00
-- url     : https://prove2.me/theorems/fa1cad3a-be8e-4d13-bbbe-dc30fb7e40cb
-- title:
--   $\sup_{w\ge0}g(w)$ in the extended reals
-- statement:
--   This is the supremum
--   $$\sup_{w\in\mathbb R_+}g(w)\in(-\infty,+\infty],$$
--   used for the case distinction of Lemma A.3.6.
--
--   **Formalization Note** The supremum can be $+\infty$, and a real supremum would return $0$ there, so it is taken in `EReal`.
-- source:
--   Özkan and van Houtum, Joint Inventory and Scheduling Control in a Repair Facility, SSRN 3784144 (2023), Lemmas A.3.6 and A.3.8, OA pp.10, 15

import Mathlib

open Set

namespace RepairSched

/-- **`sup_{w∈ℝ₊} g(w)` in the extended reals.**
Özkan and van Houtum, *Joint Inventory and Scheduling Control in a Repair Facility*, SSRN 3784144 (2023), Lemmas A.3.6 and A.3.8, OA pp.10, 15.

**Formalization Note.** The supremum can be `+∞`, and a real `⨆` would return `0` there, so it
is taken in `EReal`, indexed by the nonempty set `[0,∞)`. -/
noncomputable def supOn (g : ℝ → ℝ) : EReal :=
  ⨆ w : Ici (0 : ℝ), ((g w : ℝ) : EReal)

end RepairSched


