-- Prove2me | Definitions.Def_PrivLittlestone_phaseCount
-- name    : PrivLittlestone_phaseCount
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:29:33.426096+00:00
-- url     : https://prove2.me/theorems/3f3645ba-d112-4115-90c1-4f64d391f527
-- title:
--   Reset phase counter $q_t$ on the continuation
-- statement:
--   On the continuation with fixed aggregate $g$ from the phase start $t_0$, the **reset counter** $q_t$ is the number of rounds $i$ with $t_0 \le i \le t$ on which $g$ errs on the supplied record.
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), proof of Lemma B.2, p.22

import Mathlib
import Definitions.Def_PrivLittlestone_contInput

namespace PrivLittlestone

/-- The **reset phase counter** `q_t` on the continuation with fixed aggregate `g` from the
phase-start round `t₀` (He–He, *Private Online Learning of Littlestone Classes and Matroid
Flats*, STOC 2027 submission manuscript (sha256 21480556…c562), proof of Lemma B.2, p.22): the
number of rounds `i` with `t₀ ≤ i ≤ t` on which `g` errs on the continuation's record. -/
def phaseCount {X : Type*} {T : ℕ} (inp : InputStrategy X T) (past : Fin T → X → Bool) (t₀ : ℕ)
    (g : X → Bool) (t : ℕ) : ℕ :=
  (Finset.univ.filter fun i : Fin T => t₀ ≤ (i : ℕ) ∧ (i : ℕ) ≤ t ∧
    g (contInput inp past t₀ g i).1 ≠ (contInput inp past t₀ g i).2).card

end PrivLittlestone


