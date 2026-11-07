-- Prove2me | Definitions.Def_GenSort_TieRules_Valid
-- name    : GenSort_TieRules_Valid
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:29:28.828845+00:00
-- url     : https://prove2.me/theorems/6d7c6e10-900f-4c58-ba8a-7836810b3893
-- title:
--   Validity of the choices of a pass
-- statement:
--   The choice rules of a pass are **valid** if (1) $Q$ always selects $t$ highest-score neighbours (in the sense of the top-$t$ selection) and (2) $\tau_{\mathrm{sel}}$ always returns an ordering $\tau'$ whose candidate removal set $C_{\tau'}$ misses the fewest validation edges among all orderings of $S$, validation edges counted with multiplicity: "We choose the candidate removal set $C_{\tau'}$ that misses the fewest validation edges".
-- source:
--   Khanna, Putterman, Song, A Near-Optimal Generalized Sorting Algorithm, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), §3.4 step 4, p.8 and §3.5 step 3, p.10 (PDF pp.10, 12)

import Mathlib
import Definitions.Def_GenSort_TieRules
import Definitions.Def_GenSort_score
import Definitions.Def_GenSort_IsTopSelection
import Definitions.Def_GenSort_removalSet

namespace GenSort

/-- **Validity of the arbitrary choices of a pass**, Khanna–Putterman–Song, *A Near-Optimal Generalized Sorting Algorithm*, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), §3.4 step 4, p.8 and §3.5 step 3, p.10
(PDF pp.10, 12): `Q` selects `t` highest-score neighbours for every edge set, sample and ordering,
and `τsel` returns an ordering `τ'` whose candidate removal set `C_τ'` misses the fewest of the
validation edges (counted with multiplicity) among all orderings of `S`. -/
def TieRules.Valid {n : ℕ} {L R : Type*} {s : ℕ} (ρ : TieRules L R s) (ℓ : L → Fin n)
    (r : R → Fin n) (π : Equiv.Perm (Fin n)) (t : ℕ) : Prop :=
  open Classical in
  (∀ (E : Finset (L × R)) (S : Fin s → R) (τ : Equiv.Perm (Fin s)),
      IsTopSelection E (score E S τ) t (ρ.Q E S τ)) ∧
  ∀ (E : Finset (L × R)) (S : Fin s → R) (val : List (L × R)) (τ : Equiv.Perm (Fin s)),
    (val.filter fun p => decide (p ∉ removalSet E ℓ r π S (ρ.Q E S (ρ.τsel E S val)))).length ≤
      (val.filter fun p => decide (p ∉ removalSet E ℓ r π S (ρ.Q E S τ))).length

end GenSort


