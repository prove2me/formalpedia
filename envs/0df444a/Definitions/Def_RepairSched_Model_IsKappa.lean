-- Prove2me | Definitions.Def_RepairSched_Model_IsKappa
-- name    : RepairSched_Model_IsKappa
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:46:38.233988+00:00
-- url     : https://prove2.me/theorems/ad39f5e9-6e1d-456f-b252-c344a21a237c
-- title:
--   The tie-broken index in $\arg\min_i\{b_i\mu_i-\lambda_i y\}$
-- statement:
--   An index $i$ has this property at slope $y$ if it minimizes $b_i\mu_i-\lambda_iy$, has the largest $\lambda$ among the minimizers, and is the least index among those.
--
--   **Formalization Note** The paper fixes the tie-break only by "we can choose κ(w) such that β becomes right continuous" (OA p.26). To the right of a crossing of two lines $b_i\mu_i-\lambda_iy$, the line with the larger $\lambda_i$ is the lower one, and $f'$ is strictly increasing on $[0,B]$, so the largest-$\lambda$ rule is that choice.
-- source:
--   Özkan and van Houtum, Joint Inventory and Scheduling Control in a Repair Facility, SSRN 3784144 (2023), Lemma 1 Part ii, p.21; OA p.26 (PDF p.66)

import Mathlib
import Definitions.Def_RepairSched_Model

namespace RepairSched

/-- **`i` is the tie-broken element of `arg minᵢ {bᵢμᵢ − λᵢy}`**: it minimizes `bᵢμᵢ − λᵢy`,
has the largest `λ` among the minimizers, and is the least index among those.
Özkan and van Houtum, *Joint Inventory and Scheduling Control in a Repair Facility*, SSRN 3784144 (2023), Lemma 1 Part ii, p.21, and OA p.26 (PDF p.66).

**Formalization Note.** The paper fixes this choice only by "we can choose κ(w) such that
β(λ,µ,s) becomes right continuous" (OA p.26). Right of a crossing of two lines `bᵢμᵢ − λᵢy` the
line with the larger `λᵢ` is the lower one, and `f′` is strictly increasing on `[0,B]`
(Lemma 2 Part ii), so the largest-`λ` rule is that choice. -/
def Model.IsKappa {n : ℕ} (M : Model n) (y : ℝ) (i : Fin n) : Prop :=
  (∀ k, M.b i * M.mu i - M.lam i * y ≤ M.b k * M.mu k - M.lam k * y) ∧
    ∀ k, M.b k * M.mu k - M.lam k * y = M.b i * M.mu i - M.lam i * y →
      M.lam k ≤ M.lam i ∧ (M.lam k = M.lam i → i ≤ k)

end RepairSched


