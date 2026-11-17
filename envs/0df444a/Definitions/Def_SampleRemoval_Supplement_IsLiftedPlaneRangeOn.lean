-- Prove2me | Definitions.Def_SampleRemoval_Supplement_IsLiftedPlaneRangeOn
-- name    : SampleRemoval_Supplement_IsLiftedPlaneRangeOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T02:19:27.673045+00:00
-- url     : https://prove2.me/theorems/02116328-5535-4686-a6a4-55e484126ff1
-- title:
--   Lifted-plane range in a sub-instance
-- statement:
--   A retained set $S$ is a **lifted-plane range** relative to a finite sub-instance $U$ when some strict plane cut selects exactly its saddle lifts:
--
--   $$S=\{i\in U:c_1x_iy_i+c_2x_i+c_3y_i+c_4<0\}.$$
--
--   Taking $U=[n]$ gives the paper's ordinary lifted-plane range; allowing a stated $U$ expresses Theorem 5.7's persistence claim.
-- source:
--   Xu, Gao, Hu, Rounding, Ranges, and Exact Sample-Removal Audits for Least Squares, STOC 2027 submission (manuscript sha256 dcd33acebc1ccdc626c7ee41bfabc29795abe2e1cd9267d8cbd66d98f81c4b26), Section 5.3, p.10 (PDF p.12)

import Mathlib

set_option autoImplicit false

namespace SampleRemoval.Supplement

/-- `S` is a lifted-plane range relative to the finite sub-instance `U`: one strict plane cut in
the saddle lift selects exactly `S` among `U` (Xu, Gao, Hu, STOC 2027 submission, §5.3, p.10
(PDF p.12)). Taking `U=univ` is the paper's ordinary lifted-plane range. -/
def IsLiftedPlaneRangeOn {n : ℕ} (p : Fin n → ℝ × ℝ) (U S : Finset (Fin n)) : Prop :=
  S ⊆ U ∧ ∃ c : Fin 4 → ℝ, ∀ i ∈ U,
    (i ∈ S ↔ c ⟨0, by omega⟩ * (p i).1 * (p i).2 + c ⟨1, by omega⟩ * (p i).1 +
      c ⟨2, by omega⟩ * (p i).2 + c ⟨3, by omega⟩ < 0)

end SampleRemoval.Supplement


