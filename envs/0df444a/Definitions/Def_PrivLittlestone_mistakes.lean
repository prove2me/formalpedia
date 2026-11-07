-- Prove2me | Definitions.Def_PrivLittlestone_mistakes
-- name    : PrivLittlestone_mistakes
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:26:28.631603+00:00
-- url     : https://prove2.me/theorems/b1a3cd2f-34b6-4ff5-a8a7-4b9929afd7be
-- title:
--   Number of mistakes $M_T$ on a fixed stream
-- statement:
--   On a fixed stream $z = ((x_t, y_t))_{t=1}^T$, the **number of mistakes** of an online learner with transcript $(g_1, \dots, g_T)$ is
--   $$
--   M_T = \sum_{t=1}^{T} \mathbf 1\{g_t(x_t) \neq y_t\}.
--   $$
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), §1.1, p.1

import Mathlib
import Definitions.Def_PrivLittlestone_transcript

namespace PrivLittlestone

/-- The **number of mistakes** `M_T = ∑_{t=1}^T 1{g_t(x_t) ≠ y_t}` of an online learner on a fixed
length-`T` stream `z = ((x_t, y_t))_t` (He–He, *Private Online Learning of Littlestone Classes
and Matroid Flats*, STOC 2027 submission manuscript (sha256 21480556…c562), §1.1, p.1). -/
def mistakes {X : Type*} {T : ℕ} (A : OnlineLearner X) (z : Fin T → X × Bool) (ω : A.Ω) : ℕ :=
  (Finset.univ.filter fun t : Fin T => transcript A z ω t (z t).1 ≠ (z t).2).card

end PrivLittlestone


