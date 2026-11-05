-- Prove2me | Definitions.Def_RotationLadder_Protocol_stopTime
-- name    : RotationLadder_Protocol_stopTime
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:36:38.29082+00:00
-- url     : https://prove2.me/theorems/60965f35-014d-4239-bfdd-35479e4ba54a
-- title:
--   Online cost of a run
-- statement:
--   The online cost of a run with target $Z(\varphi)$ and accuracy $\varepsilon$ is the first time at which the rotation applied so far is accurate enough:
--
--   $$\tau=\min\bigl\{t:\ \text{the accuracy of }Z(\varphi-r_t)\text{ against }Z(\varphi)\text{ is at most }\varepsilon\bigr\},$$
--
--   with value $\infty$ if there is no such time. Each step uses one non-Clifford resource.
-- source:
--   Duclos-Cianci, Svore, A State Distillation Protocol to Implement Arbitrary Single-qubit Rotations, arXiv:1210.1980v1, Sec. III, unnumbered, p. 4, steps 5-6

import Mathlib
import Definitions.Def_RotationLadder_Protocol_accuracy
import Definitions.Def_RotationLadder_Protocol_residual
import Definitions.Def_RotationLadder_Protocol_zRot

namespace RotationLadder.Protocol

/-- **The online cost of a run.**
Duclos-Cianci, Svore, *A State Distillation Protocol to Implement Arbitrary Single-qubit Rotations*,
arXiv:1210.1980v1, Sec. III, p. 4, step 6: "Recurse on steps 3 through 5 until the desired accuracy is reached",
and step 5: each rotation adds "one to the online cost".

`stopTime pick φ ε ω` is the least `t` at which the rotation applied so far, `Z(φ - r_t)`, has
accuracy at most `ε` against the target `Z(φ)`, and `⊤` if there is none.

**Formalization Note.** Deterministic level-`0` steps are counted too: each uses a non-Clifford
gate. The initial distillation of `|H⟩` is not counted (p. 2). -/
noncomputable def stopTime (pick : ℝ → ℕ) (φ ε : ℝ) (ω : Coins) : ℕ∞ :=
  sInf ((fun t : ℕ => (t : ℕ∞)) ''
    {t : ℕ | accuracy (zRot φ) (zRot (φ - residual pick φ ω t)) ≤ ε})

end RotationLadder.Protocol


