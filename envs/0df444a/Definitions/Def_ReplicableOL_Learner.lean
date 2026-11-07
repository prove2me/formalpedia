-- Prove2me | Definitions.Def_ReplicableOL_Learner
-- name    : ReplicableOL_Learner
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:43:34.292942+00:00
-- url     : https://prove2.me/theorems/64303224-8aa1-4847-bf62-d634a55aa281
-- title:
--   Online learner with a seed
-- statement:
--   A **learner** for $n$ experts and $T$ rounds, with seed space $\mathcal R$, is a family of maps $a_t(S_{<t},r)\in[n]$, $t\le T$, where $S_{<t}=(\ell_1,\dots,\ell_{t-1})$ is the sequence of loss vectors seen so far and $r\in\mathcal R$ is the seed. Each map is jointly measurable. The seed is drawn once, independently of the data, and is all of the learner's randomness (hypothesis (H2) of the paper).
--
--   Every result of the mission quantifies over these objects.
--
--   **Formalization Note** Rounds are 0-based (`t : Fin T`), so the prefix at round `t` is indexed by `Fin t`; causality is in the type. Losses are typed `ℝ` and read only on `[0,1]`: a learner on `[0,1]` extends measurably to `ℝ`, and every law in this mission is carried by `[0,1]`.
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Sec. 2.1, p.6

import Mathlib

namespace ReplicableOL

/-- **Online learner with a seed.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Sec. 2.1, p.6. The action at round `t` is `a_t = a_t(S_{<t}, R) ∈ [n]`, jointly measurable in the loss prefix and the seed; the seed is all of the learner's randomness (H2).

**Formalization Note.** Rounds are 0-based (`t : Fin T`), so the prefix at round `t` is indexed by `Fin t`; causality is in the type. Losses are typed `ℝ` and read only on `[0,1]`: a learner on `[0,1]` extends measurably to `ℝ`, and every law in this mission is carried by `[0,1]`. -/
structure Learner (n T : ℕ) (R : Type*) [MeasurableSpace R] where
  /-- The action at round `t`, from the loss prefix and the seed. -/
  act : (t : Fin T) → (Fin t → Fin n → ℝ) → R → Fin n
  /-- Each action is jointly measurable in the prefix and the seed. -/
  act_meas : ∀ t, Measurable (Function.uncurry (act t))

end ReplicableOL


