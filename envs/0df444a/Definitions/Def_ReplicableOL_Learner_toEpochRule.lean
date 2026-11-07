-- Prove2me | Definitions.Def_ReplicableOL_Learner_toEpochRule
-- name    : ReplicableOL_Learner_toEpochRule
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:46:34.770505+00:00
-- url     : https://prove2.me/theorems/0dce0e0c-7925-4ea3-b23b-10e640c8c75e
-- title:
--   The epoch rule of a learner at a seed
-- statement:
--   At a fixed seed $r$, a learner on the two-expert losses of Construction C induces an epoch rule: position $i$ of epoch $j$ is the action at round $(j-1)L+i$ on the loss prefix built from the earlier blocks $h$ and the first $i-1$ bits of $s$. This rule is round-causal.
--
--   **Formalization Note** Position `i` of epoch `j` is round `jL + i` (0-based). The prefix passed to the learner is the loss sequence of the bits `(h, s_1, …, s_i)`, with `ℓ = (B, 1 − B)`. The verification file proves that this rule reproduces `traj` on `embed`.
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Sec. 4.1, p.15

import Mathlib
import Definitions.Def_ReplicableOL_Learner
import Definitions.Def_ReplicableOL_EpochRule

namespace ReplicableOL

/-- **The epoch rule of a learner at a seed.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Sec. 4.1, p.15. `Φ_j(h; s) := (a_{(j−1)L+1}(h, r), a_{(j−1)L+2}((h, s_1), r), …, a_{jL}((h, s_1, …, s_{L−1}), r))`.

**Formalization Note.** Position `i` of epoch `j` is round `jL + i` (0-based). The prefix passed to the learner is the loss sequence of the bits `(h, s_1, …, s_i)`, with `ℓ = (B, 1 − B)`. The verification file proves that this rule reproduces `traj` on `embed`. -/
noncomputable def Learner.toEpochRule {T : ℕ} {R : Type*} [MeasurableSpace R] (𝓛 : Learner 2 T R)
    (L : ℕ) (r : R) : EpochRule (T / L) L :=
  fun j h s i =>
    𝓛.act ⟨j.val * L + i.val, by
        have hj := j.2
        have hi := i.2
        calc j.val * L + i.val < j.val * L + L := by omega
          _ = (j.val + 1) * L := by ring
          _ ≤ (T / L) * L := Nat.mul_le_mul_right _ hj
          _ ≤ T := Nat.div_mul_le_self _ _⟩
      (fun t' =>
        let b : Bool :=
          if hlt : t'.val / L < j.val then
            h ⟨t'.val / L, hlt⟩ ⟨t'.val % L, Nat.mod_lt _ i.pos⟩
          else s ⟨t'.val % L, Nat.mod_lt _ i.pos⟩
        let B : ℝ := if b then 1 else 0
        ![B, 1 - B])
      r

end ReplicableOL


