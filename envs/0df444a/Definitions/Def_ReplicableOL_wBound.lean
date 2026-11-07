-- Prove2me | Definitions.Def_ReplicableOL_wBound
-- name    : ReplicableOL_wBound
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:47:09.456124+00:00
-- url     : https://prove2.me/theorems/d42ab4fd-7650-4462-ade1-91058c0d8520
-- title:
--   The seed-uniform bound on $\|\widetilde W\|_4$
-- statement:
--   The bound $3^{1/4}(s+s_\mu)+0.673\sqrt{kL}$ on $\|\widetilde W\|_4$, uniform over seeds and learners. Lemma 3.6 is stated with this number in the role of $\|\widetilde W\|_4$.
--
--   **Formalization Note** `s` and `s_μ` are the square roots of `sSq` and `sMuSq`. `0.673` is the printed decimal.
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Lemma 3.4(c), p.12

import Mathlib
import Definitions.Def_ReplicableOL_sSq
import Definitions.Def_ReplicableOL_sMuSq

namespace ReplicableOL

/-- **The seed-uniform bound on $\|\widetilde W\|_4$.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Lemma 3.4(c), p.12. `3^{1/4}(s + s_μ) + 0.673 √(kL)`.

**Formalization Note.** `s` and `s_μ` are the square roots of `sSq` and `sMuSq`. `0.673` is the printed decimal. -/
noncomputable def wBound (k L : ℕ) (Δ : ℝ) : ℝ :=
  (3 : ℝ) ^ (1 / 4 : ℝ) * (√(sSq k L Δ) + √(sMuSq k L Δ)) + 0.673 * √((k : ℝ) * L)

end ReplicableOL


