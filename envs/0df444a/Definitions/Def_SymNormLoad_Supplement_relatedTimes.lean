-- Prove2me | Definitions.Def_SymNormLoad_Supplement_relatedTimes
-- name    : SymNormLoad_Supplement_relatedTimes
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:55:37.167556+00:00
-- url     : https://prove2.me/theorems/9e0c4950-7147-4170-be79-cd0eac5e3cf3
-- title:
--   Processing times $p_{ji}=p_j/v_i$ on related machines
-- statement:
--   In the **related-machine model** there are $M$ machines, and machine $i$ has a fixed positive speed $v_i$, known before any jobs arrive. Job $j$ reveals a size $p_j$, and its processing time on machine $i$ is
--   $$
--   p_{ji}=\frac{p_j}{v_i}.
--   $$
--
--   This turns a speed vector $v=(v_1,\dots,v_M)$ and a size sequence $(p_1,\dots,p_N)$ into the processing-time matrix of the unrelated-machine model, so that loads, online rules and offline assignments of the base mission apply unchanged. Identical machines are the case of equal speeds.
--
--   **Formalization Note** Jobs and machines are indexed by `Fin N` and `Fin M`, both 0-based. Positivity of speeds and sizes is a hypothesis of each statement that uses this definition, not part of it.
-- source:
--   Chen–Im–Sirri, Online Load Balancing under Symmetric Norms, manuscript (STOC 2027 submission), Section 1.1, p.2

import Mathlib

namespace SymNormLoad.Supplement

/-- **Processing times on related machines.** Chen–Im–Sirri, *Online Load Balancing under
Symmetric Norms*, manuscript (STOC 2027 submission), §1.1, p.2: in the related-machine model,
machine `i` has a fixed positive speed `v_i`, known before any jobs arrive; job `j` reveals a size
`p_j`, and its processing time on machine `i` is `p_{ji} = p_j / v_i`.

**Formalization Note** Jobs are `Fin N` and machines `Fin M`, both 0-based; `s j` is the size of
job `j` and `v i` the speed of machine `i`. Positivity of speeds and sizes is a hypothesis of each
statement, not part of this definition. The result is the processing-time matrix consumed by the
published `SymNormLoad.loadVec` and `SymNormLoad.runAssign`. -/
noncomputable def relatedTimes {N M : ℕ} (v : Fin M → ℝ) (s : Fin N → ℝ) : Fin N → Fin M → ℝ :=
  fun j i => s j / v i

end SymNormLoad.Supplement


