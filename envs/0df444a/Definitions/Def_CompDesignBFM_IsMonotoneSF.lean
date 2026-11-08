-- Prove2me | Definitions.Def_CompDesignBFM_IsMonotoneSF
-- name    : CompDesignBFM_IsMonotoneSF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:32:30.500455+00:00
-- url     : https://prove2.me/theorems/d6b6fc40-b45f-4dd9-99f7-a3135fa38908
-- title:
--   Monotone set function
-- statement:
--   A set function $v$ is **monotone** if $v(S)\le v(T)$ for all $S\subseteq T\subseteq N$.
-- source:
--   Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, §1, p.1 (PDF 3)

import Mathlib

namespace CompDesignBFM

/-- A monotone set function (Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, §1, p.1, PDF 3): `v S ≤ v T` for all `S ⊆ T`. -/
def IsMonotoneSF {n : ℕ} (v : Finset (Fin n) → ℝ) : Prop :=
  ∀ S T, S ⊆ T → v S ≤ v T

end CompDesignBFM


