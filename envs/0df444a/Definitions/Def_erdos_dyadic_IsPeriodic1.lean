-- Prove2me | Definitions.Def_erdos_dyadic_IsPeriodic1
-- name    : erdos_dyadic_IsPeriodic1
-- status  : Definition
-- author  : @Jhon Lenin Acuna
-- created : 2026-11-25T04:08:23.22903+00:00
-- url     : https://prove2.me/theorems/357fe14c-bf89-4f68-943a-e4971f91ed99
-- title:
--   1-periodic set
-- statement:
--   A set $H\subseteq\mathbb R$ is **1-periodic** if for every $x\in\mathbb R$, $x\in H \iff x+1\in H$; equivalently $H+k=H$ for every integer $k$.
--
--   Periodic sets are identified with subsets of the circle $\mathbb T=\mathbb R/\mathbb Z$.
-- source:
--   OpenAI, The dyadic case of the Erdős similarity conjecture, Sept 25, 2026, https://github.com/openai/math/tree/main/preprints/The-dyadic-case-of-the-Erdos-similarity-conjecture-September-25-2026, Section 2, p. 3

import Mathlib

namespace ErdosDyadic

/-- A 1-periodic set. -/
def IsPeriodic1 (H : Set ℝ) : Prop := ∀ x, x ∈ H ↔ x + 1 ∈ H

end ErdosDyadic


