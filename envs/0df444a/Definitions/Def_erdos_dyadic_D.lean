-- Prove2me | Definitions.Def_erdos_dyadic_D
-- name    : erdos_dyadic_D
-- status  : Definition
-- author  : @Jhon Lenin Acuna
-- created : 2026-11-25T04:04:57.288819+00:00
-- url     : https://prove2.me/theorems/e634ce7c-1fb7-42d5-b3c7-72c5b570fad3
-- title:
--   The dyadic sequence $D=\{2^{-n}:n\ge 1\}$
-- statement:
--   The dyadic sequence
--   $$D=\{2^{-n} : n\in\mathbb N,\ n\ge 1\}=\{1/2,1/4,1/8,\dots\}\subseteq\mathbb R .$$
--
--   It is the single infinite pattern whose affine copies $x+sD$ are studied in the mission.
--
--   **Formalization Note** Lean indexes by $n\ge 0$ and uses the exponent $-(n+1)$, so the range is exactly $\{2^{-m}:m\ge1\}$; $0\notin D$.
-- source:
--   OpenAI, The dyadic case of the Erdős similarity conjecture, Sept 25, 2026, https://github.com/openai/math/tree/main/preprints/The-dyadic-case-of-the-Erdos-similarity-conjecture-September-25-2026, Section 1, p. 2 (definition of D)

import Mathlib

namespace ErdosDyadic

/-- D = {2^{-n} : n ≥ 1}. -/
noncomputable def D : Set ℝ := Set.range fun n : ℕ => (2 : ℝ) ^ (-(n + 1 : ℤ))

end ErdosDyadic


