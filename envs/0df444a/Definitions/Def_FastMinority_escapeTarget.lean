-- Prove2me | Definitions.Def_FastMinority_escapeTarget
-- name    : FastMinority_escapeTarget
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:05:20.061843+00:00
-- url     : https://prove2.me/theorems/0172efb9-998d-4cf1-95e8-36547bd38fd7
-- title:
--   Target set $\{0\}\cup[L,R-1]$
-- statement:
--   The set
--   $$
--   \{0\}\cup[L,R-1]
--   $$
--   of minority sizes (consensus, or a state between the lower and the upper region). Since $[L,R-1]\subseteq\mathcal C\cup\mathcal H$, it is contained in $\mathcal C\cup\mathcal H^+$ for every value of the constant $b$, and it does not depend on $b$. Reaching it therefore implies reaching $\mathcal C\cup\mathcal H^+$; it is the target used for the exit bounds of Lemma 3.6 and Proposition 3.3.
-- source:
--   Berenbrink–Giriyan–Götte–Richa, Fast Minority Dynamics with Θ(log² n)-Size Samples, STOC 2027 submission (manuscript sha256 841077e0…abcdd1), Section 3, p.6 (PDF p.8)

import Mathlib
import Definitions.Def_FastMinority_lowThr
import Definitions.Def_FastMinority_upThr

set_option autoImplicit false

open Classical

namespace FastMinority

/-- The set `{0} ∪ [L, R − 1]` of minority counts (Berenbrink–Giriyan–Götte–Richa, *Fast Minority Dynamics with Θ(log² n)-Size Samples*, STOC 2027 submission manuscript (sha256 841077e0…abcdd1), §3, p.6 = PDF p.8): consensus, or a
state between the lower and the upper region. It is contained in `𝓒 ∪ 𝓗⁺` for every `b` (since
`[L, R − 1] ⊆ 𝓒 ∪ 𝓗`), and it does not depend on `b`.

**Formalization Note** Used as the target of Lemma 3.6 and Proposition 3.3: reaching this smaller set
implies reaching `𝓒 ∪ 𝓗⁺`. -/
noncomputable def escapeTarget (n k : ℕ) (D : ℝ) : Set (Fin (n + 1)) :=
  {x | (x : ℕ) = 0 ∨ (lowThr n k ≤ (x : ℕ) ∧ (x : ℕ) < upThr n k D)}

end FastMinority


