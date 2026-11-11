-- Prove2me | Definitions.Def_DecDynMatch_RuleOK
-- name    : DecDynMatch_RuleOK
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:56:18.829519+00:00
-- url     : https://prove2.me/theorems/99bc62c6-a788-4685-9391-c66e136df7f4
-- title:
--   Admissible replay rules (12) and the SC-DA rule $F(x)=H+2x$
-- statement:
--   A **replay rule** is a function $F$ from positive integers to positive integers that SC-DA uses to set the replay length $L=F(a-\ell)$ at every Work output. The analysis allows every rule that is non-decreasing and satisfies
--   $$
--   F(x)\ \ge\ H+2x\qquad(x\ge 1). \tag{12}
--   $$
--   The original SC-DA uses $F(x)=H+2x$.
--
--   **Formalization Note** `RuleOK K F` is: `F : ℕ → ℕ` is monotone and $F(x)\ge H+2x$ for $x\ge 1$. The value $F(0)$ is never evaluated by the protocol; computability is not required, since no argument uses it. `scdaRule K` is $x\mapsto H+2x$.
-- source:
--   J. Chen, M. Gao, Z. Zhang, Decentralized Dynamic Stable Matching, arXiv:2610.41912 (held version, sha256 6a27277e…), App. A, eq. (12)–(13), p.14

import Mathlib
import Definitions.Def_DecDynMatch_J

namespace DecDynMatch

/-- **Admissible replay rules.** J. Chen, M. Gao, Z. Zhang, *Decentralized Dynamic Stable
Matching*, arXiv:2610.41912 (held version, sha256 6a27277e…), App. A, eq. (12), p.14: "allow any
nondecreasing computable replay rule F : ℕ≥1 → ℕ≥1 satisfying F(x) ≥ H + 2x (x ≥ 1)."

**Formalization Note.** `F : ℕ → ℕ` is monotone on all of `ℕ`; its value at `0` is never read by the
protocol (the argument `a − ℓ` of an output is always positive, p.14), and every rule of the paper
extends to `0` by `F 0 := F 1`. Computability is not required: no statement uses it. -/
def RuleOK (K : ℕ) (F : ℕ → ℕ) : Prop :=
  Monotone F ∧ ∀ x, 1 ≤ x → H K + 2 * x ≤ F x

/-- The SC-DA replay rule `F(x) = H + 2x` (Algorithm 1, line 31, p.6; p.14: "The original SC-DA
uses F(x) = H + 2x"). -/
def scdaRule (K : ℕ) : ℕ → ℕ := fun x => H K + 2 * x

end DecDynMatch


