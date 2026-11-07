-- Prove2me | Definitions.Def_QPACLarge_Jmap
-- name    : QPACLarge_Jmap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:06:15.38422+00:00
-- url     : https://prove2.me/theorems/4831ad3e-aec8-4c83-b394-80d1737fd9d8
-- title:
--   Feature map $J:\{\bot\}\cup\{0,1\}^n\to\{0,1\}^r$
-- statement:
--   The **feature map** sends the reference label $\bot$ to the zero seed and an input $x$ to its monomials:
--   $$
--   J(\bot) = 0^r, \qquad J(x) = (1, \{x_i\}_{i=1}^n, \{x_i x_j\}_{1 \le i < j \le n}).
--   $$
--   It satisfies $q_a(x) = a \cdot J(x)$ over $\mathbb F_2$ (Lemma 3.1).
--
--   **Formalization Note** The label set $\{\bot\} \cup \{0,1\}^n$ is `Option (Qubits n)`, with `none` = $\bot$.
-- source:
--   Oliveira, Unconditional Quantum PAC Learning Advantage in the Large Error Regime, arXiv:2610.23268 (held file sha256 e749e7c9…), Proof of Lemma 3.1, p.20

import Mathlib
import Definitions.Def_QPACLarge_Seed
import Definitions.Def_QAlgorithms_Defs_Basic

namespace QPACLarge

open QAlgorithms

/-- **The feature map `J : {⊥} ∪ {0,1}ⁿ → {0,1}^r`.**
Oliveira, *Unconditional Quantum PAC Learning Advantage in the Large Error Regime*, arXiv:2610.23268 (held file sha256 e749e7c9…), proof of Lemma 3.1, p.20: "Define the feature map `J(⊥) = 0^r`,
`J(x) = (1, {xᵢ}_{i=1}^n, {xᵢxⱼ}_{1≤i<j≤n})`."

**Formalization Note.** The label set `{⊥} ∪ {0,1}ⁿ` is `Option (Qubits n)` (`none` = `⊥`). -/
def Jmap (n : ℕ) : Option (Qubits n) → Seed n
  | none => (false, fun _ => false, fun _ => false)
  | some x => (true, x, fun p => x p.1.1 && x p.1.2)

end QPACLarge


