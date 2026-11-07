-- Prove2me | Definitions.Def_QPACLarge_agreement
-- name    : QPACLarge_agreement
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:05:11.900242+00:00
-- url     : https://prove2.me/theorems/23a6116f-fb9c-4524-aa66-bde6073a708d
-- title:
--   Agreement $\mathrm{agreement}(f,h)=\Pr_{x\sim U_n}[f(x)=h(x)]$
-- statement:
--   For Boolean functions $f, h : \{0,1\}^n \to \{0,1\}$, their **agreement** under the uniform distribution is
--
--   $$
--   \mathrm{agreement}(f,h) = \Pr_{x \sim U_n}[f(x) = h(x)] = \frac{|\{x \in \{0,1\}^n : f(x) = h(x)\}|}{2^n}.
--   $$
--
--   An **advantage** $\gamma$ means agreement at least $1/2 + \gamma$. Agreement measures the error of a hypothesis $h$ against a target $f$; it is distinct from the success probability of a learner, the probability that the learner outputs a hypothesis with the required agreement.
--
--   **Formalization Note** Boolean functions are `Qubits n → Bool` (`true` = 1).
-- source:
--   Oliveira, Unconditional Quantum PAC Learning Advantage in the Large Error Regime, arXiv:2610.23268 (held file sha256 e749e7c9…), Section 1, p.4; Eq. (2), p.14

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic

namespace QPACLarge

open QAlgorithms

/-- **Agreement under the uniform distribution.**
Oliveira, *Unconditional Quantum PAC Learning Advantage in the Large Error Regime*,
arXiv:2610.23268 (held file sha256 e749e7c9…), Section 1, p.4 (and Eq. (2), p.14):
`agreement(f, h) ≜ Pr_{x∼U_n}[f(x) = h(x)]`.

**Formalization Note.** Boolean functions `{0,1}ⁿ → {0,1}` are `Qubits n → Bool` (`true` = 1). The
probability over the uniform distribution is the number of agreeing inputs divided by `2ⁿ`. -/
noncomputable def agreement {n : ℕ} (f h : Qubits n → Bool) : ℝ :=
  ((Finset.univ.filter fun x => f x = h x).card : ℝ) / 2 ^ n

end QPACLarge


