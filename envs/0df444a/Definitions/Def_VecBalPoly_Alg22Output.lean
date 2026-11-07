-- Prove2me | Definitions.Def_VecBalPoly_Alg22Output
-- name    : VecBalPoly_Alg22Output
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T23:18:35.494227+00:00
-- url     : https://prove2.me/theorems/41f05315-59e2-400a-aa24-becb1f2043bc
-- title:
--   Outputs of Algorithm 2.2
-- statement:
--   A vector $\varepsilon\in\mathbb R^n$ is an **output of Algorithm 2.2** on $A$ when either $n\le K$ and $\varepsilon$ is all $+1$, or $n>K$ and $\varepsilon$ is obtained from the last state of a run by rounding every coordinate to the nearest sign, choosing $+1$ on a tie.
--
--   **Formalization Note** Runs range over all directions meeting the conclusion of Lemma 2.1.
-- source:
--   S. Guo, E. X. Fang, J. Lu, Vector Balancing in Polynomial Time, arXiv:2609.23540 (held file sha256 b777ade4…), Algorithm 2.2, p.6 (PDF p.7)

import Mathlib
import Definitions.Def_VecBalPoly_IsPrefixRun

namespace VecBalPoly

variable {m n : ℕ}

/-- The final rounding: every coordinate to the nearest sign, `+1` on a tie (frozen coordinates
already equal `±1`). -/
noncomputable def roundSigns (st : St m n) : Fin n → ℝ :=
  fun j => if 0 ≤ st.x j then 1 else -1

/-- **The outputs of Algorithm 2.2.** `ε` is an output of the algorithm on `A` when either
`n ≤ K` and `ε` is all positive signs, or `n > K` and `ε` is the rounding of the last state of a
complete run.
Source: Guo, Fang, Lu, *Vector Balancing in Polynomial Time*, arXiv:2609.23540 (held file sha256
b777ade4…), Algorithm 2.2, p.6 (PDF p.7): "If n ≤ K, return all positive signs. … Round each
remaining active coordinate to the nearest sign, choosing +1 in case of a tie. Return the resulting
signing."

**Formalization Note** Runs range over all directions meeting Lemma 2.1's conclusion (see
`IsPrefixRun`), so this is the set of outputs over those choices. -/
def Alg22Output (A : Matrix (Fin m) (Fin n) ℝ) (ε : Fin n → ℝ) : Prop :=
  ((n : ℝ) ≤ K ∧ ε = fun _ => 1) ∨
  (K < (n : ℝ) ∧ ∃ N sts hs, IsRun A N sts hs ∧ ε = roundSigns (sts N))

end VecBalPoly


