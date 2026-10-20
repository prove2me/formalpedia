-- Prove2me | Definitions.Def_OAI_LinearAlgebra_Barker_PeriodicModFour
-- name    : OAI_LinearAlgebra_Barker_PeriodicModFour
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T13:35:37.968983+00:00
-- url     : https://prove2.me/theorems/feaf5c01-1379-4550-8f8c-709cb6290120
-- title:
--   Negative bits and cyclic shifts
-- statement:
--   A sequence $h_0,\dots,h_{n-1}$ of signs $\pm1$ is a Barker sequence when all its nontrivial aperiodic autocorrelations $A(k)=\sum_{j<n-k}h_jh_{j+k}$, $0<k<n$, satisfy $|A(k)|\le1$. These notions serve the proof that an even-length Barker sequence has length $2$ or $4$. The proof turns such a sequence of length $n>2$ into a real circulant Hadamard matrix of order $n$, and uses that such matrices exist only for $n=1$ and $n=4$.
--
--   1. **Negative bits.** For a sequence $h$, the indicator $\beta_j$ that equals $1$ when $h_j=-1$ and $0$ otherwise. A sign is then $h_j=1-2\beta_j$.
--   2. **Cyclic shift.** For $a\in\mathbb Z/n$, the bijection $j\mapsto j-a$ of $\mathbb Z/n$, with inverse $j\mapsto j+a$.
--
--   Expanding $P(a)$ in the negative bits shows that
--   $$
--   P(a)\equiv n\pmod 4
--   $$
--   for every $\pm1$ sequence and every shift $a$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/LinearAlgebra/Barker/PeriodicModFour.lean

-- Generated from openai/math@1581d4c lean/OAI/LinearAlgebra/Barker/PeriodicModFour.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the EvenBarker mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Model
import Definitions.Def_OAI_LinearAlgebra_Barker_Model

namespace OAI

namespace CirculantHadamard.Barker

open scoped BigOperators

def negativeBit {n : ℕ} (h : Fin n → ℤ) (j : Fin n) : ℤ :=
  if h j = -1 then 1 else 0

def cyclicSubtractEquiv {n : ℕ} [NeZero n] (a : Fin n) : Fin n ≃ Fin n where
  toFun j := j - a
  invFun j := j + a
  left_inv j := sub_add_cancel j a
  right_inv j := add_sub_cancel_right j a

end CirculantHadamard.Barker

end OAI


