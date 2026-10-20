-- Prove2me | Definitions.Def_OAI_LinearAlgebra_Barker_Model
-- name    : OAI_LinearAlgebra_Barker_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T13:34:19.518217+00:00
-- url     : https://prove2.me/theorems/bb0f4bf1-6656-4867-b3b5-eaece0a58be3
-- title:
--   Periodic autocorrelation of an integer sequence
-- statement:
--   A sequence $h_0,\dots,h_{n-1}$ of signs $\pm1$ is a Barker sequence when all its nontrivial aperiodic autocorrelations $A(k)=\sum_{j<n-k}h_jh_{j+k}$, $0<k<n$, satisfy $|A(k)|\le1$. These notions serve the proof that an even-length Barker sequence has length $2$ or $4$. The proof turns such a sequence of length $n>2$ into a real circulant Hadamard matrix of order $n$, and uses that such matrices exist only for $n=1$ and $n=4$.
--
--   For $n\ge1$, an integer sequence $h:\mathbb Z/n\to\mathbb Z$ and a shift $a\in\mathbb Z/n$, this module defines the periodic autocorrelation
--   $$
--   P(a)=\sum_{j\in\mathbb Z/n}h_j\,h_{j-a},
--   $$
--   with indices taken modulo $n$. A $\pm1$ sequence gives a circulant Hadamard matrix exactly when $P(a)=0$ for every $a\ne0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/LinearAlgebra/Barker/Model.lean

-- Generated from openai/math@1581d4c lean/OAI/LinearAlgebra/Barker/Model.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the EvenBarker mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_EvenBarker
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Model

namespace OAI

namespace CirculantHadamard.Barker

open scoped BigOperators

def periodic {n : ℕ} [NeZero n] (h : Fin n → ℤ) (a : Fin n) : ℤ :=
  ∑ j : Fin n, h j * h (j - a)

end CirculantHadamard.Barker

end OAI


