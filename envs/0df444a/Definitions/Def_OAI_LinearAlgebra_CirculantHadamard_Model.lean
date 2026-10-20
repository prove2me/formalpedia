-- Prove2me | Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Model
-- name    : OAI_LinearAlgebra_CirculantHadamard_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T13:33:28.433551+00:00
-- url     : https://prove2.me/theorems/c8675cf6-bd1d-4aa8-a1bb-b1f8537c60e4
-- title:
--   Real circulant Hadamard matrices
-- statement:
--   A sequence $h_0,\dots,h_{n-1}$ of signs $\pm1$ is a Barker sequence when all its nontrivial aperiodic autocorrelations $A(k)=\sum_{j<n-k}h_jh_{j+k}$, $0<k<n$, satisfy $|A(k)|\le1$. These notions serve the proof that an even-length Barker sequence has length $2$ or $4$. The proof turns such a sequence of length $n>2$ into a real circulant Hadamard matrix of order $n$, and uses that such matrices exist only for $n=1$ and $n=4$.
--
--   For $n\in\mathbb N$, real $n\times n$ matrices are indexed by $\mathbb Z/n$.
--
--   1. **Circulant.** $H$ is circulant when $H_{ij}=h(j-i)$ for some $h:\mathbb Z/n\to\mathbb R$.
--   2. **Sign Hadamard.** $H$ has all entries $\pm1$ and satisfies
--   $$
--   HH^{\mathsf T}=n\,I .
--   $$
--   3. **Existence.** A real circulant Hadamard matrix of order $n$ exists when some matrix is both circulant and sign Hadamard. The circulant Hadamard theorem states that this happens only for $n=1$ and $n=4$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/LinearAlgebra/CirculantHadamard/Model.lean

-- Generated from openai/math@1581d4c lean/OAI/LinearAlgebra/CirculantHadamard/Model.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the EvenBarker mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_EvenBarker

namespace OAI

namespace CirculantHadamard

universe u

abbrev RealMatrix (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

def IsCirculant {n : ℕ} (H : RealMatrix n) : Prop :=
  ∃ h : Fin n → ℝ, ∀ i j, H i j = h (j - i)

def IsSignHadamard {n : ℕ} (H : RealMatrix n) : Prop :=
  (∀ i j, IsSign (H i j)) ∧
    H * H.transpose = (n : ℝ) • (1 : RealMatrix n)

def ExistsRealCirculantHadamard (n : ℕ) : Prop :=
  ∃ H : RealMatrix n, IsCirculant H ∧ IsSignHadamard H

end CirculantHadamard

end OAI


