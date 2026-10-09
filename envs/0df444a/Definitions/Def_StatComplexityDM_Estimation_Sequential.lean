-- Prove2me | Definitions.Def_StatComplexityDM_Estimation_Sequential
-- name    : StatComplexityDM_Estimation_Sequential
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T21:21:47.17812+00:00
-- url     : https://prove2.me/theorems/7a900d82-5b6a-4a77-a9e9-a0efc1e60940
-- title:
--   Appendix A.1, p. 70 — finite sequential histories, probability kernels, and path law
-- statement:
--   Let $Z$ be a finite alphabet and $T$ a nonnegative integer. A history of length $t$ is a sequence $z_{<t}=(z_0,\ldots,z_{t-1})\in Z^t$. For a complete path $z\in Z^T$, its prefix before round $t$ is $z_{<t}$.
--
--   A sequential probability kernel assigns a probability vector $K_t(\cdot\mid z_{<t})$ on $Z$ to every round and every preceding history. It induces the path probability
--   $$
--   P_K(z)=\prod_{t=0}^{T-1}K_t(z_t\mid z_{<t}).
--   $$
--
--   These objects realize the adapted process in Lemma A.4 and provide a reusable interface for finite online estimation.
--
--   **Formalization Note** The paper allows general measurable spaces and filtrations. Here alphabets are finite, histories use 0-based indices, and expectations are finite sums. Kernels are normalized at every history.
-- source:
--   arXiv:2112.13487v3, Appendix A.1, Lemma A.4 (setting), p. 70; Appendix A.3.1, pp. 75–76

import Mathlib
import Definitions.Def_StatComplexityDM_LowerBound_Core

namespace StatComplexityDM.Estimation

/-- A finite history of length `n`, with rounds numbered from zero. -/
abbrev Hist (Z : Type*) (n : ℕ) := Fin n → Z

/-- The observations strictly before round `t`. -/
def histPrefix {Z : Type*} {T : ℕ} (z : Hist Z T) (t : Fin T) : Hist Z t.val :=
  fun s => z ⟨s.val, Nat.lt_trans s.isLt t.isLt⟩

/-- A history-dependent probability kernel for a finite sequential process. -/
def IsKernel {Z : Type*} [Fintype Z] {T : ℕ}
    (K : (t : Fin T) → Hist Z t.val → Z → ℝ) : Prop :=
  ∀ t h, StatComplexityDM.LowerBound.IsDist (K t h)

/-- The probability of a complete path under the successive kernels. -/
def seqLaw {Z : Type*} {T : ℕ}
    (K : (t : Fin T) → Hist Z t.val → Z → ℝ) (z : Hist Z T) : ℝ :=
  ∏ t, K t (histPrefix z t) (z t)

end StatComplexityDM.Estimation


