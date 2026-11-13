-- Prove2me | Definitions.Def_SigRoute_IsProfile
-- name    : SigRoute_IsProfile
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:41:35.832816+00:00
-- url     : https://prove2.me/theorems/e12d4bfa-2cdd-41e5-8d06-41f729a1f258
-- title:
--   Soundness profile $\mathcal Q$ and $\Lambda_{\mathcal Q}(\lambda)$
-- statement:
--   For a round $j$ of a run write
--
--   $$
--   q_X=\mathbb P[\rho_j=X\wedge a_j=1\mid\mathcal F_{j-1}],\qquad X\in\{A,B\}.
--   $$
--
--   A set $\mathcal Q\subseteq[0,1]^2$ is a **soundness profile** of the run if $(q_A,q_B)\in\mathcal Q$ in every round $j\le N$, almost surely. For credits $u_A,u_B$ and $\lambda>0$ put
--
--   $$
--   \Lambda_{\mathcal Q}(\lambda)=1+\sup_{(q_A,q_B)\in\mathcal Q}\bigl[q_A(e^{\lambda u_A}-1)+q_B(e^{\lambda u_B}-1)\bigr].
--   $$
--
--   A profile summarizes everything about a cheating prover that the soundness bound of Theorem 14 needs.
--
--   **Formalization Note** The supremum is the real `sSup` of the image of $\mathcal Q$; since $\mathcal Q\subseteq[0,1]^2$ is part of the definition of a profile, the image is bounded and the supremum is genuine whenever $\mathcal Q\neq\varnothing$. For $\mathcal Q=\varnothing$ Lean gives $\Lambda=1$; no run with $N\ge1$ rounds has an empty profile.
-- source:
--   Dumlu, Signal-Routed Two-Arm Verification, STOC 2027 submission manuscript (held version, sha256 d56b3b7a…), Definition 12, p.7; Theorem 14, p.7

import Mathlib
import Definitions.Def_SigRoute_condProb
import Definitions.Def_SigRoute_IsRoutedRun

namespace SigRoute

open MeasureTheory

/-- A soundness profile of a run (Dumlu, Signal-Routed Two-Arm Verification, STOC 2027 submission manuscript (held version, sha256 d56b3b7a…), Definition 12, p.7): a set `Q ⊆ [0,1]²` such that in every
round `j < N`, almost surely, the pair
`(q_A, q_B) = (P[ρ_j = A ∧ a_j = 1 | F_{j−1}], P[ρ_j = B ∧ a_j = 1 | F_{j−1}])` lies in `Q`.

**Formalization Note** "For every prover, round and history" is "for every run (in each theorem), every
round `j < N` and `μ`-almost every `ω`". The conditioning σ-algebra of round `j` is `F j` (0-based). -/
def IsProfile {Ω : Type*} {m : MeasurableSpace Ω} (μ : Measure Ω) (F : Filtration ℕ m)
    (ρ : ℕ → Ω → Arm) (a : ℕ → Ω → Bool) (N : ℕ) (Q : Set (ℝ × ℝ)) : Prop :=
  Q ⊆ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 ∧
    ∀ j < N, ∀ᵐ ω ∂μ,
      (condProb μ (F j) {ω | ρ j ω = Arm.A ∧ a j ω = true} ω,
        condProb μ (F j) {ω | ρ j ω = Arm.B ∧ a j ω = true} ω) ∈ Q

/-- The profile moment `Λ_Q(λ) = 1 + sup_{(q_A,q_B)∈Q} [q_A(e^{λu_A} − 1) + q_B(e^{λu_B} − 1)]`
(Dumlu, Signal-Routed Two-Arm Verification, STOC 2027 submission manuscript (held version, sha256 d56b3b7a…), Theorem 14, p.7).

**Formalization Note** The supremum is `sSup` on `ℝ`. It is the true supremum when `Q` is nonempty
and bounded, which holds for every profile used here (`Q ⊆ [0,1]²` is part of `IsProfile`); for
`Q = ∅` Lean's `sSup ∅ = 0` gives `Λ_Q = 1`, which no run with `N ≥ 1` rounds can have as a profile. -/
noncomputable def Lam (u : Arm → ℝ) (Q : Set (ℝ × ℝ)) (lam : ℝ) : ℝ :=
  1 + sSup ((fun q : ℝ × ℝ =>
    q.1 * (Real.exp (lam * u Arm.A) - 1) + q.2 * (Real.exp (lam * u Arm.B) - 1)) '' Q)

end SigRoute


