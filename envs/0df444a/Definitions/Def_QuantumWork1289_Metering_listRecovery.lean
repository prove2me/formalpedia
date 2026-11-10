-- Prove2me | Definitions.Def_QuantumWork1289_Metering_listRecovery
-- name    : QuantumWork1289_Metering_listRecovery
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T04:36:51.922728+00:00
-- url     : https://prove2.me/theorems/cd4ab11e-1d0e-4669-a4d7-97323d8ba528
-- title:
--   Set-based list recovery and the exact binomial tail
-- statement:
--   Let $N$ be a natural codeword length, $\Sigma$ any alphabet, and $\mathcal C\subseteq\Sigma^N$ a code. A set has at most $b\in\mathbb R$ elements when every finite subset has cardinality at most $b$. This definition detects infinite sets without assigning them a default finite cardinality.
--
--   For real parameters $\zeta,\ell,L$, list recoverability means $0<\zeta<1$ and, for every family of coordinate lists $S_i\subseteq\Sigma$ with at most $\ell$ elements, at most $L$ codewords satisfy
--
--   $$|\{i:w_i\in S_i\}|\ge(1-\zeta)N.$$
--
--   For natural numbers $m,Q$, define
--
--   $$\beta(m,Q)=2^{-m}\sum_{j=0}^{\min\{Q,m\}}\binom mj,\qquad m=\lfloor\zeta N\rfloor.$$
--
--   The sum includes its endpoint. These are the counting hypothesis and numerical bound shared by both theorems. Real list bounds preserve the exact multiplier even when the source expresses its list parameters by real powers. No finiteness of the alphabet or the code is imposed.
-- source:
--   Mohammed Barhoush, Proof of Quantum Work with Classical Verification, STOC 2027 submission #1289 (October 2026), p. 18, Definition 6 and Theorem 4

import Mathlib
set_option autoImplicit false

namespace QuantumWork1289.Metering

/-- Cardinal bound valid also for sets in infinite alphabets/codes. -/
def HasAtMost {α : Type} (s : Set α) (b : ℝ) : Prop :=
  ∀ t : Finset α, (↑t : Set α) ⊆ s → (t.card : ℝ) ≤ b

open Classical in
/-- Definition 6, p.18: inclusive agreement threshold; no finite-alphabet assumption. -/
def ListRecoverable {Γ : Type} {N : ℕ} (code : Set (Fin N → Γ))
    (ζ ℓ L : ℝ) : Prop :=
  0 < ζ ∧ ζ < 1 ∧ ∀ S : Fin N → Set Γ,
    (∀ i, HasAtMost (S i) ℓ) →
    HasAtMost {w | w ∈ code ∧
      (1 - ζ) * (N : ℝ) ≤ ((Finset.univ.filter fun i => w i ∈ S i).card : ℝ)} L

/-- Inclusive binomial tail in formal Theorems 4 and 5. -/
noncomputable def beta (m Q : ℕ) : ℝ :=
  (2 : ℝ) ^ (-(m : ℤ)) * ∑ j ∈ Finset.range (min Q m + 1), (m.choose j : ℝ)

/-- Exactly floor(ζN), including m=0. -/
noncomputable def unread (ζ : ℝ) (N : ℕ) : ℕ := ⌊ζ * (N : ℝ)⌋₊

end QuantumWork1289.Metering


