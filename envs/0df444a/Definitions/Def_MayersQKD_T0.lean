-- Prove2me | Definitions.Def_MayersQKD_T0
-- name    : MayersQKD_T0
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:42:28.194237+00:00
-- url     : https://prove2.me/theorems/74323209-6543-413b-81be-7227b693a7d4
-- title:
--   The sets $T_0,T_1$, the test of step 5 and valid pairs $(E_0,E_1)$
-- statement:
--   Given Alice's bases $\theta$ and Bob's committed bases $\hat\theta$, let $T_0$ be the set of positions with $\theta_i=\hat\theta_i$ and $T_1$ the set with $\theta_i\ne\hat\theta_i$. The test on a subset $R$ counts the positions $i\in R$ with $\theta_i=\hat\theta_i$ and $w_i\ne\hat w_i$; the test result is accepted when that count is at most $\delta n$.
--
--   A pair $(E_0,E_1)$ is valid when
--
--   $$
--   E_0\subseteq T_0-R,\qquad E_1\subseteq T_1-R,\qquad |E_0|=|E_1|=N .
--   $$
--
--   Bob's rule at step 6 must answer with a valid pair, and may stop only when no valid pair exists.
--
--   These encode the phrase "Bob constructs $E_0$ and $E_1$ as specified in the protocol".
--
--   **Formalization Note** Step 5 stops on more than $\delta n$ errors and §7 says no more than $\delta n$ are tolerated, so $Pass=1$ means at most $\delta n$ errors. The paper does not treat $|T_0-R|<N$ or $|T_1-R|<N$; there the protocol stops and nothing depending on $b$ is announced.
-- source:
--   Mayers, Quantum Key Distribution and String Oblivious Transfer in Noisy Channels, arXiv:quant-ph/9606003v1, §5, p.7, steps 5–6; §7, p.9

import Mathlib
import Definitions.Def_MayersQKD_Bits

namespace MayersQKD

/-- Mayers, arXiv:quant-ph/9606003v1, §5, p.7, step 6: `T₀` is the set of all `i` with
`θᵢ = θ̂ᵢ`. -/
def T0 {n : ℕ} (θ θhat : Bases n) : Finset (Fin n) := Finset.univ.filter fun i => θ i = θhat i

/-- Mayers, arXiv:quant-ph/9606003v1, §5, p.7, step 6: `T₁` is the set of all `i` with
`θᵢ ≠ θ̂ᵢ`. -/
def T1 {n : ℕ} (θ θhat : Bases n) : Finset (Fin n) := Finset.univ.filter fun i => θ i ≠ θhat i

/-- Mayers, arXiv:quant-ph/9606003v1, §5, p.7, step 5: the number of positions `i ∈ R` revealing
`θᵢ = θ̂ᵢ` and `wᵢ ≠ ŵᵢ`. -/
def testErrors {n : ℕ} (θ θhat : Bases n) (w what : Bits n) (R : Finset (Fin n)) : ℕ :=
  (R.filter fun i => θ i = θhat i ∧ w i ≠ what i).card

/-- Mayers, arXiv:quant-ph/9606003v1, §5, p.7, step 5: the test result is accepted, i.e. `Pass = 1`
(p.8), unless more than `δn` positions fail.

**Formalization Note.** Step 5 stops on "more than `δn`" and §7 says "no more than `δn`", so
`Pass = 1` iff at most `δn` errors; the "less than `δn`" of §2, p.4, is a loose restatement. -/
def TestAccepted {n : ℕ} (δ : ℝ) (θ θhat : Bases n) (w what : Bits n) (R : Finset (Fin n)) : Prop :=
  (testErrors θ θhat w what R : ℝ) ≤ δ * n

/-- Mayers, arXiv:quant-ph/9606003v1, §5, p.7, step 6: `E₀ ⊆ T₀ − R`, `E₁ ⊆ T₁ − R` and
`|E₀| = |E₁| = N`. -/
def IsValidPair {n : ℕ} (θ θhat : Bases n) (R E0 E1 : Finset (Fin n)) : Prop :=
  E0 ⊆ T0 θ θhat \ R ∧ E1 ⊆ T1 θ θhat \ R ∧ E0.card = blockLen n ∧ E1.card = blockLen n

/-- Mayers, arXiv:quant-ph/9606003v1, §5, p.7, step 6, and p.7 ("Bob constructs `E₀` and `E₁` as
specified in the protocol"): what Bob's rule may answer at step 6. A pair must be valid, and
"stop" (`none`) is allowed only when no valid pair exists.

**Formalization Note.** The paper does not treat the case `|T₀ − R| < N` or `|T₁ − R| < N`, where
step 6 cannot be carried out. Here the protocol stops there and nothing depending on `b` is
announced. -/
def SelValid {n : ℕ} (θ θhat : Bases n) (R : Finset (Fin n)) :
    Option (Finset (Fin n) × Finset (Fin n)) → Prop
  | some E => IsValidPair θ θhat R E.1 E.2
  | none => ¬ ∃ E0 E1, IsValidPair θ θhat R E0 E1

end MayersQKD


