-- Prove2me | Definitions.Def_ChangingCache_UpperBound_Bank
-- name    : ChangingCache_UpperBound_Bank
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T12:01:00.591273+00:00
-- url     : https://prove2.me/theorems/fa449be1-b396-4109-b071-b680d952bfea
-- title:
--   Bank, slack, $\mu$ and the invariant Eq. (4) at speed 3
-- statement:
--   Under $(2,3)$ augmentation (fixed for Section 5), LRU's capacity after $k$ misses is $m_{LRU}(k)=2m(\lfloor k/3\rfloor)$ (Eq. (3)). For a run with OPT and positions $0\le i\le n$:
--
--   1. $\mu(i)=|P_{OPT}(i)\setminus P_{LRU}(i)|$ is the number of pages OPT holds after request $\sigma_i$ that LRU does not hold (p. 13).
--   2. The **bank** (Definition 3.2, p. 7) at speed 3 is
--   $$B_3(i)=3F_{OPT}(i)-F_{LRU}(i),$$
--   the misses of LRU that OPT has already paid for.
--   3. The **slack** (p. 13) is $S_3(i)=B_3(i)-|P_{OPT}(i)|$.
--   4. **Equation (4)** (p. 13) is the invariant
--   $$B_3(i)\ge |P_{OPT}(i)|+\mu(i)\qquad\text{for every } i\le n \text{ with } i\equiv1 \pmod 3 .$$
--   5. $w$ is the least position $1\le w\le n$ with $w\equiv1\pmod 3$ at which the inequality of Equation (4) fails, or $w=n+1$ if it never fails (Lemma 5.5).
--
--   LRU finishes no later than OPT exactly when the bank stays nonnegative; the slack and Eq. (4) strengthen this accounting into a statement that can be carried by induction.
--
--   **Formalization Note** Bank and slack are integers (`ℤ`), so no truncated subtraction occurs. `Eq4At m σ S i` is the inequality at one position; the restriction to $1\le i\le n$, $i\equiv 1\pmod 3$ is part of `eq4FirstFailure`, which is defined with `Nat.find`.
-- source:
--   Michael A. Bender, Daniel DeLayo, Pritom Kundu, Charlie McGuffey, Zofia Stefankovic, Zhonglue Wang, STOC 2027 submission #93 (October 2026), Caching with a Changing Cache Size, SHA-256 9d5334fdae9f69a8802bcb33b61c3699463aa88862a32b7bb8d17bd3efdf533d, Definition 3.2, p. 7; Eq. (3), p. 12; slack, $\mu$ and Eq. (4), p. 13; Lemma 5.5, p. 13

import Mathlib
import Definitions.Def_ChangingCache_UpperBound_NormalForm

namespace ChangingCache.UpperBound

/-! # Bank, slack and the invariant of §5 (Bender et al., STOC 2027 #93, pp. 7, 12–13)

Throughout §5 the augmentation is `(2, 3)`: LRU's capacity law is `augCap 2 3 m`, i.e.
`m_LRU(k) = 2 m(⌊k/3⌋)` (Eq. (3)). `S` is the policy designated OPT in the run, and `S i` is
`P_OPT(i)`. All quantities are integers; no truncated subtraction is used. -/

variable {α : Type*} [DecidableEq α]

/-- `μ(i)` (p. 13): the number of pages OPT holds after request `σ_i` that LRU does not hold. -/
noncomputable def mu (m : ℕ → ℕ) (σ : List α) (S : ℕ → Finset α) (i : ℕ) : ℕ :=
  (S i \ lruCache (augCap 2 3 m) σ i).card

/-- The **bank** at speed 3 (Definition 3.2, p. 7): `B₃(i) = 3 F_OPT(i) - F_LRU(i)`, an integer. -/
noncomputable def bank3 (m : ℕ → ℕ) (σ : List α) (S : ℕ → Finset α) (i : ℕ) : ℤ :=
  3 * (policyMisses σ S i : ℤ) - (lruMissCount (augCap 2 3 m) σ i : ℤ)

/-- The **slack** (p. 13): `S₃(i) = B₃(i) - |P_OPT(i)|`, an integer. -/
noncomputable def slack3 (m : ℕ → ℕ) (σ : List α) (S : ℕ → Finset α) (i : ℕ) : ℤ :=
  bank3 m σ S i - ((S i).card : ℤ)

/-- The inequality of **Equation (4)** (p. 13) at position `i`:
`B₃(i) ≥ |P_OPT(i)| + μ(i)`. Equation (4) asserts it at every position `1 ≤ i ≤ n` with
`i ≡ 1 (mod 3)`. -/
def Eq4At (m : ℕ → ℕ) (σ : List α) (S : ℕ → Finset α) (i : ℕ) : Prop :=
  (((S i).card + mu m σ S i : ℕ) : ℤ) ≤ bank3 m σ S i

/-- The least position `1 ≤ i ≤ n`, `i ≡ 1 (mod 3)`, at which Equation (4) fails, or `n + 1` if it
never fails (the `w` of Lemma 5.5, p. 13). -/
noncomputable def eq4FirstFailure (m : ℕ → ℕ) (σ : List α) (S : ℕ → Finset α) : ℕ := by
  classical
  exact if h : ∃ i, 1 ≤ i ∧ i ≤ σ.length ∧ i % 3 = 1 ∧ ¬ Eq4At m σ S i then Nat.find h
    else σ.length + 1

end ChangingCache.UpperBound


