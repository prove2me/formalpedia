-- Prove2me | Definitions.Def_NoisyOWMPC_concreteHalves
-- name    : NoisyOWMPC_concreteHalves
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:57:49.225202+00:00
-- url     : https://prove2.me/theorems/58daba02-397c-49c3-a72f-2a33891ddaf8
-- title:
--   The protocol halves of Theorem 5.24 and admissible parameters
-- statement:
--   The **protocol halves of Theorem 5.24** are the access test of Construction 5.6 and the release test of Construction 5.11 for every receiver, with row count $M$, and the subset selector of Construction 5.17 on $[N]$. A row count $M$ is **admissible** if it is a public polynomial parameter (polynomially bounded, computable from $1^\lambda$ in polynomial time), odd, $M+1$ is a power of two and $M\ge\lambda^5$; a block length $N$ is admissible if it is a public polynomial parameter, even and $N\ge\lambda$. The guard error is $b_N=2e^{-2r_N^2/N}$.
-- source:
--   Ishai, Lu, Zafar, Non-Interactive Cryptography over Noisy Channels from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 3a9569fa…), Theorem 5.24, p.30; §5.2, p.24; Lemmas 5.5, 5.10, 5.16, pp.24–28

import Mathlib
import Definitions.Def_NoisyOWMPC_accessHalf
import Definitions.Def_NoisyOWMPC_releaseHalf
import Definitions.Def_NoisyOWMPC_selectorHalf
import Definitions.Def_NoisyOWMPC_Negligible

namespace NoisyOWMPC

variable {k : ℕ} {X : Type} [Fintype X] {Y : Fin k → Type} [∀ i, Fintype (Y i)]

/-- The **protocol halves of Theorem 5.24** (Ishai, Lu, Zafar, STOC 2027 submission (manuscript
sha256 3a9569fa…), Theorem 5.24, p.30: "Construction 5.23 instantiated with the tests of Theorem
5.22 and the subset selector of Lemma 5.16"): the access test of Construction 5.6 and the release
test of Construction 5.11 for every receiver, with row count `M`, and the subset selector of
Construction 5.17 on `[N]`. -/
noncomputable def concreteHalves (C : ∀ i, DMC X (Y i)) (β : ∀ i, X → Y i → Bool)
    (apx : ℕ → ∀ i, X → Y i → ℚ) (M N : ℕ → ℕ) : Halves k X Y where
  nacc := nAcc k M
  nrel := nRel X M
  N := N
  acc i := accessHalf apx M i
  rel i := releaseHalf C apx β M i
  sel := selectorHalf N

/-- The **public row count** is admissible (§5.2, p.24: "the public row count `M` is odd with
`M + 1` a power of two"; Lemmas 5.5 and 5.10: "every polynomial `M = M(λ) ≥ λ⁵` with `M + 1` a power
of two"): a public polynomial parameter (`PolyParam`: polynomially bounded, computed from `1^λ` in
polynomial time). -/
def AdmissibleM (M : ℕ → ℕ) : Prop :=
  PolyParam M ∧ ∀ lam, Odd (M lam) ∧ (∃ e : ℕ, M lam + 1 = 2 ^ e) ∧ lam ^ 5 ≤ M lam

/-- The **block length** is admissible (Lemma 5.16, p.28: "every even `N = N(λ) ≥ λ` polynomial in
`λ`"), a public polynomial parameter (`PolyParam`). -/
def AdmissibleN (N : ℕ → ℕ) : Prop := PolyParam N ∧ ∀ lam, Even (N lam) ∧ lam ≤ N lam

/-- The guard error `b_N = 2e^{−2r_N²/N}` (Lemma 5.16, p.28). -/
noncomputable def bN (N : ℕ) : ℝ := 2 * Real.exp (-2 * (rN N : ℝ) ^ 2 / (N : ℝ))

end NoisyOWMPC


