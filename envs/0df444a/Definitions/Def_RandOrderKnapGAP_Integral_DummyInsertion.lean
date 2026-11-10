-- Prove2me | Definitions.Def_RandOrderKnapGAP_Integral_DummyInsertion
-- name    : RandOrderKnapGAP_Integral_DummyInsertion
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T04:26:05.083699+00:00
-- url     : https://prove2.me/theorems/ba987bf5-93f9-4104-9198-a08742ef7b4c
-- title:
--   Online insertion of labeled dummy requests (§B.10.2)
-- statement:
--   $n$ real requests arrive in the order $\sigma$ (a permutation of $[n]$); $d$ labeled dummy requests are inserted online. When $r'$ real and $d'$ dummy requests are still unplaced, the next position receives the next real arrival with probability $r'/(r'+d')$, and otherwise a dummy chosen uniformly among the $d'$ remaining ones (probability $d'/(r'+d')$ in total). An augmented sequence is a bijection $\tau$ from the $n+d$ positions to the real and dummy identities. `insertionProb σ τ` is the probability that the procedure, given $\sigma$, outputs $\tau$: the product over positions of the probability of the step taken (a real at position $t$ must be $\sigma$'s next real arrival).
--
--   **Formalization Note.** $\tau$ is `Fin (n + d) ≃ Fin n ⊕ Fin d`; $r'$ and $d'$ are computed from the numbers of real and dummy identities before position $t$.
-- source:
--   Agrawal, Khan, Pareek, Improved Algorithms in the Random-Order Model: Knapsack, GAP, and Beyond, STOC 2027 submission (manuscript sha256 7825a05f…), pp. 63–64 (PDF 65–66), §B.10.2

import Mathlib

open scoped BigOperators

namespace RandOrderKnapGAP.Integral

/-!
# Online insertion of labeled dummy requests (§B.10.2)

Agrawal, Khan, Pareek, *Improved Algorithms in the Random-Order Model: Knapsack, GAP, and
Beyond*, STOC 2027 submission, §B.10.2, pp. 63–64.

`n` real requests (`Fin n`) arrive in the order `σ : Equiv.Perm (Fin n)` (`σ r` is the `r`-th
real arrival, 0-based). `d` labeled dummies (`Fin d`) are inserted online. An augmented sequence
of the `n + d` identities is `τ : Fin (n + d) ≃ Fin n ⊕ Fin d` (position `t` holds `τ t`).
When `r'` real and `d'` dummy requests are still unplaced, the next position is
* the next real arrival with probability `r'/(r' + d')`;
* a dummy chosen uniformly among the `d'` remaining ones with probability `d'/(r' + d')`.

`insertionProb σ τ` is the probability that this procedure, fed the real arrival order `σ`,
produces `τ`: the product over positions of the probability of the step taken.
-/

open Classical in
/-- The number of real requests placed before position `t` in `τ`. -/
noncomputable def realsBefore {n d : ℕ} (τ : Fin (n + d) ≃ Fin n ⊕ Fin d) (t : Fin (n + d)) : ℕ :=
  (Finset.univ.filter (fun u : Fin (n + d) => u < t ∧ (τ u).isLeft)).card

open Classical in
/-- The number of dummy requests placed before position `t` in `τ`. -/
noncomputable def dummiesBefore {n d : ℕ} (τ : Fin (n + d) ≃ Fin n ⊕ Fin d) (t : Fin (n + d)) :
    ℕ :=
  (Finset.univ.filter (fun u : Fin (n + d) => u < t ∧ (τ u).isRight)).card

/-- The probability of the step taken at position `t`: with `r' = n − realsBefore` and
`d' = d − dummiesBefore`, a real request costs `r'/(r'+d')` and must be the next real arrival
`σ (realsBefore)`; a dummy costs `d'/(r'+d') · 1/d'`. -/
noncomputable def insertionStep {n d : ℕ} (σ : Equiv.Perm (Fin n))
    (τ : Fin (n + d) ≃ Fin n ⊕ Fin d) (t : Fin (n + d)) : ℝ :=
  let r' : ℝ := ((n - realsBefore τ t : ℕ) : ℝ)
  let d' : ℝ := ((d - dummiesBefore τ t : ℕ) : ℝ)
  match τ t with
  | Sum.inl j => r' / (r' + d') * (if (σ.symm j).val = realsBefore τ t then 1 else 0)
  | Sum.inr _ => d' / (r' + d') * (1 / d')

/-- The probability that the online insertion procedure, given the real arrival order `σ`,
produces the augmented sequence `τ`. -/
noncomputable def insertionProb {n d : ℕ} (σ : Equiv.Perm (Fin n))
    (τ : Fin (n + d) ≃ Fin n ⊕ Fin d) : ℝ :=
  ∏ t : Fin (n + d), insertionStep σ τ t

end RandOrderKnapGAP.Integral


