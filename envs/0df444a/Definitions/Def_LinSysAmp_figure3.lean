-- Prove2me | Definitions.Def_LinSysAmp_figure3
-- name    : LinSysAmp_figure3
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:59:29.60942+00:00
-- url     : https://prove2.me/theorems/231f7b9e-1b9c-4ab7-a584-fcaaaff0b60d
-- title:
--   Algorithm $\mathcal B_k$ of Figure 3, as a distribution
-- statement:
--   Given an oracle $\mathcal O$, the rank $k$ and a number of attempts $t$, the algorithm $\mathcal B_k^{\mathcal O}(M,y)$ does the following.
--
--   1. For $j=1,\dots,t$:
--      1. Sample an invertible update $R$ of rank $k$. If $R=\bot$, go to the next attempt.
--      2. Sample $z$ uniformly from $F^n$ and compute $w=\mathcal O(RM,R(y+Mz))$. If $M(w-z)=y$, output $w-z$ and stop.
--   2. Output $\bot$.
--
--   This item is the output distribution of that procedure. The attempts restart from the original $M$: the algorithm is not a walk.
--
--   **Formalization Note** The definition recurses on the number of remaining attempts, with fresh randomness (the update, $z$ and the oracle's coins) at every attempt. It is used by the milestones only. The goal theorem is about programs of the machine and does not mention this distribution.
-- source:
--   Couteau, Melissaris, Radhika Sajith, Hardness Self-Amplification in Linear Algebra and Fine-Grained Cryptography, arXiv:2611.04680 (version held, sha256 af7a90ac…), Figure 3, p.22 (PDF p.24)

import Mathlib
import Definitions.Def_LinSysAmp_rankUpdate

set_option autoImplicit false

open Matrix

namespace LinSysAmp

/-!
# Algorithm `B_k` of Figure 3, as a distribution

G. Couteau, N. Melissaris, T. Radhika Sajith, *Hardness Self-Amplification in Linear Algebra and
Fine-Grained Cryptography*, arXiv:2611.04680 (version held, sha256 af7a90ac…), Figure 3, p.22
(PDF p.24):

"Algorithm B^O_k(M, y). Parameters: rank k and number of attempts t.
1. For j = 1, …, t: (a) Sample an invertible update R of rank k. If R = ⊥, go to the next attempt.
(b) Sample z ← F_qⁿ and compute w = O(RM, R(y + Mz)). If M(w − z) = y, output w − z and stop.
2. Output ⊥."

**Formalization Note.** This is the output distribution of Figure 3 (`none` is `⊥`), written by
recursion on the number `t` of remaining attempts, with fresh randomness (update, `z`, the oracle's
coins) at every attempt. It is used by the milestones only; the goal theorem is about programs of the
machine `LinSysAmp.Machine` and does not mention this definition.
-/

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- One attempt of Figure 3: sample `R`; on `⊥` fail; else sample `z`, query
`w = O(RM, R(y + Mz))`, and return `some (w − z)` if `M(w − z) = y`, else fail.
(arXiv:2611.04680, version held, sha256 af7a90ac…, Figure 3, p.22 (PDF p.24).) -/
noncomputable def attempt {n : ℕ} (O : Oracle n F) (k : ℕ) (M : Matrix (Fin n) (Fin n) F)
    (y : Fin n → F) : PMF (Option (Fin n → F)) :=
  (updateDist n k F).bind fun r =>
    match r with
    | none => PMF.pure none
    | some R => (PMF.uniformOfFintype (Fin n → F)).bind fun z =>
        (O (R * M) (R *ᵥ (y + M *ᵥ z))).bind fun w =>
          PMF.pure (if M *ᵥ (w - z) = y then some (w - z) else none)

/-- Figure 3 with `t` attempts: the output distribution of `B^O_k(M, y)`.
(arXiv:2611.04680, version held, sha256 af7a90ac…, Figure 3, p.22 (PDF p.24).) -/
noncomputable def figure3 {n : ℕ} (O : Oracle n F) (k : ℕ) :
    ℕ → Matrix (Fin n) (Fin n) F → (Fin n → F) → PMF (Option (Fin n → F))
  | 0, _, _ => PMF.pure none
  | t + 1, M, y => (attempt O k M y).bind fun r =>
      match r with
      | some x => PMF.pure (some x)
      | none => figure3 O k t M y

end LinSysAmp


