-- Prove2me | Definitions.Def_RestrictedAP_Counting_MuP
-- name    : RestrictedAP_Counting_MuP
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T06:19:06.825336+00:00
-- url     : https://prove2.me/theorems/70d3cddf-28a1-405c-8010-4377ddb4e629
-- title:
--   The somewhat restricted 3-AP distribution $\mu_p$ on $\mathbb F_p^3$
-- statement:
--   For a prime $p\ge3$, $\mu_p$ is the law of $(x,\ x+a,\ x+2a)\in\mathbb F_p^3$ for independent uniform $x\in\mathbb F_p$ and $a\in\{0,1,2\}$ ($a$ read in $\mathbb F_p$): the weight of $t\in\mathbb F_p^3$ is
--   $$\mu_p(t)=\frac{\#\{(x,a)\in\mathbb F_p\times\{0,1,2\}:(x,x+a,x+2a)=t\}}{3p}.$$
--   Its tensor power $\mu_p^{\otimes n}$ is the law of the triple $(x,x+a,x+2a)$ with $x$ uniform on $\mathbb F_p^n$ and $a$ uniform on $\{0,1,2\}^n$, so Theorem 1.2 is Theorem 1.4 for $\mu_p$ (remark in §1.2).
--
--   **Formalization Note.** `muP p` on `ZMod p × ZMod p × ZMod p`, the difference $a$ ranging over `Fin 3` cast through `ℕ`.
-- source:
--   Bhangale, Khot, Liu, Minzer, A Counting Lemma for Somewhat Restricted 3-APs, arXiv:2608.17365 (copy sha256 de0b96c1…), p. 3, §1.2 (remark before Theorem 1.4)

import Mathlib

namespace RestrictedAP.Counting

/-!
# The somewhat restricted 3-AP distribution `μ_p` on `F_p^3`

Bhangale, Khot, Liu, Minzer, *A Counting Lemma for Somewhat Restricted 3-APs*,
arXiv:2608.17365 (copy sha256 de0b96c1…), p. 3, §1.2 (the remark deriving Theorem 1.2 from
Theorem 1.4).

`muP p` is the law of `(x, x + a, x + 2a)` for independent uniform `x ∈ F_p` and
`a ∈ {0, 1, 2}` (cast into `F_p`): the weight of `t ∈ F_p^3` is the number of pairs
`(x, a) ∈ F_p × {0,1,2}` with `(x, x + a, x + 2a) = t`, divided by `3p`. Its `n`-fold tensor
power is the law of the triple `(x, x + a, x + 2a)` of Theorem 1.2.
-/

/-- The somewhat restricted 3-AP distribution `μ_p` on `ZMod p × ZMod p × ZMod p`. -/
noncomputable def muP (p : ℕ) [NeZero p] : ZMod p × ZMod p × ZMod p → ℝ :=
  fun t => ((Finset.univ.filter (fun xa : ZMod p × Fin 3 =>
      (xa.1, xa.1 + ((xa.2 : ℕ) : ZMod p), xa.1 + 2 * ((xa.2 : ℕ) : ZMod p)) = t)).card : ℝ) /
    (3 * (p : ℝ))

end RestrictedAP.Counting


