-- Prove2me | Definitions.Def_ApproxDegComp_Supplement_prTh
-- name    : ApproxDegComp_Supplement_prTh
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T12:58:11.700566+00:00
-- url     : https://prove2.me/theorems/e9d93483-545e-45d0-abfe-9370ee0b17d0
-- title:
--   Promise threshold function $\mathrm{PrTH}^t_m$
-- statement:
--   For $x\in\{0,1\}^m$ write $|x|$ for its **Hamming weight**, the number of coordinates equal to $1$. For integers $m\ge0$ and $t\ge1$, the **promise threshold function** $\mathrm{PrTH}^t_m$ is the partial Boolean function on $\{0,1\}^m$ given by
--
--   $$\mathrm{PrTH}^t_m(x)=\begin{cases}1,&|x|=t,\\0,&|x|=t-1,\\\text{undefined},&\text{otherwise.}\end{cases}$$
--
--   Its domain is the two Hamming layers of weight $t-1$ and $t$. It is the inner function of Theorem 19, the warm-up case of the composition theorem in which the inner function is partial.
--
--   **Formalization Note** A partial function is the published `NoPerfectRandComp.PartialFn` (a domain set and a value function read only on the domain). The condition $|x|=t-1$ is written $|x|+1=t$, so no natural-number subtraction occurs.
-- source:
--   Pednekar–Podder, On the Composition Theorem for Approximate Degree, Randomized and Exact Quantum Query Complexity, STOC 2027 submission (manuscript sha256 b9a66c7fdb2afdb57851f3734661cd2140455987b17e2a1e2400586be814092b), Definition 16, p.13 (restated in Theorem 19, p.20)

import Mathlib
import Definitions.Def_NoPerfectRandComp_PartialFn

namespace ApproxDegComp

namespace Supplement

/-- **Hamming weight** `|x|` of `x ∈ {0,1}^m`: the number of coordinates equal to `1`
(Pednekar–Podder, STOC 2027 submission (manuscript sha256 b9a66c7f…), Definitions 15–16, p.13). -/
def hamWt {m : ℕ} (x : Fin m → Bool) : ℕ :=
  (Finset.univ.filter fun j => x j = true).card

/-- **Promise threshold function** `PrTH^t_m` (Definition 16, p.13; restated in Theorem 19,
p.20). Pednekar–Podder, *On the Composition Theorem for Approximate Degree, Randomized and Exact
Quantum Query Complexity*, STOC 2027 submission (manuscript sha256 b9a66c7f…), Definition 16,
p.13: "PrTH^t_m(x) = 1 if |x| = t, 0 if |x| = t − 1, undefined otherwise."

It is the partial Boolean function on `{0,1}^m` whose domain is the inputs of Hamming weight
`t − 1` or `t`, with value `1` exactly on weight `t`.

**Formalization Note** A partial function is the published `NoPerfectRandComp.PartialFn`
(domain set, value function; the value off the domain is never read). "Undefined" means
"outside `dom`". The weight condition `|x| = t − 1` is written `|x| + 1 = t`, so no natural-number
subtraction occurs: for `t = 0` that branch is empty (the statements that use `PrTH` assume
`1 ≤ t`, as the paper does). -/
def prTh (m t : ℕ) : NoPerfectRandComp.PartialFn (Fin m) where
  dom := {x | hamWt x + 1 = t ∨ hamWt x = t}
  val := fun x => decide (hamWt x = t)

end Supplement

end ApproxDegComp


