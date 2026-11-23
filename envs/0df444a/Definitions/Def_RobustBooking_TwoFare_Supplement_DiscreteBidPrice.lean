-- Prove2me | Definitions.Def_RobustBooking_TwoFare_Supplement_DiscreteBidPrice
-- name    : RobustBooking_TwoFare_Supplement_DiscreteBidPrice
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T04:44:05.679452+00:00
-- url     : https://prove2.me/theorems/0ac96377-b597-4d10-a701-e53e13bd10d1
-- title:
--   The discrete bid-price problem, the order quantity control $P_\rho$ of Eqs. (18)–(19), and $G$, $G^{(-1)}$
-- statement:
--   These definitions set up the **discrete bid-price control problem** of §2.3 of Ball and Queyranne (2009). There are $n$ units of capacity, $n$ an integer. An instance is a finite sequence of unit orders with offered fares $O_1,O_2,\dots$; each order is accepted whole or rejected at its arrival, and at most $n$ orders are accepted. A policy decides from the earlier fares, its earlier decisions and the current fare. The online revenue $v'(I)$ is the total fare of the accepted orders and the offline optimum $v^*(I)$ is the largest total fare of at most $n$ orders of $I$.
--
--   For $f_{\min}>0$ and a parameter $\rho>0$, Eqs. (18)–(19) define, for integers $q\ge 0$,
--   $$P_\rho(q)=\begin{cases} f_{\min} & q\le\lceil\rho n\rceil-1,\\[2pt] f_{\min}\Big(1+\dfrac{1}{\rho n}\Big)^{\lceil q-\rho n-1\rceil} & q\ge\rho n.\end{cases}$$
--   The exponent is an integer and can be $-1$. The **order quantity control policy** based on $P_\rho$ (p. 956): with $\hat q$ orders accepted so far and current fare $O$, reject if $O<P_\rho(\hat q)$; otherwise accept iff $P_\rho(\hat q+1)\le O$ (the order that brings the total to $\hat q+1$ needs a fare of at least $P_\rho(\hat q+1)$), subject to $\hat q<n$.
--
--   Finally $G(x)=(1+1/x)^x$ for $x>0$, which increases from $1$ to $e$, and $G^{(-1)}$ is its inverse on $[1,e)$: $G^{(-1)}(1)=0$, and for $1<a<e$, $G^{(-1)}(a)$ is the unique $x>0$ with $G(x)=a$.
--
--   These are the objects of Theorem 8, the discrete counterpart of the continuous bid-price guarantee of Theorem 7.
--
--   **Formalization Note** Instances are `List ℝ`; the fare range $[f_{\min},f_{\max}]$ is a hypothesis of the theorem. The offline optimum is `sSup` of a finite nonempty set. `Prho` uses `Int.ceil` and an integer power (`zpow`), literally as printed; for a natural number $q$ the condition $q\le\lceil\rho n\rceil-1$ is the negation of $q\ge\rho n$. $P_\rho$ is not clipped at $f_{\max}$. `Ginv a` is defined as $\sup\{x>0 : G(x)\le a\}$: this is $0$ at $a=1$ (empty set) and the true inverse for $1<a<e$; it is used only for such arguments. The capacity test $\hat q<n$ is made by the run.
-- source:
--   Ball, Queyranne, Toward Robust Revenue Management: Competitive Analysis of Online Booking, Oper. Res. 57(4), 2009, p. 956 (bid-price problem, policy A′_θ, discrete version α ∈ {0,1}), p. 960, Eqs. (18)–(19), p. 961 (G and G^(−1))

import Mathlib

namespace RobustBooking.TwoFare.Supplement

/-- A deterministic online policy for the discrete bid-price problem (Ball–Queyranne 2009, p. 956):
from the history (earlier fares, each with its accept/reject decision) and the fare `O` of the
current unit order it decides to accept or reject. -/
abbrev BPPolicy : Type := List (ℝ × Bool) → ℝ → Bool

/-- Running a discrete bid-price policy with integer capacity `n`: an order is accepted iff fewer
than `n` orders have been accepted and the policy accepts it. -/
def bpRunFrom (n : ℕ) (A : BPPolicy) : List (ℝ × Bool) → ℕ → List ℝ → List Bool
  | _, _, [] => []
  | hist, used, O :: rest =>
      let a : Bool := decide (used < n) && A hist O
      a :: bpRunFrom n A (hist ++ [(O, a)]) (if a then used + 1 else used) rest

/-- The online revenue `v′(I)`: the sum of the fares of the accepted orders. -/
noncomputable def bpRevenue (n : ℕ) (A : BPPolicy) (I : List ℝ) : ℝ :=
  (List.zipWith (fun O a => if a then O else 0) I (bpRunFrom n A [] 0 I)).sum

/-- The optimal offline revenue `v*(I)` of the discrete bid-price problem: the largest total fare
of a set of at most `n` orders of `I` (attained; the set of values is finite and contains `0`). -/
noncomputable def bpOpt (n : ℕ) (I : List ℝ) : ℝ :=
  sSup {v : ℝ | ∃ S : Finset (Fin I.length), S.card ≤ n ∧ v = ∑ i ∈ S, I.get i}

/-- Eqs. (18)–(19), p. 960: `P_ρ(q) = f_min` for `q ≤ ⌈ρn⌉ - 1`, and
`P_ρ(q) = f_min (1 + 1/(ρn))^⌈q - ρn - 1⌉` for `q ≥ ρn` (integer exponent, possibly `-1`).
For a natural number `q` the two cases are exhaustive and disjoint. -/
noncomputable def Prho (fmin ρ : ℝ) (n : ℕ) (q : ℕ) : ℝ :=
  if (q : ℤ) ≤ ⌈ρ * n⌉ - 1 then fmin
  else fmin * (1 + 1 / (ρ * n)) ^ (⌈(q : ℝ) - ρ * n - 1⌉)

/-- The number of orders accepted so far, `q̂`. -/
def acceptedCount (hist : List (ℝ × Bool)) : ℕ :=
  (hist.filter (fun p => p.2)).length

/-- The discrete order quantity control policy `A′` based on `P_ρ` (p. 956): with `q̂` orders
accepted and current fare `O`, reject if `O < P_ρ(q̂)`; otherwise set
`x = sup {α ∈ {0, 1} : P_ρ(α + q̂) ≤ O}`, i.e. accept iff `P_ρ(q̂) ≤ O` and `P_ρ(q̂ + 1) ≤ O`.
The capacity constraint `q̂ + α ≤ n` is enforced by the run. -/
noncomputable def orderQtyPolicy (fmin ρ : ℝ) (n : ℕ) : BPPolicy := fun hist O =>
  decide (Prho fmin ρ n (acceptedCount hist) ≤ O ∧ Prho fmin ρ n (acceptedCount hist + 1) ≤ O)

/-- `G(x) = (1 + 1/x)^x` (real power), p. 961. -/
noncomputable def Gfun (x : ℝ) : ℝ := (1 + 1 / x) ^ x

/-- The inverse `G^(-1)` of p. 961, as the supremum of `{x > 0 : G(x) ≤ a}`. Since `G` is
increasing on `(0, ∞)` from `1` to `e`, this is `0` at `a = 1` (the set is empty) and the unique
`x > 0` with `G(x) = a` for `1 < a < e`; other arguments are not used. -/
noncomputable def Ginv (a : ℝ) : ℝ := sSup {x : ℝ | 0 < x ∧ Gfun x ≤ a}

end RobustBooking.TwoFare.Supplement


