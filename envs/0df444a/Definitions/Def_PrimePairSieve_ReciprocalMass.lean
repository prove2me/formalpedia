-- Prove2me | Definitions.Def_PrimePairSieve_ReciprocalMass
-- name    : PrimePairSieve_ReciprocalMass
-- status  : Definition
-- author  : @moona3k
-- created : 2026-10-04T21:02:40.316972+00:00
-- url     : https://prove2.me/theorems/d4e1f470-296c-4661-9db1-a5d4f12cc8d0
-- title:
--   Disjoint interval mass certificates for reciprocal sieve sums
-- statement:
--   This interface stores a finite collection of integer intervals and certified lower bounds for their squarefree sieve-weight masses. For the literal weight
--
--   $$w(n)=\begin{cases}\prod_{p\mid n}b_p,&n\text{ squarefree},\\0,&\text{otherwise},\end{cases}\qquad b_2=1,\quad b_p=2/(p-2)\ (p>2),$$
--
--   a bucket records integers $(a,b,M)$. At positive scale $S$, validity means $M/S\le\sum_{a\le n\le b}w(n)$ for every bucket. The interface also defines integer-rounded row masses, structural checks on row lists, and the endpoint integer sum
--
--   $$A(L)=\sum_{(a,b,M):\ b\le L}\left\lfloor\frac{ML}{L+b}\right\rfloor.$$
--
--   The definition does not assert validity or disjointness. Separate soundness theorems prove that checked factor data imply valid masses, and that positive, disjoint intervals imply $A(L)/S$ is a lower bound for the original reciprocal sum. This separates one-time weight verification from repeated endpoint evaluation.
--
--   Source: the literal weight and reciprocal sum in [the registered reciprocal threshold](https://prove2.me/theorems/dd059254-26a3-414d-be7b-44976fbe068b), and the row interface of [the accepted batch checker](https://prove2.me/theorems/ad4bcc2f-0185-49a3-a4b5-1f232307b1c2). This is a computational certificate interface, not a new analytic estimate.
-- source:
--   Finite certificate for https://prove2.me/theorems/dd059254-26a3-414d-be7b-44976fbe068b; exact argument and scope in the statement.

import Definitions.Def_PrimePairSieve_ReciprocalBatch
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.List.Basic
open scoped BigOperators
set_option autoImplicit false
namespace PrimePairSieve.ReciprocalMass
structure Bucket where
  lower : ℕ
  upper : ℕ
  mass : ℕ
  deriving DecidableEq

def roundedMass (scale : ℕ) (rows : List ReciprocalBatch.Row) : ℕ :=
  (rows.map (fun r => scale * r.a / r.b)).sum

def massCheck (scale : ℕ) (cert : Bucket × List ReciprocalBatch.Row) : Bool :=
  decide ((cert.2.map ReciprocalBatch.Row.n).IsChain (· < ·)) &&
  cert.2.all (fun r => decide (cert.1.lower ≤ r.n ∧ r.n ≤ cert.1.upper)) &&
  decide (roundedMass scale cert.2 = cert.1.mass)

noncomputable def Valid (scale : ℕ) (buckets : Finset Bucket) : Prop :=
  ∀ b ∈ buckets, (b.mass : ℝ) / scale ≤
    ∑ n ∈ Finset.Icc b.lower b.upper, ReciprocalBatch.weight n

def endpointSum (L : ℕ) (buckets : Finset Bucket) : ℕ :=
  ∑ b ∈ buckets.filter (fun b => b.upper ≤ L), b.mass * L / (L + b.upper)
end PrimePairSieve.ReciprocalMass


