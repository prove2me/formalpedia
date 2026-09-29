-- Prove2me | Definitions.Def_BlockCycleRotation_Continuant
-- name    : BlockCycleRotation_Continuant
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-09-05T09:35:18.778808+00:00
-- url     : https://prove2.me/theorems/a6b5861f-276d-4949-b7e6-55fb0801b160
-- title:
--   Continuant: Continuants and continued fraction expansions
-- statement:
--   Defines the continuant $K(l)$ of a list of positive integers -- the numerator of the continued fraction $[c_1;c_2,\dots,c_r]$ -- together with the expansion map $\operatorname{cf}$ produced by the Euclidean algorithm. These are the objects of Heilbronn's bijection.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Continuant.lean

-- Generated from BlockCycleRotation/Continuant.lean by skeleton subtraction (Def bundle).
import Mathlib
/-
# Continuants

Heilbronn's bijection (Heilbronn 1969, p. 93), which underlies equation
(eq. heilbron) of Blomer--Bux, sends a continued-fraction expansion
`n = K(c₀,…,c_l)` together with a split point `j` to the quadruple

  `a = K(c₀,…,c_j)`,   `b = K(c_{j+1},…,c_l)`,
  `a' = K(c₀,…,c_{j-1})`, `b' = K(c_{j+2},…,c_l)`,

and the relation `n = a·b + a'·b'` that makes the quadruple a solution is
exactly **Euler's continuant identity**.  This file defines the continuant of a
list and proves that identity.

The continuant is `K[] = 1`, `K[c] = c`, `K(c₀ :: c₁ :: cs) = c₀·K(c₁ :: cs) + K cs`;
`K` of the expansion of a rational is the numerator of its continued fraction.
-/


namespace BlockCycleRotation

/-- The continuant of a list, `K(c₀,…,c_l)`. -/
def K : List ℕ → ℕ
  | [] => 1
  | [c] => c
  | c₀ :: c₁ :: cs => c₀ * K (c₁ :: cs) + K cs















/-! ## Size conditions

Heilbronn's quadruples satisfy `a > a' ≥ 1` and `b > b' ≥ 1`, where `a'` is the
continuant of the truncated prefix and `b'` that of the truncated suffix.  These
follow from positivity together with the two truncation inequalities below. -/













/-! ## Heilbronn's correspondence, forward direction

Splitting an expansion `n = K (l₁ ++ l₂)` at an interior point produces the
quadruple

  `a = K l₁`,  `b = K l₂`,  `a' = K l₁.dropLast`,  `b' = K l₂.tail`,

and the theorem below is that this quadruple satisfies every condition defining
the target set of Heilbronn's bijection. -/



/-! ## The inverse map

Recovering the expansion from the pair `(a, a')` is exactly the Euclidean
algorithm: `K_concat` says `a = c·a' + K m.dropLast` with `c = a / a'` and
`K m.dropLast = a mod a'`, so peeling entries off the end of the list is the
same as running Euclid on `(a, a')`.  This is the point of contact between
Heilbronn's bijection and the remainder sums of `Euclid.lean`. -/

/-- The continued-fraction expansion of `a / a'`, read off by the Euclidean
algorithm.  The quotients are collected from the end of the list backwards. -/
def cf (a a' : ℕ) : List ℕ :=
  if h : a' = 0 then [] else cf a' (a % a') ++ [a / a']
termination_by a'
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero h)



















/-! ## The bridge to remainder sums

Equation (eq. RemainderSum) of the paper: for coprime `n > k`, the remainders
`r₁, r₂, …` of the Euclidean algorithm are exactly the continuants of the
prefixes of the expansion `cf n k`, so the remainder sum of `Euclid.lean` is a
sum of continuants.  This is the point where Tier 1 meets Heilbronn. -/



/-! ## The constraint `k ≤ n/2`

Heilbronn's correspondence also asks `2 ≤ c_l`.  The last entry of `cf n k` is
the first Euclidean quotient `n / k`, so that condition says exactly `2k ≤ n` —
which is the range of shifts the block cycle algorithm recurses on.  The two
lemmas below are the two directions of that equivalence. -/









/-! ## Towards equation (eq. heilbron)

The left-hand side of (eq. heilbron) sums `remSum` over the shifts the
algorithm recurses on.  Expanding each term by `remSum_eq_sum_K` and splitting
off the `j = 0` contribution `K [] = 1` gives the shape of the identity: a count
of shifts, plus a double sum over splits of expansions.  The `j = 0` terms are
what the paper records as `∑ gcd(n,k)`, here all equal to `1` by coprimality. -/

/-- The shifts the block cycle algorithm recurses on that are coprime to `n`. -/
def shifts (n : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter (fun k => 1 ≤ k ∧ 2 * k ≤ n ∧ Nat.gcd n k = 1)

















/-! ## The quadruple index set

The right-hand side of (eq. heilbron) sums over quadruples `(a, b, a', b')`
with `a > a' ≥ 1`, `b > b' ≥ 1`, both coprimality conditions, and
`n = a·b + a'·b'`.  Every component is bounded by `n`, so this is a `Finset`. -/

/-- The quadruples appearing on the right of (eq. heilbron). -/
def quadruples (n : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  ((Finset.range (n + 1)) ×ˢ (Finset.range (n + 1)) ×ˢ (Finset.range (n + 1))
      ×ˢ (Finset.range (n + 1))).filter
    (fun q => 1 ≤ q.2.2.1 ∧ q.2.2.1 < q.1 ∧ 1 ≤ q.2.2.2 ∧ q.2.2.2 < q.2.1
      ∧ Nat.gcd q.1 q.2.2.1 = 1 ∧ Nat.gcd q.2.1 q.2.2.2 = 1
      ∧ n = q.1 * q.2.1 + q.2.2.1 * q.2.2.2)







/-! ## The expansion attached to a quadruple

The inverse of the passage from splits to quadruples: given `(a, b, a', b')`,
reassemble the expansion as `cf a a'` followed by the reverse of `cf b b'`.
Reversing is what `K_reverse` licenses. -/



/-- The expansion attached to a quadruple. -/
def quadExpansion (a b a' b' : ℕ) : List ℕ := cf a a' ++ (cf b b').reverse





/-! ## Equation (eq. heilbron)

The reindexing: the double sum of continuants over interior splits equals the
sum of `a` over Heilbronn's quadruples. -/









/-! ## Aggregating over the gcd

Equation (eq. heilbron) drops both coprimality restrictions.  Recovering it from
the coprime form means classifying each shift `k` by `g = gcd(n,k)`, writing
`k = g·k'` with `k'` coprime to `n/g`.  The following reindexing does that once
and for all, for an arbitrary summand. -/

/-- All shifts the algorithm recurses on, coprime or not. -/
def allShifts (n : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter (fun k => 1 ≤ k ∧ 2 * k ≤ n)











/-! ## The quadruples of (eq. heilbron)

The paper's right-hand side sums `b` over quadruples constrained only by
`gcd(a,a') = 1`.  Classifying those by `e = gcd(b,b')` regroups them into the
divisor-weighted sum over fully coprime quadruples. -/

/-- The quadruples of (eq. heilbron): only `gcd(a,a') = 1` is imposed. -/
def quadruplesAll (n : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  ((Finset.range (n + 1)) ×ˢ (Finset.range (n + 1)) ×ˢ (Finset.range (n + 1))
      ×ˢ (Finset.range (n + 1))).filter
    (fun q => 1 ≤ q.2.2.1 ∧ q.2.2.1 < q.1 ∧ 1 ≤ q.2.2.2 ∧ q.2.2.2 < q.2.1
      ∧ Nat.gcd q.1 q.2.2.1 = 1 ∧ n = q.1 * q.2.1 + q.2.2.1 * q.2.2.2)







/-! ## Removing the gcd condition

The paper writes `R(n)` for the sum of `b` over quadruples with `gcd(a,a') = 1`
— the right-hand side of (eq. heilbron) — and `Q(n)` for the same sum with no
gcd condition at all.  Classifying by `d = gcd(a,a')` gives `Q(n) = ∑_{d ∣ n} R(d)`,
which is what Möbius inversion is then applied to.

Note the summand `b` is untouched by this classification, so unlike the
aggregation of (eq. heilbron) there is no divisor weight. -/

/-- The quadruples with no gcd condition. -/
def quadruplesQ (n : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  ((Finset.range (n + 1)) ×ˢ (Finset.range (n + 1)) ×ˢ (Finset.range (n + 1))
      ×ˢ (Finset.range (n + 1))).filter
    (fun q => 1 ≤ q.2.2.1 ∧ q.2.2.1 < q.1 ∧ 1 ≤ q.2.2.2 ∧ q.2.2.2 < q.2.1
      ∧ n = q.1 * q.2.1 + q.2.2.1 * q.2.2.2)





/-! ## Möbius inversion

With `Q(n) = ∑_{d ∣ n} R(d)` in hand, Möbius inversion gives `R` back from `Q`.
This is equation (mobius) of the paper.  Both are recast over `ℤ` so that
Mathlib's inversion applies. -/

/-- `R(n)`: the sum of `b` over quadruples with `gcd(a,a') = 1`. -/
def Rquad (n : ℕ) : ℤ := ∑ q ∈ quadruplesAll n, (q.2.1 : ℤ)

/-- `Q(n)`: the same sum with no gcd condition. -/
def Qquad (n : ℕ) : ℤ := ∑ q ∈ quadruplesQ n, (q.2.1 : ℤ)







/-! ## Sanity checks

`K(c₀,…,c_l)` is the numerator of the continued fraction `[c₀; c₁,…,c_l]`.
For instance `[2;3,4] = 2 + 1/(3 + 1/4) = 30/13`, so `K[2,3,4] = 30`. -/

-- `K [2,3,4] = 30` and `K [2,3] = 7`, so the pair `(30, 7)` recovers `[2,3,4]`.
-- `(30, 13)` is the reversed expansion, since `K [4,3] = 13`.
-- Euclid on (30,13) gives remainders 13, 4, 1, summing to 18; the prefixes of
-- `cf 30 13 = [4,3,2]` have continuants `K [] = 1`, `K [4] = 4`, `K [4,3] = 13`.
-- `k = 13 > 30/2`, so the last entry of `cf 30 13` is `30/13 = 2`; for `k = 7`
-- we get `30/7 = 4`.
-- Splitting `cf 30 7 = [2,3,4]` at `j = 1` gives `a = K [2] = 2`,
-- `b = K [3,4] = 13`, `a' = K [] = 1`, `b' = K [4] = 4`, and indeed
-- `2 * 13 + 1 * 4 = 30`.
-- Equation (eq. heilbron), checked numerically for several `n`.
-- The remainder sum scales: Euclid on `(dn, dk)` is `d` times Euclid on `(n,k)`.
-- Q(n) = sum over divisors of R, checked numerically.
-- Equation (eq. heilbron) itself, checked numerically.
-- The aggregated Heilbronn identity, checked numerically.

end BlockCycleRotation


