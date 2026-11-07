-- Prove2me | Definitions.Def_MatMulTimeLP_Chain
-- name    : MatMulTimeLP_Chain
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:50:01.329418+00:00
-- url     : https://prove2.me/theorems/2429efd8-eb31-40c0-8f72-6cca776cdae8
-- title:
--   Algorithms 3 and 4 as an ideal chain: cleanup, expectations, row-query work
-- statement:
--   This module writes Algorithms 3 and 4 as a finite probability tree on $\mathbb R^n$, with $\Lambda=2^{24}n^2$, $K=\lceil\log_2(360n)\rceil$ and $L=\lceil 8\Lambda\log(64n^{11}(2+320n)^2)\rceil$.
--
--   1. The **label** of coordinate $i$ is $\lfloor\log_2\max\{1,|z_i|\}\rfloor$, and $B_j(z)$ is the set of coordinates with label $j$. A bucket is **violated** if $2^j|B_j(z)|>160n$.
--   2. **Cleanup**: while a bucket is violated, take the largest violated scale $j$ and replace $z_i$ by $z_i/3$ on $B_j(z)$. It returns the new point and the number $C$ of coordinate shrinkages, counting multiplicity.
--   3. The **coordinate step** at $i$ replaces $z_i$ by $(\psi')^{-1}(\psi'(z_i)+r_i/(8w_i))$, where $w_i=(2+|z_i|)^2+r_i^2$.
--   4. One **iteration** selects $i$ with probability $w_i/\Lambda$, takes the coordinate step and runs cleanup; with the remaining probability $z$ is unchanged. The module defines the expectation of a function over one iteration (`stepExp`), of a function of $z_L$ (`iterExp`), and of a running sum (`runSum`).
--   5. **Reachable** points are those obtained from $0$ by any sequence of selected coordinates.
--   6. **Row-query work** counts the operation bounds of Theorem 5.13 at the labels of each moment: $K+|L_{\ge\ell(i)}|$ for a query, $K+|L_{>\ell(i)}|$ for a value update, and $K+|L_{[p,q]}|$ for a label change.
--
--   These objects carry the convergence analysis, which is independent of the data structures that implement the sampling.
--
--   **Formalization Note** As on p.25, Line 14 sits inside the `if`, so an iteration that returns $\bot$ does not run cleanup. Cleanup is written with fuel; the verification file proves that it leaves no violated bucket, and checks the instance $n=1$, $z=1000$.
-- source:
--   Jiang–Kyng–Zöcklein, Solving Linear Programs in Truly Matrix Multiplication Time, STOC 2027 submission (manuscript sha256 6539350a…81ffcc), Algorithms 3, 4 p.25; buckets pp.24, 28; labels (13) p.34; Algorithm 5 p.35; Theorem 5.13 p.32

import Mathlib
import Definitions.Def_MatMulTimeLP_FixPoint

namespace MatMulTimeLP

open Matrix

/-!
# Algorithms 3 and 4 as an ideal chain

Jiang–Kyng–Zöcklein, *Solving Linear Programs in Truly Matrix Multiplication Time*, STOC 2027
submission (manuscript sha256 6539350a…81ffcc): Algorithms 3, 4 p.25; the buckets p.24, p.28; the labels
(13) p.34; Algorithm 5 p.35; the operation costs of Theorem 5.13 p.32.

**Formalization Note** The chain samples coordinate `i` with the exact probability `wᵢ/Λ`, as the
sections on convergence assume. Expectations are finite trees: `stepExp` is one iteration, `iterExp`
and `runSum` iterate it, so no measure appears. As on p.25, a `⊥` iteration leaves `z` unchanged and
does not run `Cleanup` (Line 14 sits inside the `if`). The buckets come from one label,
`lab z i = ⌊log₂ max{1, |zᵢ|}⌋`, as on p.34. `rowWork` counts Theorem 5.13's operation bounds, not machine
steps. `Violated` compares natural numbers.
-/

/-- `Λ = 2²⁴ n²`, Algorithm 3, Line 1. -/
noncomputable def bigLam (n : ℕ) : ℝ := 2 ^ 24 * (n : ℝ) ^ 2

/-- `K = ⌈log₂(360 n)⌉`, Algorithm 3, Line 1. -/
noncomputable def bigK (n : ℕ) : ℕ := ⌈Real.logb 2 (360 * (n : ℝ))⌉₊

/-- `L = ⌈8Λ log(64 n¹¹ (2 + 320 n)²)⌉`, Algorithm 3, Line 2. -/
noncomputable def stepsL (n : ℕ) : ℕ :=
  ⌈8 * bigLam n * Real.log (64 * (n : ℝ) ^ 11 * (2 + 320 * (n : ℝ)) ^ 2)⌉₊

variable {n : ℕ}

/-- The label `ℓ(i) = ⌊log₂ max{1, |zᵢ|}⌋` of (13), p.34: `Nat.log 2 0 = Nat.log 2 1 = 0`. -/
noncomputable def lab (z : Fin n → ℝ) (i : Fin n) : ℕ := Nat.log 2 ⌊|z i|⌋₊

open scoped Classical in
/-- The bucket `B_j(z)`, p.24: the coordinates with label `j`. -/
noncomputable def bucket (z : Fin n → ℝ) (j : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i => lab z i = j

/-- The bucket `B_j(z)` is violated: `2^j |B_j(z)| > 160 n`, Algorithm 4, Line 1. -/
def Violated (z : Fin n → ℝ) (j : ℕ) : Prop := 160 * n < 2 ^ j * (bucket z j).card

/-- The largest label of `z`, which bounds every violated scale for `n ≥ 1`. -/
noncomputable def maxScale (z : Fin n → ℝ) : ℕ := Finset.univ.sup (lab z)

/-- The point `z'` of Lemma 5.9, p.29: `zᵢ/3` on `B_j(z)`, unchanged elsewhere. -/
noncomputable def shrink (z : Fin n → ℝ) (j : ℕ) : Fin n → ℝ :=
  fun i => if lab z i = j then z i / 3 else z i

open scoped Classical in
/-- The loop of Algorithm 4 with fuel: while a scale is violated, shrink the bucket of the largest one,
adding `|B_j|` to the shrink count. -/
noncomputable def cleanupAux : ℕ → (Fin n → ℝ) → ℕ → (Fin n → ℝ) × ℕ
  | 0, z, C => (z, C)
  | m + 1, z, C =>
    let j := Nat.findGreatest (Violated z) (maxScale z)
    if Violated z j then cleanupAux m (shrink z j) (C + (bucket z j).card) else (z, C)

/-- `Cleanup` (Algorithm 4): the new point and the number `C` of coordinate shrinkages, counting
multiplicity. The largest violated scale strictly decreases, so `maxScale z + 1` rounds suffice; the
verification file proves that the output has no violated bucket. -/
noncomputable def cleanup (z : Fin n → ℝ) : (Fin n → ℝ) × ℕ :=
  cleanupAux (maxScale z + 1) z 0

/-- The weight `wᵢ = (2 + |zᵢ|)² + rᵢ²`, p.24. -/
noncomputable def weight (H : Matrix (Fin n) (Fin n) ℝ) (h z : Fin n → ℝ) (i : Fin n) : ℝ :=
  (2 + |z i|) ^ 2 + residual H h z i ^ 2

/-- The new `i`-th coordinate `(ψ')⁻¹(ψ'(zᵢ) + rᵢ/(8wᵢ))`, Algorithm 3, Line 12. -/
noncomputable def coordNew (H : Matrix (Fin n) (Fin n) ℝ) (h z : Fin n → ℝ) (i : Fin n) : ℝ :=
  dpsiInv (dpsi (z i) + residual H h z i / (8 * weight H h z i))

/-- The point after the coordinate step, before cleanup. -/
noncomputable def coordStep (H : Matrix (Fin n) (Fin n) ℝ) (h z : Fin n → ℝ) (i : Fin n) :
    Fin n → ℝ :=
  Function.update z i (coordNew H h z i)

/-- The expectation of `Φ` over one iteration of Algorithm 3 from `z`, where `Φ` reads the next point
and the shrink count `C`: coordinate `i` with probability `wᵢ/Λ`, followed by cleanup; with the
remaining probability the point stays and `C = 0`. -/
noncomputable def stepExp (H : Matrix (Fin n) (Fin n) ℝ) (h z : Fin n → ℝ)
    (Φ : (Fin n → ℝ) × ℕ → ℝ) : ℝ :=
  ∑ i, weight H h z i / bigLam n * Φ (cleanup (coordStep H h z i)) +
    (1 - ∑ i, weight H h z i / bigLam n) * Φ (z, 0)

/-- `E[Φ(z_L)]` for the chain started at `z`. -/
noncomputable def iterExp (H : Matrix (Fin n) (Fin n) ℝ) (h : Fin n → ℝ) :
    ℕ → (Fin n → ℝ) → ((Fin n → ℝ) → ℝ) → ℝ
  | 0, z, Φ => Φ z
  | L + 1, z, Φ => stepExp H h z fun o => iterExp H h L o.1 Φ

/-- `E[∑_{k<L} (g(z_k) + c · C_k)]` for the chain started at `z`. -/
noncomputable def runSum (H : Matrix (Fin n) (Fin n) ℝ) (h : Fin n → ℝ) (g : (Fin n → ℝ) → ℝ)
    (c : ℝ) : ℕ → (Fin n → ℝ) → ℝ
  | 0, _ => 0
  | L + 1, z => g z + stepExp H h z fun o => c * (o.2 : ℝ) + runSum H h g c L o.1

/-- The iterates of Algorithm 3 for **any** sequence of selected coordinates (p.38): the closure of
`0` under "coordinate step, then cleanup". -/
inductive Reachable (H : Matrix (Fin n) (Fin n) ℝ) (h : Fin n → ℝ) : (Fin n → ℝ) → Prop
  | zero : Reachable H h 0
  | step {z : Fin n → ℝ} (i : Fin n) :
      Reachable H h z → Reachable H h (cleanup (coordStep H h z i)).1

open scoped Classical in
/-- `|L_{≥ℓ}|`, Theorem 5.13, p.32. -/
noncomputable def labelsGe (z : Fin n → ℝ) (l : ℕ) : ℕ :=
  (Finset.univ.filter fun j => l ≤ lab z j).card

open scoped Classical in
/-- `|L_{[p,q]}|`, Theorem 5.13, p.32. -/
noncomputable def labelsBetween (z : Fin n → ℝ) (p q : ℕ) : ℕ :=
  (Finset.univ.filter fun j => p ≤ lab z j ∧ lab z j ≤ q).card

/-- The cost `K + |L_{≥ℓ(i)}|` of `Query(i)`, Theorem 5.13. -/
noncomputable def queryCost (z : Fin n → ℝ) (i : Fin n) : ℕ :=
  bigK n + labelsGe z (lab z i)

open scoped Classical in
/-- The row-query cost of `UpdateCoordinate(i, w)`, Algorithm 5, Lines 20 and 25, at the labels before
the call: `SetValue` costs `K + |L_{>ℓ(i)}|`, and if the label changes then `SetLabel` costs
`K + |L_{[p,q]}|`. -/
noncomputable def updateCost (z : Fin n → ℝ) (i : Fin n) (w : ℝ) : ℕ :=
  let c := lab (Function.update z i w) i
  bigK n + labelsGe z (lab z i + 1) +
    if c = lab z i then 0 else bigK n + labelsBetween z (min (lab z i) c) (max (lab z i) c)

/-- The total row-query cost of shrinking the listed coordinates one at a time, each at the labels of
that moment. -/
noncomputable def shrinkWork : List (Fin n) → (Fin n → ℝ) → ℕ
  | [], _ => 0
  | i :: l, z => updateCost z i (z i / 3) + shrinkWork l (Function.update z i (z i / 3))

open scoped Classical in
/-- The row-query cost of the loop of Algorithm 4, processing each bucket in coordinate order. -/
noncomputable def cleanupWorkAux : ℕ → (Fin n → ℝ) → ℕ
  | 0, _ => 0
  | m + 1, z =>
    let j := Nat.findGreatest (Violated z) (maxScale z)
    if Violated z j then
      shrinkWork ((List.finRange n).filter fun i => lab z i = j) z + cleanupWorkAux m (shrink z j)
    else 0

/-- The row-query cost of `Cleanup` from `z`. -/
noncomputable def cleanupWork (z : Fin n → ℝ) : ℕ :=
  cleanupWorkAux (maxScale z + 1) z

/-- The row-query cost of an iteration that selects `i`: the query, the update, then the cleanup. -/
noncomputable def rowWork (H : Matrix (Fin n) (Fin n) ℝ) (h z : Fin n → ℝ) (i : Fin n) : ℕ :=
  queryCost z i + updateCost z i (coordNew H h z i) + cleanupWork (coordStep H h z i)

/-- The expected total row-query cost of `L` iterations started at `z`. -/
noncomputable def rowExp (H : Matrix (Fin n) (Fin n) ℝ) (h : Fin n → ℝ) :
    ℕ → (Fin n → ℝ) → ℝ
  | 0, _ => 0
  | L + 1, z =>
    ∑ i, weight H h z i / bigLam n *
        ((rowWork H h z i : ℝ) + rowExp H h L (cleanup (coordStep H h z i)).1) +
      (1 - ∑ i, weight H h z i / bigLam n) * rowExp H h L z

end MatMulTimeLP


