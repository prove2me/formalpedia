-- Prove2me | Definitions.Def_PrivLearn_Parity_Amplified
-- name    : PrivLearn_Parity_Amplified
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T07:51:29.49797+00:00
-- url     : https://prove2.me/theorems/307492c1-3c81-4eeb-9e59-e8657585f0e4
-- title:
--   The amplified private PAC learner $\mathcal A^*(z,\varepsilon,\alpha,\beta)$ for PARITY
-- statement:
--   Let $c, c' > 0$ be the constants of the algorithm, $d \in \mathbb N$, $\varepsilon, \alpha, \beta > 0$, and $z = (z_1,\dots,z_n)$ a database of labeled examples $z_i = (x_i, y_i)$. Algorithm $\mathcal A^*(z,\varepsilon,\alpha,\beta)$ (p. 17):
--
--   1. $\beta' = \beta/2$, $\alpha' = \alpha/5$, $k = \lceil \log_{4/3}(1/\beta') \rceil$, $n' = \lceil c d/(\varepsilon\alpha') \rceil$, $s = \lceil (c'k/(\alpha'\varepsilon)) \log_2(k/\beta') \rceil$;
--   2. if $n \le kn' + s$, return "insufficient samples";
--   3. the training set is $\bar z = (z_1,\dots,z_{kn'})$ and the test set is $\hat z = (z_{kn'+1},\dots,z_{kn'+s})$;
--   4. $\bar z$ is divided into $k$ consecutive blocks $\bar z_j$ of size $n'$;
--   5. for each $j$, $h_j = \mathcal A(\bar z_j, \varepsilon)$, and the perturbed training error is
--   $$
--   \widehat{\mathrm{err}}_T(h_j) = \frac{|\{z_i \in \hat z : h_j(x_i) \neq y_i\}|}{s} + \eta_j, \qquad \eta_j \sim \mathrm{Lap}\Big(\frac{k}{s\varepsilon}\Big);
--   $$
--   6. output $h^* = h_{j^*}$ where $j^*$ minimizes $\widehat{\mathrm{err}}_T(h_j)$.
--
--   The $k$ runs of $\mathcal A$ and the $k$ Laplace noises are mutually independent. The output space consists of "insufficient samples", $\bot$, and the hypotheses $c_r$.
--
--   This is the algorithm of Theorem 4.4: amplification of $\mathcal A$'s constant success probability by private model selection on a test set.
--
--   **Formalization Note** (1) The paper prints $k = \lceil \log_{3/4}(1/\beta') \rceil$, which is $\le 0$; its proof needs $(3/4)^k \le \beta'$, so the base is corrected to $4/3$. (2) Sizes are made integers by ceilings; $\log$ is base 2 (p. 8). (3) $c, c'$ are parameters of the definition; the theorems quantify them. (4) $\mathcal A$ may return $\bot$, which the paper does not treat: here a $\bot$ candidate takes no part in the argmin, and $\mathcal A^*$ outputs $\bot$ only when every $h_j$ is $\bot$; $\bot$ counts as failure. Ties in the argmin go to the least $j$. (5) The label "$c(x_i)$" of step 5 is the label $y_i$ stored in the test example. (6) Indices are 0-based: block $j \in \{0,\dots,k-1\}$ is $(z_{jn'+1},\dots,z_{(j+1)n'})$; positions past the end of $z$ are never read, because step 2 returns first. (7) The output law is the sum over all candidate tuples $(h_j)_j$ of $\prod_j \Pr[\mathcal A(\bar z_j) = h_j]$ times the push-forward of the product Laplace law under the selection map.
-- source:
--   Kasiviswanathan, Lee, Nissim, Raskhodnikova and Smith, What Can We Learn Privately?, arXiv:0803.0924v3, p. 17, algorithm A*(z, ϵ, α, β)

import Mathlib
import Definitions.Def_PrivLearn_Generic_Privacy
import Definitions.Def_PrivLearn_Parity_Learner

namespace PrivLearn.Parity

open MeasureTheory

/-- Outputs of the amplified learner `A*`: "insufficient samples" (step 2), the failure symbol `⊥`
(every candidate `h_j` is `⊥`), or a hypothesis `c_r`. -/
inductive AstarOut (d : ℕ) where
  | insufficient : AstarOut d
  | fail : AstarOut d
  | hyp : (Fin d → ZMod 2) → AstarOut d

/-- Every set of outputs of `A*` is measurable (a discrete output space). -/
instance instMeasurableSpaceAstarOut (d : ℕ) : MeasurableSpace (AstarOut d) := ⊤

/-- Step 1 of `A*` (p. 17), with the base of the logarithm corrected from `3/4` to `4/3`:
`k = ⌈log_{4/3}(1/β′)⌉`, `β′ = β/2`. -/
noncomputable def paramK (β : ℝ) : ℕ :=
  ⌈Real.logb (4 / 3) (1 / (β / 2))⌉₊

/-- Step 1 of `A*`: the block size `n′ = ⌈c d/(ε α′)⌉`, `α′ = α/5`. -/
noncomputable def paramN (c : ℝ) (d : ℕ) (ε α : ℝ) : ℕ :=
  ⌈c * d / (ε * (α / 5))⌉₊

/-- Step 1 of `A*`: the test-set size `s = ⌈(c′k/(α′ε)) log₂(k/β′)⌉`. -/
noncomputable def paramS (c' ε α β : ℝ) : ℕ :=
  ⌈c' * paramK β / ((α / 5) * ε) * Real.logb 2 (paramK β / (β / 2))⌉₊

/-- The entry `z_{i+1}` of the database, read at the 0-based position `i` (a dummy example
past the end; `A*` only reads positions below `n`). -/
def entry {d n : ℕ} (z : Fin n → Example d) (i : ℕ) : Example d :=
  if h : i < n then z ⟨i, h⟩ else (0, 0)

/-- Step 4 of `A*`: the `j`-th training block `z̄_j = (z_{j n′ + 1}, …, z_{(j+1) n′})` (`j` 0-based). -/
def trainBlock {d n : ℕ} (z : Fin n → Example d) (n' j : ℕ) : Fin n' → Example d :=
  fun t => entry z (j * n' + t)

/-- Step 3 of `A*`: the test set `ẑ = (z_{k n′ + 1}, …, z_{k n′ + s})`. -/
def testSet {d n : ℕ} (z : Fin n → Example d) (k n' s : ℕ) : Fin s → Example d :=
  fun t => entry z (k * n' + t)

/-- Step 5 of `A*`: the training error `|{z_i ∈ ẑ : h(x_i) ≠ y_i}|/s` of the hypothesis `c_r` on the
test set (labels as stored in the database). The value `1` given to `⊥` is never used:
`⊥` is not a candidate of the argmin. -/
noncomputable def testErr {d s : ℕ} (T : Fin s → Example d) : Option (Fin d → ZMod 2) → ℝ
  | none => 1
  | some r => ((Finset.univ.filter fun t => parity r (T t).1 ≠ (T t).2).card : ℝ) / s

/-- Step 6 of `A*`: output `h_{j*}` where `j*` minimizes the perturbed training error `e j` over the
candidates `h_j ≠ ⊥` (ties to the least `j`); output `⊥` if every `h_j` is `⊥`. -/
noncomputable def select {d k : ℕ} (H : Fin k → Option (Fin d → ZMod 2)) (e : Fin k → ℝ) : AstarOut d :=
  match ((List.finRange k).filter fun j => (H j).isSome).argmin e with
  | none => AstarOut.fail
  | some j =>
    match H j with
    | none => AstarOut.fail
    | some r => AstarOut.hyp r

/-- Algorithm `A*(z, ε, α, β)` (p. 17), with the constants `c, c′` as parameters, as the law of its
output. If `n ≤ k n′ + s` it returns "insufficient samples". Otherwise the candidates
`h_j = A(z̄_j, ε)`, `j < k`, are drawn independently, the `k` Laplace noises `η_j ∼ Lap(k/(sε))` are
drawn independently of them and of each other, and the output is `select` applied to the perturbed
training errors `testErr ẑ h_j + η_j`. -/
noncomputable def algAstar (c c' : ℝ) (d : ℕ) (ε α β : ℝ) {n : ℕ} (z : Fin n → Example d) :
    Measure (AstarOut d) :=
  if n ≤ paramK β * paramN c d ε α + paramS c' ε α β then Measure.dirac AstarOut.insufficient
  else
    ∑ H : Fin (paramK β) → Option (Fin d → ZMod 2),
      (∏ j : Fin (paramK β), algA ε (trainBlock z (paramN c d ε α) (j : ℕ)) {H j}) •
        (Measure.pi fun _ : Fin (paramK β) =>
            PrivLearn.Generic.laplace ((paramK β : ℝ) / (paramS c' ε α β * ε))).map
          (fun η => select H (fun j =>
            testErr (testSet z (paramK β) (paramN c d ε α) (paramS c' ε α β)) (H j) + η j))

end PrivLearn.Parity


