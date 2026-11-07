-- Prove2me | Definitions.Def_AlgoPFR_Protocols
-- name    : AlgoPFR_Protocols
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:43:09.247054+00:00
-- url     : https://prove2.me/theorems/5e6f76dc-fc9a-439a-b5a5-305e882c596c
-- title:
--   The sum, fiber, endgame and bucketing protocols
-- statement:
--   These are the operational protocols of the source, written as procedures that use their parents only through calls to the sampler and the coin.
--
--   1. **Sum** (proof of Lemma 4.4): $\mathrm{Sample}_{X+Y}$ draws $x,y$ and returns $x+y$; $\mathrm{Coin}_{X+Y}(z)$ draws $x\sim X$ and returns $\mathrm{Coin}_Y(z-x)$.
--   2. **Fiber** (proof of Lemma 4.5): the sampler repeats "draw $x\sim X$, run $\mathrm{Coin}_Y(z-x)$, return $x$ on success"; the coin on $x$ is $\mathrm{Coin}_X(x)\cdot\mathrm{Coin}_Y(z-x)$.
--   3. **Endgame** (proof of Lemma 4.6): the sum protocol applied to the two fibers $(X_1\mid X_1+Y_0=z)$ and $(Y_1\mid X_0+Y_1=s)$.
--   4. **Bucketing** (Algorithm 1): $J=\lfloor\log N_X\rfloor$ with $N_X$ the first success of $\mathrm{Coin}_X(x)$ after $x\sim X$. The sampler of $X_j$ repeats "draw $x$; accept if the first $2^j-1$ coins fail and at least one of the next $2^j$ coins succeeds". The coin of $X_j$ draws $2^{j+1}$ coins and accepts if the first $2^j$ contain exactly one success and the next $2^j$ at least one. The envelope is $M_{X_j}=M_X/(2^j\Pr[J=j])$.
--
--   None of these is defined by its target law; that a protocol yields the intended conditional law is the content of Lemmas 4.4–4.7.
--
--   **Formalization Note** Coin flips within a trial are counted whether or not their value is needed, as in the source's bound "fewer than $2^{j+1}$ parent coins" per iteration.
-- source:
--   Arunachalam, Dutt, Grewal, Gupte, Marton's conjecture in polynomial time, arXiv:2609.20771 (sha256 60e45066…), Lemmas 4.4–4.6, pp.20–23; Algorithm 1, p.25

import Mathlib
import Definitions.Def_AlgoPFR_condLaw
import Definitions.Def_AlgoPFR_Oracle

set_option autoImplicit false

open scoped ENNReal

namespace AlgoPFR

noncomputable section

variable {n : ℕ}

/-! ### Sums (Lemma 4.4, p.20 of arXiv:2609.20771, sha256 60e45066…) -/

/-- Step (i) of the proof of Lemma 4.4, p.20: `Sample_{X+Y}` runs `x ← Sample_X`, `y ← Sample_Y` and
outputs `x + y`. -/
def sumSampleProc (X Y : Oracle n) : Proc (Vec n) := do
  let x ← X.callSample
  let y ← Y.callSample
  pure (x + y)

/-- Step (ii) of the proof of Lemma 4.4, p.20: `Coin_{X+Y}(z)` samples `x ← Sample_X` and outputs
`Coin_Y(z − x)`. -/
def sumCoinProc (X Y : Oracle n) (z : Vec n) : Proc Bool := do
  let x ← X.callSample
  Y.callCoin (z - x)

/-- The sum protocol of Lemma 4.4, p.20, built from the two parents as black boxes. -/
def sumOracle (X Y : Oracle n) : Oracle n where
  sample := (sumSampleProc X Y).law
  coin z := (sumCoinProc X Y z).law

/-! ### Fibers (Lemma 4.5, p.21) -/

/-- One trial of the rejection sampler in the proof of Lemma 4.5, p.21: sample `x ← Sample_X`, run
`w ← Coin_Y(z − x)`, return `x` if `w = 1`. -/
def fiberTrial (X Y : Oracle n) (z : Vec n) : Proc (Option (Vec n)) := do
  let x ← X.callSample
  let w ← Y.callCoin (z - x)
  pure (if w then some x else none)

/-- The density coin in the proof of Lemma 4.5, p.21: run `w₁ ← Coin_X(x)`, `w₂ ← Coin_Y(z − x)` and
output `w₁ w₂`. -/
def fiberCoinProc (X Y : Oracle n) (z x : Vec n) : Proc Bool := do
  let w₁ ← X.callCoin x
  let w₂ ← Y.callCoin (z - x)
  pure (w₁ && w₂)

/-- The fiber protocol of Lemma 4.5, p.21: the sampler repeats `fiberTrial` until it succeeds. -/
def fiberOracle (X Y : Oracle n) (z : Vec n) : Oracle n where
  sample := (loop (fiberTrial X Y z).law).map Prod.fst
  coin x := (fiberCoinProc X Y z x).law

/-- The endgame protocol of the proof of Lemma 4.6, p.22–23: Lemma 4.4 applied to the two fibers
`F_z = (X₁ | X₁ + Y₀ = z)` and `G_s = (Y₁ | X₀ + Y₁ = s)`. -/
def endgameOracle (X Y : Oracle n) (z s : Vec n) : Oracle n :=
  sumOracle (fiberOracle X Y z) (fiberOracle Y X s)

/-! ### Bucketing (Algorithm 1, p.25) -/

/-- `k` independent runs of `Coin_X(x)`. -/
def coinFlips (X : Oracle n) (x : Vec n) : ℕ → Proc (List Bool)
  | 0 => pure []
  | k + 1 => do
    let b ← X.callCoin x
    let bs ← coinFlips X x k
    pure (b :: bs)

/-- The test of line 6 of Algorithm 1, p.25, on the list of `2^(j+1) − 1` coin outcomes: "the first
`2^j − 1` coins fail and at least one of the next `2^j` coins succeeds". -/
def sampleTest (j : ℕ) (bs : List Bool) : Bool :=
  (bs.take (2 ^ j - 1)).all (fun b => !b) && (bs.drop (2 ^ j - 1)).any id

/-- The test of line 10 of Algorithm 1, p.25, on the list of `2^(j+1)` coin outcomes: "the first
`2^j` trials contain exactly one success and the next `2^j` trials contain at least one success". -/
def coinTest (j : ℕ) (bs : List Bool) : Bool :=
  decide ((bs.take (2 ^ j)).count true = 1) && (bs.drop (2 ^ j)).any id

/-- One trial of `Sample_{X_j}`, lines 5–6 of Algorithm 1, p.25. -/
def bucketTrial (X : Oracle n) (j : ℕ) : Proc (Option (Vec n)) := do
  let x ← X.callSample
  let bs ← coinFlips X x (2 ^ (j + 1) - 1)
  pure (if sampleTest j bs then some x else none)

/-- `Coin_{X_j}(x)`, lines 9–10 of Algorithm 1, p.25. -/
def bucketCoinProc (X : Oracle n) (j : ℕ) (x : Vec n) : Proc Bool := do
  let bs ← coinFlips X x (2 ^ (j + 1))
  pure (coinTest j bs)

/-- The output of Algorithm 1, p.25, for the label `j`: the sampler repeats `bucketTrial` (line 7:
"Otherwise repeat from step 5") and the coin is `bucketCoinProc`. -/
def bucketOracle (X : Oracle n) (j : ℕ) : Oracle n where
  sample := (loop (bucketTrial X j).law).map Prod.fst
  coin x := (bucketCoinProc X j x).law

/-- One run of `Coin_X(x)` as a trial of the loop in line 2 of Algorithm 1, p.25. -/
def coinTrial (X : Oracle n) (x : Vec n) : PMF (Option Unit) :=
  (X.coin x).map fun b => if b then some () else none

/-- Lines 1–3 of Algorithm 1, p.25, as the joint law of `(X, J)`: sample `x ← Sample_X`, run
`Coin_X(x)` until the first success at time `N_x`, and set `j := ⌊log N_x⌋`.

**Formalization Note.** `loop` counts the failures `k` before the first success, so `N_x = k + 1`;
`Nat.log 2 m` is `⌊log₂ m⌋` for `m ≥ 1`. -/
def bucketJoint (X : Oracle n) : PMF (Vec n × ℕ) :=
  X.sample.bind fun x => (loop (coinTrial X x)).map fun y => (x, Nat.log 2 (y.2 + 1))

/-- The law of the bucket label `J`, with `π_j = Pr[J = j]` of Eq. (22), p.25. -/
def bucketLabel (X : Oracle n) : PMF ℕ :=
  (bucketJoint X).map Prod.snd

/-- `π_j = Pr[J = j]` as a real number, Eq. (22), p.25. -/
def bucketProb (X : Oracle n) (j : ℕ) : ℝ :=
  (bucketLabel X j).toReal

/-- The envelope `M_{X_j} = M_X / (2^j Pr[J = j])` of Lemma 4.7, p.24. -/
def bucketEnv (X : Oracle n) (M : ℝ) (j : ℕ) : ℝ :=
  M / (2 ^ j * bucketProb X j)

end

end AlgoPFR


