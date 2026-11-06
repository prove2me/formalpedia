-- Prove2me | Definitions.Def_ImpatientQPTAS_Program
-- name    : ImpatientQPTAS_Program
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:59:35.936838+00:00
-- url     : https://prove2.me/theorems/ee1ac4ea-6951-4ada-b96a-6cbe8106f4eb
-- title:
--   The algorithm of Theorem 1.1 — the plan, the dynamic program of §2.6 and the action rule
-- statement:
--   The algorithm has two parts, each a counted computation.
--
--   **Preparation.** With $e=1/\lceil16/\epsilon\rceil$ and $\delta=e^2/16$, classify the customers against $e/n^2$ and $1-e/n$. Compute $r_{\max}$; round all rewards, and the probabilities of the average customers up, by scanning the grids with multiplications and comparisons only. Group the average customers into classes of equal $(\tilde r,p^\uparrow)$. Fill the tables of the **dynamic program of §2.6** over the count vectors $N$:
--   $$
--   \mathrm{Val}[N]=\max_{c:\,N_c\ge1}\Big(\tilde r_c+\sum_{D\le N-e_c}\Pr[D\mid N-e_c]\;\mathrm{Val}[N-e_c-D]\Big),\qquad \mathrm{Val}[0]=0,
--   $$
--   with $\Pr[D\mid M]=\prod_c\binom{M_c}{D_c}p_c^{D_c}(1-p_c)^{M_c-D_c}$, and record the least maximizing class. Evaluate $\tilde Q(i)$ for each average customer and quitter, and keep the least maximizer as the first move.
--
--   **Action.** $\tilde S(t,A)$ is: nothing for $A=\emptyset$; the first move at $t=1$, $A=[n]$, if there is one; greedily for $\mathrm{Val}$ among the average customers of $A$, if any; else the sticker of $A$ of the largest reward; else the least element of $A$.
--
--   The goal theorem is a statement about this program.
--
--   **Formalization Note** The cost model is the published `CapacitatedAssort.General.Work`, a counter with no randomness: scalar arithmetic, comparisons, reads and writes each cost one, and every number the program uses comes from charged code. `prep` stops at once when $n=0$. The loops carry a structural fuel, which only makes the recursion structural; each scan stops by its own test, so its cost is the number of steps taken. The stage index of the printed dynamic program is dropped, as the value does not depend on it. `timeBound c d ε n` is $c\,(n+1)^{c(1/\epsilon)^d\log^2(n+1)}$; the base $n+1$ keeps it meaningful at $n=1$, and for $n\ge2$ it is exactly $O(n^{O_\epsilon(\log^2 n)})$.
-- source:
--   Segev, Near-Optimal Adaptive Policies for Serving Stochastically Departing Customers, arXiv:2209.13878v1, Theorem 1.1, p.4; §2.1, p.8; §§2.2–2.3, pp.9–10; §2.5, pp.12–13; §2.6, pp.13–14

import Mathlib
import Definitions.Def_CapacitatedAssort_General_Work
import Definitions.Def_ImpatientQPTAS_Model

namespace ImpatientQPTAS

open CapacitatedAssort.General

/-- The least `m ≥ m₀` with `16 ≤ m·ε`, by counting up.

**Formalization Note.** `fuel` only makes the recursion structural, and the test stops the loop first.
`prep` passes `⌈16/ε⌉₊ + 1`, so the cost is the number of steps taken. -/
noncomputable def accLoop (ε : ℝ) : ℕ → ℕ → Work ℕ
  | 0, m => pure m
  | k + 1, m => do
    charge 3 -- multiplication, comparison, increment
    if 16 ≤ (m : ℝ) * ε then pure m else accLoop ε k (m + 1)

/-- From `cur`, divide by `b` for as long as the result stays at least `x`: the last term of
`cur, cur/b, cur/b², …` that is at least `x`. With `cur = 1` and `b = 1 + δ`, and `0 < x ≤ 1`, this is
the operator `U` of §2.3, p.10, with no logarithm. `fuel` is structural, as in `accLoop`. -/
noncomputable def scanCeil (b x : ℝ) : ℕ → ℝ → Work ℝ
  | 0, cur => pure cur
  | k + 1, cur => do
    charge 3 -- division, comparison, dispatch
    if cur / b < x then pure cur else scanCeil b x k (cur / b)

/-- The first term of `cur, cur/b, cur/b², …` that is at most `x`. With `cur = 1` and `b = 1 + δ`, and
`0 < x ≤ 1`, this is the operator `D` of §2.3, p.10; with `cur = r_max` and `b = 1 + e` it rounds a
reward down to the grid of §2.2, p.9. `fuel` is structural, as in `accLoop`. -/
noncomputable def scanFloor (b x : ℝ) : ℕ → ℝ → Work ℝ
  | 0, cur => pure cur
  | k + 1, cur => do
    charge 3 -- comparison, division, dispatch
    if cur ≤ x then pure cur else scanFloor b x k (cur / b)

/-- The binomial coefficient `C(a, b)` as a real number, by
`C(a, k+1) = C(a, k)·(a − k)/(k + 1)`. -/
noncomputable def binomW (a b : ℕ) : Work ℝ := do
  charge 1
  let mut acc : ℝ := 1
  for k in List.range b do
    charge 5 -- dispatch, subtraction, addition, multiplication, division
    acc := acc * ((a : ℝ) - (k : ℝ)) / ((k : ℝ) + 1)
  return acc

/-- `x ^ k` by repeated multiplication, with `x ^ 0 = 1`. -/
noncomputable def powW (x : ℝ) (k : ℕ) : Work ℝ := do
  charge 1
  let mut acc : ℝ := 1
  for _ in List.range k do
    charge 2 -- dispatch, multiplication
    acc := acc * x
  return acc

/-- `Pr[D | M] = Π_c C(M c, D c)·p_c^(D c)·(1 − p_c)^(M c − D c)`, the law of the departures from a
count vector `M`, §2.6, p.14. -/
noncomputable def probOf (prob : Array ℝ) (M Dv : Array ℤ) : Work ℝ := do
  charge 1
  let mut w : ℝ := 1
  for c in List.range prob.size do
    charge 6 -- dispatch, three reads, two integer conversions
    let a := (M[c]!).toNat
    let d := (Dv[c]!).toNat
    let b ← binomW a d
    let x ← powW prob[c]! d
    let y ← powW (1 - prob[c]!) (a - d)
    charge 5 -- subtractions and three multiplications
    w := w * b * x * y
  return w

/-- `Σ_{D ≤ M} Pr[D | M]·Val[M − D]`, the enumeration over the support of the departures, §2.6,
p.14. `bases` addresses the table `val`. -/
noncomputable def expectW (prob : Array ℝ) (bases : Array ℕ) (val : Array ℝ) (M : Array ℤ) :
    Work ℝ := do
  charge (2 * M.size + 1) -- the bases of the box below M
  let mb := M.map fun x => x.toNat + 1
  let box ← boxSize mb
  let mut acc : ℝ := 0
  for j in List.range box do
    charge 1 -- dispatch
    let Dv ← decode mb j
    let w ← probOf prob M Dv
    charge (3 * M.size + 1) -- the residual count vector M − D
    let rest := Array.zipWith (fun a b => a - b) M Dv
    let idx ← encode bases rest
    charge 3 -- read, multiplication, addition
    acc := acc + w * val[idx]!
  return acc

/-- The tables of the dynamic program: `val[j]` is the value of the count vector with index `j`, and
`act[j]` the least class attaining it. -/
structure Tables where
  val : Array ℝ
  act : Array ℕ

/-- The mixed-radix bases of the count vectors `N ≤ sizes`. -/
def basesOf (sizes : Array ℕ) : Array ℕ := sizes.map (· + 1)

/-- **The dynamic program of §2.6**, Segev, arXiv:2209.13878v1, pp.13–14. Class `c` has reward
`rew[c]`, departure probability `prob[c]` and `sizes[c]` customers.

The tables run over the count vectors `N`, `N c ≤ sizes[c]`, in increasing index order; a
coordinatewise smaller vector has a smaller index, so every entry read is already filled. At `N ≠ 0`
the recursion of p.14 takes, over the classes `c` with `N c ≥ 1` and `M = N − e_c`, the maximum of
`rew[c] + Σ_{D ≤ M} Pr[D | M]·Val[M − D]`. `Val[0] = 0`.

**Formalization Note.** The printed state also carries the stage `t`, on which the value does not
depend, so the program drops it. -/
noncomputable def dp (rew prob : Array ℝ) (sizes : Array ℕ) : Work Tables := do
  charge (2 * sizes.size + 1)
  let bases := basesOf sizes
  let total ← boxSize bases
  let mut val : Array ℝ := #[]
  let mut act : Array ℕ := #[]
  for j in List.range total do
    charge 3 -- dispatch and two pushes
    let N ← decode bases j
    let mut best : ℝ := 0
    let mut arg : ℕ := 0
    let mut found : Bool := false
    for c in List.range sizes.size do
      charge 3 -- dispatch, read, comparison
      if 1 ≤ N[c]! then
        charge (sizes.size + 1) -- copy N with one coordinate decremented
        let M := N.modify c (· - 1)
        let x ← expectW prob bases val M
        charge 4 -- read, addition, two comparisons
        let q := rew[c]! + x
        if !found || best < q then
          best := q
          arg := c
          found := true
    val := val.push best
    act := act.push arg
  return ⟨val, act⟩

/-- Whether the customer is a sticker, average, or a quitter. -/
inductive Kind
  | stick
  | average
  | quit
  deriving DecidableEq, Inhabited

/-- What `prep` computes once: the true rewards, each customer's kind and class, the bases and action
table of the dynamic program, and the first move. -/
structure Plan (n : ℕ) where
  rew : Array ℝ
  kind : Array Kind
  cls : Array ℕ
  bases : Array ℕ
  act : Array ℕ
  first : Option (Fin n)

/-- The largest entry of an array, and `0` for the empty one. -/
noncomputable def maxScan (a : Array ℝ) : Work ℝ := do
  charge 1
  let mut best : ℝ := 0
  for k in List.range a.size do
    charge 3 -- dispatch, read, comparison
    if k = 0 ∨ best < a[k]! then best := a[k]!
  return best

/-- The distinct pairs (r̃, p↑) among average customers, by insertion into a list: the class of each
customer, the reward and probability of each class, and the sizes. -/
noncomputable def classify (n : ℕ) (kind : Array Kind) (rT pU : Array ℝ) :
    Work (Array ℕ × Array ℝ × Array ℝ × Array ℕ) := do
  charge (n + 1)
  let mut cls : Array ℕ := Array.replicate n 0
  let mut kr : Array ℝ := #[]
  let mut kp : Array ℝ := #[]
  let mut sz : Array ℕ := #[]
  for i in List.range n do
    charge 2 -- dispatch, read
    if kind[i]! = Kind.average then
      let mut idx := kr.size
      for c in List.range kr.size do
        charge 6 -- dispatch, four reads, two comparisons
        if kr[c]! = rT[i]! ∧ kp[c]! = pU[i]! then
          idx := c
      charge 5 -- test, reads, pushes or update, write
      if idx = kr.size then
        kr := kr.push rT[i]!
        kp := kp.push pU[i]!
        sz := sz.push 1
      else
        sz := sz.modify idx (· + 1)
      cls := cls.set! i idx
  return (cls, kr, kp, sz)

/-- The preprocessing at the accuracy `e = 1/m`.

1. Classify each customer against `e/n²` and `1 − e/n`.
2. Compute `r_max` by a scan; round every reward against the global `r_max` (§2.2, p.9, relative
   grid), and the probability of every average customer (§2.3, p.10) up, by scans.
3. Form the classes of average customers.
4. Run the dynamic program `dp`.
5. For each `i ∈ C_average ∪ C_quit`, evaluate
   `Q̃(i) = r̃_i + Σ_{D ≤ N⁰} Pr[D | N⁰]·Val[N⁰ − D]`, with `N⁰` the full count vector, minus `e_{class i}`
   when `i` is average. The first move is the least `i` attaining the maximum, `none` if there is no
   such `i`.

**Formalization Note.** Step 5 replaces the guess of `i₁`, §2.1, p.8, which a deterministic algorithm
must evaluate. Rounding once against the global `r_max` is what makes a count vector summarize a set
of average customers. `fuel` is structural: `(1+δ)^J ≥ 1 + Jδ`, so `16·(n+1)²·m³` steps always suffice,
and the scans stop by their own tests. -/
noncomputable def prepAt {n : ℕ} (m : ℕ) (I : Instance n) : Work (Plan n) := do
  charge 12 -- the arithmetic of the parameters below
  let e : ℝ := 1 / (m : ℝ)
  let δ : ℝ := e ^ 2 / 16
  let lo : ℝ := e / (n : ℝ) ^ 2
  let hi : ℝ := 1 - e / (n : ℝ)
  let fuel : ℕ := 16 * (n + 1) ^ 2 * m ^ 3
  let rA ← tabulate n fun i => do
    charge 1 -- input read
    return I.r i
  let kind ← tabulate n fun i => do
    charge 3 -- input read, two comparisons
    return if I.p i < lo then Kind.stick else if hi < I.p i then Kind.quit else Kind.average
  let rm ← maxScan rA
  charge 2 -- the threshold (e/n)·r_max
  let thr : ℝ := e / (n : ℝ) * rm
  let rT ← tabulate n fun i => do
    charge 2 -- read, comparison
    if rA[i.val]! ≤ thr then return 0 else scanFloor (1 + e) rA[i.val]! fuel rm
  let pU ← tabulate n fun i => do
    charge 3 -- read, test of the kind, input read
    if kind[i.val]! = Kind.average then
      charge 2 -- comparison and the subtraction
      if I.p i ≤ e / 4 then
        scanCeil (1 + δ) (I.p i) fuel 1
      else do
        let y ← scanFloor (1 + δ) (1 - I.p i) fuel 1
        charge 1 -- subtraction
        return 1 - y
    else return 0
  let (cls, kr, kp, sizes) ← classify n kind rT pU
  let tb ← dp kr kp sizes
  charge (3 * sizes.size + 1) -- the bases and the full count vector
  let bases := basesOf sizes
  let full : Array ℤ := sizes.map fun s : ℕ => (s : ℤ)
  let mut best : ℝ := 0
  let mut first : Option (Fin n) := none
  for i in List.finRange n do
    charge 2 -- dispatch, read
    if kind[i.val]! ≠ Kind.stick then
      charge (sizes.size + 3) -- copy the count vector
      let N := if kind[i.val]! = Kind.average then full.modify cls[i.val]! (· - 1) else full
      let x ← expectW kp bases tb.val N
      charge 4 -- read, addition, two comparisons
      let q := rT[i.val]! + x
      if first.isNone || best < q then
        best := q
        first := some i
  return ⟨rA, kind, cls, bases, tb.act, first⟩

/-- **The preprocessing**, the first half of the algorithm of Theorem 1.1, Segev, arXiv:2209.13878v1,
p.4. With no customers it stops at once. Otherwise it finds `m = ⌈16/ε⌉` and calls `prepAt`. -/
noncomputable def prep {n : ℕ} (ε : ℝ) (I : Instance n) : Work (Plan n) := do
  charge 1 -- test
  if n = 0 then
    return ⟨#[], #[], #[], #[], #[], none⟩
  else
    let m ← accLoop ε (⌈16 / ε⌉₊ + 1) 1
    prepAt m I

/-- The least customer of `A` selected by `sel` whose class is the one the table `act` prescribes for
the count vector of the selected customers of `A`; `none` if `A` has no selected customer. -/
noncomputable def pickClass {n : ℕ} (bases act cls : Array ℕ) (sel : Fin n → Bool)
    (A : Finset (Fin n)) : Work (Option (Fin n)) := do
  charge (bases.size + 1)
  let mut N : Array ℤ := Array.replicate bases.size 0
  let mut any : Bool := false
  for i in List.finRange n do
    charge 5 -- dispatch, two tests, read, update
    if i ∈ A ∧ sel i = true then
      N := N.modify cls[i.val]! (· + 1)
      any := true
  if !any then
    return none
  else
    let j ← encode bases N
    charge 1 -- read
    let c := act[j]!
    let mut out : Option (Fin n) := none
    for i in (List.finRange n).reverse do
      charge 5 -- dispatch, three tests, read
      if i ∈ A ∧ sel i = true ∧ cls[i.val]! = c then
        out := some i
    return out

/-- **The action rule**, the second half of the algorithm of Theorem 1.1: `S̃(t, A)`, in this order.

1. `A = ∅`: `none`.
2. `t = 1`, `A = [n]` and the plan has a first move: that move.
3. `A` holds an average customer: greedily for the rounded values, `pickClass` on the average customers
   of `A`.
4. `A` holds a sticker: the sticker of `A` with the largest reward, ties to the least index.
5. Otherwise the least element of `A`.

**Formalization Note.** The policy of §2.5 acts greedily for the rounded-up values in the true
process, in place of the randomized translation of Appendix A.6, so the output is a deterministic
policy `ℕ × 2^[n] → [n]` as §1.1 asks. It never idles. -/
noncomputable def act {n : ℕ} (pl : Plan n) (t : ℕ) (A : Finset (Fin n)) :
    Work (Option (Fin n)) := do
  charge 1
  let mut size : ℕ := 0
  let mut least : Option (Fin n) := none
  for i in (List.finRange n).reverse do
    charge 3 -- dispatch, test, increment
    if i ∈ A then
      size := size + 1
      least := some i
  charge 3 -- tests
  if size = 0 then
    return none
  else if t = 1 ∧ size = n ∧ pl.first.isSome then
    return pl.first
  else
    let a ← pickClass pl.bases pl.act pl.cls (fun i => pl.kind[i.val]! == Kind.average) A
    if a.isSome then
      return a
    else
      let mut best : Option (Fin n) := none
      let mut bestR : ℝ := 0
      for i in List.finRange n do
        charge 5 -- dispatch, two tests, read, comparison
        if i ∈ A ∧ pl.kind[i.val]! = Kind.stick then
          if best.isNone || bestR < pl.rew[i.val]! then
            best := some i
            bestR := pl.rew[i.val]!
      charge 1 -- test
      if best.isSome then return best else return least

/-- The count vector of `A` for the class map `cl`, §2.6, p.13: `N c` is the number of customers of `A`
in class `c`. -/
def countVec {n K : ℕ} (cl : Fin n → Fin K) (A : Finset (Fin n)) : Array ℤ :=
  Array.ofFn fun k => (((A.filter fun i => cl i = k).card : ℕ) : ℤ)

/-- The value computed by a charged computation. -/
def value {α : Type} (w : Work α) : α := (w.run 0).1

/-- The number of operations charged by a computation. -/
def cost {α : Type} (w : Work α) : ℕ := (w.run 0).2

/-- The plan of the instance at accuracy `ε`. -/
noncomputable def plan {n : ℕ} (ε : ℝ) (I : Instance n) : Plan n := value (prep ε I)

/-- The computed policy `S̃`. -/
noncomputable def policy {n : ℕ} (ε : ℝ) (I : Instance n) : Policy n :=
  fun t A => value (act (plan ε I) t A)

/-- The running-time bound `c·(n+1)^(c·(1/ε)^d·log²(n+1))`, the `O(n^{O_ε(log² n)})` of Theorem 1.1
with `O_ε(f(n)) = poly(1/ε)·f(n)`, p.4.

**Formalization Note.** The base `n + 1` keeps the bound meaningful at `n = 1`, where `n^{…log² n} = 1`
could not absorb the poly(1/ε) work of the grid scans. For `n ≥ 2`, `n + 1 ≤ n^1.6` and
`log(n+1) ≤ 1.6·log n`, so this is exactly `O(n^{O_ε(log² n)})`. The power is `Real.rpow`; its base is
at least `1`. -/
noncomputable def timeBound (c d : ℕ) (ε : ℝ) (n : ℕ) : ℝ :=
  (c : ℝ) * ((n : ℝ) + 1) ^ ((c : ℝ) * (1 / ε) ^ d * (Real.log ((n : ℝ) + 1)) ^ 2)

end ImpatientQPTAS


