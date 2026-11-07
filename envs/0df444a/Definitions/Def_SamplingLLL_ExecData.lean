-- Prove2me | Definitions.Def_SamplingLLL_ExecData
-- name    : SamplingLLL_ExecData
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:56:23.981215+00:00
-- url     : https://prove2.me/theorems/7b0a1332-f30f-4b42-a2c8-7ccbc1ba9130
-- title:
--   Application data of the Execution Theorem, and the sampler and FPRAS on it
-- statement:
--   The data of the Execution Theorem on a product-space CSP. A task is a pair $(S,c)$ with target family $S\cup\{c\}$. For each task: a membership search; separator data ($R_t$, the restoration order of $D_t=S\setminus R_t$, $W_t$, $E_t$); a budget; an executable proposal; the exact local operation; fixed charges for a search step, a constraint test, and a move of the configuration.
--
--   From these data the following are defined, by the text of Appendix A. The child tasks are $(A_{j-1},d_j)$ with $A_0=R_t$, $A_j=A_{j-1}\cup\{d_j\}$. The entry row deletes the constraints of $D_t$ in reverse order and writes the mark on $W_t$. The exit row redraws $W_t$ from $\lambda_{W_t}$ and reinserts $D_t$ in order. The insertion and deletion kernels of a task are the circuit's forward and reverse kernels, and with the reciprocal coin they form the kernels at one level, built on the level below, since children are strictly smaller. The sampler draws from $\lambda$ and inserts the constraints in index order. The FPRAS takes the product of $1-\hat r_i$, where $\hat r_i$ is the average of
--   $$
--   N_i=\max\Big(1,\Big\lceil\frac{32B_i^2m^2}{\varepsilon^2s_i^2}\Big\rceil\lceil\log_2(16m)\rceil\Big)
--   $$
--   independent experiments clipped to $[0,B_i]$, under a cap on the total work.
--
--   **Formalization Note** A counted call is one invocation of an insertion kernel, a deletion kernel, or a reciprocal coin, and nothing else counts (p.15). The fixed order of the paper is the index order. The count $N_i$ raises the printed count to an integer; more copies only help. The weight `cw` of a counted call is $1$ in the sampler.
-- source:
--   Achlioptas, Counting and Sampling by Local Repair: From the Lovász Local Lemma to Random k-SAT, STOC 2027 submission (manuscript sha256 7a943167…), §5.1, pp.14–15; Appendix A.3, p.21; proof of Theorem 5.1, p.25

import Mathlib
import Definitions.Def_SamplingLLL_Factory
import Definitions.Def_SamplingLLL_Exploration
import Definitions.Def_SamplingLLL_Circuit

set_option autoImplicit false

open scoped ENNReal

namespace SamplingLLL

open Proc

variable {n m : ℕ}

/-- The application data of the Execution Theorem (§5.1, pp.14–15) on a product-space CSP. A task
is a pair `(S, c)`. For each task: a membership search, separator data for its transcripts, a
budget, an executable proposal, the exact local operation. Costs are charged to the `Proc` of
each primitive and by the three fixed charges below.

Source: Achlioptas, STOC 2027 submission (manuscript sha256 7a943167…), §5.1, pp.14–15. -/
structure ExecData (P : ProductCSP n m) where
  /-- The membership search of the task `(S, c)`. -/
  next : Finset (Fin m) → Fin m → NextQuery m
  /-- The far family `R_t`. -/
  rest : Finset (Fin m) → Fin m → Leaf m → Finset (Fin m)
  /-- `D_t = S ∖ R_t`, in its fixed restoration order. -/
  restore : Finset (Fin m) → Fin m → Leaf m → List (Fin m)
  /-- The separator variable set `W_t`. -/
  vars : Finset (Fin m) → Fin m → Leaf m → Finset (Fin n)
  /-- The separator event `E_t`. -/
  event : Finset (Fin m) → Fin m → Leaf m → P.Config → Bool
  /-- The budget `B_i`. -/
  budget : Finset (Fin m) → Fin m → ℚ
  /-- The charge for computing the budget of a task. -/
  budgetCost : Finset (Fin m) → Fin m → ℕ
  /-- The proposal `q_i`; an outcome is a transcript with its exact probability, `none` is null. -/
  propose : Finset (Fin m) → Fin m → Proc (Option (Leaf m × ℚ))
  /-- The exact local operation at a transcript with its proposal probability: the thinning decision
  and, on acceptance (`some`), a mark whose `W_t` coordinates are the local draw. -/
  localOp : Finset (Fin m) → Fin m → Leaf m → ℚ → Proc (Option P.Config)
  /-- The charge of one search step. -/
  stepCost : ℕ
  /-- The charge of one constraint test. -/
  testCost : ℕ
  /-- The charge of reading or writing the configuration on a variable set. -/
  moveCost : ℕ

/-- The three recursive operations available to a task, one level down. -/
structure Kernels (P : ProductCSP n m) where
  /-- Insertion kernel of the task `(S, c)`. -/
  insert : Finset (Fin m) → Fin m → P.Config → Proc P.Config
  /-- Deletion kernel of the task `(S, c)`. -/
  delete : Finset (Fin m) → Fin m → P.Config → Proc P.Config
  /-- Reciprocal coin of the task `(S, c)`. -/
  coin : Finset (Fin m) → Fin m → Proc Bool

/-- The child tasks `(A_{j-1}, d_j)` of a restoration list from `A₀`, with `A_j = A_{j-1} ∪ {d_j}`,
p.21. -/
def chain : List (Fin m) → Finset (Fin m) → List (Finset (Fin m) × Fin m)
  | [], _ => []
  | d :: l, A => (A, d) :: chain l (insert d A)

/-- The tasks with target families `{0,…,i}` in sequential insertion order: `S = {0,…,i-1}`. -/
def rootSet (i : Fin m) : Finset (Fin m) := Finset.univ.filter fun j => j < i

namespace ExecData

variable {P : ProductCSP n m} (D : ExecData P)

/-- The ordered child tasks `C_t` of the transcript `t` of `(S, c)`. -/
def children (S : Finset (Fin m)) (c : Fin m) (t : Leaf m) : List (Finset (Fin m) × Fin m) :=
  chain (D.restore S c t) (D.rest S c t)

/-- The terminal transcripts of the task `(S, c)`. -/
def leavesOf (S : Finset (Fin m)) (c : Fin m) : Finset (Leaf m) :=
  leaves (insert c S) c (D.next S c)

/-- The scalar factory of a task system (Appendix A.4), with tasks as types. -/
def factory : Factory (Finset (Fin m) × Fin m) (Leaf m) P.Config where
  budget i := D.budget i.1 i.2
  budgetCost i := D.budgetCost i.1 i.2
  sgn := sign
  kids i t := D.children i.1 i.2 t
  propose i := D.propose i.1 i.2
  localOp i := D.localOp i.1 i.2

/-- The signed experiment of the task `(S, c)`, on the coins of `K`. -/
noncomputable def experiment (K : Kernels P) (S : Finset (Fin m)) (c : Fin m) :
    Proc (Option (Leaf m × P.Config)) :=
  D.factory.experiment (fun j => K.coin j.1 j.2) (S, c)

/-- The reciprocal coin of the task `(S, c)`, on the coins of `K`, one counted invocation of weight
`cw S c`. -/
noncomputable def coinAt (cw : Finset (Fin m) → Fin m → ℕ) (K : Kernels P)
    (S : Finset (Fin m)) (c : Fin m) : Proc Bool :=
  D.factory.coinAt (fun j => cw j.1 j.2) (fun j => K.coin j.1 j.2) (S, c)

/-- The unnormalized packet generator of the task `(S, c)`, on the coins of `K`. -/
noncomputable def generator (K : Kernels P) (S : Finset (Fin m)) (c : Fin m) :
    Proc (Option (Leaf m × P.Config)) :=
  D.factory.generator (fun j => K.coin j.1 j.2) (S, c)

/-- Deletion chain along a list of tasks, in the order given. -/
noncomputable def deleteChain (K : Kernels P) : List (Finset (Fin m) × Fin m) → P.Config → Proc P.Config
  | [], x => pure x
  | (A, d) :: l, x => do
    let y ← K.delete A d x
    deleteChain K l y

/-- Insertion chain along a list of tasks, in the order given. -/
noncomputable def insertChain (K : Kernels P) : List (Finset (Fin m) × Fin m) → P.Config → Proc P.Config
  | [], x => pure x
  | (A, d) :: l, x => do
    let y ← K.insert A d x
    insertChain K l y

/-- The entry row, p.21: delete the constraints of `D_t` in reverse order, then write the mark on
`W_t`. -/
noncomputable def enterAt (K : Kernels P) (S : Finset (Fin m)) (c : Fin m) (t : Leaf m)
    (mark : P.Config) (x : P.Config) : Proc P.Config := do
  let y ← deleteChain K (D.children S c t).reverse x
  tick D.moveCost
  pure fun v => if v ∈ D.vars S c t then mark v else y v

/-- The exit row, p.21: redraw `W_t` from `λ_{W_t}`, then reinsert `D_t` in order. -/
noncomputable def exitAt (K : Kernels P) (S : Finset (Fin m)) (c : Fin m) (t : Leaf m)
    (x : P.Config) : Proc P.Config := do
  tick D.moveCost
  let y ← P.redraw ((List.finRange n).filter fun v => v ∈ D.vars S c t) x
  insertChain K (D.children S c t) y

/-- The executable last-defect router, p.15 and Lemma A.3: `none` is the residual label, returned
when the bad set in the target family is exactly `{c}`. Charged as one replay of the two searches and
a test of every constraint of the target family. -/
noncomputable def routeAt (S : Finset (Fin m)) (c : Fin m) (t : Leaf m) (x : P.Config) :
    Proc (Option (Leaf m)) := do
  tick ((m + 1) * (D.testCost + 2 * D.stepCost))
  let B := P.badSet (insert c S) x
  if B = {c} then pure none else pure (some (routerLeaf (D.next S c) c B t))

/-- The circuit of Lemma A.6 for the task `(S, c)`. The residual partner is the all-no leaf `t₊`
(the leaf on input `{c}`), p.21. -/
noncomputable def circuit (K : Kernels P) (S : Finset (Fin m)) (c : Fin m) :
    Circuit P.Config (Leaf m) P.Config where
  good x := do
    tick D.testCost
    pure (!P.bad c x)
  gen := generator D K S c
  neg t := decide (sign t = -1)
  enter := enterAt D K S c
  exit := exitAt D K S c
  route := routeAt D S c
  resid _ := do
    tick ((m + 1) * D.stepCost)
    pure (leafOf (D.next S c) c {c})

/-- The kernels at target-size level `k`. `level (k+1)` serves tasks with target family of size
`≤ k+1` from `level k`, since every child has a strictly smaller target family (Lemma A.4); `level 0`
has mass `0`. `cw` is the weight of a counted invocation (`1` in the sampler). Each of `insert`,
`delete`, `coin` counts once on entry; nothing else counts (p.15: "recursive kernel and coin
invocations, counted with multiplicity"). -/
noncomputable def level (cw : Finset (Fin m) → Fin m → ℕ) : ℕ → Kernels P
  | 0 => ⟨fun _ _ _ _ => 0, fun _ _ _ _ => 0, fun _ _ _ => 0⟩
  | k + 1 =>
    { insert := fun S c x => do
        countCall (cw S c)
        (circuit D (level cw k) S c).forward x
      delete := fun S c x => do
        countCall (cw S c)
        (circuit D (level cw k) S c).backward x
      coin := coinAt D cw (level cw k) }

/-- Sequential insertion along a list of constraints. -/
noncomputable def insertAll (K : Kernels P) : List (Fin m) → P.Config → Proc P.Config
  | [], x => pure x
  | i :: l, x => do
    let y ← K.insert (rootSet i) i x
    insertAll K l y

/-- Sequential insertion with call weight `cw`, from the product law (proof of Theorem 5.1, p.25). -/
noncomputable def samplerW (cw : Finset (Fin m) → Fin m → ℕ) : Proc P.Config := do
  let x ← P.drawAll
  insertAll (level D cw m) (List.finRange m) x

/-- The perfect sampler of Theorem 5.1: sequential insertion, each invocation counted once. -/
noncomputable def sampler : Proc P.Config := samplerW D fun _ _ => 1

/-- The copy count of p.25, `N_i = max(1, ⌈32 B² m² / (ε² s²)⌉ · ⌈log₂(16m)⌉)`, computed by charged
operations. Taking ceilings only raises the printed count, since `log(16m) ≤ ⌈log₂(16m)⌉`. -/
noncomputable def copies (B ε : ℚ) : Proc ℕ := do
  let s ← qsub 1 B
  let b2 ← qmul B B
  let m2 ← qmul (m : ℚ) (m : ℚ)
  let e2 ← qmul ε ε
  let s2 ← qmul s s
  let n1 ← qmul 32 b2
  let num ← qmul n1 m2
  let den ← qmul e2 s2
  let v ← qdiv num den
  tick (bits v + (16 * m).size)
  pure (max 1 (⌈v⌉₊ * Nat.clog 2 (16 * m)))

/-- The value `ε_t B` of an experiment's outcome (`0` on the null outcome). -/
def value (B : ℚ) (o : Option (Leaf m × P.Config)) : ℚ :=
  match o with
  | none => 0
  | some (t, _) => (sign t : ℚ) * B

/-- The sum of `N` independent copies of the signed experiment, added to `acc`. -/
noncomputable def sumCopies (K : Kernels P) (S : Finset (Fin m)) (c : Fin m) (B : ℚ) :
    ℕ → ℚ → Proc ℚ
  | 0, acc => pure acc
  | k + 1, acc => do
    let o ← experiment D K S c
    let acc' ← qadd acc (value B o)
    sumCopies K S c B k acc'

/-- The clipped estimate `r̂_i` of `r_i`, p.25. -/
noncomputable def estimate (K : Kernels P) (S : Finset (Fin m)) (c : Fin m) (ε : ℚ) : Proc ℚ := do
  tick (D.budgetCost S c)
  let B := D.budget S c
  let N ← copies (m := m) B ε
  let total ← sumCopies D K S c B N 0
  let avg ← qdiv total (N : ℚ)
  let low ← qle avg 0
  if low then pure 0 else do
    let high ← qle B avg
    if high then pure B else pure avg

/-- The product of `1 - r̂_i` along the insertion order, multiplied into `acc`. -/
noncomputable def productFrom (K : Kernels P) (ε : ℚ) : List (Fin m) → ℚ → Proc ℚ
  | [], acc => pure acc
  | i :: l, acc => do
    let rhat ← estimate D K (rootSet i) i ε
    let f ← qsub 1 rhat
    let acc' ← qmul acc f
    productFrom K ε l acc'

/-- The FPRAS estimator of p.25, before the cap: the product of the factors `1 - r̂_i`. With no
constraints the output is `1`. -/
noncomputable def fprasCore (ε : ℚ) : Proc ℚ :=
  productFrom D (level D (fun _ _ => 1) m) ε (List.finRange m) 1

/-- The FPRAS of p.25: the estimator under the work cap `T`. -/
noncomputable def fpras (T : ℕ) (ε : ℚ) : Proc ℚ := capped T 0 (fprasCore D ε)

end ExecData

end SamplingLLL


