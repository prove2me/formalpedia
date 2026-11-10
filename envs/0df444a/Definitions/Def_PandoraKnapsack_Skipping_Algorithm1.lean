-- Prove2me | Definitions.Def_PandoraKnapsack_Skipping_Algorithm1
-- name    : PandoraKnapsack_Skipping_Algorithm1
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T00:24:27.000076+00:00
-- url     : https://prove2.me/theorems/a46b887f-9e10-4954-a348-f0f04030fbf1
-- title:
--   Algorithm 1 (SA-PK) as a finite random experiment and the predecessor load
-- statement:
--   Given an array $x$ (in the source an optimal solution of $\Psi(T)$), each item $i$ independently receives an assignment: with $\alpha_i=\sum_{j,t\le T}x_{i,j,t}$, it is kept with probability $\alpha_i/4$ and, if kept, given one pair $(j,t)$ with probability $x_{i,j,t}/\alpha_i$. So the assignment is $(j,t)$ with probability $x_{i,j,t}/4$ and empty with probability $1-\alpha_i/4$; if $\alpha_i=0$ the categorical law is never used. The size of an assigned item is drawn from the law of its assigned choice, independently across items. An unassigned item's size is a dummy $0$ and is never used. `alg1Prob I x E` is the probability of an event $E$ (a finite weighted sum over outcomes).
--
--   The retained triples $(i,j,b_{i,j})$ are sorted by nondecreasing $b$, ties by increasing item. Step 3 scans them from used capacity $S=0$: a triple is inserted iff $S\le b_{i,j}$, and then $S\leftarrow S+s_i^j$. The **predecessor load** $s(I_{i,j})$ of item $i$ is the value of $S$ when the scan reaches $i$, i.e. the total size of the triples inserted before it, whether or not $i$ itself is inserted.
-- source:
--   Barak, Berlin, Cohen, Eden, Porat and Talgam-Cohen (2026), Pandora's Knapsack via Simple Policies, supplied PDF (STOC 2027 submission), SHA256 45e5830b173d687c08d5175988af81bf660c693ff805b1d2e7bc213140d27a2d, Algorithm 1 and Lemma 5.3, printed p. 23 (PDF 25)

import Definitions.Def_PandoraKnapsack_Skipping_TimeIndexedLP

open scoped Classical

namespace PandoraKnapsack.Skipping

/-- **Algorithm 1 (SA-PK) as a random experiment.**

Barak et al. (2026), *Pandora's Knapsack via Simple Policies*, supplied PDF (SHA256
45e5830b…7a2d), Algorithm 1 and Lemma 5.3, printed p. 23 (PDF 25).

Given an array `x` (in the source, an optimal solution `x*` of `Ψ(T)`), independently for every
item `i` let `α_i = Σ_{j, t ≤ T} x_{i,j,t}`, sample `A_i ∼ Bernoulli(α_i / 4)`, and if `A_i = 1`
draw `(j_i, t_i) ∼ Categorical(x_{i,j,t} / α_i)` and set `b_{i,j_i} = t_i`. The retained triples
are sorted by nondecreasing `b`, ties broken by increasing `(i, j)`. Starting from `S = 0`, a
triple `(i, j, b)` is inserted iff `S ≤ b`, and then `S ← S + s_i^j`.

**Formalization Note.** The sample space is finite: an assignment `a i ∈ {none} ∪ (Fin m ×
{0, …, T})` per item and a realized size per item. The assignment of item `i` is `some (j, t)`
with probability `x_{i,j,t}/4` (the product of `α_i/4` and `x_{i,j,t}/α_i`) and `none` with
probability `1 − α_i/4`; when `α_i = 0` the categorical law is never evaluated. The size of an
assigned item is drawn from the law of its assigned choice; only that one choice is sampled, and
an unassigned item's size is the dummy value `0`, never used. Assignments of distinct items and
the sizes are independent: the weight of an outcome is the product. `alg1Prob` is the probability
of an event (a finite weighted sum). The weights form a probability law whenever `x` satisfies
(9) and (10). -/
abbrev Assignment (n m T : ℕ) := Fin n → Option (Fin m × Fin (T + 1))

/-- An outcome of the experiment: the assignment and the realized size of every item. -/
abbrev Outcome (n m T : ℕ) := Assignment n m T × (Fin n → Fin (T + 2))

variable {n m T : ℕ}

/-- The probability that item `i` receives the assignment `o`. -/
noncomputable def assignWeight (x : LPArray n m) (i : Fin n) : Option (Fin m × Fin (T + 1)) → ℝ
  | none => 1 - (∑ j, ∑ t ∈ Finset.range (T + 1), x i j t) / 4
  | some (j, t) => x i j (t : ℕ) / 4

/-- The probability of the realized size `s` of item `i` given its assignment. -/
noncomputable def sizeWeight (I : Instance n m T) (i : Fin n) :
    Option (Fin m × Fin (T + 1)) → Fin (T + 2) → ℝ
  | none, s => if (s : ℕ) = 0 then 1 else 0
  | some (j, _), s => (I.sizeLaw i j s).toReal

/-- The probability of one outcome. -/
noncomputable def outcomeWeight (I : Instance n m T) (x : LPArray n m) (ω : Outcome n m T) : ℝ :=
  ∏ i, assignWeight x i (ω.1 i) * sizeWeight I i (ω.1 i) (ω.2 i)

/-- The probability of an event of the experiment. -/
noncomputable def alg1Prob (I : Instance n m T) (x : LPArray n m) (E : Outcome n m T → Prop) : ℝ :=
  ∑ ω : Outcome n m T, if E ω then outcomeWeight I x ω else 0

/-- The retained triples `(i, j, b_{i,j})`, in increasing item order. -/
def retained (a : Assignment n m T) : List (Fin n × Fin m × ℕ) :=
  (List.finRange n).filterMap fun i => (a i).map fun jt => (i, jt.1, (jt.2 : ℕ))

/-- The retained triples sorted by nondecreasing `b`, ties by increasing item (each item occurs
at most once, so this is the source's tie-break by increasing `(i, j)`). -/
def scanOrder (a : Assignment n m T) : List (Fin n × Fin m × ℕ) :=
  (retained a).mergeSort fun e f => decide (e.2.2 < f.2.2 ∨ (e.2.2 = f.2.2 ∧ e.1 ≤ f.1))

/-- Step 3 of Algorithm 1, run with realized sizes `s` until item `target` is reached: the
returned value is the used capacity `S` at that moment, i.e. the total size `s(I_{i,j})` of the
triples inserted before it (whether or not `target` is then inserted). If `target` is not in the
list, the final used capacity is returned. -/
def loadBefore (s : Fin n → ℕ) (target : Fin n) : List (Fin n × Fin m × ℕ) → ℕ → ℕ
  | [], S => S
  | (i, _, b) :: rest, S =>
    if i = target then S else loadBefore s target rest (if S ≤ b then S + s i else S)

/-- The predecessor load `s(I_{i,j})` of item `i` in an outcome of Algorithm 1. -/
def predecessorLoad (ω : Outcome n m T) (i : Fin n) : ℕ :=
  loadBefore (fun k => (ω.2 k : ℕ)) i (scanOrder ω.1) 0

end PandoraKnapsack.Skipping


