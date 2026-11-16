-- Prove2me | Definitions.Def_CNFLearning873_Valiant_Supplement_OracleProgram
-- name    : CNFLearning873_Valiant_Supplement_OracleProgram
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:37:28.17068+00:00
-- url     : https://prove2.me/theorems/0b11ac39-939b-4ac6-8a7f-db466f01fd1e
-- title:
--   Definition 6.3 — exact counting queries and random-program semantics
-- statement:
--   An exact counting query explicitly supplies a CNF $Q$ on the original $n$ variables and receives $|\Omega(Q)|$, including zero when $Q$ is unsatisfiable. A finite program sequences query operations, charged ordinary operations, and uniform integer draws. Its report records the returned value or abort, the full query list, and the accumulated work. For a supplied deterministic counting implementation with cost $\tau(Q)$, the charged running time is
--
--   $$\mathrm{work}+\sum_{Q\text{ queried}}\tau(Q).$$
--
--   The ideal interpreter draws an exact uniform integer in $\{0,\ldots,N-1\}$. The bounded interpreter tries at most $L$ draws of $\lceil\log_2 N\rceil$ independent unbiased bits, rejects integers at least $N$, and aborts on exhaustion. Event probabilities are PMF push-forwards to Boolean events. A zero range has an explicit total-function convention and is never used for a valid nonempty sampler. These definitions carry no success or resource guarantees.
-- source:
--   Weiming Feng, Yixiao Yu, Yiyao Zhang, STOC 2027 submission #873 (October 2026), Definition 6.3 and Lemma 6.6 implementation, printed pp.27–29 = 1-based PDF pp.27–29; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/873.pdf

import Definitions.Def_CNFLearning873_Valiant_CNF

noncomputable section

namespace CNFLearning873.Valiant.Supplement

/-- Finite oracle/random program; work charges count ordinary operations, queries count separately.
The program carries no correctness or complexity guarantee. -/
inductive OProg (n : ℕ) (α : Type) : Type
  | ret (a : α)
  | work (operations : ℕ) (next : OProg n α)
  | count (query : CNF n) (next : ℕ → OProg n α)
  | draw (range : ℕ) (next : ℕ → OProg n α)

namespace OProg

def bind {n : ℕ} {α β : Type} (p : OProg n α) (f : α → OProg n β) : OProg n β :=
  match p with
  | .ret a => f a
  | .work w p => .work w (p.bind f)
  | .count q g => .count q (fun z => (g z).bind f)
  | .draw N g => .draw N (fun z => (g z).bind f)

instance {n : ℕ} : Monad (OProg n) where
  pure := OProg.ret
  bind := OProg.bind

end OProg

/-- The oracle takes an explicitly supplied formula, including unsatisfiable ones. -/
def exactCount {n : ℕ} (F : CNF n) : ℕ := (solutions F).card

/-- Uniform [0,N); the unused invalid N=0 case returns 0, never an empty uniform law. -/
def uniformNat (N : ℕ) : PMF ℕ :=
  if h : 0 < N then
    letI : NeZero N := ⟨Nat.ne_of_gt h⟩
    (PMF.uniformOfFintype (Fin N)).map Fin.val
  else PMF.pure 0

/-- Rejection draws use ceil(log₂ N) bits. For N=1 there are zero bits. -/
def integerBits (N : ℕ) : ℕ := Nat.clog 2 N

/-- At most L trials; none is the abort signal. Fresh bits are used in every trial. -/
def rejectionDraw (N : ℕ) : ℕ → PMF (Option ℕ)
  | 0 => PMF.pure none
  | L + 1 => (uniformNat (2 ^ integerBits N)).bind fun z =>
      if z < N then PMF.pure (some z) else rejectionDraw N L

/-- Operational report; query list and work are accumulated by the interpreter. -/
structure Report (n : ℕ) (α : Type) where
  result : Option α
  queries : List (CNF n) := []
  work : ℕ := 0

/-- Ideal untruncated sampler semantics, with unit-cost exact counts. -/
def ideal {n : ℕ} {α : Type} : OProg n α → PMF α
  | .ret a => PMF.pure a
  | .work _ p => ideal p
  | .count q g => ideal (g (exactCount q))
  | .draw N g => (uniformNat N).bind fun z => ideal (g z)

/-- Bounded rejection implementation. Every query is interpreted by exactCount; its running cost
is charged later by the chosen deterministic counting implementation. Abort ends the computation. -/
def implemented {n : ℕ} {α : Type} (L : ℕ) : OProg n α → PMF (Report n α)
  | .ret a => PMF.pure ⟨some a, [], 0⟩
  | .work w p => (implemented L p).map fun z => {z with work := w + z.work}
  | .count q g => (implemented L (g (exactCount q))).map fun z =>
      {z with queries := q :: z.queries}
  | .draw N g => (rejectionDraw N L).bind fun z => match z with
      | none => PMF.pure ⟨none, [], L * (integerBits N + 1)⟩
      | some z => (implemented L (g z)).map fun a =>
          {a with work := L * (integerBits N + 1) + a.work}

/-- Event probability by a PMF push-forward to Bool, using exact discrete probabilities. -/
def probability {α : Type} (p : PMF α) (E : α → Prop) : ℝ := by
  classical
  exact ((p.map fun a => decide (E a)) true).toReal

/-- Actual oracle implementation cost plus the charged ordinary operations. -/
def reportTime {n : ℕ} {α : Type} (cost : CNF n → ℕ) (z : Report n α) : ℕ :=
  z.work + (z.queries.map cost).sum

end CNFLearning873.Valiant.Supplement


