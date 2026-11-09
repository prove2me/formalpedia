-- Prove2me | Definitions.Def_WatsonPseudodeterminism_MASeparation_Families
-- name    : WatsonPseudodeterminism_MASeparation_Families
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:31:46.81474+00:00
-- url     : https://prove2.me/theorems/f991352b-2c4a-4ec8-a2cb-16e4a46ca619
-- title:
--   Growing communication families and polylogarithmic classes
-- statement:
--   A communication family consists of input lengths $N_t$ and partial Boolean functions $F_t$ on two $N_t$-bit strings. Membership requires $N_t\to\infty$. Write $\ell(N)=\lfloor\log_2N\rfloor+1$, with the integer binary logarithm convention $\ell(0)=1$. MA membership means
--
--   $$\exists C\in\mathbb N\ \forall t\ \exists d\le C\ell(N_t)^C:\ F_t\text{ has an MA protocol of cost }d.$$
--
--   N·BPP membership is the same statement using standard-error N·BPP protocols. The constant $C$ is chosen once for the entire family. Growth is part of each membership predicate, rather than a proof field of the raw family structure. Finitely many short lengths cause no change to these polylogarithmic classes, since every finite-input partial function has a finite deterministic protocol. This interface states the paper's class separation without replacing polylogarithmic complexity by an instance-dependent bound.
-- source:
--   Thomas Watson, STOC 2027 submission #13 (October 2026), §1, pp. 1–2; §1.1, p. 3 (infinite families with polylog N complexity); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/13.pdf

import Definitions.Def_WatsonPseudodeterminism_MASeparation_Models

namespace WatsonPseudodeterminism.MASeparation

abbrev Bits (N : ℕ) := Fin N → Bool

/-- §1.1, p. 3: an indexed collection of two-party partial Boolean functions. -/
structure Family where
  length : ℕ → ℕ
  fn : (t : ℕ) → PartialFn (Bits (length t)) (Bits (length t))

/-- Infinite families have unbounded input length tending to infinity. -/
def Growing (F : Family) : Prop :=
  Filter.Tendsto F.length Filter.atTop Filter.atTop

/-- One constant, fixed for the entire family, bounds the MA cost by a power of log N. -/
def InMA (F : Family) : Prop :=
  Growing F ∧ ∃ C : ℕ, ∀ t, ∃ d : ℕ,
    d ≤ C * (Nat.log 2 (F.length t) + 1) ^ C ∧ MAProtocol (F.fn t) d

/-- §1, p. 2 identifies NP^BPP with N·BPP. No gap is imposed on invalid inputs. -/
def InNBPP (F : Family) : Prop :=
  Growing F ∧ ∃ C : ℕ, ∀ t, ∃ d : ℕ,
    d ≤ C * (Nat.log 2 (F.length t) + 1) ^ C ∧ NBPPProtocol (F.fn t) d

end WatsonPseudodeterminism.MASeparation


