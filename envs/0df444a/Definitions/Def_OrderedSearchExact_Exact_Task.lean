-- Prove2me | Definitions.Def_OrderedSearchExact_Exact_Task
-- name    : OrderedSearchExact_Exact_Task
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:03:35.989456+00:00
-- url     : https://prove2.me/theorems/d09a2783-7518-489c-ad88-07c69c8ee14e
-- title:
--   Ordered-search inputs and exact phase-query algorithms
-- statement:
--   For $n\ge1$, a hidden transition $j\in\{0,\ldots,n-1\}$ specifies the bits $x_j(i)=\mathbf1[i\ge j]$. The phase oracle is diagonal with entries $(-1)^{x_j(i)}$. An exact $k$-query algorithm has an arbitrary finite ancillary register, a normalized input-independent initial state, input-independent interleaved unitaries, and a final basis measurement followed by an input-independent output map. Its success condition is
--
--   $$\Pr[\mathrm{output}=j\mid x_j]=1\qquad\text{for every }j.$$
--
--   The algorithm and output map are chosen before $j$. The symmetrized input is $x_j\overline{x_j}$, with an optional global bit complement; the output remains $j$. These predicates use the published query semantics with a one-element dummy answer register, and impose no time or gate bound. They provide the operational side of Proposition 2.1.
-- source:
--   Joseph Carolan, Andrew Childs, STOC 2027 submission #1443 (October 2026), §2.1, p.5–6 (PDF p.5–6); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1443.pdf; sha256 8bb6cbb4037a439039875fd77a9f212e2c0f90a6e87f0c4c690230223813da44

import Definitions.Def_QAlgorithms_Defs_Query

namespace OrderedSearchExact.Exact

/-- Section 2.1, pp.5–6: the unknown transition is fixed before a run. -/
def inputBit {n : ℕ} (j i : Fin n) : Bool := decide (j ≤ i)

def searchOracle {n : ℕ} (j : Fin n) :
    Matrix (Fin n × PUnit.{1}) (Fin n × PUnit.{1}) ℂ :=
  QAlgorithms.phaseOracle (fun p => inputBit j p.1)

/-- Actual finite quantum query semantics, with no bound on the ancillary dimension.
The algorithm and output map are quantified before the hidden transition. -/
def ExactAlgorithm (n k : ℕ) : Prop :=
  ∃ w : ℕ, ∃ A : QAlgorithms.QueryAlg (Fin n) PUnit.{1} (Fin w) k,
    ∃ out : (Fin n × PUnit.{1}) × Fin w → Fin n,
      ∀ j : Fin n, A.outputProb (searchOracle j) out j = 1

/-- The symmetrized input x followed by its complement, including either global sign.
The complement bit does not affect the shift modulo n. -/
def symInputBit {n : ℕ} (hn : 0 < n) (j : Fin n) (flip : Bool)
    (i : Fin (2 * n)) : Bool :=
  xor flip (xor (decide (n ≤ i.val)) (inputBit j ⟨i.val % n, Nat.mod_lt _ hn⟩))

def SymExactAlgorithm (n k : ℕ) (hn : 0 < n) : Prop :=
  ∃ w : ℕ, ∃ A : QAlgorithms.QueryAlg (Fin (2 * n)) PUnit.{1} (Fin w) k,
    ∃ out : (Fin (2 * n) × PUnit.{1}) × Fin w → Fin n,
      ∀ (j : Fin n) (flip : Bool),
        A.outputProb (QAlgorithms.phaseOracle (fun p => symInputBit hn j flip p.1)) out j = 1

end OrderedSearchExact.Exact


