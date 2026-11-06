-- Prove2me | Definitions.Def_SymNormLoad_OnlineAlgorithm
-- name    : SymNormLoad_OnlineAlgorithm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:28:46.130492+00:00
-- url     : https://prove2.me/theorems/644ea020-655c-4593-9186-f7aff1be594f
-- title:
--   Deterministic online assignment algorithm on $M$ machines
-- statement:
--   Jobs arrive one at a time and each must be assigned integrally and irrevocably before the next arrives. A **deterministic online algorithm** on $M$ machines is a rule that, given the processing-time vectors $p_0,\dots,p_n$ of the jobs seen so far (the current job is the last), returns the machine for job $n$. Its **run** on an instance $p=(p_0,\dots,p_{N-1})$ assigns job $j$ to the machine the rule returns on the prefix $p_0,\dots,p_j$.
--
--   The rule never sees later jobs or the number of jobs; earlier decisions are functions of earlier prefixes, so they are not needed as input.
--
--   **Formalization Note** The type is `(n : ℕ) → (Fin (n+1) → Fin M → ℝ) → Fin M`, and `runAssign A p j` applies `A` to the prefix ending at job `j`. Jobs are 0-based; no computability requirement is imposed.
-- source:
--   Chen–Im–Sirri, Online Load Balancing under Symmetric Norms, manuscript (STOC 2027 submission), Section 1.1, p.2

import Mathlib

namespace SymNormLoad

/-- **Deterministic online assignment algorithm on `M` unrelated machines.** Chen–Im–Sirri,
*Online Load Balancing under Symmetric Norms*, manuscript (STOC 2027 submission), §1.1, p.2:
jobs arrive one at a time, and each job must be assigned integrally and irrevocably before the
next job arrives.

An algorithm is a rule that, given the processing-time vectors of jobs `0, …, n` (the current
job is the last one), returns the machine of job `n`. It never sees later jobs or the number of
jobs. Earlier decisions are functions of earlier prefixes, so they need not be an input.

**Formalization Note** Jobs are 0-based. The rule is an arbitrary function (no computability
requirement), and it is deterministic. -/
def OnlineAlgorithm (M : ℕ) : Type :=
  (n : ℕ) → (Fin (n + 1) → Fin M → ℝ) → Fin M

/-- The run of an online algorithm on an instance `p : Fin N → Fin M → ℝ`: job `j` goes to the
machine `A j (p 0, …, p j)` chosen from the prefix ending at `j`. -/
def runAssign {M N : ℕ} (A : OnlineAlgorithm M) (p : Fin N → Fin M → ℝ) : Fin N → Fin M :=
  fun j => A j.val (fun k => p (Fin.castLE j.isLt k))

end SymNormLoad


