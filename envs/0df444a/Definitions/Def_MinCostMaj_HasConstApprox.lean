-- Prove2me | Definitions.Def_MinCostMaj_HasConstApprox
-- name    : MinCostMaj_HasConstApprox
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T06:33:09.276534+00:00
-- url     : https://prove2.me/theorems/2ec2ae46-51cf-4aca-8e49-69c362b13753
-- title:
--   $\mathrm{MinCostCSP}(\mathbf A)$ has a randomized polynomial-time constant-factor approximation
-- statement:
--   $\mathrm{MinCostCSP}(\mathbf A)$ **admits a randomized polynomial-time constant-factor approximation algorithm** if there are a constant $C\ge1$, a polynomial $p$ and a polynomial-time algorithm that reads an instance $I$ and a coin string $w$ such that, for every instance $I$:
--
--   1. for every coin string $w$ of length $p(|\mathrm{enc}(I)|)$, the algorithm outputs a solution of $I$ if $I$ has one, and outputs *infeasible* otherwise;
--   2. the expected cost of the output over uniform coin strings of that length is at most $C\cdot\mathrm{OPT}(I)$.
--
--   $C$ and $p$ are fixed before the instance. Costs may be $\infty$; if every solution has infinite cost the bound is vacuous but a solution must still be returned.
--
--   This is the first alternative of the main theorem; the algorithm of §5 (consistency, LP relaxation, randomized threshold rounding, then solving the truncated instance) is of this kind.
--
--   **Formalization Note** "Polynomial time" is Mathlib's `Turing.TM2ComputableInPolyTime` on the fixed binary encodings; the expected cost is the exact average over all coin strings, computed in $[0,\infty]$. Inputs that encode no well-formed instance may get any output.
-- source:
--   Kozik, Živný, Constant-factor approximation of MinCostCSP with a conservative majority polymorphism, arXiv:2607.10667 (held version, sha256 ec17e13c…), Theorem 1.1, p.4; §5, pp.10–11 (PDF pp.5, 11–12)

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_MinCostMaj_Struct
import Definitions.Def_MinCostMaj_MCInst
import Definitions.Def_MinCostMaj_encInst
import Definitions.Def_MinCostMaj_coinAvg

namespace MinCostMaj

open scoped ENNReal

/-- The cost of an algorithm's answer: `0` for "infeasible" (`none`); for a list of `n` values
`< d` the cost of that assignment; `⊤` for any other list. -/
noncomputable def outCost (d : ℕ) (I : MCInst) : Option (List ℕ) → ℝ≥0∞
  | none => 0
  | some L =>
    if h : L.length = I.n ∧ ∀ x ∈ L, x < d then
      I.costOf (fun x : Fin I.n =>
        (⟨L.get (x.cast h.1.symm), h.2 _ (List.get_mem _ _)⟩ : Fin d))
    else ⊤

/-- **MinCostCSP(A) admits a randomized polynomial-time constant-factor approximation algorithm.**

Kozik, Živný, *Constant-factor approximation of MinCostCSP with a conservative majority
polymorphism*, arXiv:2607.10667, Theorem 1.1, first bullet, p.4; the algorithm of §5, pp.10–11
(it outputs "infeasible" exactly when there is no solution, and otherwise a solution whose expected
cost is within a constant factor of the optimum, Proposition 5.3).

There are a constant `C ≥ 1`, a polynomial `p` and a polynomial-time machine `alg` reading an
instance and a coin string such that, for every well-formed instance `I` and **every** coin string
of length `p(|enc I|)`, `alg` outputs a solution if `I` has one and "infeasible" (`none`)
otherwise, and the average cost of the output over all such coin strings is at most `C · OPT(I)`.

**Formalization Note.** "Randomized polynomial-time" is Mathlib's
`Turing.TM2ComputableInPolyTime` from `encInstCoins` (instance and coin string, binary) to `encOut`,
with coins uniform on strings of length `p(|enc I|)` (`coinAvg`, the exact average); the guarantee
is in expectation (Proposition 5.3). `C` and `p` are chosen before the instance. Costs may be `∞`
(Definition 2.1); a solution must be returned even when every solution has infinite cost
(`OPT = ∞`), and the cost bound is then vacuous. Malformed inputs may get any output. -/
def HasConstApprox {d : ℕ} (A : Struct d) : Prop :=
  ∃ (C : ℝ) (p : Polynomial ℕ) (alg : MCInst × List Bool → Option (List ℕ)),
    1 ≤ C ∧
    Nonempty (Turing.TM2ComputableInPolyTime encInstCoins encOut alg) ∧
    ∀ I : MCInst, I.WellFormed A →
      (∀ w : List Bool, w.length = p.eval (encInst I).length →
        ((∃ α : Fin I.n → Fin d, I.IsSolution A α) →
            ∃ α : Fin I.n → Fin d, I.IsSolution A α ∧
              alg (I, w) = some (List.ofFn (fun x => (α x : ℕ)))) ∧
        ((¬ ∃ α : Fin I.n → Fin d, I.IsSolution A α) → alg (I, w) = none)) ∧
      coinAvg I p (fun w => outCost d I (alg (I, w))) ≤ ENNReal.ofReal C * I.OPT A

end MinCostMaj


