-- Prove2me | Definitions.Def_RefWPHP_Supplement_PKAutomatable
-- name    : RefWPHP_Supplement_PKAutomatable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T22:25:11.361979+00:00
-- url     : https://prove2.me/theorems/8dc74d49-0dc3-4ff9-8537-f7186f077cfe
-- title:
--   Polynomial-time automatability of PK$_d$ on CNF formulas
-- statement:
--   Following Bonet, Pitassi and Raz, a refutation system $P$ is **automatable in polynomial time** on CNF formulas if there are an algorithm $A$ and a polynomial $p$ such that, given an unsatisfiable CNF formula $\varphi$, the algorithm outputs a $P$-refutation of $\varphi$ in time
--
--   $$
--   p\bigl(|\varphi| + \mathrm{size}_P(\varphi)\bigr),
--   $$
--
--   where $\mathrm{size}_P(\varphi)$ is the minimum size of a $P$-refutation of $\varphi$. Here $P = \mathrm{PK}_d$; on satisfiable inputs nothing is required.
--
--   **Formalization Note** Algorithms are Mathlib's `Turing.FinTM2` machines (finitely many stacks, states and labels) whose input and output alphabets are identified with $\{0,1\}$; the step count on each input is bounded with `Turing.TM2OutputsInTime`. Inputs are `encodeCNF φ` and outputs `encodeDeriv ρ` for a $\mathrm{PK}_d$-refutation $\rho$ of the cedents of $\varphi$; $\mathrm{size}_{\mathrm{PK}_d}(\varphi)$ is `pkSize d φ`. The paper names no machine model; polynomial-time automatability is invariant under the polynomial simulations between standard deterministic models.
-- source:
--   Arteche, Resolution Lower Bounds versus the Weak Pigeonhole Principle, STOC 2027 submission (held manuscript, sha256 ee75d7f1…), §2.1.4, p.17 (PDF p.19)

import Mathlib
import Definitions.Def_RefWPHP_Supplement_Unsat
import Definitions.Def_RefWPHP_Supplement_cnfCedents
import Definitions.Def_RefWPHP_Supplement_encodeCNF

namespace RefWPHP

namespace Supplement

/-- `PK_d` is automatable in polynomial time on CNF formulas, N. Arteche, *Resolution Lower Bounds
versus the Weak Pigeonhole Principle*, STOC 2027 submission (held manuscript, sha256 ee75d7f1…),
§2.1.4, p.17 (PDF 19), following Bonet, Pitassi and Raz: "there exists an algorithm that given a
propositional tautology `φ`, outputs a `P`-proof of `φ` in time `T(|φ| + size_P(φ))` … The
definition for refutation systems and unsatisfiable `φ` is analogous. When `T` is a polynomial, we
simply say `P` is automatable."

There are a machine `tm` and a polynomial `p` such that on the code of every unsatisfiable CNF `φ`
(any `n`, `m`), `tm` halts within `p(|φ| + size_{PK_d}(φ))` steps with the code of a
`PK_d`-refutation of the cedents of `φ` on its output stack. Satisfiable inputs are unconstrained.

**Formalization Note.**
1. The machine model is Mathlib's `Turing.FinTM2` (finitely many stacks, states and labels), with
   input and output alphabets identified with `Bool`; `Turing.TM2OutputsInTime` (a type of
   evaluation traces, hence `Nonempty`) bounds the number of steps on each input. The paper names
   no model; polynomial-time automatability is invariant under the polynomial simulations between
   standard deterministic models.
2. Inputs are `encodeCNF φ`, `|φ|` its length; outputs are `encodeDeriv ρ`, whose length is between
   `derivSize ρ` and a fixed polynomial of `derivSize ρ · (n + 1)`.
3. `size_{PK_d}(φ)` is `pkSize d φ`, the minimum `derivSize` of a `PK_d`-refutation of `φ`. -/
def PKAutomatable (d : ℕ) : Prop :=
  ∃ (tm : Turing.FinTM2) (e₀ : tm.Γ tm.k₀ ≃ Bool) (e₁ : tm.Γ tm.k₁ ≃ Bool) (p : Polynomial ℕ),
    ∀ (n m : ℕ) (φ : Fin m → Finset (Lit n)), Unsat φ →
      ∃ ρ : List (Cedent (Fin n)), IsPKRefutation d (cnfCedents φ) ρ ∧
        Nonempty (Turing.TM2OutputsInTime tm ((encodeCNF φ).map e₀.symm)
          (some ((encodeDeriv ρ).map e₁.symm)) (p.eval ((encodeCNF φ).length + pkSize d φ)))

end Supplement

end RefWPHP


