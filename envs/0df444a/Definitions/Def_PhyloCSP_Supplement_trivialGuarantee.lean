-- Prove2me | Definitions.Def_PhyloCSP_Supplement_trivialGuarantee
-- name    : PhyloCSP_Supplement_trivialGuarantee
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T12:25:34.191218+00:00
-- url     : https://prove2.me/theorems/792b6582-c233-4b65-81a7-22e202a27e47
-- title:
--   The trivial approximation guarantee $\alpha_0$ of a predicate
-- statement:
--   For a predicate $\varphi$, the **trivial approximation guarantee** is the largest fraction of constraints that can be satisfied on every instance of $\mathrm{CSP}(\varphi)$:
--   $$
--   \alpha_0(\varphi)=\inf_{I}\ \max_{T}\ \mathrm{val}(I,T),
--   $$
--   the infimum over all instances $I$ of $\mathrm{CSP}(\varphi)$ with at least one constraint, the maximum over all solutions $T$ (trees on the variables of $I$).
--
--   This is the guarantee of pp.1–2: "every instance has a solution satisfying at least an $\alpha_0$ fraction of its constraints … We refer to $\alpha_0$ as the trivial guarantee because it is obtainable on every instance." Theorem 6.1 computes it for arity 4.
--
--   **Formalization Note** The paper names $\alpha_0$ through the characterization of Chatziafratis and Makarychev [CM23]; this definition is the intrinsic quantity the page describes, so that Theorem 6.1 asserts both that every instance has a solution of value at least the formula and that no larger constant has this property. The maximum is over finitely many trees and the infimum is over a nonempty family of values in $[0,1]$, so no junk value arises.
-- source:
--   Makarychev, Approximation Algorithms for Satisfiable Phylogenetic CSPs, STOC 2027 submission (manuscript sha256 3444b6c029bce73ce9a6ad0ae6bc8386c291dcb0b1e504e8216c60cd4d682dac), pp.1–2 (PDF pp.3–4); Theorem 6.1 and its proof, pp.15–17 (PDF pp.17–19)

import Mathlib
import Definitions.Def_PhyloCSP_Supplement_Instance

set_option autoImplicit false

namespace PhyloCSP

namespace Supplement

/-- **The trivial approximation guarantee `α₀` of a predicate.**

Makarychev, *Approximation Algorithms for Satisfiable Phylogenetic CSPs*, STOC 2027 submission
(manuscript sha256 3444b6c0…682dac), pp.1–2 (PDF pp.3–4): "their result identifies a guarantee
α0 such that every instance has a solution satisfying at least an α0 fraction of its constraints.
… We refer to α0 as the trivial guarantee because it is obtainable on every instance." Theorem 6.1,
p.15 (PDF p.17), and its proof, "First, we show that α0 is at least the right-hand side of (3)
… Optimality. We now prove that this guarantee is optimal."

`trivialGuarantee φ` is the largest fraction obtainable on every instance of `CSP(φ)`: the infimum,
over all instances of `CSP(φ)` with at least one constraint, of the optimal value
`max_T value(I, T)`.

**Formalization Note.** The paper names `α₀` through the characterization of [CM23]; this is the
intrinsic quantity the page describes (every instance has a solution of value at least `α₀`, and no
larger constant has this property). The optimal value is a maximum over the finitely many trees on
the variables; the infimum is over a nonempty family of values in `[0, 1]`, so neither takes a junk
value. -/
noncomputable def trivialGuarantee {k : ℕ} (φ : Predicate k) : ℝ :=
  ⨅ I : {I : Instance (singleLang φ) // I.constraints ≠ []},
    ⨆ T : Pattern (Fin I.1.n), value I.1 T

end Supplement

end PhyloCSP


