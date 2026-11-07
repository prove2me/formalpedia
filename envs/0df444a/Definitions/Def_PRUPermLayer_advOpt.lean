-- Prove2me | Definitions.Def_PRUPermLayer_advOpt
-- name    : PRUPermLayer_advOpt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:30:33.172286+00:00
-- url     : https://prove2.me/theorems/11d201c9-aaf9-49cf-b760-1ced9216a5c5
-- title:
--   Optimal $t$-query forward advantage $\mathrm{Adv}^{\mathrm{opt}}_t(E)$
-- statement:
--   The **optimal $t$-query forward advantage** of an ensemble $E$ on $U(N)$, $N = 2^n$, is
--   $$
--   \mathrm{Adv}^{\mathrm{opt}}_t(E) = \sup_{A} \mathrm{Adv}_A(E, \mathrm{Haar}),
--   $$
--   the supremum over all $t$-query forward algorithms $A$, which may be computationally unbounded.
--
--   **Formalization Note** A supremum of real numbers. For a probability measure $E$ the family is nonempty and bounded by $1$ (proved in the sanity file), so the supremum is the genuine least upper bound.
-- source:
--   Shen–Zhong, Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), §2.2, p.9 (PDF p.11)

import Mathlib
import Definitions.Def_PRUPermLayer_advantage
import Definitions.Def_PRUPermLayer_haar
open MeasureTheory

namespace PRUPermLayer

/-- The optimal `t`-query forward advantage `Adv^opt_t(E) = sup_A Adv_A(E, Haar)` over all
(computationally unbounded) `t`-query forward algorithms (Shen–Zhong, *Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates*, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), §2.2, p.9 (PDF p.11)).

**Formalization Note** A real supremum. It is over a nonempty family bounded by `1` for every
probability measure `E` (proved in the sanity file), so it is the genuine least upper bound and not
the junk value of an unbounded family. -/
noncomputable def advOpt (n t : ℕ) (E : Measure (Matrix.unitaryGroup (Fin (2 ^ n)) ℂ)) : ℝ :=
  ⨆ alg : FwdAlg n t, advantage alg E (haar n)

end PRUPermLayer


