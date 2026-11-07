-- Prove2me | Definitions.Def_ReplicableOL_outputDisagree
-- name    : ReplicableOL_outputDisagree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:43:35.789848+00:00
-- url     : https://prove2.me/theorems/f9054939-641c-41d2-9137-7659e72c24a3
-- title:
--   Per-seed disagreement $\rho_F(Q,r)$ of an output $F$
-- statement:
--   The **per-seed disagreement** of an output $F$ is $\rho_F(Q,r)=\mathbb P_{S,S'\sim Q}[F(S,r)\ne F(S',r)]$, with $S,S'$ independent. For $F=\tau$ it is the quantity $\rho_\tau(Q,r)$.
--
--   **Formalization Note** The value is read in `ℝ` through `toReal`; for a probability law `Q` it is finite.
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Sec. 2.3, p.8

import Mathlib
open MeasureTheory ProbabilityTheory

namespace ReplicableOL

/-- **Per-seed disagreement $\rho_F(Q,r)$ of an output $F$.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Sec. 2.3, p.8. "ρ_F(Q, r) is as defined after Definition 2.1, with F in place of τ".

**Formalization Note.** The value is read in `ℝ` through `toReal`; for a probability law `Q` it is finite. -/
noncomputable def outputDisagree {X Z R : Type*} [MeasurableSpace X]
    (F : X → R → Z) (Q : Measure X) (r : R) : ℝ :=
  ((Q.prod Q) {p | F p.1 r ≠ F p.2 r}).toReal

end ReplicableOL


