-- Prove2me | Definitions.Def_BindingEntChannels_IsBoundEntangled
-- name    : BindingEntChannels_IsBoundEntangled
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:39:05.459918+00:00
-- url     : https://prove2.me/theorems/0559438e-bbff-4cdf-a6c7-7b7985325f08
-- title:
--   Bound entangled (BE) state: entangled but not distillable
-- statement:
--   A bipartite density matrix $\rho$ on $\mathbb C^I\otimes\mathbb C^J$ is **bound entangled** (BE) if
--
--   1. it is entangled, i.e. not separable (not a finite convex combination of product density matrices $A\otimes B$), and
--   2. it is not distillable: it is not free entangled (FE).
--
--   Following the paper (p. 1), FE states are those "which can be converted into pure singlet form by means of local quantum operations and classical communication", and BE states those "which cannot be distilled"; a state that is not BE "can be separable or FE" (p. 2).
--
--   **Formalization Note** "Distillable" is the platform definition of the paper's ref. [3]: for every $\varepsilon>0$ some local operation on finitely many copies produces, with positive probability, a two-qubit state of singlet fidelity at least $1-\varepsilon$.
-- source:
--   Horodecki, Horodecki, Horodecki, Binding entanglement channels, arXiv:quant-ph/9904092v1, §I, p. 1, and §II, p. 2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_BoundEntPPT_IsDistillable
import Definitions.Def_HorodeckiBoundKey_IsSeparable

open scoped Matrix

namespace BindingEntChannels

/-- Horodecki, Horodecki, Horodecki, *Binding entanglement channels*, arXiv:quant-ph/9904092v1,
p. 1 ("free entanglement (FE) which can be converted into pure singlet form by means of local
quantum operations and classical communication (LQCC)"; "bound entanglement (BE), which cannot be
distilled") and p. 2 ("Then it can be separable or FE"): a bipartite density matrix `ρ` on
`I × J` is *bound entangled* if it is entangled (not separable) and not distillable.

**Formalization Note.** "Separable" is the published `HorodeckiBoundKey.IsSeparable` (a finite
convex combination of product density matrices); "FE" is the published
`BoundEntPPT.IsDistillable`, the definition of the paper's ref. [3] (singlet fidelity tending to
one on a single output pair, with post-selection, from finitely many copies). -/
def IsBoundEntangled {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (ρ : Matrix (I × J) (I × J) ℂ) : Prop :=
  QAlgorithms.IsDensityMatrix ρ ∧ ¬ HorodeckiBoundKey.IsSeparable ρ ∧
    ¬ BoundEntPPT.IsDistillable ρ

end BindingEntChannels


