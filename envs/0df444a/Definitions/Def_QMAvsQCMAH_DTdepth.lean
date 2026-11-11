-- Prove2me | Definitions.Def_QMAvsQCMAH_DTdepth
-- name    : QMAvsQCMAH_DTdepth
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:19:18.107695+00:00
-- url     : https://prove2.me/theorems/c35195bf-cde2-4be1-9d74-c94088e4e010
-- title:
--   Deterministic decision-tree depth
-- statement:
--   The **decision-tree depth** $\mathrm{DT}(g)$ of $g:\{0,1\}^P\to\{0,1\}$ is the least depth of a deterministic decision tree, querying only inputs in $P$, that computes $g(r)$ for every $r:P\to\{0,1\}$.
-- source:
--   Cakan, Classical Oracle Separation of QMA from the QCMA Hierarchy and Quantum Cryptography Even When P = QCMA, STOC 2027 submission (held version, sha256 336ce016…c897), Lemma 11, p.38

import Definitions.Def_QMAvsQCMAH_DTree

set_option autoImplicit false

namespace QMAvsQCMAH

/-- The **deterministic decision-tree depth** `DT(g)` of a function `g : {0,1}^P → {0,1}`: the
least depth of a decision tree querying only inputs in `P` that computes `g(r)` for every
`r : P → {0,1}`.

Cakan, *Classical Oracle Separation of QMA from the QCMA Hierarchy and Quantum Cryptography
Even When P = QCMA*, STOC 2027 submission (held version, sha256 336ce016…c897), Lemma 11, p.38 (PDF p.41): "DT denotes deterministic decision-tree depth".

**Formalization Note.** The tree is run on the assignment equal to `r` on `P` (its queries lie
in `P`, so the values off `P` are never read). The set is nonempty (the complete tree of depth
`|P|`), so the infimum is attained. -/
noncomputable def DTdepth {X : Type} [DecidableEq X] (P : Finset X)
    (g : ({u // u ∈ P} → Bool) → Bool) : ℕ :=
  sInf {d | ∃ t : DTree X Bool, t.LabelsIn ↑P ∧ t.depth = d ∧
    ∀ r : {u // u ∈ P} → Bool, t.eval (fun u => if h : u ∈ P then r ⟨u, h⟩ else false) = g r}

end QMAvsQCMAH


