-- Prove2me | Definitions.Def_DepthOneQExp_cnotAvg
-- name    : DepthOneQExp_cnotAvg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:50:29.294304+00:00
-- url     : https://prove2.me/theorems/8cacce6c-e183-45d3-9661-5e8931c0c4be
-- title:
--   Second-moment operator $\mathbb E_{P\sim\mu(G_n)} P\otimes P$
-- statement:
--   The second-moment operator of the CNOT group is the uniform average
--   $$
--   \mathbb E_{P\sim\mu(G_n)} P\otimes P = \frac1{|G_n|}\sum_{P\in G_n} P\otimes P ,
--   $$
--   with $P$ the permutation matrix of $P\in G_n$ and $\mu(G_n)$ the uniform distribution (Eqs. (2.28), (2.43)). Since the matrices are real, $P\otimes P=P\otimes\overline P$.
-- source:
--   Anshu–Balasubramanian–Haferkamp–Harrow–Tan, Depth-1 expanders on the unitary group and applications, arXiv:2609.01605 (held version, sha256 3c3f8513…aebfd87), Eqs. (2.28) and (2.43), pp.11, 13

import Mathlib
import Definitions.Def_MITMSynthesis_Gate
import Definitions.Def_DepthOneQExp_permToMatrix
import Definitions.Def_DepthOneQExp_cnotGroup

namespace DepthOneQExp

open scoped Kronecker

/-- The second-moment operator of the CNOT group, `E_{P∼µ(G_n)} P ⊗ P`
(Anshu–Balasubramanian–Haferkamp–Harrow–Tan, *Depth-1 expanders on the unitary group and
applications*, arXiv:2609.01605, held version sha256 3c3f8513…aebfd87, Eqs. (2.28) and (2.43),
pp.11, 13), where `µ(G_n)` is the uniform distribution on `G_n`:
`(1/|G_n|) Σ_{P ∈ G_n} P ⊗ P`, with `P` the permutation matrix `|x⟩ ↦ |P x⟩`.

**Formalization Note** The expectation over the finite group is the uniform finite average. The
matrices are real, so `P ⊗ P = P ⊗ P̄`, as the paper writes. -/
noncomputable def cnotAvg (n : ℕ) :
    Matrix (MITMSynthesis.Q n × MITMSynthesis.Q n) (MITMSynthesis.Q n × MITMSynthesis.Q n) ℂ :=
  (1 / (Fintype.card (cnotGroup n) : ℂ)) •
    ∑ P : cnotGroup n, (permToMatrix (P : Equiv.Perm (MITMSynthesis.Q n)) ⊗ₖ
      permToMatrix (P : Equiv.Perm (MITMSynthesis.Q n)))

end DepthOneQExp


