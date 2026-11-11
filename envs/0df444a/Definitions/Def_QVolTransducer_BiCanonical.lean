-- Prove2me | Definitions.Def_QVolTransducer_BiCanonical
-- name    : QVolTransducer_BiCanonical
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:23:20.821891+00:00
-- url     : https://prove2.me/theorems/319f53b0-cc04-4c41-ac88-4ea354f11004
-- title:
--   Bidirectional canonical transducer $T(O)=U(I_{\mathcal V}\oplus((O\oplus O^\dagger)\otimes I_{\mathcal W}))$
-- statement:
--   Let $\mathcal V$, $\mathcal H$, $\mathcal W$ be Hilbert spaces and let $\{O_x\}_{x\in D}$ be unitaries on $\mathcal H$ (the **oracles**). A **bidirectional canonical transducer** is given by a unitary
--
--   $$
--   U\in\mathcal U\bigl(\mathcal V\oplus(\mathcal H^{\oplus 2}\otimes\mathcal W)\bigr)
--   $$
--
--   that does not depend on the input $x$; on input $x$ it is the transducer
--
--   $$
--   T(O_x):=U\bigl(I_{\mathcal V}\oplus((O_x\oplus O_x^\dagger)\otimes I_{\mathcal W})\bigr),
--   $$
--
--   with public space $\mathcal V$ and private space $\mathcal H^{\oplus 2}\otimes\mathcal W$. Each application makes one forward and one inverse query.
--
--   Every algorithmic statement of the mission asserts the existence of one such $U$, chosen before the input (the convex body), so that the public and private spaces do not depend on the input.
--
--   **Formalization Note** The spaces are $\mathbb C^V$, $\mathbb C^H$, $\mathbb C^W$ for finite index types; $\mathcal H^{\oplus2}\otimes\mathcal W$ is $\mathbb C^{(H\sqcup H)\times W}$, and $O^\dagger$ is the conjugate transpose.
-- source:
--   Cornelissen, Apers, Gribling, Improved quantum volume estimation with transducers and amortized quantum walks, arXiv:2609.40217 (version of November 3, 2026, sha256 40d7b52d…), Definition 2.10.2, p.14 (PDF p.16)

import Mathlib
import Definitions.Def_QVolTransducer_transductionComplexity

namespace QVolTransducer

/-- A bidirectional canonical transducer (Cornelissen, Apers, Gribling, *Improved quantum volume
estimation with transducers and amortized quantum walks*, arXiv:2609.40217 (version of November 3,
2026, sha256 40d7b52d…), Definition 2.10.2, p.14: "T(O_x) := U(I_V ⊕ ((O_x ⊕ O_x†) ⊗ I_W)), where
U ∈ U(V ⊕ (H^{⊕2} ⊗ W)) does not depend on the input x"). It is given by its input-independent
unitary `U` on `V ⊕ ((H ⊕ H) × W)`, with public space `ℂ^V`, oracle space `ℂ^H` and workspace
`ℂ^W`.

**Formalization Note** The spaces are coordinate spaces over finite index types; `H^{⊕2} ⊗ W` is
`ℂ^((H ⊕ H) × W)`. -/
structure BiCanonical (V H W : Type*) [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H]
    [Fintype W] [DecidableEq W] where
  /-- The input-independent unitary `U ∈ U(V ⊕ (H^{⊕2} ⊗ W))`. -/
  U : Matrix.unitaryGroup (V ⊕ ((H ⊕ H) × W)) ℂ

namespace BiCanonical

variable {V H W : Type*} [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H] [Fintype W]
  [DecidableEq W]

/-- The transducer `T(O) := U (I_V ⊕ ((O ⊕ O†) ⊗ I_W))` obtained by instantiating the canonical
transducer `T` with the oracle `O` (arXiv:2609.40217, Definition 2.10.2, p.14). Its public space is
`ℂ^V` and its private space is `ℂ^((H ⊕ H) × W)`. -/
noncomputable def apply (T : BiCanonical V H W) (O : Matrix H H ℂ) :
    Matrix (V ⊕ ((H ⊕ H) × W)) (V ⊕ ((H ⊕ H) × W)) ℂ :=
  (T.U : Matrix (V ⊕ ((H ⊕ H) × W)) (V ⊕ ((H ⊕ H) × W)) ℂ) *
    Matrix.fromBlocks 1 0 0
      (Matrix.kronecker (Matrix.fromBlocks O 0 0 O.conjTranspose) (1 : Matrix W W ℂ))

end BiCanonical

end QVolTransducer


