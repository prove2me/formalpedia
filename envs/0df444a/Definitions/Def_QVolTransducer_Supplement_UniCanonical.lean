-- Prove2me | Definitions.Def_QVolTransducer_Supplement_UniCanonical
-- name    : QVolTransducer_Supplement_UniCanonical
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:32:01.672252+00:00
-- url     : https://prove2.me/theorems/a0d4fe7b-c546-4ada-9b81-e71e654b0dae
-- title:
--   Unidirectional canonical transducer $T(O)=U(I_{\mathcal V}\oplus(O\otimes I_{\mathcal W}))$
-- statement:
--   Let $\mathcal V,\mathcal H,\mathcal W$ be Hilbert spaces and $\{O_x\}_{x\in\mathcal D}\subseteq\mathcal U(\mathcal H)$ a set of oracles. A **unidirectional canonical transducer** is the map
--
--   $$T(O_x):=U\big(I_{\mathcal V}\oplus(O_x\otimes I_{\mathcal W})\big),$$
--
--   where $U\in\mathcal U(\mathcal V\oplus(\mathcal H\otimes\mathcal W))$ does not depend on the input $x$. Its public space is $\mathcal V$ and its private space is $\mathcal H\otimes\mathcal W$; each application makes one forward query.
--
--   It is the one-directional counterpart of the published bidirectional canonical transducer, and is the object of Theorem 2.12.
--
--   **Formalization Note** As for the published `QVolTransducer.BiCanonical`, the spaces are coordinate spaces $\mathbb C^V,\mathbb C^H,\mathbb C^W$ over finite types and $\mathcal H\otimes\mathcal W$ is $\mathbb C^{H\times W}$; the structure stores the unitary $U$ and `apply` instantiates it with an oracle matrix.
-- source:
--   Cornelissen, Apers, Gribling, Improved quantum volume estimation with transducers and amortized quantum walks, arXiv:2609.40217 (version of November 3, 2026, sha256 40d7b52d…), Definition 2.10.1, p.14 (PDF p.16)

import Mathlib
import Definitions.Def_QVolTransducer_transductionComplexity

namespace QVolTransducer.Supplement

/-- A unidirectional canonical transducer (Cornelissen, Apers, Gribling, *Improved quantum volume
estimation with transducers and amortized quantum walks*, arXiv:2609.40217 (version of November 3,
2026, sha256 40d7b52d…), Definition 2.10.1, p.14: "T(O_x) := U(I_V ⊕ (O_x ⊗ I_W)), where
U ∈ U(V ⊕ (H ⊗ W)) does not depend on the input x"). It is given by its input-independent unitary
`U` on `V ⊕ (H × W)`, with public space `ℂ^V`, oracle space `ℂ^H` and workspace `ℂ^W`.

**Formalization Note** As for the published bidirectional `QVolTransducer.BiCanonical`, the spaces
are coordinate spaces over finite index types and `H ⊗ W` is `ℂ^(H × W)`. -/
structure UniCanonical (V H W : Type*) [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H]
    [Fintype W] [DecidableEq W] where
  /-- The input-independent unitary `U ∈ U(V ⊕ (H ⊗ W))`. -/
  U : Matrix.unitaryGroup (V ⊕ (H × W)) ℂ

namespace UniCanonical

variable {V H W : Type*} [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H] [Fintype W]
  [DecidableEq W]

/-- The transducer `T(O) := U (I_V ⊕ (O ⊗ I_W))` obtained by instantiating the unidirectional
canonical transducer with the oracle `O` (arXiv:2609.40217, Definition 2.10.1, p.14). Its public
space is `ℂ^V` and its private space is `ℂ^(H × W)`. -/
noncomputable def apply (T : UniCanonical V H W) (O : Matrix H H ℂ) :
    Matrix (V ⊕ (H × W)) (V ⊕ (H × W)) ℂ :=
  (T.U : Matrix (V ⊕ (H × W)) (V ⊕ (H × W)) ℂ) *
    Matrix.fromBlocks 1 0 0 (Matrix.kronecker O (1 : Matrix W W ℂ))

end UniCanonical

end QVolTransducer.Supplement


