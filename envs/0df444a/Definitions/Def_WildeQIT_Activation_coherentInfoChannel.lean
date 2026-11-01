-- Prove2me | Definitions.Def_WildeQIT_Activation_coherentInfoChannel
-- name    : WildeQIT_Activation_coherentInfoChannel
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T19:12:42.402136+00:00
-- url     : https://prove2.me/theorems/22535661-b73e-44e9-88dd-404bbfc83515
-- title:
--   Channel coherent information $Q(\mathcal N)=\max_\varphi I(A\rangle B)_\sigma$
-- statement:
--   The **channel coherent information** of $\mathcal N_{A'\to B}$ is
--
--   $$
--   Q(\mathcal N)\equiv\max_{\varphi}\, I(A\rangle B)_\sigma ,\qquad I(A\rangle B)_\sigma=H(B)_\sigma-H(AB)_\sigma ,
--   $$
--
--   where the optimization is over all pure bipartite states $\varphi_{AA'}$ and $\sigma_{AB}\equiv\mathcal N_{A'\to B}(\varphi_{AA'})$. It is the $Q$ of (24.166); by Theorem 24.3.1 the quantum capacity is its regularization.
--
--   **Formalization Note** The maximum is a real supremum over pure inputs with a reference system of any finite dimension. The values are bounded above by $\log_2\dim\mathcal H_B$, and the book's maximum is attained, so the two agree. For an empty input type there is no pure state and the supremum is the junk value $0$. Entropies are the published `QAlgorithms.vnEntropy`, in bits.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 24.3.1, eq. (24.9), p. 661

import Definitions.Def_WildeQIT_Activation_PureInput
import Definitions.Def_WildeQIT_EADamping_idTensorApply
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_WildeQIT_partialTrace

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Theorem 24.3.1, p. 661, eq. (24.9) (the channel coherent information `Q(N)`).
-/

open Matrix

namespace WildeQIT.Activation

/-- **Channel coherent information** (Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, (24.9), p. 661): `Q(N) ≡ max_φ I(A⟩B)_σ`, "where the
optimization is with respect to all pure, bipartite states `φ_{AA′}` and
`σ_{AB} ≡ N_{A′→B}(φ_{AA′})`", with `I(A⟩B)_σ = H(B)_σ − H(AB)_σ` (Definition 11.5.1). This is
the `Q` of (24.166).

**Formalization Note.** Supremum `⨆` over pure inputs with a reference `Fin k` of any finite
dimension (`PureInput`); the values are bounded above by `log₂ |B|`, so `⨆` is the least upper
bound, which the book's maximum attains. `σ_B = Tr_R σ` is `WildeQIT.partialTraceLeft`; `H` is
the published `QAlgorithms.vnEntropy` (bits). Empty input space: no pure state exists and
`⨆ = 0`. -/
noncomputable def coherentInfoChannel {a b : Type} [Fintype a] [Fintype b] [DecidableEq a]
    [DecidableEq b] (N : QChannel a b) : ℝ :=
  ⨆ φ : PureInput a,
    (QAlgorithms.vnEntropy (partialTraceLeft (WildeQIT.EADamping.idTensorApply N (vecMulVec φ.vec (star φ.vec)))) -
      QAlgorithms.vnEntropy (WildeQIT.EADamping.idTensorApply N (vecMulVec φ.vec (star φ.vec))))

end WildeQIT.Activation


