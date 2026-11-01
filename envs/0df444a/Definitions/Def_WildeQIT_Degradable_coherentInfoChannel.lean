-- Prove2me | Definitions.Def_WildeQIT_Degradable_coherentInfoChannel
-- name    : WildeQIT_Degradable_coherentInfoChannel
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:57:51.100674+00:00
-- url     : https://prove2.me/theorems/aafa6a83-9620-46a2-9bc8-87085fa34ce0
-- title:
--   Coherent information of a quantum channel $Q(\mathcal N)$ (Definition 13.5.1)
-- statement:
--   The **coherent information** of a quantum channel $\mathcal N_{A'\to B}$ is the maximum of the coherent information with respect to all input pure states:
--
--   $$
--   Q(\mathcal N) \equiv \max_{\varphi_{AA'}} I(A\rangle B)_\rho ,\qquad \rho_{AB}=\mathcal N_{A'\to B}(\varphi_{AA'}),
--   $$
--
--   where $I(A\rangle B)_\rho=H(B)_\rho-H(AB)_\rho$. It is a lower bound on the quantum capacity of the channel, and equals it for degradable channels.
--
--   **Formalization Note** The maximum is the real supremum over `PureInput` (reference `Fin m`, any `m`), with $\mathcal N_{A'\to B}(\varphi_{AA'})$ given by `QAlgorithms.idTensorSuperop`. The values are at most $\log_2|B|$, so the supremum is finite and equals the attained maximum.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Definition 13.5.1, eqs. (13.146)–(13.147), p. 411

import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_WildeQIT_QChannel
import Definitions.Def_WildeQIT_Degradable_coherentInfoState
import Definitions.Def_WildeQIT_Degradable_PureInput

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Definition 13.5.1 (Coherent Information of a Quantum Channel), p. 411.
-/

namespace WildeQIT.Degradable

/-- **Definition 13.5.1 (Coherent Information of a Quantum Channel)** (Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, p. 411,
eq. (13.147)): "The coherent information `Q(N)` of a quantum channel is the maximum of the
coherent information with respect to all input pure states: `Q(N) ≡ max_{φ_{AA′}} I(A⟩B)_ρ`",
with `ρ_{AB} = N_{A′→B}(φ_{AA′})` (13.146).

**Formalization Note.** The maximum is a supremum `⨆` over all pure inputs with a reference
`A = Fin m` of any finite dimension (`PureInput`); `N_{A′→B}(φ_{AA′})` is the published
`QAlgorithms.idTensorSuperop` (reference = left factor) applied to `|φ⟩⟨φ|`. The values are
bounded above (`I(A⟩B) ≤ H(B) ≤ log₂ |b|`), so `⨆` is the least upper bound, which the book's
maximum attains. When the input space is empty there is no input and `⨆` returns `0`. -/
noncomputable def coherentInfoChannel {a b : Type} [Fintype a] [Fintype b] [DecidableEq a]
    [DecidableEq b] (N : QChannel a b) : ℝ :=
  ⨆ φ : PureInput a, coherentInfoState
    (QAlgorithms.idTensorSuperop (R := Fin φ.m) N.apply (QAlgorithms.pureDensity φ.ψ))

end WildeQIT.Degradable


