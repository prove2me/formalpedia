-- Prove2me | Definitions.Def_WildeQIT_Degradable_mutualInfoChannel
-- name    : WildeQIT_Degradable_mutualInfoChannel
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:57:06.359529+00:00
-- url     : https://prove2.me/theorems/e39200e2-4e1d-45a6-b84f-d34c10a07192
-- title:
--   Mutual information of a quantum channel $I(\mathcal N)$
-- statement:
--   The **mutual information** of a quantum channel $\mathcal N_{A'\to B}$ is
--
--   $$
--   I(\mathcal N) \equiv \max_{\varphi_{AA'}} I(A;B)_\rho ,\qquad \rho_{AB}=\mathcal N_{A'\to B}(\varphi_{AA'}),
--   $$
--
--   the maximum over all pure input states $\varphi_{AA'}$, with a reference system $A$ of any dimension. It is the entanglement-assisted classical capacity of the channel.
--
--   **Formalization Note** The maximum is the real supremum over `PureInput` (reference `Fin m`, any `m`). $\mathcal N_{A'\to B}(\varphi_{AA'})$ is the published `QAlgorithms.idTensorSuperop` (reference = left factor) applied to $|\varphi\rangle\langle\varphi|$ (`QAlgorithms.pureDensity`), and $I(A;B)$ is the published `DattaDiscord.mutualInfo`. The values are bounded by $2\log_2|A'|$, so the supremum is finite and equals the attained maximum.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, §13.4, eqs. (13.120)–(13.121), pp. 406–407

import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_DattaDiscord_mutualInfo
import Definitions.Def_WildeQIT_QChannel
import Definitions.Def_WildeQIT_Degradable_PureInput

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §13.4, p. 407, eq. (13.121) (Mutual Information of a Quantum Channel).
-/

namespace WildeQIT.Degradable

/-- **Mutual information of a quantum channel** (Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, p. 407, eq. (13.121)):
`I(N) ≡ max_{φ_{AA′}} I(A; B)_ρ`, with `ρ_{AB} = N_{A′→B}(φ_{AA′})` (13.120).

**Formalization Note.** The maximum is a supremum `⨆` over all pure inputs `φ_{AA′}` with a
reference `A = Fin m` of any finite dimension (`PureInput`). `N_{A′→B}(φ_{AA′})` is
`id_A ⊗ N` applied to `|φ⟩⟨φ|`, written with the published `QAlgorithms.idTensorSuperop`
(reference = left factor) and `QAlgorithms.pureDensity`; `I(A; B)` is the published
`DattaDiscord.mutualInfo` (`H(A) + H(B) − H(AB)`, von Neumann entropy in bits). The set of
values is bounded above (`I(A; B) ≤ 2 log₂ |a|` for a pure input), so `⨆` is the least upper
bound; it is attained, so it equals the book's maximum. When the input space is empty there is
no input and `⨆` returns `0`. -/
noncomputable def mutualInfoChannel {a b : Type} [Fintype a] [Fintype b] [DecidableEq a]
    [DecidableEq b] (N : QChannel a b) : ℝ :=
  ⨆ φ : PureInput a, DattaDiscord.mutualInfo
    (QAlgorithms.idTensorSuperop (R := Fin φ.m) N.apply (QAlgorithms.pureDensity φ.ψ))

end WildeQIT.Degradable


