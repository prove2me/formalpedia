-- Prove2me | Definitions.Def_WildeQIT_EADamping_channelMutualInfo
-- name    : WildeQIT_EADamping_channelMutualInfo
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T18:37:30.205138+00:00
-- url     : https://prove2.me/theorems/e4133f2a-e1f3-45f9-aff1-9c8cc182bb66
-- title:
--   Mutual information of a quantum channel $I(\mathcal N)$
-- statement:
--   For a quantum channel $\mathcal N_{A'\to B}$, the **mutual information of the channel** is
--
--   $$
--   I(\mathcal N)\equiv\max_{\varphi_{AA'}} I(A;B)_\rho,\qquad \rho_{AB}\equiv\mathcal N_{A'\to B}(\varphi_{AA'}),
--   $$
--
--   the maximum over all pure bipartite input states $\varphi_{AA'}$, with a reference $A$ of any finite dimension.
--
--   By the Bennett–Shor–Smolin–Thapliyal theorem it equals the entanglement-assisted classical capacity of $\mathcal N$.
--
--   **Formalization Note** The maximum is written as a supremum `⨆` over all pure inputs (`PureInput`). The set of values is bounded above (for a pure input $I(A;B)_\rho\le 2\log_2|A'|$), so for a nonempty input space `⨆` is the least upper bound; theorems that need the maximum state its attainment. For an empty input space there is no input and `⨆` returns the junk value $0$; the theorems assume a nonempty input space.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, §13.4, p. 407, (13.121); Theorem 21.3.1, p. 593

import Definitions.Def_WildeQIT_EADamping_idTensorApply
import Definitions.Def_DattaDiscord_mutualInfo
import Definitions.Def_WildeQIT_Degradable_PureInput

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §13.4, p. 407, (13.121), and
Theorem 21.3.1, p. 593 (Mutual Information of a Quantum Channel).
-/

namespace WildeQIT.EADamping

/-- **Mutual information of a quantum channel** (Wilde, *From Classical to Quantum Shannon Theory*,
arXiv:1106.1445v8, p. 407, (13.121); p. 593): `I(N) ≡ max_{φ_{AA′}} I(A; B)_ρ`, with
`ρ_{AB} = N_{A′→B}(φ_{AA′})` and `φ_{AA′}` a pure bipartite state.

**Formalization Note.** `I(A; B)_ρ` is the published `DattaDiscord.mutualInfo`
(`H(A) + H(B) − H(AB)`, Definition 11.6.1, von Neumann entropy in bits). The maximum is a supremum `⨆` over all pure inputs `φ_{AA′}` with a
reference `A = Fin m` of any finite dimension (`PureInput`). The set of values is bounded above
(`I(A; B) ≤ 2 log₂ |a|` for a pure input), so `⨆` is its least upper bound. When the input space
is empty there is no input and `⨆` returns the junk value `0`; theorems assume a nonempty input
space. -/
noncomputable def channelMutualInfo {a b : Type} [Fintype a] [Fintype b] [DecidableEq a]
    [DecidableEq b] (N : QChannel a b) : ℝ :=
  ⨆ φ : WildeQIT.Degradable.PureInput a, DattaDiscord.mutualInfo (idTensorApply N (QAlgorithms.pureDensity φ.ψ))

end WildeQIT.EADamping


