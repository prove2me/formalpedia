-- Prove2me | Definitions.Def_WildeQIT_Activation_privateInfoChannel
-- name    : WildeQIT_Activation_privateInfoChannel
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T19:13:18.33733+00:00
-- url     : https://prove2.me/theorems/a467eefc-c4df-41d2-a5fb-ca1cb9685a15
-- title:
--   Private information of a quantum channel $P(\mathcal N)$ (Definition 13.6.1)
-- statement:
--   **Definition 13.6.1.** The **private information** of a quantum channel $\mathcal N$ is
--
--   $$
--   P(\mathcal N)\equiv\max_{\rho_{XA'}}\; I(X;B)_\rho-I(X;E)_\rho ,
--   $$
--
--   where the maximization is over all classical–quantum input states $\rho_{XA'}=\sum_xp_X(x)|x\rangle\langle x|_X\otimes\rho^x_{A'}$ and the entropic quantities are evaluated on $U^{\mathcal N}_{A'\to BE}(\rho_{XA'})$.
--
--   It is the $P(\mathcal N_2)$ of (24.166).
--
--   **Formalization Note** The maximum is a real supremum over ensembles with a finite alphabet of any size. The values are bounded above by $\log_2\dim\mathcal H_B$, and the book's maximum is attained, so the two agree. For an empty input type there is no ensemble and the supremum is the junk value $0$.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Definition 13.6.1, eq. (13.179), p. 416

import Definitions.Def_WildeQIT_Activation_privateInfoEnsemble

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Definition 13.6.1 (Private Information of a Quantum Channel), p. 416, eq. (13.179).
-/

namespace WildeQIT.Activation

/-- **Definition 13.6.1 (Private Information of a Quantum Channel)** (Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, p. 416, eq. (13.179)):
`P(N) ≡ max_{ρ_{XA′}} I(X; B)_ρ − I(X; E)_ρ`, "where the maximization is with respect to all
states of the form in (13.178) and the entropic quantities are evaluated with respect to the
state `U^N_{A′→BE}(ρ_{XA′})`".

**Formalization Note.** Supremum `⨆` over all ensembles with a finite alphabet `Fin k` of any
size (`CQInput`); the values are bounded above by `log₂ |B|`, so `⨆` is the least upper bound,
which the book's maximum attains. Empty input space: no ensemble exists and `⨆ = 0`. -/
noncomputable def privateInfoChannel {a b : Type} [Fintype a] [Fintype b] [DecidableEq a]
    [DecidableEq b] (N : QChannel a b) : ℝ :=
  ⨆ E : WildeQIT.Degradable.CQInput a, privateInfoEnsemble N E

end WildeQIT.Activation


