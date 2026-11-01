-- Prove2me | Definitions.Def_WildeQIT_Degradable_holevoInfoChannel
-- name    : WildeQIT_Degradable_holevoInfoChannel
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:57:35.495852+00:00
-- url     : https://prove2.me/theorems/a4609f17-6935-4dd1-99d7-f91b4a3cf332
-- title:
--   Holevo information of a quantum channel $\chi(\mathcal N)$ (Definition 13.3.1)
-- statement:
--   The **Holevo information** of a quantum channel $\mathcal N_{A\to B}$ is
--
--   $$
--   \chi(\mathcal N) \equiv \max_{\rho_{XA}} I(X;B)_\rho ,
--   $$
--
--   where the maximization is over all classical–quantum inputs $\rho_{XA}=\sum_x p_X(x)|x\rangle\langle x|_X\otimes\rho^x_A$ and $I(X;B)_\rho$ is evaluated on $\rho_{XB}=\sum_x p_X(x)|x\rangle\langle x|_X\otimes\mathcal N_{A\to B}(\rho^x_A)$. It measures the classical correlations Alice can establish with Bob through one use of the channel.
--
--   **Formalization Note** The maximum is the real supremum over classical–quantum inputs with alphabets `Fin k` of every size (`CQInput`). The values satisfy $0\le I(X;B)\le\log_2|B|$, so the supremum is that of a nonempty bounded set; the maximum is attained, so the two agree. $I(X;B)$ is the published `DattaDiscord.mutualInfo` of the classical–quantum state.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Definition 13.3.1, eqs. (13.82)–(13.84), pp. 400–401

import Definitions.Def_WildeQIT_Degradable_cqState
import Definitions.Def_DattaDiscord_mutualInfo
import Definitions.Def_WildeQIT_Degradable_CQInput
import Definitions.Def_WildeQIT_QChannel

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Definition 13.3.1 (Holevo Information of a Quantum Channel), p. 401.
-/

namespace WildeQIT.Degradable

/-- **Definition 13.3.1 (Holevo Information of a Quantum Channel)** (Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, p. 401,
eq. (13.84)): `χ(N) ≡ max_{ρ_{XA}} I(X; B)_ρ`, "where the maximization is with respect to all
input classical–quantum states of the form in (13.82) and `I(X; B)_ρ` is evaluated with respect
to the state in (13.83)", `ρ_{XB} ≡ ∑ₓ p_X(x)|x⟩⟨x|_X ⊗ N_{A→B}(ρˣ_A)`.

**Formalization Note.** Supremum `⨆` over all classical–quantum inputs with a finite alphabet
`Fin k` of any size (`CQInput`). The values are bounded above (`I(X; B) ≤ H(B) ≤ log₂ |b|`), so
`⨆` is the least upper bound, which the book's maximum attains. Empty input space: `⨆ = 0`. -/
noncomputable def holevoInfoChannel {a b : Type} [Fintype a] [Fintype b] [DecidableEq a]
    [DecidableEq b] (N : QChannel a b) : ℝ :=
  ⨆ ρ : CQInput a, DattaDiscord.mutualInfo (cqState ρ.p.prob fun x => N.apply (ρ.ρ x))

end WildeQIT.Degradable


