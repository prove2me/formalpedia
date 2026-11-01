-- Prove2me | Definitions.Def_WildeQIT_ErasureClassical_holevoInfoMixed
-- name    : WildeQIT_ErasureClassical_holevoInfoMixed
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T18:36:50.398884+00:00
-- url     : https://prove2.me/theorems/6b5b3d30-1a1b-4908-a520-876abdd739cd
-- title:
--   Holevo information $\chi(\mathcal N)$ of a channel (Definition 13.3.1)
-- statement:
--   **Definition 13.3.1.** Let $\mathcal N_{A\to B}$ be a quantum channel. Its Holevo information is
--
--   $$
--   \chi(\mathcal N)\equiv\max_{\rho_{XA}} I(X;B)_\rho ,
--   $$
--
--   where the maximization is over all classical–quantum inputs $\rho_{XA}=\sum_x p_X(x)|x\rangle\langle x|_X\otimes\rho^x_A$ with arbitrary (mixed) states $\rho^x$, and $\rho_{XB}=\sum_x p_X(x)|x\rangle\langle x|_X\otimes\mathcal N_{A\to B}(\rho^x_A)$.
--
--   Theorem 13.3.2 shows that restricting to pure states $\rho^x$ gives the same value, which is the form (20.8) used in Chapter 20.
--
--   **Formalization Note** $I(X;B)$ is the published `HolevoCQ.holevoChi`. Supremum over all finite ensembles of density operators; the values are bounded above by $\log_2\dim\mathcal H_B$. Logarithms are base 2.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Definition 13.3.1, (13.82)–(13.84), pp. 400–401

import Definitions.Def_HolevoCQ_holevoChi
import Definitions.Def_WildeQIT_ErasureClassical_MixedEnsemble
import Definitions.Def_WildeQIT_QChannel

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Definition 13.3.1, p. 401,
eq. (13.84) (Holevo information of a channel, maximized over mixed-state ensembles).
-/

namespace WildeQIT.ErasureClassical

/-- **Definition 13.3.1 (Holevo Information of a Quantum Channel)** (Wilde, *From Classical to
Quantum Shannon Theory*, arXiv:1106.1445v8, p. 401, (13.84)): `χ(N) ≡ max_{ρ_{XA}} I(X; B)_ρ`,
"where the maximization is with respect to all input classical–quantum states of the form in
(13.82) and `I(X; B)_ρ` is evaluated with respect to the state in (13.83)",
`ρ_{XB} ≡ ∑ₓ p_X(x)|x⟩⟨x|_X ⊗ N_{A→B}(ρˣ_A)`, with arbitrary (mixed) `ρˣ`.

**Formalization Note.** Supremum `⨆` over all ensembles of density operators on a finite
alphabet `Fin k` of any size (`MixedEnsemble`), of `I(X; B)` (the published `HolevoCQ.holevoChi`), in bits. The values are
bounded above by `log₂ |B|`, so `⨆` is the least upper bound. This is the book's first
definition; (20.8) (`holevoInfo`) restricts to pure states, and Theorem 13.3.2 says the two
coincide. -/
noncomputable def holevoInfoMixed {a b : Type} [Fintype a] [Fintype b] [DecidableEq a]
    [DecidableEq b] (N : QChannel a b) : ℝ :=
  ⨆ e : MixedEnsemble a, HolevoCQ.holevoChi (fun x => N.apply (e.ρ x)) e.p.prob

end WildeQIT.ErasureClassical


