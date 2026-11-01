-- Prove2me | Definitions.Def_WildeQIT_ErasureClassical_holevoInfo
-- name    : WildeQIT_ErasureClassical_holevoInfo
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T18:36:54.258205+00:00
-- url     : https://prove2.me/theorems/257ae98a-fe9d-493a-aa2b-b6aa996af6c9
-- title:
--   Holevo information $\chi(\mathcal N)$ of a channel (pure-state inputs, (20.8))
-- statement:
--   Let $\mathcal N_{A'\to B}$ be a quantum channel. Its **Holevo information** is
--
--   $$
--   \chi(\mathcal N)\equiv\max_\rho I(X;B)_\rho ,
--   $$
--
--   where the maximization is over classical–quantum states $\rho_{XB}=\sum_x p_X(x)|x\rangle\langle x|_X\otimes\mathcal N_{A'\to B}(\psi^x_{A'})$ with pure states $\psi^x$ and a finite alphabet of any size.
--
--   The regularization $\chi_{\rm reg}(\mathcal N)=\lim_k\frac1k\chi(\mathcal N^{\otimes k})$ is the classical capacity (Theorem 20.3.1).
--
--   **Formalization Note** $I(X;B)=H(\sum_xp_X(x)\sigma^x)-\sum_xp_X(x)H(\sigma^x)$ is the published `HolevoCQ.holevoChi` with the base-2 von Neumann entropy. The maximum is written as a supremum over all pure-state ensembles; the values are bounded above by $\log_2\dim\mathcal H_B$ and the family is nonempty when the input space is, so the supremum is the least upper bound. That it is attained is part of Theorem 13.3.2. Logarithms are base 2.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, §20.1, (20.8)–(20.9), p. 561

import Definitions.Def_HolevoCQ_holevoChi
import Definitions.Def_WildeQIT_ErasureClassical_PureEnsemble
import Definitions.Def_WildeQIT_QChannel

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §20.1, p. 561,
eqs. (20.8)–(20.9) (the Holevo information `χ(N)` of a channel).
-/

namespace WildeQIT.ErasureClassical

/-- **Holevo information of a channel** `χ(N) ≡ max_ρ I(X; B)` (Wilde, *From Classical to
Quantum Shannon Theory*, arXiv:1106.1445v8, (20.8), p. 561), "where the maximization is with
respect to classical–quantum states `ρ_{XB}` of the following form:
`ρ_{XB} ≡ ∑ₓ p_X(x)|x⟩⟨x|_X ⊗ N_{A′→B}(ψˣ_{A′})`" (20.9), with pure `ψˣ`.

**Formalization Note.** Supremum `⨆` over all pure-state ensembles on a finite alphabet `Fin k`
of any size (`PureEnsemble`), of `I(X; B) = H(∑ₓ p(x) N(ψˣ)) − ∑ₓ p(x) H(N(ψˣ))`
(the published `HolevoCQ.holevoChi`, `H(∑ₓ p(x)σˣ) − ∑ₓ p(x)H(σˣ)` with the base-2 von Neumann entropy), in bits. The values are bounded above (`I(X; B) ≤ log₂ |B|`) and the index
type is nonempty when the input space is, so `⨆` is the least upper bound, the book's maximum
(attainment is Theorem 13.3.2 of this mission). When the input index type is empty there is no
ensemble and `⨆ = 0`; no statement of this mission uses that case. -/
noncomputable def holevoInfo {a b : Type} [Fintype a] [Fintype b] [DecidableEq a]
    [DecidableEq b] (N : QChannel a b) : ℝ :=
  ⨆ e : PureEnsemble a, HolevoCQ.holevoChi (fun x => N.apply (e.state x)) e.p.prob

end WildeQIT.ErasureClassical


