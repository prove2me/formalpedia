-- Prove2me | Definitions.Def_WildeQIT_Degradable_privateInfoChannel
-- name    : WildeQIT_Degradable_privateInfoChannel
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:57:54.480965+00:00
-- url     : https://prove2.me/theorems/7edd0b50-e089-4c2a-a9ec-70693515d9ae
-- title:
--   Private information of a quantum channel $P(\mathcal N)$ (Definition 13.6.1)
-- statement:
--   The **private information** of a quantum channel $\mathcal N_{A'\to B}$ is
--
--   $$
--   P(\mathcal N) \equiv \max_{\rho_{XA'}}\ I(X;B)_\rho - I(X;E)_\rho ,
--   $$
--
--   where the maximization is over all classical–quantum inputs $\rho_{XA'}=\sum_x p_X(x)|x\rangle\langle x|_X\otimes\rho^x_{A'}$ and the entropic quantities are evaluated on $U^{\mathcal N}_{A'\to BE}(\rho_{XA'})$, the output of an isometric extension of the channel. It measures the classical correlations Alice can establish with Bob that are hidden from the environment.
--
--   **Formalization Note** The reduced states of $U^{\mathcal N}(\rho_{XA'})$ on $XB$ and $XE$ are $\sum_x p_X(x)|x\rangle\langle x|\otimes\mathcal N(\rho^x)$ and $\sum_x p_X(x)|x\rangle\langle x|\otimes\mathcal N^c(\rho^x)$, with the canonical isometric extension (environment `N.ι`); another isometric extension gives the same entropies. The maximum is the real supremum over `CQInput` (alphabets `Fin k`, any `k`); the values are at most $\log_2|B|$, so it is the supremum of a nonempty bounded set and equals the attained maximum.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Definition 13.6.1, eqs. (13.178)–(13.179), p. 416

import Definitions.Def_WildeQIT_Degradable_cqState
import Definitions.Def_DattaDiscord_mutualInfo
import Definitions.Def_WildeQIT_Degradable_CQInput
import Definitions.Def_WildeQIT_Degradable_complementaryApply

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Definition 13.6.1 (Private Information of a Quantum Channel), p. 416.
-/

namespace WildeQIT.Degradable

open Classical in
/-- **Definition 13.6.1 (Private Information of a Quantum Channel)** (Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, p. 416,
eq. (13.179)): `P(N) ≡ max_{ρ_{XA′}} I(X; B)_ρ − I(X; E)_ρ`, "where the maximization is with
respect to all states of the form in (13.178) and the entropic quantities are evaluated with
respect to the state `U^N_{A′→BE}(ρ_{XA′})`".

**Formalization Note.** The reduced states of `U^N(ρ_{XA′})` on `XB` and `XE` are the
classical–quantum states `∑ₓ p_X(x)|x⟩⟨x| ⊗ N(ρˣ)` and `∑ₓ p_X(x)|x⟩⟨x| ⊗ N^c(ρˣ)`, with `U^N`
the canonical isometric extension (environment `N.ι`); any other isometric extension gives the
same entropies. Supremum `⨆` over all classical–quantum inputs with a finite alphabet `Fin k` of
any size (`CQInput`); the values are bounded above by `log₂ |b|`, so `⨆` is the least upper
bound, which the book's maximum attains. Empty input space: `⨆ = 0`. Decidable equality on the
environment index is classical. -/
noncomputable def privateInfoChannel {a b : Type} [Fintype a] [Fintype b] [DecidableEq a]
    [DecidableEq b] (N : QChannel a b) : ℝ :=
  ⨆ ρ : CQInput a, (DattaDiscord.mutualInfo (cqState ρ.p.prob fun x => N.apply (ρ.ρ x)) -
    DattaDiscord.mutualInfo (cqState ρ.p.prob fun x => complementaryApply N (ρ.ρ x)))

end WildeQIT.Degradable


