-- Prove2me | Definitions.Def_WildeQIT_Activation_privateInfoEnsemble
-- name    : WildeQIT_Activation_privateInfoEnsemble
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T19:12:15.530703+00:00
-- url     : https://prove2.me/theorems/bc0735e1-84ff-4277-9fae-d9078844969d
-- title:
--   Private information of an ensemble $I(X;B)_\rho-I(X;E)_\rho$
-- statement:
--   For an ensemble $\{p_X(x),\rho^x_A\}$ and a channel $\mathcal N_{A\to B}$ with isometric extension $U^{\mathcal N}_{A\to BE}$, let
--
--   $$
--   \rho_{XBE}\equiv\sum_x p_X(x)\,|x\rangle\langle x|_X\otimes U^{\mathcal N}(\rho^x_A).
--   $$
--
--   The **private information of the ensemble** is $I(X;B)_\rho-I(X;E)_\rho$, the classical correlation the sender establishes with the receiver less the correlation the environment obtains. It is the right-hand side of (24.163), up to the factor $\tfrac12$.
--
--   **Formalization Note** The reduced states of $\rho_{XBE}$ on $XB$ and $XE$ are the classical–quantum states $\sum_xp_X(x)|x\rangle\langle x|\otimes\mathcal N(\rho^x)$ and $\sum_xp_X(x)|x\rangle\langle x|\otimes\mathcal N^c(\rho^x)$, which is how they are computed. Any isometric extension gives the same value.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 24.8.1, eqs. (24.163) and (24.165), p. 684

import Definitions.Def_WildeQIT_Degradable_CQInput
import Definitions.Def_WildeQIT_Degradable_cqState
import Definitions.Def_WildeQIT_AFW_qMutualInfo
import Definitions.Def_WildeQIT_Degradable_complementaryApply

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Theorem 24.8.1, p. 684, eqs. (24.163) and (24.165) (`I(X; B2)_ρ − I(X; E2)_ρ`).
-/

namespace WildeQIT.Activation

open Classical in
/-- **Private information of an ensemble** (Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, (24.163), (24.165), p. 684): for an ensemble
`{p_X(x), ρˣ_{A}}` and a channel `N_{A→B}` with isometric extension `U^N_{A→BE}`, the quantity
`I(X; B)_ρ − I(X; E)_ρ` evaluated on `ρ_{XBE} ≡ ∑ₓ p_X(x)|x⟩⟨x|_X ⊗ U^N(ρˣ)`.

**Formalization Note.** The reduced states of `ρ_{XBE}` on `XB` and `XE` are the
classical–quantum states `∑ₓ p_X(x)|x⟩⟨x| ⊗ N(ρˣ)` and `∑ₓ p_X(x)|x⟩⟨x| ⊗ N^c(ρˣ)`, with
`N^c` the complementary channel of the canonical isometric extension (environment `N.ι`); any
other isometric extension gives the same entropies. Decidable equality on the environment index
is classical. -/
noncomputable def privateInfoEnsemble {a b : Type} [Fintype a] [Fintype b] [DecidableEq a]
    [DecidableEq b] (N : QChannel a b) (E : WildeQIT.Degradable.CQInput a) : ℝ :=
  WildeQIT.AFW.qMutualInfo (WildeQIT.Degradable.cqState E.p.prob fun x => N.apply (E.ρ x)) -
    WildeQIT.AFW.qMutualInfo (WildeQIT.Degradable.cqState E.p.prob fun x => WildeQIT.Degradable.complementaryApply N (E.ρ x))

end WildeQIT.Activation


