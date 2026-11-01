-- Prove2me | Definitions.Def_WildeQIT_HSW_holevoInfoMixed
-- name    : WildeQIT_HSW_holevoInfoMixed
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T19:12:10.326986+00:00
-- url     : https://prove2.me/theorems/57e7fd9c-3e70-4ca2-a267-3367c60d05dd
-- title:
--   Holevo information of a channel over mixed-state ensembles (Definition 13.3.1)
-- statement:
--   Let $\mathcal N_{A\to B}$ be a quantum channel. Its Holevo information in the sense of Definition 13.3.1 is
--
--   $$
--   \chi(\mathcal N) \equiv \max_{\rho_{XA}} I(X;B)_\rho ,
--   $$
--
--   where the maximization is over all input classical–quantum states $\rho_{XA} \equiv \sum_x p_X(x)|x\rangle\langle x|_X\otimes\rho^x_A$, with $\mathcal X$ an arbitrary finite alphabet, $p_X$ a probability distribution and $\rho^x_A$ arbitrary (mixed) density operators, and $I(X;B)_\rho$ is evaluated on $\rho_{XB} \equiv \sum_x p_X(x)|x\rangle\langle x|_X\otimes\mathcal N_{A\to B}(\rho^x_A)$.
--
--   Theorem 13.3.2 shows that this agrees with the pure-state form (20.8) used in Chapter 20.
--
--   **Formalization Note** As for `WildeQIT.HSW.holevoInfo`, except that the signal states are arbitrary density operators. The alphabet is $\{0,\dots,k-1\}$ for an arbitrary $k$, the basis $|x\rangle$ standard, and the maximum is written as `sSup`.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Definition 13.3.1, (13.82)–(13.84), pp. 400–401

import Mathlib
import Definitions.Def_WildeQIT_FinDist
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_AFW_cqState
import Definitions.Def_WildeQIT_AFW_qMutualInfo

namespace WildeQIT.HSW

/-- Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Definition 13.3.1,
p. 401: the **Holevo information of a quantum channel** over mixed input ensembles,
`χ(N) ≡ max_{ρ_XA} I(X;B)_ρ` (13.84), "where the maximization is with respect to all input
classical–quantum states of the form in (13.82)", `ρ_XA ≡ Σ_x p_X(x)|x⟩⟨x|_X ⊗ ρ^x_A`, and
`I(X;B)_ρ` is evaluated on `ρ_XB ≡ Σ_x p_X(x)|x⟩⟨x|_X ⊗ N_{A→B}(ρ^x_A)` (13.83).

**Formalization Note.** As in `WildeQIT.HSW.holevoInfo` (the pure-state form (20.8)), except
that the signal states `ρ^x_A` are arbitrary density operators (`WildeQIT.IsDensityOperator`).
The alphabet is `Fin k`, the basis `{|x⟩}` standard, the maximum written as `sSup`. -/
noncomputable def holevoInfoMixed {A B : Type} [Fintype A] [Fintype B] [DecidableEq B]
    (Φ : Matrix A A ℂ → Matrix B B ℂ) : ℝ :=
  sSup {r : ℝ | ∃ (k : ℕ) (p : WildeQIT.FinDist (Fin k)) (ρ : Fin k → Matrix A A ℂ),
    (∀ x, WildeQIT.IsDensityOperator (ρ x)) ∧
    r = WildeQIT.AFW.qMutualInfo (WildeQIT.AFW.cqState (1 : Matrix (Fin k) (Fin k) ℂ) p (fun x => Φ (ρ x)))}

end WildeQIT.HSW


