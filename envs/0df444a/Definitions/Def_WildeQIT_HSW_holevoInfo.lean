-- Prove2me | Definitions.Def_WildeQIT_HSW_holevoInfo
-- name    : WildeQIT_HSW_holevoInfo
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T19:12:15.30533+00:00
-- url     : https://prove2.me/theorems/7f08d6d6-74d9-4a5b-862e-97562a03322a
-- title:
--   Holevo information of a channel $\chi(\mathcal N) = \max I(X;B)$ over pure-state ensembles
-- statement:
--   Let $\mathcal N_{A'\to B}$ be a quantum channel. Its Holevo information is
--
--   $$
--   \chi(\mathcal N) \equiv \max_{\rho} I(X;B)_\rho ,
--   $$
--
--   where the maximization is over all classical–quantum states of the form
--
--   $$
--   \rho_{XB} \equiv \sum_x p_X(x)\,|x\rangle\langle x|_X\otimes\mathcal N_{A'\to B}(\psi^x_{A'}),
--   $$
--
--   with $\mathcal X$ an arbitrary finite alphabet, $p_X$ a probability distribution on $\mathcal X$, $\{|x\rangle\}$ an orthonormal basis, and $\psi^x_{A'} = |\psi_x\rangle\langle\psi_x|$ pure states.
--
--   The classical capacity theorem identifies the classical capacity with the regularization $\lim_k \frac1k\chi(\mathcal N^{\otimes k})$.
--
--   **Formalization Note** The definition takes the channel's action on operators as a map (for a `WildeQIT.QChannel` this is `N.apply`; for $\mathcal N^{\otimes k}$ it is `WildeQIT.HSW.tensorPowMap N k`). The alphabet is $\{0,\dots,k-1\}$ for an arbitrary $k$, which loses nothing because mutual information does not depend on the names of the letters; $|x\rangle$ is the standard basis; $|\psi_x\rangle$ are unit vectors. The maximum is written as a supremum (`sSup`); for a channel the set of values is bounded above by $\log_2\dim\mathcal H_B$ and nonempty when the input space is nonempty, and Theorem 13.3.2 states that the supremum is attained.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, (20.8)–(20.9), p. 561

import Mathlib
import Definitions.Def_WildeQIT_FinDist
import Definitions.Def_WildeQIT_AFW_cqState
import Definitions.Def_WildeQIT_AFW_qMutualInfo

open Matrix

namespace WildeQIT.HSW

/-- Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, (20.8)–(20.9), p. 561:
the **Holevo information of a channel**, `χ(N) ≡ max_ρ I(X;B)`, "where the maximization is with
respect to classical–quantum states ρ_XB of the following form:
ρ_XB ≡ Σ_x p_X(x)|x⟩⟨x|_X ⊗ N_{A′→B}(ψ^x_{A′})", with pure input states `ψ^x`.

**Formalization Note.** The map `Φ` is the channel's action on operators (`N.apply` for a
`WildeQIT.QChannel`, `WildeQIT.HSW.tensorPowMap N k` for `N^⊗k`). The classical alphabet is an
arbitrary finite set; it is taken to be `Fin k` for some `k`, which loses nothing because the
mutual information is invariant under relabelling the alphabet. `p_X` is a published
`WildeQIT.FinDist (Fin k)`, `ψ^x = |ψ_x⟩⟨ψ_x|` with `ψ_x` a unit vector, `|x⟩` the standard
basis (`U = 1`), and `I(X;B)` is `WildeQIT.AFW.qMutualInfo`. The maximum is written as `sSup`;
for a channel the set is nonempty (when `A` is nonempty) and bounded above by `log₂ |B|`, so
`sSup` is its least upper bound, and Theorem 13.3.2 states that it is attained. -/
noncomputable def holevoInfo {A B : Type} [Fintype A] [Fintype B] [DecidableEq B]
    (Φ : Matrix A A ℂ → Matrix B B ℂ) : ℝ :=
  sSup {r : ℝ | ∃ (k : ℕ) (p : WildeQIT.FinDist (Fin k)) (ψ : Fin k → A → ℂ),
    (∀ x, star (ψ x) ⬝ᵥ ψ x = 1) ∧
    r = WildeQIT.AFW.qMutualInfo (WildeQIT.AFW.cqState (1 : Matrix (Fin k) (Fin k) ℂ) p
      (fun x => Φ (Matrix.vecMulVec (ψ x) (star (ψ x)))))}

end WildeQIT.HSW


