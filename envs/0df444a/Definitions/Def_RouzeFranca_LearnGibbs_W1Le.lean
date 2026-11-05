-- Prove2me | Definitions.Def_RouzeFranca_LearnGibbs_W1Le
-- name    : RouzeFranca_LearnGibbs_W1Le
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:46:54.243447+00:00
-- url     : https://prove2.me/theorems/58000ae4-a3c0-4482-b892-e78bea08a981
-- title:
--   Bound on the Wasserstein distance $W_1(\rho,\sigma)\le w$ induced by a Lipschitz constant
-- statement:
--   Let $\|\cdot\|_{\mathrm{Lip}}$ be a Lipschitz constant on observables. The associated **Wasserstein distance** is
--   $$
--   W_1(\rho,\sigma)=\sup\bigl\{\,|\operatorname{tr}[O(\rho-\sigma)]| \;:\; O=O^\dagger,\ \|O\|_{\mathrm{Lip}}\le1\,\bigr\}.
--   $$
--   The predicate $W_1(\rho,\sigma)\le w$ states that $|\operatorname{tr}[O(\rho-\sigma)]|\le w$ for every Hermitian $O$ with $\|O\|_{\mathrm{Lip}}\le 1$.
--
--   For $\|\cdot\|_{\mathrm{Lip},\square}$ this is $W_{1,\square}$ of Eq. (35), for $\|\cdot\|_{\mathrm{Lip},\nabla}$ it is $W_{1,\nabla}$ of §B.1.2.
--
--   **Formalization Note** The supremum is not formed; only the bound is, so there is no junk value for an unbounded or empty set. The absolute value agrees with the form of (35) without absolute value, because $O$ and $-O$ have the same Lipschitz constant. Traces are recorded by their real parts.
-- source:
--   Rouzé, Stilck França, Learning quantum many-body systems from a few copies, arXiv:2107.03333v4, Eq. (35), p. 22; §B.1.2, p. 23

import Mathlib
import Definitions.Def_RouzeFranca_LearnGibbs_gibbs

open Matrix

namespace RouzeFranca.LearnGibbs

/-- `W1Le lip ρ σ w` says that the Wasserstein distance induced by the Lipschitz constant `lip`
is at most `w`: `W₁(ρ, σ) = sup {|tr[O(ρ − σ)]| : O = O†, ‖O‖_Lip ≤ 1} ≤ w`.

Rouzé, Stilck França, arXiv:2107.03333v4, Eq. (35), p. 22 (`W_{1,□}`), and §B.1.2, p. 23
(`W_{1,∇}(ρ, σ) := sup_{X=X†, ‖X‖_Lip,∇ ≤ 1} |Tr(X(ρ − σ))|`).

**Formalization Note.** The supremum is not formed: the bound is stated for every admissible `O`,
so there is no junk value of a real `sSup` and no `+∞` case. The absolute value matches the
no-absolute-value form of (35) for every absolutely homogeneous `lip`, since `O` and `−O` are
both admissible. The trace is recorded by its real part (real for Hermitian `O` and `ρ − σ`). -/
def W1Le {n : ℕ} (lip : Mat n → ℝ) (ρ σ : Mat n) (w : ℝ) : Prop :=
  ∀ O : Mat n, O.IsHermitian → lip O ≤ 1 → |(trace (O * (ρ - σ))).re| ≤ w

end RouzeFranca.LearnGibbs


