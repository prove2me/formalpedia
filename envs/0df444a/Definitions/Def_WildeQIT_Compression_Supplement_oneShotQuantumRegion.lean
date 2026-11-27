-- Prove2me | Definitions.Def_WildeQIT_Compression_Supplement_oneShotQuantumRegion
-- name    : WildeQIT_Compression_Supplement_oneShotQuantumRegion
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T04:09:31.50079+00:00
-- url     : https://prove2.me/theorems/72e13cd1-a2da-55d7-ac3d-3e053dbae8c7
-- title:
--   One-shot quantum region $\mathcal C^{(1)}_Q(\mathcal N)$
-- statement:
--   The one-shot quantum region is the union over states $\sigma$ with a degenerate distribution $p_X$ (a point mass) of the regions $\mathcal C^{(1)}_{Q,\sigma}(\mathcal N)$ of all $Q\ge0$ with
--
--   $$
--   Q\le I(A\rangle BX)_\sigma .
--   $$
--
--   Here $\sigma_{XAB}=\sum_xp_X(x)|x\rangle\langle x|_X\otimes\mathcal N_{A'\to B}(\varphi^x_{AA'})$ is a classical–quantum state with pure $\varphi^x_{AA'}$ (25.11), the union ranges over all such states, and the entropic quantities are in bits.
--
--   **Formalization Note** A state $\sigma$ of (25.11) is a finite pure ensemble with a reference of any finite dimension (`DynamicPureEnsemble` of the published `Claimed50.P20`), and `bounds N e` is the triple $(I(AX;B)_\sigma,\ I(A\rangle BX)_\sigma,\ I(X;B)_\sigma+I(A\rangle BX)_\sigma)$.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 25.2.3, p. 699, eq. (25.20)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P20

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Theorem 25.2.3, p. 699, (25.20).
-/

namespace WildeQIT.Compression.Supplement

open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P20

/-- **One-shot quantum region `C^(1)_Q(N)`** (Wilde, *From Classical to Quantum Shannon Theory*,
arXiv:1106.1445v8, Theorem 25.2.3, p. 699): the union of the regions `C^(1)_{Q,σ}(N)`, "the set of
all `Q ≥ 0`, such that `Q ≤ I(A⟩BX)_σ` (25.20). The entropic quantity is with respect to the state
`σ_{XAB}` in (25.11) with the restriction that the density `p_X(x)` is degenerate."

**Formalization Note.** A state `σ_{XAB}` of (25.11) is given by a finite ensemble of pure
states `φˣ_{AA′}` with a reference `A` of any finite dimension (`DynamicPureEnsemble` of the
published `Claimed50.P20`); `bounds N e` is the triple `(I(AX;B)_σ, I(A⟩BX)_σ,
I(X;B)_σ + I(A⟩BX)_σ)` of (25.8)–(25.10) for that state, in bits. A degenerate density is a point mass: some letter has probability one. -/
def oneShotQuantumRegion {A B : Type} [Fintype A] [Fintype B] [DecidableEq B]
    (N : Superop A B) : Set ℝ :=
  {Q | 0 ≤ Q ∧ ∃ e : DynamicPureEnsemble A, (∃ x, e.ensemble.prob x = 1) ∧ Q ≤ bounds N e 1}

end WildeQIT.Compression.Supplement


