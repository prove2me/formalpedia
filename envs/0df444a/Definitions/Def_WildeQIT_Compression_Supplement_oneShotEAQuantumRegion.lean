-- Prove2me | Definitions.Def_WildeQIT_Compression_Supplement_oneShotEAQuantumRegion
-- name    : WildeQIT_Compression_Supplement_oneShotEAQuantumRegion
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T04:10:13.581189+00:00
-- url     : https://prove2.me/theorems/7f919446-74d9-4ba9-b900-5ec4ee7641f4
-- title:
--   One-shot entanglement-assisted quantum region $\mathcal C^{(1)}_{QE}(\mathcal N)$
-- statement:
--   The one-shot entanglement-assisted quantum region is the union over states $\sigma$ with a degenerate distribution $p_X$ (a point mass) of the regions $\mathcal C^{(1)}_{QE,\sigma}(\mathcal N)$ of all $Q,E\ge0$ with
--
--   $$
--   2Q\le I(AX;B)_\sigma,\qquad Q\le I(A\rangle BX)_\sigma+|E| .
--   $$
--
--   Here $\sigma_{XAB}=\sum_xp_X(x)|x\rangle\langle x|_X\otimes\mathcal N_{A'\to B}(\varphi^x_{AA'})$ is a classical–quantum state with pure $\varphi^x_{AA'}$ (25.11), the union ranges over all such states, and the entropic quantities are in bits.
--
--   **Formalization Note** A state $\sigma$ of (25.11) is a finite pure ensemble with a reference of any finite dimension (`DynamicPureEnsemble` of the published `Claimed50.P20`), and `bounds N e` is the triple $(I(AX;B)_\sigma,\ I(A\rangle BX)_\sigma,\ I(X;B)_\sigma+I(A\rangle BX)_\sigma)$.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 25.2.4, p. 699, eqs. (25.22)–(25.23)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P20

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Theorem 25.2.4, p. 699, (25.22)–(25.23).
-/

namespace WildeQIT.Compression.Supplement

open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P20

/-- **One-shot entanglement-assisted quantum region `C^(1)_QE(N)`** (Wilde, *From Classical to
Quantum Shannon Theory*, arXiv:1106.1445v8, Theorem 25.2.4, p. 699): the union of the regions
`C^(1)_{QE,σ}(N)`, "the set of all `Q, E ≥ 0`, such that `2Q ≤ I(AX;B)_σ` (25.22),
`Q ≤ I(A⟩BX)_σ + |E|` (25.23). The entropic quantities are with respect to the state `σ_{XAB}` in
(25.11) with the restriction that the density `p_X(x)` is degenerate."

**Formalization Note.** A state `σ_{XAB}` of (25.11) is given by a finite ensemble of pure
states `φˣ_{AA′}` with a reference `A` of any finite dimension (`DynamicPureEnsemble` of the
published `Claimed50.P20`); `bounds N e` is the triple `(I(AX;B)_σ, I(A⟩BX)_σ,
I(X;B)_σ + I(A⟩BX)_σ)` of (25.8)–(25.10) for that state, in bits. A degenerate density is a point mass: some letter has probability one. Pairs are `(Q, E)`. -/
def oneShotEAQuantumRegion {A B : Type} [Fintype A] [Fintype B] [DecidableEq B]
    (N : Superop A B) : Set (ℝ × ℝ) :=
  {x | 0 ≤ x.1 ∧ 0 ≤ x.2 ∧ ∃ e : DynamicPureEnsemble A, (∃ y, e.ensemble.prob y = 1) ∧
    2 * x.1 ≤ bounds N e 0 ∧ x.1 ≤ bounds N e 1 + |x.2|}

end WildeQIT.Compression.Supplement


