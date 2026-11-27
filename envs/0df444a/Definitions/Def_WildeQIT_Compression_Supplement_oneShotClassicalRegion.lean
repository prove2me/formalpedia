-- Prove2me | Definitions.Def_WildeQIT_Compression_Supplement_oneShotClassicalRegion
-- name    : WildeQIT_Compression_Supplement_oneShotClassicalRegion
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T04:09:00.28629+00:00
-- url     : https://prove2.me/theorems/1f3ab4f3-7648-500f-95dd-5aabb3bce6fa
-- title:
--   One-shot classical region $\mathcal C^{(1)}_C(\mathcal N)$
-- statement:
--   The one-shot classical region is the union over states $\sigma$ of the regions $\mathcal C^{(1)}_{C,\sigma}(\mathcal N)$ of all $C\ge0$ with
--
--   $$
--   C\le I(X;B)_\sigma+I(A\rangle BX)_\sigma .
--   $$
--
--   Here $\sigma_{XAB}=\sum_xp_X(x)|x\rangle\langle x|_X\otimes\mathcal N_{A'\to B}(\varphi^x_{AA'})$ is a classical–quantum state with pure $\varphi^x_{AA'}$ (25.11), the union ranges over all such states, and the entropic quantities are in bits.
--
--   **Formalization Note** A state $\sigma$ of (25.11) is a finite pure ensemble with a reference of any finite dimension (`DynamicPureEnsemble` of the published `Claimed50.P20`), and `bounds N e` is the triple $(I(AX;B)_\sigma,\ I(A\rangle BX)_\sigma,\ I(X;B)_\sigma+I(A\rangle BX)_\sigma)$.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 25.2.2, p. 698, eq. (25.18)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P20

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Theorem 25.2.2, p. 698, (25.18).
-/

namespace WildeQIT.Compression.Supplement

open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P20

/-- **One-shot classical region `C^(1)_C(N)`** (Wilde, *From Classical to Quantum Shannon Theory*,
arXiv:1106.1445v8, Theorem 25.2.2, p. 698): "The region `C^(1)_C(N)` is the union of the
state-dependent regions `C^(1)_{C,σ}(N)`, where `C^(1)_{C,σ}(N)` is the set of all `C ≥ 0`, such
that `C ≤ I(X;B)_σ + I(A⟩BX)_σ` (25.18). The entropic quantity is with respect to the state
`σ_{XAB}` in (25.11)."

**Formalization Note.** A state `σ_{XAB}` of (25.11) is given by a finite ensemble of pure
states `φˣ_{AA′}` with a reference `A` of any finite dimension (`DynamicPureEnsemble` of the
published `Claimed50.P20`); `bounds N e` is the triple `(I(AX;B)_σ, I(A⟩BX)_σ,
I(X;B)_σ + I(A⟩BX)_σ)` of (25.8)–(25.10) for that state, in bits. -/
def oneShotClassicalRegion {A B : Type} [Fintype A] [Fintype B] [DecidableEq B]
    (N : Superop A B) : Set ℝ :=
  {C | 0 ≤ C ∧ ∃ e : DynamicPureEnsemble A, C ≤ bounds N e 2}

end WildeQIT.Compression.Supplement


