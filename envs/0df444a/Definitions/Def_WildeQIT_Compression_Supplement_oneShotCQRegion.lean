-- Prove2me | Definitions.Def_WildeQIT_Compression_Supplement_oneShotCQRegion
-- name    : WildeQIT_Compression_Supplement_oneShotCQRegion
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T04:10:51.082431+00:00
-- url     : https://prove2.me/theorems/914c91f1-7c43-526d-93fb-2c4268b1a421
-- title:
--   One-shot classically enhanced quantum region $\mathcal C^{(1)}_{CQ}(\mathcal N)$
-- statement:
--   The one-shot classically enhanced quantum region is the union over states $\sigma$ of the regions $\mathcal C^{(1)}_{CQ,\sigma}(\mathcal N)$ of all $C,Q\ge0$ with
--
--   $$
--   C+Q\le I(X;B)_\sigma+I(A\rangle BX)_\sigma,\qquad Q\le I(A\rangle BX)_\sigma .
--   $$
--
--   Here $\sigma_{XAB}=\sum_xp_X(x)|x\rangle\langle x|_X\otimes\mathcal N_{A'\to B}(\varphi^x_{AA'})$ is a classical–quantum state with pure $\varphi^x_{AA'}$ (25.11), the union ranges over all such states, and the entropic quantities are in bits.
--
--   **Formalization Note** A state $\sigma$ of (25.11) is a finite pure ensemble with a reference of any finite dimension (`DynamicPureEnsemble` of the published `Claimed50.P20`), and `bounds N e` is the triple $(I(AX;B)_\sigma,\ I(A\rangle BX)_\sigma,\ I(X;B)_\sigma+I(A\rangle BX)_\sigma)$.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 25.2.5, p. 700, eqs. (25.25)–(25.26)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P20

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Theorem 25.2.5, p. 700, (25.25)–(25.26).
-/

namespace WildeQIT.Compression.Supplement

open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P20

/-- **One-shot classically enhanced quantum region `C^(1)_CQ(N)`** (Wilde, *From Classical to
Quantum Shannon Theory*, arXiv:1106.1445v8, Theorem 25.2.5, p. 700): the union of the regions
`C^(1)_{CQ,σ}(N)`, "the set of all `C, Q ≥ 0`, such that `C + Q ≤ I(X;B)_σ + I(A⟩BX)_σ` (25.25),
`Q ≤ I(A⟩BX)_σ` (25.26). The entropic quantities are with respect to the state `σ_{XAB}` in
(25.11)."

**Formalization Note.** A state `σ_{XAB}` of (25.11) is given by a finite ensemble of pure
states `φˣ_{AA′}` with a reference `A` of any finite dimension (`DynamicPureEnsemble` of the
published `Claimed50.P20`); `bounds N e` is the triple `(I(AX;B)_σ, I(A⟩BX)_σ,
I(X;B)_σ + I(A⟩BX)_σ)` of (25.8)–(25.10) for that state, in bits. Pairs are `(C, Q)`. -/
def oneShotCQRegion {A B : Type} [Fintype A] [Fintype B] [DecidableEq B]
    (N : Superop A B) : Set (ℝ × ℝ) :=
  {x | 0 ≤ x.1 ∧ 0 ≤ x.2 ∧ ∃ e : DynamicPureEnsemble A,
    x.1 + x.2 ≤ bounds N e 2 ∧ x.2 ≤ bounds N e 1}

end WildeQIT.Compression.Supplement


