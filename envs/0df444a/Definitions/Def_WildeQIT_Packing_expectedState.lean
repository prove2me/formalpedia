-- Prove2me | Definitions.Def_WildeQIT_Packing_expectedState
-- name    : WildeQIT_Packing_expectedState
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:56:07.050355+00:00
-- url     : https://prove2.me/theorems/61a80991-d49d-49ff-8580-70e9854751f7
-- title:
--   Expected density operator $\sigma=\sum_x p_X(x)\sigma_x$ of an ensemble
-- statement:
--   Let $\mathcal X$ be a finite alphabet, $p_X$ a probability distribution on $\mathcal X$, and $\{p_X(x),\sigma_x\}_{x\in\mathcal X}$ an ensemble of quantum states $\sigma_x\in\mathcal D(\mathcal H)$ (Definition 16.2.1). The **expected density operator** of the ensemble is
--
--   $$\sigma\equiv\sum_{x\in\mathcal X}p_X(x)\,\sigma_x .$$
--
--   It is the operator in the fourth condition $\Pi\sigma\Pi\le\frac1D\Pi$ of the packing lemma.
--
--   **Formalization Note** The distribution is the published `WildeQIT.FinDist`; the states are complex matrices on a finite-dimensional space. Statements using this definition assume each $\sigma_x$ is a density operator.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Definition 16.2.1, eq. (16.2), p. 487

import Mathlib.Analysis.Complex.Basic
import Definitions.Def_WildeQIT_FinDist
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Complex.Basic

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Definition 16.2.1
(Ensemble), eq. (16.2), p. 487.
-/

open Matrix
open scoped ComplexOrder

namespace WildeQIT.Packing

/-- **Expected density operator of an ensemble** (Wilde, arXiv:1106.1445v8, Definition 16.2.1,
eq. (16.2), p. 487). For an ensemble `{p_X(x), σ_x}_{x ∈ 𝒳}` on a finite alphabet `𝒳`,
`σ ≡ ∑_{x ∈ 𝒳} p_X(x) σ_x`.

**Formalization Note.** The distribution `p_X` is the published `WildeQIT.FinDist`; the states
`σ_x` are a family of matrices on a finite-dimensional Hilbert space (basis indexed by `n`).
Statements that use this definition assume each `σ_x` is a density operator, as Definition 16.2.1
does. -/
noncomputable def expectedState {X n : Type} [Fintype X] (p : FinDist X)
    (σ : X → Matrix n n ℂ) : Matrix n n ℂ :=
  ∑ x, ((p.prob x : ℝ) : ℂ) • σ x

end WildeQIT.Packing


