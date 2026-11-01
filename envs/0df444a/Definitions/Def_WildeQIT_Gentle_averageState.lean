-- Prove2me | Definitions.Def_WildeQIT_Gentle_averageState
-- name    : WildeQIT_Gentle_averageState
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:56:06.889969+00:00
-- url     : https://prove2.me/theorems/ce9d3428-192c-4ae1-9e52-de02bf296bd3
-- title:
--   Average density operator $\rho=\sum_x p_X(x)\rho_x$ of an ensemble
-- statement:
--   Let $\{p_X(x),\rho_x\}$ be an ensemble: a probability distribution $p_X$ on a finite alphabet $\mathcal X$ together with a family of operators $\rho_x$, $x\in\mathcal X$. Its **average density operator** is
--
--   $$\rho\equiv\sum_{x\in\mathcal X}p_X(x)\,\rho_x .$$
--
--   It is the state whose detection probability $\operatorname{Tr}\{\rho\Lambda\}$ controls the gentle measurement lemma for ensembles (Lemma 9.4.3).
--
--   **Formalization Note** The distribution is the published `WildeQIT.FinDist`; statements using this definition assume each $\rho_x$ is a density operator.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Lemma 9.4.3, p. 279

import Definitions.Def_WildeQIT_FinDist
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Complex.Basic

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Lemma 9.4.3, p. 279
(the average density operator of an ensemble; cf. §4.1.2).
-/

open Matrix

namespace WildeQIT.Gentle

/-- **Average density operator of an ensemble** (Wilde, arXiv:1106.1445v8, Lemma 9.4.3, p. 279).
For an ensemble `{p_X(x), ρ_x}` over a finite alphabet `𝒳`, `ρ ≡ ∑_x p_X(x) ρ_x`.

**Formalization Note.** The distribution `p_X` is the published `WildeQIT.FinDist` (non-negative
weights summing to one on a finite alphabet); the states `ρ_x` are a family of matrices, and the
statements that use this definition assume each `ρ_x` is a density operator. -/
noncomputable def averageState {X n : Type} [Fintype X] (p : FinDist X)
    (ρ : X → Matrix n n ℂ) : Matrix n n ℂ :=
  ∑ x, ((p.prob x : ℝ) : ℂ) • ρ x

end WildeQIT.Gentle


