-- Prove2me | Definitions.Def_LowErrExt_strongBias
-- name    : LowErrExt_strongBias
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:52:30.322391+00:00
-- url     : https://prove2.me/theorems/4b75ea0a-4980-48b0-8af6-eb7bf8440a00
-- title:
--   Strong biases $\mathbb E_{x\sim\mathbf X}|\mathbb E\,\Psi(x,\mathbf Y)|$ and $\mathbb E_{y\sim\mathbf Y}|\mathbb E\,\Psi(\mathbf X,y)|$
-- statement:
--   For a function $\Psi:A\times B\to\mathbb C$ and independent sources $\mathbf X$ on $A$, $\mathbf Y$ on $B$, the module defines the expectation $\mathbb E[\Psi(\mathbf X,\mathbf Y)]$ and the two **strong biases**
--   $$\mathbb E_{x\sim\mathbf X}\big[\,|\mathbb E[\Psi(x,\mathbf Y)]|\,\big],\qquad \mathbb E_{y\sim\mathbf Y}\big[\,|\mathbb E[\Psi(\mathbf X,y)]|\,\big].$$
--   $\Psi$ is strongly $\varepsilon$-biased on $(\mathbf X,\mathbf Y)$ when both are at most $\varepsilon$ (Definition 7.2).
-- source:
--   D. Doron, J. Goodman, Low-Error Extractors, STOC 2027 submission (manuscript sha256 43c922d6…), Definition 7.2, pp.51–52

import Mathlib

namespace LowErrExt

/-- **Expectation of a complex function of an independent pair.** `pairExp X Y Ψ = E[Ψ(X, Y)]`
for independent `X, Y`.
Doron, Goodman, *Low-Error Extractors*, STOC 2027 submission (manuscript sha256 43c922d6…),
Definition 7.2, p.51. -/
noncomputable def pairExp {A B : Type*} (X : PMF A) (Y : PMF B) (Ψ : A → B → ℂ) : ℂ :=
  ∑' x, ∑' y, ((X x).toReal : ℂ) * ((Y y).toReal : ℂ) * Ψ x y

/-- **`E_{x∼X}[|E[Ψ(x, Y)]|]`** (Definition 7.2, p.52, the first strong bias). -/
noncomputable def strongBiasLeft {A B : Type*} (X : PMF A) (Y : PMF B) (Ψ : A → B → ℂ) : ℝ :=
  ∑' x, (X x).toReal * ‖∑' y, ((Y y).toReal : ℂ) * Ψ x y‖

/-- **`E_{y∼Y}[|E[Ψ(X, y)]|]`** (Definition 7.2, p.52, the second strong bias).
Doron, Goodman, *Low-Error Extractors*, STOC 2027 submission (manuscript sha256 43c922d6…),
Definition 7.2, p.52: "We say that Ψ is strongly ε-biased on (X, Y) if the following holds:
E_{y∼Y}[|E[Ψ(X, y)]|] ≤ ε, and E_{x∼X}[|E[Ψ(x, Y)]|] ≤ ε."

**Formalization Note.** Sums are `tsum`s; every type they are used on is finite. -/
noncomputable def strongBiasRight {A B : Type*} (X : PMF A) (Y : PMF B) (Ψ : A → B → ℂ) : ℝ :=
  ∑' y, (Y y).toReal * ‖∑' x, ((X x).toReal : ℂ) * Ψ x y‖

end LowErrExt


