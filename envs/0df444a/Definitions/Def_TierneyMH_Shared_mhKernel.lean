-- Prove2me | Definitions.Def_TierneyMH_Shared_mhKernel
-- name    : TierneyMH_Shared_mhKernel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T11:25:52.819811+00:00
-- url     : https://prove2.me/theorems/c80f45ad-4603-4fb9-a79a-4be0790057fa
-- title:
--   Metropolis–Hastings transition kernel $P(x,dy) = Q(x,dy)\alpha(x,y) + \delta_x(dy)\int(1-\alpha(x,u))Q(x,du)$
-- statement:
--   Let $(E,\mathcal E)$ be a measurable space, let $Q(x,dy)$ be a transition kernel on $E$ (the **proposal kernel**), and let $\alpha : E\times E\to[0,1]$ be a measurable function (the **acceptance probability**). From the current state $x$, a candidate $y$ is drawn from $Q(x,dy)$ and accepted with probability $\alpha(x,y)$; otherwise the chain stays at $x$. The resulting **Metropolis–Hastings transition kernel** is
--
--   $$P(x,dy) = Q(x,dy)\,\alpha(x,y) + \delta_x(dy)\int \bigl(1-\alpha(x,u)\bigr)\,Q(x,du),$$
--
--   where $\delta_x$ is the point mass at $x$. The first term is the accepted moves; the second puts the total rejection probability at the current state.
--
--   This kernel is the object of Theorem 2 and Proposition 5; Theorem 2 characterizes exactly when it satisfies detailed balance with respect to a target distribution $\pi$.
--
--   **Formalization Note** $\alpha$ takes values in $[0,\infty]$ (`ℝ≥0∞`), which avoids casts in `Kernel.withDensity`. Every theorem that uses the kernel assumes that $\alpha$ is measurable and that $\alpha\le1$, which is the paper's "measurable function $E\times E\to[0,1]$". Under these hypotheses the definition is exactly (1): `Kernel.withDensity` returns the zero kernel only for a non-measurable density, and the truncated subtraction $1-\alpha$ in `ℝ≥0∞` agrees with the real one because $\alpha\le 1$. The point mass $\delta_x$ is `Kernel.id x`. The proposal is only required to be an s-finite kernel here; the theorems take it to be a Markov kernel.
--
--   It is shared by two missions of this series and reviewed once for both: `01-reversibility` (Eq. (1), p. 1; the kernel of Theorem 2, p. 3, and of the special cases of §2, pp. 3–4) and `03-mixture-proposals` (Eq. (1), p. 1; the kernel with the maximal acceptance probability $\alpha_{MH}$ of §2, p. 3, the maximal Metropolis–Hastings kernel of §3, p. 7, and the mixtures of Proposition 5, pp. 7–8). In `03-mixture-proposals` it is also applied to the specific acceptance probability $\alpha_{MH}$.
-- source:
--   L. Tierney, A Note on Metropolis–Hastings Kernels for General State Spaces, Ann. Appl. Probab. 8(1) (1998) 1–9, DOI 10.1214/aoap/1027961031, p. 1, §1, Eq. (1)

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace TierneyMH.Shared

/-- The **Metropolis–Hastings transition kernel** (Tierney 1998, Eq. (1), p. 1) built from a
proposal kernel `Q` and an acceptance function `α : E × E → [0, 1]`:
`P(x, dy) = Q(x, dy) α(x, y) + δ_x(dy) ∫ (1 − α(x, u)) Q(x, du)`.

The first summand is `Q` reweighted by the density `y ↦ α (x, y)`; the second is the point mass
`δ_x = Kernel.id x` weighted by the rejection mass `∫⁻ u, (1 - α (x, u)) ∂(Q x)`.

Conventions: `α` takes values in `ℝ≥0∞`, and every theorem using `mhKernel` with a general `α`
assumes `Measurable α` and `∀ p, α p ≤ 1` (the paper's "measurable function
`α : E × E → [0, 1]`").
Under those hypotheses the definition is the paper's kernel: `Kernel.withDensity` returns the
junk value `0` only for a non-measurable density, and the truncated `ℝ≥0∞` subtraction
`1 - α` agrees with the real one because `α ≤ 1`. -/
noncomputable def mhKernel {E : Type*} [MeasurableSpace E] (Q : Kernel E E) [IsSFiniteKernel Q]
    (α : E × E → ℝ≥0∞) : Kernel E E :=
  Q.withDensity (fun x y => α (x, y)) +
    Kernel.withDensity Kernel.id (fun x _ => ∫⁻ u, (1 - α (x, u)) ∂(Q x))

end TierneyMH.Shared


