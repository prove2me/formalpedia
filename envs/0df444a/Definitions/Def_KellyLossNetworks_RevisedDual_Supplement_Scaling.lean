-- Prove2me | Definitions.Def_KellyLossNetworks_RevisedDual_Supplement_Scaling
-- name    : KellyLossNetworks_RevisedDual_Supplement_Scaling
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T02:55:06.205345+00:00
-- url     : https://prove2.me/theorems/c4cb915b-9c94-4bec-afc5-a1f8f398784c
-- title:
--   Limiting-regime objects of §2: maximal-support B, critical links 𝒪, B(N), the conditioned normal mean and b(N)
-- statement:
--   Fix limiting rates $\nu_r>0$ and limiting capacities $C_j\ge0$. The conditions (2.7) on $B=(B_1,\dots,B_J)\in[0,1)^J$ read
--   $$\sum_r A_{jr}\nu_r\prod_i(1-B_i)^{A_{ir}}\ \begin{cases}=C_j,& B_j>0,\\ \le C_j,& B_j=0.\end{cases}$$
--   A solution $B$ is **of maximal support** if every solution $B'$ satisfies $B'_j>0\Rightarrow B_j>0$. Its support $\mathcal B=\{j:B_j>0\}$ is the set of busy links. With $x_r=\nu_r\prod_j(1-B_j)^{A_{jr}}$ and slack $z=C-Ax$, the **critically loaded links** are $\mathcal O=\{j\notin\mathcal B: z_j=0\}$.
--
--   For the $N$-th network with rates $\nu_r(N)$ and capacities $C_j(N)$, $B(N)$ solves (2.7) with $\nu_r(N)$ in place of $\nu_r$, capacity $C_j(N)$ for $j\in\mathcal B$ and infinite capacity for $j\notin\mathcal B$; then $x_r(N)=\nu_r(N)\prod_j(1-B_j(N))^{A_{jr}}$.
--
--   Let $u$ be the random vector obtained from independent $u_r\sim N(0,x_r)$ by conditioning on $A_{\mathcal B}u=0$ and $A_{\mathcal O}u\le\alpha_{\mathcal O}$. Its mean $\mathbb E u_r$ is defined here as
--   $$\mathbb E u_r=\frac{\int_{K} u_r\,e^{-\sum_s u_s^2/(2x_s)}\,d\lambda(u)}{\int_{K} e^{-\sum_s u_s^2/(2x_s)}\,d\lambda(u)},\qquad K=\{u\in\ker A_{\mathcal B}: A_{\mathcal O}u\le \alpha_{\mathcal O}\},$$
--   where $\lambda$ is Lebesgue (Haar) measure on the subspace $\ker A_{\mathcal B}$. Finally, given $\beta\in\mathbb R^J$,
--   $$b_j(N)=B_j(N)-N^{-1/2}\beta_j\big(1-B_j(N)\big).$$
--
--   These are the objects in terms of which Theorems 2.30 and 3.12 are stated.
--
--   **Formalization Note** (2.7) is the published `KellyStochasticNetworks.LossLimits.blockingConditions`, which allows real capacities. Infinite capacity on a link is encoded as $B_j(N)=0$, the only value (2.7) then allows. The conditioning on the null event $A_{\mathcal B}u=0$ uses the canonical law on the subspace; the ratio does not depend on the normalization of the Haar measure, and rank-deficient $A_{\mathcal B}$ is allowed. If the denominator vanishes the value is $0$.
-- source:
--   Kelly, Loss networks, Ann. Appl. Probab. 1(3):319–378 (1991), DOI 10.1214/aoap/1177005872, pp. 329–331, §§2.1–2.2 (maximal support, ℬ, 𝒪, B(N), x(N), the conditioned vector u); p. 332 (Σ = diag(x_r)); p. 334, (2.29) and b_j(N)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_LossLimits_Optimization

open MeasureTheory

namespace KellyLossNetworks.RevisedDual.Supplement

/-- **A solution of maximal support** of the conditions (2.7) on `B` for the limiting rates `ν`
and (real) limiting capacities `C`: `B` solves (2.7) and every solution `B'` of (2.7) has
`B'_j > 0 ⇒ B_j > 0`. The conditions (2.7) are the published predicate
`KellyStochasticNetworks.LossLimits.blockingConditions`.

Kelly, Loss networks, Ann. Appl. Probab. 1(3):319–378 (1991), DOI 10.1214/aoap/1177005872,
p. 329 (end of §2.1) and p. 330, §2.2 ("a solution of maximal support to the conditions (2.7)").

**Formalization Note.** `blockingConditions A ν C B` is `B_j ∈ [0, 1)`,
`Σ_r A_jr ν_r ∏_i (1 − B_i)^{A_ir} ≤ C_j`, with equality when `B_j > 0`: exactly (2.7). Its
support `ℬ = {j : B_j > 0}` is the set of busy links. -/
def IsMaxSupportSolution {J R : ℕ} (A : Fin J → Fin R → ℕ) (ν : Fin R → ℝ)
    (C B : Fin J → ℝ) : Prop :=
  KellyStochasticNetworks.LossLimits.blockingConditions A ν C B ∧
    ∀ B' : Fin J → ℝ, KellyStochasticNetworks.LossLimits.blockingConditions A ν C B' →
      ∀ j, 0 < B' j → 0 < B j

/-- **The critically loaded links** `𝒪 = {j : z_j = 0, j ∉ ℬ}`, where `z = C − Ax` is the slack
of the primal optimum `x_r = ν_r ∏_j (1 − B_j)^{A_jr}` and `ℬ = {j : B_j > 0}`.

Kelly (1991), p. 330, §2.1. -/
def criticalLinks {J R : ℕ} (A : Fin J → Fin R → ℕ) (ν : Fin R → ℝ) (C B : Fin J → ℝ) :
    Set (Fin J) :=
  {j | B j = 0 ∧
    ∑ r, (A j r : ℝ) * KellyStochasticNetworks.LossLimits.carried A ν B r = C j}

/-- **The conditions defining `B(N)`** (§2.2, p. 330): the conditions (2.7) on `B` with `ν_r`
replaced by `ν_r(N)` and with `C_j` replaced by `C_j(N)` for `j ∈ ℬ` and by infinity for
`j ∉ ℬ`. Here `busy` is the set `ℬ`.

Kelly (1991), p. 330, §2.2.

**Formalization Note.** For a link with infinite capacity the inequality of (2.7) always holds and
its equality case `B_j > 0` is impossible, so such a link has `B_j = 0`; this is how capacity `∞`
is encoded. -/
def CenterConditions {J R : ℕ} (A : Fin J → Fin R → ℕ) (ν' : Fin R → ℝ) (C' : Fin J → ℕ)
    (busy : Set (Fin J)) (B' : Fin J → ℝ) : Prop :=
  (∀ j, 0 ≤ B' j ∧ B' j < 1) ∧
  (∀ j ∈ busy,
    ∑ r, (A j r : ℝ) * KellyStochasticNetworks.LossLimits.carried A ν' B' r ≤ (C' j : ℝ) ∧
    (0 < B' j →
      ∑ r, (A j r : ℝ) * KellyStochasticNetworks.LossLimits.carried A ν' B' r = (C' j : ℝ))) ∧
  (∀ j ∉ busy, B' j = 0)

/-- The subspace `{u ∈ ℝ^ℛ : A_ℬ u = 0}` on which the normal vector of §2.2 is conditioned,
for `ℬ = busy`. Kelly (1991), p. 331, before (2.18). -/
noncomputable def busyKernel {J R : ℕ} (A : Fin J → Fin R → ℕ) (busy : Set (Fin J)) :
    Submodule ℝ (Fin R → ℝ) :=
  LinearMap.ker (Matrix.mulVecLin (Matrix.of fun (j : busy) (r : Fin R) => (A j.1 r : ℝ)))

/-- The (unnormalized) density `exp(−Σ_r u_r² / (2 x_r))` of independent `u_r ∼ N(0, x_r)`,
i.e. of `u ∼ N(0, Σ)` with `Σ = diag(x_r)_r` (p. 332). -/
noncomputable def gaussDensity {R : ℕ} (x u : Fin R → ℝ) : ℝ :=
  Real.exp (-∑ r, u r ^ 2 / (2 * x r))

/-- **The conditional mean `𝔼 u_r`** of the vector `u` of §2.2: independent normal random
variables `u_r ∼ N(0, x_r)` conditioned on `A_ℬ u = 0` and `A_𝒪 u ≤ α_𝒪`.

Kelly (1991), p. 331 (construction before (2.18)) and p. 334, (2.29).

**Formalization Note.** The event `A_ℬ u = 0` is null, so the conditional law is the canonical
one: the Gaussian density restricted to the subspace `busyKernel A busy`, integrated against a
Haar measure on that subspace (any Haar measure; the ratio does not depend on its
normalization), further restricted to the polyhedron `A_𝒪 u ≤ α_𝒪`. The value is
`∫ u_r g(u) dμ / ∫ g(u) dμ` over that polyhedron, with `g = gaussDensity x`; it is `0` if the
denominator vanishes. No general Moore–Penrose machinery is needed, and rank-deficient `A_ℬ`
is allowed. -/
noncomputable def conditionalMean {J R : ℕ} (A : Fin J → Fin R → ℕ) (busy crit : Set (Fin J))
    (x : Fin R → ℝ) (α : Fin J → ℝ) (r : Fin R) : ℝ :=
  open Classical in
  let region : Set (busyKernel A busy) :=
    {v | ∀ j ∈ crit, ∑ s, (A j s : ℝ) * (v : Fin R → ℝ) s ≤ α j}
  (∫ v in region, (v : Fin R → ℝ) r * gaussDensity x (v : Fin R → ℝ) ∂Measure.addHaar) /
    (∫ v in region, gaussDensity x (v : Fin R → ℝ) ∂Measure.addHaar)

/-- **The corrected blocking vector** `b_j(N) = B_j(N) − N^{−1/2} β_j (1 − B_j(N))` of §2.4.

Kelly (1991), p. 334 (after (2.29)). -/
noncomputable def correctedBlocking {J : ℕ} (BN : Fin J → ℝ) (β : Fin J → ℝ) (N : ℕ) :
    Fin J → ℝ :=
  fun j => BN j - (Real.sqrt N)⁻¹ * β j * (1 - BN j)

end KellyLossNetworks.RevisedDual.Supplement


