-- Prove2me | Definitions.Def_RGGDetect_Delta
-- name    : RGGDetect_Delta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:39:00.489147+00:00
-- url     : https://prove2.me/theorems/4aa00b53-0413-4384-9c1b-c961cf88ccae
-- title:
--   The row likelihood: $\Lambda$, $K$, $r^+$, $T^+$ and the truncated $\chi^2$ divergence $\Delta$
-- statement:
--   Let $n'=n-1$, let $x_1,\dots,x_{n'}$ and $z$ be independent and uniform on $S^{d-1}$, $G_{n'}$ the geometric graph of $x_1,\dots,x_{n'}$, and $Y=(\mathbf 1\{\langle z,x_i\rangle\ge\tau\})_{i\le n'}$ the new row (8). Let $Q=\mathrm{Bern}(p)^{\otimes n'}$.
--
--   1. $\Lambda(y)=\mathbb P(Y=y\mid G_{n'})/Q(y)$, the density of $\mathcal L(Y\mid G_{n'})$ relative to $Q$.
--   2. $K=\mathbb E_{G_{n'}}\big[\mathrm{KL}(\mathcal L(Y\mid G_{n'})\,\|\,Q)\big]$.
--   3. For a slack $B^*$, $r^+=\lceil 2np+100\log n\rceil+B^*$ and $T^+=\{y\in\{0,1\}^{n'}:\sum_iy_i\le r^+\}$.
--   4. The **truncated $\chi^2$-divergence** (9) is
--   $$
--   \Delta=\mathbb E_{G_{n'}}\Big[\int_{T^+}(\Lambda-1)^2\,dQ\Big].
--   $$
--
--   Theorem 2 bounds $\mathrm{KL}(P_{\mathrm{RGG}}\|P_{\mathrm{ER}})$ by $n'\Delta+o(1)$, so the main theorem reduces to $\Delta=o(1/n)$.
--
--   **Formalization Note** The slack $B^*$ ("a suitably large constant") is an explicit natural-number parameter. Expectations over $G_{n'}$ are finite sums over the graphs on $n-1$ vertices; graphs of probability $0$ contribute $0$. $p$ is computed from $(d,\tau)$; KL is Mathlib's `klDiv` with values in $[0,\infty]$.
-- source:
--   Du, Mao, Sun, Wu, Xu, Sharp detection thresholds for random geometric graphs with polynomial average degrees, arXiv:2610.08517 (held version, sha256 e7bebd4a…), §2.1, eqs. (8)–(9), p.4 (PDF p.6)

import Mathlib
import Definitions.Def_RGGDetect_rggLaw
import Definitions.Def_RGGDetect_kappa
import Definitions.Def_RGGDetect_erLaw

open MeasureTheory

namespace RGGDetect

/-- The new row (8) `Y = (1{⟨z, x_i⟩ ≥ τ})_{i ≤ n'}` of the adjacency matrix when the vertex `z` is
added to the points `x₁, …, x_{n'}` (arXiv:2610.08517, held version, §2.1, p.4, eq. (8)). -/
noncomputable def newRow {m d : ℕ} (τ : ℝ) (x : Config m d) (z : Sph d) : Fin m → Bool :=
  fun i => decide (τ ≤ ip z (x i))

/-- The joint probability `P(G_{n'} = G, Y = y)` under independent uniform `x₁, …, x_{n'}, z`. -/
noncomputable def rowJoint (m d : ℕ) (τ : ℝ) (G : SimpleGraph (Fin m)) (y : Fin m → Bool) : ℝ :=
  ((prior m d).prod (unifSphere d)).real {q | rggGraph τ q.1 = G ∧ newRow τ q.1 q.2 = y}

/-- `Λ(y)`, the density of `L(Y | G_{n'} = G)` relative to `Q = Bern(p)^{⊗n'}`,
`Λ(y) = P(Y = y | G_{n'} = G)/Q(y)` (arXiv:2610.08517, held version, §2.1, p.4), with
`p = capProb d τ`. -/
noncomputable def rowLambda (m d : ℕ) (τ : ℝ) (G : SimpleGraph (Fin m)) (y : Fin m → Bool) : ℝ :=
  rowJoint m d τ G y / ((prior m d).real {x | rggGraph τ x = G} * bernProd (capProb d τ) y)

/-- `L(Y | G_{n'} = G)`, the conditional law of the new row given the old graph. -/
noncomputable def condRowLaw (m d : ℕ) (τ : ℝ) (G : SimpleGraph (Fin m)) : Measure (Fin m → Bool) :=
  ∑ y : Fin m → Bool,
    ENNReal.ofReal (rowJoint m d τ G y / (prior m d).real {x | rggGraph τ x = G}) • Measure.dirac y

/-- The reference measure `Q = Bern(p)^{⊗ι}` on `{0,1}^ι`. -/
noncomputable def bernLaw (p : ℝ) (ι : Type*) [Fintype ι] [DecidableEq ι] : Measure (ι → Bool) :=
  ∑ y : ι → Bool, ENNReal.ofReal (bernProd p y) • Measure.dirac y

/-- `K = E_{G_{n'}}[KL(L(Y | G_{n'}) ∥ Q)]` for `n' = n - 1` old vertices
(arXiv:2610.08517, held version, §2.1, p.4). -/
noncomputable def rowK (n d : ℕ) (τ : ℝ) : ENNReal :=
  ∑ G : SimpleGraph (Fin (n - 1)), (prior (n - 1) d {x | rggGraph τ x = G}) *
    InformationTheory.klDiv (condRowLaw (n - 1) d τ G) (bernLaw (capProb d τ) (Fin (n - 1)))

/-- `r⁺ = ⌈2np + 100 log n⌉ + B*` (arXiv:2610.08517, held version, §2.1, p.4). -/
noncomputable def rPlus (n : ℕ) (p : ℝ) (B : ℕ) : ℕ :=
  ⌈2 * (n : ℝ) * p + 100 * Real.log n⌉₊ + B

/-- The truncated `χ²`-divergence (9), `Δ = E_{G_{n'}}[∫_{T⁺} (Λ - 1)² dQ]` with
`T⁺ = {y ∈ {0,1}^{n'} : ∑ y_i ≤ r⁺}` and `n' = n - 1` (arXiv:2610.08517, held version, §2.1, p.4,
eq. (9)).

**Formalization Note** The slack `B*` ("a suitably large constant") is the explicit parameter `B`.
The expectation over `G_{n'}` is the finite sum over graphs on `Fin (n - 1)`; a graph of probability
`0` contributes `0`. The edge density is `p = capProb d τ`. -/
noncomputable def Delta (n d : ℕ) (τ : ℝ) (B : ℕ) : ℝ :=
  ∑ G : SimpleGraph (Fin (n - 1)), (prior (n - 1) d).real {x | rggGraph τ x = G} *
    ∑ y : Fin (n - 1) → Bool,
      (if (Finset.univ.filter fun i => y i = true).card ≤ rPlus n (capProb d τ) B then
        (rowLambda (n - 1) d τ G y - 1) ^ 2 * bernProd (capProb d τ) y else 0)

end RGGDetect


