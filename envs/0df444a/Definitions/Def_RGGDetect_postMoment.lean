-- Prove2me | Definitions.Def_RGGDetect_postMoment
-- name    : RGGDetect_postMoment
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:37:44.270201+00:00
-- url     : https://prove2.me/theorems/7ed82158-f771-44cc-9ff6-25ca5719d13d
-- title:
--   Posterior second moments: $\mathrm{Post}(D)$, $G_{-u}$ and $Y_I$
-- statement:
--   Let $x_1,\dots,x_n$ follow the product spherical prior and let $F$ be a statistic of the configuration with finitely many values. The **second moment of the posterior mean** of a function $D$ is
--
--   $$
--   \mathbb E\big[(\mathbb E[D\mid F])^2\big]=\sum_b\frac{\big(\mathbb E[D\,\mathbf 1\{F=b\}]\big)^2}{\mathbb P(F=b)} .
--   $$
--
--   1. $\mathrm{Post}(D):=\mathbb E[(\mathbb E[D\mid G_n])^2]$ (5), with $G_n$ the observed graph on all $n$ vertices.
--   2. $G_{-u}$ is the subgraph induced by all vertices except $u$.
--   3. $Y_I=(A_{ui}:i\in I)$ are the edges between $u$ and the vertices of $I$.
--   4. A function $f$ of $k\le n$ points is placed on the first $k$ vertices as $x\mapsto f(x_1,\dots,x_k)$.
--
--   **Formalization Note** All conditionings in the mission except Proposition 3 are on statistics with finitely many values, so the conditional expectation is the finite sum over atoms; an atom of probability $0$ contributes $0$. $G_{-u}$ is recorded as a graph on $[n]$ in which $u$ is isolated, which carries the same information.
-- source:
--   Du, Mao, Sun, Wu, Xu, Sharp detection thresholds for random geometric graphs with polynomial average degrees, arXiv:2610.08517 (held version, sha256 e7bebd4a…), eq. (5), p.2 (PDF p.4); §3.1, p.11 (PDF p.13)

import Mathlib
import Definitions.Def_RGGDetect_rggLaw

open MeasureTheory

namespace RGGDetect

/-- The second moment of the posterior mean of `D` given a finite-valued statistic `F` of the
configuration, `E[(E[D | F])²] = ∑_b (E[D 1{F = b}])² / P(F = b)`, under the product spherical prior.

**Formalization Note** Every conditioning used in the statements (on `G_n`, `G_{-u}`, `(G_{-u}, Y_I)`)
is on a statistic with finitely many values, so the conditional expectation is the finite sum over
the atoms; an atom of probability `0` contributes `0`, its true value. -/
noncomputable def postMoment {n d : ℕ} {β : Type*} [Fintype β] (F : Config n d → β)
    (D : Config n d → ℝ) : ℝ :=
  ∑ b, (∫ x in F ⁻¹' {b}, D x ∂(prior n d)) ^ 2 / (prior n d).real (F ⁻¹' {b})

/-- `Post(D) := E[(E[D | G_n])²]` (5), the second moment of the posterior mean of `D` given the observed
graph `G_n` on all `n` vertices (arXiv:2610.08517, held version, p.2, eq. (5)). -/
noncomputable def Post {n d : ℕ} (τ : ℝ) (D : Config n d → ℝ) : ℝ :=
  postMoment (rggGraph τ) D

/-- `G_{-u}`, the subgraph induced by all vertices except `u` (arXiv:2610.08517, held version, §3.1,
p.11), recorded as a graph on `Fin n` in which `u` is isolated. -/
def graphMinus {n d : ℕ} (τ : ℝ) (u : Fin n) (x : Config n d) : SimpleGraph (Fin n) where
  Adj i j := i ≠ j ∧ i ≠ u ∧ j ≠ u ∧ τ ≤ ip (x i) (x j)
  symm := ⟨fun i j h => ⟨h.1.symm, h.2.2.1, h.2.1, by
    have : ip (x j) (x i) = ip (x i) (x j) := real_inner_comm _ _
    rw [this]; exact h.2.2.2⟩⟩
  loopless := ⟨fun i h => h.1 rfl⟩

/-- `Y_I = (A_{ui} : i ∈ I)`, the edges between `u` and the vertices of `I`
(arXiv:2610.08517, held version, §3.1, p.11; `true` is an edge). -/
noncomputable def rowY {n d : ℕ} (τ : ℝ) (u : Fin n) (I : Finset (Fin n)) (x : Config n d) :
    I → Bool :=
  fun i => decide (τ ≤ ip (x u) (x i))

/-- A function `f` of `k` points, placed on the first `k` vertices `x₁, …, x_k` of an `n`-point
configuration (`0` if `k > n`, a case the statements never use). -/
noncomputable def onFirst {n d : ℕ} (k : ℕ) (f : (Fin k → Sph d) → ℝ) (x : Config n d) : ℝ :=
  if h : k ≤ n then f (fun j => x (Fin.castLE h j)) else 0

end RGGDetect


