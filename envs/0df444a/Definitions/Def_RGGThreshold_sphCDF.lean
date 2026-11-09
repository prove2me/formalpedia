-- Prove2me | Definitions.Def_RGGThreshold_sphCDF
-- name    : RGGThreshold_sphCDF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:57:37.500197+00:00
-- url     : https://prove2.me/theorems/0fb86695-4f90-473d-bfcc-c5667ac68a72
-- title:
--   The law $S_k$ of $\sqrt k\,y(1)$: distribution function $\Psi_k$ and density $\psi_k$
-- statement:
--   For an integer $k\ge 1$ let $y$ be a uniform random point of the unit sphere $\mathbb S^{k-1}\subset\mathbb R^k$ and let $S_k$ be the law of $\sqrt k\,y(1)$, where $y(1)$ is the first coordinate. Its distribution function is
--
--   $$
--   \Psi_k(t)=\mathbb P\big[\sqrt k\,y(1)\le t\big],
--   $$
--
--   and its density is
--
--   $$
--   \psi_k(t)=\frac{\Gamma(k/2)}{\sqrt{k\pi}\,\Gamma((k-1)/2)}\Big(1-\frac{t^2}{k}\Big)^{(k-3)/2}\quad(|t|<\sqrt k),\qquad \psi_k(t)=0\quad(|t|\ge\sqrt k).
--   $$
--
--   The scaling by $\sqrt k$ makes $S_k$ close to $N(0,1)$; the paper compares $\Psi_k,\psi_k$ with $\Phi,\phi$ (Lemma 4.4) and uses $S_k$ for the conditional laws of Gram–Schmidt coordinates.
--
--   **Formalization Note** The uniform law on the sphere is the published `RGGDetect.unifSphere`; coordinates are indexed by `Fin k`, so the first coordinate is index $0$. The paper names "the PDF" of $S_k$ without a formula; a density is only defined almost everywhere, and a pointwise inequality needs a fixed version, so $\psi_k$ is the standard closed form above, continuous for $k\ge3$. The sanity file proves $\psi_k\ge0$ and $\Psi_k(t)=0$ for $t<-\sqrt k$, $\Psi_k(t)=1$ for $t\ge\sqrt k$.
-- source:
--   Hunter–Milojević–Sudakov, Distinguishability Threshold for Random Geometric Graphs, arXiv:2607.22480 (held version, sha256 1a398ef9…), §4.2, p.13 (PDF p.15)

import Mathlib
import Definitions.Def_RGGDetect_unifSphere

open MeasureTheory

namespace RGGThreshold

/-- The first coordinate `y(1)` of a point `y` of the unit sphere `S^{k-1} ⊂ ℝ^k`
(Hunter–Milojević–Sudakov, arXiv:2607.22480, held version, sha256 1a398ef9…, §4.2, p.13
(PDF p.15)).

**Formalization Note** Coordinates are `Fin k`, so the paper's first coordinate is index `0`. For
`k = 0` the sphere is empty and the value `0` is never used. -/
noncomputable def firstCoord {k : ℕ} (y : RGGDetect.Sph k) : ℝ :=
  if h : 0 < k then (y : EuclideanSpace ℝ (Fin k)) ⟨0, h⟩ else 0

/-- The distribution function `Ψ_k(t) = P[√k · y(1) ≤ t]` of the law `S_k` of `√k · y(1)`, where `y`
is uniform on `S^{k-1} ⊂ ℝ^k` (arXiv:2607.22480, held version, §4.2, p.13 (PDF p.15)). -/
noncomputable def sphCDF (k : ℕ) (t : ℝ) : ℝ :=
  (RGGDetect.unifSphere k).real {y | Real.sqrt k * firstCoord y ≤ t}

/-- The density `ψ_k` of the law `S_k` of `√k · y(1)`, `y` uniform on `S^{k-1} ⊂ ℝ^k`
(arXiv:2607.22480, held version, §4.2, p.13 (PDF p.15)):
`ψ_k(t) = Γ(k/2) / (√(kπ) Γ((k-1)/2)) · (1 - t²/k)^{(k-3)/2}` for `|t| < √k`, and `0` otherwise.

**Formalization Note** The paper names "the PDF" of `S_k` without a formula; a density is only
defined almost everywhere, and a pointwise inequality such as Lemma 4.4 needs one fixed version.
This is the standard closed form, which is continuous for `k ≥ 3` (the range of the paper). -/
noncomputable def sphPDF (k : ℕ) (t : ℝ) : ℝ :=
  if |t| < Real.sqrt k then
    Real.Gamma ((k : ℝ) / 2) / (Real.sqrt ((k : ℝ) * Real.pi) * Real.Gamma (((k : ℝ) - 1) / 2)) *
      (1 - t ^ 2 / k) ^ (((k : ℝ) - 3) / 2)
  else 0

end RGGThreshold


