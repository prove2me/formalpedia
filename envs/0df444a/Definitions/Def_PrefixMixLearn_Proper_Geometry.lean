-- Prove2me | Definitions.Def_PrefixMixLearn_Proper_Geometry
-- name    : PrefixMixLearn_Proper_Geometry
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T19:45:31.431141+00:00
-- url     : https://prove2.me/theorems/3c345459-b9e0-4fca-88e1-0aed0a7ae919
-- title:
--   Mean–direction coordinates $M(m,v,w)$, the feasibility box $I(m,w)$, $\rho(d)$, clipping and the restoration of Lemma F.1
-- statement:
--   For $0<w<1$, $M(m,v,w)=(1-w)Q_{m-wv}+wQ_{m+(1-w)v}$. For $m\in[\alpha,1-\alpha]^T$ the **feasibility box** is $I(m,w)=\prod_i[L_i,U_i]$ with
--   $$L_i=\max\Big\{\tfrac{m_i-(1-\alpha)}{w},\tfrac{\alpha-m_i}{1-w}\Big\},\quad U_i=\min\Big\{\tfrac{m_i-\alpha}{w},\tfrac{1-\alpha-m_i}{1-w}\Big\};$$
--   $\Pi_{I(m,w)}$ is the coordinatewise projection $v_i\mapsto\max\{L_i,\min\{U_i,v_i\}\}$ and clipping into $[\alpha,1-\alpha]$ is $v_i\mapsto\max\{\alpha,\min\{1-\alpha,v_i\}\}$. For a vector $d$, $\rho(d)=\sqrt{(\sum_i d_i^2)^2-\sum_i d_i^4}$, and $\|v\|_2$ is the Euclidean norm.
--
--   The **restoration** of raw vectors $\tilde\nu,\tilde\mu$ at weight $w$: put $\tilde d=\tilde\mu-\tilde\nu$, $\tilde m=(1-w)\tilde\nu+w\tilde\mu$, clip $\tilde m$ to $\hat m$, project $\tilde d$ onto $I(\hat m,w)$ to get $\hat d$, and return $M(\hat m,\hat d,w)$.
--
--   **Formalization Note.** The box formulas are used only for $0<w<1$ and $m$ in the balanced box, as in the paper; there $L_i\le0\le U_i$ and the projection formula is the Euclidean projection.
-- source:
--   Saravanan, Proper Agnostic Learning of Two Balanced Product Distributions from Prefix-Conditional Samples, STOC 2027 submission (manuscript sha256 9c359910…), p. 13–14 (PDF 15–16), §A.2–A.3; p. 39 (PDF 41), Lemma F.1

import Mathlib
import Definitions.Def_PrefixMixLearn_Proper_Laws

set_option autoImplicit false

noncomputable section

namespace PrefixMixLearn.Proper

/-!
# Mean–direction coordinates, the feasibility box `I(m, w)`, clipping and restoration

Saravanan, *Proper Agnostic Learning of Two Balanced Product Distributions from Prefix-Conditional
Samples*, STOC 2027 submission (manuscript sha256 9c359910…), §A.2–A.3, pp. 13–14 (PDF 15–16);
Lemma F.1, p. 39 (PDF 41).

* `rhoQuad d = ρ(d) = √((Σ d_i²)² − Σ d_i⁴)` (Lemma A.2).
* `mixMD m v w = M(m, v, w) = (1 − w) Q_{m − w v} + w Q_{m + (1 − w) v}` (§A.3).
* `boxLo α m w i = L_i = max{(m_i − (1 − α))/w, (α − m_i)/(1 − w)}`,
  `boxHi α m w i = U_i = min{(m_i − α)/w, (1 − α − m_i)/(1 − w)}`; `I(m, w) = Π_i [L_i, U_i]`
  (used only for `0 < w < 1`, `m ∈ [α, 1 − α]^T`, where `L_i ≤ 0 ≤ U_i`).
* `projBox α m w v` is the coordinatewise Euclidean projection of `v` onto `I(m, w)`:
  `max L_i (min U_i v_i)`.
* `clipBox α v` clips every coordinate into `[α, 1 − α]`.
* `restore α w ν̃ μ̃` is the construction of Lemma F.1: with `d̃ = μ̃ − ν̃`,
  `m̃ = (1 − w)ν̃ + wμ̃`, clip `m̃` to `m̂`, project `d̃` onto `I(m̂, w)` to `d̂`, return
  `M(m̂, d̂, w)`.
-/

/-- `ρ(d) = √((Σ_i d_i²)² − Σ_i d_i⁴)`. -/
def rhoQuad {T : ℕ} (d : Fin T → ℝ) : ℝ :=
  Real.sqrt ((∑ i, d i ^ 2) ^ 2 - ∑ i, d i ^ 4)

/-- Mean–direction coordinates `M(m, v, w) = (1 − w)Q_{m − wv} + wQ_{m + (1 − w)v}`. -/
def mixMD {T : ℕ} (m v : Fin T → ℝ) (w : ℝ) : Cube T → ℝ :=
  mixLaw w (fun i => m i - w * v i) (fun i => m i + (1 - w) * v i)

/-- The lower endpoint `L_i = max{(m_i − (1 − α))/w, (α − m_i)/(1 − w)}`. -/
def boxLo {T : ℕ} (α : ℝ) (m : Fin T → ℝ) (w : ℝ) (i : Fin T) : ℝ :=
  max ((m i - (1 - α)) / w) ((α - m i) / (1 - w))

/-- The upper endpoint `U_i = min{(m_i − α)/w, (1 − α − m_i)/(1 − w)}`. -/
def boxHi {T : ℕ} (α : ℝ) (m : Fin T → ℝ) (w : ℝ) (i : Fin T) : ℝ :=
  min ((m i - α) / w) ((1 - α - m i) / (1 - w))

/-- The coordinatewise projection `Π_{I(m,w)} v` onto the box `Π_i [L_i, U_i]`. -/
def projBox {T : ℕ} (α : ℝ) (m : Fin T → ℝ) (w : ℝ) (v : Fin T → ℝ) : Fin T → ℝ :=
  fun i => max (boxLo α m w i) (min (boxHi α m w i) (v i))

/-- Coordinatewise clipping into `[α, 1 − α]` (the projection `Π_{[α,1−α]^T}`). -/
def clipBox {T : ℕ} (α : ℝ) (v : Fin T → ℝ) : Fin T → ℝ :=
  fun i => max α (min (1 - α) (v i))

/-- The restored proper mixture of Lemma F.1 / Theorem D.2: clip the weighted mean of the raw
vectors, project their difference onto `I(m̂, w)`, return `M(m̂, d̂, w)`. -/
def restore {T : ℕ} (α w : ℝ) (νt μt : Fin T → ℝ) : Cube T → ℝ :=
  let mhat := clipBox α (fun i => (1 - w) * νt i + w * μt i)
  mixMD mhat (projBox α mhat w (fun i => μt i - νt i)) w

end PrefixMixLearn.Proper


