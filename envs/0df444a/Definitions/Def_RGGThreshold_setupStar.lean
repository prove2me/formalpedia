-- Prove2me | Definitions.Def_RGGThreshold_setupStar
-- name    : RGGThreshold_setupStar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:58:51.631238+00:00
-- url     : https://prove2.me/theorems/11653622-7d1b-4eed-84fd-4ac159e18998
-- title:
--   Setup (⋆): the conditional law of the new column $v_{s+1}(s),\dots,v_n(s)$
-- statement:
--   Suppose the coordinates $v_i(j)$, $i\in[n]$, $1\le j\le s-1$, are revealed and satisfy $\Pi_{s-1}$. For $s<i\le n$ let $r_i(s)=\sqrt{1-\sum_{k=1}^{s-1}v_i(k)^2}$ be the residual length of $v_i$, let $v_s(s)=\sqrt{1-\|\pi_{s-1}(v_s)\|^2}$, and
--
--   $$
--   \tau_{si}=\frac{c_p}{\sqrt d\,v_s(s)r_i(s)}-\frac{\langle\pi_{s-1}(v_i),\pi_{s-1}(v_s)\rangle}{v_s(s)r_i(s)} .
--   $$
--
--   In **Setup (⋆)** the coordinates $v_i(s)$, $s<i\le n$, are independent, and $v_i(s)/r_i(s)$ is distributed as the first coordinate of a uniform point of $\mathbb S^{d-s}\subset\mathbb R^{d-s+1}$ conditioned on being at least $\tau_{si}$ if $si\in E(H)$, and on being smaller than $\tau_{si}$ if $si\notin E(H)$. Lemma 5.2 shows this is the conditional law of the new column given $\mathcal G_{s-1}$ and the agreement of the edges at $s$.
--
--   **Formalization Note** The paper's vertex $s$ is the 0-based vertex $v$ ($s=v+1$), so the sphere is $\mathbb S^{d-v-1}\subset\mathbb R^{d-v}$. The edge threshold $c_p/\sqrt d$ is the parameter $\tau$ of the random geometric graph (edges are $\langle x_i,x_j\rangle\ge\tau$). The column is a vector indexed by all of `Fin n`; its entries $i\le v$ are the point mass at $0$, an unused placeholder. Conditioning is `ProbabilityTheory.cond`. The file also defines the matrix obtained by inserting the new column into the revealed data.
-- source:
--   Hunter–Milojević–Sudakov, Distinguishability Threshold for Random Geometric Graphs, arXiv:2607.22480 (held version, sha256 1a398ef9…), Setup (⋆), p.16 (PDF p.18); Lemma 4.9, p.14 (PDF p.16)

import Mathlib
import Definitions.Def_RGGThreshold_gsCoord
import Definitions.Def_RGGThreshold_sphCDF

open MeasureTheory

namespace RGGThreshold

/-- The residual length `r_i(s) = √(1 - ∑_{k=1}^{s-1} v_i(k)²)` of row `i` of a coordinate matrix after
`m = s - 1` revealed coordinates (Hunter–Milojević–Sudakov, arXiv:2607.22480, held version, sha256
1a398ef9…, Lemma 4.9, p.14 (PDF p.16); Setup (⋆), p.16 (PDF p.18)). For the row of the vertex `s`
itself it is `v_s(s) = √(1 - ‖π_{s-1}(v_s)‖²)`.

**Formalization Note** The argument `m` is the number of revealed coordinates, i.e. the paper's
`s - 1`. -/
noncomputable def residW {n : ℕ} (m : ℕ) (W : Fin n → Fin n → ℝ) (i : Fin n) : ℝ :=
  Real.sqrt (1 - ipUpTo m W i i)

/-- The truncation point `τ_{si} = c_p/(√d v_s(s) r_i(s)) - ⟨π_{s-1}(v_i), π_{s-1}(v_s)⟩/(v_s(s) r_i(s))`
of Setup (⋆) (arXiv:2607.22480, held version, p.16 (PDF p.18)).

**Formalization Note** The paper's vertex `s` is the 0-based vertex `v` (so `s = v + 1` and the
revealed coordinates are the first `v`). The edge threshold `c_p/√d` is the parameter `τ` of the
random geometric graph (`τ ≤ ⟨x_i, x_j⟩` iff `ij` is an edge). -/
noncomputable def tauSI {n : ℕ} (τ : ℝ) (v : Fin n) (W : Fin n → Fin n → ℝ) (i : Fin n) : ℝ :=
  (τ - ipUpTo v.val W i v) / (residW v.val W v * residW v.val W i)

open Classical in
/-- The law of one new coordinate `v_i(s)` in Setup (⋆) (arXiv:2607.22480, held version, p.16
(PDF p.18)): `v_i(s) = r_i(s) · Y`, where `Y` is the first coordinate of a uniform point of
`S^{d-s} ⊂ ℝ^{d-s+1}` conditioned on `Y ≥ τ_{si}` if `si ∈ E(H)` and on `Y < τ_{si}` otherwise.

**Formalization Note** With `s = v + 1`, the sphere is `S^{d-v-1} ⊂ ℝ^{d-v}`. Conditioning is
`ProbabilityTheory.cond`. -/
noncomputable def colLaw {n : ℕ} (d : ℕ) (τ : ℝ) (H : SimpleGraph (Fin n)) (v : Fin n)
    (W : Fin n → Fin n → ℝ) (i : Fin n) : Measure ℝ :=
  (ProbabilityTheory.cond (RGGDetect.unifSphere (d - v.val))
      (if H.Adj v i then {y | tauSI τ v W i ≤ firstCoord y}
        else {y | firstCoord y < tauSI τ v W i})).map
    (fun y => residW v.val W i * firstCoord y)

open Classical in
/-- The law of coordinate `i` of the new column in Setup (⋆): `colLaw` for the vertices `i > s`,
and the point mass at `0` (an unused placeholder) for the other indices. -/
noncomputable def coordLaw {n : ℕ} (d : ℕ) (τ : ℝ) (H : SimpleGraph (Fin n)) (v : Fin n)
    (W : Fin n → Fin n → ℝ) (i : Fin n) : Measure ℝ :=
  if v < i then colLaw d τ H v W i else Measure.dirac 0

/-- A conditioned finite measure is finite (it is `0` when the conditioning set is null). -/
instance cond.instIsFiniteMeasure {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] (E : Set α) : IsFiniteMeasure (ProbabilityTheory.cond μ E) := by
  by_cases hE : μ E = 0
  · rw [ProbabilityTheory.cond_eq_zero_of_meas_eq_zero hE]; infer_instance
  · have := ProbabilityTheory.cond_isProbabilityMeasure (μ := μ) hE; infer_instance

instance coordLaw.instIsFiniteMeasure {n : ℕ} (d : ℕ) (τ : ℝ) (H : SimpleGraph (Fin n))
    (v : Fin n) (W : Fin n → Fin n → ℝ) (i : Fin n) : IsFiniteMeasure (coordLaw d τ H v W i) := by
  unfold coordLaw colLaw
  split_ifs <;> infer_instance

/-- Setup (⋆) (arXiv:2607.22480, held version, p.16 (PDF p.18)): given revealed coordinates
`W` (the coordinates `j ≤ s - 1` of all `n` vectors), the new column `(v_i(s))_{s<i≤n}` has
independent coordinates, `v_i(s) = r_i(s) · Y_i` with `Y_i` the first coordinate of a uniform point
of `S^{d-s}` conditioned on `Y_i ≥ τ_{si}` if `si ∈ E(H)` and on `Y_i < τ_{si}` otherwise.

**Formalization Note** The paper's vertex `s` is the 0-based vertex `v`. The column is a vector
indexed by `Fin n`; its entries `i ≤ v` are the constant `0` and unused. -/
noncomputable def setupStar {n : ℕ} (d : ℕ) (τ : ℝ) (H : SimpleGraph (Fin n)) (v : Fin n)
    (W : Fin n → Fin n → ℝ) : Measure (Fin n → ℝ) :=
  Measure.pi fun i => coordLaw d τ H v W i

/-- The coordinate matrix after the column of the vertex `v` (the paper's coordinate `s = v + 1`)
is revealed: column `v` is replaced by `u`, the other columns are kept. -/
def extendCol {n : ℕ} (v : Fin n) (W : Fin n → Fin n → ℝ) (u : Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  fun i k => if k = v then u i else W i k

end RGGThreshold


