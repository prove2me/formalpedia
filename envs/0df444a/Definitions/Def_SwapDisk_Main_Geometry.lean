-- Prove2me | Definitions.Def_SwapDisk_Main_Geometry
-- name    : SwapDisk_Main_Geometry
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T22:15:41.1462+00:00
-- url     : https://prove2.me/theorems/e3dd2a00-73d7-4fc6-82aa-669ea24ba19d
-- title:
--   The Euclidean unit disk $B^2_2$, unit circle, tangent $\tau_x$, support defect $\psi_x(G)$, normalized arc measure $\sigma$, $h_A$, $\beta_N$ and $m_T$
-- statement:
--   Write $\mathbb R^2$ with its Euclidean inner product $\langle\cdot,\cdot\rangle$ and norm $\|\cdot\|_2$, and let
--   $$B^2_2=\{x\in\mathbb R^2:\|x\|_2\le1\},\qquad S^1=\{x\in\mathbb R^2:\|x\|_2=1\}.$$
--   $B^2_2$ carries its Borel $\sigma$-field (it is a compact, hence Polish, space). For $x=(x_1,x_2)$ the unit tangent is $\tau_x=(-x_2,x_1)$, and for $x\in B^2_2$, $G\in\mathbb R^2$ the **support defect** is
--   $$\psi_x(G)=\langle G,x\rangle+\|G\|_2 .$$
--   The **normalized arc measure** $\sigma$ on $S^1$ is the image of $d\theta/2\pi$ on $[0,2\pi)$ under $\theta\mapsto(\cos\theta,\sin\theta)$. For a nonempty finite $A\subseteq\mathbb R^2$, $h_A(u)=\max_{x\in A}\langle u,x\rangle$. Finally
--   $$\beta_N=1-\frac N\pi\sin\frac\pi N,\qquad m_T=\mathbb E\Big|\sum_{t=1}^T\varepsilon_t\Big|$$
--   for independent uniform signs $\varepsilon_t$; $m_T$ is the published Rademacher first moment $K_T(1,\dots,1)$.
--
--   These are the geometric and numerical objects of the lower bounds (Appendix D) and of the regret identities (Appendix A).
--
--   **Formalization Note.** $\mathbb R^2$ is `EuclideanSpace ℝ (Fin 2)` (coordinates 0-based: $x_1,x_2$ are `x 0`, `x 1`), never the sup-norm space `ℝ × ℝ`. The disk type `Disk` is the subtype of points of norm at most one. `toDisk` maps a point of norm at most one to itself (and other points to the origin); it is only applied to points of $S^1$. `angleLaw` is $d\theta/2\pi$ on $[0,2\pi)$, used for a uniform direction.
-- source:
--   Saravanan, Minimax Realized Full Swap Regret on the Euclidean Disk, STOC 2027 submission (manuscript sha256 e7138cc2…), p. 13 (notation), p. 14 Eq. (A.4), p. 15 (τ_x), p. 42 Eq. (D.1), p. 45 Eq. (D.11), p. 47 Eq. (D.18) and h_A

import Mathlib
import Definitions.Def_KhintchineTwoRegime_K

/-!
# The Euclidean unit disk, the support defect `ψ_x(G)`, arc measure, `β_N` and `m_T`

Saravanan, *Minimax Realized Full Swap Regret on the Euclidean Disk*, STOC 2027 submission
(manuscript sha256 e7138cc2…): p. 13 (standing notation), p. 14 Eq. (A.4), p. 15 (`τ_x`),
p. 42 Eq. (D.1), p. 45 Eq. (D.11), p. 47 Eq. (D.18) and the definition of `h_A`.

Conventions.
* `ℝ²` is `EuclideanSpace ℝ (Fin 2)` (Euclidean norm and inner product, not the sup norm of
  `ℝ × ℝ`); coordinates are 0-based: the paper's `x₁, x₂` are `x 0, x 1`.
* `B²₂` is the subtype `Disk` of points of norm at most one, with the subspace topology and its
  Borel σ-field; it is a Polish, hence standard Borel, space.
* `σ` (normalized arc measure on `S¹`) is the push-forward of `dθ / 2π` on `[0, 2π)` under
  `θ ↦ (cos θ, sin θ)`.
* `m_T = E|ε₁ + ⋯ + ε_T|` is the published Rademacher first moment
  `KhintchineTwoRegime.K T (1, …, 1)` (uniform average over the `2^T` sign vectors).
-/

open MeasureTheory

namespace SwapDisk.Main

/-- The Euclidean plane `ℝ²`. -/
abbrev E2 : Type := EuclideanSpace ℝ (Fin 2)

/-- The Euclidean inner product `⟨u, v⟩` on `ℝ²`. -/
noncomputable def ip (u v : E2) : ℝ := inner ℝ u v

/-- The closed Euclidean unit disk `B²₂ = {x ∈ ℝ² : ‖x‖₂ ≤ 1}` as a set. -/
def disk : Set E2 := {x | ‖x‖ ≤ 1}

/-- The closed Euclidean unit disk `B²₂` as a type (subspace topology, Borel σ-field). -/
abbrev Disk : Type := ↥disk

/-- `B²₂` is closed in `ℝ²`, hence Polish. -/
instance : PolishSpace Disk :=
  IsClosed.polishSpace (isClosed_le continuous_norm continuous_const)

/-- The unit circle `S¹ = {x ∈ ℝ² : ‖x‖₂ = 1}`. -/
def unitCircle : Set E2 := {x | ‖x‖ = 1}

/-- The unit tangent `τ_x = (−x₂, x₁)`. -/
noncomputable def tau (x : E2) : E2 := !₂[-(x 1), x 0]

/-- The support defect `ψ_x(G) = ⟨G, x⟩ + ‖G‖₂` (Eq. (A.4)). -/
noncomputable def psi (x G : E2) : ℝ := ip G x + ‖G‖

/-- The point `(cos θ, sin θ)` of the unit circle. -/
noncomputable def circlePt (θ : ℝ) : E2 := !₂[Real.cos θ, Real.sin θ]

/-- Normalized arc measure `σ` on `S¹` (total mass one), as a measure on `ℝ²`. -/
noncomputable def arcMeasure : Measure E2 :=
  ((ENNReal.ofReal (2 * Real.pi))⁻¹ • volume.restrict (Set.Ico (0 : ℝ) (2 * Real.pi))).map
    circlePt

/-- The point `(cos θ, sin θ)` as a point of the disk. -/
noncomputable def circleDisk (θ : ℝ) : Disk :=
  ⟨circlePt θ, by simp [disk, circlePt, EuclideanSpace.norm_eq]⟩

/-- The uniform law `dθ / 2π` of an angle on `[0, 2π)`. -/
noncomputable def angleLaw : Measure ℝ :=
  (ENNReal.ofReal (2 * Real.pi))⁻¹ • volume.restrict (Set.Ico (0 : ℝ) (2 * Real.pi))

instance : IsProbabilityMeasure angleLaw :=
  ⟨by
    simp only [angleLaw, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ,
      Set.univ_inter, Real.volume_Ico, sub_zero, smul_eq_mul]
    exact ENNReal.inv_mul_cancel (by simp [Real.pi_pos]) ENNReal.ofReal_ne_top⟩

/-- The negation `x ↦ −x` of the disk. -/
def negDisk (x : Disk) : Disk := ⟨-(x : E2), by simpa [disk] using x.2⟩

@[fun_prop]
theorem measurable_negDisk : Measurable negDisk :=
  ((continuous_neg.comp continuous_subtype_val).subtype_mk _).measurable

@[fun_prop]
theorem measurable_circleDisk : Measurable circleDisk :=
  (Continuous.subtype_mk (by unfold circlePt; fun_prop) _).measurable

/-- A point of `ℝ²` as a point of the disk (the point itself when `‖v‖ ≤ 1`, else the origin;
used only on points already known to lie in `B²₂`). -/
noncomputable def toDisk (v : E2) : Disk :=
  if h : ‖v‖ ≤ 1 then ⟨v, h⟩ else ⟨0, by simp [disk]⟩

/-- The support function `h_A(u) = max_{x ∈ A} ⟨u, x⟩` of a nonempty finite set `A`. -/
noncomputable def supportFn (A : Finset E2) (hA : A.Nonempty) (u : E2) : ℝ :=
  A.sup' hA (fun x => ip u x)

/-- `β_N = 1 − (N/π) sin(π/N)` (Eq. (D.18)). -/
noncomputable def betaN (N : ℕ) : ℝ := 1 - ((N : ℝ) / Real.pi) * Real.sin (Real.pi / N)

/-- `m_T = E|∑_{t=1}^T ε_t|` for independent uniform signs (Eqs. (D.1), (D.11)): the published
Rademacher first moment `K_T` at the all-ones vector. -/
noncomputable def mT (T : ℕ) : ℝ := KhintchineTwoRegime.K T (fun _ => 1)

end SwapDisk.Main


