-- Prove2me | Definitions.Def_JRCurvedQFT_Symmetries_trajectorySet
-- name    : JRCurvedQFT_Symmetries_trajectorySet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T07:02:07.424548+00:00
-- url     : https://prove2.me/theorems/d557b321-cc69-4fdf-99a6-ce4706c46b92
-- title:
--   The trajectory set $U_\alpha$, the reading of $\Omega_{\xi,\alpha}$
-- statement:
--   For $\alpha\ge0$, the **trajectory set** is
--   $$U_\alpha=\{p\in M:\ \phi_s(p)\in\Omega_+\ \text{for every } s\in[0,\alpha]\}.$$
--   It is the set of points whose trajectory stays at positive time up to parameter $\alpha$. It lies in $\Omega_+$, shrinks as $\alpha$ grows, satisfies $U_0=\Omega_+$ and $\phi_\beta(U_\alpha)\subseteq U_{\alpha-\beta}$.
--
--   **Formalization Note** This is the reading of the set $\Omega_{\xi,\alpha}$ of the proof of Theorem 6.4. The printed $\phi_\alpha^{-1}(\Omega_+)$ is not contained in $\Omega_+$, and $\Omega_+\cap\phi_\alpha^{-1}(\Omega_+)$ makes the theorem false (rotations of $\mathbb R^2$ at $\alpha=2\pi$).
-- source:
--   Jaffe, Ritter, Quantum Field Theory on Curved Backgrounds. II. Spacetime Symmetries, arXiv:0704.0052v1, proof of Theorem 6.4, p. 12

import Mathlib
import Definitions.Def_JRCurvedQFT_Symmetries_IsometryFlow

open scoped Manifold ContDiff ENNReal Topology InnerProductSpace
open Bundle MeasureTheory

namespace JRCurvedQFT.Symmetries

variable {d : ℕ} {M : Type} [EMetricSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) x)]

/-- The **trajectory set** `U_α = {p ∈ M : φ_s(p) ∈ Ω₊ for every s ∈ [0, α]}`, the reading of the
set `Ω_{ξ,α}` of the proof of Theorem 6.4.

Jaffe, Ritter, *Quantum Field Theory on Curved Backgrounds. II. Spacetime Symmetries*, arXiv:0704.0052v1, proof of Theorem 6.4, p. 12: "Define Ω_{ξ,α} := φ_α⁻¹(Ω₊). For all α in some neighborhood
of zero, Ω_{ξ,α} is a nonempty open subset of Ω₊, and moreover, as α → 0⁺, Ω_{ξ,α} increases to
fill Ω₊ with Ω_{ξ,0} = Ω₊."

**Formalization Note** Reading 2. The printed `φ_α⁻¹(Ω₊)` is not a subset of `Ω₊` (for `ξ = ∂_t` and
`α > 0` it is `{t > −α}`), so the quantization map is not defined on its field space. The
alternative `Ω₊ ∩ φ_α⁻¹(Ω₊)` makes the theorem false (rotations of `ℝ²` at `α = 2π`, where it is all
of `Ω₊`). `U_α` lies in `Ω₊` for `α ≥ 0`, increases to `Ω₊` as `α ↓ 0`, and has `φ_β(U_α) ⊆ U_{α−β}`,
which are the assertions the proof makes. It is used only for `α ≥ 0`. -/
def trajectorySet (S : JRCurvedQFT.SharpTime.StaticStructure (d := d) M) (φ : IsometryFlow (d := d) M) (α : ℝ) : Set M :=
  {p | ∀ s ∈ Set.Icc (0 : ℝ) α, φ.toFun s p ∈ S.positiveTime}

end JRCurvedQFT.Symmetries


