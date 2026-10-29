-- Prove2me | Definitions.Def_PeskirShiryaev_SharpInequalities_submartingaleSetting
-- name    : PeskirShiryaev_SharpInequalities_submartingaleSetting
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:25:40.53773+00:00
-- url     : https://prove2.me/theorems/1f4c4ab2-9e8a-402e-a49b-f4a733bcce7e
-- title:
--   Uniformly integrable càdlàg submartingales and sharpness
-- statement:
--   On a filtered probability space, let $X=(X_t)_{t\ge0}$ be a nonnegative submartingale started at the deterministic value $x\ge0$, uniformly integrable in $L^1$. Require its paths to be right continuous with finite left limits, outside one null set. Define
--   $$\mathcal M_P(X)=\mathbb E\sup_{t>0}X_t\in[0,\infty].$$
--   For either logarithmic cost $G$, sharpness at $(x,c)$ means that there exists such a process and its measurable almost sure terminal limit $Y$, with finite $\mathbb E G(Y)$, attaining
--   $$\mathcal M_P(X)=W_G(x;c)+c\,\mathbb E G(Y).$$
--   The existential example is allowed its own probability measure and filtration on the fixed path carrier $[0,\infty)\to\mathbb R$. It need not exist on every previously specified probability space.
--
--   This class gives the general-process setting of Corollary 19.6 and an explicit meaning to sharpness.
--
--   **Formalization Note** The process class does not assume terminal convergence or the inequality. These are theorem conclusions. The supremum and its integral use nonnegative extended reals. For right-continuous paths the supremum over $t>0$ equals the supremum including $0$. The canonical carrier has its product measurable space.
-- source:
--   Peskir and Shiryaev, Optimal Stopping and Free-Boundary Problems, Birkhäuser Verlag, 2006, DOI 10.1007/978-3-7643-7390-0, p. 282 (PDF p. 300), Corollary 19.6 and Eq. (19.2.46)

import Definitions.Def_PeskirShiryaev_SharpInequalities_logarithmicCosts
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
noncomputable section

namespace PeskirShiryaev.SharpInequalities

/-- The nonnegative càdlàg uniformly integrable submartingales of Corollary 19.6.
Path properties hold simultaneously outside one null set; left limits are finite. -/
def IsUICadlagSubmartingale {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (ℱ : Filtration ℝ≥0 mΩ) (X : ℝ≥0 → Ω → ℝ) (x : ℝ) : Prop :=
  Submartingale X ℱ P ∧ UniformIntegrable X 1 P ∧
  (∀ᵐ ω ∂P, X 0 ω = x ∧ (∀ t, 0 ≤ X t ω) ∧
    (∀ t, ContinuousWithinAt (fun s => X s ω) (Set.Ici t) t) ∧
    ∀ t : ℝ≥0, 0 < t → ∃ a : ℝ, Tendsto (fun s => X s ω) (𝓝[<] t) (𝓝 a))

/-- The extended expected supremum over strictly positive times, as printed. -/
def fullMaximumExpectation {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℝ≥0 → Ω → ℝ) : EReal :=
  ((∫⁻ ω, ⨆ t : ℝ≥0, ⨆ (_ : 0 < t), ENNReal.ofReal (X t ω) ∂P) : EReal)

/-- Finite equality examples on a fixed canonical path carrier express sharpness;
no demand is made that an arbitrary given probability space support an extremizer. -/
def SharpAt (k : LogCost) (x c : ℝ) : Prop :=
  ∃ (P : Measure (ℝ≥0 → ℝ))
    (ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace (ℝ≥0 → ℝ)))
    (X : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ) (Y : (ℝ≥0 → ℝ) → ℝ),
    IsProbabilityMeasure P ∧ IsUICadlagSubmartingale P ℱ X x ∧
    AEMeasurable Y P ∧ (∀ᵐ ω ∂P, Tendsto (fun t => X t ω) atTop (𝓝 (Y ω))) ∧
    costExpectation P k Y < ⊤ ∧
    fullMaximumExpectation P X = (boundConstant k x c : EReal) +
      (c : EReal) * costExpectation P k Y

end PeskirShiryaev.SharpInequalities


