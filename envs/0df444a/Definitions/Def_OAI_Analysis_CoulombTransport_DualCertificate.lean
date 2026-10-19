-- Prove2me | Definitions.Def_OAI_Analysis_CoulombTransport_DualCertificate
-- name    : OAI_Analysis_CoulombTransport_DualCertificate
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T18:36:35.32195+00:00
-- url     : https://prove2.me/theorems/a3dd8171-562b-4968-ab54-b1d5eaf6304d
-- title:
--   Integrals of coordinate potential sums against couplings
-- statement:
--   Work in $\mathbb{R}^3$. The three-body Coulomb cost of a triple $(x,y,z)$ is $c(x,y,z)=|x-y|^{-1}+|x-z|^{-1}+|y-z|^{-1}\in[0,\infty]$, with $0^{-1}=\infty$. A three-coupling of a probability measure $\mu$ is a probability measure on triples whose three coordinate marginals all equal $\mu$. For $v:\mathbb{R}^3\to[0,\infty]$ let $(v\oplus v\oplus v)(x,y,z)=v(x)+v(y)+v(z)$.
--
--   1. If $v$ is measurable and $\pi$ is a three-coupling of $\mu$, then
--   $$
--   \int v\oplus v\oplus v\,d\pi=3\int v\,d\mu .
--   $$
--   2. For a probability measure $\pi$, a function $c\ge0$ and a constant $s$, $\int(c+s)\,d\pi=\int c\,d\pi+s$.
--
--   The integral of a potential sum is the same for every coupling. This is the basis of Kantorovich duality certificates.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/DualCertificate.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/DualCertificate.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the CoulombCounterexample mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_CoulombCounterexample
import Definitions.Def_OAI_Analysis_CoulombTransport_AxisHessian
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchCoupling
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombEstimates
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchSeparation
import Definitions.Def_OAI_Analysis_CoulombTransport_GraphBridge

namespace OAI

universe uAlpha

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem356
namespace DualCertificate

/-- The sum of a nonnegative supporting potential over the three coordinates.
A bounded signed potential can be shifted by a constant before using this sum. -/
def potentialSum (v : E3 → ℝ≥0∞) (t : Triple) : ℝ≥0∞ :=
  v (tripleFst t) + v (tripleSnd t) + v (tripleThd t)

/-- The integral of a coordinate potential sum depends only on the common marginal. -/
lemma lintegral_potentialSum {mu : Measure E3} {pi : Measure Triple}
    (hpi : IsThreeCoupling mu pi) {v : E3 → ℝ≥0∞} (hv : Measurable v) :
    (∫⁻ t, potentialSum v t ∂pi) =
      (∫⁻ x, v x ∂mu) + (∫⁻ x, v x ∂mu) + (∫⁻ x, v x ∂mu) := by
  have hf : Measurable tripleFst := measurable_fst
  have hs : Measurable tripleSnd := measurable_fst.comp measurable_snd
  have ht : Measurable tripleThd := measurable_snd.comp measurable_snd
  simp only [potentialSum]
  have hfs : Measurable (fun t : Triple => v (tripleFst t) + v (tripleSnd t)) :=
    (hv.comp hf).add (hv.comp hs)
  have hf' : Measurable (fun t : Triple => v (tripleFst t)) := hv.comp hf
  rw [lintegral_add_left hfs,
    lintegral_add_left hf',
    ← lintegral_map hv hf, ← lintegral_map hv hs, ← lintegral_map hv ht,
    hpi.2.1, hpi.2.2.1, hpi.2.2.2]

/-- Adding a constant to a nonnegative cost shifts its integral by that constant
under a probability measure; no measurability assumption on the cost is needed. -/
lemma lintegral_add_offset {α : Type uAlpha} [MeasurableSpace α]
    (pi : Measure α) [IsProbabilityMeasure pi] (c : α → ℝ≥0∞) (offset : ℝ≥0∞) :
    (∫⁻ t, c t + offset ∂pi) = (∫⁻ t, c t ∂pi) + offset := by
  rw [lintegral_add_right c measurable_const]
  simp

end DualCertificate
end Problem356

end

end OAI


