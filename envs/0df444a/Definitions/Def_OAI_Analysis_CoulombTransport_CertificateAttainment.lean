-- Prove2me | Definitions.Def_OAI_Analysis_CoulombTransport_CertificateAttainment
-- name    : OAI_Analysis_CoulombTransport_CertificateAttainment
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T18:39:44.730987+00:00
-- url     : https://prove2.me/theorems/9f4446e7-447f-4bc8-b9a2-544095d9c55d
-- title:
--   Certificates from a contact coupling
-- statement:
--   Work in $\mathbb{R}^3$. The three-body Coulomb cost of a triple $(x,y,z)$ is $c(x,y,z)=|x-y|^{-1}+|x-z|^{-1}+|y-z|^{-1}\in[0,\infty]$, with $0^{-1}=\infty$. A three-coupling of a probability measure $\mu$ is a probability measure on triples whose three coordinate marginals all equal $\mu$. Let $\pi_0$ be a three-coupling of $\mu$, $v\ge0$ measurable, and $s$ finite. Suppose that for every three-coupling $\pi$,
--   $$
--   v(x)+v(y)+v(z)\le c(x,y,z)+s\quad\pi\text{-a.e.},
--   $$
--   and that equality holds $\pi_0$-a.e. Then $v\oplus v\oplus v$ with shift $s$ is a shifted Coulomb certificate with value $\int c\,d\pi_0$.
--
--   So a coupling living on the contact set of a supporting potential is optimal. Its cost is the Kantorovich value. The triple potential $v\oplus v\oplus v$ is recorded separately.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/CertificateAttainment.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/CertificateAttainment.lean by skeleton subtraction
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
import Definitions.Def_OAI_Analysis_CoulombTransport_DualCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_OptimalLocalization
import Definitions.Def_OAI_Analysis_CoulombTransport_Calibration

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem356

open DualCertificate

namespace ShiftedCoulombCertificate

/-- A contact candidate calibrates the common marginal potential integral.
This constructs the abstract certificate without assuming the candidate is optimal. -/
def ofContactCandidate {mu : Measure E3} {pi0 : Measure Triple}
    (hpi0 : IsThreeCoupling mu pi0) {v : E3 → ℝ≥0∞} (hv : Measurable v)
    {offset : ℝ≥0∞} (hoffset : offset ≠ ⊤)
    (hbound : ∀ pi, IsThreeCoupling mu pi →
      ∀ᵐ t ∂pi, potentialSum v t ≤ coulombCost t + offset)
    (hcontact : ∀ᵐ t ∂pi0, potentialSum v t = coulombCost t + offset) :
    ShiftedCoulombCertificate mu (∫⁻ t, coulombCost t ∂pi0) where
  potential := potentialSum v
  shift := offset
  shift_ne_top := hoffset
  lower_bound := hbound
  integral_eq := by
    intro pi hpi
    have : IsProbabilityMeasure pi0 := hpi0.1
    rw [lintegral_potentialSum hpi hv, ← lintegral_potentialSum hpi0 hv,
      ← lintegral_add_offset pi0 coulombCost offset]
    exact lintegral_congr_ae hcontact

end ShiftedCoulombCertificate

/-- The sum of the marginal potential over the three coordinates. -/
def triplePotential (p : E3 → ℝ≥0∞) (t : Triple) : ℝ≥0∞ :=
  p (tripleFst t) + p (tripleSnd t) + p (tripleThd t)

end Problem356

end

end OAI


