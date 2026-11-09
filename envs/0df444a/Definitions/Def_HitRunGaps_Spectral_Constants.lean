-- Prove2me | Definitions.Def_HitRunGaps_Spectral_Constants
-- name    : HitRunGaps_Spectral_Constants
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:10:46.576592+00:00
-- url     : https://prove2.me/theorems/22729494-82ff-4bdc-8599-8b51f185b9f9
-- title:
--   Ordinary, improved and Babuška–Aziz constants
-- statement:
--   For the full Sobolev class on a bounded domain $\Omega$, let $\delta(x)=\operatorname{dist}(x,\partial\Omega)$ and let $m_f$ be the uniform mean. The ordinary and improved Poincaré constants are the least extended nonnegative constants satisfying
--
--   $$\int_\Omega(f-m_f)^2\,dx\le C_{PI}\int_\Omega|\nabla f|^2\,dx,\qquad
--   \int_\Omega(f-m_f)^2\,dx\le C_{IPI}\int_\Omega\delta^2|\nabla f|^2\,dx.$$
--
--   Define
--
--   $$C_{BA}=\sup_{0\ne f\in Q}\ \inf_{u\in V,\ \operatorname{div}u=f}
--   \frac{\|\nabla u\|_2^2}{\|f\|_2^2}.$$
--
--   An infeasible inner problem has value $+\infty$. No optimizer or bound is assumed. Multiplying every integral by the uniform density leaves these constants unchanged. The same module defines bounded full-dimensional measurable convex bodies, their inradius as the supremum of inscribed ball radii, and the open unit-inball bodies in the goal. It imposes no smooth-boundary or isotropic convention.
-- source:
--   Yunbum Kook, Santosh Vempala, Spectral Gaps of Hit-and-Run and Coordinate Hit-and-Run, STOC 2027 submission #207 (October 2026), published basis, pinned PDF SHA256 a0cdd91dff374c90e51e64b6848852bf973795b9a3005c4f1ee37214f9d5a940, pp.4–6,9, §1.2 and §3

import Definitions.Def_HitRunGaps_Spectral_Sobolev

open MeasureTheory
noncomputable section

namespace HitRunGaps.Spectral

/-- Unnormalized variance: uniform normalization cancels in PI ratios. PDF pp.4–5. -/
def variance {n : ℕ} {Ω : Set (Space n)} (f : L2 Ω) : ENNReal :=
  let m := (volume Ω).toReal⁻¹ * ∫ x in Ω, f x
  ∫⁻ x in Ω, ENNReal.ofReal ((f x - m) ^ 2)

def scalarEnergy {n : ℕ} {Ω : Set (Space n)} (f : H1 Ω) : ENNReal :=
  ∑ i, ENNReal.ofReal (‖f.grad i‖ ^ 2)

def weightedEnergy {n : ℕ} (Ω : Set (Space n)) (g : Fin n → Space n → ℝ) : ENNReal :=
  ∫⁻ x in Ω, ENNReal.ofReal ((boundaryDistance Ω x) ^ 2 * ∑ i, (g i x) ^ 2)

/-- Least extended nonnegative constants over the full source H¹ class, not smooth tests only. -/
def poincare {n : ℕ} (Ω : Set (Space n)) : ENNReal :=
  sInf {C : ENNReal | ∀ f : H1 Ω, variance f.val ≤ C * scalarEnergy f}

def improvedPoincare {n : ℕ} (Ω : Set (Space n)) : ENNReal :=
  sInf {C : ENNReal | ∀ f : H1 Ω,
    variance f.val ≤ C * weightedEnergy Ω (fun i => f.grad i)}

/-- Source sup-inf; empty feasible sets have infimum +∞. No optimizer is postulated. PDF p.6. -/
def babuskaAziz {n : ℕ} (Ω : Set (Space n)) : ENNReal :=
  ⨆ (f : Q Ω) (_ : f.val ≠ 0),
    ⨅ (u : V Ω) (_ : divergence u = f.val),
      ENNReal.ofReal (fieldEnergy u) / ENNReal.ofReal (‖f.val‖ ^ 2)

/-- All bounded full-dimensional convex bodies, open or closed. PDF p.9. -/
def IsConvexBody {n : ℕ} (K : Set (Space n)) : Prop :=
  MeasurableSet K ∧ Bornology.IsBounded K ∧ Convex ℝ K ∧ (interior K).Nonempty

/-- Supremum of inscribed radii; on convex bodies this is finite, positive and attained
in the closure, and agrees for K and its interior. PDF p.9. -/
def inradius {n : ℕ} (K : Set (Space n)) : ℝ :=
  sSup {r : ℝ | 0 ≤ r ∧ ∃ c : Space n, Metric.ball c r ⊆ K}

/-- The main theorem's domain, with no fixed center. PDF p.4. -/
def UnitBody {n : ℕ} (K : Set (Space n)) : Prop :=
  IsOpen K ∧ Bornology.IsBounded K ∧ Convex ℝ K ∧
    ∃ c : Space n, Metric.ball c 1 ⊆ K

end HitRunGaps.Spectral


