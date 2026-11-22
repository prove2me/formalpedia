-- Prove2me | Definitions.Def_NoHair_TwoCentreBlackHole
-- name    : NoHair_TwoCentreBlackHole
-- status  : Definition
-- author  : @Igor Valuev
-- created : 2026-11-22T21:47:41.533971+00:00
-- url     : https://prove2.me/theorems/fab8c342-d2a7-4a2d-afd0-dc16fba51f37
-- title:
--   The concrete one-horizon two-centre manifold, metric, field, time orientation, and flow
-- statement:
--   A concrete open four-manifold for the two-centre Majumdar–Papapetrou solution, with the left future horizon adjoined and the other throat omitted. In global coordinates $(v,X)$ take $|X|>3/4$ and $X\ne3e_1$. Write $r=|X|-1$, $n=X/|X|$, $c=n_1$. The metric is the advanced radial block together with $H^2d\Omega^2$ pulled back by $X\mapsto n$. The Faraday tensor is the exterior derivative of the regular advanced potential. The stationary flow translates $v$. A future orientation is given by $\partial_v-\alpha\partial_r$, where $\alpha=g_{vr}/(1+g_{rr}^2)$. The total chart agrees on the full two-centre isotropic exterior with the smooth advanced coordinate transformation.
-- source:
--   J. B. Hartle and S. W. Hawking, Solutions of the Einstein-Maxwell equations with many black holes, Commun. Math. Phys. 26 (1972), 87–101, §II, equations (2.1)–(2.13), https://doi.org/10.1007/BF01645696. The chosen open subextension and the shifted Cartesian radius are specified explicitly.

import Definitions.Def_NoHair_TwoCentreSpacetime
import Definitions.Def_NoHair_TwoCentreAdvanced
import Definitions.Def_NoHair_kerrNewman

open NoHair NoHair.TwoCentre NoHair.TwoCentre.Cartesian Set
open scoped ContDiff Manifold

namespace NoHair.TwoCentre.Model

noncomputable section

private theorem spatial_continuous : Continuous spatial := by
  have hs : ContDiff ℝ ∞ spatial :=
    contDiff_euclidean.2 (fun i => contDiff_piLp_apply (p := 2) (i := i.succ))
  exact hs.continuous

/-- The extended spacetime as an open submanifold of advanced Cartesian coordinate space. -/
def manifold : TopologicalSpace.Opens E4 := ⟨spacetime,
  (isOpen_lt continuous_const spatial_continuous.norm).inter
    (isOpen_ne_fun spatial_continuous continuous_const)⟩

def outer : Set manifold := {z | (z : E4) ∈ outerRegion}

def angularDirection (z : E4) : E3 := ‖spatial z‖⁻¹ • spatial z
def parameters (z : E4) : ℝ × ℝ := (‖spatial z‖ - 1, angularDirection z 0)
def dt (i : Fin 4) : ℝ := if i = 0 then 1 else 0
def dr (z : E4) (i : Fin 4) : ℝ := coordinates 0 (angularDirection z) i
def spatialDelta (i j : Fin 4) : ℝ := if i = j ∧ i ≠ 0 then 1 else 0

/-- The advanced radial block together with H² times the pullback unit sphere metric. -/
def metricCoeffs (z : E4) (i j : Fin 4) : ℝ :=
  let p := parameters z
  Advanced.gvv p * dt i * dt j +
    Advanced.gvr p * (dt i * dr z j + dr z i * dt j) +
    Advanced.grr p * dr z i * dr z j +
    Advanced.angularScale p / ‖spatial z‖ ^ 2 * (spatialDelta i j - dr z i * dr z j)

def potential (i : Fin 4) (z : E4) : ℝ :=
  Advanced.potentialV (parameters z) * dt i + Advanced.potentialR (parameters z) * dr z i

def faradayCoeffs (z : E4) (i j : Fin 4) : ℝ :=
  coordPartial (potential j) i z - coordPartial (potential i) j z

def metric : BilinField manifold := fun z => matrixBilin (metricCoeffs z)
def faraday : BilinField manifold := fun z => matrixBilin (faradayCoeffs z)

/-- A stationary, future timelike reference vector K − α∂r.
For α = gvr/(1+grr²), its squared norm is strictly negative. -/
def orientation : VecField manifold := fun z =>
  let p := parameters z
  coordinates 1 (-(Advanced.gvr p / (1 + Advanced.grr p ^ 2)) • angularDirection z)

theorem spatial_coordinates (t : ℝ) (x : E3) : spatial (coordinates t x) = x := by
  ext i
  simp [spatial, coordinates, Fin.cons_succ]

def flow (s : ℝ) (z : manifold) : manifold :=
  ⟨coordinates ((z : E4) 0 + s) (spatial z), by
    change 3 / 4 < ‖spatial (coordinates _ _)‖ ∧ spatial (coordinates _ _) ≠ _
    rw [spatial_coordinates]
    exact z.2⟩

private def basePoint : manifold :=
  ⟨coordinates 0 unitAxis, by
    change 3 / 4 < ‖spatial (coordinates _ _)‖ ∧ spatial (coordinates _ _) ≠ _
    rw [spatial_coordinates]
    have hn : ‖unitAxis‖ = 1 := by simp [unitAxis]
    refine ⟨by rw [hn]; norm_num, ?_⟩
    intro hh
    have h := congrArg norm hh
    rw [norm_smul, hn] at h
    norm_num at h⟩

/-- The isotropic chart valued in the actual open spacetime, total off its chart source. -/
def chart (y : E4) : manifold := by
  classical
  exact if h : toAdvanced y ∈ spacetime then ⟨toAdvanced y, h⟩ else basePoint

end
end NoHair.TwoCentre.Model


