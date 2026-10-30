-- Prove2me | Definitions.Def_ContactTopology_AntipodalSphereQuotients
-- name    : ContactTopology_AntipodalSphereQuotients
-- status  : Definition
-- author  : @Johan Mercedes
-- created : 2026-10-30T02:29:36.634038+00:00
-- url     : https://prove2.me/theorems/623073c3-4032-4adc-b7d6-50b170234154
-- title:
--   Normalized real spheres and their antipodal quotients
-- statement:
--   For a nonnegative integer $n$, define the normalized real sphere and its antipodal quotient by
--   $$S^{n-1}=\left\{x\in\mathbb R^n:\sum_i x_i^2=1\right\},\qquad P^{n-1}=S^{n-1}/(x\sim -x).$$
--   The invertible integers $\{1,-1\}$ act by scalar multiplication, so the quotient is the orbit quotient of this action with its quotient topology. The map $\pi_n:S^{n-1}\to P^{n-1}$ is the canonical projection. For $n=2$ and $n=4$ these are the sphere-cover models of the projective circle and projective three-space. For $n=0$ the normalized sphere and its quotient are empty.
--
--   These definitions provide concrete topological targets for equivariant contact knots and rational Seifert disks. The action laws are included. Covering, fiber-cardinality, compactness and embedding assertions are supplied by separate proofs.
-- source:
--   Standard normalized-sphere model of real projective space. The rational Seifert disk application follows Kenneth L. Baker and John B. Etnyre, Rational linking and contact geometry, corrected version, https://etnyre.math.gatech.edu/preprints/papers/ratlink.pdf, Section 1, pp. 2–3, and Hyunki Min, arXiv:2207.03590v2, Sections 2.4–2.5.

import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Algebra.GroupWithZero.Units.Fintype

namespace ContactTopology.Projective
noncomputable section
set_option backward.isDefEq.respectTransparency false

def sphereSet (n : ℕ) : Set (Fin n → ℝ) := {y | ∑ i, y i^2=1}
abbrev RoundSphere (n : ℕ) := sphereSet n


instance (n : ℕ) : MulAction ℤˣ (RoundSphere n) where
  smul g y := ⟨(g : ℤ) • (y : Fin n → ℝ),by
    have hnorm : ∑ i, (y : Fin n → ℝ) i^2=1 := y.property
    obtain rfl|rfl := Int.units_eq_one_or g
    · change ∑ i, ((1:ℤ) • (y : Fin n → ℝ)) i^2=1
      simpa only [one_smul] using hnorm
    · change ∑ i, ((-1:ℤ) • (y : Fin n → ℝ)) i^2=1
      simpa only [neg_one_zsmul,Pi.neg_apply,neg_sq] using hnorm⟩
  one_smul y := by
    apply Subtype.ext
    change (1:ℤ) • (y : Fin n → ℝ)=(y : Fin n → ℝ)
    exact one_smul ℤ (y : Fin n → ℝ)
  mul_smul g h y := by
    apply Subtype.ext
    change ((g*h : ℤˣ):ℤ) • (y : Fin n → ℝ)=
      (g:ℤ) • ((h:ℤ) • (y : Fin n → ℝ))
    rw [Units.val_mul,mul_smul]


abbrev ProjectiveSphere (n : ℕ) := Quotient (MulAction.orbitRel ℤˣ (RoundSphere n))

def project (n : ℕ) : RoundSphere n → ProjectiveSphere n :=
  Quotient.mk (MulAction.orbitRel ℤˣ (RoundSphere n))

end
end ContactTopology.Projective


