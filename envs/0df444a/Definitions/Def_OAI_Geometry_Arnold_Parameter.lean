-- Prove2me | Definitions.Def_OAI_Geometry_Arnold_Parameter
-- name    : OAI_Geometry_Arnold_Parameter
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T09:05:29.724354+00:00
-- url     : https://prove2.me/theorems/79e53146-1bdb-4b51-8c05-3aaf64c25c95
-- title:
--   The time-dependent midpoint isotopy on the unit quadric and its Hamiltonian
-- statement:
--   On $\mathbb{C}^5$ write $q(z)=\sum_jz_j^2$, $|z|^2=\sum_j|z_j|^2$, $B(z,w)=\sum_jz_jw_j$ and $\omega(u,v)=2\operatorname{Im}\sum_j\bar u_jv_j$. The unit quadric is $S=\{z:|z|^2=1,\ q(z)=0\}$, and $Q_3=S/U(1)$ is the projective quadric. Let $X$ be the compactly supported Hamiltonian field with potential $K$ (so that $\omega(X,\cdot)=dK$ near the unit quadric), and let $\Lambda$ be a Lipschitz constant of $X$.
--
--   1. **Step-size profile.** With $\varepsilon=\dfrac{1}{100(\Lambda+1)}>0$, set
--   $$
--   \tau(t)=\varepsilon\,\sin\frac{\pi t}{2}.
--   $$
--   Then $\tau$ is smooth, $\tau(0)=0$, and $|\tau(t)|\,\Lambda<\tfrac1{10}$.
--   2. **The isotopy.** Let $c(t,z)$ solve $c=z+\tau(t)X(c)$. Define the forward map $F(t,z)=2c-z$, the backward map $G$ (the same construction with $-\tau$), and the Hamiltonian $H(t,w)=2\tau'(t)\,K\bigl(c^-(t,w)\bigr)$, where $c^-$ is the centre for $-\tau$.
--   3. **Properties.**
--      - $F$, $G$ and $H$ are smooth.
--      - $F(t,\cdot)$ and $G(t,\cdot)$ map the unit quadric to itself and are mutually inverse.
--      - $F$ and $G$ commute with unit complex scalars, and $H$ is invariant under them.
--      - $F(0,\cdot)=\mathrm{id}$.
--      - For $z\in S$, $|c(t,z)|^2\in(\tfrac12,2)$.
--      - For all $t$, $z\in S$ and $v\in\mathbb{C}^5$,
--   $$
--   \omega\bigl(\partial_tF(t,z),v\bigr)=d_wH\bigl(t,F(t,z)\bigr)[v].
--   $$
--
--   This is a concrete Hamiltonian isotopy of the quadric whose time-one map is a small implicit-midpoint perturbation. Composed with the coordinate involution, it gives the map with exactly three fixed points.
--
--   **Formalization Note** The Lipschitz constant is chosen by `Classical.choose` from `vectorField_lipschitz`. The names are `parameter`, `center`, `forwardMid`, `backwardMid` and `midHamiltonian`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/Arnold/Parameter.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/Arnold/Parameter.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ArnoldCounterexample mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ArnoldCounterexample
import Definitions.Def_OAI_Geometry_Arnold_Involution
import Definitions.Def_OAI_Geometry_Arnold_Projective
import Definitions.Def_OAI_Geometry_Arnold_Rotation
import Definitions.Def_OAI_Geometry_Arnold_Tangent
import Definitions.Def_OAI_Geometry_Arnold_Haar
import Definitions.Def_OAI_Geometry_Arnold_Differentiation
import Definitions.Def_OAI_Geometry_Arnold_Orbit
import Definitions.Def_OAI_Geometry_Arnold_Symplectic
import Definitions.Def_OAI_Geometry_Arnold_Coordinates
import Definitions.Def_OAI_Geometry_Arnold_Extension
import Definitions.Def_OAI_Geometry_Arnold_Deformation
import Definitions.Def_OAI_Geometry_Arnold_Exterior
import Definitions.Def_OAI_Geometry_Arnold_Homotopy
import Definitions.Def_OAI_Geometry_Arnold_Volume
import Definitions.Def_OAI_Geometry_Arnold_Obstruction
import Definitions.Def_OAI_Geometry_Arnold_ThreePoints
import Definitions.Def_OAI_Geometry_Arnold_Factors
import Definitions.Def_OAI_Geometry_Arnold_Field
import Definitions.Def_OAI_Geometry_Arnold_CompactField
import Definitions.Def_OAI_Geometry_Arnold_Midpoint
import Definitions.Def_OAI_Geometry_Arnold_MidpointGeometry

namespace OAI

noncomputable section
open scoped BigOperators ContDiff
open scoped Topology NNReal
open Set Filter

namespace ArnoldCounterexample.Construction
open ArnoldCounterexample.Quadric ArnoldCounterexample.Field
open scoped ContDiff Topology NNReal
open Set Filter

def constant : ℝ≥0 := vectorField_lipschitz.choose
lemma lipschitz : LipschitzWith constant vectorField := vectorField_lipschitz.choose_spec

def epsilon : ℝ := 1 / (100 * ((constant:ℝ)+1))
lemma epsilon_pos : 0 < epsilon := by unfold epsilon; positivity

def parameter (t : ℝ) : ℝ := epsilon * Real.sin (Real.pi * t / 2)
lemma parameter_smooth : ContDiff ℝ ∞ parameter := by unfold parameter; fun_prop
lemma parameter_zero : parameter 0 = 0 := by simp [parameter]
lemma parameter_small : ∀ t, ‖parameter t‖ * constant < 1/10 := by
  intro t
  have hc : 0 ≤ (constant:ℝ) := constant.coe_nonneg
  have hden : 0 < 100 * ((constant:ℝ)+1) := by positivity
  have he : epsilon * (constant:ℝ) < 1/100 := by
    unfold epsilon
    rw [one_div_mul_eq_div, div_lt_iff₀ hden]
    linarith
  have hb : ‖parameter t‖ ≤ epsilon := by
    rw [parameter, norm_mul, Real.norm_eq_abs, abs_of_pos epsilon_pos, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) epsilon_pos.le).trans_eq (mul_one _)
  exact lt_trans (lt_of_le_of_lt (mul_le_mul_of_nonneg_right hb hc) he) (by norm_num)
lemma parameter_contract : ∀ t, ‖parameter t‖ * constant < 1 :=
  fun t ↦ lt_trans (parameter_small t) (by norm_num)

def center : ℝ × CV → CV := Midpoint.resolvent vectorField lipschitz parameter parameter_contract
def forwardMid : ℝ × CV → CV := Midpoint.step vectorField lipschitz parameter parameter_contract
def backwardMid : ℝ × CV → CV :=
  Midpoint.step vectorField lipschitz (fun t ↦ -parameter t) (Midpoint.neg_small parameter_contract)
def midHamiltonian : ℝ × CV → ℝ :=
  Midpoint.hamiltonian vectorField lipschitz parameter parameter_contract potential

lemma forwardMid_smooth : ContDiff ℝ ∞ forwardMid :=
  Midpoint.step_smooth _ lipschitz vectorField_smooth _ _ parameter_smooth
lemma backwardMid_smooth : ContDiff ℝ ∞ backwardMid :=
  Midpoint.step_smooth _ lipschitz vectorField_smooth _ _ parameter_smooth.neg
lemma midHamiltonian_smooth : ContDiff ℝ ∞ midHamiltonian :=
  Midpoint.hamiltonian_smooth _ lipschitz vectorField_smooth _ _ parameter_smooth _ potential_smooth

lemma forwardMid_preserves (t : ℝ) (z : UnitQuadric) : IsUnitQuadric (forwardMid (t,z)) :=
  midpoint_preserves lipschitz parameter parameter_contract t z
lemma backwardMid_preserves (t : ℝ) (z : UnitQuadric) : IsUnitQuadric (backwardMid (t,z)) :=
  midpoint_preserves lipschitz _ (Midpoint.neg_small parameter_contract) t z

lemma center_phase_general (τ : ℝ → ℝ) (hτ : ∀ t, ‖τ t‖*constant < 1)
    (p : ℝ × CV) (c : ℂ) (hc : Complex.normSq c = 1) :
    Midpoint.resolvent vectorField lipschitz τ hτ (p.1,c•p.2) =
      c • Midpoint.resolvent vectorField lipschitz τ hτ p := by
  exact Midpoint.resolvent_symmetry _ lipschitz τ hτ (c • (LinearMap.id : CV →ₗ[ℝ] CV))
    (fun z ↦ vectorField_phase c hc z) p

lemma forwardMid_phase (p : ℝ × CV) (c : ℂ) (hc : Complex.normSq c = 1) :
    forwardMid (p.1,c•p.2) = c • forwardMid p := by
  simp only [forwardMid, Midpoint.step, center_phase_general _ _ p c hc, smul_sub, smul_comm c]
lemma backwardMid_phase (p : ℝ × CV) (c : ℂ) (hc : Complex.normSq c = 1) :
    backwardMid (p.1,c•p.2) = c • backwardMid p := by
  simp only [backwardMid, Midpoint.step, center_phase_general _ _ p c hc, smul_sub, smul_comm c]
lemma midHamiltonian_phase (p : ℝ × CV) (c : ℂ) (hc : Complex.normSq c = 1) :
    midHamiltonian (p.1,c•p.2) = midHamiltonian p := by
  simp only [midHamiltonian, Midpoint.hamiltonian, center_phase_general _ _ p c hc, potential_phase c hc]

lemma backward_forward (p : ℝ × CV) : backwardMid (p.1,forwardMid p) = p.2 :=
  Midpoint.step_inverse _ lipschitz parameter parameter_contract p
lemma forward_backward (p : ℝ × CV) : forwardMid (p.1,backwardMid p) = p.2 := by
  simpa only [neg_neg, forwardMid, backwardMid] using Midpoint.step_inverse _ lipschitz (fun t ↦ -parameter t)
    (Midpoint.neg_small parameter_contract) p
lemma forwardMid_start (z : CV) : forwardMid (0,z) = z :=
  Midpoint.step_zero _ lipschitz _ _ 0 parameter_zero z

lemma center_bound (t : ℝ) (z : UnitQuadric) : normSquared (center (t,z)) ∈ Ioo (1/2:ℝ) 2 :=
  ⟨center_norm_gt_half lipschitz _ _ parameter_small t z,
    lt_of_le_of_lt (center_norm_le_one lipschitz _ _ t z) (by norm_num)⟩

lemma mid_equation (t : ℝ) (z : UnitQuadric) (v : CV) :
    omega (deriv (fun s ↦ forwardMid (s,z)) t) v =
      fderiv ℝ (fun w ↦ midHamiltonian (t,w)) (forwardMid (t,z)) v := by
  simpa only [forwardMid, midHamiltonian, symplectic_apply] using Midpoint.step_hamiltonian_equation symplectic symplectic_skew _ lipschitz vectorField_smooth
    parameter parameter_contract parameter_smooth potential potential_smooth (t,z)
    (vectorField_hamiltonian (lt_trans (center_bound t z).2 (by norm_num))) v

end ArnoldCounterexample.Construction

end

end OAI


