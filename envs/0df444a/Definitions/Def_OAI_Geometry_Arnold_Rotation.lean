-- Prove2me | Definitions.Def_OAI_Geometry_Arnold_Rotation
-- name    : OAI_Geometry_Arnold_Rotation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T08:23:46.477192+00:00
-- url     : https://prove2.me/theorems/b8202e64-0f83-44f3-98e8-67cbcf50829c
-- title:
--   A Hamiltonian rotation path from the identity to the coordinate involution of $Q_3$
-- statement:
--   Write $q(z)=\sum_{j=0}^4z_j^2$ and $|z|^2=\sum_j|z_j|^2$ for $z\in\mathbb{C}^5$. The quadric is $Q_3=\{[z]\in\mathbb{CP}^4:q(z)=0\}$. Its points are represented by unit isotropic vectors $z$, i.e. $|z|^2=1$ and $q(z)=0$, which form the unit quadric $S$, and $\pi:S\to Q_3$ is the projection $z\mapsto[z]$. A vector $v$ is horizontal at $z$ if $\sum_j\bar z_jv_j=0$ and $\sum_jz_jv_j=0$. The form $\omega(u,v)=2\operatorname{Im}\sum_j\bar u_jv_j$ is the Fubini–Study form on horizontal vectors.
--
--   1. **Double rotation.** For $c,s\in\mathbb{R}$,
--   $$
--   R_{c,s}(z)=\bigl(z_0,\ cz_1-sz_2,\ sz_1+cz_2,\ cz_3-sz_4,\ sz_3+cz_4\bigr).
--   $$
--   When $c^2+s^2=1$ it preserves $q$ and $|z|^2$, and $R_{c,-s}$ is its inverse. It always commutes with complex scalars. $R_{1,0}=\mathrm{id}$, and $R_{-1,0}$ is the involution $z\mapsto(z_0,-z_1,\dots,-z_4)$.
--   2. **Rotation path.** $F(t,z)=R_{\cos\pi t,\sin\pi t}(z)$. It is smooth on $\mathbb{R}\times\mathbb{C}^5$, preserves the unit quadric, and has inverse $F(-t,\cdot)$. It starts at the identity ($t=0$), ends at the involution ($t=1$), and commutes with complex scalars.
--   3. **Generator and Hamiltonian.** The vector field $X(z)=\pi\,(0,-z_2,z_1,-z_4,z_3)$ and the smooth function
--   $$
--   H(z)=2\pi\bigl(\operatorname{Re}z_1\operatorname{Im}z_2-\operatorname{Im}z_1\operatorname{Re}z_2+\operatorname{Re}z_3\operatorname{Im}z_4-\operatorname{Im}z_3\operatorname{Re}z_4\bigr).
--   $$
--   $H(az)=|a|^2H(z)$, its real derivative is given explicitly, and for all $z,v$
--   $$
--   \omega\bigl(X(z),v\bigr)=dH(z)[v],\qquad \partial_tF(t,z)=X\bigl(F(t,z)\bigr).
--   $$
--
--   Together these exhibit the coordinate involution of $Q_3$ as the time-one map of a Hamiltonian flow. Here $\omega(u,v)=2\operatorname{Im}\sum_j\bar u_jv_j$, and the Hamiltonian equation is $\iota_X\omega=dH$.
--
--   **Formalization Note** `realCoord j` and `imCoord j` are the real-linear coordinate functionals, and `rotationHamiltonianDiff z` is the derivative of $H$ at $z$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/Arnold/Rotation.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/Arnold/Rotation.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ArnoldCounterexample mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ArnoldCounterexample
import Definitions.Def_OAI_Geometry_Arnold_Involution
import Definitions.Def_OAI_Geometry_Arnold_Projective

namespace OAI

noncomputable section
open scoped BigOperators ContDiff

namespace ArnoldCounterexample.Quadric

/-- Two simultaneous identical planar rotations. -/
def rotation (c s : ℝ) (z : CV) : CV :=
  ![z 0, (c : ℂ) * z 1 - (s : ℂ) * z 2, (s : ℂ) * z 1 + (c : ℂ) * z 2,
    (c : ℂ) * z 3 - (s : ℂ) * z 4, (s : ℂ) * z 3 + (c : ℂ) * z 4]

lemma rotation_quadricPolynomial (c s : ℝ) (z : CV) (hcs : c ^ 2 + s ^ 2 = 1) :
    quadricPolynomial (rotation c s z) = quadricPolynomial z := by
  have hc : (c : ℂ) ^ 2 + (s : ℂ) ^ 2 = 1 := by exact_mod_cast hcs
  simp [quadricPolynomial, rotation, Fin.sum_univ_succ]
  linear_combination (z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2 + z 4 ^ 2) * hc

lemma rotation_normSquared (c s : ℝ) (z : CV) (hcs : c ^ 2 + s ^ 2 = 1) :
    normSquared (rotation c s z) = normSquared z := by
  simp [normSquared, rotation, Fin.sum_univ_succ,
    Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  linear_combination
    ((z 1).re ^ 2 + (z 1).im ^ 2 + (z 2).re ^ 2 + (z 2).im ^ 2 +
     (z 3).re ^ 2 + (z 3).im ^ 2 + (z 4).re ^ 2 + (z 4).im ^ 2) * hcs

lemma rotation_inverse (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) (z : CV) :
    rotation c (-s) (rotation c s z) = z := by
  have hc : (c : ℂ) ^ 2 + (s : ℂ) ^ 2 = 1 := by exact_mod_cast hcs
  funext j
  fin_cases j <;> dsimp [rotation]
  all_goals simp only [Complex.ofReal_neg]
  · linear_combination z 1 * hc
  · linear_combination z 2 * hc
  · linear_combination z 3 * hc
  · linear_combination z 4 * hc

lemma rotation_phase (c s : ℝ) (a : ℂ) (z : CV) :
    rotation c s (a • z) = a • rotation c s z := by
  funext j
  fin_cases j <;> simp [rotation] <;> ring

@[simp] lemma rotation_start (z : CV) : rotation 1 0 z = z := by
  funext j
  fin_cases j <;> simp [rotation]

@[simp] lemma rotation_finish (z : CV) : rotation (-1) 0 z = involutionLinear z := by
  funext j
  fin_cases j <;> simp [rotation]

@[fun_prop] lemma contDiff_ofReal (n : WithTop ℕ∞) : ContDiff ℝ n Complex.ofReal :=
  Complex.ofRealCLM.contDiff

@[fun_prop] lemma contDiff_re (n : WithTop ℕ∞) : ContDiff ℝ n Complex.re :=
  Complex.reCLM.contDiff

@[fun_prop] lemma contDiff_im (n : WithTop ℕ∞) : ContDiff ℝ n Complex.im :=
  Complex.imCLM.contDiff

def rotationPath (p : ℝ × CV) : CV := rotation (Real.cos (Real.pi * p.1))
  (Real.sin (Real.pi * p.1)) p.2

lemma rotationPath_smooth : ContDiff ℝ ∞ rotationPath := by
  unfold rotationPath rotation
  apply contDiff_pi.mpr
  intro j
  fin_cases j <;> dsimp <;> fun_prop

lemma rotationPath_preserves (t : ℝ) (z : UnitQuadric) :
    IsUnitQuadric (rotationPath (t, z)) := by
  have hcs : Real.cos (Real.pi * t) ^ 2 + Real.sin (Real.pi * t) ^ 2 = 1 :=
    Real.cos_sq_add_sin_sq _
  exact ⟨(rotation_normSquared _ _ _ hcs).trans z.property.1,
    (rotation_quadricPolynomial _ _ _ hcs).trans z.property.2⟩

lemma rotationPath_inverse (t : ℝ) (z : CV) :
    rotationPath (-t, rotationPath (t, z)) = z := by
  simpa only [rotationPath, mul_neg, Real.cos_neg, Real.sin_neg] using
    rotation_inverse _ _ (Real.cos_sq_add_sin_sq (Real.pi * t)) z

@[simp] lemma rotationPath_start (z : CV) : rotationPath (0, z) = z := by
  simp [rotationPath]

@[simp] lemma rotationPath_finish (z : CV) : rotationPath (1, z) = involutionLinear z := by
  simp [rotationPath]

lemma rotationPath_phase (t : ℝ) (a : ℂ) (z : CV) :
    rotationPath (t, a • z) = a • rotationPath (t, z) := rotation_phase _ _ _ _

end ArnoldCounterexample.Quadric

namespace ArnoldCounterexample.Quadric

/-- The ambient vector field generating the prescribed rotations. -/
def rotationGenerator (z : CV) : CV :=
  ![0, -(Real.pi : ℂ) * z 2, (Real.pi : ℂ) * z 1,
    -(Real.pi : ℂ) * z 4, (Real.pi : ℂ) * z 3]

/-- Minus alpha(Z), exactly the sign convention i_X omega = dH. -/
def rotationHamiltonian (z : CV) : ℝ :=
  2 * Real.pi * ((z 1).re * (z 2).im - (z 1).im * (z 2).re +
    (z 3).re * (z 4).im - (z 3).im * (z 4).re)

lemma rotationHamiltonian_smooth : ContDiff ℝ ∞ rotationHamiltonian := by
  unfold rotationHamiltonian
  fun_prop

lemma rotationHamiltonian_smul (a : ℂ) (z : CV) :
    rotationHamiltonian (a • z) = Complex.normSq a * rotationHamiltonian z := by
  simp only [rotationHamiltonian, Pi.smul_apply, smul_eq_mul, Complex.mul_re,
    Complex.mul_im, Complex.normSq_apply]
  ring

def realCoord (j : Fin 5) : CV →L[ℝ] ℝ :=
  Complex.reCLM.comp (ContinuousLinearMap.proj j)

def imagCoord (j : Fin 5) : CV →L[ℝ] ℝ :=
  Complex.imCLM.comp (ContinuousLinearMap.proj j)

@[simp] lemma realCoord_apply (j : Fin 5) (z : CV) : realCoord j z = (z j).re := rfl
@[simp] lemma imagCoord_apply (j : Fin 5) (z : CV) : imagCoord j z = (z j).im := rfl

def rotationHamiltonianDiff (z : CV) : CV →L[ℝ] ℝ :=
  (2 * Real.pi) • ((z 1).re • imagCoord 2 + (z 2).im • realCoord 1 -
    ((z 1).im • realCoord 2 + (z 2).re • imagCoord 1) +
    ((z 3).re • imagCoord 4 + (z 4).im • realCoord 3) -
    ((z 3).im • realCoord 4 + (z 4).re • imagCoord 3))

lemma rotationHamiltonian_hasFDerivAt (z : CV) :
    HasFDerivAt rotationHamiltonian (rotationHamiltonianDiff z) z := by
  have hr (j : Fin 5) := (realCoord j).hasFDerivAt (x := z)
  have hi (j : Fin 5) := (imagCoord j).hasFDerivAt (x := z)
  have h := ((((hr 1).mul (hi 2)).sub ((hi 1).mul (hr 2))).add
    ((hr 3).mul (hi 4))).sub ((hi 3).mul (hr 4))
  convert! h.const_mul (2 * Real.pi) using 1

lemma rotationHamiltonian_equation (z v : CV) :
    omega (rotationGenerator z) v = fderiv ℝ rotationHamiltonian z v := by
  rw [(rotationHamiltonian_hasFDerivAt z).fderiv]
  simp [omega, rotationGenerator, rotationHamiltonianDiff, Fin.sum_univ_succ,
    Complex.mul_re, Complex.mul_im]
  ring

end ArnoldCounterexample.Quadric

namespace ArnoldCounterexample.Quadric

lemma rotationPath_hasDerivAt (t : ℝ) (z : CV) :
    HasDerivAt (fun s : ℝ ↦ rotationPath (s, z))
      (rotationGenerator (rotationPath (t, z))) t := by
  have hc := ((hasDerivAt_id t).const_mul Real.pi).cos.ofReal_comp
  have hs := ((hasDerivAt_id t).const_mul Real.pi).sin.ofReal_comp
  apply hasDerivAt_pi.mpr
  intro j
  fin_cases j <;> dsimp [rotationPath, rotation, rotationGenerator]
  · exact hasDerivAt_const t (z 0)
  · convert! (hc.mul_const (z 1)).sub (hs.mul_const (z 2)) using 1
    simp only [id_eq, mul_one, Complex.ofReal_neg, Complex.ofReal_mul]
    ring
  · convert! (hs.mul_const (z 1)).add (hc.mul_const (z 2)) using 1
    simp only [id_eq, mul_one, Complex.ofReal_neg, Complex.ofReal_mul]
    ring
  · convert! (hc.mul_const (z 3)).sub (hs.mul_const (z 4)) using 1
    simp only [id_eq, mul_one, Complex.ofReal_neg, Complex.ofReal_mul]
    ring
  · convert! (hs.mul_const (z 3)).add (hc.mul_const (z 4)) using 1
    simp only [id_eq, mul_one, Complex.ofReal_neg, Complex.ofReal_mul]
    ring

end ArnoldCounterexample.Quadric

end

end OAI


