-- Prove2me | Definitions.Def_AutomorphicForm_ArchDerivCasimir
-- name    : AutomorphicForm_ArchDerivCasimir
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/7b6d9f16-d9e4-536d-bd2b-0b23bdad587a
-- title:
--   Archimedean flows, invariant derivatives and Casimir at real places
-- statement:
--   Two groups of definitions are made. First, for an archimedean parameter in the sense of [`LanglandsTunnell.RealArchParam`](../def/LanglandsTunnell_ArchParam.html#L9), `laplaceEigenvalue` assigns a complex number: $1/4-((u_1-u_2)/2)^2$ to a principal parameter `principal u₁ a₁ u₂ a₂`, and $(1-k^2)/4$ to a discrete parameter `discrete u k`; the two accompanying lemmas record these values.
--
--   Second, let $F$ be a number field and $w$ a real infinite place, with the isomorphism $F_w\cong\mathbb{R}$ given by `ringEquivRealOfIsReal`. Then `archRealGLAt hw` is the monoid homomorphism from $\mathrm{GL}_2(\mathbb{R})$ to `AdelicGL2`, obtained by transporting entries along $\mathbb{R}\cong F_w$ and applying the inclusion of $\mathrm{GL}_2(F_w)$ that is the identity at all other infinite places and at all finite places; `archRealProjAt hw` is the homomorphism in the reverse direction given by taking the infinite part, its component at $w$ and transporting back, and it is a left inverse of `archRealGLAt hw`. The total map `archRealLiftAt hw` sends an array $e:\mathrm{Fin}\,2\to\mathrm{Fin}\,2\to\mathbb{R}$ to `archRealGLAt hw` of the corresponding invertible matrix when $\det e\ne 0$, and to $1$ otherwise; $\{e:\det e\ne 0\}$ is open. A function $\varphi$ on `AdelicGL2` satisfies `IsArchSmoothAt hw` when, for every $g$, the map sending $e$ to $\varphi(g\cdot x)$, where $x$ is `archRealLiftAt hw e`, is $C^\infty$ on that open set. The three-element type `ArchDir` indexes the directions $H$, $E$, $F^-$; `splitTorusGL2` at $t$ is $\mathrm{diag}(e^t,e^{-t})$ and `lowerUnipotentGL2` at $x$ is $\begin{pmatrix}1&0\\x&1\end{pmatrix}$, defined with their identity and one-parameter-group laws, and together with the upper unipotent `unipotentGL2` they give `archFlowMatrix`, pushed to `archFlowAt hw d t` inside `AdelicGL2`; `archDirMatrix` gives the corresponding $\mathfrak{sl}_2$ generators $\mathrm{diag}(1,-1)$, $e_{12}$, $e_{21}$, each being the derivative of its flow at $t=0$ entrywise. Then `archDerivAt hw d φ` sends $g$ to $\tfrac{d}{dt}\varphi(g\cdot a(t))|_{t=0}$, where $a(t)$ is `archFlowAt hw d t`, using Mathlib's `deriv` (hence $0$ where the curve fails to be differentiable), and `archCasimirAt hw` sends $\varphi$ to
--   $$-\bigl(\tfrac14 D_HD_H-\tfrac12 D_H+D_ED_{F^-}\bigr)\varphi .$$
--   The remaining lemmas record: vanishing of both operators on constants; stability of `IsArchSmoothAt` under sums, complex scalar multiples, negation, subtraction, under each `archDerivAt` and under `archCasimirAt`, and under left translation and under right translation by an element whose infinite part is trivial; additivity of `archDerivAt` and `archCasimirAt` for smooth arguments and homogeneity for arbitrary arguments; differentiability at $0$ along each flow; commutation of `archDerivAt` and `archCasimirAt` with left translation and with right translation by elements of trivial infinite part; and that an element of `AdelicGL2` is determined by its infinite and finite components.
--
--   **Relation to Mathlib.** Mathlib supplies the adele ring, general linear groups, `deriv` and `ContDiffOn` used here, but has no notion of smoothness along archimedean directions, invariant differentiation or a Casimir operator for functions on an adelic $\mathrm{GL}_2$; those are the project's own. The upper unipotent one-parameter subgroup `unipotentGL2` is taken from another module of the project, while the split torus and lower unipotent subgroups are introduced here.
--
--   **Where it is used.** These operators supply the archimedean side of the definition of automorphic forms on $\mathrm{GL}_2$ over a number field: smoothness at a real place, and the Casimir eigenvalue condition, whose prescribed eigenvalue is the `laplaceEigenvalue` of the archimedean parameter. This is the setting in which the Langlands–Tunnell input to the modularity argument is formulated.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_ArchDerivCasimir.lean

import Definitions.Def_AutomorphicForm_ArchType
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_LanglandsTunnell_ArchParam
import Definitions.Def_AutomorphicForm_ConstantTerm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell.RealArchParam

def laplaceEigenvalue : RealArchParam → ℂ
  | principal u₁ _ u₂ _ => 1 / 4 - ((u₁ - u₂) / 2) ^ 2
  | discrete _ k _ => (1 - (k : ℂ) ^ 2) / 4

theorem laplaceEigenvalue_principal (u₁ : ℂ) (a₁ : ZMod 2) (u₂ : ℂ) (a₂ : ZMod 2) :
    laplaceEigenvalue (principal u₁ a₁ u₂ a₂) = 1 / 4 - ((u₁ - u₂) / 2) ^ 2 :=
  rfl

theorem laplaceEigenvalue_discrete (u : ℂ) (k : ℕ) (hk : 1 ≤ k) :
    laplaceEigenvalue (discrete u k hk) = (1 - (k : ℂ) ^ 2) / 4 :=
  rfl

end LanglandsTunnell.RealArchParam

namespace AutomorphicForm

open NumberField NumberField.InfinitePlace.Completion Matrix

variable (F : Type) [Field F] [NumberField F]

section RealPlaceTransport

variable {F}

def archRealGLAt {w : InfinitePlace F} (hw : w.IsReal) : GL (Fin 2) ℝ →* AdelicGL2 (𝓞 F) F :=
  (adelicArchGLInclAt F w).comp (glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm).toMonoidHom

def archRealLiftAt {w : InfinitePlace F} (hw : w.IsReal) (e : Fin 2 → Fin 2 → ℝ) : AdelicGL2 (𝓞 F) F :=
  if h : (Matrix.of e).det ≠ 0 then archRealGLAt hw (GeneralLinearGroup.mkOfDetNeZero (Matrix.of e) h)
  else 1

theorem archRealLiftAt_of_det_ne_zero {w : InfinitePlace F} (hw : w.IsReal) {e : Fin 2 → Fin 2 → ℝ}
    (h : (Matrix.of e).det ≠ 0) :
    archRealLiftAt hw e = archRealGLAt hw (GeneralLinearGroup.mkOfDetNeZero (Matrix.of e) h) :=
  dif_pos h

theorem isOpen_setOf_det_ne_zero :
    IsOpen {e : Fin 2 → Fin 2 → ℝ | (Matrix.of e).det ≠ 0} :=
  (isClosed_singleton.preimage (continuous_id.matrix_det)).isOpen_compl

def IsArchSmoothAt {w : InfinitePlace F} (hw : w.IsReal) (φ : AdelicGL2 (𝓞 F) F → ℂ) : Prop :=
  ∀ g : AdelicGL2 (𝓞 F) F,
    ContDiffOn ℝ (⊤ : ℕ∞) (fun e : Fin 2 → Fin 2 → ℝ => φ (g * archRealLiftAt hw e))
      {e | (Matrix.of e).det ≠ 0}

theorem isArchSmoothAt_const {w : InfinitePlace F} (hw : w.IsReal) (c : ℂ) :
    IsArchSmoothAt hw (fun _ => c) :=
  fun _ => contDiffOn_const

end RealPlaceTransport

section Flows

variable {F}

inductive ArchDir where
  | H : ArchDir
  | E : ArchDir
  | Fm : ArchDir

def lowerUnipotentGL2 {R : Type*} [CommRing R] (x : R) : GL (Fin 2) R where
  val := !![1, 0; x, 1]
  inv := !![1, 0; -x, 1]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem lowerUnipotentGL2_coe {R : Type*} [CommRing R] (x : R) :
    (lowerUnipotentGL2 x : Matrix (Fin 2) (Fin 2) R) = !![1, 0; x, 1] :=
  rfl

theorem lowerUnipotentGL2_zero {R : Type*} [CommRing R] : lowerUnipotentGL2 (0 : R) = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [lowerUnipotentGL2]

theorem lowerUnipotentGL2_add {R : Type*} [CommRing R] (x y : R) :
    lowerUnipotentGL2 (x + y) = lowerUnipotentGL2 x * lowerUnipotentGL2 y := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [lowerUnipotentGL2, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

def splitTorusGL2 (t : ℝ) : GL (Fin 2) ℝ where
  val := !![Real.exp t, 0; 0, Real.exp (-t)]
  inv := !![Real.exp (-t), 0; 0, Real.exp t]
  val_inv := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, ← Real.exp_add]
  inv_val := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, ← Real.exp_add]

theorem splitTorusGL2_coe (t : ℝ) :
    (splitTorusGL2 t : Matrix (Fin 2) (Fin 2) ℝ) = !![Real.exp t, 0; 0, Real.exp (-t)] :=
  rfl

theorem splitTorusGL2_zero : splitTorusGL2 0 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [splitTorusGL2]

theorem splitTorusGL2_add (s t : ℝ) : splitTorusGL2 (s + t) = splitTorusGL2 s * splitTorusGL2 t := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [splitTorusGL2, Matrix.mul_apply, Fin.sum_univ_two, Real.exp_add]; ring

def archFlowMatrix : ArchDir → ℝ → GL (Fin 2) ℝ
  | .H, t => splitTorusGL2 t
  | .E, t => unipotentGL2 t
  | .Fm, t => lowerUnipotentGL2 t

theorem archFlowMatrix_zero (d : ArchDir) : archFlowMatrix d 0 = 1 := by
  cases d
  · exact splitTorusGL2_zero
  · exact unipotentGL2_zero
  · exact lowerUnipotentGL2_zero

theorem archFlowMatrix_add (d : ArchDir) (s t : ℝ) :
    archFlowMatrix d (s + t) = archFlowMatrix d s * archFlowMatrix d t := by
  cases d
  · exact splitTorusGL2_add s t
  · exact unipotentGL2_add s t
  · exact lowerUnipotentGL2_add s t

def archFlowAt {w : InfinitePlace F} (hw : w.IsReal) (d : ArchDir) (t : ℝ) : AdelicGL2 (𝓞 F) F :=
  archRealGLAt hw (archFlowMatrix d t)

theorem archFlowAt_zero {w : InfinitePlace F} (hw : w.IsReal) (d : ArchDir) : archFlowAt hw d 0 = 1 := by
  rw [archFlowAt, archFlowMatrix_zero, map_one]

theorem archFlowAt_add {w : InfinitePlace F} (hw : w.IsReal) (d : ArchDir) (s t : ℝ) :
    archFlowAt hw d (s + t) = archFlowAt hw d s * archFlowAt hw d t := by
  rw [archFlowAt, archFlowMatrix_add, map_mul]; rfl

def archDerivAt {w : InfinitePlace F} (hw : w.IsReal) (d : ArchDir) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    AdelicGL2 (𝓞 F) F → ℂ :=
  fun g => deriv (fun t : ℝ => φ (g * archFlowAt hw d t)) 0

def archCasimirAt {w : InfinitePlace F} (hw : w.IsReal) (φ : AdelicGL2 (𝓞 F) F → ℂ) : AdelicGL2 (𝓞 F) F → ℂ :=
  -((1 / 4 : ℂ) • archDerivAt hw .H (archDerivAt hw .H φ) - (1 / 2 : ℂ) • archDerivAt hw .H φ +
    archDerivAt hw .E (archDerivAt hw .Fm φ))

theorem archDerivAt_const {w : InfinitePlace F} (hw : w.IsReal) (d : ArchDir) (c : ℂ) :
    archDerivAt hw d (fun _ => c) = fun _ => 0 := by
  funext g
  simp [archDerivAt]

theorem archCasimirAt_const {w : InfinitePlace F} (hw : w.IsReal) (c : ℂ) :
    archCasimirAt hw (fun _ => c) = fun _ => 0 := by
  funext g
  simp [archCasimirAt, archDerivAt_const]

def archDirMatrix : ArchDir → Matrix (Fin 2) (Fin 2) ℝ
  | .H => !![1, 0; 0, -1]
  | .E => !![0, 1; 0, 0]
  | .Fm => !![0, 0; 1, 0]

theorem hasDerivAt_archFlowMatrix_apply (d : ArchDir) (i j : Fin 2) :
    HasDerivAt (fun t : ℝ => (archFlowMatrix d t : Matrix (Fin 2) (Fin 2) ℝ) i j) (archDirMatrix d i j) 0 := by
  cases d <;> fin_cases i <;> fin_cases j <;>
    simp only [archFlowMatrix, archDirMatrix, splitTorusGL2_coe, unipotentGL2_coe, lowerUnipotentGL2_coe,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Fin.zero_eta, Fin.mk_one, Fin.isValue] <;>
    first
      | exact hasDerivAt_const _ _
      | exact hasDerivAt_id _
      | simpa using Real.hasDerivAt_exp 0
      | exact ((Real.hasDerivAt_exp (-(0 : ℝ))).comp (0 : ℝ) (hasDerivAt_neg (0 : ℝ))).congr_deriv (by simp)

theorem archRealLiftAt_mul_archRealGLAt {w : InfinitePlace F} (hw : w.IsReal) {e : Fin 2 → Fin 2 → ℝ}
    (h : (Matrix.of e).det ≠ 0) (m : GL (Fin 2) ℝ) :
    archRealLiftAt hw e * archRealGLAt hw m =
      archRealLiftAt hw (Matrix.of.symm (Matrix.of e * (m : Matrix (Fin 2) (Fin 2) ℝ))) := by
  have hm : ((m : Matrix (Fin 2) (Fin 2) ℝ)).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 m.isUnit).ne_zero
  have h' : (Matrix.of (Matrix.of.symm (Matrix.of e * (m : Matrix (Fin 2) (Fin 2) ℝ)))).det ≠ 0 := by
    rw [Equiv.apply_symm_apply, Matrix.det_mul]
    exact mul_ne_zero h hm
  rw [archRealLiftAt_of_det_ne_zero hw h, archRealLiftAt_of_det_ne_zero hw h', ← map_mul]
  congr 1
  ext i j
  simp [GeneralLinearGroup.mkOfDetNeZero]

theorem contDiff_of_symm_mul_const (A : Matrix (Fin 2) (Fin 2) ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) fun e : Fin 2 → Fin 2 → ℝ => (Matrix.of.symm (Matrix.of e * A) : Fin 2 → Fin 2 → ℝ) := by
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  simp only [Matrix.of_symm_apply, Matrix.mul_apply, Matrix.of_apply]
  exact ContDiff.sum fun k _ =>
    ((contDiff_apply ℝ ℝ k).comp (contDiff_apply ℝ (Fin 2 → ℝ) i)).mul contDiff_const

theorem hasDerivAt_of_symm_mul_archFlowMatrix (e : Fin 2 → Fin 2 → ℝ) (d : ArchDir) :
    HasDerivAt
      (fun t : ℝ => (Matrix.of.symm (Matrix.of e * (archFlowMatrix d t : Matrix (Fin 2) (Fin 2) ℝ)) :
        Fin 2 → Fin 2 → ℝ))
      (Matrix.of.symm (Matrix.of e * archDirMatrix d)) 0 := by
  rw [hasDerivAt_pi]
  intro i
  rw [hasDerivAt_pi]
  intro j
  simp only [Matrix.of_symm_apply, Matrix.mul_apply, Matrix.of_apply]
  exact HasDerivAt.fun_sum fun k _ => (hasDerivAt_archFlowMatrix_apply d k j).const_mul (e i k)

theorem of_symm_mul_archFlowMatrix_zero (e : Fin 2 → Fin 2 → ℝ) (d : ArchDir) :
    (Matrix.of.symm (Matrix.of e * (archFlowMatrix d 0 : Matrix (Fin 2) (Fin 2) ℝ)) : Fin 2 → Fin 2 → ℝ) = e := by
  rw [archFlowMatrix_zero, Units.val_one, mul_one, Equiv.symm_apply_apply]

theorem IsArchSmoothAt.archDerivAt {w : InfinitePlace F} {hw : w.IsReal} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAt hw φ) (d : ArchDir) : IsArchSmoothAt hw (archDerivAt hw d φ) := by
  intro g
  have hΦ := hφ g
  have hopen := isOpen_setOf_det_ne_zero
  refine contDiffOn_infty.2 fun n => ?_
  refine ((hΦ.fderiv_of_isOpen hopen (by exact_mod_cast le_top)).clm_apply
    ((contDiff_of_symm_mul_const (archDirMatrix d)).contDiffOn.of_le (by exact_mod_cast le_top))).congr ?_
  intro e he
  have hdiff : HasFDerivAt (fun e' => φ (g * archRealLiftAt hw e'))
      (fderiv ℝ (fun e' => φ (g * archRealLiftAt hw e')) e)
      (Matrix.of.symm (Matrix.of e * (archFlowMatrix d 0 : Matrix (Fin 2) (Fin 2) ℝ))) := by
    rw [of_symm_mul_archFlowMatrix_zero]
    exact ((hΦ.contDiffAt (hopen.mem_nhds he)).differentiableAt (by simp)).hasFDerivAt
  have hfun : (fun t : ℝ => φ (g * archRealLiftAt hw e * archFlowAt hw d t)) =
      fun t : ℝ => φ (g * archRealLiftAt hw
        (Matrix.of.symm (Matrix.of e * (archFlowMatrix d t : Matrix (Fin 2) (Fin 2) ℝ)))) := by
    funext t
    rw [archFlowAt, mul_assoc, archRealLiftAt_mul_archRealGLAt hw he]
  show deriv (fun t : ℝ => φ (g * archRealLiftAt hw e * archFlowAt hw d t)) 0 = _
  rw [hfun]
  simpa only [Function.comp_def] using
    (hdiff.comp_hasDerivAt (0 : ℝ) (hasDerivAt_of_symm_mul_archFlowMatrix e d)).deriv

theorem archRealLiftAt_of_symm_one {w : InfinitePlace F} (hw : w.IsReal) :
    archRealLiftAt hw (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ)) = 1 := by
  have hdet : (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ))).det ≠ 0 := by
    rw [Equiv.apply_symm_apply, Matrix.det_one]
    exact one_ne_zero
  rw [archRealLiftAt_of_det_ne_zero hw hdet, ← map_one (archRealGLAt hw)]
  congr 1
  ext i j
  simp [GeneralLinearGroup.mkOfDetNeZero]

theorem IsArchSmoothAt.differentiableAt_flow {w : InfinitePlace F} {hw : w.IsReal} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAt hw φ) (d : ArchDir) (g : AdelicGL2 (𝓞 F) F) :
    DifferentiableAt ℝ (fun t : ℝ => φ (g * archFlowAt hw d t)) 0 := by
  have hopen := isOpen_setOf_det_ne_zero
  have hdet : (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ))).det ≠ 0 := by
    rw [Equiv.apply_symm_apply, Matrix.det_one]
    exact one_ne_zero
  have hdiff : DifferentiableAt ℝ (fun e' => φ (g * archRealLiftAt hw e'))
      (Matrix.of.symm (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ)) *
        (archFlowMatrix d 0 : Matrix (Fin 2) (Fin 2) ℝ))) := by
    rw [of_symm_mul_archFlowMatrix_zero]
    exact ((hφ g).contDiffAt (hopen.mem_nhds hdet)).differentiableAt (by simp)
  have hfun : (fun t : ℝ => φ (g * archFlowAt hw d t)) =
      fun t : ℝ => φ (g * archRealLiftAt hw
        (Matrix.of.symm (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ)) *
          (archFlowMatrix d t : Matrix (Fin 2) (Fin 2) ℝ)))) := by
    funext t
    rw [← archRealLiftAt_mul_archRealGLAt hw hdet, archRealLiftAt_of_symm_one, one_mul, archFlowAt]
  rw [hfun]
  simpa only [Function.comp_def] using
    (hdiff.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_of_symm_mul_archFlowMatrix _ d)).differentiableAt

theorem archDerivAt_add {w : InfinitePlace F} {hw : w.IsReal} {φ ψ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAt hw φ) (hψ : IsArchSmoothAt hw ψ) (d : ArchDir) :
    archDerivAt hw d (φ + ψ) = archDerivAt hw d φ + archDerivAt hw d ψ := by
  funext g
  show deriv (fun t : ℝ => (φ + ψ) (g * archFlowAt hw d t)) 0 =
    deriv (fun t : ℝ => φ (g * archFlowAt hw d t)) 0 + deriv (fun t : ℝ => ψ (g * archFlowAt hw d t)) 0
  simp only [Pi.add_apply]
  exact deriv_fun_add (hφ.differentiableAt_flow d g) (hψ.differentiableAt_flow d g)

theorem archDerivAt_smul {w : InfinitePlace F} (hw : w.IsReal) (d : ArchDir) (c : ℂ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) : archDerivAt hw d (c • φ) = c • archDerivAt hw d φ := by
  funext g
  show deriv (fun t : ℝ => (c • φ) (g * archFlowAt hw d t)) 0 = c • deriv (fun t : ℝ => φ (g * archFlowAt hw d t)) 0
  simp only [Pi.smul_apply, smul_eq_mul]
  exact deriv_const_mul_field c

theorem archCasimirAt_add {w : InfinitePlace F} {hw : w.IsReal} {φ ψ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAt hw φ) (hψ : IsArchSmoothAt hw ψ) :
    archCasimirAt hw (φ + ψ) = archCasimirAt hw φ + archCasimirAt hw ψ := by
  simp only [archCasimirAt, archDerivAt_add hφ hψ, archDerivAt_add (hφ.archDerivAt .H) (hψ.archDerivAt .H),
    archDerivAt_add (hφ.archDerivAt .Fm) (hψ.archDerivAt .Fm)]
  funext g
  simp only [Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem archCasimirAt_smul {w : InfinitePlace F} (hw : w.IsReal) (c : ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    archCasimirAt hw (c • φ) = c • archCasimirAt hw φ := by
  simp only [archCasimirAt, archDerivAt_smul]
  funext g
  simp only [Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem IsArchSmoothAt.add {w : InfinitePlace F} {hw : w.IsReal} {φ ψ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAt hw φ) (hψ : IsArchSmoothAt hw ψ) : IsArchSmoothAt hw (φ + ψ) := by
  intro g
  show ContDiffOn ℝ (⊤ : ℕ∞) (fun e => φ (g * archRealLiftAt hw e) + ψ (g * archRealLiftAt hw e)) _
  exact (hφ g).add (hψ g)

theorem IsArchSmoothAt.smul {w : InfinitePlace F} {hw : w.IsReal} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAt hw φ) (c : ℂ) : IsArchSmoothAt hw (c • φ) := by
  intro g
  show ContDiffOn ℝ (⊤ : ℕ∞) (fun e => c * φ (g * archRealLiftAt hw e)) _
  exact contDiffOn_const.mul (hφ g)

theorem IsArchSmoothAt.neg {w : InfinitePlace F} {hw : w.IsReal} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAt hw φ) : IsArchSmoothAt hw (-φ) := by
  rw [← neg_one_smul ℂ φ]
  exact hφ.smul (-1)

theorem IsArchSmoothAt.sub {w : InfinitePlace F} {hw : w.IsReal} {φ ψ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAt hw φ) (hψ : IsArchSmoothAt hw ψ) : IsArchSmoothAt hw (φ - ψ) := by
  rw [sub_eq_add_neg]
  exact hφ.add hψ.neg

theorem eq_of_glArch_eq_of_glFin_eq {x y : AdelicGL2 (𝓞 F) F}
    (h₁ : AdelicLevel.glArch (𝓞 F) F x = AdelicLevel.glArch (𝓞 F) F y)
    (h₂ : AdelicLevel.glFin (𝓞 F) F x = AdelicLevel.glFin (𝓞 F) F y) : x = y := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  have h₁' := congrArg
    (fun m : GL (Fin 2) (InfiniteAdeleRing F) => (m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j) h₁
  have h₂' := congrArg
    (fun m : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) =>
      (m : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j) h₂
  exact Prod.ext h₁' h₂'

theorem archRealGLAt_mul_comm_of_glArch_eq_one {w : InfinitePlace F} (hw : w.IsReal) (m : GL (Fin 2) ℝ)
    {k : AdelicGL2 (𝓞 F) F} (hk : AdelicLevel.glArch (𝓞 F) F k = 1) :
    archRealGLAt hw m * k = k * archRealGLAt hw m := by
  have hfin : AdelicLevel.glFin (𝓞 F) F (archRealGLAt hw m) = 1 := glFin_adelicArchGLIncl F _
  refine eq_of_glArch_eq_of_glFin_eq ?_ ?_
  · rw [map_mul, map_mul, hk, mul_one, one_mul]
  · rw [map_mul, map_mul, hfin, mul_one, one_mul]

theorem archRealLiftAt_mul_comm_of_glArch_eq_one {w : InfinitePlace F} (hw : w.IsReal) (e : Fin 2 → Fin 2 → ℝ)
    {k : AdelicGL2 (𝓞 F) F} (hk : AdelicLevel.glArch (𝓞 F) F k = 1) :
    archRealLiftAt hw e * k = k * archRealLiftAt hw e := by
  unfold archRealLiftAt
  split_ifs
  · exact archRealGLAt_mul_comm_of_glArch_eq_one hw _ hk
  · rw [one_mul, mul_one]

theorem archFlowAt_mul_comm_of_glArch_eq_one {w : InfinitePlace F} (hw : w.IsReal) (d : ArchDir) (t : ℝ)
    {k : AdelicGL2 (𝓞 F) F} (hk : AdelicLevel.glArch (𝓞 F) F k = 1) :
    archFlowAt hw d t * k = k * archFlowAt hw d t :=
  archRealGLAt_mul_comm_of_glArch_eq_one hw _ hk

theorem IsArchSmoothAt.comp_mul_right {w : InfinitePlace F} {hw : w.IsReal} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAt hw φ) {k : AdelicGL2 (𝓞 F) F} (hk : AdelicLevel.glArch (𝓞 F) F k = 1) :
    IsArchSmoothAt hw fun g => φ (g * k) := by
  intro g
  show ContDiffOn ℝ (⊤ : ℕ∞) (fun e => φ (g * archRealLiftAt hw e * k)) _
  have hfun : (fun e : Fin 2 → Fin 2 → ℝ => φ (g * archRealLiftAt hw e * k)) =
      fun e => φ (g * k * archRealLiftAt hw e) := by
    funext e
    rw [mul_assoc, archRealLiftAt_mul_comm_of_glArch_eq_one hw e hk, ← mul_assoc]
  rw [hfun]
  exact hφ (g * k)

theorem archDerivAt_comp_mul_right {w : InfinitePlace F} (hw : w.IsReal) (d : ArchDir) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    {k : AdelicGL2 (𝓞 F) F} (hk : AdelicLevel.glArch (𝓞 F) F k = 1) :
    archDerivAt hw d (fun g => φ (g * k)) = fun g => archDerivAt hw d φ (g * k) := by
  funext g
  show deriv (fun t : ℝ => φ (g * archFlowAt hw d t * k)) 0 = deriv (fun t : ℝ => φ (g * k * archFlowAt hw d t)) 0
  congr 1
  funext t
  rw [mul_assoc, archFlowAt_mul_comm_of_glArch_eq_one hw d t hk, ← mul_assoc]

theorem archCasimirAt_comp_mul_right {w : InfinitePlace F} (hw : w.IsReal) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    {k : AdelicGL2 (𝓞 F) F} (hk : AdelicLevel.glArch (𝓞 F) F k = 1) :
    archCasimirAt hw (fun g => φ (g * k)) = fun g => archCasimirAt hw φ (g * k) := by
  rw [archCasimirAt, archCasimirAt, archDerivAt_comp_mul_right hw .H φ hk,
    archDerivAt_comp_mul_right hw .H (archDerivAt hw .H φ) hk, archDerivAt_comp_mul_right hw .Fm φ hk,
    archDerivAt_comp_mul_right hw .E (archDerivAt hw .Fm φ) hk]
  funext g
  simp only [Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply]

theorem archRealGLAt_glEquivOfRingEquiv {w : InfinitePlace F} (hw : w.IsReal) (k : GL (Fin 2) w.Completion) :
    archRealGLAt hw (glEquivOfRingEquiv (ringEquivRealOfIsReal hw) k) = adelicArchGLInclAt F w k := by
  show adelicArchGLInclAt F w
    (glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm (glEquivOfRingEquiv (ringEquivRealOfIsReal hw) k)) =
      adelicArchGLInclAt F w k
  congr 1
  ext i j
  rw [glEquivOfRingEquiv_apply_entry, glEquivOfRingEquiv_apply_entry]
  exact congrArg _ ((ringEquivRealOfIsReal hw).symm_apply_apply _)

def archRealProjAt {w : InfinitePlace F} (hw : w.IsReal) : AdelicGL2 (𝓞 F) F →* GL (Fin 2) ℝ :=
  (glEquivOfRingEquiv (ringEquivRealOfIsReal hw)).toMonoidHom.comp
    ((AdelicLevel.archComponent F w).comp (AdelicLevel.glArch (𝓞 F) F))

theorem archRealProjAt_archRealGLAt {w : InfinitePlace F} (hw : w.IsReal) (m : GL (Fin 2) ℝ) :
    archRealProjAt hw (archRealGLAt hw m) = m := by
  have h1 : AdelicLevel.glArch (𝓞 F) F (archRealGLAt hw m) =
      archGLIncl F w (glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm m) :=
    glArch_adelicArchGLIncl F _
  have h2 : AdelicLevel.archComponent F w (AdelicLevel.glArch (𝓞 F) F (archRealGLAt hw m)) =
      glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm m := by
    rw [h1, archComponent_archGLIncl_self]
  show glEquivOfRingEquiv (ringEquivRealOfIsReal hw)
    (AdelicLevel.archComponent F w (AdelicLevel.glArch (𝓞 F) F (archRealGLAt hw m))) = m
  rw [h2]
  ext i j
  rw [glEquivOfRingEquiv_apply_entry, glEquivOfRingEquiv_apply_entry]
  exact (ringEquivRealOfIsReal hw).apply_symm_apply _

theorem IsArchSmoothAt.archCasimirAt {w : InfinitePlace F} {hw : w.IsReal} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAt hw φ) : IsArchSmoothAt hw (archCasimirAt hw φ) := by
  unfold AutomorphicForm.archCasimirAt
  exact (((((hφ.archDerivAt .H).archDerivAt .H).smul _).sub ((hφ.archDerivAt .H).smul _)).add
    ((hφ.archDerivAt .Fm).archDerivAt .E)).neg

theorem IsArchSmoothAt.comp_mul_left {w : InfinitePlace F} {hw : w.IsReal} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAt hw φ) (h : AdelicGL2 (𝓞 F) F) : IsArchSmoothAt hw fun g => φ (h * g) := by
  intro g
  show ContDiffOn ℝ (⊤ : ℕ∞) (fun e => φ (h * (g * archRealLiftAt hw e))) _
  simp only [← mul_assoc]
  exact hφ (h * g)

theorem archDerivAt_comp_mul_left {w : InfinitePlace F} (hw : w.IsReal) (d : ArchDir) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (h : AdelicGL2 (𝓞 F) F) : archDerivAt hw d (fun g => φ (h * g)) = fun g => archDerivAt hw d φ (h * g) := by
  funext g
  show deriv (fun t : ℝ => φ (h * (g * archFlowAt hw d t))) 0 = deriv (fun t : ℝ => φ (h * g * archFlowAt hw d t)) 0
  simp only [mul_assoc]

theorem archCasimirAt_comp_mul_left {w : InfinitePlace F} (hw : w.IsReal) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (h : AdelicGL2 (𝓞 F) F) : archCasimirAt hw (fun g => φ (h * g)) = fun g => archCasimirAt hw φ (h * g) := by
  rw [archCasimirAt, archCasimirAt, archDerivAt_comp_mul_left hw .H φ h,
    archDerivAt_comp_mul_left hw .H (archDerivAt hw .H φ) h, archDerivAt_comp_mul_left hw .Fm φ h,
    archDerivAt_comp_mul_left hw .E (archDerivAt hw .Fm φ) h]
  funext g
  simp only [Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply]

end Flows

end AutomorphicForm

end


