-- Prove2me | Definitions.Def_LanglandsTunnell_CubicInduction_EnvelopingAction3
-- name    : LanglandsTunnell_CubicInduction_EnvelopingAction3
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/614dfb95-527e-548b-9418-29423fd5945e
-- title:
--   Enveloping algebra action by archimedean right derivatives on GL₃
-- statement:
--   Let $\mathrm{GL}_3(\mathbf{A}_{\mathbf{Q}})$ be the adelic group `AdelicGL 3 (𝓞 ℚ) ℚ` and let `smoothFunctions3` be the $\mathbf{C}$-submodule of functions $\varphi$ on it that are smooth at the infinite place, in the sense that for every $g$ the function $e\mapsto\varphi(g\cdot\mathrm{archRealLift3}(e))$ on real $3\times 3$ entry arrays is $C^\infty$ on $\{\det e\neq 0\}$; on this space `archDerivₗ i j` is the operator induced by the right derivative $\mathrm{archDeriv}\,i\,j$ along the one-parameter family $1+sE_{ij}$ at the archimedean place. This module assembles those operators into a Lie action. `envelopingAlgebra3` abbreviates the universal enveloping algebra over $\mathbf{C}$ of $\mathfrak{gl}_3(\mathbf{C})=$ `Matrix (Fin 3) (Fin 3) ℂ` with the commutator bracket. `derivAction3` is the $\mathbf{C}$-linear map $\mathfrak{gl}_3(\mathbf{C})\to\operatorname{End}_{\mathbf{C}}(\mathtt{smoothFunctions3})$ determined on the basis of matrix units by sending `Matrix.single i j 1` to `archDerivₗ i j`. The commutation relations are proved in a chart: for a real matrix $A$, `rightField A F e` is the derivative of $F$ at $e$ in the direction $e\mapsto eA$ of the right-invariant vector field, the bracket of the fields attached to two matrices is the field attached to their matrix commutator (via symmetry of the second derivative), and translating back gives $[\mathrm{archDeriv}_{ij},\mathrm{archDeriv}_{kl}]=\delta_{jk}\,\mathrm{archDeriv}_{il}-\delta_{li}\,\mathrm{archDeriv}_{kj}$ at every point, first at points $g\cdot\mathrm{archRealLift3}(e)$ with $\det e\neq 0$ and then generally. Hence `derivAction3_lie`: $\mathrm{derivAction3}\,\lceil X,Y\rceil=[\mathrm{derivAction3}\,X,\mathrm{derivAction3}\,Y]$. The corresponding Lie algebra homomorphism is `derivLieHom3`, its extension to the enveloping algebra is the algebra homomorphism `envelopingHom3` (satisfying $\mathrm{envelopingHom3}(\iota X)=\mathrm{derivAction3}\,X$), and `envelopingModule3` is the resulting module structure of `envelopingAlgebra3` on `smoothFunctions3`, registered as a scoped instance together with the scalar-tower compatibility over $\mathbf{C}$.
--
--   **Relation to Mathlib.** The enveloping algebra, its universal property (`UniversalEnvelopingAlgebra.lift`), the Lie ring structure on an associative ring, the standard basis of matrix units and the transport of a module structure along a ring homomorphism are Mathlib's; the space of archimedean-smooth functions on the adelic group, the right derivatives along matrix units and their action are the project's own.
--
--   **Where it is used.** The enveloping algebra action supplies the archimedean differential operators used in the cubic-induction construction of automorphic forms on $\mathrm{GL}_3$ over $\mathbf{Q}$: the Casimir elements `casimir1`, `casimir2`, `casimir3` and the finiteness condition `IsCentreFinite` are expressed through these right derivatives. That construction is part of the Langlands–Tunnell input to the modularity of the residual representation attached to a Frey curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LanglandsTunnell_CubicInduction_EnvelopingAction3.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchSmoothSpace3

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open IsDedekindDomain NumberField AutomorphicForm

attribute [local instance 100] LieRing.ofAssociativeRing

namespace LanglandsTunnell.CubicInduction.WhittakerBlock

abbrev envelopingAlgebra3 : Type := UniversalEnvelopingAlgebra ℂ (Matrix (Fin 3) (Fin 3) ℂ)

def derivAction3 : Matrix (Fin 3) (Fin 3) ℂ →ₗ[ℂ] Module.End ℂ smoothFunctions3 :=
  (Matrix.stdBasis ℂ (Fin 3) (Fin 3)).constr ℂ fun p => archDerivₗ p.1 p.2

theorem derivAction3_single (i j : Fin 3) : derivAction3 (Matrix.single i j (1 : ℂ)) = archDerivₗ i j := by
  rw [← Matrix.stdBasis_eq_single]
  exact (Matrix.stdBasis ℂ (Fin 3) (Fin 3)).constr_basis ℂ (fun p => archDerivₗ p.1 p.2) (i, j)

private def rightFieldLin (A : Matrix (Fin 3) (Fin 3) ℝ) : (Fin 3 → Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → Fin 3 → ℝ) where
  toFun e := fun a b => ∑ c, e a c * A c b
  map_add' e e' := by
    funext a b
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' r e := by
    funext a b
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc]

private def rightFieldCLM (A : Matrix (Fin 3) (Fin 3) ℝ) : (Fin 3 → Fin 3 → ℝ) →L[ℝ] (Fin 3 → Fin 3 → ℝ) :=
  LinearMap.toContinuousLinearMap (rightFieldLin A)

private theorem rightFieldCLM_apply (A : Matrix (Fin 3) (Fin 3) ℝ) (e : Fin 3 → Fin 3 → ℝ) :
    rightFieldCLM A e = fun a b => ∑ c, e a c * A c b := rfl

private theorem rightFieldCLM_rightFieldCLM (A B : Matrix (Fin 3) (Fin 3) ℝ) (e : Fin 3 → Fin 3 → ℝ) :
    rightFieldCLM B (rightFieldCLM A e) = rightFieldCLM (A * B) e := by
  funext a b
  simp only [rightFieldCLM_apply, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

private theorem rightFieldCLM_sub (A B : Matrix (Fin 3) (Fin 3) ℝ) (e : Fin 3 → Fin 3 → ℝ) :
    rightFieldCLM (A - B) e = rightFieldCLM A e - rightFieldCLM B e := by
  funext a b
  simp only [rightFieldCLM_apply, Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib, Pi.sub_apply]

private theorem rightFieldCLM_zero (e : Fin 3 → Fin 3 → ℝ) : rightFieldCLM 0 e = 0 := by
  funext a b
  simp only [rightFieldCLM_apply, Matrix.zero_apply, mul_zero, Finset.sum_const_zero, Pi.zero_apply]

private theorem rightFieldCLM_single (i j : Fin 3) (e : Fin 3 → Fin 3 → ℝ) :
    rightFieldCLM (Matrix.single i j (1 : ℝ)) e = fun a b => if b = j then e a i else 0 := by
  funext a b
  simp only [rightFieldCLM_apply, Matrix.single_apply, mul_ite, mul_one, mul_zero]
  by_cases hb : b = j
  · subst hb
    simp
  · simp [hb, Ne.symm hb]

private def rightField (A : Matrix (Fin 3) (Fin 3) ℝ) (F : (Fin 3 → Fin 3 → ℝ) → ℂ) (e : Fin 3 → Fin 3 → ℝ) : ℂ :=
  fderiv ℝ F e (rightFieldCLM A e)

private theorem hasFDerivAt_rightField (A : Matrix (Fin 3) (Fin 3) ℝ) {F : (Fin 3 → Fin 3 → ℝ) → ℂ}
    {e : Fin 3 → Fin 3 → ℝ} (hF : ContDiffAt ℝ 2 F e) :
    HasFDerivAt (rightField A F)
      ((fderiv ℝ F e).comp (rightFieldCLM A) + (fderiv ℝ (fderiv ℝ F) e).flip (rightFieldCLM A e)) e := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ F) e := hF.fderiv_right (by norm_num)
  exact (h1.differentiableAt (by norm_num)).hasFDerivAt.clm_apply (rightFieldCLM A).hasFDerivAt

private theorem rightField_comm (A B : Matrix (Fin 3) (Fin 3) ℝ) {F : (Fin 3 → Fin 3 → ℝ) → ℂ}
    {e : Fin 3 → Fin 3 → ℝ} (hF : ContDiffAt ℝ 2 F e) :
    rightField A (rightField B F) e - rightField B (rightField A F) e = rightField (A * B - B * A) F e := by
  have hsymm : IsSymmSndFDerivAt ℝ F e := hF.isSymmSndFDerivAt (by simp)
  have h1 := (hasFDerivAt_rightField B hF).fderiv
  have h2 := (hasFDerivAt_rightField A hF).fderiv
  change fderiv ℝ (rightField B F) e (rightFieldCLM A e) - fderiv ℝ (rightField A F) e (rightFieldCLM B e) =
    rightField (A * B - B * A) F e
  rw [h1, h2]
  unfold rightField
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]
  rw [hsymm (rightFieldCLM A e) (rightFieldCLM B e), rightFieldCLM_rightFieldCLM, rightFieldCLM_rightFieldCLM,
    rightFieldCLM_sub, map_sub]
  ring

private theorem single_mul_single_sub {R : Type} [Ring R] (i j k l : Fin 3) :
    Matrix.single i j (1 : R) * Matrix.single k l 1 - Matrix.single k l 1 * Matrix.single i j 1 =
      (if j = k then Matrix.single i l (1 : R) else 0) - (if l = i then Matrix.single k j (1 : R) else 0) := by
  congr 1
  · split_ifs with h
    · subst h
      rw [Matrix.single_mul_single_same, mul_one]
    · rw [Matrix.single_mul_single_of_ne (h := h)]
  · split_ifs with h
    · subst h
      rw [Matrix.single_mul_single_same, mul_one]
    · rw [Matrix.single_mul_single_of_ne (h := h)]

private theorem isOpen_invertibleEntries3 : IsOpen {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0} :=
  isOpen_ne.preimage (Continuous.matrix_det (continuous_matrix fun a b =>
    (continuous_apply b).comp (continuous_apply a)))

private theorem archDeriv_comm_chart {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hφ : WhittakerBlock.IsArchSmooth3 φ)
    (i j k l : Fin 3) (g : AdelicGL 3 (𝓞 ℚ) ℚ) {e : Fin 3 → Fin 3 → ℝ} (he : (Matrix.of e).det ≠ 0) :
    archDeriv i j (archDeriv k l φ) (g * WhittakerBlock.archRealLift3 e) -
        archDeriv k l (archDeriv i j φ) (g * WhittakerBlock.archRealLift3 e) =
      (if j = k then archDeriv i l φ (g * WhittakerBlock.archRealLift3 e) else 0) -
        (if l = i then archDeriv k j φ (g * WhittakerBlock.archRealLift3 e) else 0) := by
  have hU : IsOpen {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0} := isOpen_invertibleEntries3
  have hF : ContDiffOn ℝ (⊤ : ℕ∞) (fun e' => φ (g * WhittakerBlock.archRealLift3 e'))
      {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0} := hφ g
  have hF2 : ContDiffAt ℝ 2 (fun e' => φ (g * WhittakerBlock.archRealLift3 e')) e :=
    contDiffAt_infty.mp (hF.contDiffAt (hU.mem_nhds he)) 2

  have hfield : ∀ k l : Fin 3, (fun e' => archDeriv k l φ (g * WhittakerBlock.archRealLift3 e')) =ᶠ[nhds e]
      rightField (Matrix.single k l (1 : ℝ)) fun e' => φ (g * WhittakerBlock.archRealLift3 e') := by
    intro k l
    filter_upwards [hU.mem_nhds he] with e' he'
    rw [rightField, rightFieldCLM_single]
    exact archDeriv_eq_fderiv hφ k l g he'

  have hsecond : ∀ i j k l : Fin 3, archDeriv i j (archDeriv k l φ) (g * WhittakerBlock.archRealLift3 e) =
      rightField (Matrix.single i j (1 : ℝ))
        (rightField (Matrix.single k l 1) fun e' => φ (g * WhittakerBlock.archRealLift3 e')) e := by
    intro i j k l
    rw [archDeriv_eq_fderiv (isArchSmooth3_archDeriv hφ k l) i j g he, (hfield k l).fderiv_eq, rightField,
      rightFieldCLM_single]
  rw [hsecond i j k l, hsecond k l i j, rightField_comm _ _ hF2, rightField, single_mul_single_sub,
    rightFieldCLM_sub, map_sub]
  congr 1
  · split_ifs
    · rw [rightFieldCLM_single, archDeriv_eq_fderiv hφ i l g he]
    · rw [rightFieldCLM_zero, map_zero]
  · split_ifs
    · rw [rightFieldCLM_single, archDeriv_eq_fderiv hφ k j g he]
    · rw [rightFieldCLM_zero, map_zero]

private theorem det_of_one_ne_zero : (Matrix.of fun a b : Fin 3 => if a = b then (1 : ℝ) else 0).det ≠ 0 := by
  have h : (Matrix.of fun a b : Fin 3 => if a = b then (1 : ℝ) else 0) = 1 := by
    ext a b
    simp only [Matrix.of_apply, Matrix.one_apply]
  rw [h, Matrix.det_one]
  exact one_ne_zero

private theorem archDeriv_comm {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hφ : WhittakerBlock.IsArchSmooth3 φ)
    (i j k l : Fin 3) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    archDeriv i j (archDeriv k l φ) g - archDeriv k l (archDeriv i j φ) g =
      (if j = k then archDeriv i l φ g else 0) - (if l = i then archDeriv k j φ g else 0) := by
  have h := archDeriv_comm_chart hφ i j k l
    (g * (WhittakerBlock.archRealLift3 fun a b => if a = b then (1 : ℝ) else 0)⁻¹) det_of_one_ne_zero
  rwa [inv_mul_cancel_right] at h

private theorem archDerivₗ_comm (i j k l : Fin 3) :
    archDerivₗ i j * archDerivₗ k l - archDerivₗ k l * archDerivₗ i j =
      (if j = k then archDerivₗ i l else 0) - (if l = i then archDerivₗ k j else 0) := by
  refine LinearMap.ext fun φ => Subtype.ext (funext fun g => ?_)
  have h := archDeriv_comm (mem_smoothFunctions3.mp φ.2) i j k l g
  split_ifs at h ⊢ <;>
    simpa only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.zero_apply, Submodule.coe_sub,
      Submodule.coe_zero, Pi.sub_apply, Pi.zero_apply, coe_archDerivₗ_apply, sub_zero] using h

private theorem derivAction3_comm (X Y : Matrix (Fin 3) (Fin 3) ℂ) :
    derivAction3 (X * Y - Y * X) = derivAction3 X * derivAction3 Y - derivAction3 Y * derivAction3 X := by
  let B₁ : Matrix (Fin 3) (Fin 3) ℂ →ₗ[ℂ] Matrix (Fin 3) (Fin 3) ℂ →ₗ[ℂ] Module.End ℂ smoothFunctions3 :=
    LinearMap.mk₂ ℂ (fun X Y => derivAction3 (X * Y - Y * X))
      (fun X₁ X₂ Y => by simp only [add_mul, mul_add, map_sub, map_add]; abel)
      (fun c X Y => by simp only [smul_mul_assoc, mul_smul_comm, ← smul_sub, map_smul])
      (fun X Y₁ Y₂ => by simp only [add_mul, mul_add, map_sub, map_add]; abel)
      (fun c X Y => by simp only [smul_mul_assoc, mul_smul_comm, ← smul_sub, map_smul])
  let B₂ : Matrix (Fin 3) (Fin 3) ℂ →ₗ[ℂ] Matrix (Fin 3) (Fin 3) ℂ →ₗ[ℂ] Module.End ℂ smoothFunctions3 :=
    LinearMap.mk₂ ℂ (fun X Y => derivAction3 X * derivAction3 Y - derivAction3 Y * derivAction3 X)
      (fun X₁ X₂ Y => by simp only [map_add, add_mul, mul_add]; abel)
      (fun c X Y => by
        simp only [map_smul, smul_mul_assoc, mul_smul_comm]
        exact (smul_sub c (derivAction3 X * derivAction3 Y) (derivAction3 Y * derivAction3 X)).symm)
      (fun X Y₁ Y₂ => by simp only [map_add, add_mul, mul_add]; abel)
      (fun c X Y => by
        simp only [map_smul, smul_mul_assoc, mul_smul_comm]
        exact (smul_sub c (derivAction3 X * derivAction3 Y) (derivAction3 Y * derivAction3 X)).symm)
  have hbil : B₁ = B₂ := by
    refine LinearMap.ext_basis (Matrix.stdBasis ℂ (Fin 3) (Fin 3)) (Matrix.stdBasis ℂ (Fin 3) (Fin 3)) ?_
    rintro ⟨i, j⟩ ⟨k, l⟩
    simp only [B₁, B₂, LinearMap.mk₂_apply, Matrix.stdBasis_eq_single, derivAction3_single]
    rw [single_mul_single_sub, map_sub, archDerivₗ_comm]
    congr 1
    · split_ifs <;> simp only [derivAction3_single, map_zero]
    · split_ifs <;> simp only [derivAction3_single, map_zero]
  have h := LinearMap.congr_fun₂ hbil X Y
  simpa only [B₁, B₂, LinearMap.mk₂_apply] using h

theorem derivAction3_lie (X Y : Matrix (Fin 3) (Fin 3) ℂ) :
    derivAction3 ⁅X, Y⁆ = ⁅derivAction3 X, derivAction3 Y⁆ := by
  rw [Ring.lie_def, Module.End.instLieRingModule_eq, LieRing.of_associative_ring_bracket]
  exact derivAction3_comm X Y

def derivLieHom3 : Matrix (Fin 3) (Fin 3) ℂ →ₗ⁅ℂ⁆ Module.End ℂ smoothFunctions3 :=
  { derivAction3 with map_lie' := fun {X Y} => derivAction3_lie X Y }

def envelopingHom3 : envelopingAlgebra3 →ₐ[ℂ] Module.End ℂ smoothFunctions3 :=
  UniversalEnvelopingAlgebra.lift ℂ derivLieHom3

theorem envelopingHom3_ι (X : Matrix (Fin 3) (Fin 3) ℂ) :
    envelopingHom3 (UniversalEnvelopingAlgebra.ι ℂ X) = derivAction3 X :=
  UniversalEnvelopingAlgebra.lift_ι_apply ℂ derivLieHom3 X

abbrev envelopingModule3 : Module envelopingAlgebra3 smoothFunctions3 :=
  Module.compHom smoothFunctions3 envelopingHom3.toRingHom

scoped instance instEnvelopingModule3 : Module envelopingAlgebra3 smoothFunctions3 := envelopingModule3

scoped instance instEnvelopingScalarTower3 : IsScalarTower ℂ envelopingAlgebra3 smoothFunctions3 :=
  ⟨fun c u φ => by
    show envelopingHom3 (c • u) φ = c • envelopingHom3 u φ
    rw [map_smul]
    rfl⟩

end LanglandsTunnell.CubicInduction.WhittakerBlock


