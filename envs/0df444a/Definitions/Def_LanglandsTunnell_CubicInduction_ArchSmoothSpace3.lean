-- Prove2me | Definitions.Def_LanglandsTunnell_CubicInduction_ArchSmoothSpace3
-- name    : LanglandsTunnell_CubicInduction_ArchSmoothSpace3
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/dbd3e5f7-24b0-5902-9f0d-c21ff059ec44
-- title:
--   Archimedean-smooth functions on adelic GL3​ and their derivations
-- statement:
--   The ambient object is the space of complex-valued functions on `AdelicGL 3 (𝓞 ℚ) ℚ`, the general linear group of degree $3$ over the adele ring of $\mathbb{Q}$. A real entry array $e \colon$ `Fin 3 → Fin 3 → ℝ` is placed into this group by `archRealMat3`, which sends $e$ entrywise into the infinite adeles (through the inverses of the real-completion isomorphisms at the infinite places) and takes the identity matrix at the finite part; `archRealLift3 e` is the corresponding unit of the adelic matrix ring when that matrix is invertible, and $1$ otherwise. The predicate `IsArchSmooth3 φ` says that for every $g$ the map $e \mapsto φ(g \cdot$ `archRealLift3` $e)$ is $C^\infty$ on the locus $\{e : \det e \neq 0\}$, and `archDeriv i j φ g` is the derivative at $s = 0$ of $s \mapsto φ(g \cdot$ `archRealLift3`$(1 + s E_{ij}))$.
--
--   Two objects are defined. `smoothFunctions3` is the $\mathbb{C}$-submodule of functions satisfying `IsArchSmooth3`, membership in which is by definition the predicate (`mem_smoothFunctions3`); closure under zero, sums and scalar multiples comes from the corresponding properties of `ContDiffOn`. `archDerivₗ i j` is the $\mathbb{C}$-linear endomorphism of this submodule given by $φ \mapsto$ `archDeriv i j φ`, with `coe_archDerivₗ_apply` identifying its underlying function.
--
--   The accompanying results are: `archRealLift3_mul`, stating that for arrays $e, e'$ of nonzero determinant the lifts multiply, $\mathrm{lift}(e)\,\mathrm{lift}(e') = \mathrm{lift}(ee')$; `archDeriv_eq_fderiv`, which for arch-smooth $φ$ and $\det e \neq 0$ identifies `archDeriv i j φ (g · archRealLift3 e)` with the Fréchet derivative at $e$ of $e' \mapsto φ(g \cdot \mathrm{lift}(e'))$ in the direction whose $(a,b)$ entry is $e_{ai}$ for $b = j$ and $0$ otherwise, that is the array of $e E_{ij}$; and `isArchSmooth3_archDeriv`, the resulting stability of arch-smoothness under `archDeriv i j`. Private auxiliaries record that the nonvanishing-determinant locus is open, that $1 + sE_{ij}$ lies in it for small $s$ and equals $1 + s\,E_{ij}$ as a sum, that $e \mapsto eE_{ij}$ is smooth, the differentiability of the one-parameter lines $s \mapsto F(e + sv)$, and a ring homomorphism `realAdeleHom` from $\mathbb{R}$ to the infinite adeles of $\mathbb{Q}$ through which the placement of real matrices is multiplicative.
--
--   **Relation to Mathlib.** Mathlib has no notion of smooth vectors or of a Lie-algebra action on functions on an adelic group; the placement `archRealLift3`, the smoothness predicate `IsArchSmooth3` and the operators `archDeriv` are the project's own, expressed through Mathlib's `ContDiffOn`, `deriv` and `fderiv` on the finite-dimensional real space `Fin 3 → Fin 3 → ℝ`, and the space of smooth functions is a plain `Submodule ℂ` of the function space.
--
--   **Where it is used.** The operators `archDeriv` are the archimedean differentiations out of which the three Casimir-type operators `casimir1`, `casimir2`, `casimir3` and the centre-finiteness condition `IsCentreFinite` on functions on adelic $GL_3$ are built; the submodule and the linear operators defined here make that action available on a fixed space of arch-smooth functions. This vocabulary belongs to the cubic-induction treatment of the Langlands–Tunnell theorem, which supplies the modularity of the residual mod $3$ representation used in the Wiles argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LanglandsTunnell_CubicInduction_ArchSmoothSpace3.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open IsDedekindDomain NumberField AutomorphicForm

namespace LanglandsTunnell.CubicInduction.WhittakerBlock

private def invertibleEntries : Set (Fin 3 → Fin 3 → ℝ) := {e | (Matrix.of e).det ≠ 0}

private theorem isOpen_invertibleEntries : IsOpen invertibleEntries :=
  isOpen_ne.preimage (Continuous.matrix_det (continuous_matrix fun a b =>
    (continuous_apply b).comp (continuous_apply a)))

private def unipotentEntries (i j : Fin 3) (s : ℝ) : Fin 3 → Fin 3 → ℝ :=
  fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0

private def oneEntries : Fin 3 → Fin 3 → ℝ := fun a b => if a = b then (1 : ℝ) else 0

private def elementaryEntries (i j : Fin 3) : Fin 3 → Fin 3 → ℝ := fun a b => if a = i ∧ b = j then (1 : ℝ) else 0

private theorem archDeriv_eq_deriv (i j : Fin 3) (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    archDeriv i j φ g = deriv (fun s : ℝ => φ (g * WhittakerBlock.archRealLift3 (unipotentEntries i j s))) 0 :=
  rfl

private theorem unipotentEntries_eq (i j : Fin 3) (s : ℝ) :
    unipotentEntries i j s = oneEntries + s • elementaryEntries i j := by
  funext a b
  simp only [unipotentEntries, oneEntries, elementaryEntries, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_ite,
    mul_one, mul_zero]

private theorem of_oneEntries : Matrix.of oneEntries = 1 := by
  ext a b
  simp only [oneEntries, Matrix.of_apply, Matrix.one_apply]

private theorem oneEntries_mem : oneEntries ∈ invertibleEntries := by
  show (Matrix.of oneEntries).det ≠ 0
  rw [of_oneEntries, Matrix.det_one]
  exact one_ne_zero

private theorem eventually_unipotentEntries_mem (i j : Fin 3) :
    ∀ᶠ s : ℝ in nhds 0, unipotentEntries i j s ∈ invertibleEntries := by
  have hc : Continuous fun s : ℝ => unipotentEntries i j s := by
    refine continuous_pi fun a => continuous_pi fun b => ?_
    show Continuous fun s : ℝ => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0
    refine continuous_const.add ?_
    by_cases h : a = i ∧ b = j
    · simp only [h]
      exact continuous_id
    · simp only [h, if_false]
      exact continuous_const
  have h0 : unipotentEntries i j 0 ∈ invertibleEntries := by
    rw [unipotentEntries_eq, zero_smul, add_zero]
    exact oneEntries_mem
  exact hc.continuousAt.eventually_mem (isOpen_invertibleEntries.mem_nhds h0)

private theorem mul_unipotentEntries_eq (i j : Fin 3) (e : Fin 3 → Fin 3 → ℝ) (s : ℝ) :
    (fun a b => (Matrix.of e * Matrix.of (unipotentEntries i j s)) a b) =
      e + s • fun a b => if b = j then e a i else 0 := by
  funext a b
  by_cases hb : b = j
  · subst hb
    simp [Matrix.mul_apply, unipotentEntries, mul_add, Finset.sum_add_distrib, mul_comm]
  · simp [Matrix.mul_apply, unipotentEntries, hb]

private theorem contDiff_direction (i j : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) fun e : Fin 3 → Fin 3 → ℝ => (fun a b => if b = j then e a i else 0 : Fin 3 → Fin 3 → ℝ) := by
  refine contDiff_pi.2 fun a => contDiff_pi.2 fun b => ?_
  by_cases hb : b = j
  · simp only [hb, if_true]
    exact contDiff_pi.1 (contDiff_pi.1 contDiff_id a) i
  · simp only [hb, if_false]
    exact contDiff_const

private theorem hasDerivAt_line {F : (Fin 3 → Fin 3 → ℝ) → ℂ} (hF : ContDiffOn ℝ (⊤ : ℕ∞) F invertibleEntries)
    {e : Fin 3 → Fin 3 → ℝ} (he : e ∈ invertibleEntries) (v : Fin 3 → Fin 3 → ℝ) :
    HasDerivAt (fun s : ℝ => F (e + s • v)) (fderiv ℝ F e v) 0 := by
  have hd : DifferentiableAt ℝ F e :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen isOpen_invertibleEntries).1 hF).1.differentiableAt
      (isOpen_invertibleEntries.mem_nhds he)
  have hl : HasDerivAt (fun s : ℝ => e + s • v) ((1 : ℝ) • v) 0 :=
    ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add e
  rw [one_smul] at hl
  exact hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)

private theorem differentiableAt_unipotent {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hφ : WhittakerBlock.IsArchSmooth3 φ)
    (i j : Fin 3) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    DifferentiableAt ℝ (fun s : ℝ => φ (g * WhittakerBlock.archRealLift3 (unipotentEntries i j s))) 0 := by
  simp only [unipotentEntries_eq]
  exact (hasDerivAt_line (hφ g) oneEntries_mem (elementaryEntries i j)).differentiableAt

private def realAdeleHom : ℝ →+* InfiniteAdeleRing ℚ :=
  RingHom.pi fun v => (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v)).symm.toRingHom

private theorem archRealMat3_eq (e : Fin 3 → Fin 3 → ℝ) :
    WhittakerBlock.archRealMat3 e = archMatrixInclN (Fin 3) ℚ ((Matrix.of e).map realAdeleHom) :=
  rfl

private theorem archRealMat3_mul (e e' : Fin 3 → Fin 3 → ℝ) :
    WhittakerBlock.archRealMat3 (fun a b => (Matrix.of e * Matrix.of e') a b) =
      WhittakerBlock.archRealMat3 e * WhittakerBlock.archRealMat3 e' := by
  rw [archRealMat3_eq, archRealMat3_eq, archRealMat3_eq, ← archMatrixInclN_mul, ← Matrix.map_mul]
  rfl

private theorem isUnit_archRealMat3 {e : Fin 3 → Fin 3 → ℝ} (he : e ∈ invertibleEntries) :
    IsUnit (WhittakerBlock.archRealMat3 e) := by
  have hdet : IsUnit ((Matrix.of e).map realAdeleHom) := by
    rw [Matrix.isUnit_iff_isUnit_det, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (isUnit_iff_ne_zero.2 he).map realAdeleHom
  rw [archRealMat3_eq]
  exact hdet.map (archMatrixInclHomN (Fin 3) ℚ)

private theorem coe_archRealLift3 {e : Fin 3 → Fin 3 → ℝ} (he : e ∈ invertibleEntries) :
    (WhittakerBlock.archRealLift3 e : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) = WhittakerBlock.archRealMat3 e := by
  unfold WhittakerBlock.archRealLift3
  rw [dif_pos (isUnit_archRealMat3 he)]
  exact (isUnit_archRealMat3 he).unit_spec

private theorem mul_mem_invertibleEntries {e e' : Fin 3 → Fin 3 → ℝ} (he : e ∈ invertibleEntries)
    (he' : e' ∈ invertibleEntries) : (fun a b => (Matrix.of e * Matrix.of e') a b) ∈ invertibleEntries := by
  show (Matrix.of e * Matrix.of e').det ≠ 0
  rw [Matrix.det_mul]
  exact mul_ne_zero he he'

theorem archRealLift3_mul {e e' : Fin 3 → Fin 3 → ℝ} (he : (Matrix.of e).det ≠ 0) (he' : (Matrix.of e').det ≠ 0) :
    WhittakerBlock.archRealLift3 e * WhittakerBlock.archRealLift3 e' =
      WhittakerBlock.archRealLift3 (fun a b => (Matrix.of e * Matrix.of e') a b) := by
  have hm : e ∈ invertibleEntries := he
  have hm' : e' ∈ invertibleEntries := he'
  apply Units.ext
  rw [Units.val_mul, coe_archRealLift3 hm, coe_archRealLift3 hm', coe_archRealLift3 (mul_mem_invertibleEntries hm hm')]
  exact (archRealMat3_mul e e').symm

theorem archDeriv_eq_fderiv {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hφ : WhittakerBlock.IsArchSmooth3 φ) (i j : Fin 3)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) {e : Fin 3 → Fin 3 → ℝ} (he : (Matrix.of e).det ≠ 0) :
    archDeriv i j φ (g * WhittakerBlock.archRealLift3 e) =
      fderiv ℝ (fun e' => φ (g * WhittakerBlock.archRealLift3 e')) e (fun a b => if b = j then e a i else 0) := by
  have he' : e ∈ invertibleEntries := he
  have hev : (fun s : ℝ =>
        φ (g * WhittakerBlock.archRealLift3 e * WhittakerBlock.archRealLift3 (unipotentEntries i j s))) =ᶠ[nhds 0]
      fun s : ℝ => φ (g * WhittakerBlock.archRealLift3 (e + s • fun a b => if b = j then e a i else 0)) := by
    filter_upwards [eventually_unipotentEntries_mem i j] with s hs
    rw [mul_assoc, archRealLift3_mul he hs, mul_unipotentEntries_eq]
  rw [archDeriv_eq_deriv, hev.deriv_eq]
  exact (hasDerivAt_line (hφ g) he' _).deriv

theorem isArchSmooth3_archDeriv {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hφ : WhittakerBlock.IsArchSmooth3 φ) (i j : Fin 3) :
    WhittakerBlock.IsArchSmooth3 (archDeriv i j φ) := by
  intro g
  have hF := (contDiffOn_infty_iff_fderiv_of_isOpen isOpen_invertibleEntries).1 (hφ g)
  refine (hF.2.clm_apply (contDiff_direction i j).contDiffOn).congr fun e he => ?_
  exact archDeriv_eq_fderiv hφ i j g he

def smoothFunctions3 : Submodule ℂ (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) where
  carrier := {φ | WhittakerBlock.IsArchSmooth3 φ}
  zero_mem' := by
    intro g
    exact contDiffOn_const
  add_mem' := by
    intro φ ψ hφ hψ g
    exact (hφ g).add (hψ g)
  smul_mem' := by
    intro c φ hφ g
    exact (hφ g).const_smul c

theorem mem_smoothFunctions3 {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} :
    φ ∈ smoothFunctions3 ↔ WhittakerBlock.IsArchSmooth3 φ :=
  Iff.rfl

def archDerivₗ (i j : Fin 3) : smoothFunctions3 →ₗ[ℂ] smoothFunctions3 where
  toFun φ := ⟨archDeriv i j φ, isArchSmooth3_archDeriv φ.2 i j⟩
  map_add' φ ψ := Subtype.ext <| funext fun g =>
    ((differentiableAt_unipotent φ.2 i j g).hasDerivAt.add (differentiableAt_unipotent ψ.2 i j g).hasDerivAt).deriv
  map_smul' c φ := Subtype.ext <| funext fun g =>
    ((differentiableAt_unipotent φ.2 i j g).hasDerivAt.const_smul c).deriv

@[simp]
theorem coe_archDerivₗ_apply (i j : Fin 3) (φ : smoothFunctions3) :
    ((archDerivₗ i j φ : smoothFunctions3) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) = archDeriv i j φ :=
  rfl

end LanglandsTunnell.CubicInduction.WhittakerBlock


