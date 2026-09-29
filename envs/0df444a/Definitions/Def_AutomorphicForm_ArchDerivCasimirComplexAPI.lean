-- Prove2me | Definitions.Def_AutomorphicForm_ArchDerivCasimirComplexAPI
-- name    : AutomorphicForm_ArchDerivCasimirComplexAPI
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/c460b9e9-a82c-56d9-9b5b-9d902dcc585e
-- title:
--   Complex-place flow generators, projection, and operator calculus API
-- statement:
--   This module supplies the working lemmas for the archimedean differential vocabulary at a complex place $w$ of a number field $F$, for $\mathbb{C}$-valued functions on $\mathrm{GL}_2$ of the adeles of $F$.
--
--   Two definitions are made. First, `archDirMatrixComplex` assigns to each of the six labels of `ArchDirComplex` a matrix in $M_2(\mathbb{C})$: $H=\mathrm{diag}(1,-1)$, $E=\begin{pmatrix}0&1\\0&0\end{pmatrix}$, $F=\begin{pmatrix}0&0\\1&0\end{pmatrix}$ and $iH$, $iE$, $iF$ their multiples by $i$. It is shown entrywise that this matrix is the derivative at $t=0$ of the corresponding one-parameter flow `archFlowMatrixComplex` ($t\mapsto\mathrm{diag}(e^{t},e^{-t})$, upper and lower unipotents, and the $i$-twisted versions). Second, `archComplexProjAt hw` is the monoid homomorphism obtained by composing the projection to the infinite-adelic $\mathrm{GL}_2$, the component at $w$, and the isomorphism $\mathrm{GL}_2(F_w)\simeq\mathrm{GL}_2(\mathbb{C})$ induced by the chosen ring isomorphism $F_w\cong\mathbb{C}$; it is a retraction of the inclusion `archComplexGLAt hw`.
--
--   The remaining declarations are closure and transport lemmas for the project's predicate `IsArchSmoothAtComplex hw` (for every $g$, the map $e\mapsto\varphi(g\cdot\mathrm{lift}(e))$ is $C^\infty$ over $\mathbb{R}$ on the open set of entry tuples with non-vanishing determinant) and for `HasCircleWeightAt hw m` ($\varphi(g\,\mathrm{diag}(\zeta,\zeta^{-1})_w)=\zeta^m\varphi(g)$ for all $\zeta$ of modulus one). Via a chain rule in the entry chart one obtains: differentiability along each flow; stability of smoothness under `archDerivAtComplex`, sums, complex scalars, negation, subtraction, the combinations $\partial$, $\bar\partial$ and the two Casimir expressions; additivity of `archDerivAtComplex` on smooth functions and homogeneity with no hypothesis. Finally, any element placed at $w$ commutes with every adelic element of trivial archimedean component, whence right translation by such elements commutes with all these operators and preserves smoothness and circle weights; left translation is treated likewise, and `circleGL2` is shown to be multiplicative.
--
--   **Relation to Mathlib.** Mathlib has no notion of flow derivatives or Casimir operators for functions on an adelic $\mathrm{GL}_2$; the predicates and operators here are the project's own, with smoothness expressed through Mathlib's `ContDiffOn ℝ ⊤` on the chart of matrix entries and the derivative computations reduced to Mathlib's `HasDerivAt` calculus.
--
--   **Where it is used.** These operators and their elementary calculus form part of the vocabulary for automorphic forms on $\mathrm{GL}(2)$ over a number field with complex places, as required by the Langlands–Tunnell input to the modularity argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_ArchDerivCasimirComplexAPI.lean

import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace AutomorphicForm

open NumberField NumberField.InfinitePlace.Completion Matrix Complex

variable {F : Type} [Field F] [NumberField F]

theorem splitTorusGL2Complex_coe (z : ℂ) :
    (splitTorusGL2Complex z : Matrix (Fin 2) (Fin 2) ℂ) = !![Complex.exp z, 0; 0, Complex.exp (-z)] :=
  rfl

def archDirMatrixComplex : ArchDirComplex → Matrix (Fin 2) (Fin 2) ℂ
  | .H => !![1, 0; 0, -1]
  | .E => !![0, 1; 0, 0]
  | .Fm => !![0, 0; 1, 0]
  | .iH => !![I, 0; 0, -I]
  | .iE => !![0, I; 0, 0]
  | .iFm => !![0, 0; I, 0]

theorem hasDerivAt_ofReal_mul_const (c : ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (s : ℂ) * c) c t := by
  simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const c

theorem hasDerivAt_cexp_ofReal_mul_const (c : ℂ) :
    HasDerivAt (fun s : ℝ => Complex.exp ((s : ℂ) * c)) c 0 := by
  have h := (Complex.hasDerivAt_exp ((0 : ℝ) * c)).comp (0 : ℝ) (hasDerivAt_ofReal_mul_const c 0)
  simp at h
  exact h

theorem hasDerivAt_cexp_neg_ofReal_mul_const (c : ℂ) :
    HasDerivAt (fun s : ℝ => Complex.exp (-((s : ℂ) * c))) (-c) 0 := by
  have h0 : HasDerivAt (fun s : ℝ => -((s : ℂ) * c)) (-c) 0 := (hasDerivAt_ofReal_mul_const c 0).neg
  have h := (Complex.hasDerivAt_exp (-((0 : ℝ) * c))).comp (0 : ℝ) h0
  simp at h
  exact h

theorem hasDerivAt_archFlowMatrixComplex_apply (d : ArchDirComplex) (i j : Fin 2) :
    HasDerivAt (fun t : ℝ => (archFlowMatrixComplex d t : Matrix (Fin 2) (Fin 2) ℂ) i j)
      (archDirMatrixComplex d i j) 0 := by
  have e1 : HasDerivAt (fun s : ℝ => Complex.exp (s : ℂ)) 1 0 := by
    simpa using hasDerivAt_cexp_ofReal_mul_const 1
  have e2 : HasDerivAt (fun s : ℝ => Complex.exp (-(s : ℂ))) (-1) 0 := by
    simpa using hasDerivAt_cexp_neg_ofReal_mul_const 1
  have e3 : HasDerivAt (fun s : ℝ => Complex.exp ((s : ℂ) * I)) I 0 := hasDerivAt_cexp_ofReal_mul_const I
  have e4 : HasDerivAt (fun s : ℝ => Complex.exp (-((s : ℂ) * I))) (-I) 0 := hasDerivAt_cexp_neg_ofReal_mul_const I
  have e5 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 0 := by simpa using hasDerivAt_ofReal_mul_const 1 0
  have e6 : HasDerivAt (fun s : ℝ => (s : ℂ) * I) I 0 := hasDerivAt_ofReal_mul_const I 0
  cases d <;> fin_cases i <;> fin_cases j <;>
    simp only [archFlowMatrixComplex, archDirMatrixComplex, splitTorusGL2Complex_coe, unipotentGL2_coe,
      lowerUnipotentGL2_coe, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Fin.zero_eta, Fin.mk_one, Fin.isValue] <;>
    first
      | exact hasDerivAt_const _ _
      | exact e1 | exact e2 | exact e3 | exact e4 | exact e5 | exact e6

theorem archComplexLiftAt_mul_archComplexGLAt {w : InfinitePlace F} (hw : w.IsComplex) {e : Fin 2 → Fin 2 → ℂ}
    (h : (Matrix.of e).det ≠ 0) (m : GL (Fin 2) ℂ) :
    archComplexLiftAt hw e * archComplexGLAt hw m =
      archComplexLiftAt hw (Matrix.of.symm (Matrix.of e * (m : Matrix (Fin 2) (Fin 2) ℂ))) := by
  have hm : ((m : Matrix (Fin 2) (Fin 2) ℂ)).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 m.isUnit).ne_zero
  have h' : (Matrix.of (Matrix.of.symm (Matrix.of e * (m : Matrix (Fin 2) (Fin 2) ℂ)))).det ≠ 0 := by
    rw [Equiv.apply_symm_apply, Matrix.det_mul]
    exact mul_ne_zero h hm
  rw [archComplexLiftAt_of_det_ne_zero hw h, archComplexLiftAt_of_det_ne_zero hw h', ← map_mul]
  congr 1
  ext i j
  simp [GeneralLinearGroup.mkOfDetNeZero]

theorem contDiff_of_symm_mul_const_complex (A : Matrix (Fin 2) (Fin 2) ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) fun e : Fin 2 → Fin 2 → ℂ => (Matrix.of.symm (Matrix.of e * A) : Fin 2 → Fin 2 → ℂ) := by
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  simp only [Matrix.of_symm_apply, Matrix.mul_apply, Matrix.of_apply]
  exact ContDiff.sum fun k _ =>
    ((contDiff_apply ℝ ℂ k).comp (contDiff_apply ℝ (Fin 2 → ℂ) i)).mul contDiff_const

theorem hasDerivAt_of_symm_mul_archFlowMatrixComplex (e : Fin 2 → Fin 2 → ℂ) (d : ArchDirComplex) :
    HasDerivAt
      (fun t : ℝ => (Matrix.of.symm (Matrix.of e * (archFlowMatrixComplex d t : Matrix (Fin 2) (Fin 2) ℂ)) :
        Fin 2 → Fin 2 → ℂ))
      (Matrix.of.symm (Matrix.of e * archDirMatrixComplex d)) 0 := by
  rw [hasDerivAt_pi]
  intro i
  rw [hasDerivAt_pi]
  intro j
  simp only [Matrix.of_symm_apply, Matrix.mul_apply, Matrix.of_apply]
  exact HasDerivAt.fun_sum fun k _ => (hasDerivAt_archFlowMatrixComplex_apply d k j).const_mul (e i k)

theorem of_symm_mul_archFlowMatrixComplex_zero (e : Fin 2 → Fin 2 → ℂ) (d : ArchDirComplex) :
    (Matrix.of.symm (Matrix.of e * (archFlowMatrixComplex d 0 : Matrix (Fin 2) (Fin 2) ℂ)) : Fin 2 → Fin 2 → ℂ) = e := by
  rw [archFlowMatrixComplex_zero, Units.val_one, mul_one, Equiv.symm_apply_apply]

theorem IsArchSmoothAtComplex.archDerivAtComplex {w : InfinitePlace F} {hw : w.IsComplex} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAtComplex hw φ) (d : ArchDirComplex) : IsArchSmoothAtComplex hw (archDerivAtComplex hw d φ) := by
  intro g
  have hΦ := hφ g
  have hopen := isOpen_setOf_det_ne_zero_complex
  refine contDiffOn_infty.2 fun n => ?_
  refine ((hΦ.fderiv_of_isOpen hopen (by exact_mod_cast le_top)).clm_apply
    ((contDiff_of_symm_mul_const_complex (archDirMatrixComplex d)).contDiffOn.of_le (by exact_mod_cast le_top))).congr ?_
  intro e he
  have hdiff : HasFDerivAt (fun e' => φ (g * archComplexLiftAt hw e'))
      (fderiv ℝ (fun e' => φ (g * archComplexLiftAt hw e')) e)
      (Matrix.of.symm (Matrix.of e * (archFlowMatrixComplex d 0 : Matrix (Fin 2) (Fin 2) ℂ))) := by
    rw [of_symm_mul_archFlowMatrixComplex_zero]
    exact ((hΦ.contDiffAt (hopen.mem_nhds he)).differentiableAt (by simp)).hasFDerivAt
  have hfun : (fun t : ℝ => φ (g * archComplexLiftAt hw e * archFlowAtComplex hw d t)) =
      fun t : ℝ => φ (g * archComplexLiftAt hw
        (Matrix.of.symm (Matrix.of e * (archFlowMatrixComplex d t : Matrix (Fin 2) (Fin 2) ℂ)))) := by
    funext t
    rw [archFlowAtComplex, mul_assoc, archComplexLiftAt_mul_archComplexGLAt hw he]
  show deriv (fun t : ℝ => φ (g * archComplexLiftAt hw e * archFlowAtComplex hw d t)) 0 = _
  rw [hfun]
  simpa only [Function.comp_def] using
    (hdiff.comp_hasDerivAt (0 : ℝ) (hasDerivAt_of_symm_mul_archFlowMatrixComplex e d)).deriv

theorem archComplexLiftAt_of_symm_one {w : InfinitePlace F} (hw : w.IsComplex) :
    archComplexLiftAt hw (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 1 := by
  have hdet : (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℂ))).det ≠ 0 := by
    rw [Equiv.apply_symm_apply, Matrix.det_one]
    exact one_ne_zero
  rw [archComplexLiftAt_of_det_ne_zero hw hdet, ← map_one (archComplexGLAt hw)]
  congr 1
  ext i j
  simp [GeneralLinearGroup.mkOfDetNeZero]

theorem IsArchSmoothAtComplex.differentiableAt_flow {w : InfinitePlace F} {hw : w.IsComplex}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAtComplex hw φ) (d : ArchDirComplex) (g : AdelicGL2 (𝓞 F) F) :
    DifferentiableAt ℝ (fun t : ℝ => φ (g * archFlowAtComplex hw d t)) 0 := by
  have hopen := isOpen_setOf_det_ne_zero_complex
  have hdet : (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℂ))).det ≠ 0 := by
    rw [Equiv.apply_symm_apply, Matrix.det_one]
    exact one_ne_zero
  have hdiff : DifferentiableAt ℝ (fun e' => φ (g * archComplexLiftAt hw e'))
      (Matrix.of.symm (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℂ)) *
        (archFlowMatrixComplex d 0 : Matrix (Fin 2) (Fin 2) ℂ))) := by
    rw [of_symm_mul_archFlowMatrixComplex_zero]
    exact ((hφ g).contDiffAt (hopen.mem_nhds hdet)).differentiableAt (by simp)
  have hfun : (fun t : ℝ => φ (g * archFlowAtComplex hw d t)) =
      fun t : ℝ => φ (g * archComplexLiftAt hw
        (Matrix.of.symm (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℂ)) *
          (archFlowMatrixComplex d t : Matrix (Fin 2) (Fin 2) ℂ)))) := by
    funext t
    rw [← archComplexLiftAt_mul_archComplexGLAt hw hdet, archComplexLiftAt_of_symm_one, one_mul, archFlowAtComplex]
  rw [hfun]
  simpa only [Function.comp_def] using
    (hdiff.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_of_symm_mul_archFlowMatrixComplex _ d)).differentiableAt

theorem archDerivAtComplex_add {w : InfinitePlace F} {hw : w.IsComplex} {φ ψ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAtComplex hw φ) (hψ : IsArchSmoothAtComplex hw ψ) (d : ArchDirComplex) :
    archDerivAtComplex hw d (φ + ψ) = archDerivAtComplex hw d φ + archDerivAtComplex hw d ψ := by
  funext g
  show deriv (fun t : ℝ => (φ + ψ) (g * archFlowAtComplex hw d t)) 0 =
    deriv (fun t : ℝ => φ (g * archFlowAtComplex hw d t)) 0 + deriv (fun t : ℝ => ψ (g * archFlowAtComplex hw d t)) 0
  simp only [Pi.add_apply]
  exact deriv_fun_add (hφ.differentiableAt_flow d g) (hψ.differentiableAt_flow d g)

theorem archDerivAtComplex_smul {w : InfinitePlace F} (hw : w.IsComplex) (d : ArchDirComplex) (c : ℂ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) : archDerivAtComplex hw d (c • φ) = c • archDerivAtComplex hw d φ := by
  funext g
  show deriv (fun t : ℝ => (c • φ) (g * archFlowAtComplex hw d t)) 0 =
    c • deriv (fun t : ℝ => φ (g * archFlowAtComplex hw d t)) 0
  simp only [Pi.smul_apply, smul_eq_mul]
  exact deriv_const_mul_field c

theorem IsArchSmoothAtComplex.add {w : InfinitePlace F} {hw : w.IsComplex} {φ ψ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAtComplex hw φ) (hψ : IsArchSmoothAtComplex hw ψ) : IsArchSmoothAtComplex hw (φ + ψ) := by
  intro g
  show ContDiffOn ℝ (⊤ : ℕ∞) (fun e => φ (g * archComplexLiftAt hw e) + ψ (g * archComplexLiftAt hw e)) _
  exact (hφ g).add (hψ g)

theorem IsArchSmoothAtComplex.smul {w : InfinitePlace F} {hw : w.IsComplex} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAtComplex hw φ) (c : ℂ) : IsArchSmoothAtComplex hw (c • φ) := by
  intro g
  show ContDiffOn ℝ (⊤ : ℕ∞) (fun e => c * φ (g * archComplexLiftAt hw e)) _
  exact contDiffOn_const.mul (hφ g)

theorem IsArchSmoothAtComplex.neg {w : InfinitePlace F} {hw : w.IsComplex} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAtComplex hw φ) : IsArchSmoothAtComplex hw (-φ) := by
  rw [← neg_one_smul ℂ φ]
  exact hφ.smul (-1)

theorem IsArchSmoothAtComplex.sub {w : InfinitePlace F} {hw : w.IsComplex} {φ ψ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAtComplex hw φ) (hψ : IsArchSmoothAtComplex hw ψ) : IsArchSmoothAtComplex hw (φ - ψ) := by
  rw [sub_eq_add_neg]
  exact hφ.add hψ.neg

theorem IsArchSmoothAtComplex.archDelAt {w : InfinitePlace F} {hw : w.IsComplex} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAtComplex hw φ) (d : ArchDir) : IsArchSmoothAtComplex hw (archDelAt hw d φ) := by
  unfold AutomorphicForm.archDelAt
  exact ((hφ.archDerivAtComplex _).sub ((hφ.archDerivAtComplex _).smul _)).smul _

theorem IsArchSmoothAtComplex.archDelBarAt {w : InfinitePlace F} {hw : w.IsComplex} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAtComplex hw φ) (d : ArchDir) : IsArchSmoothAtComplex hw (archDelBarAt hw d φ) := by
  unfold AutomorphicForm.archDelBarAt
  exact ((hφ.archDerivAtComplex _).add ((hφ.archDerivAtComplex _).smul _)).smul _

theorem IsArchSmoothAtComplex.archCasimirAtComplex {w : InfinitePlace F} {hw : w.IsComplex} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAtComplex hw φ) : IsArchSmoothAtComplex hw (archCasimirAtComplex hw φ) := by
  unfold AutomorphicForm.archCasimirAtComplex
  exact (((((hφ.archDelAt .H).archDelAt .H).smul _).sub ((hφ.archDelAt .H).smul _)).add
    ((hφ.archDelAt .Fm).archDelAt .E)).neg

theorem IsArchSmoothAtComplex.archCasimirBarAtComplex {w : InfinitePlace F} {hw : w.IsComplex}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAtComplex hw φ) :
    IsArchSmoothAtComplex hw (archCasimirBarAtComplex hw φ) := by
  unfold AutomorphicForm.archCasimirBarAtComplex
  exact (((((hφ.archDelBarAt .H).archDelBarAt .H).smul _).sub ((hφ.archDelBarAt .H).smul _)).add
    ((hφ.archDelBarAt .Fm).archDelBarAt .E)).neg

theorem archComplexGLAt_mul_comm_of_glArch_eq_one {w : InfinitePlace F} (hw : w.IsComplex) (m : GL (Fin 2) ℂ)
    {k : AdelicGL2 (𝓞 F) F} (hk : AdelicLevel.glArch (𝓞 F) F k = 1) :
    archComplexGLAt hw m * k = k * archComplexGLAt hw m := by
  have hfin : AdelicLevel.glFin (𝓞 F) F (archComplexGLAt hw m) = 1 := glFin_adelicArchGLIncl F _
  refine eq_of_glArch_eq_of_glFin_eq ?_ ?_
  · rw [map_mul, map_mul, hk, mul_one, one_mul]
  · rw [map_mul, map_mul, hfin, mul_one, one_mul]

theorem archComplexLiftAt_mul_comm_of_glArch_eq_one {w : InfinitePlace F} (hw : w.IsComplex) (e : Fin 2 → Fin 2 → ℂ)
    {k : AdelicGL2 (𝓞 F) F} (hk : AdelicLevel.glArch (𝓞 F) F k = 1) :
    archComplexLiftAt hw e * k = k * archComplexLiftAt hw e := by
  unfold archComplexLiftAt
  split_ifs
  · exact archComplexGLAt_mul_comm_of_glArch_eq_one hw _ hk
  · rw [one_mul, mul_one]

theorem archFlowAtComplex_mul_comm_of_glArch_eq_one {w : InfinitePlace F} (hw : w.IsComplex) (d : ArchDirComplex)
    (t : ℝ) {k : AdelicGL2 (𝓞 F) F} (hk : AdelicLevel.glArch (𝓞 F) F k = 1) :
    archFlowAtComplex hw d t * k = k * archFlowAtComplex hw d t :=
  archComplexGLAt_mul_comm_of_glArch_eq_one hw _ hk

theorem IsArchSmoothAtComplex.comp_mul_right {w : InfinitePlace F} {hw : w.IsComplex} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAtComplex hw φ) {k : AdelicGL2 (𝓞 F) F} (hk : AdelicLevel.glArch (𝓞 F) F k = 1) :
    IsArchSmoothAtComplex hw fun g => φ (g * k) := by
  intro g
  show ContDiffOn ℝ (⊤ : ℕ∞) (fun e => φ (g * archComplexLiftAt hw e * k)) _
  have hfun : (fun e : Fin 2 → Fin 2 → ℂ => φ (g * archComplexLiftAt hw e * k)) =
      fun e => φ (g * k * archComplexLiftAt hw e) := by
    funext e
    rw [mul_assoc, archComplexLiftAt_mul_comm_of_glArch_eq_one hw e hk, ← mul_assoc]
  rw [hfun]
  exact hφ (g * k)

theorem archDerivAtComplex_comp_mul_right {w : InfinitePlace F} (hw : w.IsComplex) (d : ArchDirComplex)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) {k : AdelicGL2 (𝓞 F) F} (hk : AdelicLevel.glArch (𝓞 F) F k = 1) :
    archDerivAtComplex hw d (fun g => φ (g * k)) = fun g => archDerivAtComplex hw d φ (g * k) := by
  funext g
  show deriv (fun t : ℝ => φ (g * archFlowAtComplex hw d t * k)) 0 =
    deriv (fun t : ℝ => φ (g * k * archFlowAtComplex hw d t)) 0
  congr 1
  funext t
  rw [mul_assoc, archFlowAtComplex_mul_comm_of_glArch_eq_one hw d t hk, ← mul_assoc]

theorem archDelAt_comp_mul_right {w : InfinitePlace F} (hw : w.IsComplex) (d : ArchDir)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) {k : AdelicGL2 (𝓞 F) F} (hk : AdelicLevel.glArch (𝓞 F) F k = 1) :
    archDelAt hw d (fun g => φ (g * k)) = fun g => archDelAt hw d φ (g * k) := by
  unfold AutomorphicForm.archDelAt
  rw [archDerivAtComplex_comp_mul_right hw _ φ hk, archDerivAtComplex_comp_mul_right hw _ φ hk]
  funext g
  simp only [Pi.smul_apply, Pi.sub_apply]

theorem archDelBarAt_comp_mul_right {w : InfinitePlace F} (hw : w.IsComplex) (d : ArchDir)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) {k : AdelicGL2 (𝓞 F) F} (hk : AdelicLevel.glArch (𝓞 F) F k = 1) :
    archDelBarAt hw d (fun g => φ (g * k)) = fun g => archDelBarAt hw d φ (g * k) := by
  unfold AutomorphicForm.archDelBarAt
  rw [archDerivAtComplex_comp_mul_right hw _ φ hk, archDerivAtComplex_comp_mul_right hw _ φ hk]
  funext g
  simp only [Pi.smul_apply, Pi.add_apply]

theorem archCasimirAtComplex_comp_mul_right {w : InfinitePlace F} (hw : w.IsComplex) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    {k : AdelicGL2 (𝓞 F) F} (hk : AdelicLevel.glArch (𝓞 F) F k = 1) :
    archCasimirAtComplex hw (fun g => φ (g * k)) = fun g => archCasimirAtComplex hw φ (g * k) := by
  unfold AutomorphicForm.archCasimirAtComplex
  rw [archDelAt_comp_mul_right hw .H φ hk, archDelAt_comp_mul_right hw .H (archDelAt hw .H φ) hk,
    archDelAt_comp_mul_right hw .Fm φ hk, archDelAt_comp_mul_right hw .E (archDelAt hw .Fm φ) hk]
  funext g
  simp only [Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply]

theorem archCasimirBarAtComplex_comp_mul_right {w : InfinitePlace F} (hw : w.IsComplex)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) {k : AdelicGL2 (𝓞 F) F} (hk : AdelicLevel.glArch (𝓞 F) F k = 1) :
    archCasimirBarAtComplex hw (fun g => φ (g * k)) = fun g => archCasimirBarAtComplex hw φ (g * k) := by
  unfold AutomorphicForm.archCasimirBarAtComplex
  rw [archDelBarAt_comp_mul_right hw .H φ hk, archDelBarAt_comp_mul_right hw .H (archDelBarAt hw .H φ) hk,
    archDelBarAt_comp_mul_right hw .Fm φ hk, archDelBarAt_comp_mul_right hw .E (archDelBarAt hw .Fm φ) hk]
  funext g
  simp only [Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply]

theorem IsArchSmoothAtComplex.comp_mul_left {w : InfinitePlace F} {hw : w.IsComplex} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAtComplex hw φ) (h : AdelicGL2 (𝓞 F) F) : IsArchSmoothAtComplex hw fun g => φ (h * g) := by
  intro g
  show ContDiffOn ℝ (⊤ : ℕ∞) (fun e => φ (h * (g * archComplexLiftAt hw e))) _
  simp only [← mul_assoc]
  exact hφ (h * g)

theorem archDerivAtComplex_comp_mul_left {w : InfinitePlace F} (hw : w.IsComplex) (d : ArchDirComplex)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (h : AdelicGL2 (𝓞 F) F) :
    archDerivAtComplex hw d (fun g => φ (h * g)) = fun g => archDerivAtComplex hw d φ (h * g) := by
  funext g
  show deriv (fun t : ℝ => φ (h * (g * archFlowAtComplex hw d t))) 0 =
    deriv (fun t : ℝ => φ (h * g * archFlowAtComplex hw d t)) 0
  simp only [mul_assoc]

theorem archComplexGLAt_glEquivOfRingEquiv {w : InfinitePlace F} (hw : w.IsComplex) (k : GL (Fin 2) w.Completion) :
    archComplexGLAt hw (glEquivOfRingEquiv (ringEquivComplexOfIsComplex hw) k) = adelicArchGLInclAt F w k := by
  show adelicArchGLInclAt F w
    (glEquivOfRingEquiv (ringEquivComplexOfIsComplex hw).symm
      (glEquivOfRingEquiv (ringEquivComplexOfIsComplex hw) k)) = adelicArchGLInclAt F w k
  congr 1
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [glEquivOfRingEquiv_apply_entry, glEquivOfRingEquiv_apply_entry]
  exact (ringEquivComplexOfIsComplex hw).symm_apply_apply _

def archComplexProjAt {w : InfinitePlace F} (hw : w.IsComplex) : AdelicGL2 (𝓞 F) F →* GL (Fin 2) ℂ :=
  (glEquivOfRingEquiv (ringEquivComplexOfIsComplex hw)).toMonoidHom.comp
    ((AdelicLevel.archComponent F w).comp (AdelicLevel.glArch (𝓞 F) F))

theorem archComplexProjAt_archComplexGLAt {w : InfinitePlace F} (hw : w.IsComplex) (m : GL (Fin 2) ℂ) :
    archComplexProjAt hw (archComplexGLAt hw m) = m := by
  have h1 : AdelicLevel.glArch (𝓞 F) F (archComplexGLAt hw m) =
      archGLIncl F w (glEquivOfRingEquiv (ringEquivComplexOfIsComplex hw).symm m) :=
    glArch_adelicArchGLIncl F _
  have h2 : AdelicLevel.archComponent F w (AdelicLevel.glArch (𝓞 F) F (archComplexGLAt hw m)) =
      glEquivOfRingEquiv (ringEquivComplexOfIsComplex hw).symm m := by
    rw [h1, archComponent_archGLIncl_self]
  show glEquivOfRingEquiv (ringEquivComplexOfIsComplex hw)
    (AdelicLevel.archComponent F w (AdelicLevel.glArch (𝓞 F) F (archComplexGLAt hw m))) = m
  rw [h2]
  ext i j
  rw [glEquivOfRingEquiv_apply_entry, glEquivOfRingEquiv_apply_entry]
  exact (ringEquivComplexOfIsComplex hw).apply_symm_apply _

theorem circleGL2_coe (ζ : ℂˣ) : (circleGL2 ζ : Matrix (Fin 2) (Fin 2) ℂ) = !![(ζ : ℂ), 0; 0, ((ζ⁻¹ : ℂˣ) : ℂ)] :=
  rfl

theorem circleGL2_one : circleGL2 1 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [circleGL2]

theorem circleGL2_mul (ζ ζ' : ℂˣ) : circleGL2 (ζ * ζ') = circleGL2 ζ * circleGL2 ζ' := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [circleGL2, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem archCircleAt_one {w : InfinitePlace F} (hw : w.IsComplex) : archCircleAt hw 1 = 1 := by
  rw [archCircleAt, circleGL2_one, map_one]

theorem archCircleAt_mul {w : InfinitePlace F} (hw : w.IsComplex) (ζ ζ' : ℂˣ) :
    archCircleAt hw (ζ * ζ') = archCircleAt hw ζ * archCircleAt hw ζ' := by
  rw [archCircleAt, circleGL2_mul, map_mul]; rfl

theorem archCircleAt_mul_comm_of_glArch_eq_one {w : InfinitePlace F} (hw : w.IsComplex) (ζ : ℂˣ)
    {k : AdelicGL2 (𝓞 F) F} (hk : AdelicLevel.glArch (𝓞 F) F k = 1) :
    archCircleAt hw ζ * k = k * archCircleAt hw ζ :=
  archComplexGLAt_mul_comm_of_glArch_eq_one hw _ hk

theorem HasCircleWeightAt.comp_mul_right {w : InfinitePlace F} {hw : w.IsComplex} {m : ℤ}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : HasCircleWeightAt hw m φ)
    {k : AdelicGL2 (𝓞 F) F} (hk : AdelicLevel.glArch (𝓞 F) F k = 1) :
    HasCircleWeightAt hw m fun g => φ (g * k) := by
  intro ζ hζ g
  show φ (g * archCircleAt hw ζ * k) = (ζ : ℂ) ^ m * φ (g * k)
  rw [mul_assoc, archCircleAt_mul_comm_of_glArch_eq_one hw ζ hk, ← mul_assoc]
  exact hφ ζ hζ (g * k)

theorem HasCircleWeightAt.add {w : InfinitePlace F} {hw : w.IsComplex} {m : ℤ} {φ ψ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : HasCircleWeightAt hw m φ) (hψ : HasCircleWeightAt hw m ψ) : HasCircleWeightAt hw m (φ + ψ) := by
  intro ζ hζ g
  simp only [Pi.add_apply, hφ ζ hζ g, hψ ζ hζ g, mul_add]

theorem HasCircleWeightAt.smul {w : InfinitePlace F} {hw : w.IsComplex} {m : ℤ} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : HasCircleWeightAt hw m φ) (c : ℂ) : HasCircleWeightAt hw m (c • φ) := by
  intro ζ hζ g
  simp only [Pi.smul_apply, smul_eq_mul, hφ ζ hζ g]
  ring

end AutomorphicForm

end


