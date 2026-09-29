-- Prove2me | Definitions.Def_AutomorphicForm_ArchLoweringAnnihilated
-- name    : AutomorphicForm_ArchLoweringAnnihilated
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/5352083f-bcfd-5a5a-81df-e197b6dd7cad
-- title:
--   Archimedean lowering operator and its annihilation predicate
-- statement:
--   Throughout, $F$ is a number field, $w$ an infinite place of $F$ with a proof `hw` that $w$ is real, and $\varphi$ a complex-valued function on $\mathrm{GL}_2$ of the adele ring of $F$. Three things are defined.
--
--   First, `loweringAt` acts on a function $f$ of a real $2\times 2$ matrix (regarded as a function of its entries, so that the real Fréchet derivative `fderiv ℝ` applies) and a matrix $m$, producing
--   $$\tfrac12\Bigl(Df(m)\bigl[m\begin{pmatrix}1&0\\0&-1\end{pmatrix}\bigr]-i\,Df(m)\bigl[m\begin{pmatrix}0&1\\1&0\end{pmatrix}\bigr]\Bigr).$$
--   This is the right-translation action of the element $\tfrac12(\hat H-iS)$ of $\mathfrak{gl}_2(\mathbb R)\otimes\mathbb C$, the operator lowering the $\mathrm{SO}(2)$-weight by $2$. Its value on a constant function is $0$.
--
--   Second, `archSliceAt w hw φ g` is the function on real $2\times 2$ matrices sending $m$ with $\det m\neq 0$ to $\varphi\bigl(g\cdot\iota_w(m)\bigr)$, where $m$ is carried into $\mathrm{GL}_2$ of the completion $F_w$ along the inverse of the isomorphism $F_w\cong\mathbb R$ attached to a real place, and $\iota_w$ is `adelicArchGLInclAt`, the embedding placing an element of $\mathrm{GL}_2(F_w)$ at $w$, the identity at all other infinite places and $1$ at the finite part; singular $m$ are sent to $0$. Accompanying lemmas evaluate the slice on invertible matrices, in particular at the Iwasawa section $\begin{pmatrix}y&x\\0&1\end{pmatrix}$ attached to $z=x+iy$ in the upper half-plane, and record that the slice of the zero function is zero and that it is homogeneous in $\varphi$ under multiplication by a constant.
--
--   Third, `IsArchLoweringAnnihilatedAt w hw φ` asserts that for every adelic $g$ and every $z$ in the upper half-plane the slice `archSliceAt w hw φ g` is real-differentiable at $\begin{pmatrix}\mathrm{Im}\,z&\mathrm{Re}\,z\\0&1\end{pmatrix}$ and `loweringAt` of it vanishes there. The zero function satisfies the predicate.
--
--   **Relation to Mathlib.** Mathlib supplies the differential calculus (`fderiv`), the upper half-plane and the completions at infinite places; the lowering operator, the archimedean slice of an adelic function and the annihilation predicate are the project's own notions.
--
--   **Where it is used.** The predicate expresses, at a real place, that an adelic function is killed by the weight-lowering element of the complexified Lie algebra of $\mathrm{GL}_2(F_w)$, without putting a manifold structure on the adelic group. It is the archimedean condition used alongside the weight character `archWeightOneAt` in the cuspidality notions through which Hecke eigensystems are realised by automorphic functions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_ArchLoweringAnnihilated.lean

import Mathlib
import Definitions.Def_AutomorphicForm_ViaCompactCuspNotion

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion

noncomputable section

namespace AutomorphicForm

def loweringAt (f : (Fin 2 → Fin 2 → ℝ) → ℂ) (m : Matrix (Fin 2) (Fin 2) ℝ) : ℂ :=
  (fderiv ℝ f m (m * !![1, 0; 0, -1]) - Complex.I * fderiv ℝ f m (m * !![0, 1; 1, 0])) / 2

theorem loweringAt_eq (f : (Fin 2 → Fin 2 → ℝ) → ℂ) (m : Matrix (Fin 2) (Fin 2) ℝ) :
    loweringAt f m =
      (fderiv ℝ f m (m * !![1, 0; 0, -1]) - Complex.I * fderiv ℝ f m (m * !![0, 1; 1, 0])) / 2 :=
  rfl

theorem loweringAt_const (c : ℂ) (m : Matrix (Fin 2) (Fin 2) ℝ) :
    loweringAt (fun _ => c) m = 0 := by
  have h : fderiv ℝ (fun _ : Fin 2 → Fin 2 → ℝ => c) (m : Fin 2 → Fin 2 → ℝ) = 0 := by
    rw [fderiv_fun_const]
    rfl
  simp [loweringAt, h]

variable {F : Type} [Field F] [NumberField F]

def archSliceAt (w : InfinitePlace F) (hw : w.IsReal) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (g : AdelicGL2 (𝓞 F) F) (m : Fin 2 → Fin 2 → ℝ) : ℂ :=
  if h : (Matrix.of m).det ≠ 0 then
    φ (g * adelicArchGLInclAt F w
      (Matrix.GeneralLinearGroup.map (ringEquivRealOfIsReal hw).symm.toRingHom
        (Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of m) h)))
  else 0

theorem archSliceAt_apply_of_det_ne_zero (w : InfinitePlace F) (hw : w.IsReal)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) (m : Fin 2 → Fin 2 → ℝ)
    (h : (Matrix.of m).det ≠ 0) :
    archSliceAt w hw φ g m =
      φ (g * adelicArchGLInclAt F w
        (Matrix.GeneralLinearGroup.map (ringEquivRealOfIsReal hw).symm.toRingHom
          (Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of m) h))) := by
  simp [archSliceAt, h]

theorem archSliceAt_apply_of_det_eq_zero (w : InfinitePlace F) (hw : w.IsReal)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) (m : Fin 2 → Fin 2 → ℝ)
    (h : (Matrix.of m).det = 0) :
    archSliceAt w hw φ g m = 0 := by
  simp [archSliceAt, h]

theorem archSliceAt_coe_generalLinearGroup (w : InfinitePlace F) (hw : w.IsReal)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) (m : GL (Fin 2) ℝ) :
    archSliceAt w hw φ g ((m : Matrix (Fin 2) (Fin 2) ℝ) : Fin 2 → Fin 2 → ℝ) =
      φ (g * adelicArchGLInclAt F w
        (Matrix.GeneralLinearGroup.map (ringEquivRealOfIsReal hw).symm.toRingHom m)) := by
  have h : (Matrix.of ((m : Matrix (Fin 2) (Fin 2) ℝ) : Fin 2 → Fin 2 → ℝ)).det ≠ 0 := by
    have : Matrix.of ((m : Matrix (Fin 2) (Fin 2) ℝ) : Fin 2 → Fin 2 → ℝ) = (m : Matrix _ _ ℝ) :=
      rfl
    rw [this, ← Matrix.GeneralLinearGroup.val_det_apply]
    exact (Matrix.GeneralLinearGroup.det m).ne_zero
  rw [archSliceAt_apply_of_det_ne_zero w hw φ g _ h]
  congr 3
  ext i j
  rfl

theorem archSliceAt_iwasawa (w : InfinitePlace F) (hw : w.IsReal)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) (z : UpperHalfPlane) :
    archSliceAt w hw φ g (!![z.im, z.re; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) =
      φ (g * adelicArchGLInclAt F w
        (Matrix.GeneralLinearGroup.map (ringEquivRealOfIsReal hw).symm.toRingHom
          (iwasawaSectionGL z))) :=
  archSliceAt_coe_generalLinearGroup w hw φ g (iwasawaSectionGL z)

theorem archSliceAt_zero (w : InfinitePlace F) (hw : w.IsReal) (g : AdelicGL2 (𝓞 F) F) :
    archSliceAt w hw (fun _ => (0 : ℂ)) g = fun _ => 0 := by
  funext m
  by_cases h : (Matrix.of m).det ≠ 0
  · simp [archSliceAt, h]
  · simp [archSliceAt, h]

theorem archSliceAt_const_mul (w : InfinitePlace F) (hw : w.IsReal)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (a : ℂ) (g : AdelicGL2 (𝓞 F) F) :
    archSliceAt w hw (fun x => a * φ x) g = fun m => a * archSliceAt w hw φ g m := by
  funext m
  by_cases h : (Matrix.of m).det ≠ 0
  · simp [archSliceAt, h]
  · simp [archSliceAt, h]

def IsArchLoweringAnnihilatedAt (w : InfinitePlace F) (hw : w.IsReal)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) : Prop :=
  ∀ (g : AdelicGL2 (𝓞 F) F) (z : UpperHalfPlane),
    DifferentiableAt ℝ (archSliceAt w hw φ g) (!![z.im, z.re; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) ∧
      loweringAt (archSliceAt w hw φ g) !![z.im, z.re; 0, 1] = 0

theorem isArchLoweringAnnihilatedAt_iff (w : InfinitePlace F) (hw : w.IsReal)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    IsArchLoweringAnnihilatedAt w hw φ ↔
      ∀ (g : AdelicGL2 (𝓞 F) F) (z : UpperHalfPlane),
        DifferentiableAt ℝ (archSliceAt w hw φ g)
            (!![z.im, z.re; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) ∧
          loweringAt (archSliceAt w hw φ g) !![z.im, z.re; 0, 1] = 0 :=
  Iff.rfl

theorem isArchLoweringAnnihilatedAt_zero (w : InfinitePlace F) (hw : w.IsReal) :
    IsArchLoweringAnnihilatedAt w hw (fun _ => (0 : ℂ)) := by
  intro g z
  rw [archSliceAt_zero]
  exact ⟨differentiableAt_const _, loweringAt_const 0 _⟩

end AutomorphicForm

end

section Battery
open AutomorphicForm
#check @loweringAt
#check @archSliceAt
#check @IsArchLoweringAnnihilatedAt
#print axioms AutomorphicForm.loweringAt_const
#print axioms AutomorphicForm.archSliceAt_coe_generalLinearGroup
#print axioms AutomorphicForm.archSliceAt_iwasawa
#print axioms AutomorphicForm.archSliceAt_const_mul
#print axioms AutomorphicForm.isArchLoweringAnnihilatedAt_zero
end Battery


