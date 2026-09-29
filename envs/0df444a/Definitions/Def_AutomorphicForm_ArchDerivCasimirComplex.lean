-- Prove2me | Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
-- name    : AutomorphicForm_ArchDerivCasimirComplex
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/05c886b1-12d0-5209-80fd-5d2b07a1f851
-- title:
--   Archimedean derivatives and Casimir operators at a complex place
-- statement:
--   Throughout, $F$ is a number field and $w$ an infinite place of $F$ together with a proof `hw` that $w$ is complex; $\varphi$ denotes a complex-valued function on $\mathrm{GL}_2$ of the adeles of $F$. The monoid homomorphism `archComplexGLAt` transports $\mathrm{GL}_2(\mathbb{C})$ to $\mathrm{GL}_2(F_w)$ along the inverse of the ring isomorphism $F_w\cong\mathbb{C}$ attached to `hw`, and then includes it adelically at $w$ (identity at the other infinite places, trivial finite part); `archComplexLiftAt` extends this to an arbitrary array $e$ of complex entries, sending $e$ with $\det e\neq 0$ to the corresponding adelic element and all singular $e$ to $1$. The predicate `IsArchSmoothAtComplex` asks that for every adelic $g$ the map $e\mapsto\varphi(g\cdot\text{lift}(e))$ be $C^\infty$ in the real sense on the open set $\{\det e\neq 0\}$ of the real $8$-dimensional space of $2\times 2$ complex arrays; no holomorphy is imposed. The inductive type `ArchDirComplex` has six constructors $H,E,F_-,iH,iE,iF_-$, and `archFlowMatrixComplex` assigns to each the real one-parameter subgroup $t\mapsto \mathrm{diag}(e^{z},e^{-z})$, upper unipotent with entry $z$, or lower unipotent with entry $z$, where $z=t$ for the first three and $z=ti$ for the last three; `archFlowAtComplex` places these at $w$, and `archDerivAtComplex` is the derivative at $t=0$ of $t\mapsto\varphi(g\cdot\text{flow}(t))$. From these, `archDelAt` and `archDelBarAt` form $\tfrac12(D_X\mp i D_{iX})$ for $X\in\{H,E,F_-\}$, and `archCasimirAtComplex`, `archCasimirBarAtComplex` are $-\bigl(\tfrac14\partial_H\partial_H-\tfrac12\partial_H+\partial_E\partial_{F_-}\bigr)$ and its barred analogue; `archKCasimirAtComplex` is the unnormalised sum of squares of the directions $iH$, $E-F_-$ and $iE+iF_-$. Finally `circleGL2` is $\mathrm{diag}(\zeta,\zeta^{-1})$ for $\zeta\in\mathbb{C}^\times$, `archCircleAt` places it at $w$, and `HasCircleWeightAt hw m φ` asserts $\varphi(g\cdot\mathrm{diag}(\zeta,\zeta^{-1})_w)=\zeta^m\varphi(g)$ for all $g$ and all $\zeta$ of modulus $1$. Accompanying lemmas record that the set of invertible arrays is open, that each flow satisfies $\text{flow}(0)=1$ and $\text{flow}(s+t)=\text{flow}(s)\text{flow}(t)$, that constants are smooth and killed by all these operators, and that the zero function has every circle weight.
--
--   **Relation to Mathlib.** Mathlib supplies the ambient ingredients (general linear groups, `ContDiffOn`, `deriv`, the infinite adele ring and completions at infinite places); the archimedean directions, the one-parameter flows at a place, the smoothness predicate, the Casimir operators and the circle-weight predicate are the project's own, mirroring the real-place module name for name.
--
--   **Where it is used.** These definitions supply the archimedean conditions at a complex place in the project's notion of automorphic form on $\mathrm{GL}_2$ over a number field, alongside the real-place analogues: smoothness, eigenvalue conditions for the two $\mathfrak{sl}_2(\mathbb{C})$ Casimir operators and for the compact Casimir, and the weight of the diagonal circle.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_ArchDerivCasimirComplex.lean

import Definitions.Def_AutomorphicForm_ArchDerivCasimir

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace AutomorphicForm

open NumberField NumberField.InfinitePlace.Completion Matrix Complex

variable (F : Type) [Field F] [NumberField F]

section ComplexPlaceTransport

variable {F}

def archComplexGLAt {w : InfinitePlace F} (hw : w.IsComplex) : GL (Fin 2) ℂ →* AdelicGL2 (𝓞 F) F :=
  (adelicArchGLInclAt F w).comp (glEquivOfRingEquiv (ringEquivComplexOfIsComplex hw).symm).toMonoidHom

def archComplexLiftAt {w : InfinitePlace F} (hw : w.IsComplex) (e : Fin 2 → Fin 2 → ℂ) : AdelicGL2 (𝓞 F) F :=
  if h : (Matrix.of e).det ≠ 0 then archComplexGLAt hw (GeneralLinearGroup.mkOfDetNeZero (Matrix.of e) h) else 1

theorem archComplexLiftAt_of_det_ne_zero {w : InfinitePlace F} (hw : w.IsComplex) {e : Fin 2 → Fin 2 → ℂ}
    (h : (Matrix.of e).det ≠ 0) :
    archComplexLiftAt hw e = archComplexGLAt hw (GeneralLinearGroup.mkOfDetNeZero (Matrix.of e) h) :=
  dif_pos h

theorem isOpen_setOf_det_ne_zero_complex :
    IsOpen {e : Fin 2 → Fin 2 → ℂ | (Matrix.of e).det ≠ 0} :=
  (isClosed_singleton.preimage (continuous_id.matrix_det)).isOpen_compl

def IsArchSmoothAtComplex {w : InfinitePlace F} (hw : w.IsComplex) (φ : AdelicGL2 (𝓞 F) F → ℂ) : Prop :=
  ∀ g : AdelicGL2 (𝓞 F) F,
    ContDiffOn ℝ (⊤ : ℕ∞) (fun e : Fin 2 → Fin 2 → ℂ => φ (g * archComplexLiftAt hw e))
      {e | (Matrix.of e).det ≠ 0}

theorem isArchSmoothAtComplex_const {w : InfinitePlace F} (hw : w.IsComplex) (c : ℂ) :
    IsArchSmoothAtComplex hw (fun _ => c) :=
  fun _ => contDiffOn_const

end ComplexPlaceTransport

section ComplexFlows

variable {F}

inductive ArchDirComplex where
  | H : ArchDirComplex
  | E : ArchDirComplex
  | Fm : ArchDirComplex
  | iH : ArchDirComplex
  | iE : ArchDirComplex
  | iFm : ArchDirComplex

def ArchDir.toComplex : ArchDir → ArchDirComplex
  | .H => .H
  | .E => .E
  | .Fm => .Fm

def ArchDir.toComplexI : ArchDir → ArchDirComplex
  | .H => .iH
  | .E => .iE
  | .Fm => .iFm

def splitTorusGL2Complex (z : ℂ) : GL (Fin 2) ℂ where
  val := !![Complex.exp z, 0; 0, Complex.exp (-z)]
  inv := !![Complex.exp (-z), 0; 0, Complex.exp z]
  val_inv := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, ← Complex.exp_add]
  inv_val := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, ← Complex.exp_add]

theorem splitTorusGL2Complex_zero : splitTorusGL2Complex 0 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [splitTorusGL2Complex]

theorem splitTorusGL2Complex_add (z z' : ℂ) : splitTorusGL2Complex (z + z') = splitTorusGL2Complex z * splitTorusGL2Complex z' := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [splitTorusGL2Complex, Matrix.mul_apply, Fin.sum_univ_two, Complex.exp_add]; ring_nf

def archFlowMatrixComplex : ArchDirComplex → ℝ → GL (Fin 2) ℂ
  | .H, t => splitTorusGL2Complex (t : ℂ)
  | .E, t => unipotentGL2 (t : ℂ)
  | .Fm, t => lowerUnipotentGL2 (t : ℂ)
  | .iH, t => splitTorusGL2Complex ((t : ℂ) * I)
  | .iE, t => unipotentGL2 ((t : ℂ) * I)
  | .iFm, t => lowerUnipotentGL2 ((t : ℂ) * I)

theorem archFlowMatrixComplex_zero (d : ArchDirComplex) : archFlowMatrixComplex d 0 = 1 := by
  cases d
  · simpa [archFlowMatrixComplex] using splitTorusGL2Complex_zero
  · simp [archFlowMatrixComplex, unipotentGL2_zero]
  · simp [archFlowMatrixComplex, lowerUnipotentGL2_zero]
  · simpa [archFlowMatrixComplex] using splitTorusGL2Complex_zero
  · simp [archFlowMatrixComplex, unipotentGL2_zero]
  · simp [archFlowMatrixComplex, lowerUnipotentGL2_zero]

theorem archFlowMatrixComplex_add (d : ArchDirComplex) (s t : ℝ) :
    archFlowMatrixComplex d (s + t) = archFlowMatrixComplex d s * archFlowMatrixComplex d t := by
  cases d
  · simp [archFlowMatrixComplex, ← splitTorusGL2Complex_add]
  · simp [archFlowMatrixComplex, ← unipotentGL2_add]
  · simp [archFlowMatrixComplex, ← lowerUnipotentGL2_add]
  · simp [archFlowMatrixComplex, ← splitTorusGL2Complex_add, add_mul]
  · simp [archFlowMatrixComplex, ← unipotentGL2_add, add_mul]
  · simp [archFlowMatrixComplex, ← lowerUnipotentGL2_add, add_mul]

def archFlowAtComplex {w : InfinitePlace F} (hw : w.IsComplex) (d : ArchDirComplex) (t : ℝ) : AdelicGL2 (𝓞 F) F :=
  archComplexGLAt hw (archFlowMatrixComplex d t)

theorem archFlowAtComplex_zero {w : InfinitePlace F} (hw : w.IsComplex) (d : ArchDirComplex) : archFlowAtComplex hw d 0 = 1 := by
  rw [archFlowAtComplex, archFlowMatrixComplex_zero, map_one]

theorem archFlowAtComplex_add {w : InfinitePlace F} (hw : w.IsComplex) (d : ArchDirComplex) (s t : ℝ) :
    archFlowAtComplex hw d (s + t) = archFlowAtComplex hw d s * archFlowAtComplex hw d t := by
  rw [archFlowAtComplex, archFlowMatrixComplex_add, map_mul]; rfl

def archDerivAtComplex {w : InfinitePlace F} (hw : w.IsComplex) (d : ArchDirComplex) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    AdelicGL2 (𝓞 F) F → ℂ :=
  fun g => deriv (fun t : ℝ => φ (g * archFlowAtComplex hw d t)) 0

def archDelAt {w : InfinitePlace F} (hw : w.IsComplex) (d : ArchDir) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    AdelicGL2 (𝓞 F) F → ℂ :=
  (1 / 2 : ℂ) • (archDerivAtComplex hw d.toComplex φ - I • archDerivAtComplex hw d.toComplexI φ)

def archDelBarAt {w : InfinitePlace F} (hw : w.IsComplex) (d : ArchDir) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    AdelicGL2 (𝓞 F) F → ℂ :=
  (1 / 2 : ℂ) • (archDerivAtComplex hw d.toComplex φ + I • archDerivAtComplex hw d.toComplexI φ)

def archCasimirAtComplex {w : InfinitePlace F} (hw : w.IsComplex) (φ : AdelicGL2 (𝓞 F) F → ℂ) : AdelicGL2 (𝓞 F) F → ℂ :=
  -((1 / 4 : ℂ) • archDelAt hw .H (archDelAt hw .H φ) - (1 / 2 : ℂ) • archDelAt hw .H φ +
    archDelAt hw .E (archDelAt hw .Fm φ))

def archCasimirBarAtComplex {w : InfinitePlace F} (hw : w.IsComplex) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    AdelicGL2 (𝓞 F) F → ℂ :=
  -((1 / 4 : ℂ) • archDelBarAt hw .H (archDelBarAt hw .H φ) - (1 / 2 : ℂ) • archDelBarAt hw .H φ +
    archDelBarAt hw .E (archDelBarAt hw .Fm φ))

def archKCasimirAtComplex {w : InfinitePlace F} (hw : w.IsComplex) (φ : AdelicGL2 (𝓞 F) F → ℂ) : AdelicGL2 (𝓞 F) F → ℂ :=
  archDerivAtComplex hw .iH (archDerivAtComplex hw .iH φ) +
    (archDerivAtComplex hw .E (archDerivAtComplex hw .E φ - archDerivAtComplex hw .Fm φ) -
      archDerivAtComplex hw .Fm (archDerivAtComplex hw .E φ - archDerivAtComplex hw .Fm φ)) +
    (archDerivAtComplex hw .iE (archDerivAtComplex hw .iE φ + archDerivAtComplex hw .iFm φ) +
      archDerivAtComplex hw .iFm (archDerivAtComplex hw .iE φ + archDerivAtComplex hw .iFm φ))

theorem archDerivAtComplex_const {w : InfinitePlace F} (hw : w.IsComplex) (d : ArchDirComplex) (c : ℂ) :
    archDerivAtComplex hw d (fun _ => c) = fun _ => 0 := by
  funext g; simp [archDerivAtComplex]

theorem archDelAt_const {w : InfinitePlace F} (hw : w.IsComplex) (d : ArchDir) (c : ℂ) :
    archDelAt hw d (fun _ => c) = fun _ => 0 := by
  funext g; simp [archDelAt, archDerivAtComplex_const]

theorem archDelBarAt_const {w : InfinitePlace F} (hw : w.IsComplex) (d : ArchDir) (c : ℂ) :
    archDelBarAt hw d (fun _ => c) = fun _ => 0 := by
  funext g; simp [archDelBarAt, archDerivAtComplex_const]

theorem archCasimirAtComplex_const {w : InfinitePlace F} (hw : w.IsComplex) (c : ℂ) :
    archCasimirAtComplex hw (fun _ => c) = fun _ => 0 := by
  funext g
  simp [archCasimirAtComplex, archDelAt_const]

theorem archCasimirBarAtComplex_const {w : InfinitePlace F} (hw : w.IsComplex) (c : ℂ) :
    archCasimirBarAtComplex hw (fun _ => c) = fun _ => 0 := by
  funext g
  simp [archCasimirBarAtComplex, archDelBarAt_const]

end ComplexFlows

section Circle

variable {F}

def circleGL2 (ζ : ℂˣ) : GL (Fin 2) ℂ where
  val := !![(ζ : ℂ), 0; 0, ((ζ⁻¹ : ℂˣ) : ℂ)]
  inv := !![((ζ⁻¹ : ℂˣ) : ℂ), 0; 0, (ζ : ℂ)]
  val_inv := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

def archCircleAt {w : InfinitePlace F} (hw : w.IsComplex) (ζ : ℂˣ) : AdelicGL2 (𝓞 F) F :=
  archComplexGLAt hw (circleGL2 ζ)

def HasCircleWeightAt {w : InfinitePlace F} (hw : w.IsComplex) (m : ℤ) (φ : AdelicGL2 (𝓞 F) F → ℂ) : Prop :=
  ∀ (ζ : ℂˣ), ‖(ζ : ℂ)‖ = 1 → ∀ g : AdelicGL2 (𝓞 F) F, φ (g * archCircleAt hw ζ) = (ζ : ℂ) ^ m * φ g

theorem hasCircleWeightAt_zero {w : InfinitePlace F} (hw : w.IsComplex) (m : ℤ) :
    HasCircleWeightAt hw m (fun _ => (0 : ℂ)) := fun _ _ _ => by simp

end Circle

end AutomorphicForm

end


