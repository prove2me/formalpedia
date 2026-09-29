-- Prove2me | Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
-- name    : LanglandsTunnell_CubicInduction_PrincipalSeries3
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/2859ecf7-93fc-524a-85de-3b407e157ee8
-- title:
--   Local GL(3) principal series, Whittaker functionals, and nonvanishing witness
-- statement:
--   Fix a finite place $v$ of $\mathbb{Q}$, i.e. a height-one prime of $\mathcal{O}_{\mathbb{Q}}$, write $\mathbb{Q}_v$ for the adic completion, and let `LocalGL3 v` be $GL_3(\mathbb{Q}_v)$. For a triple $a$ of units of $\mathbb{Q}_v$, `diagonal3` is the diagonal element $\mathrm{diag}(a_0,a_1,a_2)$ (multiplicative in $a$); `halfModulus3` is the complex number $\lVert a_0\rVert/\lVert a_2\rVert$ in the normalised absolute value at $v$, i.e. $\delta_B^{1/2}$, evaluated explicitly at the three elementary diagonal matrices built from a uniformiser; and `torusChar3` $\chi$ $a=\prod_i\chi_i(a_i)$ for a triple $\chi$ of homomorphisms $\mathbb{Q}_v^{\times}\to\mathbb{C}^{\times}$. The principal series `principalSeries3 v χ` is then defined as a $\mathbb{C}$-submodule of all functions $f:GL_3(\mathbb{Q}_v)\to\mathbb{C}$: those that are locally constant, satisfy $f(ug)=f(g)$ for every upper-triangular unipotent $u=$ `upperUnipotent3` $x\,y\,z$, and satisfy $f(\mathrm{diag}(a)g)=\chi(a)\,\delta^{1/2}(a)\,f(g)$. Membership is closed under right translation, so the space carries the right-translation action; `coefficientFn` sends a linear form $L$ and a vector $f$ to $g\mapsto L(g\cdot f)$, and `IsWhittakerFunctional3` $\psi$ $\Lambda$ asks that $\Lambda$ transform by $\psi(x+y)$ under right translation by `upperUnipotent3` $x\,y\,z$; for such $\Lambda$ the coefficient function satisfies the $\psi$-Whittaker law `IsGL3PsiWhittakerFn`.
--
--   The remainder constructs an explicit nonzero vector. With `cornerEntry` $=g_{20}$, `lowerMinor` $=g_{10}g_{21}-g_{11}g_{20}$, `outerMinor` $=g_{10}g_{22}-g_{12}g_{20}$ and `gl3Det`, the triple `cellRatio` $=(g_{21}/g_{20},\,g_{22}/g_{20},\,\mathrm{outerMinor}/\mathrm{lowerMinor})$ cuts out `cellCutoff`: corner entry and lower minor nonzero and all three ratios of valuation $\le 1$. On it `cellValue` is $\chi_0(\det/\mathrm{lowerMinor})\,\chi_1(\mathrm{lowerMinor}/\mathrm{corner})\,\chi_2(\mathrm{corner})\cdot\lVert\det/\mathrm{lowerMinor}\rVert/\lVert\mathrm{corner}\rVert$, the characters being extended to $\mathbb{Q}_v$ by `charExt`; `cellSection` is the indicator of `cellCutoff` times `cellValue`. All these data are invariant, resp. transform correctly, under left multiplication by unipotent and diagonal elements, and local constancy is proved by a valuation analysis near the loci where a denominator vanishes; hence `cellVector` lies in `principalSeries3 v χ` whenever each $\chi_i$ is locally constant. Evaluation at the antidiagonal permutation matrix gives a linear form `evalAntidiagonal3`, and the corresponding coefficient function is shown nonzero at the identity.
--
--   **Relation to Mathlib.** Mathlib supplies $GL_n$, adic completions and their valuations and finite-place norms, and `IsLocallyConstant`; the principal series, its Whittaker functionals and the explicit big-cell section are the project's own notions.
--
--   **Where it is used.** These local objects belong to the cubic-induction package for the Langlands–Tunnell theorem, where the automorphic form on $GL_3$ induced from a character of a cubic extension is analysed place by place; its local Whittaker functions must live in such induced models, and the witness vector shows these models are nonzero.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LanglandsTunnell_CubicInduction_PrincipalSeries3.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField NumberField.AdelicLevel LanglandsTunnell.TateLocal

noncomputable section

namespace LanglandsTunnell.CubicInduction

section PrincipalSeries3

variable (v : HeightOneSpectrum (𝓞 ℚ))

def diagonal3 (a : Fin 3 → (v.adicCompletion ℚ)ˣ) : LocalGL3 v where
  val := diagonal fun i => (a i : v.adicCompletion ℚ)
  inv := diagonal fun i => ((a i)⁻¹ : (v.adicCompletion ℚ)ˣ)
  val_inv := by
    rw [diagonal_mul_diagonal]
    simp only [Units.mul_inv, diagonal_one]
  inv_val := by
    rw [diagonal_mul_diagonal]
    simp only [Units.inv_mul, diagonal_one]

theorem diagonal3_mul (a b : Fin 3 → (v.adicCompletion ℚ)ˣ) :
    diagonal3 v (a * b) = diagonal3 v a * diagonal3 v b := by
  ext i j
  rcases eq_or_ne i j with rfl | hij
  · simp [diagonal3]
  · simp [diagonal3, Matrix.diagonal_apply_ne _ hij]

@[simp] theorem diagonal3_coe (a : Fin 3 → (v.adicCompletion ℚ)ˣ) :
    (diagonal3 v a : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = diagonal fun i => (a i : v.adicCompletion ℚ) :=
  rfl

def halfModulus3 (a : Fin 3 → (v.adicCompletion ℚ)ˣ) : ℂ :=
  ((‖(a 0 : v.adicCompletion ℚ)‖ / ‖(a 2 : v.adicCompletion ℚ)‖ : ℝ) : ℂ)

theorem halfModulus3_mul (a b : Fin 3 → (v.adicCompletion ℚ)ˣ) :
    halfModulus3 v (a * b) = halfModulus3 v a * halfModulus3 v b := by
  simp only [halfModulus3, Pi.mul_apply, Units.val_mul, norm_mul]
  push_cast
  ring

@[simp] theorem halfModulus3_one : halfModulus3 v 1 = 1 := by
  simp [halfModulus3]

private theorem toAdd_unzero_exp (n : ℤ) (h : (WithZero.exp n : WithZero (Multiplicative ℤ)) ≠ 0) :
    Multiplicative.toAdd (WithZero.unzero h) = n :=
  rfl

private theorem norm_uniformizerUnit :
    ‖(uniformizerUnit ℚ v : v.adicCompletion ℚ)‖ = (((Ideal.absNorm v.asIdeal : ℕ) : ℝ))⁻¹ := by
  rw [NumberField.FinitePlace.norm_def, valued_uniformizerUnit,
    WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero, toAdd_unzero_exp]
  simp

theorem halfModulus3_uniformizerUnit :
    halfModulus3 v ![uniformizerUnit ℚ v, 1, 1] = (((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹ : ℝ) := by
  simp [halfModulus3, norm_uniformizerUnit]

theorem halfModulus3_one_uniformizerUnit_one : halfModulus3 v ![1, uniformizerUnit ℚ v, 1] = 1 := by
  simp [halfModulus3]

theorem halfModulus3_one_one_uniformizerUnit :
    halfModulus3 v ![1, 1, uniformizerUnit ℚ v] = (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) : ℝ) := by
  simp [halfModulus3, norm_uniformizerUnit]

def torusChar3 (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (a : Fin 3 → (v.adicCompletion ℚ)ˣ) : ℂ :=
  ∏ i : Fin 3, ((χ i (a i) : ℂˣ) : ℂ)

theorem torusChar3_mul (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (a b : Fin 3 → (v.adicCompletion ℚ)ˣ) :
    torusChar3 v χ (a * b) = torusChar3 v χ a * torusChar3 v χ b := by
  simp only [torusChar3, Pi.mul_apply, map_mul, Units.val_mul, Finset.prod_mul_distrib]

@[simp] theorem torusChar3_one (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) : torusChar3 v χ 1 = 1 := by
  simp [torusChar3]

def principalSeries3 (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) : Submodule ℂ (LocalGL3 v → ℂ) where
  carrier := {f | IsLocallyConstant f ∧
    (∀ (x y z : v.adicCompletion ℚ) (g : LocalGL3 v), f (upperUnipotent3 x y z * g) = f g) ∧
    ∀ (a : Fin 3 → (v.adicCompletion ℚ)ˣ) (g : LocalGL3 v),
      f (diagonal3 v a * g) = torusChar3 v χ a * halfModulus3 v a * f g}
  zero_mem' := ⟨IsLocallyConstant.const 0, fun _ _ _ _ => rfl, fun _ _ => by simp⟩
  add_mem' := by
    intro f₁ f₂ h₁ h₂
    obtain ⟨h₁lc, h₁n, h₁t⟩ := h₁
    obtain ⟨h₂lc, h₂n, h₂t⟩ := h₂
    refine ⟨h₁lc.comp₂ h₂lc (· + ·), fun x y z g => ?_, fun a g => ?_⟩
    · show f₁ _ + f₂ _ = f₁ g + f₂ g
      rw [h₁n, h₂n]
    · show f₁ _ + f₂ _ = _ * (f₁ g + f₂ g)
      rw [h₁t, h₂t]
      ring
  smul_mem' := by
    intro c f hf
    obtain ⟨hlc, hn, ht⟩ := hf
    refine ⟨hlc.comp (c * ·), fun x y z g => ?_, fun a g => ?_⟩
    · show c * f _ = c * f g
      rw [hn]
    · show c * f _ = _ * (c * f g)
      rw [ht]
      ring

variable {v}

theorem mem_principalSeries3_iff {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)} {f : LocalGL3 v → ℂ} :
    f ∈ principalSeries3 v χ ↔
      IsLocallyConstant f ∧
        (∀ (x y z : v.adicCompletion ℚ) (g : LocalGL3 v), f (upperUnipotent3 x y z * g) = f g) ∧
        ∀ (a : Fin 3 → (v.adicCompletion ℚ)ˣ) (g : LocalGL3 v),
          f (diagonal3 v a * g) = torusChar3 v χ a * halfModulus3 v a * f g :=
  Iff.rfl

theorem isLocallyConstant_of_mem_principalSeries3 {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)}
    {f : LocalGL3 v → ℂ} (hf : f ∈ principalSeries3 v χ) : IsLocallyConstant f :=
  (mem_principalSeries3_iff.mp hf).1

theorem apply_upperUnipotent3_mul_of_mem_principalSeries3 {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)}
    {f : LocalGL3 v → ℂ} (hf : f ∈ principalSeries3 v χ) (x y z : v.adicCompletion ℚ) (g : LocalGL3 v) :
    f (upperUnipotent3 x y z * g) = f g :=
  (mem_principalSeries3_iff.mp hf).2.1 x y z g

theorem apply_diagonal3_mul_of_mem_principalSeries3 {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)}
    {f : LocalGL3 v → ℂ} (hf : f ∈ principalSeries3 v χ) (a : Fin 3 → (v.adicCompletion ℚ)ˣ) (g : LocalGL3 v) :
    f (diagonal3 v a * g) = torusChar3 v χ a * halfModulus3 v a * f g :=
  (mem_principalSeries3_iff.mp hf).2.2 a g

theorem rightTranslate_mem_principalSeries3 {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)}
    {f : LocalGL3 v → ℂ} (hf : f ∈ principalSeries3 v χ) (g : LocalGL3 v) :
    gl3AmbientRightTranslate (R := ℂ) g f ∈ principalSeries3 v χ := by
  obtain ⟨hlc, hn, ht⟩ := mem_principalSeries3_iff.mp hf
  refine mem_principalSeries3_iff.mpr
    ⟨hlc.comp_continuous (continuous_id.mul continuous_const), fun x y z h => ?_, fun a h => ?_⟩
  · show f (upperUnipotent3 x y z * h * g) = f (h * g)
    rw [mul_assoc, hn]
  · show f (diagonal3 v a * h * g) = _ * f (h * g)
    rw [mul_assoc, ht]

def coefficientFn {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)} (L : ↥(principalSeries3 v χ) →ₗ[ℂ] ℂ)
    (f : ↥(principalSeries3 v χ)) : LocalGL3 v → ℂ :=
  fun g => L ⟨gl3AmbientRightTranslate (R := ℂ) g f, rightTranslate_mem_principalSeries3 f.2 g⟩

def IsWhittakerFunctional3 {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)} (ψ : AddChar (v.adicCompletion ℚ) ℂ)
    (Λ : ↥(principalSeries3 v χ) →ₗ[ℂ] ℂ) : Prop :=
  ∀ (x y z : v.adicCompletion ℚ) (F : ↥(principalSeries3 v χ)),
    Λ ⟨gl3AmbientRightTranslate (R := ℂ) (upperUnipotent3 x y z) F,
        rightTranslate_mem_principalSeries3 F.2 (upperUnipotent3 x y z)⟩ = ψ (x + y) * Λ F

theorem isWhittakerFunctional3_zero {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)} (ψ : AddChar (v.adicCompletion ℚ) ℂ) :
    IsWhittakerFunctional3 (χ := χ) ψ 0 := by
  intro x y z F
  simp

theorem isGL3PsiWhittakerFn_coefficientFn {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)}
    {ψ : AddChar (v.adicCompletion ℚ) ℂ} {Λ : ↥(principalSeries3 v χ) →ₗ[ℂ] ℂ} (hΛ : IsWhittakerFunctional3 ψ Λ)
    (f : ↥(principalSeries3 v χ)) : IsGL3PsiWhittakerFn ψ (coefficientFn Λ f) := by
  intro x y z g
  have hfun : gl3AmbientRightTranslate (R := ℂ) (upperUnipotent3 x y z * g) (f : LocalGL3 v → ℂ)
      = gl3AmbientRightTranslate (R := ℂ) (upperUnipotent3 x y z) (gl3AmbientRightTranslate (R := ℂ) g f) := by
    funext h
    simp [gl3AmbientRightTranslate, mul_assoc]
  have hsub : (⟨_, rightTranslate_mem_principalSeries3 f.2 (upperUnipotent3 x y z * g)⟩ : ↥(principalSeries3 v χ))
      = ⟨_, rightTranslate_mem_principalSeries3 (rightTranslate_mem_principalSeries3 f.2 g) (upperUnipotent3 x y z)⟩ :=
    Subtype.ext hfun
  show Λ _ = ψ (x + y) * Λ _
  rw [hsub]
  exact hΛ x y z ⟨_, rightTranslate_mem_principalSeries3 f.2 g⟩

end PrincipalSeries3

section Witness

variable (v : HeightOneSpectrum (𝓞 ℚ))

def gl3Entry (g : LocalGL3 v) (i j : Fin 3) : v.adicCompletion ℚ :=
  (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j

def cornerEntry (g : LocalGL3 v) : v.adicCompletion ℚ := gl3Entry v g 2 0

def lowerMinor (g : LocalGL3 v) : v.adicCompletion ℚ :=
  gl3Entry v g 1 0 * gl3Entry v g 2 1 - gl3Entry v g 1 1 * gl3Entry v g 2 0

def outerMinor (g : LocalGL3 v) : v.adicCompletion ℚ :=
  gl3Entry v g 1 0 * gl3Entry v g 2 2 - gl3Entry v g 1 2 * gl3Entry v g 2 0

def gl3Det (g : LocalGL3 v) : v.adicCompletion ℚ := (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)).det

theorem gl3Det_ne_zero (g : LocalGL3 v) : gl3Det v g ≠ 0 := by
  have h := (Matrix.GeneralLinearGroup.det g).ne_zero
  rwa [Matrix.GeneralLinearGroup.val_det_apply] at h

theorem gl3Entry_upperUnipotent3_mul_two (x y z : v.adicCompletion ℚ) (g : LocalGL3 v) (j : Fin 3) :
    gl3Entry v (upperUnipotent3 x y z * g) 2 j = gl3Entry v g 2 j := by
  simp [gl3Entry, Matrix.mul_apply, Fin.sum_univ_three]

theorem gl3Entry_upperUnipotent3_mul_one (x y z : v.adicCompletion ℚ) (g : LocalGL3 v) (j : Fin 3) :
    gl3Entry v (upperUnipotent3 x y z * g) 1 j = gl3Entry v g 1 j + y * gl3Entry v g 2 j := by
  simp [gl3Entry, Matrix.mul_apply, Fin.sum_univ_three]

theorem gl3Entry_diagonal3_mul (a : Fin 3 → (v.adicCompletion ℚ)ˣ) (g : LocalGL3 v) (i j : Fin 3) :
    gl3Entry v (diagonal3 v a * g) i j = (a i : v.adicCompletion ℚ) * gl3Entry v g i j := by
  simp [gl3Entry, diagonal3_coe, Matrix.diagonal_mul]

theorem cornerEntry_upperUnipotent3_mul (x y z : v.adicCompletion ℚ) (g : LocalGL3 v) :
    cornerEntry v (upperUnipotent3 x y z * g) = cornerEntry v g :=
  gl3Entry_upperUnipotent3_mul_two v x y z g 0

theorem lowerMinor_upperUnipotent3_mul (x y z : v.adicCompletion ℚ) (g : LocalGL3 v) :
    lowerMinor v (upperUnipotent3 x y z * g) = lowerMinor v g := by
  simp only [lowerMinor, gl3Entry_upperUnipotent3_mul_one, gl3Entry_upperUnipotent3_mul_two]
  ring

theorem outerMinor_upperUnipotent3_mul (x y z : v.adicCompletion ℚ) (g : LocalGL3 v) :
    outerMinor v (upperUnipotent3 x y z * g) = outerMinor v g := by
  simp only [outerMinor, gl3Entry_upperUnipotent3_mul_one, gl3Entry_upperUnipotent3_mul_two]
  ring

theorem gl3Det_upperUnipotent3_mul (x y z : v.adicCompletion ℚ) (g : LocalGL3 v) :
    gl3Det v (upperUnipotent3 x y z * g) = gl3Det v g := by
  have h1 : Matrix.det !![(1 : v.adicCompletion ℚ), x, z; 0, 1, y; 0, 0, 1] = 1 := by
    simp [Matrix.det_fin_three]
  rw [gl3Det, gl3Det, Units.val_mul, Matrix.det_mul, upperUnipotent3_coe, h1, one_mul]

theorem cornerEntry_diagonal3_mul (a : Fin 3 → (v.adicCompletion ℚ)ˣ) (g : LocalGL3 v) :
    cornerEntry v (diagonal3 v a * g) = (a 2 : v.adicCompletion ℚ) * cornerEntry v g :=
  gl3Entry_diagonal3_mul v a g 2 0

theorem lowerMinor_diagonal3_mul (a : Fin 3 → (v.adicCompletion ℚ)ˣ) (g : LocalGL3 v) :
    lowerMinor v (diagonal3 v a * g) = ((a 1 : v.adicCompletion ℚ) * a 2) * lowerMinor v g := by
  simp only [lowerMinor, gl3Entry_diagonal3_mul]
  ring

theorem outerMinor_diagonal3_mul (a : Fin 3 → (v.adicCompletion ℚ)ˣ) (g : LocalGL3 v) :
    outerMinor v (diagonal3 v a * g) = ((a 1 : v.adicCompletion ℚ) * a 2) * outerMinor v g := by
  simp only [outerMinor, gl3Entry_diagonal3_mul]
  ring

theorem gl3Det_diagonal3_mul (a : Fin 3 → (v.adicCompletion ℚ)ˣ) (g : LocalGL3 v) :
    gl3Det v (diagonal3 v a * g) = ((a 0 : v.adicCompletion ℚ) * a 1 * a 2) * gl3Det v g := by
  rw [gl3Det, gl3Det, Units.val_mul, Matrix.det_mul, diagonal3_coe, Matrix.det_diagonal, Fin.prod_univ_three]

def cellRatio (g : LocalGL3 v) : Fin 3 → v.adicCompletion ℚ :=
  ![gl3Entry v g 2 1 / cornerEntry v g, gl3Entry v g 2 2 / cornerEntry v g, outerMinor v g / lowerMinor v g]

theorem cellRatio_upperUnipotent3_mul (x y z : v.adicCompletion ℚ) (g : LocalGL3 v) :
    cellRatio v (upperUnipotent3 x y z * g) = cellRatio v g := by
  simp only [cellRatio, gl3Entry_upperUnipotent3_mul_two, cornerEntry_upperUnipotent3_mul,
    outerMinor_upperUnipotent3_mul, lowerMinor_upperUnipotent3_mul]

theorem cellRatio_diagonal3_mul (a : Fin 3 → (v.adicCompletion ℚ)ˣ) (g : LocalGL3 v) :
    cellRatio v (diagonal3 v a * g) = cellRatio v g := by
  have h2 : (a 2 : v.adicCompletion ℚ) ≠ 0 := (a 2).ne_zero
  have h12 : (a 1 : v.adicCompletion ℚ) * a 2 ≠ 0 := mul_ne_zero (a 1).ne_zero h2
  simp only [cellRatio, gl3Entry_diagonal3_mul, cornerEntry_diagonal3_mul, outerMinor_diagonal3_mul,
    lowerMinor_diagonal3_mul, mul_div_mul_left _ _ h2, mul_div_mul_left _ _ h12]

def cellCutoff : Set (LocalGL3 v) :=
  {g | cornerEntry v g ≠ 0 ∧ lowerMinor v g ≠ 0 ∧ ∀ i, Valued.v (cellRatio v g i) ≤ 1}

theorem upperUnipotent3_mul_mem_cellCutoff_iff (x y z : v.adicCompletion ℚ) (g : LocalGL3 v) :
    upperUnipotent3 x y z * g ∈ cellCutoff v ↔ g ∈ cellCutoff v := by
  simp only [cellCutoff, Set.mem_setOf_eq, cornerEntry_upperUnipotent3_mul, lowerMinor_upperUnipotent3_mul,
    cellRatio_upperUnipotent3_mul]

theorem diagonal3_mul_mem_cellCutoff_iff (a : Fin 3 → (v.adicCompletion ℚ)ˣ) (g : LocalGL3 v) :
    diagonal3 v a * g ∈ cellCutoff v ↔ g ∈ cellCutoff v := by
  simp only [cellCutoff, Set.mem_setOf_eq, cornerEntry_diagonal3_mul, lowerMinor_diagonal3_mul,
    cellRatio_diagonal3_mul, ne_eq, mul_eq_zero, Units.ne_zero, false_or]

def cellValue (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (g : LocalGL3 v) : ℂ :=
  charExt (χ 0) (gl3Det v g / lowerMinor v g) * charExt (χ 1) (lowerMinor v g / cornerEntry v g) *
    charExt (χ 2) (cornerEntry v g) *
    ((‖gl3Det v g / lowerMinor v g‖ / ‖cornerEntry v g‖ : ℝ) : ℂ)

def cellSection (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) : LocalGL3 v → ℂ :=
  (cellCutoff v).indicator (cellValue v χ)

theorem charExt_units_mul (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (u : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ) :
    charExt χ ((u : v.adicCompletion ℚ) * x) = (χ u : ℂ) * charExt χ x := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [charExt_of_ne_zero χ (mul_ne_zero u.ne_zero hx), charExt_of_ne_zero χ hx,
      show Units.mk0 ((u : v.adicCompletion ℚ) * x) (mul_ne_zero u.ne_zero hx) = u * Units.mk0 x hx from
        Units.ext (by simp),
      map_mul, Units.val_mul]

theorem cellValue_upperUnipotent3_mul (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (x y z : v.adicCompletion ℚ)
    (g : LocalGL3 v) : cellValue v χ (upperUnipotent3 x y z * g) = cellValue v χ g := by
  simp only [cellValue, gl3Det_upperUnipotent3_mul, lowerMinor_upperUnipotent3_mul, cornerEntry_upperUnipotent3_mul]

theorem cellValue_diagonal3_mul (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (a : Fin 3 → (v.adicCompletion ℚ)ˣ)
    (g : LocalGL3 v) : cellValue v χ (diagonal3 v a * g) = torusChar3 v χ a * halfModulus3 v a * cellValue v χ g := by
  have h2 : (a 2 : v.adicCompletion ℚ) ≠ 0 := (a 2).ne_zero
  have h12 : (a 1 : v.adicCompletion ℚ) * a 2 ≠ 0 := mul_ne_zero (a 1).ne_zero h2
  have hdet : gl3Det v (diagonal3 v a * g) / lowerMinor v (diagonal3 v a * g)
      = (a 0 : v.adicCompletion ℚ) * (gl3Det v g / lowerMinor v g) := by
    rw [gl3Det_diagonal3_mul, lowerMinor_diagonal3_mul,
      show (a 0 : v.adicCompletion ℚ) * a 1 * a 2 * gl3Det v g
          = ((a 1 : v.adicCompletion ℚ) * a 2) * (a 0 * gl3Det v g) by ring,
      mul_div_mul_left _ _ h12, mul_div_assoc]
  have hlow : lowerMinor v (diagonal3 v a * g) / cornerEntry v (diagonal3 v a * g)
      = (a 1 : v.adicCompletion ℚ) * (lowerMinor v g / cornerEntry v g) := by
    rw [lowerMinor_diagonal3_mul, cornerEntry_diagonal3_mul,
      show (a 1 : v.adicCompletion ℚ) * a 2 * lowerMinor v g
          = (a 2 : v.adicCompletion ℚ) * (a 1 * lowerMinor v g) by ring,
      mul_div_mul_left _ _ h2, mul_div_assoc]
  unfold cellValue
  rw [hdet, hlow, cornerEntry_diagonal3_mul]
  simp only [charExt_units_mul, norm_mul, halfModulus3, torusChar3, Fin.prod_univ_three]
  push_cast
  ring

theorem cellSection_upperUnipotent3_mul (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (x y z : v.adicCompletion ℚ)
    (g : LocalGL3 v) : cellSection v χ (upperUnipotent3 x y z * g) = cellSection v χ g := by
  by_cases hg : g ∈ cellCutoff v
  · rw [cellSection, Set.indicator_of_mem (by rwa [upperUnipotent3_mul_mem_cellCutoff_iff]),
      Set.indicator_of_mem hg, cellValue_upperUnipotent3_mul]
  · rw [cellSection, Set.indicator_of_notMem (by rwa [upperUnipotent3_mul_mem_cellCutoff_iff]),
      Set.indicator_of_notMem hg]

theorem cellSection_diagonal3_mul (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (a : Fin 3 → (v.adicCompletion ℚ)ˣ)
    (g : LocalGL3 v) :
    cellSection v χ (diagonal3 v a * g) = torusChar3 v χ a * halfModulus3 v a * cellSection v χ g := by
  by_cases hg : g ∈ cellCutoff v
  · rw [cellSection, Set.indicator_of_mem (by rwa [diagonal3_mul_mem_cellCutoff_iff]),
      Set.indicator_of_mem hg, cellValue_diagonal3_mul]
  · rw [cellSection, Set.indicator_of_notMem (by rwa [diagonal3_mul_mem_cellCutoff_iff]),
      Set.indicator_of_notMem hg, mul_zero]

def antidiagonal3 : LocalGL3 v :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(0 : v.adicCompletion ℚ), 0, 1; 0, 1, 0; 1, 0, 0] (by
    simp [Matrix.det_fin_three])

theorem antidiagonal3_coe :
    (antidiagonal3 v : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))
      = !![(0 : v.adicCompletion ℚ), 0, 1; 0, 1, 0; 1, 0, 0] :=
  rfl

theorem cornerEntry_antidiagonal3 : cornerEntry v (antidiagonal3 v) = 1 := by
  simp [cornerEntry, gl3Entry, antidiagonal3_coe]

theorem lowerMinor_antidiagonal3 : lowerMinor v (antidiagonal3 v) = -1 := by
  simp [lowerMinor, gl3Entry, antidiagonal3_coe]

theorem outerMinor_antidiagonal3 : outerMinor v (antidiagonal3 v) = 0 := by
  simp [outerMinor, gl3Entry, antidiagonal3_coe]

theorem gl3Det_antidiagonal3 : gl3Det v (antidiagonal3 v) = -1 := by
  simp [gl3Det, antidiagonal3_coe, Matrix.det_fin_three]

theorem antidiagonal3_mem_cellCutoff : antidiagonal3 v ∈ cellCutoff v := by
  refine ⟨?_, ?_, ?_⟩
  · rw [cornerEntry_antidiagonal3]
    exact one_ne_zero
  · rw [lowerMinor_antidiagonal3]
    exact neg_ne_zero.mpr one_ne_zero
  · intro i
    fin_cases i <;> simp [cellRatio, gl3Entry, antidiagonal3_coe, cornerEntry_antidiagonal3, outerMinor_antidiagonal3]

theorem cellValue_antidiagonal3 (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) :
    cellValue v χ (antidiagonal3 v) = (χ 0 1 : ℂ) * (χ 1 (-1) : ℂ) * (χ 2 1 : ℂ) := by
  have h1 : charExt (χ 1) (-1 : v.adicCompletion ℚ) = (χ 1 (-1) : ℂ) := by
    simpa using charExt_coe_units (χ 1) (-1)
  have h0 : charExt (χ 0) (1 : v.adicCompletion ℚ) = (χ 0 1 : ℂ) := by simpa using charExt_coe_units (χ 0) 1
  have h2 : charExt (χ 2) (1 : v.adicCompletion ℚ) = (χ 2 1 : ℂ) := by simpa using charExt_coe_units (χ 2) 1
  simp [cellValue, gl3Det_antidiagonal3, lowerMinor_antidiagonal3, cornerEntry_antidiagonal3, h0, h1, h2]

theorem cellSection_antidiagonal3_ne_zero (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) :
    cellSection v χ (antidiagonal3 v) ≠ 0 := by
  rw [cellSection, Set.indicator_of_mem (antidiagonal3_mem_cellCutoff v), cellValue_antidiagonal3]
  exact mul_ne_zero (mul_ne_zero (Units.ne_zero _) (Units.ne_zero _)) (Units.ne_zero _)

theorem cellSection_ne_zero (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) : cellSection v χ ≠ 0 :=
  fun h => cellSection_antidiagonal3_ne_zero v χ (by rw [h]; rfl)

end Witness

section WitnessTopology

open Filter Topology

variable (v : HeightOneSpectrum (𝓞 ℚ))

theorem isClopen_valued_le_one : IsClopen {y : v.adicCompletion ℚ | Valued.v y ≤ 1} := by
  exact Valued.isClopen_integer (v.adicCompletion ℚ)

theorem eventually_valued_eq {x : v.adicCompletion ℚ} (hx : x ≠ 0) :
    ∀ᶠ y in 𝓝 x, Valued.v y = Valued.v x := by
  have hvx : Valued.v x ≠ (0 : WithZero (Multiplicative ℤ)) := (Valuation.ne_zero_iff _).mpr hx
  exact Valued.locally_const hvx

theorem eventually_valued_lt {c : v.adicCompletion ℚ} (hc : c ≠ 0) :
    ∀ᶠ y in 𝓝 (0 : v.adicCompletion ℚ), Valued.v y < Valued.v c := by
  have hvc : Valued.v c ≠ 0 := (Valuation.ne_zero_iff _).mpr hc
  rw [Filter.Eventually, Valued.mem_nhds_zero]
  refine ⟨Units.mk0 (Valued.v.restrict c) ((Valuation.ne_zero_iff _).mpr hc), fun y hy => ?_⟩
  exact (Valuation.restrict_lt_iff _).mp hy

theorem eventually_norm_eq {x : v.adicCompletion ℚ} (hx : x ≠ 0) : ∀ᶠ y in 𝓝 x, ‖y‖ = ‖x‖ := by
  filter_upwards [eventually_valued_eq v hx] with y hy
  rw [NumberField.FinitePlace.norm_def, NumberField.FinitePlace.norm_def, hy]

theorem eventually_charExt_eq (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ)
    {x : v.adicCompletion ℚ} (hx : x ≠ 0) : ∀ᶠ y in 𝓝 x, charExt χ y = charExt χ x := by
  obtain ⟨U, hU, hUF⟩ := Units.isEmbedding_val₀.toIsInducing.isOpen_iff.mp (hχ.isOpen_fiber (χ (Units.mk0 x hx)))
  have hxU : x ∈ U := by
    have : Units.mk0 x hx ∈ (Units.val ⁻¹' U : Set (v.adicCompletion ℚ)ˣ) := by
      rw [hUF]
      exact rfl
    simpa using this
  filter_upwards [hU.mem_nhds hxU, eventually_ne_nhds hx] with y hyU hy0
  have hyF : Units.mk0 y hy0 ∈ (Units.val ⁻¹' U : Set (v.adicCompletion ℚ)ˣ) := by simpa using hyU
  rw [hUF] at hyF
  rw [charExt_of_ne_zero χ hy0, charExt_of_ne_zero χ hx]
  exact congrArg Units.val hyF

theorem eventually_mem_iff_of_isClopen {s : Set (v.adicCompletion ℚ)} (hs : IsClopen s) (x : v.adicCompletion ℚ) :
    ∀ᶠ y in 𝓝 x, (y ∈ s ↔ x ∈ s) := by
  by_cases hx : x ∈ s
  · filter_upwards [hs.isOpen.mem_nhds hx] with y hy
    exact iff_of_true hy hx
  · filter_upwards [hs.isClosed.isOpen_compl.mem_nhds hx] with y hy
    exact iff_of_false hy hx

theorem continuous_gl3Entry (i j : Fin 3) : Continuous fun g : LocalGL3 v => gl3Entry v g i j :=
  Units.continuous_val.matrix_elem i j

theorem continuous_cornerEntry : Continuous (cornerEntry v) := continuous_gl3Entry v 2 0

theorem continuous_lowerMinor : Continuous (lowerMinor v) :=
  ((continuous_gl3Entry v 1 0).mul (continuous_gl3Entry v 2 1)).sub
    ((continuous_gl3Entry v 1 1).mul (continuous_gl3Entry v 2 0))

theorem continuous_outerMinor : Continuous (outerMinor v) :=
  ((continuous_gl3Entry v 1 0).mul (continuous_gl3Entry v 2 2)).sub
    ((continuous_gl3Entry v 1 2).mul (continuous_gl3Entry v 2 0))

theorem continuous_gl3Det : Continuous (gl3Det v) := Units.continuous_val.matrix_det

theorem gl3Det_eq_bottom_expansion (g : LocalGL3 v) :
    gl3Det v g = gl3Entry v g 2 0 * (gl3Entry v g 0 1 * gl3Entry v g 1 2 - gl3Entry v g 0 2 * gl3Entry v g 1 1)
      - gl3Entry v g 2 1 * (gl3Entry v g 0 0 * gl3Entry v g 1 2 - gl3Entry v g 0 2 * gl3Entry v g 1 0)
      + gl3Entry v g 2 2 * (gl3Entry v g 0 0 * gl3Entry v g 1 1 - gl3Entry v g 0 1 * gl3Entry v g 1 0) := by
  simp only [gl3Det, gl3Entry, Matrix.det_fin_three]
  ring

theorem cornerEntry_mul_gl3Det (g : LocalGL3 v) :
    cornerEntry v g * gl3Det v g
      = (gl3Entry v g 0 0 * gl3Entry v g 2 1 - gl3Entry v g 0 1 * cornerEntry v g) * outerMinor v g
        + (gl3Entry v g 0 2 * cornerEntry v g - gl3Entry v g 0 0 * gl3Entry v g 2 2) * lowerMinor v g := by
  simp only [gl3Det, gl3Entry, cornerEntry, outerMinor, lowerMinor, Matrix.det_fin_three]
  ring

theorem exists_bottom_entry_ne_zero_of_cornerEntry_eq_zero {g : LocalGL3 v} (hc : cornerEntry v g = 0) :
    gl3Entry v g 2 1 ≠ 0 ∨ gl3Entry v g 2 2 ≠ 0 := by
  by_contra h
  push Not at h
  apply gl3Det_ne_zero v g
  rw [gl3Det_eq_bottom_expansion, h.1, h.2]
  have hc' : gl3Entry v g 2 0 = 0 := hc
  rw [hc']
  ring

theorem outerMinor_ne_zero_of_lowerMinor_eq_zero {g : LocalGL3 v} (hc : cornerEntry v g ≠ 0)
    (hl : lowerMinor v g = 0) : outerMinor v g ≠ 0 := by
  intro ho
  apply gl3Det_ne_zero v g
  have h := cornerEntry_mul_gl3Det v g
  rw [ho, hl, mul_zero, mul_zero, add_zero] at h
  exact (mul_eq_zero.mp h).resolve_left hc

theorem eventually_one_lt_valued_div {n d : LocalGL3 v → v.adicCompletion ℚ} {g : LocalGL3 v}
    (hn : Continuous n) (hd : Continuous d) (hng : n g ≠ 0) (hdg : d g = 0) :
    ∀ᶠ h in 𝓝 g, d h ≠ 0 → 1 < Valued.v (n h / d h) := by
  have h1 : ∀ᶠ h in 𝓝 g, Valued.v (n h) = Valued.v (n g) :=
    (hn.tendsto g).eventually (eventually_valued_eq v hng)
  have h2 : ∀ᶠ h in 𝓝 g, Valued.v (d h) < Valued.v (n g) := by
    have ht : Filter.Tendsto d (nhds g) (nhds 0) := by simpa [hdg] using hd.tendsto g
    exact ht.eventually (eventually_valued_lt v hng)
  filter_upwards [h1, h2] with h hn' hd' hd0
  have hvd : Valued.v (d h) ≠ 0 := (Valuation.ne_zero_iff _).mpr hd0
  rw [map_div₀, hn', one_lt_div₀ (lt_of_le_of_ne zero_le' hvd.symm)]
  exact hd'

theorem eventually_cellSection_eq_zero_of_den {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)} {g : LocalGL3 v}
    {n d : LocalGL3 v → v.adicCompletion ℚ} (i : Fin 3) (hn : Continuous n) (hd : Continuous d) (hng : n g ≠ 0)
    (hdg : d g = 0) (hratio : ∀ h, cellRatio v h i = n h / d h) (hden : ∀ h, h ∈ cellCutoff v → d h ≠ 0) :
    ∀ᶠ h in 𝓝 g, cellSection v χ h = cellSection v χ g := by
  have hg : g ∉ cellCutoff v := fun hmem => hden g hmem hdg
  filter_upwards [eventually_one_lt_valued_div v hn hd hng hdg] with h hh
  have hh' : h ∉ cellCutoff v := by
    intro hmem
    have hi := hmem.2.2 i
    rw [hratio] at hi
    exact absurd hi (not_le.mpr (hh (hden h hmem)))
  simp only [cellSection, Set.indicator_of_notMem hh', Set.indicator_of_notMem hg]

theorem isLocallyConstant_cellSection (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (hχ : ∀ i, IsLocallyConstant (χ i)) : IsLocallyConstant (cellSection v χ) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g
  by_cases hc : cornerEntry v g = 0
  · rcases exists_bottom_entry_ne_zero_of_cornerEntry_eq_zero v hc with h21 | h22
    · exact eventually_cellSection_eq_zero_of_den v 0 (continuous_gl3Entry v 2 1) (continuous_cornerEntry v) h21 hc
        (fun h => rfl) (fun h hh => hh.1)
    · exact eventually_cellSection_eq_zero_of_den v 1 (continuous_gl3Entry v 2 2) (continuous_cornerEntry v) h22 hc
        (fun h => rfl) (fun h hh => hh.1)
  by_cases hl : lowerMinor v g = 0
  · exact eventually_cellSection_eq_zero_of_den v 2 (continuous_outerMinor v) (continuous_lowerMinor v)
      (outerMinor_ne_zero_of_lowerMinor_eq_zero v hc hl) hl (fun h => rfl) (fun h hh => hh.2.1)
  have hcA : ContinuousAt (cornerEntry v) g := (continuous_cornerEntry v).continuousAt
  have hlA : ContinuousAt (lowerMinor v) g := (continuous_lowerMinor v).continuousAt
  have hdA : ContinuousAt (gl3Det v) g := (continuous_gl3Det v).continuousAt
  have hr : ∀ i, ContinuousAt (fun h => cellRatio v h i) g := by
    intro i
    fin_cases i
    · exact ((continuous_gl3Entry v 2 1).continuousAt).div hcA hc
    · exact ((continuous_gl3Entry v 2 2).continuousAt).div hcA hc
    · exact ((continuous_outerMinor v).continuousAt).div hlA hl
  have hmem : ∀ᶠ h in 𝓝 g, (h ∈ cellCutoff v ↔ g ∈ cellCutoff v) := by
    have hc' : ∀ᶠ h in 𝓝 g, cornerEntry v h ≠ 0 := hcA.eventually_ne hc
    have hl' : ∀ᶠ h in 𝓝 g, lowerMinor v h ≠ 0 := hlA.eventually_ne hl
    have hr' : ∀ᶠ h in 𝓝 g, ∀ i, (Valued.v (cellRatio v h i) ≤ 1 ↔ Valued.v (cellRatio v g i) ≤ 1) :=
      eventually_all.mpr fun i =>
        (hr i).eventually (eventually_mem_iff_of_isClopen v (isClopen_valued_le_one v) (cellRatio v g i))
    filter_upwards [hc', hl', hr'] with h hch hlh hrh
    simp only [cellCutoff, Set.mem_setOf_eq, hch, hc, hlh, hl, ne_eq, not_false_eq_true, true_and]
    exact forall_congr' hrh
  have hval : ∀ᶠ h in 𝓝 g, cellValue v χ h = cellValue v χ g := by
    have hq0 : gl3Det v g / lowerMinor v g ≠ 0 := div_ne_zero (gl3Det_ne_zero v g) hl
    have hq1 : lowerMinor v g / cornerEntry v g ≠ 0 := div_ne_zero hl hc
    have e0 : ∀ᶠ h in nhds g,
        charExt (χ 0) (gl3Det v h / lowerMinor v h) = charExt (χ 0) (gl3Det v g / lowerMinor v g) :=
      (hdA.div hlA hl).eventually (eventually_charExt_eq v (χ 0) (hχ 0) hq0)
    have e1 : ∀ᶠ h in nhds g,
        charExt (χ 1) (lowerMinor v h / cornerEntry v h) = charExt (χ 1) (lowerMinor v g / cornerEntry v g) :=
      (hlA.div hcA hc).eventually (eventually_charExt_eq v (χ 1) (hχ 1) hq1)
    have e2 : ∀ᶠ h in nhds g, charExt (χ 2) (cornerEntry v h) = charExt (χ 2) (cornerEntry v g) :=
      hcA.eventually (eventually_charExt_eq v (χ 2) (hχ 2) hc)
    have e3 : ∀ᶠ h in nhds g, ‖gl3Det v h / lowerMinor v h‖ = ‖gl3Det v g / lowerMinor v g‖ :=
      (hdA.div hlA hl).eventually (eventually_norm_eq v hq0)
    have e4 : ∀ᶠ h in nhds g, ‖cornerEntry v h‖ = ‖cornerEntry v g‖ := hcA.eventually (eventually_norm_eq v hc)
    filter_upwards [e0, e1, e2, e3, e4] with h h0 h1 h2 h3 h4
    simp only [cellValue, h0, h1, h2, h3, h4]
  filter_upwards [hmem, hval] with h h1 h2
  by_cases hgS : g ∈ cellCutoff v
  · rw [cellSection, Set.indicator_of_mem (h1.mpr hgS), Set.indicator_of_mem hgS, h2]
  · rw [cellSection, Set.indicator_of_notMem (fun hh => hgS (h1.mp hh)), Set.indicator_of_notMem hgS]

theorem cellSection_mem_principalSeries3 (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (hχ : ∀ i, IsLocallyConstant (χ i)) : cellSection v χ ∈ principalSeries3 v χ :=
  ⟨isLocallyConstant_cellSection v χ hχ, cellSection_upperUnipotent3_mul v χ, cellSection_diagonal3_mul v χ⟩

def cellVector (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (hχ : ∀ i, IsLocallyConstant (χ i)) :
    ↥(principalSeries3 v χ) :=
  ⟨cellSection v χ, cellSection_mem_principalSeries3 v χ hχ⟩

def evalAntidiagonal3 (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) : ↥(principalSeries3 v χ) →ₗ[ℂ] ℂ :=
  (LinearMap.proj (antidiagonal3 v) : (LocalGL3 v → ℂ) →ₗ[ℂ] ℂ).comp (principalSeries3 v χ).subtype

theorem coefficientFn_evalAntidiagonal3_cellVector_one (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (hχ : ∀ i, IsLocallyConstant (χ i)) :
    coefficientFn (evalAntidiagonal3 v χ) (cellVector v χ hχ) 1 ≠ 0 := by
  have : coefficientFn (evalAntidiagonal3 v χ) (cellVector v χ hχ) 1 = cellSection v χ (antidiagonal3 v) := by
    simp [coefficientFn, evalAntidiagonal3, cellVector, gl3AmbientRightTranslate]
  rw [this]
  exact cellSection_antidiagonal3_ne_zero v χ

end WitnessTopology

end LanglandsTunnell.CubicInduction

end


