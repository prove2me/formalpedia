-- Prove2me | Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
-- name    : LanglandsTunnell_CubicInduction_PrincipalSeries2
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/bc8301a5-9e79-5045-bd48-bfb221bf20eb
-- title:
--   Local principal series for GL(2) over a completion of Q
-- statement:
--   Fix a finite place $v$ of $\mathbb{Q}$ (a height-one prime of $\mathcal{O}_{\mathbb{Q}}$) and write $F_v$ for the completion $v.\mathrm{adicCompletion}\ \mathbb{Q}$; `LocalGL2 v` is $\mathrm{GL}_2(F_v)$. The module introduces the standard Borel data: `diagonal2 v a` is the diagonal matrix with unit entries $a_0,a_1$ (multiplicative in $a$), `upperUnipotent2 v x` is $\begin{pmatrix}1&x\\0&1\end{pmatrix}$, `torusChar2 v χ a` $= \prod_{i} χ_i(a_i)$ for a pair $χ$ of homomorphisms $F_v^{\times}\to\mathbb{C}^{\times}$, and `halfModulus2 v a` is the real positive square root of $\lVert a_0\rVert/\lVert a_1\rVert$, viewed in $\mathbb{C}$; it is multiplicative, never zero, always a positive real, and its square at $(\varpi_v,1)$ is the inverse of the absolute norm of $v$. `rightTranslate2 v g` is the $\mathbb{C}$-linear endomorphism $f\mapsto(h\mapsto f(hg))$ of functions on $\mathrm{GL}_2(F_v)$, multiplicative in $g$. The carrier `principalSeries2 v χ` is the $\mathbb{C}$-subspace of functions $f:\mathrm{GL}_2(F_v)\to\mathbb{C}$ that are locally constant, satisfy $f(u(x)g)=f(g)$ for all $x$, and $f(\mathrm{diag}(a)g)=\mathrm{torusChar2}(a)\,\mathrm{halfModulus2}(a)\,f(g)$; right translation preserves it and `principalSeries2Rep` is the resulting monoid homomorphism $\mathrm{GL}_2(F_v)\to\mathrm{End}_{\mathbb{C}}$ of that subspace.
--
--   A non-vanishing witness is constructed explicitly. With `gl2Entry`, `gl2Det` the matrix entries and determinant (continuous, determinant non-zero), `cornerEntry2 g` the $(1,0)$ entry, the big-cell region `cellCutoff2 v` consists of the $g$ with $\mathrm{cornerEntry2}(g)\neq0$ and $v(g_{11}/\mathrm{cornerEntry2}(g))\le 1$; it is stable under left multiplication by unipotents and diagonals. On it, `cellValue2 v χ g` is $\mathrm{charExt}(χ_0)(\det g/c(g))\cdot\mathrm{charExt}(χ_1)(c(g))\cdot\sqrt{\lVert\det g/c(g)\rVert/\lVert c(g)\rVert}$, where `charExt` extends a character of $F_v^{\times}$ to $F_v$, and `cellSection2` is the indicator extension of this by zero. It satisfies the two transformation laws, is locally constant when each $χ_i$ is, hence lies in `principalSeries2 v χ`; its value at the antidiagonal matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ is non-zero, so the principal series is not the zero subspace. Finally `unipotentHom2 v` is the homomorphism from the multiplicative copy of $(F_v,+)$ sending $x$ to $u(x)$, and `unipotentRep2 v χ` is the induced representation of that group on the principal series, acting by $f\mapsto f(\cdot\,u(x))$. Auxiliary lemmas record continuity of entries and determinant, the finite-place norm of a uniformiser, and the fact that near a point where a continuous numerator is non-zero and a continuous denominator vanishes the quotient has valuation $>1$ wherever defined.
--
--   **Relation to Mathlib.** Mathlib supplies the general linear group, adic completions and the finite-place norm, local constancy and `Representation`; the principal series subspace, the big-cell section and the accompanying torus and modulus functions are the project's own constructions.
--
--   **Where it is used.** These local principal series for $\mathrm{GL}_2$ accompany the $\mathrm{GL}_3$ constructions of the cubic-induction package, which supplies the automorphic input for the Langlands–Tunnell step establishing modularity of the mod $3$ representation used in the Fermat argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LanglandsTunnell_CubicInduction_PrincipalSeries2.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField NumberField.AdelicLevel LanglandsTunnell.TateLocal

noncomputable section

namespace LanglandsTunnell.CubicInduction

section PrincipalSeries2

variable (v : HeightOneSpectrum (𝓞 ℚ))

abbrev LocalGL2 : Type := GL (Fin 2) (v.adicCompletion ℚ)

def rightTranslate2 (g : LocalGL2 v) : Module.End ℂ (LocalGL2 v → ℂ) where
  toFun f := fun h => f (h * g)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem rightTranslate2_apply (g : LocalGL2 v) (f : LocalGL2 v → ℂ) (h : LocalGL2 v) :
    rightTranslate2 v g f h = f (h * g) :=
  rfl

theorem rightTranslate2_mul (g g' : LocalGL2 v) :
    rightTranslate2 v (g * g') = rightTranslate2 v g * rightTranslate2 v g' := by
  ext f h
  simp [rightTranslate2_apply, mul_assoc]

def diagonal2 (a : Fin 2 → (v.adicCompletion ℚ)ˣ) : LocalGL2 v where
  val := diagonal fun i => (a i : v.adicCompletion ℚ)
  inv := diagonal fun i => ((a i)⁻¹ : (v.adicCompletion ℚ)ˣ)
  val_inv := by
    rw [diagonal_mul_diagonal]
    simp only [Units.mul_inv, diagonal_one]
  inv_val := by
    rw [diagonal_mul_diagonal]
    simp only [Units.inv_mul, diagonal_one]

@[simp] theorem diagonal2_coe (a : Fin 2 → (v.adicCompletion ℚ)ˣ) :
    (diagonal2 v a : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) = diagonal fun i => (a i : v.adicCompletion ℚ) :=
  rfl

theorem diagonal2_mul (a b : Fin 2 → (v.adicCompletion ℚ)ˣ) :
    diagonal2 v (a * b) = diagonal2 v a * diagonal2 v b := by
  ext i j
  rcases eq_or_ne i j with rfl | hij
  · simp [diagonal2]
  · simp [diagonal2, Matrix.diagonal_apply_ne _ hij]

def upperUnipotent2 (x : v.adicCompletion ℚ) : LocalGL2 v where
  val := !![1, x; 0, 1]
  inv := !![1, -x; 0, 1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem upperUnipotent2_coe (x : v.adicCompletion ℚ) :
    (upperUnipotent2 v x : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) = !![1, x; 0, 1] :=
  rfl

def halfModulus2 (a : Fin 2 → (v.adicCompletion ℚ)ˣ) : ℂ :=
  ((Real.sqrt (‖(a 0 : v.adicCompletion ℚ)‖ / ‖(a 1 : v.adicCompletion ℚ)‖) : ℝ) : ℂ)

theorem halfModulus2_mul (a b : Fin 2 → (v.adicCompletion ℚ)ˣ) :
    halfModulus2 v (a * b) = halfModulus2 v a * halfModulus2 v b := by
  simp only [halfModulus2, Pi.mul_apply, Units.val_mul, norm_mul]
  rw [show ‖(a 0 : v.adicCompletion ℚ)‖ * ‖(b 0 : v.adicCompletion ℚ)‖ /
        (‖(a 1 : v.adicCompletion ℚ)‖ * ‖(b 1 : v.adicCompletion ℚ)‖)
      = ‖(a 0 : v.adicCompletion ℚ)‖ / ‖(a 1 : v.adicCompletion ℚ)‖ *
        (‖(b 0 : v.adicCompletion ℚ)‖ / ‖(b 1 : v.adicCompletion ℚ)‖) by ring,
    Real.sqrt_mul (by positivity)]
  push_cast
  ring

@[simp] theorem halfModulus2_one : halfModulus2 v 1 = 1 := by
  simp [halfModulus2]

theorem halfModulus2_ne_zero (a : Fin 2 → (v.adicCompletion ℚ)ˣ) : halfModulus2 v a ≠ 0 := by
  unfold halfModulus2
  exact_mod_cast (Real.sqrt_pos.mpr (div_pos (norm_pos_iff.mpr (a 0).ne_zero)
    (norm_pos_iff.mpr (a 1).ne_zero))).ne'

theorem halfModulus2_eq_pos_real (a : Fin 2 → (v.adicCompletion ℚ)ˣ) :
    ∃ r : ℝ, 0 < r ∧ halfModulus2 v a = (r : ℂ) :=
  ⟨_, Real.sqrt_pos.mpr (div_pos (norm_pos_iff.mpr (a 0).ne_zero) (norm_pos_iff.mpr (a 1).ne_zero)), rfl⟩

private theorem toAdd_unzero_exp (n : ℤ) (h : (WithZero.exp n : WithZero (Multiplicative ℤ)) ≠ 0) :
    Multiplicative.toAdd (WithZero.unzero h) = n :=
  rfl

private theorem norm_uniformizerUnit :
    ‖(uniformizerUnit ℚ v : v.adicCompletion ℚ)‖ = (((Ideal.absNorm v.asIdeal : ℕ) : ℝ))⁻¹ := by
  rw [NumberField.FinitePlace.norm_def, valued_uniformizerUnit,
    WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero, toAdd_unzero_exp]
  simp

theorem halfModulus2_sq_uniformizerUnit :
    halfModulus2 v ![uniformizerUnit ℚ v, 1] ^ 2 = ((((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) := by
  have h : halfModulus2 v ![uniformizerUnit ℚ v, 1]
      = ((Real.sqrt ‖(uniformizerUnit ℚ v : v.adicCompletion ℚ)‖ : ℝ) : ℂ) := by
    simp [halfModulus2]
  rw [h, ← Complex.ofReal_pow, Real.sq_sqrt (norm_nonneg _), norm_uniformizerUnit]

def torusChar2 (χ : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (a : Fin 2 → (v.adicCompletion ℚ)ˣ) : ℂ :=
  ∏ i : Fin 2, ((χ i (a i) : ℂˣ) : ℂ)

theorem torusChar2_mul (χ : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (a b : Fin 2 → (v.adicCompletion ℚ)ˣ) :
    torusChar2 v χ (a * b) = torusChar2 v χ a * torusChar2 v χ b := by
  simp only [torusChar2, Pi.mul_apply, map_mul, Units.val_mul, Finset.prod_mul_distrib]

@[simp] theorem torusChar2_one (χ : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) : torusChar2 v χ 1 = 1 := by
  simp [torusChar2]

def principalSeries2 (χ : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) : Submodule ℂ (LocalGL2 v → ℂ) where
  carrier := {f | IsLocallyConstant f ∧
    (∀ (x : v.adicCompletion ℚ) (g : LocalGL2 v), f (upperUnipotent2 v x * g) = f g) ∧
    ∀ (a : Fin 2 → (v.adicCompletion ℚ)ˣ) (g : LocalGL2 v),
      f (diagonal2 v a * g) = torusChar2 v χ a * halfModulus2 v a * f g}
  zero_mem' := ⟨IsLocallyConstant.const 0, fun _ _ => rfl, fun _ _ => by simp⟩
  add_mem' := by
    intro f₁ f₂ h₁ h₂
    obtain ⟨h₁lc, h₁n, h₁t⟩ := h₁
    obtain ⟨h₂lc, h₂n, h₂t⟩ := h₂
    refine ⟨h₁lc.comp₂ h₂lc (· + ·), fun x g => ?_, fun a g => ?_⟩
    · show f₁ _ + f₂ _ = f₁ g + f₂ g
      rw [h₁n, h₂n]
    · show f₁ _ + f₂ _ = _ * (f₁ g + f₂ g)
      rw [h₁t, h₂t]
      ring
  smul_mem' := by
    intro c f hf
    obtain ⟨hlc, hn, ht⟩ := hf
    refine ⟨hlc.comp (c * ·), fun x g => ?_, fun a g => ?_⟩
    · show c * f _ = c * f g
      rw [hn]
    · show c * f _ = _ * (c * f g)
      rw [ht]
      ring

variable {v}

theorem mem_principalSeries2_iff {χ : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)} {f : LocalGL2 v → ℂ} :
    f ∈ principalSeries2 v χ ↔
      IsLocallyConstant f ∧
        (∀ (x : v.adicCompletion ℚ) (g : LocalGL2 v), f (upperUnipotent2 v x * g) = f g) ∧
        ∀ (a : Fin 2 → (v.adicCompletion ℚ)ˣ) (g : LocalGL2 v),
          f (diagonal2 v a * g) = torusChar2 v χ a * halfModulus2 v a * f g :=
  Iff.rfl

theorem rightTranslate2_mem_principalSeries2 {χ : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)}
    {f : LocalGL2 v → ℂ} (hf : f ∈ principalSeries2 v χ) (g : LocalGL2 v) :
    rightTranslate2 v g f ∈ principalSeries2 v χ := by
  obtain ⟨hlc, hn, ht⟩ := mem_principalSeries2_iff.mp hf
  refine mem_principalSeries2_iff.mpr
    ⟨hlc.comp_continuous (continuous_id.mul continuous_const), fun x h => ?_, fun a h => ?_⟩
  · show f (upperUnipotent2 v x * h * g) = f (h * g)
    rw [mul_assoc, hn]
  · show f (diagonal2 v a * h * g) = _ * f (h * g)
    rw [mul_assoc, ht]

def principalSeries2Rep (χ : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) :
    LocalGL2 v →* Module.End ℂ ↥(principalSeries2 v χ) where
  toFun g := (rightTranslate2 v g).restrict fun f hf => rightTranslate2_mem_principalSeries2 hf g
  map_one' := by
    ext f h
    simp [rightTranslate2_apply]
  map_mul' g g' := by
    ext f h
    simp [rightTranslate2_apply, mul_assoc]

section Witness2

variable (v)

def gl2Entry (g : LocalGL2 v) (i j : Fin 2) : v.adicCompletion ℚ :=
  (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j

def gl2Det (g : LocalGL2 v) : v.adicCompletion ℚ := (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det

theorem gl2Det_ne_zero (g : LocalGL2 v) : gl2Det v g ≠ 0 := by
  have h := (Matrix.GeneralLinearGroup.det g).ne_zero
  rwa [Matrix.GeneralLinearGroup.val_det_apply] at h

theorem gl2Det_eq (g : LocalGL2 v) :
    gl2Det v g = gl2Entry v g 0 0 * gl2Entry v g 1 1 - gl2Entry v g 0 1 * gl2Entry v g 1 0 := by
  simp only [gl2Det, gl2Entry, Matrix.det_fin_two]

theorem continuous_gl2Entry (i j : Fin 2) : Continuous fun g : LocalGL2 v => gl2Entry v g i j :=
  Units.continuous_val.matrix_elem i j

theorem continuous_gl2Det : Continuous (gl2Det v) := Units.continuous_val.matrix_det

theorem gl2Entry_upperUnipotent2_mul_one (x : v.adicCompletion ℚ) (g : LocalGL2 v) (j : Fin 2) :
    gl2Entry v (upperUnipotent2 v x * g) 1 j = gl2Entry v g 1 j := by
  simp [gl2Entry, Matrix.mul_apply, Fin.sum_univ_two]

theorem gl2Det_upperUnipotent2_mul (x : v.adicCompletion ℚ) (g : LocalGL2 v) :
    gl2Det v (upperUnipotent2 v x * g) = gl2Det v g := by
  simp only [gl2Det, Units.val_mul, Matrix.det_mul, upperUnipotent2_coe, Matrix.det_fin_two_of]
  simp

theorem gl2Entry_diagonal2_mul (a : Fin 2 → (v.adicCompletion ℚ)ˣ) (g : LocalGL2 v) (i j : Fin 2) :
    gl2Entry v (diagonal2 v a * g) i j = (a i : v.adicCompletion ℚ) * gl2Entry v g i j := by
  simp [gl2Entry, diagonal2_coe, Matrix.diagonal_mul]

theorem gl2Det_diagonal2_mul (a : Fin 2 → (v.adicCompletion ℚ)ˣ) (g : LocalGL2 v) :
    gl2Det v (diagonal2 v a * g) = (a 0 : v.adicCompletion ℚ) * a 1 * gl2Det v g := by
  simp only [gl2Det, Units.val_mul, Matrix.det_mul, diagonal2_coe, Matrix.det_diagonal, Fin.prod_univ_two]

def cornerEntry2 (g : LocalGL2 v) : v.adicCompletion ℚ := gl2Entry v g 1 0

theorem continuous_cornerEntry2 : Continuous (cornerEntry2 v) := continuous_gl2Entry v 1 0

theorem cornerEntry2_upperUnipotent2_mul (x : v.adicCompletion ℚ) (g : LocalGL2 v) :
    cornerEntry2 v (upperUnipotent2 v x * g) = cornerEntry2 v g :=
  gl2Entry_upperUnipotent2_mul_one v x g 0

theorem cornerEntry2_diagonal2_mul (a : Fin 2 → (v.adicCompletion ℚ)ˣ) (g : LocalGL2 v) :
    cornerEntry2 v (diagonal2 v a * g) = (a 1 : v.adicCompletion ℚ) * cornerEntry2 v g :=
  gl2Entry_diagonal2_mul v a g 1 0

theorem gl2Entry_one_one_ne_zero_of_cornerEntry2_eq_zero {g : LocalGL2 v} (hc : cornerEntry2 v g = 0) :
    gl2Entry v g 1 1 ≠ 0 := by
  intro h
  apply gl2Det_ne_zero v g
  have hc' : gl2Entry v g 1 0 = 0 := hc
  rw [gl2Det_eq, h, hc']
  ring

def cellCutoff2 : Set (LocalGL2 v) :=
  {g | cornerEntry2 v g ≠ 0 ∧ Valued.v (gl2Entry v g 1 1 / cornerEntry2 v g) ≤ 1}

theorem upperUnipotent2_mul_mem_cellCutoff2_iff (x : v.adicCompletion ℚ) (g : LocalGL2 v) :
    upperUnipotent2 v x * g ∈ cellCutoff2 v ↔ g ∈ cellCutoff2 v := by
  simp only [cellCutoff2, Set.mem_setOf_eq, cornerEntry2_upperUnipotent2_mul, gl2Entry_upperUnipotent2_mul_one]

theorem diagonal2_mul_mem_cellCutoff2_iff (a : Fin 2 → (v.adicCompletion ℚ)ˣ) (g : LocalGL2 v) :
    diagonal2 v a * g ∈ cellCutoff2 v ↔ g ∈ cellCutoff2 v := by
  simp only [cellCutoff2, Set.mem_setOf_eq, cornerEntry2_diagonal2_mul, gl2Entry_diagonal2_mul,
    mul_div_mul_left _ _ (a 1).ne_zero, mul_ne_zero_iff, ne_eq, (a 1).ne_zero, not_false_eq_true, true_and]

def cellValue2 (χ : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (g : LocalGL2 v) : ℂ :=
  charExt (χ 0) (gl2Det v g / cornerEntry2 v g) * charExt (χ 1) (cornerEntry2 v g) *
    ((Real.sqrt (‖gl2Det v g / cornerEntry2 v g‖ / ‖cornerEntry2 v g‖) : ℝ) : ℂ)

def cellSection2 (χ : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) : LocalGL2 v → ℂ :=
  (cellCutoff2 v).indicator (cellValue2 v χ)

theorem cellValue2_upperUnipotent2_mul (χ : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (x : v.adicCompletion ℚ)
    (g : LocalGL2 v) : cellValue2 v χ (upperUnipotent2 v x * g) = cellValue2 v χ g := by
  simp only [cellValue2, cornerEntry2_upperUnipotent2_mul, gl2Det_upperUnipotent2_mul]

theorem cellSection2_upperUnipotent2_mul (χ : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (x : v.adicCompletion ℚ)
    (g : LocalGL2 v) : cellSection2 v χ (upperUnipotent2 v x * g) = cellSection2 v χ g := by
  by_cases hg : g ∈ cellCutoff2 v
  · rw [cellSection2, Set.indicator_of_mem (by rwa [upperUnipotent2_mul_mem_cellCutoff2_iff]),
      Set.indicator_of_mem hg, cellValue2_upperUnipotent2_mul]
  · rw [cellSection2, Set.indicator_of_notMem (by rwa [upperUnipotent2_mul_mem_cellCutoff2_iff]),
      Set.indicator_of_notMem hg]

theorem cellValue2_diagonal2_mul (χ : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (a : Fin 2 → (v.adicCompletion ℚ)ˣ)
    (g : LocalGL2 v) :
    cellValue2 v χ (diagonal2 v a * g) = torusChar2 v χ a * halfModulus2 v a * cellValue2 v χ g := by
  have h1 : (a 1 : v.adicCompletion ℚ) ≠ 0 := (a 1).ne_zero
  have hdet : gl2Det v (diagonal2 v a * g) / cornerEntry2 v (diagonal2 v a * g)
      = (a 0 : v.adicCompletion ℚ) * (gl2Det v g / cornerEntry2 v g) := by
    rw [gl2Det_diagonal2_mul, cornerEntry2_diagonal2_mul,
      show (a 0 : v.adicCompletion ℚ) * a 1 * gl2Det v g = (a 1 : v.adicCompletion ℚ) * (a 0 * gl2Det v g) by ring,
      mul_div_mul_left _ _ h1, mul_div_assoc]
  have hmod : ‖(a 0 : v.adicCompletion ℚ) * (gl2Det v g / cornerEntry2 v g)‖ /
        ‖(a 1 : v.adicCompletion ℚ) * cornerEntry2 v g‖
      = ‖(a 0 : v.adicCompletion ℚ)‖ / ‖(a 1 : v.adicCompletion ℚ)‖ *
        (‖gl2Det v g / cornerEntry2 v g‖ / ‖cornerEntry2 v g‖) := by
    rw [norm_mul, norm_mul]
    ring
  rw [cellValue2, cellValue2, hdet, cornerEntry2_diagonal2_mul, hmod, charExt_units_mul, charExt_units_mul,
    Real.sqrt_mul (div_nonneg (norm_nonneg _) (norm_nonneg _))]
  simp only [torusChar2, halfModulus2, Fin.prod_univ_two]
  push_cast
  ring

theorem cellSection2_diagonal2_mul (χ : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (a : Fin 2 → (v.adicCompletion ℚ)ˣ)
    (g : LocalGL2 v) :
    cellSection2 v χ (diagonal2 v a * g) = torusChar2 v χ a * halfModulus2 v a * cellSection2 v χ g := by
  by_cases hg : g ∈ cellCutoff2 v
  · rw [cellSection2, Set.indicator_of_mem (by rwa [diagonal2_mul_mem_cellCutoff2_iff]),
      Set.indicator_of_mem hg, cellValue2_diagonal2_mul]
  · rw [cellSection2, Set.indicator_of_notMem (by rwa [diagonal2_mul_mem_cellCutoff2_iff]),
      Set.indicator_of_notMem hg, mul_zero]

theorem eventually_one_lt_valued_div2 {n d : LocalGL2 v → v.adicCompletion ℚ} {g : LocalGL2 v}
    (hn : Continuous n) (hd : Continuous d) (hng : n g ≠ 0) (hdg : d g = 0) :
    ∀ᶠ h in nhds g, d h ≠ 0 → 1 < Valued.v (n h / d h) := by
  have h1 : ∀ᶠ h in nhds g, Valued.v (n h) = Valued.v (n g) :=
    (hn.tendsto g).eventually (eventually_valued_eq v hng)
  have h2 : ∀ᶠ h in nhds g, Valued.v (d h) < Valued.v (n g) := by
    have ht : Filter.Tendsto d (nhds g) (nhds 0) := by simpa [hdg] using hd.tendsto g
    exact ht.eventually (eventually_valued_lt v hng)
  filter_upwards [h1, h2] with h hn' hd' hd0
  have hvd : Valued.v (d h) ≠ 0 := (Valuation.ne_zero_iff _).mpr hd0
  rw [map_div₀, hn', one_lt_div₀ (lt_of_le_of_ne zero_le' hvd.symm)]
  exact hd'

theorem isLocallyConstant_cellSection2 (χ : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (hχ : ∀ i, IsLocallyConstant (χ i)) : IsLocallyConstant (cellSection2 v χ) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g
  by_cases hc : cornerEntry2 v g = 0
  · have hg : g ∉ cellCutoff2 v := fun hg => hg.1 hc
    have hev := eventually_one_lt_valued_div2 v (continuous_gl2Entry v 1 1) (continuous_cornerEntry2 v)
      (gl2Entry_one_one_ne_zero_of_cornerEntry2_eq_zero v hc) hc
    filter_upwards [hev] with h hh
    have hh' : h ∉ cellCutoff2 v := fun hmem => (not_le.mpr (hh hmem.1)) hmem.2
    rw [cellSection2, Set.indicator_of_notMem hh', Set.indicator_of_notMem hg]
  have hcA : ContinuousAt (cornerEntry2 v) g := (continuous_cornerEntry2 v).continuousAt
  have hc' : ∀ᶠ h in nhds g, cornerEntry2 v h ≠ 0 := hcA.eventually_ne hc
  have hr : ∀ᶠ h in nhds g,
      (Valued.v (gl2Entry v h 1 1 / cornerEntry2 v h) ≤ 1 ↔ Valued.v (gl2Entry v g 1 1 / cornerEntry2 v g) ≤ 1) :=
    (((continuous_gl2Entry v 1 1).continuousAt).div hcA hc).eventually
      (eventually_mem_iff_of_isClopen v (isClopen_valued_le_one v) (gl2Entry v g 1 1 / cornerEntry2 v g))
  have hmem : ∀ᶠ h in nhds g, (h ∈ cellCutoff2 v ↔ g ∈ cellCutoff2 v) := by
    filter_upwards [hc', hr] with h hh hrh
    simp only [cellCutoff2, Set.mem_setOf_eq, hh, hc, ne_eq, not_false_eq_true, true_and]
    exact hrh
  have hval : ∀ᶠ h in nhds g, cellValue2 v χ h = cellValue2 v χ g := by
    have hdA : ContinuousAt (fun h => gl2Det v h / cornerEntry2 v h) g :=
      ((continuous_gl2Det v).continuousAt).div hcA hc
    have hd0 : gl2Det v g / cornerEntry2 v g ≠ 0 := div_ne_zero (gl2Det_ne_zero v g) hc
    filter_upwards [hdA.eventually (eventually_charExt_eq v (χ 0) (hχ 0) hd0),
      hcA.eventually (eventually_charExt_eq v (χ 1) (hχ 1) hc), hdA.eventually (eventually_norm_eq v hd0),
      hcA.eventually (eventually_norm_eq v hc)] with h e0 e1 n0 n1
    simp only [cellValue2, e0, e1, n0, n1]
  filter_upwards [hmem, hval] with h hm hv
  by_cases hg : g ∈ cellCutoff2 v
  · rw [cellSection2, Set.indicator_of_mem (hm.mpr hg), Set.indicator_of_mem hg, hv]
  · rw [cellSection2, Set.indicator_of_notMem (fun hh => hg (hm.mp hh)), Set.indicator_of_notMem hg]

theorem cellSection2_mem_principalSeries2 (χ : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (hχ : ∀ i, IsLocallyConstant (χ i)) : cellSection2 v χ ∈ principalSeries2 v χ :=
  ⟨isLocallyConstant_cellSection2 v χ hχ, cellSection2_upperUnipotent2_mul v χ, cellSection2_diagonal2_mul v χ⟩

def antidiagonal2 : LocalGL2 v :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(0 : v.adicCompletion ℚ), 1; 1, 0] (by simp [Matrix.det_fin_two_of])

theorem antidiagonal2_coe :
    (antidiagonal2 v : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) = !![(0 : v.adicCompletion ℚ), 1; 1, 0] :=
  rfl

theorem cornerEntry2_antidiagonal2 : cornerEntry2 v (antidiagonal2 v) = 1 := by
  simp [cornerEntry2, gl2Entry, antidiagonal2_coe]

theorem gl2Entry_antidiagonal2_one_one : gl2Entry v (antidiagonal2 v) 1 1 = 0 := by
  simp [gl2Entry, antidiagonal2_coe]

theorem gl2Det_antidiagonal2 : gl2Det v (antidiagonal2 v) = -1 := by
  simp [gl2Det, antidiagonal2_coe, Matrix.det_fin_two_of]

theorem antidiagonal2_mem_cellCutoff2 : antidiagonal2 v ∈ cellCutoff2 v := by
  refine ⟨?_, ?_⟩
  · rw [cornerEntry2_antidiagonal2]
    exact one_ne_zero
  · simp [gl2Entry_antidiagonal2_one_one]

theorem cellSection2_antidiagonal2_ne_zero (χ : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) :
    cellSection2 v χ (antidiagonal2 v) ≠ 0 := by
  have h0 : charExt (χ 0) (-1 : v.adicCompletion ℚ) = (χ 0 (-1) : ℂ) := by simpa using charExt_coe_units (χ 0) (-1)
  have h1 : charExt (χ 1) (1 : v.adicCompletion ℚ) = (χ 1 1 : ℂ) := by simpa using charExt_coe_units (χ 1) 1
  rw [cellSection2, Set.indicator_of_mem (antidiagonal2_mem_cellCutoff2 v)]
  simp only [cellValue2, gl2Det_antidiagonal2, cornerEntry2_antidiagonal2, div_one, h0, h1, norm_neg, norm_one,
    Real.sqrt_one, Complex.ofReal_one, mul_one]
  exact mul_ne_zero (Units.ne_zero _) (Units.ne_zero _)

theorem principalSeries2_ne_bot (χ : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (hχ : ∀ i, IsLocallyConstant (χ i)) :
    principalSeries2 v χ ≠ ⊥ := by
  intro hbot
  have hmem := cellSection2_mem_principalSeries2 v χ hχ
  rw [hbot, Submodule.mem_bot] at hmem
  exact cellSection2_antidiagonal2_ne_zero v χ (by simp [hmem])

end Witness2

section UnipotentLine

variable (v)

theorem upperUnipotent2_mul (x y : v.adicCompletion ℚ) :
    upperUnipotent2 v x * upperUnipotent2 v y = upperUnipotent2 v (x + y) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem upperUnipotent2_zero : upperUnipotent2 v 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

def unipotentHom2 : Multiplicative (v.adicCompletion ℚ) →* LocalGL2 v where
  toFun x := upperUnipotent2 v (Multiplicative.toAdd x)
  map_one' := upperUnipotent2_zero v
  map_mul' x y := (upperUnipotent2_mul v (Multiplicative.toAdd x) (Multiplicative.toAdd y)).symm

@[simp] theorem unipotentHom2_ofAdd (x : v.adicCompletion ℚ) :
    unipotentHom2 v (Multiplicative.ofAdd x) = upperUnipotent2 v x :=
  rfl

def unipotentRep2 (χ : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) :
    Representation ℂ (Multiplicative (v.adicCompletion ℚ)) ↥(principalSeries2 v χ) :=
  (principalSeries2Rep (v := v) χ).comp (unipotentHom2 v)

theorem unipotentRep2_ofAdd_apply_coe (χ : Fin 2 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (x : v.adicCompletion ℚ)
    (f : ↥(principalSeries2 v χ)) (g : LocalGL2 v) :
    (unipotentRep2 v χ (Multiplicative.ofAdd x) f : LocalGL2 v → ℂ) g
      = (f : LocalGL2 v → ℂ) (g * upperUnipotent2 v x) :=
  rfl

end UnipotentLine

end PrincipalSeries2

end LanglandsTunnell.CubicInduction

end


