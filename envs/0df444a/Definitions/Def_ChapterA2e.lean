-- Prove2me | Definitions.Def_ChapterA2e
-- name    : ChapterA2e
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-20T16:33:54.569049+00:00
-- url     : https://prove2.me/theorems/5340876b-03cb-4c39-9e21-bb1879daf980
-- title:
--   The Lean 4 theorem `theta_inner_self_zero` in the `?` chapter of the timepiece formalization
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterA2e.lean`): generated def bundle for ChapterA2e. See BookProof/ChapterA2e.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterA2e.lean

import Theorems.Thm_BookProof_ChapterA_AntiUnitary_inner_map_map
import Theorems.Thm_BookProof_ChapterA_cembed_apply

import Definitions.Def_ChapterA
import Definitions.Def_ChapterA1
import Definitions.Def_ChapterA1c
import Definitions.Def_ChapterA2
import Definitions.Def_ChapterA2b
import Definitions.Def_ChapterA2c
import Mathlib
import Theorems.Thm_BookProof_ChapterA_Rcomplex_realCommutant_eq_complex
import Theorems.Thm_BookProof_ChapterA_Rpseudoreal_realCommutant_eq_quaternion


/-!
# Chapter A, §A.2 — realification isomorphism criterion (Prop 16), N2 leftover

This file discharges the **Prop 16** leftover of work-package **N2** of
`FORMALIZATION_ROADMAP.md` (§A.2, the commutant classification): the criterion
that identifies C-complex / C-pseudoreal Schur systems by their *realifications*.

## The framework

For a complex system `(M, V)` its **realification** `(M, V^r)` is `V` viewed as a
real inner-product space (`Module ℝ V` / `V →L[ℝ] V`) with the operators of `M`
restricted to `ℝ`-scalars (`ContinuousLinearMap.restrictScalars ℝ`).  A
**realification isometry** between `(M, V)` and `(N, W)` is an `ℝ`-linear
isometric equivalence `β : V ≃ₗᵢ[ℝ] W` carrying the realified `M` onto the
realified `N` by conjugation (`IsRealSystemIso`).

In this language a *complex system isometry* is a realification isometry that is
additionally **`ℂ`-linear** (`∀ x, β (i • x) = i • β x`), and a *complex system
antiisometry* is one that is **`ℂ`-antilinear** (`∀ x, β (i • x) = -(i • β x)`).
Thus **Prop 16** ("two C-complex / C-pseudoreal Schur systems are isometric *or*
antiisometric iff their realifications are isometric") becomes:

> a realification isometry that is `ℂ`-linear or `ℂ`-antilinear exists **iff** a
> realification isometry exists.

The backward direction is trivial.  The forward (content) direction is proved via
the **real commutant classification** already established in `ChapterA2c.lean`
(Props 18–19): the operator `K := β ∘ (i·) ∘ β⁻¹` is an `ℝ`-linear operator of
the realified target commuting with `N` and squaring to `-1`, i.e. an element of
the real commutant.

* **C-complex case.**  By Prop 18 (`Rcomplex_realCommutant_eq_complex`) the real
  commutant is `ℂ`, so `K = c·1` with `c² = -1`, i.e. `c = ±i`; since
  `K (β x) = β (i • x)` this says `β (i • x) = ±(i • β x)`, i.e. `β` is *itself*
  `ℂ`-linear or `ℂ`-antilinear.  (`Ccomplex_realification_dichotomy`,
  `Ccomplex_iso_or_antiiso_iff_realification_iso`.)

Everything here is `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`).
-/

open scoped ComplexConjugate InnerProductSpace

namespace BookProof.ChapterA

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

/-! ## Realification isometries -/

/-- The underlying `ℝ`-linear continuous map of an `ℝ`-linear isometric
equivalence. -/
noncomputable def betaR (β : V ≃ₗᵢ[ℝ] W) : V →L[ℝ] W :=
  β.toContinuousLinearEquiv.toContinuousLinearMap

omit [CompleteSpace V] [CompleteSpace W] in
@[simp] lemma betaR_apply (β : V ≃ₗᵢ[ℝ] W) (x : V) : betaR β x = β x := rfl

/-- Conjugation of an `ℝ`-linear operator `m : V →L[ℝ] V` by an `ℝ`-linear
isometric equivalence `β : V ≃ₗᵢ[ℝ] W`, giving `β ∘ m ∘ β⁻¹ : W →L[ℝ] W`. -/
noncomputable def conjClmR (β : V ≃ₗᵢ[ℝ] W) (m : V →L[ℝ] V) : W →L[ℝ] W :=
  (betaR β) ∘L m ∘L (betaR β.symm)

omit [CompleteSpace V] [CompleteSpace W] in
@[simp] lemma conjClmR_apply (β : V ≃ₗᵢ[ℝ] W) (m : V →L[ℝ] V) (w : W) :
    conjClmR β m w = β (m (β.symm w)) := rfl

/-- A **realification system isometry** between complex systems `(M, V)` and
`(N, W)`: the `ℝ`-linear isometric equivalence `β` carries the realified `M` onto
the realified `N` by conjugation. -/
def IsRealSystemIso (M : System ℂ V) (N : System ℂ W) (β : V ≃ₗᵢ[ℝ] W) : Prop :=
  (fun n : W →L[ℂ] W => n.restrictScalars ℝ) '' N.ops
    = (fun m : V →L[ℂ] V => conjClmR β (m.restrictScalars ℝ)) '' M.ops

/-- `ℂ`-linearity of a realification isometry — it *is* a complex system
isometry. -/
def CLinear (β : V ≃ₗᵢ[ℝ] W) : Prop := ∀ x, β (Complex.I • x) = Complex.I • β x

/-- `ℂ`-antilinearity of a realification isometry — it *is* a complex system
antiisometry. -/
def CAntilinear (β : V ≃ₗᵢ[ℝ] W) : Prop := ∀ x, β (Complex.I • x) = -(Complex.I • β x)

/-! ## The transported complex structure `K = β ∘ (i·) ∘ β⁻¹` -/

/-- The transported complex structure: `K := β ∘ mulI ∘ β⁻¹`, an `ℝ`-linear
operator on `W`. -/
noncomputable def transK (β : V ≃ₗᵢ[ℝ] W) : W →L[ℝ] W := conjClmR β mulI

omit [CompleteSpace V] [CompleteSpace W] in
@[simp] lemma transK_apply (β : V ≃ₗᵢ[ℝ] W) (w : W) :
    transK β w = β (Complex.I • β.symm w) := by
  simp [transK, conjClmR_apply, mulI_apply]

omit [CompleteSpace V] [CompleteSpace W] in
/-- `K (β x) = β (i • x)`. -/
lemma transK_beta (β : V ≃ₗᵢ[ℝ] W) (x : V) :
    transK β (β x) = β (Complex.I • x) := by
  simp [transK_apply]

omit [CompleteSpace V] [CompleteSpace W] in
/-- `K² = -1`: the transported operator is again a complex structure. -/
lemma transK_sq (β : V ≃ₗᵢ[ℝ] W) : (transK β) * (transK β) = -1 := by
  ext w
  simp only [ContinuousLinearMap.mul_apply, transK_apply, LinearIsometryEquiv.symm_apply_apply,
    ContinuousLinearMap.neg_apply, ContinuousLinearMap.one_apply, smul_smul, Complex.I_mul_I,
    neg_one_smul, map_neg, LinearIsometryEquiv.apply_symm_apply]

/-- From a realification system isometry, each `n ∈ N` is `β`-conjugate to some
`m ∈ M`: `∀ w, n w = β (m (β⁻¹ w))`. -/
lemma exists_source_of_isRealSystemIso {M : System ℂ V} {N : System ℂ W}
    {β : V ≃ₗᵢ[ℝ] W} (hβ : IsRealSystemIso M N β) {n : W →L[ℂ] W} (hn : n ∈ N.ops) :
    ∃ m ∈ M.ops, ∀ w, n w = β (m (β.symm w)) := by
  have hmem : (n.restrictScalars ℝ) ∈
      (fun m : V →L[ℂ] V => conjClmR β (m.restrictScalars ℝ)) '' M.ops := by
    rw [← hβ]; exact ⟨n, hn, rfl⟩
  obtain ⟨m, hm, hmeq⟩ := hmem
  refine ⟨m, hm, fun w => ?_⟩
  have := congr_arg (fun T : W →L[ℝ] W => T w) hmeq
  simpa [conjClmR_apply] using this.symm

/-- The transported complex structure `K` commutes with the target system `N`
(as a real-linear operator). -/
lemma transK_realCommutes {M : System ℂ V} {N : System ℂ W}
    {β : V ≃ₗᵢ[ℝ] W} (hβ : IsRealSystemIso M N β) : RealCommutes N (transK β) := by
  intro n hn x
  obtain ⟨m, hm, hmeq⟩ := exists_source_of_isRealSystemIso hβ hn
  -- `n x = β (m (β⁻¹ x))`; `K` is `β ∘ (i·) ∘ β⁻¹`; use `m` is ℂ-linear.
  have hsym : β.symm (n x) = m (β.symm x) := by
    rw [hmeq x, LinearIsometryEquiv.symm_apply_apply]
  simp only [transK_apply]
  rw [hsym, hmeq (β (Complex.I • β.symm x)), LinearIsometryEquiv.symm_apply_apply, ← map_smul]

/-! ## C-complex case (Prop 16) -/

/-- **Prop 16, C-complex dichotomy.**  If `(N, W)` is a C-complex Schur system
(`IsSchurFull N`, `NoAntilinearCommutant N`) on a nontrivial space, then any
realification system isometry `β : V ≃ₗᵢ[ℝ] W` is either `ℂ`-linear or
`ℂ`-antilinear: the realifications of two C-complex Schur systems are isometric
iff the systems are isometric or antiisometric. -/
theorem Ccomplex_realification_dichotomy [Nontrivial W]
    {M : System ℂ V} {N : System ℂ W}
    (hSchurN : IsSchurFull N) (hNo : NoAntilinearCommutant N)
    {β : V ≃ₗᵢ[ℝ] W} (hβ : IsRealSystemIso M N β) :
    CLinear β ∨ CAntilinear β := by
  -- `K = β ∘ (i·) ∘ β⁻¹` lies in the real commutant, hence is `c·1` (Prop 18).
  have hKcomm : RealCommutes N (transK β) := transK_realCommutes hβ
  obtain ⟨c, hc⟩ := (Rcomplex_realCommutant_eq_complex N hSchurN hNo (transK β)).1 hKcomm
  -- `K² = -1` forces `c² = -1`.
  have hKsq : (transK β) * (transK β) = -1 := transK_sq β
  have hcsq : c ^ 2 = -1 := by
    obtain ⟨w, hw⟩ := exists_ne (0 : W)
    have h1 : (transK β) ((transK β) w) = -w := by
      have := congr_arg (fun T : W →L[ℝ] W => T w) hKsq
      simpa [ContinuousLinearMap.mul_apply] using this
    rw [hc] at h1
    simp only [cembed_apply] at h1
    rw [smul_smul] at h1
    have : (c * c) • w = (-1 : ℂ) • w := by rw [h1]; simp
    have hcc : c * c = -1 := by
      have := smul_left_injective ℂ hw this
      simpa using this
    rw [sq]; exact hcc
  -- `c = i` or `c = -i`.
  have hcval : c = Complex.I ∨ c = -Complex.I := by
    have hfac : (c - Complex.I) * (c + Complex.I) = 0 := by
      have : (c - Complex.I) * (c + Complex.I) = c ^ 2 - Complex.I ^ 2 := by ring
      rw [this, hcsq, Complex.I_sq]; ring
    rcases mul_eq_zero.1 hfac with h | h
    · left; linear_combination h
    · right; linear_combination h
  -- Translate `K = c·1` into the statement about `β`.
  have hKb : ∀ x, β (Complex.I • x) = c • β x := by
    intro x
    have := hc
    have h2 : transK β (β x) = c • (β x) := by rw [hc]; simp [cembed_apply]
    rw [transK_beta] at h2
    exact h2
  rcases hcval with h | h
  · left; intro x; rw [hKb x, h]
  · right; intro x; rw [hKb x, h]; simp

/-- **Prop 16 (C-complex case), packaged as an iff.**  For C-complex Schur
systems, a realification isometry that is `ℂ`-linear or `ℂ`-antilinear (i.e. a
complex system isometry or antiisometry) exists **iff** a realification isometry
exists. -/
theorem Ccomplex_iso_or_antiiso_iff_realification_iso [Nontrivial W]
    (M : System ℂ V) (N : System ℂ W)
    (hSchurN : IsSchurFull N) (hNo : NoAntilinearCommutant N) :
    (∃ β : V ≃ₗᵢ[ℝ] W, IsRealSystemIso M N β ∧ (CLinear β ∨ CAntilinear β)) ↔
    (∃ β : V ≃ₗᵢ[ℝ] W, IsRealSystemIso M N β) := by
  constructor
  · rintro ⟨β, hβ, _⟩; exact ⟨β, hβ⟩
  · rintro ⟨β, hβ⟩
    exact ⟨β, hβ, Ccomplex_realification_dichotomy hSchurN hNo hβ⟩

/-! ## C-pseudoreal case: the `rot` (quaternion) rotations

The C-pseudoreal target carries a commuting anti-unitary `θN` with `θN² = -1`.
By Prop 19 (`Rpseudoreal_realCommutant_eq_quaternion`) the real commutant is the
quaternions `ℝ⟨1, i, θN, i·θN⟩`.  We realize this algebra concretely through the
operators `rot θ p s : w ↦ p • w + s • θ w` (`p, s : ℂ`), which is the quaternion
`p + s·j` acting on `w`; `rot` composition is quaternion multiplication and, for a
`θ`-anti-unitary with `θ² = -1`, the crucial orthogonality `x ⊥ θ x`
(`theta_inner_self_zero`, a Frobenius–Schur relation) makes every unit `rot` an
isometry. -/

section Rot

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Scalar multiplication by `p : ℂ` as an `ℝ`-linear operator. -/
noncomputable def cScal (p : ℂ) : H →L[ℝ] H :=
  ContinuousLinearMap.restrictScalars ℝ (p • (1 : H →L[ℂ] H))

omit [CompleteSpace H] in
@[simp] lemma cScal_apply (p : ℂ) (w : H) : cScal p w = p • w := by simp [cScal]

/-- The quaternion rotation `w ↦ p • w + s • θ w`. -/
noncomputable def rot (θ : AntiUnitary H) (p s : ℂ) : H →L[ℝ] H :=
  cScal p + cScal s ∘L thetaR θ

omit [CompleteSpace H] in
@[simp] lemma rot_apply (θ : AntiUnitary H) (p s : ℂ) (w : H) :
    rot θ p s w = p • w + s • θ w := by simp [rot, cScal_apply, thetaR_apply]

omit [CompleteSpace H] in
/-- **Frobenius–Schur orthogonality.**  For an anti-unitary `θ` with `θ² = -1`,
every vector is orthogonal to its image `x ⊥ θ x`. -/
lemma theta_inner_self_zero (θ : AntiUnitary H) (hθ : ∀ x, θ (θ x) = -x) (x : H) :
    inner ℂ x (θ x) = (0 : ℂ) := by
  have h1 : inner ℂ (θ x) (θ (θ x)) = conj (inner ℂ x (θ x)) := θ.inner_map_map x (θ x)
  rw [hθ x, inner_neg_right, inner_conj_symm] at h1
  have h2 : inner ℂ (θ x) x = (0 : ℂ) := by linear_combination (-1 / 2 : ℂ) * h1
  rw [← inner_conj_symm, h2, map_zero]

omit [CompleteSpace H] in
/-- `rot` composition is quaternion multiplication `(p₁ + s₁ j)(p₂ + s₂ j)`. -/
lemma rot_comp (θ : AntiUnitary H) (hθ : ∀ x, θ (θ x) = -x) (p1 s1 p2 s2 : ℂ) :
    rot θ p1 s1 ∘L rot θ p2 s2
      = rot θ (p1 * p2 - s1 * conj s2) (p1 * s2 + s1 * conj p2) := by
  ext w
  simp only [ContinuousLinearMap.comp_apply, rot_apply, map_add, map_smulₛₗ, smul_smul, hθ w]
  simp only [smul_neg, sub_smul, add_smul, mul_smul]; abel

omit [CompleteSpace H] in
/-- The squared norm of a `rot` image: `‖rot θ p s x‖² = (‖p‖² + ‖s‖²)·‖x‖²`. -/
lemma rot_normSq (θ : AntiUnitary H) (hθ : ∀ x, θ (θ x) = -x) (p s : ℂ) (x : H) :
    ‖rot θ p s x‖ ^ 2 = (‖p‖ ^ 2 + ‖s‖ ^ 2) * ‖x‖ ^ 2 := by
  rw [rot_apply]
  have horth : inner ℂ (p • x) (s • θ x) = (0 : ℂ) := by
    rw [inner_smul_left, inner_smul_right, theta_inner_self_zero θ hθ x]; ring
  rw [norm_add_sq (𝕜 := ℂ), horth]; simp only [map_zero, mul_zero, add_zero]
  rw [norm_smul, norm_smul, θ.norm_map, mul_pow, mul_pow]; ring

omit [CompleteSpace H] in
/-- Unit `rot`s are isometries. -/
lemma rot_isometry (θ : AntiUnitary H) (hθ : ∀ x, θ (θ x) = -x) (p s : ℂ)
    (hps : ‖p‖ ^ 2 + ‖s‖ ^ 2 = 1) (x : H) : ‖rot θ p s x‖ = ‖x‖ := by
  have hsq : ‖rot θ p s x‖ ^ 2 = ‖x‖ ^ 2 := by rw [rot_normSq θ hθ, hps, one_mul]
  have h := congr_arg Real.sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h

omit [CompleteSpace H] in
lemma rot_one_zero (θ : AntiUnitary H) : rot θ 1 0 = (1 : H →L[ℝ] H) := by ext w; simp

omit [CompleteSpace H] in
/-- `rot θ i 0` is multiplication by `i`. -/
lemma mulI_eq_rot (θ : AntiUnitary H) : (mulI : H →L[ℝ] H) = rot θ Complex.I 0 := by
  ext w; simp

/-- A unit `rot` as an `ℝ`-linear isometric equivalence. -/
noncomputable def rotEquiv (θ : AntiUnitary H) (hθ : ∀ x, θ (θ x) = -x) (p s : ℂ)
    (hps : ‖p‖ ^ 2 + ‖s‖ ^ 2 = 1) : H ≃ₗᵢ[ℝ] H := by
  have hinvR : rot θ p s ∘L rot θ (conj p) (-s) = 1 := by
    rw [rot_comp θ hθ]
    have h1 : p * conj p - s * conj (-s) = 1 := by
      rw [map_neg, mul_neg, sub_neg_eq_add, Complex.mul_conj, Complex.mul_conj]
      push_cast [Complex.normSq_eq_norm_sq]; exact_mod_cast hps
    have h2 : p * -s + s * conj (conj p) = 0 := by rw [Complex.conj_conj]; ring
    rw [h1, h2, rot_one_zero]
  refine LinearIsometryEquiv.ofSurjective
    ⟨(rot θ p s).toLinearMap, fun x => rot_isometry θ hθ p s hps x⟩ ?_
  intro w
  exact ⟨rot θ (conj p) (-s) w, by
    have := congr_arg (fun T : H →L[ℝ] H => T w) hinvR; simpa using this⟩

omit [CompleteSpace H] in
@[simp] lemma rotEquiv_apply (θ : AntiUnitary H) (hθ : ∀ x, θ (θ x) = -x) (p s : ℂ)
    (hps : ‖p‖ ^ 2 + ‖s‖ ^ 2 = 1) (w : H) : rotEquiv θ hθ p s hps w = p • w + s • θ w := by
  change (rot θ p s) w = _; rw [rot_apply]

omit [CompleteSpace H] in
/-- `rot` coefficient injectivity (on a nontrivial space, using `x ⊥ θ x`). -/
lemma rot_inj (θ : AntiUnitary H) (hθ : ∀ x, θ (θ x) = -x) [Nontrivial H]
    {a b c d : ℂ} (h : rot θ a b = rot θ c d) : a = c ∧ b = d := by
  obtain ⟨x, hx⟩ := exists_ne (0 : H)
  have heq : a • x + b • θ x = c • x + d • θ x := by
    have := congr_arg (fun T : H →L[ℝ] H => T x) h; simpa [rot_apply] using this
  have hθx : θ x ≠ 0 := fun h0 => hx (θ.map_eq_zero_iff.mp h0)
  have hi := congr_arg (fun v => inner ℂ x v) heq
  simp only [inner_add_right, inner_smul_right, theta_inner_self_zero θ hθ x, mul_zero,
    add_zero] at hi
  have hxi : inner ℂ x x ≠ 0 := inner_self_ne_zero.2 hx
  have hac : a = c := mul_right_cancel₀ hxi hi
  refine ⟨hac, ?_⟩
  rw [hac] at heq
  have h5 : b • θ x = d • θ x := add_left_cancel heq
  have h6 := sub_eq_zero.2 h5
  rw [← sub_smul] at h6
  rcases smul_eq_zero.1 h6 with h1 | h1
  · exact sub_eq_zero.1 h1
  · exact absurd h1 hθx

omit [CompleteSpace H] in
/-- Coercion form of `qembed`: the image of a quaternion is its real part times the
identity plus the three imaginary coefficients against `mulI`/`thetaR`. -/
lemma qembed_apply (θ : AntiUnitary H) (hθ : ∀ x, θ (θ x) = -x) (q : Quaternion ℝ) :
    qembed θ hθ q
      = algebraMap ℝ (H →L[ℝ] H) q.re + q.imI • mulI + q.imJ • thetaR θ
        + q.imK • (mulI * thetaR θ) := rfl

omit [CompleteSpace H] in
/-- The quaternion `q` as a `rot` (in the `θ`-frame). -/
lemma qembed_eq_rot (θ : AntiUnitary H) (hθ : ∀ x, θ (θ x) = -x) (q : Quaternion ℝ) :
    qembed θ hθ q = rot θ (q.re + q.imI * Complex.I) (q.imJ + q.imK * Complex.I) := by
  ext w
  simp only [qembed_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    Algebra.algebraMap_eq_smul_one, ContinuousLinearMap.one_apply, mulI_apply,
    ContinuousLinearMap.mul_apply, thetaR_apply, rot_apply]
  rw [add_smul, add_smul, mul_smul, mul_smul]
  simp only [Complex.coe_smul]; abel

/-- A `rot` in the `θN`-frame commutes with `N` when `θN` does. -/
lemma rot_realCommutes {N : System ℂ H} {θ : AntiUnitary H}
    (hθc : CommutesAntiUnitary N θ) (p s : ℂ) : RealCommutes N (rot θ p s) := by
  intro n hn x
  simp only [rot_apply, map_add, map_smul]
  rw [hθc n hn x]

end Rot

/-! ## C-pseudoreal case (Prop 16) -/

omit [CompleteSpace V] [CompleteSpace W] in
/-- `transK β` is an isometry (conjugate of the isometry `mulI` by the isometry
`β`). -/
lemma transK_isometry (β : V ≃ₗᵢ[ℝ] W) (w : W) : ‖transK β w‖ = ‖w‖ := by
  rw [transK_apply, β.norm_map, norm_smul]
  simp

/-- Post-composing a realification isometry with an `ℝ`-isometric equivalence
that commutes with `N` is again a realification isometry. -/
lemma isRealSystemIso_trans_commuting {M : System ℂ V} {N : System ℂ W}
    {β : V ≃ₗᵢ[ℝ] W} (hβ : IsRealSystemIso M N β) {U : W ≃ₗᵢ[ℝ] W}
    (hU : RealCommutes N (betaR U)) : IsRealSystemIso M N (β.trans U) := by
  -- On each `m ∈ M`, conjugation by `β.trans U` agrees with conjugation by `β`.
  have hkey : ∀ m ∈ M.ops, conjClmR β (m.restrictScalars ℝ)
      = conjClmR (β.trans U) (m.restrictScalars ℝ) := by
    intro m hm
    -- `conjClmR β (realify m) = realify n` for some `n ∈ N`; `U` fixes it.
    have hmem : conjClmR β (m.restrictScalars ℝ) ∈
        (fun n : W →L[ℂ] W => n.restrictScalars ℝ) '' N.ops := by
      rw [hβ]; exact ⟨m, hm, rfl⟩
    obtain ⟨n, hn, hneq⟩ := hmem
    have hnw : ∀ y, β ((m.restrictScalars ℝ) (β.symm y)) = n y := by
      intro y
      have h0 : conjClmR β (m.restrictScalars ℝ) y = n y := by rw [← hneq]; rfl
      rwa [conjClmR_apply] at h0
    have hUcomm : ∀ y, U (n y) = n (U y) := fun y => hU n hn y
    ext w
    rw [conjClmR_apply, conjClmR_apply,
      (show (β.trans U).symm w = β.symm (U.symm w) by
        apply (β.trans U).injective
        rw [LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.trans_apply,
          LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply]),
      LinearIsometryEquiv.trans_apply]
    -- RHS : U (β (realm (β.symm (U.symm w)))) ; LHS : β (realm (β.symm w))
    rw [hnw w, hnw (U.symm w), hUcomm, LinearIsometryEquiv.apply_symm_apply]
  unfold IsRealSystemIso
  rw [hβ]
  exact Set.image_congr (fun m hm => hkey m hm)

/-- **Prop 16, C-pseudoreal dichotomy.**  If `(N, W)` is a C-pseudoreal Schur
system — `IsSchurFull N` with a commuting anti-unitary `θN` satisfying `θN² = -1`
— on a nontrivial space, then every realification system isometry `β` can be
post-composed with a quaternion rotation to a realification isometry that is
`ℂ`-linear or `ℂ`-antilinear.  Hence the realifications of two C-pseudoreal Schur
systems are isometric iff the systems are isometric or antiisometric. -/
theorem Cpseudoreal_realification_dichotomy [Nontrivial W]
    {M : System ℂ V} {N : System ℂ W} (hSchurN : IsSchurFull N)
    {θN : AntiUnitary W} (hθN : ∀ x, θN (θN x) = -x) (hθNc : CommutesAntiUnitary N θN)
    {β : V ≃ₗᵢ[ℝ] W} (hβ : IsRealSystemIso M N β) :
    ∃ γ : V ≃ₗᵢ[ℝ] W, IsRealSystemIso M N γ ∧ (CLinear γ ∨ CAntilinear γ) := by
  -- `K = transK β` lies in the real commutant, so equals `qembed q = rot pK sK`.
  have hKcomm : RealCommutes N (transK β) := transK_realCommutes hβ
  obtain ⟨q, hq⟩ :=
    (Rpseudoreal_realCommutant_eq_quaternion N hSchurN hθN hθNc (transK β)).1 hKcomm
  set pK : ℂ := q.re + q.imI * Complex.I with hpKdef
  set sK : ℂ := q.imJ + q.imK * Complex.I with hsKdef
  have hKrot : transK β = rot θN pK sK := by rw [hq, qembed_eq_rot]
  -- `K` is an isometry ⇒ `‖pK‖² + ‖sK‖² = 1`.
  have hunitK : ‖pK‖ ^ 2 + ‖sK‖ ^ 2 = 1 := by
    obtain ⟨w, hw⟩ := exists_ne (0 : W)
    have h1 : ‖rot θN pK sK w‖ ^ 2 = ‖w‖ ^ 2 := by
      rw [← hKrot, transK_isometry]
    rw [rot_normSq θN hθN] at h1
    have hw2 : ‖w‖ ^ 2 ≠ 0 := by positivity
    have h2 : (‖pK‖ ^ 2 + ‖sK‖ ^ 2) * ‖w‖ ^ 2 = 1 * ‖w‖ ^ 2 := by rw [one_mul]; exact h1
    exact mul_right_cancel₀ hw2 h2
  -- `K² = -1` gives the two quaternion relations.
  have hKsq : rot θN pK sK ∘L rot θN pK sK = rot θN (-1) 0 := by
    have := transK_sq β
    rw [hKrot] at this
    rw [show rot θN pK sK ∘L rot θN pK sK = rot θN pK sK * rot θN pK sK from rfl, this]
    ext w; simp
  rw [rot_comp θN hθN] at hKsq
  obtain ⟨hC1, hC2⟩ := rot_inj θN hθN hKsq
  -- Case on whether `K = -mulI` (i.e. `β` already antilinear).
  by_cases hneg : pK = -Complex.I ∧ sK = 0
  · refine ⟨β, hβ, Or.inr ?_⟩
    intro x
    have : transK β (β x) = β (Complex.I • x) := transK_beta β x
    rw [hKrot, rot_apply, hneg.1, hneg.2] at this
    simp only [zero_smul, add_zero] at this
    rw [← this]; simp
  · -- Build the rotation `u = (pK + i, sK)` normalized.
    have hn2pos : 0 < ‖pK + Complex.I‖ ^ 2 + ‖sK‖ ^ 2 := by
      rcases eq_or_ne (pK + Complex.I) 0 with h0 | h0
      · rcases eq_or_ne sK 0 with hs0 | hs0
        · exact absurd ⟨by linear_combination h0, hs0⟩ hneg
        · have : ‖sK‖ ^ 2 > 0 := by positivity
          positivity
      · have : ‖pK + Complex.I‖ ^ 2 > 0 := by positivity
        positivity
    set n : ℝ := Real.sqrt (‖pK + Complex.I‖ ^ 2 + ‖sK‖ ^ 2) with hndef
    have hn0 : n ≠ 0 := by
      rw [hndef]; positivity
    have hnsq : (n : ℝ) ^ 2 = ‖pK + Complex.I‖ ^ 2 + ‖sK‖ ^ 2 := by
      rw [hndef, Real.sq_sqrt hn2pos.le]
    set pu : ℂ := (pK + Complex.I) / n with hpudef
    set su : ℂ := sK / n with hsudef
    have hunit : ‖pu‖ ^ 2 + ‖su‖ ^ 2 = 1 := by
      rw [hpudef, hsudef, norm_div, norm_div, div_pow, div_pow, Complex.norm_real,
        Real.norm_eq_abs, sq_abs, ← add_div, ← hnsq]
      field_simp
    set U : W ≃ₗᵢ[ℝ] W := rotEquiv θN hθN pu su hunit with hUdef
    -- `U` commutes with `N`.
    have hUcomm : RealCommutes N (betaR U) := by
      have hbU : betaR U = rot θN pu su := by
        ext w; rw [betaR_apply, hUdef, rotEquiv_apply, rot_apply]
      rw [hbU]; exact rot_realCommutes hθNc pu su
    refine ⟨β.trans U, isRealSystemIso_trans_commuting hβ hUcomm, Or.inl ?_⟩
    -- `U ∘ K = mulI ∘ U`, hence `β.trans U` is `ℂ`-linear.
    have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn0
    have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
    have e1 : pu * pK - su * conj sK = Complex.I * pu := by
      rw [hpudef, hsudef]
      field_simp
      linear_combination hC1 - hI2
    have e2 : pu * sK + su * conj pK = Complex.I * su := by
      rw [hpudef, hsudef]
      field_simp
      linear_combination hC2
    have hstep : rot θN pu su ∘L rot θN pK sK = rot θN Complex.I 0 ∘L rot θN pu su := by
      rw [rot_comp θN hθN, rot_comp θN hθN]
      simp only [zero_mul, sub_zero, add_zero]
      rw [e1, e2]
    -- Assemble `ℂ`-linearity of `γ = β.trans U`.
    have hUrot : ∀ w, U w = rot θN pu su w := fun w => by
      rw [hUdef, rotEquiv_apply, rot_apply]
    intro x
    change U (β (Complex.I • x)) = Complex.I • U (β x)
    have hbx : β (Complex.I • x) = rot θN pK sK (β x) := by
      rw [← hKrot]; exact (transK_beta β x).symm
    rw [hbx, hUrot, hUrot, ← ContinuousLinearMap.comp_apply, hstep,
      ContinuousLinearMap.comp_apply, rot_apply]
    simp

/-- **Prop 16 (C-pseudoreal case), packaged as an iff.**  For C-pseudoreal Schur
systems, a realification isometry that is `ℂ`-linear or `ℂ`-antilinear (i.e. a
complex system isometry or antiisometry) exists **iff** a realification isometry
exists. -/
theorem Cpseudoreal_iso_or_antiiso_iff_realification_iso [Nontrivial W]
    (M : System ℂ V) (N : System ℂ W) (hSchurN : IsSchurFull N)
    {θN : AntiUnitary W} (hθN : ∀ x, θN (θN x) = -x) (hθNc : CommutesAntiUnitary N θN) :
    (∃ β : V ≃ₗᵢ[ℝ] W, IsRealSystemIso M N β ∧ (CLinear β ∨ CAntilinear β)) ↔
    (∃ β : V ≃ₗᵢ[ℝ] W, IsRealSystemIso M N β) := by
  constructor
  · rintro ⟨β, hβ, _⟩; exact ⟨β, hβ⟩
  · rintro ⟨β, hβ⟩
    exact Cpseudoreal_realification_dichotomy hSchurN hθN hθNc hβ

end BookProof.ChapterA


