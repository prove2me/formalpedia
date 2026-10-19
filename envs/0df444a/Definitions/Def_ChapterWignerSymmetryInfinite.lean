-- Prove2me | Definitions.Def_ChapterWignerSymmetryInfinite
-- name    : ChapterWignerSymmetryInfinite
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-16T20:46:18.505982+00:00
-- url     : https://prove2.me/theorems/8e166382-3ab2-4788-be28-15f298610cd9
-- title:
--   The Lean 4 theorem `inner_basis_eq` in the `?` chapter of the timepiece formalization
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterWignerSymmetryInfinite.lean`): generated def bundle for ChapterWignerSymmetryInfinite. See BookProof/ChapterWignerSymmetryInfinite.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterWignerSymmetryInfinite.lean

import Theorems.Thm_BookProof_ChapterOrthogonalSums_hasSum_smul_of_hasSum_norm_sq

import Definitions.Def_ChapterWignerSymmetry
import Definitions.Def_ChapterOrthogonalSums
import Mathlib
import Theorems.Thm_BookProof_ChapterWignerSymmetry_key_complex
import Theorems.Thm_BookProof_ChapterWignerSymmetry_key_complex_prime
import Theorems.Thm_BookProof_ChapterWignerSymmetry_eq_norm_of_re_eq_norm


/-!
# Wigner's symmetry theorem in an arbitrary complex Hilbert space

`BookProof.ChapterWignerSymmetry` proves Wigner's theorem for a space with a **finite**
orthonormal basis.  This file removes the finiteness: the space is an arbitrary complex
Hilbert space, given by an arbitrary Hilbert basis `b : HilbertBasis ι ℂ E`, and the
symmetry `T` is only assumed to preserve all transition probabilities `|⟪x, y⟫|` and to be
onto.  (Surjectivity is genuinely needed in infinite dimensions: the unilateral shift
preserves all transition probabilities and is not unitary.  In finite dimensions it is
automatic, so this really extends the finite theorem.)

## The proof

The images of the basis vectors are rephased exactly as in the finite case
(`phase`, `img`), giving an orthonormal family.  Two infinite-dimensional ingredients
replace the finite sums:

* `hasSum_img_expansion` — every `T x` is the sum of its Fourier series with respect to the
  rephased family, because Bessel's inequality is saturated: `∑ₖ |⟪imgₖ, T x⟫|² = ‖T x‖²`
  (`BookProof.ChapterOrthogonalSums.hasSum_smul_of_hasSum_norm_sq`).  With surjectivity this
  makes the rephased family a Hilbert basis `imgBasis`;
* `eq_smul_of_hasSum_norm` — the equality case of the triangle inequality for series, used
  where the finite proof used it for finite sums.

The algebraic core is the same as in the finite case: the two-index relations
(`key_pair`) obtained from the test vectors `b o + b i` and `b o + i b i`, their consistency
over all indices (`key_global`), and the reconstruction of the global phase.

## Results

* **`wigner_symmetry_hilbert`** — every surjective transition-probability preserving map of a
  complex Hilbert space with a Hilbert basis agrees, up to a phase depending on the vector,
  with one unitary operator or with one antiunitary operator;
* `wigner_symmetry_of_completeSpace` — the same statement for a nontrivial separable-or-not
  complex Hilbert space, with the Hilbert basis produced internally.

Everything is `sorry`-free and uses only the standard axioms.
-/

open scoped InnerProductSpace ComplexConjugate

namespace BookProof.ChapterWignerSymmetryInfinite

open BookProof.ChapterWignerSymmetry BookProof.ChapterOrthogonalSums

variable {ι : Type*} [DecidableEq ι] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] {T : E → E}

/-! ## The rephased images of the basis vectors -/

/-- The phase by which the image `T (b i)` is rotated so that the two nonzero coordinates of
`T (b o + b i)` become equal. -/
noncomputable def phase [DecidableEq ι] (b : HilbertBasis ι ℂ E) (T : E → E) (o i : ι) : ℂ :=
  if i = o then 1 else ⟪T (b i), T (b o + b i)⟫_ℂ / ⟪T (b o), T (b o + b i)⟫_ℂ

/-- The rephased image of the `i`-th basis vector. -/
noncomputable def img (b : HilbertBasis ι ℂ E) (T : E → E) (o i : ι) : E :=
  phase b T o i • T (b i)

variable {b : HilbertBasis ι ℂ E} {o : ι}

theorem inner_basis_eq (i j : ι) : ⟪b i, b j⟫_ℂ = if i = j then 1 else 0 :=
  orthonormal_iff_ite.mp b.orthonormal i j

theorem inner_pair_left_norm (hT : IsWignerSymmetry T) {i : ι} (hi : i ≠ o) :
    ‖⟪T (b o), T (b o + b i)⟫_ℂ‖ = 1 := by
  rw [hT (b o) (b o + b i), inner_add_right, inner_basis_eq o o, inner_basis_eq o i]
  simp [Ne.symm hi]

theorem inner_pair_right_norm (hT : IsWignerSymmetry T) {i : ι} (hi : i ≠ o) :
    ‖⟪T (b i), T (b o + b i)⟫_ℂ‖ = 1 := by
  rw [hT (b i) (b o + b i), inner_add_right, inner_basis_eq i o, inner_basis_eq i i]
  simp [hi]

theorem phase_norm (hT : IsWignerSymmetry T) (i : ι) : ‖phase b T o i‖ = 1 := by
  rw [phase]
  split_ifs with h
  · simp
  · rw [norm_div, inner_pair_right_norm hT h, inner_pair_left_norm hT h, div_one]

theorem phase_self : phase b T o o = 1 := by simp [phase]

theorem phase_ne_zero (hT : IsWignerSymmetry T) (i : ι) : phase b T o i ≠ 0 := by
  intro h
  have := phase_norm (b := b) (o := o) hT i
  rw [h, norm_zero] at this
  exact zero_ne_one this

/-- The rephased images of a Hilbert basis form an orthonormal family. -/
theorem orthonormal_img (hT : IsWignerSymmetry T) : Orthonormal ℂ (img b T o) := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [img, img, inner_smul_left, inner_smul_right]
  by_cases h : i = j
  · subst h
    have hn : ‖T (b i)‖ = 1 := by rw [norm_map hT, b.orthonormal.1 i]
    have h1 : ⟪T (b i), T (b i)⟫_ℂ = 1 := by
      rw [inner_self_eq_norm_sq_to_K, hn]; norm_num
    have h2 : conj (phase b T o i) * phase b T o i = 1 := by
      rw [mul_comm, Complex.mul_conj]
      have hsq : Complex.normSq (phase b T o i) = ‖phase b T o i‖ ^ 2 := by rw [Complex.sq_norm]
      rw [hsq, phase_norm hT]
      norm_num
    rw [h1, mul_one, h2]
    simp
  · have h0 : ⟪T (b i), T (b j)⟫_ℂ = 0 := by
      have hij := hT (b i) (b j)
      rw [inner_basis_eq i j, if_neg h] at hij
      simpa using hij
    rw [h0, if_neg h]
    ring

/-- The modulus of each coordinate is preserved. -/
theorem inner_img_norm (hT : IsWignerSymmetry T) (k : ι) (x : E) :
    ‖⟪img b T o k, T x⟫_ℂ‖ = ‖⟪b k, x⟫_ℂ‖ := by
  rw [img, inner_smul_left, norm_mul, Complex.norm_conj, phase_norm hT, one_mul, hT]

/-- Parseval for the source basis. -/
theorem hasSum_basis_norm_sq (x : E) : HasSum (fun k => ‖⟪b k, x⟫_ℂ‖ ^ 2) (‖x‖ ^ 2) := by
  have h := b.hasSum_inner_mul_inner x x
  have hterm : ∀ k : ι, ⟪x, b k⟫_ℂ * ⟪b k, x⟫_ℂ = ((‖⟪b k, x⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
    intro k
    have h4 : ⟪x, b k⟫_ℂ = conj ⟪b k, x⟫_ℂ := (inner_conj_symm x (b k)).symm
    rw [h4, mul_comm, Complex.mul_conj, Complex.sq_norm]
  simp only [hterm] at h
  rw [inner_self_eq_norm_sq_to_K] at h
  have h2 := h.mapL Complex.reCLM
  simpa [← Complex.ofReal_pow] using h2

/-- Bessel's inequality is saturated for the rephased family, so `T x` is the sum of its
Fourier series. -/
theorem hasSum_img_expansion (hT : IsWignerSymmetry T) (x : E) :
    HasSum (fun k => ⟪img b T o k, T x⟫_ℂ • img b T o k) (T x) := by
  refine hasSum_smul_of_hasSum_norm_sq (orthonormal_img hT) ?_
  have h : HasSum (fun k => ‖⟪b k, x⟫_ℂ‖ ^ 2) (‖T x‖ ^ 2) := by
    rw [norm_map hT]
    exact hasSum_basis_norm_sq x
  simpa only [inner_img_norm hT] using h

/-! ## The coordinates of `T x` and the two-index relations -/

/-- The coordinate of `T x` along the rephased image of `b k`. -/
noncomputable def coord (b : HilbertBasis ι ℂ E) (T : E → E) (o k : ι) (x : E) : ℂ :=
  ⟪img b T o k, T x⟫_ℂ

theorem coord_norm (hT : IsWignerSymmetry T) (k : ι) (x : E) :
    ‖coord b T o k x‖ = ‖⟪b k, x⟫_ℂ‖ :=
  inner_img_norm hT k x

theorem coord_eq_zero (hT : IsWignerSymmetry T) {k : ι} {x : E} (h : ⟪b k, x⟫_ℂ = 0) :
    coord b T o k x = 0 := by
  have := coord_norm (b := b) (o := o) hT k x
  rw [h, norm_zero] at this
  simpa using this

/-- The image of a vector supported on a finite set of basis vectors is the corresponding
finite combination of the rephased images. -/
theorem img_expansion_finset (hT : IsWignerSymmetry T) (s : Finset ι) (w : E)
    (hw : ∀ k ∉ s, ⟪b k, w⟫_ℂ = 0) :
    T w = ∑ k ∈ s, coord b T o k w • img b T o k := by
  have h1 : HasSum (fun k => coord b T o k w • img b T o k) (T w) := hasSum_img_expansion hT w
  have h2 : HasSum (fun k => coord b T o k w • img b T o k)
      (∑ k ∈ s, coord b T o k w • img b T o k) := by
    refine hasSum_sum_of_ne_finset_zero ?_
    intro k hk
    rw [coord_eq_zero hT (hw k hk), zero_smul]
  exact h1.unique h2

/-- The transition amplitude with a finitely supported vector, in coordinates. -/
theorem inner_T_finset (hT : IsWignerSymmetry T) (s : Finset ι) (w : E)
    (hw : ∀ k ∉ s, ⟪b k, w⟫_ℂ = 0) (x : E) :
    ⟪T x, T w⟫_ℂ = ∑ k ∈ s, coord b T o k w * conj (coord b T o k x) := by
  rw [img_expansion_finset hT s w hw, inner_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [inner_smul_right, ← inner_conj_symm (T x) (img b T o k)]
  rfl

/-! ### The two test vectors -/

/-- The test vector `b o + z · b i`. -/
noncomputable def testVec (b : HilbertBasis ι ℂ E) (o i : ι) (z : ℂ) : E := b o + z • b i

theorem inner_testVec_o {i : ι} (hi : i ≠ o) (z : ℂ) : ⟪b o, testVec b o i z⟫_ℂ = 1 := by
  rw [testVec, inner_add_right, inner_smul_right, inner_basis_eq o o, inner_basis_eq o i,
    if_pos rfl, if_neg (Ne.symm hi)]
  ring

theorem inner_testVec_i {i : ι} (hi : i ≠ o) (z : ℂ) : ⟪b i, testVec b o i z⟫_ℂ = z := by
  rw [testVec, inner_add_right, inner_smul_right, inner_basis_eq i o, inner_basis_eq i i,
    if_pos rfl, if_neg hi]
  ring

theorem inner_testVec_other {i : ι} (z : ℂ) {k : ι} (hk : k ∉ ({o, i} : Finset ι)) :
    ⟪b k, testVec b o i z⟫_ℂ = 0 := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
  rw [testVec, inner_add_right, inner_smul_right, inner_basis_eq k o, inner_basis_eq k i,
    if_neg hk.1, if_neg hk.2]
  ring

theorem inner_left_testVec (i : ι) (z : ℂ) (x : E) :
    ⟪x, testVec b o i z⟫_ℂ = conj ⟪b o, x⟫_ℂ + z * conj ⟪b i, x⟫_ℂ := by
  rw [testVec, inner_add_right, inner_smul_right, ← inner_conj_symm x (b o),
    ← inner_conj_symm x (b i)]

theorem inner_T_testVec (hT : IsWignerSymmetry T) {i : ι} (hi : i ≠ o) (z : ℂ) (x : E) :
    ⟪T x, T (testVec b o i z)⟫_ℂ
      = coord b T o o (testVec b o i z) * conj (coord b T o o x)
        + coord b T o i (testVec b o i z) * conj (coord b T o i x) := by
  rw [inner_T_finset hT ({o, i} : Finset ι) _ (fun k hk => inner_testVec_other z hk) x,
    Finset.sum_pair (Ne.symm hi)]

theorem coord_testVec_o_norm (hT : IsWignerSymmetry T) {i : ι} (hi : i ≠ o) (z : ℂ) :
    ‖coord b T o o (testVec b o i z)‖ = 1 := by
  rw [coord_norm hT, inner_testVec_o hi]
  simp

theorem coord_testVec_i_norm (hT : IsWignerSymmetry T) {i : ι} (hi : i ≠ o) (z : ℂ) :
    ‖coord b T o i (testVec b o i z)‖ = ‖z‖ := by
  rw [coord_norm hT, inner_testVec_i hi]

/-- The rephasing was designed so that the two coordinates of `T (b o + b i)` coincide. -/
theorem coord_testVec_one_eq (hT : IsWignerSymmetry T) {i : ι} (hi : i ≠ o) :
    coord b T o o (testVec b o i 1) = coord b T o i (testVec b o i 1) := by
  have hw : testVec b o i 1 = b o + b i := by rw [testVec, one_smul]
  set A := ⟪T (b o), T (b o + b i)⟫_ℂ with hA
  set B := ⟪T (b i), T (b o + b i)⟫_ℂ with hB
  have hAnorm : ‖A‖ = 1 := inner_pair_left_norm hT hi
  have hBnorm : ‖B‖ = 1 := inner_pair_right_norm hT hi
  have hAA : A * conj A = 1 := by
    rw [Complex.mul_conj]
    have hsq : Complex.normSq A = ‖A‖ ^ 2 := by rw [Complex.sq_norm]
    rw [hsq, hAnorm]; norm_num
  have hBB : B * conj B = 1 := by
    rw [Complex.mul_conj]
    have hsq : Complex.normSq B = ‖B‖ ^ 2 := by rw [Complex.sq_norm]
    rw [hsq, hBnorm]; norm_num
  have hA0 : conj A ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hAA
    exact zero_ne_one hAA
  have hleft : coord b T o o (testVec b o i 1) = A := by
    rw [coord, img, phase_self, hw, one_smul]
  have hright : coord b T o i (testVec b o i 1) = conj (B / A) * B := by
    rw [coord, img, phase, if_neg hi, inner_smul_left, hw]
  rw [hleft, hright, map_div₀]
  field_simp
  linear_combination hAA - hBB

/-- The two-index modulus identity coming from the test vector `b o + b i`. -/
theorem modulus_add (hT : IsWignerSymmetry T) {i : ι} (hi : i ≠ o) (x : E) :
    ‖coord b T o o x + coord b T o i x‖ = ‖⟪b o, x⟫_ℂ + ⟪b i, x⟫_ℂ‖ := by
  have hmod := hT x (testVec b o i 1)
  rw [inner_T_testVec hT hi, ← coord_testVec_one_eq hT hi, inner_left_testVec] at hmod
  set P := coord b T o o (testVec b o i 1) with hP
  have hPnorm : ‖P‖ = 1 := coord_testVec_o_norm hT hi 1
  have hfac : P * conj (coord b T o o x) + P * conj (coord b T o i x)
      = P * conj (coord b T o o x + coord b T o i x) := by
    rw [map_add]; ring
  rw [hfac, norm_mul, hPnorm, one_mul, Complex.norm_conj] at hmod
  rw [hmod, one_mul, ← map_add, Complex.norm_conj]

/-- The sign `ζ = ±i` attached to the pair `(o, i)` by the test vector `b o + i b i`. -/
theorem exists_zeta (hT : IsWignerSymmetry T) {i : ι} (hi : i ≠ o) :
    ∃ zeta : ℂ, (zeta = Complex.I ∨ zeta = -Complex.I) ∧
      ∀ x : E, ‖conj (coord b T o o x) + zeta * conj (coord b T o i x)‖
        = ‖conj ⟪b o, x⟫_ℂ + Complex.I * conj ⟪b i, x⟫_ℂ‖ := by
  set w := testVec b o i Complex.I with hw
  set P := coord b T o o w with hP
  set Q := coord b T o i w with hQ
  have hPnorm : ‖P‖ = 1 := coord_testVec_o_norm hT hi Complex.I
  have hQnorm : ‖Q‖ = 1 := by
    rw [hQ, coord_testVec_i_norm hT hi]
    simp
  have hPP : P * conj P = 1 := by
    rw [Complex.mul_conj]
    have hsq : Complex.normSq P = ‖P‖ ^ 2 := by rw [Complex.sq_norm]
    rw [hsq, hPnorm]; norm_num
  -- the relative phase is `± i`
  have hsum : ‖P + Q‖ = ‖(1 : ℂ) + Complex.I‖ := by
    have h := modulus_add (b := b) hT hi w
    rw [inner_testVec_o hi, inner_testVec_i hi] at h
    exact h
  have hzetanorm : ‖conj P * Q‖ = 1 := by
    rw [norm_mul, Complex.norm_conj, hPnorm, hQnorm, mul_one]
  have hzetare : (conj P * Q).re = 0 := by
    have h1 : ‖P + Q‖ ^ 2 = ‖(1 : ℂ) + Complex.I‖ ^ 2 := by rw [hsum]
    have hP2 : ‖P‖ ^ 2 = 1 := by rw [hPnorm]; norm_num
    have hQ2 : ‖Q‖ ^ 2 = 1 := by rw [hQnorm]; norm_num
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im] at h1 hP2 hQ2
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    nlinarith [h1, hP2, hQ2]
  have hzeta : conj P * Q = Complex.I ∨ conj P * Q = -Complex.I := by
    set z := conj P * Q with hz
    have him : z.im = 1 ∨ z.im = -1 := by
      have h2 : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]; ring
      rw [hzetanorm, hzetare] at h2
      have hfac : (z.im - 1) * (z.im + 1) = 0 := by nlinarith
      rcases mul_eq_zero.1 hfac with h | h
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    rcases him with h | h
    · left; apply Complex.ext <;> simp [hzetare, h]
    · right; apply Complex.ext <;> simp [hzetare, h]
  refine ⟨conj P * Q, hzeta, fun x => ?_⟩
  have hmod := hT x w
  rw [inner_T_testVec hT hi, inner_left_testVec] at hmod
  have hfac : P * conj (coord b T o o x) + Q * conj (coord b T o i x)
      = P * (conj (coord b T o o x) + (conj P * Q) * conj (coord b T o i x)) := by
    calc P * conj (coord b T o o x) + Q * conj (coord b T o i x)
        = P * conj (coord b T o o x) + (P * conj P) * (Q * conj (coord b T o i x)) := by
          rw [hPP]; ring
      _ = P * (conj (coord b T o o x) + (conj P * Q) * conj (coord b T o i x)) := by ring
  rw [hfac, norm_mul, hPnorm, one_mul] at hmod
  exact hmod

/-- **The key relation for the pair `(o, i)`**: one of the two alternatives (linear or
conjugate-linear) holds for *all* vectors. -/
theorem key_pair (hT : IsWignerSymmetry T) {i : ι} (hi : i ≠ o) :
    (∀ x : E, conj (coord b T o o x) * coord b T o i x = conj ⟪b o, x⟫_ℂ * ⟪b i, x⟫_ℂ) ∨
    (∀ x : E, conj (coord b T o o x) * coord b T o i x
      = conj (conj ⟪b o, x⟫_ℂ * ⟪b i, x⟫_ℂ)) := by
  obtain ⟨zeta, hzeta, hrel⟩ := exists_zeta hT hi
  rcases hzeta with hz | hz
  · left
    intro x
    refine key_complex (coord b T o o x) (coord b T o i x) ⟪b o, x⟫_ℂ ⟪b i, x⟫_ℂ
      (coord_norm hT o x) (coord_norm hT i x) (modulus_add hT hi x) ?_
    have h := hrel x
    rw [hz] at h
    exact h
  · right
    intro x
    refine key_complex_prime (coord b T o o x) (coord b T o i x) ⟪b o, x⟫_ℂ ⟪b i, x⟫_ℂ
      (coord_norm hT o x) (coord_norm hT i x) (modulus_add hT hi x) ?_
    have h := hrel x
    rw [hz] at h
    exact h

/-! ### Consistency of the alternative over the indices -/

/-- The test vector `b o + z · b i + z · b j`. -/
noncomputable def tripleVec (b : HilbertBasis ι ℂ E) (o i j : ι) (z : ℂ) : E :=
  b o + z • b i + z • b j

variable {i j : ι}

theorem inner_tripleVec_o (hio : i ≠ o) (hjo : j ≠ o) (z : ℂ) :
    ⟪b o, tripleVec b o i j z⟫_ℂ = 1 := by
  rw [tripleVec, inner_add_right, inner_add_right, inner_smul_right, inner_smul_right,
    inner_basis_eq o o, inner_basis_eq o i, inner_basis_eq o j, if_pos rfl,
    if_neg (Ne.symm hio), if_neg (Ne.symm hjo)]
  ring

theorem inner_tripleVec_i (hio : i ≠ o) (hij : i ≠ j) (z : ℂ) :
    ⟪b i, tripleVec b o i j z⟫_ℂ = z := by
  rw [tripleVec, inner_add_right, inner_add_right, inner_smul_right, inner_smul_right,
    inner_basis_eq i o, inner_basis_eq i i, inner_basis_eq i j, if_pos rfl, if_neg hij,
    if_neg hio]
  ring

theorem inner_tripleVec_j (hij : i ≠ j) (hjo : j ≠ o) (z : ℂ) :
    ⟪b j, tripleVec b o i j z⟫_ℂ = z := by
  rw [tripleVec, inner_add_right, inner_add_right, inner_smul_right, inner_smul_right,
    inner_basis_eq j o, inner_basis_eq j i, inner_basis_eq j j, if_pos rfl, if_neg hjo,
    if_neg (Ne.symm hij)]
  ring

theorem inner_tripleVec_other (z : ℂ) {k : ι} (hk : k ∉ ({o, i, j} : Finset ι)) :
    ⟪b k, tripleVec b o i j z⟫_ℂ = 0 := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
  rw [tripleVec, inner_add_right, inner_add_right, inner_smul_right, inner_smul_right,
    inner_basis_eq k o, inner_basis_eq k i, inner_basis_eq k j, if_neg hk.1, if_neg hk.2.1,
    if_neg hk.2.2]
  ring

theorem inner_left_tripleVec (z : ℂ) (x : E) :
    ⟪x, tripleVec b o i j z⟫_ℂ
      = conj ⟪b o, x⟫_ℂ + z * conj ⟪b i, x⟫_ℂ + z * conj ⟪b j, x⟫_ℂ := by
  rw [tripleVec, inner_add_right, inner_add_right, inner_smul_right, inner_smul_right,
    ← inner_conj_symm x (b o), ← inner_conj_symm x (b i), ← inner_conj_symm x (b j)]

theorem sum_triple (hio : i ≠ o) (hjo : j ≠ o) (hij : i ≠ j) (f : ι → ℂ) :
    ∑ k ∈ ({o, i, j} : Finset ι), f k = f o + f i + f j := by
  rw [Finset.sum_insert (by simp [Ne.symm hio, Ne.symm hjo]), Finset.sum_pair hij, add_assoc]

/-- **Consistency of the alternative.**  Two different indices cannot use different
alternatives: the transition probability between `b o + b i + b j` and
`b o + i b i + i b j` would change from `√5` to `1`. -/
theorem key_consistent (hT : IsWignerSymmetry T) (hio : i ≠ o) (hjo : j ≠ o) (hij : i ≠ j)
    (hlin : ∀ x : E, conj (coord b T o o x) * coord b T o i x = conj ⟪b o, x⟫_ℂ * ⟪b i, x⟫_ℂ)
    (hanti : ∀ x : E, conj (coord b T o o x) * coord b T o j x
      = conj (conj ⟪b o, x⟫_ℂ * ⟪b j, x⟫_ℂ)) : False := by
  have hcancel : ∀ P c z : ℂ, P * conj P = 1 → conj P * c = z → c = P * z := by
    intro P c z hPP h
    calc c = (P * conj P) * c := by rw [hPP]; ring
      _ = P * (conj P * c) := by ring
      _ = P * z := by rw [h]
  have hunit : ∀ P : ℂ, ‖P‖ = 1 → P * conj P = 1 := by
    intro P hP
    rw [Complex.mul_conj]
    have hsq : Complex.normSq P = ‖P‖ ^ 2 := by rw [Complex.sq_norm]
    rw [hsq, hP]; norm_num
  set v := tripleVec b o i j 1 with hv
  set w := tripleVec b o i j Complex.I with hw
  have hvo : ⟪b o, v⟫_ℂ = 1 := inner_tripleVec_o hio hjo 1
  have hvi0 : ⟪b i, v⟫_ℂ = 1 := inner_tripleVec_i hio hij 1
  have hvj0 : ⟪b j, v⟫_ℂ = 1 := inner_tripleVec_j hij hjo 1
  have hwo : ⟪b o, w⟫_ℂ = 1 := inner_tripleVec_o hio hjo Complex.I
  have hwi0 : ⟪b i, w⟫_ℂ = Complex.I := inner_tripleVec_i hio hij Complex.I
  have hwj0 : ⟪b j, w⟫_ℂ = Complex.I := inner_tripleVec_j hij hjo Complex.I
  have hpnorm : ‖coord b T o o v‖ = 1 := by rw [coord_norm hT, hvo]; simp
  have hqnorm : ‖coord b T o o w‖ = 1 := by rw [coord_norm hT, hwo]; simp
  have hpp := hunit _ hpnorm
  have hqq := hunit _ hqnorm
  -- the coordinates of the two images
  have hvi : coord b T o i v = coord b T o o v * 1 := by
    refine hcancel _ _ _ hpp ?_
    rw [hlin v, hvo, hvi0]
    simp
  have hvj : coord b T o j v = coord b T o o v * 1 := by
    refine hcancel _ _ _ hpp ?_
    rw [hanti v, hvo, hvj0]
    simp
  have hwi : coord b T o i w = coord b T o o w * Complex.I := by
    refine hcancel _ _ _ hqq ?_
    rw [hlin w, hwo, hwi0]
    simp
  have hwj : coord b T o j w = coord b T o o w * (-Complex.I) := by
    refine hcancel _ _ _ hqq ?_
    rw [hanti w, hwo, hwj0]
    simp
  -- compare the two transition probabilities
  have hmod := hT v w
  rw [inner_T_finset hT ({o, i, j} : Finset ι) w
      (fun k hk => inner_tripleVec_other Complex.I hk) v,
    sum_triple hio hjo hij, inner_left_tripleVec, hvo, hvi0, hvj0, hvi, hvj, hwi, hwj] at hmod
  have hleft : coord b T o o w * conj (coord b T o o v)
      + coord b T o o w * Complex.I * conj (coord b T o o v * 1)
      + coord b T o o w * -Complex.I * conj (coord b T o o v * 1)
      = coord b T o o w * conj (coord b T o o v) := by
    rw [map_mul, map_one]
    ring
  rw [hleft, norm_mul, Complex.norm_conj, hpnorm, hqnorm, mul_one] at hmod
  have h5 : ‖conj (1 : ℂ) + Complex.I * conj (1 : ℂ) + Complex.I * conj (1 : ℂ)‖ ^ 2 = 5 := by
    simp [Complex.sq_norm, Complex.normSq_apply]
    norm_num
  rw [← hmod] at h5
  norm_num at h5

/-- The alternative is global: the same one works for every index. -/
theorem key_global (hT : IsWignerSymmetry T) :
    (∀ i, i ≠ o → ∀ x : E,
      conj (coord b T o o x) * coord b T o i x = conj ⟪b o, x⟫_ℂ * ⟪b i, x⟫_ℂ) ∨
    (∀ i, i ≠ o → ∀ x : E,
      conj (coord b T o o x) * coord b T o i x = conj (conj ⟪b o, x⟫_ℂ * ⟪b i, x⟫_ℂ)) := by
  by_cases hex : ∃ i₀, i₀ ≠ o ∧ ∀ x : E,
      conj (coord b T o o x) * coord b T o i₀ x = conj ⟪b o, x⟫_ℂ * ⟪b i₀, x⟫_ℂ
  · obtain ⟨i₀, hi₀, hkey₀⟩ := hex
    left
    intro k hk x
    rcases key_pair hT hk with h | h
    · exact h x
    · by_cases hki : k = i₀
      · subst hki; exact hkey₀ x
      · exact (key_consistent hT hi₀ hk (fun e => hki e.symm) hkey₀ h).elim
  · push_neg at hex
    right
    intro k hk x
    rcases key_pair hT hk with h | h
    · obtain ⟨x₀, hx₀⟩ := hex k hk
      exact absurd (h x₀) hx₀
    · exact h x

/-! ### The equality case of the triangle inequality for series -/

/-- If a series of complex numbers has `|∑ z k| = ∑ |z k|`, all its terms have the same
phase. -/
theorem eq_smul_of_hasSum_norm {z : ι → ℂ} {S : ℂ} (hz : HasSum z S)
    (hn : HasSum (fun k => ‖z k‖) ‖S‖) (hS : S ≠ 0) (k : ι) :
    z k = (S / (‖S‖ : ℂ)) * ((‖z k‖ : ℝ) : ℂ) := by
  have hSpos : (0 : ℝ) < ‖S‖ := norm_pos_iff.2 hS
  have hSC : ((‖S‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hSpos
  set w : ℂ := conj S / ((‖S‖ : ℝ) : ℂ) with hw
  have hwnorm : ‖w‖ = 1 := by
    rw [hw, norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg hSpos.le,
      div_self (ne_of_gt hSpos)]
  have hnormSq : conj S * S = ((‖S‖ ^ 2 : ℝ) : ℂ) := by
    rw [mul_comm, Complex.mul_conj, Complex.sq_norm]
  have hwS : w * S = ((‖S‖ : ℝ) : ℂ) := by
    rw [hw, div_mul_eq_mul_div, hnormSq]
    push_cast
    field_simp
  have hmul : HasSum (fun k => w * z k) (((‖S‖ : ℝ) : ℂ)) := by
    have := hz.mul_left w
    rwa [hwS] at this
  have hre : HasSum (fun k => (w * z k).re) ‖S‖ := by
    have h := hmul.mapL Complex.reCLM
    simpa using h
  have hle : ∀ k, (w * z k).re ≤ ‖z k‖ := by
    intro k
    calc (w * z k).re ≤ ‖w * z k‖ := Complex.re_le_norm _
      _ = ‖z k‖ := by rw [norm_mul, hwnorm, one_mul]
  have hdiff : HasSum (fun k => ‖z k‖ - (w * z k).re) 0 := by
    have := hn.sub hre
    simpa using this
  have hzero : (fun k => ‖z k‖ - (w * z k).re) = 0 :=
    (hasSum_zero_iff_of_nonneg (fun k => by linarith [hle k])).1 hdiff
  have hk : (w * z k).re = ‖z k‖ := by
    have := congrFun hzero k
    simp only [Pi.zero_apply] at this
    linarith
  have hnormwz : ‖w * z k‖ = ‖z k‖ := by rw [norm_mul, hwnorm, one_mul]
  have hreal : w * z k = ((‖z k‖ : ℝ) : ℂ) := by
    have := eq_norm_of_re_eq_norm (z := w * z k) (by rw [hk, hnormwz])
    rw [this, hnormwz]
  have hinv : (S / ((‖S‖ : ℝ) : ℂ)) * w = 1 := by
    have h1 : (S / ((‖S‖ : ℝ) : ℂ)) * w = (conj S * S) / ((‖S‖ : ℝ) : ℂ) ^ 2 := by
      rw [hw]
      field_simp
    rw [h1, hnormSq]
    push_cast
    field_simp
  calc z k = ((S / ((‖S‖ : ℝ) : ℂ)) * w) * z k := by rw [hinv]; ring
    _ = (S / ((‖S‖ : ℝ) : ℂ)) * (w * z k) := by ring
    _ = (S / ((‖S‖ : ℝ) : ℂ)) * ((‖z k‖ : ℝ) : ℂ) := by rw [hreal]

/-! ## The global phase -/

variable (κ : ℂ →+* ℂ)

/-- If the pivot coordinate of `x` does not vanish, all coordinates of `T x` are obtained
from those of `x` by one global phase (and the fixed alternative `κ`). -/
theorem coord_of_key_ne_zero (hT : IsWignerSymmetry T) (hκn : ∀ z, ‖κ z‖ = ‖z‖)
    (hκc : ∀ z, κ (conj z) = conj (κ z))
    (hkey : ∀ i, i ≠ o → ∀ x : E,
      conj (coord b T o o x) * coord b T o i x = κ (conj ⟪b o, x⟫_ℂ * ⟪b i, x⟫_ℂ))
    {x : E} (hx : ⟪b o, x⟫_ℂ ≠ 0) :
    ∃ lam : ℂ, ‖lam‖ = 1 ∧ ∀ k, coord b T o k x = lam * κ ⟪b k, x⟫_ℂ := by
  have hκx : κ ⟪b o, x⟫_ℂ ≠ 0 := by
    intro h
    apply hx
    have hn := hκn ⟪b o, x⟫_ℂ
    rw [h, norm_zero] at hn
    exact norm_eq_zero.1 hn.symm
  refine ⟨coord b T o o x / κ ⟪b o, x⟫_ℂ, ?_, ?_⟩
  · rw [norm_div, coord_norm hT, hκn]
    exact div_self (by simpa using hx)
  · intro k
    have hlam : coord b T o o x = (coord b T o o x / κ ⟪b o, x⟫_ℂ) * κ ⟪b o, x⟫_ℂ := by
      field_simp
    have hlamnorm : (coord b T o o x / κ ⟪b o, x⟫_ℂ) * conj (coord b T o o x / κ ⟪b o, x⟫_ℂ)
        = 1 := by
      rw [Complex.mul_conj]
      have hsq : Complex.normSq (coord b T o o x / κ ⟪b o, x⟫_ℂ)
          = ‖coord b T o o x / κ ⟪b o, x⟫_ℂ‖ ^ 2 := by rw [Complex.sq_norm]
      rw [hsq, norm_div, coord_norm hT, hκn, div_self (by simpa using hx)]
      norm_num
    by_cases hk : k = o
    · subst hk; exact hlam
    · have h := hkey k hk x
      rw [map_mul, hκc] at h
      have hconj : conj (coord b T o o x)
          = conj (coord b T o o x / κ ⟪b o, x⟫_ℂ) * conj (κ ⟪b o, x⟫_ℂ) := by
        rw [← map_mul, ← hlam]
      rw [hconj] at h
      have hne : conj (κ ⟪b o, x⟫_ℂ) ≠ 0 := by simpa using hκx
      have hcancel : conj (coord b T o o x / κ ⟪b o, x⟫_ℂ) * coord b T o k x = κ ⟪b k, x⟫_ℂ := by
        refine mul_left_cancel₀ hne ?_
        calc conj (κ ⟪b o, x⟫_ℂ) * (conj (coord b T o o x / κ ⟪b o, x⟫_ℂ) * coord b T o k x)
            = conj (coord b T o o x / κ ⟪b o, x⟫_ℂ) * conj (κ ⟪b o, x⟫_ℂ) * coord b T o k x := by
              ring
          _ = conj (κ ⟪b o, x⟫_ℂ) * κ ⟪b k, x⟫_ℂ := h
      calc coord b T o k x
          = ((coord b T o o x / κ ⟪b o, x⟫_ℂ) * conj (coord b T o o x / κ ⟪b o, x⟫_ℂ))
            * coord b T o k x := by rw [hlamnorm]; ring
        _ = (coord b T o o x / κ ⟪b o, x⟫_ℂ)
            * (conj (coord b T o o x / κ ⟪b o, x⟫_ℂ) * coord b T o k x) := by ring
        _ = (coord b T o o x / κ ⟪b o, x⟫_ℂ) * κ ⟪b k, x⟫_ℂ := by rw [hcancel]

/-- **The coordinates of `T x` for every `x`.**  Each vector is mapped to `lam · κ x` in
coordinates, for one unit scalar `lam` depending on the vector. -/
theorem coord_of_key (hT : IsWignerSymmetry T) (hκn : ∀ z, ‖κ z‖ = ‖z‖)
    (hκc : ∀ z, κ (conj z) = conj (κ z))
    (hkey : ∀ i, i ≠ o → ∀ x : E,
      conj (coord b T o o x) * coord b T o i x = κ (conj ⟪b o, x⟫_ℂ * ⟪b i, x⟫_ℂ))
    (x : E) : ∃ lam : ℂ, ‖lam‖ = 1 ∧ ∀ k, coord b T o k x = lam * κ ⟪b k, x⟫_ℂ := by
  by_cases hxo : ⟪b o, x⟫_ℂ = 0
  swap
  · exact coord_of_key_ne_zero κ hT hκn hκc hkey hxo
  by_cases hx0 : x = 0
  · refine ⟨1, by norm_num, fun k => ?_⟩
    have hzero : ⟪b k, x⟫_ℂ = 0 := by rw [hx0, inner_zero_right]
    rw [hzero, _root_.map_zero, mul_zero]
    exact coord_eq_zero hT hzero
  -- the pivot coordinate vanishes: compare with `x + b o`
  have hxnorm : (0 : ℝ) < ‖x‖ := norm_pos_iff.2 hx0
  set y := x + b o with hy
  have hyo : ⟪b o, y⟫_ℂ = 1 := by
    rw [hy, inner_add_right, hxo, inner_basis_eq o o, if_pos rfl]
    ring
  have hyk : ∀ k, k ≠ o → ⟪b k, y⟫_ℂ = ⟪b k, x⟫_ℂ := by
    intro k hk
    rw [hy, inner_add_right, inner_basis_eq k o, if_neg hk]
    ring
  obtain ⟨mu, hmunorm, hmu⟩ :=
    coord_of_key_ne_zero κ hT hκn hκc hkey (x := y) (by rw [hyo]; exact one_ne_zero)
  have hcox : coord b T o o x = 0 := coord_eq_zero hT hxo
  have hmuconj : conj mu * mu = 1 := by
    rw [mul_comm, Complex.mul_conj]
    have hsq : Complex.normSq mu = ‖mu‖ ^ 2 := by rw [Complex.sq_norm]
    rw [hsq, hmunorm]; norm_num
  -- the amplitude between `T x` and `T y`, in coordinates
  have hinner : HasSum (fun k => coord b T o k y * conj (coord b T o k x)) ⟪T x, T y⟫_ℂ := by
    have h := (hasSum_img_expansion (b := b) (o := o) hT y).mapL (innerSL ℂ (T x))
    have hterm : ∀ k : ι, ⟪T x, ⟪img b T o k, T y⟫_ℂ • img b T o k⟫_ℂ
        = coord b T o k y * conj (coord b T o k x) := by
      intro k
      rw [inner_smul_right, ← inner_conj_symm (T x) (img b T o k)]
      rfl
    simpa only [innerSL_apply_apply, hterm] using h
  have hz : HasSum (fun k => κ ⟪b k, x⟫_ℂ * conj (coord b T o k x))
      (conj mu * ⟪T x, T y⟫_ℂ) := by
    have h := hinner.mul_left (conj mu)
    have hterm : ∀ k : ι, conj mu * (coord b T o k y * conj (coord b T o k x))
        = κ ⟪b k, x⟫_ℂ * conj (coord b T o k x) := by
      intro k
      by_cases hk : k = o
      · subst hk
        rw [hcox]
        simp
      · rw [hmu k, hyk k hk]
        calc conj mu * (mu * κ ⟪b k, x⟫_ℂ * conj (coord b T o k x))
            = (conj mu * mu) * (κ ⟪b k, x⟫_ℂ * conj (coord b T o k x)) := by ring
          _ = κ ⟪b k, x⟫_ℂ * conj (coord b T o k x) := by rw [hmuconj]; ring
    simpa only [hterm] using h
  have hnormz : ∀ k : ι, ‖κ ⟪b k, x⟫_ℂ * conj (coord b T o k x)‖ = ‖⟪b k, x⟫_ℂ‖ ^ 2 := by
    intro k
    rw [norm_mul, hκn, Complex.norm_conj, coord_norm hT]
    ring
  have hnsum : HasSum (fun k => ‖κ ⟪b k, x⟫_ℂ * conj (coord b T o k x)‖) (‖x‖ ^ 2) := by
    simpa only [hnormz] using hasSum_basis_norm_sq (b := b) x
  have hinnerxy : ⟪x, y⟫_ℂ = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
    rw [hy, inner_add_right, inner_self_eq_norm_sq_to_K, ← inner_conj_symm x (b o), hxo]
    simp
  have hSnorm : ‖conj mu * ⟪T x, T y⟫_ℂ‖ = ‖x‖ ^ 2 := by
    rw [norm_mul, Complex.norm_conj, hmunorm, one_mul, hT x y, hinnerxy, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]
  have hSne : conj mu * ⟪T x, T y⟫_ℂ ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hSnorm
    nlinarith [hSnorm, hxnorm]
  have hnsum' : HasSum (fun k => ‖κ ⟪b k, x⟫_ℂ * conj (coord b T o k x)‖)
      ‖conj mu * ⟪T x, T y⟫_ℂ‖ := by rw [hSnorm]; exact hnsum
  set S := conj mu * ⟪T x, T y⟫_ℂ with hS
  set omega := S / ((‖S‖ : ℝ) : ℂ) with homega
  have homeganorm : ‖omega‖ = 1 := by
    rw [homega, norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg S),
      div_self (by simpa using hSne)]
  refine ⟨conj omega, by rw [Complex.norm_conj, homeganorm], fun k => ?_⟩
  have hterm := eq_smul_of_hasSum_norm hz hnsum' hSne k
  by_cases hak : ⟪b k, x⟫_ℂ = 0
  · rw [hak, _root_.map_zero, mul_zero]
    exact coord_eq_zero hT hak
  · have hκa : κ ⟪b k, x⟫_ℂ ≠ 0 := by
      intro h
      apply hak
      have hn := hκn ⟪b k, x⟫_ℂ
      rw [h, norm_zero] at hn
      exact norm_eq_zero.1 hn.symm
    have hprod : conj (κ ⟪b k, x⟫_ℂ) * κ ⟪b k, x⟫_ℂ
        = ((‖κ ⟪b k, x⟫_ℂ * conj (coord b T o k x)‖ : ℝ) : ℂ) := by
      have h1 : Complex.normSq (κ ⟪b k, x⟫_ℂ) = Complex.normSq ⟪b k, x⟫_ℂ := by
        rw [← Complex.sq_norm, ← Complex.sq_norm, hκn]
      rw [hnormz k, mul_comm, Complex.mul_conj, h1, Complex.sq_norm]
    have hconj := congrArg (starRingEnd ℂ) hterm
    rw [map_mul, map_mul, Complex.conj_conj, Complex.conj_ofReal] at hconj
    -- `conj (κ a) * c = conj omega * ‖z k‖`
    have hne : conj (κ ⟪b k, x⟫_ℂ) ≠ 0 := by simpa using hκa
    refine mul_left_cancel₀ hne ?_
    rw [hconj, ← hprod, ← homega]
    ring

/-! ## Wigner's theorem -/

/-- Under surjectivity the rephased images span a dense subspace. -/
theorem span_img_dense (hT : IsWignerSymmetry T) (hsurj : Function.Surjective T) :
    ⊤ ≤ (Submodule.span ℂ (Set.range (img b T o))).topologicalClosure := by
  rintro y -
  obtain ⟨x, rfl⟩ := hsurj y
  refine mem_closure_of_tendsto (hasSum_img_expansion (b := b) (o := o) hT x)
    (Filter.Eventually.of_forall fun s => ?_)
  exact Submodule.sum_mem _ fun k _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

/-- The rephased images of the basis vectors, as a Hilbert basis. -/
noncomputable def imgBasis (b : HilbertBasis ι ℂ E) (o : ι) (hT : IsWignerSymmetry T)
    (hsurj : Function.Surjective T) : HilbertBasis ι ℂ E :=
  HilbertBasis.mk (v := img b T o) (orthonormal_img hT) (span_img_dense hT hsurj)

theorem imgBasis_apply (hT : IsWignerSymmetry T) (hsurj : Function.Surjective T) :
    ⇑(imgBasis b o hT hsurj) = img b T o :=
  HilbertBasis.coe_mk _ _

/-- **Wigner's symmetry theorem in an arbitrary complex Hilbert space.**  A surjective map
of a complex Hilbert space with a Hilbert basis which preserves all transition probabilities
`|⟪x, y⟫|` agrees, up to a phase depending on the vector, with one unitary operator or with
one antiunitary operator. -/
theorem wigner_symmetry_hilbert (b : HilbertBasis ι ℂ E) (o : ι) (hT : IsWignerSymmetry T)
    (hsurj : Function.Surjective T) :
    (∃ U : E ≃ₗᵢ[ℂ] E, ∀ x, ∃ lam : ℂ, ‖lam‖ = 1 ∧ T x = lam • U x) ∨
    (∃ U : E → E, IsAntiunitary U ∧ ∀ x, ∃ lam : ℂ, ‖lam‖ = 1 ∧ T x = lam • U x) := by
  set G := imgBasis b o hT hsurj with hGdef
  have hG : ⇑G = img b T o := imgBasis_apply hT hsurj
  have hcoordG : ∀ (k : ι) (x : E), G.repr (T x) k = coord b T o k x := by
    intro k x
    rw [HilbertBasis.repr_apply_apply, hG]
    rfl
  have hbcoord : ∀ (k : ι) (x : E), b.repr x k = ⟪b k, x⟫_ℂ := fun k x =>
    b.repr_apply_apply x k
  rcases key_global (b := b) (o := o) hT with hkey | hkey
  · -- the unitary alternative
    left
    refine ⟨b.repr.trans G.repr.symm, fun x => ?_⟩
    obtain ⟨lam, hlam, hk⟩ :=
      coord_of_key (b := b) (o := o) (RingHom.id ℂ) hT (by simp) (by simp) (by simpa using hkey) x
    refine ⟨lam, hlam, ?_⟩
    have hU : HasSum (fun k => ⟪b k, x⟫_ℂ • G k) ((b.repr.trans G.repr.symm) x) := by
      have h := G.hasSum_repr_symm (b.repr x)
      simpa only [hbcoord, LinearIsometryEquiv.trans_apply] using h
    have hTx : HasSum (fun k => lam • (⟪b k, x⟫_ℂ • G k)) (T x) := by
      have h := hasSum_img_expansion (b := b) (o := o) hT x
      have hterm : ∀ k : ι, ⟪img b T o k, T x⟫_ℂ • img b T o k
          = lam • (⟪b k, x⟫_ℂ • G k) := by
        intro k
        have := hk k
        simp only [RingHom.id_apply] at this
        rw [hG, smul_smul, ← this]
        rfl
      simpa only [hterm] using h
    exact hTx.unique (hU.const_smul lam)
  · -- the antiunitary alternative
    right
    refine ⟨fun x => G.repr.symm (star (b.repr x)), ⟨?_, ?_, ?_, ?_⟩, fun x => ?_⟩
    · intro x y
      rw [map_add, star_add, map_add]
    · intro a x
      rw [map_smul, star_smul, map_smul]
      rfl
    · intro x y
      have hxy : ⟪(b.repr x : lp (fun _ : ι => ℂ) 2), b.repr y⟫_ℂ = ⟪x, y⟫_ℂ :=
        b.repr.inner_map_map x y
      have hstar : ⟪star (b.repr x), star (b.repr y)⟫_ℂ = conj ⟪b.repr x, b.repr y⟫_ℂ := by
        have h1 := lp.hasSum_inner (𝕜 := ℂ) (star (b.repr x)) (star (b.repr y))
        have h2 := (lp.hasSum_inner (𝕜 := ℂ) (b.repr x) (b.repr y)).star
        refine h1.unique ?_
        have hterm : ∀ i : ι, star ⟪(b.repr x : lp (fun _ : ι => ℂ) 2) i, (b.repr y) i⟫_ℂ
            = ⟪(star (b.repr x) : lp (fun _ : ι => ℂ) 2) i,
               (star (b.repr y) : lp (fun _ : ι => ℂ) 2) i⟫_ℂ := by
          intro i
          rw [lp.star_apply, lp.star_apply]
          simp [RCLike.inner_apply, mul_comm]
        simpa only [hterm, RCLike.star_def] using h2
      calc ⟪G.repr.symm (star (b.repr x)), G.repr.symm (star (b.repr y))⟫_ℂ
          = ⟪star (b.repr x), star (b.repr y)⟫_ℂ := G.repr.symm.inner_map_map _ _
        _ = conj ⟪(b.repr x : lp (fun _ : ι => ℂ) 2), b.repr y⟫_ℂ := hstar
        _ = conj ⟪x, y⟫_ℂ := by rw [hxy]
    · intro y
      refine ⟨b.repr.symm (star (G.repr y)), ?_⟩
      simp only [LinearIsometryEquiv.apply_symm_apply, star_star,
        LinearIsometryEquiv.symm_apply_apply]
    · obtain ⟨lam, hlam, hk⟩ :=
        coord_of_key (b := b) (o := o) (starRingEnd ℂ) hT (fun z => Complex.norm_conj z)
          (fun z => by simp) hkey x
      refine ⟨lam, hlam, ?_⟩
      have hU : HasSum (fun k => conj ⟪b k, x⟫_ℂ • G k) (G.repr.symm (star (b.repr x))) := by
        have h := G.hasSum_repr_symm (star (b.repr x))
        have hterm : ∀ k : ι, (star (b.repr x) : lp (fun _ : ι => ℂ) 2) k • G k
            = conj ⟪b k, x⟫_ℂ • G k := by
          intro k
          rw [lp.star_apply, hbcoord]
          rfl
        simpa only [hterm] using h
      have hTx : HasSum (fun k => lam • (conj ⟪b k, x⟫_ℂ • G k)) (T x) := by
        have h := hasSum_img_expansion (b := b) (o := o) hT x
        have hterm : ∀ k : ι, ⟪img b T o k, T x⟫_ℂ • img b T o k
            = lam • (conj ⟪b k, x⟫_ℂ • G k) := by
          intro k
          have := hk k
          rw [hG, smul_smul, ← this]
          rfl
        simpa only [hterm] using h
      exact hTx.unique (hU.const_smul lam)

/-- **Wigner's symmetry theorem for an arbitrary nontrivial complex Hilbert space.**  No basis
has to be supplied: one is produced internally. -/
theorem wigner_symmetry_of_completeSpace [Nontrivial E] (hT : IsWignerSymmetry T)
    (hsurj : Function.Surjective T) :
    (∃ U : E ≃ₗᵢ[ℂ] E, ∀ x, ∃ lam : ℂ, ‖lam‖ = 1 ∧ T x = lam • U x) ∨
    (∃ U : E → E, IsAntiunitary U ∧ ∀ x, ∃ lam : ℂ, ‖lam‖ = 1 ∧ T x = lam • U x) := by
  classical
  obtain ⟨s, bs, -⟩ := exists_hilbertBasis ℂ E
  have hne : Nonempty s := by
    by_contra hcon
    rw [not_nonempty_iff] at hcon
    obtain ⟨x, y, hxy⟩ := exists_pair_ne E
    refine hxy ?_
    have hrepr : bs.repr x = bs.repr y := by
      ext i
      exact (hcon.false i).elim
    simpa using congrArg bs.repr.symm hrepr
  obtain ⟨o⟩ := hne
  exact wigner_symmetry_hilbert bs o hT hsurj

end BookProof.ChapterWignerSymmetryInfinite


