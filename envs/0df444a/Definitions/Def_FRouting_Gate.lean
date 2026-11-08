-- Prove2me | Definitions.Def_FRouting_Gate
-- name    : FRouting_Gate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:08:58.382194+00:00
-- url     : https://prove2.me/theorems/fda06872-1aa1-4ce1-993a-016d235d0f68
-- title:
--   The qudit gate set
-- statement:
--   On wires of dimension $d$, with $\omega=e^{2\pi i/d}$, the gates are the shift $X_d|i\rangle=|i+1\bmod d\rangle$, the clock $Z_d=\operatorname{diag}(\omega^i)$, the Fourier transform $F_d$ with entries $d^{-1/2}\omega^{jk}$, the phase gate $T_d=\operatorname{diag}(1,e^{i\pi/4},1,\dots,1)$, each on one wire, and $\mathrm{SUM}_d|a\rangle|b\rangle=|a\rangle|b+a\bmod d\rangle$ on two distinct wires. Each is proved unitary.
--
--   At $d=2$ this is $\{X,Z,H,T,\mathrm{CNOT}\}$, the Clifford+T set of Definition 6.1.
--
--   **Formalization Note** The paper fixes no gate set on p.4, so this family is a reading. Its universality is not established here for $d>2$.
-- source:
--   Renard, Computational Bounds for f-Routing, arXiv:2609.40278 (held copy, sha256 4a327f29…), Definition 1.2, p.4; Definition 6.1, p.23

import Mathlib

set_option autoImplicit false

open Matrix
open scoped Kronecker

namespace FRouting

/-- The shift `X_d : |i⟩ ↦ |i + 1 mod d⟩`. -/
def shiftMatrix (d : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  (1 : Matrix (Fin d) (Fin d) ℂ).submatrix id (finRotate d)

/-- The clock `Z_d = diag(ω^i)`, with `ω = e^{2πi/d}`. -/
noncomputable def clockMatrix (d : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.diagonal fun i => Complex.exp (2 * Real.pi * Complex.I * (i : ℕ) / d)

/-- The Fourier transform `F_d`, with entries `d^{-1/2} ω^{jk}`. -/
noncomputable def fourierMatrix (d : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun j k =>
    ((Real.sqrt d : ℝ) : ℂ)⁻¹ * Complex.exp (2 * Real.pi * Complex.I * ((j : ℕ) * (k : ℕ)) / d)

/-- The phase gate `T_d = diag(1, e^{iπ/4}, 1, …, 1)`. -/
noncomputable def teeMatrix (d : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.diagonal fun i => if (i : ℕ) = 1 then Complex.exp (Real.pi * Complex.I / 4) else 1

theorem shiftMatrix_unitary (d : ℕ) : (shiftMatrix d)ᴴ * shiftMatrix d = 1 := by
  unfold shiftMatrix
  rw [conjTranspose_submatrix, conjTranspose_one]
  exact (submatrix_mul_equiv _ _ _ (Equiv.refl _) _).trans (by simp)

theorem clockMatrix_unitary (d : ℕ) : (clockMatrix d)ᴴ * clockMatrix d = 1 := by
  unfold clockMatrix
  rw [diagonal_conjTranspose, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  have h : ‖Complex.exp (2 * Real.pi * Complex.I * ((i : ℕ) : ℂ) / (d : ℂ))‖ = 1 := by
    have : (2 * Real.pi * Complex.I * ((i : ℕ) : ℂ) / (d : ℂ))
        = ((2 * Real.pi * (i : ℕ) / d : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [this, Complex.norm_exp_ofReal_mul_I]
  simp only [Pi.star_apply, RCLike.star_def]
  rw [Complex.conj_mul', h]
  simp

theorem teeMatrix_unitary (d : ℕ) : (teeMatrix d)ᴴ * teeMatrix d = 1 := by
  unfold teeMatrix
  rw [diagonal_conjTranspose, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  have h : ‖Complex.exp (Real.pi * Complex.I / 4)‖ = 1 := by
    have : ((Real.pi : ℂ) * Complex.I / 4) = ((Real.pi / 4 : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [this, Complex.norm_exp_ofReal_mul_I]
  simp only [Pi.star_apply, RCLike.star_def]
  split_ifs
  · rw [Complex.conj_mul', h]; simp
  · simp

theorem fourierMatrix_unitary (d : ℕ) : (fourierMatrix d)ᴴ * fourierMatrix d = 1 := by
  ext j k
  have hjd : (0 : ℝ) < d := by exact_mod_cast j.pos
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hjd.ne'
  have hs : ((Real.sqrt d : ℝ) : ℂ) * ((Real.sqrt d : ℝ) : ℂ) = d := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hjd.le]; simp
  have hs0 : ((Real.sqrt d : ℝ) : ℂ) ≠ 0 := by
    intro h; exact hd0 (by rw [← hs, h]; simp)
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I * (((k : ℕ) : ℂ) - (j : ℕ)) / d) with hζ
  have hterm : ∀ l : Fin d, (fourierMatrix d)ᴴ j l * fourierMatrix d l k
      = (d : ℂ)⁻¹ * ζ ^ (l : ℕ) := by
    intro l
    simp only [fourierMatrix, conjTranspose_apply, of_apply, star_mul', RCLike.star_def, map_inv₀,
      Complex.conj_ofReal]
    rw [← Complex.exp_conj]
    have hconj : (starRingEnd ℂ) (2 * Real.pi * Complex.I * (((l : ℕ) : ℂ) * (j : ℕ)) / d)
        = -(2 * Real.pi * Complex.I * (((l : ℕ) : ℂ) * (j : ℕ)) / d) := by
      simp [Complex.conj_ofReal, map_ofNat]
      ring
    rw [hconj]
    have : ζ ^ (l : ℕ) = Complex.exp (-(2 * Real.pi * Complex.I * (((l : ℕ) : ℂ) * (j : ℕ)) / d))
        * Complex.exp (2 * Real.pi * Complex.I * (((l : ℕ) : ℂ) * (k : ℕ)) / d) := by
      rw [hζ, ← Complex.exp_nat_mul, ← Complex.exp_add]
      congr 1
      field_simp
      ring
    rw [this, ← hs, mul_inv]
    ring
  rw [mul_apply]
  simp only [hterm]
  rw [← Finset.mul_sum, Fin.sum_univ_eq_sum_range (fun l => ζ ^ l) d]
  by_cases hjk : j = k
  · subst hjk
    have : ζ = 1 := by simp [hζ]
    simp [this, hd0]
  · have hne : ζ ≠ 1 := by
      intro h
      rw [hζ, Complex.exp_eq_one_iff] at h
      obtain ⟨m, hm⟩ := h
      have h2pi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by simp [Real.pi_ne_zero]
      have : ((k : ℕ) : ℂ) - (j : ℕ) = m * d := by
        have h3 : (2 * (Real.pi : ℂ) * Complex.I) * ((((k : ℕ) : ℂ) - (j : ℕ)) / d)
            = (2 * (Real.pi : ℂ) * Complex.I) * m := by
          rw [mul_div_assoc] at hm; rw [hm]; ring
        exact (div_eq_iff hd0).mp (mul_left_cancel₀ h2pi h3)
      have hz : ((k : ℕ) : ℤ) - (j : ℕ) = m * d := by exact_mod_cast this
      have hlt1 := k.isLt
      have hlt2 := j.isLt
      have hm0 : m = 0 := by
        by_contra hm0
        have hd : (d : ℤ) ∣ ((k : ℕ) : ℤ) - (j : ℕ) := ⟨m, by rw [hz]; ring⟩
        have hzero := Int.eq_zero_of_abs_lt_dvd hd (by rw [abs_lt]; constructor <;> omega)
        have : (m : ℤ) * d = 0 := by rw [← hz]; exact hzero
        rcases mul_eq_zero.mp this with h | h
        · exact hm0 h
        · omega
      rw [hm0] at hz
      apply hjk
      ext
      omega
    have hpow : ζ ^ d = 1 := by
      rw [hζ, ← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
      refine ⟨(k : ℕ) - (j : ℕ), ?_⟩
      push_cast
      field_simp
    have hsum : ∑ l ∈ Finset.range d, ζ ^ l = 0 := by
      have := geom_sum_mul ζ d
      rw [hpow, sub_self] at this
      exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hne)
    rw [hsum]
    simp [one_apply, hjk]

/-- **A single-wire operator on `W` qudits**: `u` on wire `w`, the identity on the other wires. -/
def onWire {d W : ℕ} (u : Matrix (Fin d) (Fin d) ℂ) (w : Fin W) :
    Matrix (Fin W → Fin d) (Fin W → Fin d) ℂ :=
  let e := Equiv.funSplitAt w (Fin d)
  (u ⊗ₖ (1 : Matrix ({ j // j ≠ w } → Fin d) ({ j // j ≠ w } → Fin d) ℂ)).submatrix e e

theorem onWire_unitary {d W : ℕ} {u : Matrix (Fin d) (Fin d) ℂ} (hu : uᴴ * u = 1) (w : Fin W) :
    (onWire u w)ᴴ * onWire u w = 1 := by
  unfold onWire
  simp only [conjTranspose_submatrix, submatrix_mul_equiv]
  rw [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, hu, Matrix.one_mul,
    one_kronecker_one, submatrix_one_equiv]

/-- `SUM_d` on control `c` and target `t`, as a permutation of basis states:
`|a⟩_c|b⟩_t ↦ |a⟩_c|b + a mod d⟩_t`. -/
def sumPerm {d W : ℕ} (c t : Fin W) (h : c ≠ t) : Equiv.Perm (Fin W → Fin d) where
  toFun s := Function.update s t (s t + s c)
  invFun s := Function.update s t (s t - s c)
  left_inv s := by
    funext i
    by_cases hi : i = t
    · subst hi
      have : NeZero d := ⟨(s i).pos.ne'⟩
      simp [Function.update_of_ne h]
    · simp [Function.update_of_ne hi]
  right_inv s := by
    funext i
    by_cases hi : i = t
    · subst hi
      have : NeZero d := ⟨(s i).pos.ne'⟩
      simp [Function.update_of_ne h]
    · simp [Function.update_of_ne hi]

/-- **The gate set `Gate d W`** on `W` wires of dimension `d`: shift `X_d`, clock `Z_d`, Fourier `F_d`,
phase `T_d` on one wire, and `SUM_d` on two distinct wires. Renard, *Computational Bounds for
f-Routing*, arXiv:2609.40278 (held copy, sha256 4a327f29…), fixes no gate set on p.4; this family
is a reading. At `d = 2` it is `{X, Z, H, T, CNOT}`, the Clifford+T set of Definition 6.1.

**Formalization Note** Wire indices are `Fin W`, so an out-of-range gate cannot be written. -/
inductive Gate (d W : ℕ) where
  | shift (w : Fin W)
  | clock (w : Fin W)
  | fourier (w : Fin W)
  | tee (w : Fin W)
  | sum (c t : Fin W) (h : c ≠ t)

/-- The unitary of a gate, on the basis `Fin W → Fin d` of the `W` wires. -/
noncomputable def Gate.matrix {d W : ℕ} : Gate d W → Matrix (Fin W → Fin d) (Fin W → Fin d) ℂ
  | .shift w => onWire (shiftMatrix d) w
  | .clock w => onWire (clockMatrix d) w
  | .fourier w => onWire (fourierMatrix d) w
  | .tee w => onWire (teeMatrix d) w
  | .sum c t h => (1 : Matrix (Fin W → Fin d) (Fin W → Fin d) ℂ).submatrix id (sumPerm c t h)

theorem Gate.matrix_unitary {d W : ℕ} (g : Gate d W) : g.matrixᴴ * g.matrix = 1 := by
  cases g with
  | shift w => exact onWire_unitary (shiftMatrix_unitary d) w
  | clock w => exact onWire_unitary (clockMatrix_unitary d) w
  | fourier w => exact onWire_unitary (fourierMatrix_unitary d) w
  | tee w => exact onWire_unitary (teeMatrix_unitary d) w
  | sum c t h =>
    simp only [Gate.matrix]
    rw [conjTranspose_submatrix, conjTranspose_one]
    exact (submatrix_mul_equiv _ _ _ (Equiv.refl _) _).trans (by simp)

end FRouting


