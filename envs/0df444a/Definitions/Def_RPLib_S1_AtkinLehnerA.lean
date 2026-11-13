-- Prove2me | Definitions.Def_RPLib_S1_AtkinLehnerA
-- name    : RPLib_S1_AtkinLehnerA
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-13T05:27:17.592203+00:00
-- url     : https://prove2.me/theorems/777b0111-be18-4701-8c4e-0429d47e0f37
-- title:
--   Atkin-Lehner operators on $S_k(\Gamma_1(M))$: matrices and basic properties
-- statement:
--   For $QQ' = M$ with $\gcd(Q,Q') = 1$ the Atkin-Lehner operator $W_Q$ acts on $S_k(\Gamma_1(M))$ by slashing with a matrix $$\begin{pmatrix} Qx & y\\ Mz & Qw\end{pmatrix}, \qquad \det = Q.$$ The file proves that this is well defined, that $W_Q\langle u\rangle = \langle \tilde u\rangle W_Q$ for an explicit twist $\tilde u$, that $W_Q$ maps $S_k(M,\chi)$ to a twisted character space, that $W_Q^2 = Q^{k-2}\langle d\rangle$, and that $W_Q$ is unitary up to a scalar for the Petersson product.
--
--   **Formalization note.** This file is a library module of a formalization of the Ramanujan-Petersson conjecture for holomorphic cusp forms on $\Gamma_1(M)$. It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   A. O. L. Atkin and J. Lehner, Hecke operators on Gamma_0(m), Math. Ann. 185 (1970) 134-160, doi:10.1007/BF01359701; W.-C. W. Li, Newforms and functional equations, Math. Ann. 212 (1975) 285-315, doi:10.1007/BF01344468

import Mathlib
import Definitions.Def_RPLib_S1_Adjoint
import Definitions.Def_RPLib_S1_Level

/-!
# S1-WOPS part A: Atkin-Lehner operators `W_Q` (and the Fricke involution `W_M`) on `S_k(Γ₁(M))`

Part A: the matrices `[[Q x, y], [M z, Q w]]` (det `Q`, `Q Q' = M`), conjugation formulas mod `M`, twist units.
-/

set_option autoImplicit false

open UpperHalfPlane ModularForm CongruenceSubgroup ConjAct
open scoped MatrixGroups Pointwise

noncomputable section

namespace RP.AtkinLehner

open RamanujanPetersson RamanujanPetersson.Diamond RP.Petersson
open Matrix.SpecialLinearGroup (mapGL mapGL_coe_matrix)

/-- Data of an Atkin-Lehner matrix `[[Q x, y], [M z, Q w]]` with `Q Q' = M` and `Q x w - Q' y z = 1`. -/
structure ALData (M Q : ℕ) where
  Q' : ℕ
  x : ℤ
  y : ℤ
  z : ℤ
  w : ℤ
  hM : Q * Q' = M
  hdet : (Q : ℤ) * x * w - (Q' : ℤ) * y * z = 1

variable {M Q : ℕ}

namespace ALData

/-- `[[Q x, y], [M z, Q w]]`. -/
def mat (D : ALData M Q) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![(Q : ℤ) * D.x, D.y; (M : ℤ) * D.z, (Q : ℤ) * D.w]

lemma hM' (D : ALData M Q) : (M : ℤ) = (Q : ℤ) * D.Q' := by
  exact_mod_cast D.hM.symm

lemma det_mat (D : ALData M Q) : D.mat.det = Q := by
  rw [mat, Matrix.det_fin_two_of, D.hM']
  linear_combination (Q : ℤ) * D.hdet

lemma Q_ne_zero [NeZero M] (D : ALData M Q) : Q ≠ 0 := by
  rintro rfl
  exact NeZero.ne M (D.hM.symm.trans (zero_mul _))

lemma det_ne [NeZero M] (D : ALData M Q) : D.mat.det ≠ 0 := by
  rw [det_mat]; exact_mod_cast D.Q_ne_zero

/-- The matrix in `GL(2, ℝ)`. -/
def gl [NeZero M] (D : ALData M Q) : GL (Fin 2) ℝ := Hecke.toGL D.mat D.det_ne

/-- The adjugate data `(w, -y, -z, x)`: `adjD.mat = adj mat`. -/
def adjD (D : ALData M Q) : ALData M Q :=
  ⟨D.Q', D.w, -D.y, -D.z, D.x, D.hM, by linear_combination D.hdet⟩

lemma adjD_mat (D : ALData M Q) : D.adjD.mat = D.mat.adjugate := by
  rw [Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mat, adjD]

/-- The idempotent `e = Q x w mod M` (`≡ 0 mod Q`, `≡ 1 mod Q'`). -/
def eQ' (D : ALData M Q) : ZMod M := (((Q : ℤ) * D.x * D.w : ℤ) : ZMod M)

lemma eQ'_mul_one_sub (D : ALData M Q) : D.eQ' * (1 - D.eQ') = 0 := by
  have key : ((Q : ℤ) * D.x * D.w) * (1 - (Q : ℤ) * D.x * D.w) =
      -(M : ℤ) * (D.x * D.y * D.z * D.w) := by
    rw [D.hM']; linear_combination (-(Q : ℤ) * D.x * D.w) * D.hdet
  have h := congrArg (fun t : ℤ => (t : ZMod M)) key
  simp only [Int.cast_mul, Int.cast_sub, Int.cast_one, Int.cast_neg, Int.cast_natCast,
    ZMod.natCast_self, zero_mul, neg_zero] at h
  rw [eQ']
  push_cast
  linear_combination h

/-- The idempotent does not depend on the data. -/
lemma eQ'_congr (D E : ALData M Q) : D.eQ' = E.eQ' := by
  have h1 : D.eQ' * (1 - E.eQ') = 0 := by
    have key : ((Q : ℤ) * D.x * D.w) * (1 - (Q : ℤ) * E.x * E.w) =
        -(M : ℤ) * (D.x * D.w * E.y * E.z) := by
      rw [E.hM']
      linear_combination (-(Q : ℤ) * D.x * D.w) * E.hdet
    have h := congrArg (fun t : ℤ => (t : ZMod M)) key
    simp only [Int.cast_mul, Int.cast_sub, Int.cast_one, Int.cast_neg, Int.cast_natCast,
      ZMod.natCast_self, zero_mul, neg_zero] at h
    rw [eQ', eQ']; push_cast; linear_combination h
  have h2 : (1 - D.eQ') * E.eQ' = 0 := by
    have key : (1 - (Q : ℤ) * D.x * D.w) * ((Q : ℤ) * E.x * E.w) =
        -(M : ℤ) * (D.y * D.z * E.x * E.w) := by
      rw [D.hM']; linear_combination (-(Q : ℤ) * E.x * E.w) * D.hdet
    have h := congrArg (fun t : ℤ => (t : ZMod M)) key
    simp only [Int.cast_mul, Int.cast_sub, Int.cast_one, Int.cast_neg, Int.cast_natCast,
      ZMod.natCast_self, zero_mul, neg_zero] at h
    rw [eQ', eQ']; push_cast; linear_combination h
  linear_combination h1 - h2

/-- Backward conjugate `A⁻¹ B A` of `B = [[a, b], [M c, d]]` (an integer matrix). -/
def conjMat (D : ALData M Q) (a b c d : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![(Q : ℤ) * D.x * D.w * a + (M : ℤ) * (D.w * D.z * b - D.x * D.y * c) - (D.Q' : ℤ) * D.y * D.z * d,
     D.w * D.y * a + (Q : ℤ) * D.w ^ 2 * b - (D.Q' : ℤ) * D.y ^ 2 * c - D.w * D.y * d;
     (M : ℤ) * (-D.z * D.x * a - (D.Q' : ℤ) * D.z ^ 2 * b + (Q : ℤ) * D.x ^ 2 * c + D.x * D.z * d),
     -(D.Q' : ℤ) * D.y * D.z * a - (M : ℤ) * D.z * D.w * b + (M : ℤ) * D.x * D.y * c +
       (Q : ℤ) * D.x * D.w * d]

lemma conj_back (D : ALData M Q) (a b c d : ℤ) :
    !![a, b; (M : ℤ) * c, d] * D.mat = D.mat * D.conjMat a b c d := by
  obtain ⟨Q', x, y, z, w, hM, hdet⟩ := D
  subst hM
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [mat, conjMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.head_cons, Fin.zero_eta, Fin.mk_one, Fin.isValue] <;> push_cast
  · linear_combination (-(a * ((Q : ℤ) * x) + b * ((Q : ℤ) * Q' * z))) * hdet
  · linear_combination (-(a * y + b * ((Q : ℤ) * w))) * hdet
  · linear_combination (-((Q : ℤ) * Q' * c * ((Q : ℤ) * x) + d * ((Q : ℤ) * Q' * z))) * hdet
  · linear_combination (-((Q : ℤ) * Q' * c * y + d * ((Q : ℤ) * w))) * hdet

lemma conj_fwd (D : ALData M Q) (a b c d : ℤ) :
    D.mat * !![a, b; (M : ℤ) * c, d] = D.adjD.conjMat a b c d * D.mat := by
  obtain ⟨Q', x, y, z, w, hM, hdet⟩ := D
  subst hM
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [mat, adjD, conjMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.head_cons, Fin.zero_eta, Fin.mk_one, Fin.isValue] <;> push_cast
  · linear_combination (-((Q : ℤ) * x * a + y * ((Q : ℤ) * Q' * c))) * hdet
  · linear_combination (-((Q : ℤ) * x * b + y * d)) * hdet
  · linear_combination (-((Q : ℤ) * Q' * z * a + (Q : ℤ) * w * ((Q : ℤ) * Q' * c))) * hdet
  · linear_combination (-((Q : ℤ) * Q' * z * b + (Q : ℤ) * w * d)) * hdet

/-! ### A2. Conjugation mod `M` -/

lemma hdetZ (D : ALData M Q) :
    (Q : ZMod M) * (D.x : ZMod M) * (D.w : ZMod M) - (D.Q' : ZMod M) * (D.y : ZMod M) * (D.z : ZMod M)
      = 1 := by
  have h := congrArg (fun t : ℤ => (t : ZMod M)) D.hdet
  push_cast at h
  exact h

lemma eQ'_eq (D : ALData M Q) : D.eQ' = (Q : ZMod M) * (D.x : ZMod M) * (D.w : ZMod M) := by
  rw [eQ']; push_cast; ring

lemma adjD_eQ' (D : ALData M Q) : D.adjD.eQ' = D.eQ' := eQ'_congr _ _

lemma conjMat_10 (D : ALData M Q) (a b c d : ℤ) : ((D.conjMat a b c d 1 0 : ℤ) : ZMod M) = 0 := by
  have hM0 : (M : ZMod M) = 0 := ZMod.natCast_self M
  show (((M : ℤ) * (-D.z * D.x * a - (D.Q' : ℤ) * D.z ^ 2 * b + (Q : ℤ) * D.x ^ 2 * c + D.x * D.z * d)
    : ℤ) : ZMod M) = 0
  push_cast
  linear_combination ((-(D.z : ZMod M)) * D.x * a - (D.Q' : ZMod M) * (D.z : ZMod M) ^ 2 * b +
    (Q : ZMod M) * (D.x : ZMod M) ^ 2 * c + (D.x : ZMod M) * D.z * d) * hM0

lemma conjMat_00 (D : ALData M Q) (a b c d : ℤ) :
    ((D.conjMat a b c d 0 0 : ℤ) : ZMod M) = D.eQ' * (a : ZMod M) + (1 - D.eQ') * (d : ZMod M) := by
  have hM0 : (M : ZMod M) = 0 := ZMod.natCast_self M
  have h := D.hdetZ
  rw [eQ'_eq]
  show (((Q : ℤ) * D.x * D.w * a + (M : ℤ) * (D.w * D.z * b - D.x * D.y * c) -
    (D.Q' : ℤ) * D.y * D.z * d : ℤ) : ZMod M) = _
  push_cast
  linear_combination (d : ZMod M) * h +
    ((D.w : ZMod M) * D.z * b - (D.x : ZMod M) * D.y * c) * hM0

lemma conjMat_11 (D : ALData M Q) (a b c d : ℤ) :
    ((D.conjMat a b c d 1 1 : ℤ) : ZMod M) = (1 - D.eQ') * (a : ZMod M) + D.eQ' * (d : ZMod M) := by
  have hM0 : (M : ZMod M) = 0 := ZMod.natCast_self M
  have h := D.hdetZ
  rw [eQ'_eq]
  show ((-(D.Q' : ℤ) * D.y * D.z * a - (M : ℤ) * D.z * D.w * b + (M : ℤ) * D.x * D.y * c +
    (Q : ℤ) * D.x * D.w * d : ℤ) : ZMod M) = _
  push_cast
  linear_combination (a : ZMod M) * h +
    ((D.x : ZMod M) * D.y * c - (D.z : ZMod M) * D.w * b) * hM0

lemma det_conjMat [NeZero M] (D : ALData M Q) (a b c d : ℤ) :
    (D.conjMat a b c d).det = a * d - b * ((M : ℤ) * c) := by
  have h := congrArg Matrix.det (D.conj_back a b c d)
  rw [Matrix.det_mul, Matrix.det_mul, det_mat, Matrix.det_fin_two_of] at h
  have hQ : (Q : ℤ) ≠ 0 := by exact_mod_cast D.Q_ne_zero
  exact mul_left_cancel₀ hQ (by linear_combination -h)

/-- Backward conjugation: `B * A = A * B'` for `B ≡ [[*, *], [0, *]] mod M`. -/
lemma exists_back [NeZero M] (D : ALData M Q) (B : Matrix (Fin 2) (Fin 2) ℤ)
    (hB : ((B 1 0 : ℤ) : ZMod M) = 0) :
    ∃ B' : Matrix (Fin 2) (Fin 2) ℤ, B * D.mat = D.mat * B' ∧ B'.det = B.det ∧
      ((B' 1 0 : ℤ) : ZMod M) = 0 ∧
      ((B' 0 0 : ℤ) : ZMod M) = D.eQ' * ((B 0 0 : ℤ) : ZMod M) + (1 - D.eQ') * ((B 1 1 : ℤ) : ZMod M) ∧
      ((B' 1 1 : ℤ) : ZMod M) = (1 - D.eQ') * ((B 0 0 : ℤ) : ZMod M) + D.eQ' * ((B 1 1 : ℤ) : ZMod M) := by
  obtain ⟨c, hc⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hB
  have hBe : B = !![B 0 0, B 0 1; (M : ℤ) * c, B 1 1] := by
    rw [← hc]; exact Matrix.eta_fin_two B
  refine ⟨D.conjMat (B 0 0) (B 0 1) c (B 1 1), ?_, ?_, D.conjMat_10 _ _ _ _, D.conjMat_00 _ _ _ _,
    D.conjMat_11 _ _ _ _⟩
  · conv_lhs => rw [hBe]
    exact D.conj_back _ _ _ _
  · rw [det_conjMat, Matrix.det_fin_two B, hc]

/-- Forward conjugation: `A * B = B' * A` for `B ≡ [[*, *], [0, *]] mod M`. -/
lemma exists_fwd [NeZero M] (D : ALData M Q) (B : Matrix (Fin 2) (Fin 2) ℤ)
    (hB : ((B 1 0 : ℤ) : ZMod M) = 0) :
    ∃ B' : Matrix (Fin 2) (Fin 2) ℤ, D.mat * B = B' * D.mat ∧ B'.det = B.det ∧
      ((B' 1 0 : ℤ) : ZMod M) = 0 ∧
      ((B' 0 0 : ℤ) : ZMod M) = D.eQ' * ((B 0 0 : ℤ) : ZMod M) + (1 - D.eQ') * ((B 1 1 : ℤ) : ZMod M) ∧
      ((B' 1 1 : ℤ) : ZMod M) = (1 - D.eQ') * ((B 0 0 : ℤ) : ZMod M) + D.eQ' * ((B 1 1 : ℤ) : ZMod M) := by
  obtain ⟨c, hc⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hB
  have hBe : B = !![B 0 0, B 0 1; (M : ℤ) * c, B 1 1] := by
    rw [← hc]; exact Matrix.eta_fin_two B
  refine ⟨D.adjD.conjMat (B 0 0) (B 0 1) c (B 1 1), ?_, ?_, D.adjD.conjMat_10 _ _ _ _, ?_, ?_⟩
  · conv_lhs => rw [hBe]
    exact D.conj_fwd _ _ _ _
  · rw [det_conjMat, Matrix.det_fin_two B, hc]
  · rw [D.adjD.conjMat_00, adjD_eQ']
  · rw [D.adjD.conjMat_11, adjD_eQ']

end ALData

lemma Gamma0_det_cast {N : ℕ} {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) :
    ((γ 0 0 : ℤ) : ZMod N) * ((γ 1 1 : ℤ) : ZMod N) = 1 := by
  have h := Matrix.SpecialLinearGroup.det_coe γ
  rw [Matrix.det_fin_two] at h
  have h' := congrArg (fun z : ℤ => (z : ZMod N)) h
  push_cast at h'
  rw [Gamma0_mem.1 hγ, mul_zero, sub_zero] at h'
  exact h'

namespace ALData

section SLconj

variable [NeZero M] (D : ALData M Q)

lemma gl_apply (i j : Fin 2) : (D.gl : Matrix (Fin 2) (Fin 2) ℝ) i j = (D.mat i j : ℝ) :=
  Hecke.toGL_apply _ _ i j

lemma gl_det : D.gl.det.val = Q := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
  simp only [gl_apply]
  have h := D.det_mat
  rw [Matrix.det_fin_two] at h
  exact_mod_cast h

lemma gl_det_pos : 0 < D.gl.det.val := by
  rw [gl_det]; exact_mod_cast Nat.pos_of_ne_zero D.Q_ne_zero

/-- `γ ∈ Γ₀(M)`: `γ A = A γ'` with `γ' ∈ Γ₀(M)`. -/
lemma exists_back_SL {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) :
    ∃ γ' : SL(2, ℤ), γ' ∈ Gamma0 M ∧
      ((γ' 0 0 : ℤ) : ZMod M) = D.eQ' * ((γ 0 0 : ℤ) : ZMod M) + (1 - D.eQ') * ((γ 1 1 : ℤ) : ZMod M) ∧
      ((γ' 1 1 : ℤ) : ZMod M) = (1 - D.eQ') * ((γ 0 0 : ℤ) : ZMod M) + D.eQ' * ((γ 1 1 : ℤ) : ZMod M) ∧
      mapGL ℝ γ * D.gl = D.gl * mapGL ℝ γ' := by
  obtain ⟨B', hB, hdet, h10, h00, h11⟩ :=
    D.exists_back (γ : Matrix (Fin 2) (Fin 2) ℤ) (Gamma0_mem.1 hγ)
  obtain ⟨γ', rfl⟩ : ∃ γ' : SL(2, ℤ), (γ' : Matrix (Fin 2) (Fin 2) ℤ) = B' :=
    ⟨⟨B', by rw [hdet, Matrix.SpecialLinearGroup.det_coe]⟩, rfl⟩
  refine ⟨γ', Gamma0_mem.2 h10, h00, h11, ?_⟩
  rw [gl, Hecke.mapGL_mul_toGL, Hecke.toGL_mul_mapGL]
  exact Hecke.toGL_congr _ _ hB

/-- `γ ∈ Γ₀(M)`: `A γ = γ' A` with `γ' ∈ Γ₀(M)`. -/
lemma exists_fwd_SL {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) :
    ∃ γ' : SL(2, ℤ), γ' ∈ Gamma0 M ∧
      ((γ' 0 0 : ℤ) : ZMod M) = D.eQ' * ((γ 0 0 : ℤ) : ZMod M) + (1 - D.eQ') * ((γ 1 1 : ℤ) : ZMod M) ∧
      ((γ' 1 1 : ℤ) : ZMod M) = (1 - D.eQ') * ((γ 0 0 : ℤ) : ZMod M) + D.eQ' * ((γ 1 1 : ℤ) : ZMod M) ∧
      D.gl * mapGL ℝ γ = mapGL ℝ γ' * D.gl := by
  obtain ⟨B', hB, hdet, h10, h00, h11⟩ :=
    D.exists_fwd (γ : Matrix (Fin 2) (Fin 2) ℤ) (Gamma0_mem.1 hγ)
  obtain ⟨γ', rfl⟩ : ∃ γ' : SL(2, ℤ), (γ' : Matrix (Fin 2) (Fin 2) ℤ) = B' :=
    ⟨⟨B', by rw [hdet, Matrix.SpecialLinearGroup.det_coe]⟩, rfl⟩
  refine ⟨γ', Gamma0_mem.2 h10, h00, h11, ?_⟩
  rw [gl, Hecke.mapGL_mul_toGL, Hecke.toGL_mul_mapGL]
  exact Hecke.toGL_congr _ _ hB

lemma exists_back_Gamma1 {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma1 M) :
    ∃ γ' : SL(2, ℤ), γ' ∈ Gamma1 M ∧ mapGL ℝ γ * D.gl = D.gl * mapGL ℝ γ' := by
  obtain ⟨h00, h11, -⟩ := (Gamma1_mem M γ).1 hγ
  obtain ⟨γ', h0, e00, e11, he⟩ := D.exists_back_SL (Gamma1_in_Gamma0 M hγ)
  refine ⟨γ', (Gamma1_mem M γ').2 ⟨?_, ?_, Gamma0_mem.1 h0⟩, he⟩
  · rw [e00, h00, h11]; ring
  · rw [e11, h00, h11]; ring

lemma exists_fwd_Gamma1 {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma1 M) :
    ∃ γ' : SL(2, ℤ), γ' ∈ Gamma1 M ∧ D.gl * mapGL ℝ γ = mapGL ℝ γ' * D.gl := by
  obtain ⟨h00, h11, -⟩ := (Gamma1_mem M γ).1 hγ
  obtain ⟨γ', h0, e00, e11, he⟩ := D.exists_fwd_SL (Gamma1_in_Gamma0 M hγ)
  refine ⟨γ', (Gamma1_mem M γ').2 ⟨?_, ?_, Gamma0_mem.1 h0⟩, he⟩
  · rw [e00, h00, h11]; ring
  · rw [e11, h00, h11]; ring

end SLconj

end ALData

/-! ### A3. Units: the twist `u ↦ (1 - e) u⁻¹ + e u` and the `Q`-part `u ↦ (1 - e) u + e` -/

section units

variable {N : ℕ} (e : ZMod N) (he : e * (1 - e) = 0)

/-- `u ↦ (1 - e) u⁻¹ + e u` (`≡ u⁻¹` on the `Q`-part, `≡ u` on the `Q'`-part). -/
def twistUnit (u : (ZMod N)ˣ) : (ZMod N)ˣ where
  val := (1 - e) * ((u⁻¹ : (ZMod N)ˣ) : ZMod N) + e * (u : ZMod N)
  inv := (1 - e) * (u : ZMod N) + e * ((u⁻¹ : (ZMod N)ˣ) : ZMod N)
  val_inv := by
    linear_combination ((1 - e) ^ 2 + e ^ 2) * Units.inv_mul u +
      ((u : ZMod N) ^ 2 + ((u⁻¹ : (ZMod N)ˣ) : ZMod N) ^ 2 - 2) * he
  inv_val := by
    linear_combination ((1 - e) ^ 2 + e ^ 2) * Units.inv_mul u +
      ((u : ZMod N) ^ 2 + ((u⁻¹ : (ZMod N)ˣ) : ZMod N) ^ 2 - 2) * he

lemma coe_twistUnit (u : (ZMod N)ˣ) :
    (twistUnit e he u : ZMod N) = (1 - e) * ((u⁻¹ : (ZMod N)ˣ) : ZMod N) + e * (u : ZMod N) := rfl

lemma coe_twistUnit_inv (u : (ZMod N)ˣ) :
    (((twistUnit e he u)⁻¹ : (ZMod N)ˣ) : ZMod N) =
      (1 - e) * (u : ZMod N) + e * ((u⁻¹ : (ZMod N)ˣ) : ZMod N) := rfl

/-- The twist as a group homomorphism. -/
def twistHom : (ZMod N)ˣ →* (ZMod N)ˣ where
  toFun := twistUnit e he
  map_one' := Units.ext (by rw [coe_twistUnit]; simp)
  map_mul' u v := Units.ext (by
    rw [Units.val_mul, coe_twistUnit, coe_twistUnit, coe_twistUnit, mul_inv, Units.val_mul,
      Units.val_mul]
    linear_combination (((u⁻¹ : (ZMod N)ˣ) : ZMod N) * ((v⁻¹ : (ZMod N)ˣ) : ZMod N) +
      (u : ZMod N) * (v : ZMod N) - ((u⁻¹ : (ZMod N)ˣ) : ZMod N) * (v : ZMod N) -
      (u : ZMod N) * ((v⁻¹ : (ZMod N)ˣ) : ZMod N)) * he)

lemma twistUnit_twistUnit (u : (ZMod N)ˣ) : twistUnit e he (twistUnit e he u) = u := by
  ext
  rw [coe_twistUnit, coe_twistUnit_inv, coe_twistUnit]
  linear_combination (2 * ((u⁻¹ : (ZMod N)ˣ) : ZMod N) - 2 * (u : ZMod N)) * he

/-- `u ↦ (1 - e) u + e` (`≡ u` on the `Q`-part, `≡ 1` on the `Q'`-part). -/
def partUnit (u : (ZMod N)ˣ) : (ZMod N)ˣ where
  val := (1 - e) * (u : ZMod N) + e
  inv := (1 - e) * ((u⁻¹ : (ZMod N)ˣ) : ZMod N) + e
  val_inv := by
    linear_combination (1 - e) ^ 2 * Units.mul_inv u +
      ((u : ZMod N) + ((u⁻¹ : (ZMod N)ˣ) : ZMod N) - 2) * he
  inv_val := by
    linear_combination (1 - e) ^ 2 * Units.mul_inv u +
      ((u : ZMod N) + ((u⁻¹ : (ZMod N)ˣ) : ZMod N) - 2) * he

lemma coe_partUnit (u : (ZMod N)ˣ) : (partUnit e he u : ZMod N) = (1 - e) * (u : ZMod N) + e := rfl

lemma coe_partUnit_inv (u : (ZMod N)ˣ) :
    (((partUnit e he u)⁻¹ : (ZMod N)ˣ) : ZMod N) = (1 - e) * ((u⁻¹ : (ZMod N)ˣ) : ZMod N) + e := rfl

/-- The `Q`-part as a group homomorphism. -/
def partHom : (ZMod N)ˣ →* (ZMod N)ˣ where
  toFun := partUnit e he
  map_one' := Units.ext (by rw [coe_partUnit]; simp)
  map_mul' u v := Units.ext (by
    rw [Units.val_mul, coe_partUnit, coe_partUnit, coe_partUnit, Units.val_mul]
    linear_combination ((u : ZMod N) * (v : ZMod N) + 1 - u - v) * he)

/-- `twist ((part u)⁻¹) = part u`. -/
lemma twistUnit_partUnit_inv (u : (ZMod N)ˣ) :
    twistUnit e he (partUnit e he u)⁻¹ = partUnit e he u := by
  ext
  rw [coe_twistUnit, inv_inv, coe_partUnit_inv, coe_partUnit]
  linear_combination (((u⁻¹ : (ZMod N)ˣ) : ZMod N) - (u : ZMod N)) * he

end units

namespace ALData

/-- The twist attached to the data: `≡ u⁻¹ mod Q`, `≡ u mod Q'`. -/
def twist (D : ALData M Q) : (ZMod M)ˣ →* (ZMod M)ˣ := twistHom D.eQ' D.eQ'_mul_one_sub

/-- The `Q`-part: `≡ u mod Q`, `≡ 1 mod Q'`. -/
def partQ (D : ALData M Q) : (ZMod M)ˣ →* (ZMod M)ˣ := partHom D.eQ' D.eQ'_mul_one_sub

lemma coe_twist (D : ALData M Q) (u : (ZMod M)ˣ) :
    (D.twist u : ZMod M) = (1 - D.eQ') * ((u⁻¹ : (ZMod M)ˣ) : ZMod M) + D.eQ' * (u : ZMod M) := rfl

lemma coe_partQ (D : ALData M Q) (u : (ZMod M)ˣ) :
    (D.partQ u : ZMod M) = (1 - D.eQ') * (u : ZMod M) + D.eQ' := rfl

lemma twist_twist (D : ALData M Q) (u : (ZMod M)ˣ) : D.twist (D.twist u) = u :=
  twistUnit_twistUnit D.eQ' D.eQ'_mul_one_sub u

lemma twist_partQ_inv (D : ALData M Q) (u : (ZMod M)ˣ) : D.twist (D.partQ u)⁻¹ = D.partQ u :=
  twistUnit_partUnit_inv D.eQ' D.eQ'_mul_one_sub u

/-- The character `χ ∘ twist` (`= χ̄_Q · χ_{Q'}`). -/
def twistChar (D : ALData M Q) (χ : DirichletCharacter ℂ M) : DirichletCharacter ℂ M :=
  MulChar.ofUnitHom (χ.toUnitHom.comp D.twist)

lemma twistChar_apply (D : ALData M Q) (χ : DirichletCharacter ℂ M) (u : (ZMod M)ˣ) :
    D.twistChar χ (u : ZMod M) = χ (D.twist u : ZMod M) := by
  rw [twistChar, MulChar.ofUnitHom_coe, MonoidHom.comp_apply, MulChar.coe_toUnitHom]

/-! ### Data: Fricke, and existence for `Q ∥ M` -/

/-- The Fricke data: `[[0, -1], [M, 0]]`. -/
def frickeD (M : ℕ) : ALData M M := ⟨1, 0, -1, 1, 0, mul_one M, by norm_num⟩

lemma frickeD_mat (M : ℕ) : (frickeD M).mat = !![0, -1; (M : ℤ), 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [frickeD, mat]

lemma frickeD_eQ' (M : ℕ) : (frickeD M).eQ' = 0 := by simp [eQ', frickeD]

lemma frickeD_twist (M : ℕ) (u : (ZMod M)ˣ) : (frickeD M).twist u = u⁻¹ :=
  Units.ext (by rw [coe_twist, frickeD_eQ']; ring)

/-- Data for `Q ∥ M`: `z = -1`, `w = 1`, `Q x + Q' y = 1`. -/
noncomputable def ofCoprime {Q' : ℕ} (hM : Q * Q' = M) (hc : Nat.Coprime Q Q') : ALData M Q :=
  ⟨Q', (Nat.isCoprime_iff_coprime.2 hc).choose, (Nat.isCoprime_iff_coprime.2 hc).choose_spec.choose,
    -1, 1, hM, by linear_combination (Nat.isCoprime_iff_coprime.2 hc).choose_spec.choose_spec⟩

/-! ### The operator `W` on `S_k(Γ₁(M))` -/

section op

variable [NeZero M] (D : ALData M Q)

lemma G1_le_conj_gl : G1 M ≤ toConjAct D.gl⁻¹ • G1 M := by
  rintro _ ⟨x, hx, rfl⟩
  rw [map_inv, Subgroup.mem_inv_pointwise_smul_iff, toConjAct_smul]
  obtain ⟨δ, hδ, he⟩ := D.exists_fwd_Gamma1 hx
  exact ⟨δ, hδ, by rw [he, mul_inv_cancel_right]⟩

/-- `f ↦ f ∣[k] A` as a cusp form on `Γ₁(M)`. -/
def alCF (k : ℤ) (f : S1 M k) : S1 M k :=
  Level.restrictCF D.G1_le_conj_gl (CuspForm.translate f D.gl)

@[simp] lemma coe_alCF (k : ℤ) (f : S1 M k) : ⇑(D.alCF k f) = ⇑f ∣[k] D.gl := rfl

/-- **The Atkin-Lehner operator** `W f = f ∣[k] [[Q x, y], [M z, Q w]]` on `S_k(Γ₁(M))`. -/
def alOp (k : ℤ) : S1 M k →ₗ[ℂ] S1 M k where
  toFun := D.alCF k
  map_add' f g := DFunLike.coe_injective (by
    simp only [coe_alCF, FunLike.coe_add, SlashAction.add_slash])
  map_smul' c f := DFunLike.coe_injective (by
    simp only [coe_alCF, FunLike.coe_smul, RingHom.id_apply]
    exact Hecke.smul_slash_of_det_pos k _ D.gl_det_pos c _)

lemma coe_alOp (k : ℤ) (f : S1 M k) : ⇑(D.alOp k f) = ⇑f ∣[k] D.gl := rfl

/-- **(1)** `W ⟨u⟩ = ⟨twist u⟩ W`. -/
theorem alOp_diamond (k : ℤ) (u : (ZMod M)ˣ) (f : S1 M k) :
    D.alOp k (diamond k u f) = diamond k (D.twist u) (D.alOp k f) := by
  apply DFunLike.coe_injective
  obtain ⟨σ, hσ⟩ := unitMap_surjective (M := M) u
  have hσ11 : (((σ : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) = u := by rw [← hσ]; rfl
  have hσ00 : (((σ : SL(2, ℤ)) 0 0 : ℤ) : ZMod M) = ((u⁻¹ : (ZMod M)ˣ) : ZMod M) :=
    Units.eq_inv_of_mul_eq_one_right (by rw [← hσ11]; exact Gamma0_det_cast σ.2)
  obtain ⟨σ', h0, -, h11, he⟩ := D.exists_back_SL σ.2
  have key : (⇑f ∣[k] mapGL ℝ (σ : SL(2, ℤ))) ∣[k] D.gl = (⇑f ∣[k] D.gl) ∣[k] mapGL ℝ σ' := by
    rw [← SlashAction.slash_mul, ← SlashAction.slash_mul, he]
  rw [coe_alOp, coe_diamond_of_mem k σ.2 u hσ11.symm f,
    coe_diamond_of_mem k h0 (D.twist u) (by rw [h11, hσ00, hσ11, coe_twist]) _, coe_alOp]
  exact key

/-- **(2)** `W` maps `S_k(M, χ)` to `S_k(M, χ ∘ twist)` (`χ ∘ twist = χ̄_Q χ_{Q'}`). -/
theorem alOp_mem_chiSubspace (k : ℤ) {χ : DirichletCharacter ℂ M} {f : S1 M k}
    (hf : f ∈ chiSubspace k χ) : D.alOp k f ∈ chiSubspace k (D.twistChar χ) := by
  rw [mem_chiSubspace_iff_diamond] at hf ⊢
  intro v
  have h := D.alOp_diamond k (D.twist v) f
  rw [D.twist_twist, hf, map_smul] at h
  rw [← h, twistChar_apply]

/-! #### (3) `W² = Q^(k-2) ⟨d⟩` -/

/-- `A² = Q · sqMat`. -/
def sqMat (D : ALData M Q) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![(Q : ℤ) * D.x ^ 2 + (D.Q' : ℤ) * D.y * D.z, D.y * (D.x + D.w);
     (M : ℤ) * (D.z * (D.x + D.w)), (D.Q' : ℤ) * D.y * D.z + (Q : ℤ) * D.w ^ 2]

lemma det_sqMat : D.sqMat.det = 1 := by
  obtain ⟨Q', x, y, z, w, hM, hdet⟩ := D
  subst hM
  simp only [sqMat, Matrix.det_fin_two_of]
  push_cast
  linear_combination ((Q : ℤ) * x * w - (Q' : ℤ) * y * z + 1) * hdet

/-- `sqMat ∈ SL(2, ℤ)`. -/
def sqSL : SL(2, ℤ) := ⟨D.sqMat, D.det_sqMat⟩

lemma sqSL_mem : D.sqSL ∈ Gamma0 M := by
  rw [Gamma0_mem]
  show (((M : ℤ) * (D.z * (D.x + D.w)) : ℤ) : ZMod M) = 0
  push_cast
  rw [ZMod.natCast_self, zero_mul]

lemma gl_mul_gl : D.gl * D.gl =
    mapGL ℝ D.sqSL * Matrix.GeneralLinearGroup.scalar (Fin 2) D.gl.det := by
  have hdet := D.gl_det
  have hsq : ∀ i j : Fin 2,
      ((mapGL ℝ D.sqSL : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j = (D.sqMat i j : ℝ) :=
    fun i j => by rw [mapGL_coe_matrix]; rfl
  have hm : D.mat * D.mat = (Q : ℤ) • D.sqMat := by
    obtain ⟨Q', x, y, z, w, hM, hdet'⟩ := D
    subst hM
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [mat, sqMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
        Matrix.head_cons, Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.smul_apply, smul_eq_mul] <;>
      push_cast <;> ring
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  have hij := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℤ => (A i j : ℝ)) hm
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul] at hij
  push_cast at hij
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul,
    Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.mul_diagonal, hsq,
    Matrix.mul_apply, Fin.sum_univ_two]
  simp only [gl_apply]
  rw [hdet]
  linear_combination hij

/-- **(3)** `W (W f) = Q^(k-2) ⟨d_A⟩ f` with `d_A = Q' y z + Q w² mod M`. -/
theorem alOp_alOp (k : ℤ) (f : S1 M k) :
    D.alOp k (D.alOp k f) = ((Q : ℂ) ^ (k - 2)) • diamond k (unitMap M ⟨D.sqSL, D.sqSL_mem⟩) f := by
  apply DFunLike.coe_injective
  rw [coe_alOp, coe_alOp, ← SlashAction.slash_mul, gl_mul_gl, SlashAction.slash_mul,
    Adjoint.slash_scalar k _ D.gl_det_pos, D.gl_det, FunLike.coe_smul, diamond_unitMap, coe_slashG0]
  push_cast
  rfl

lemma frickeD_unit : unitMap M ⟨(frickeD M).sqSL, (frickeD M).sqSL_mem⟩ = -1 :=
  Units.ext (by rw [coe_unitMap]; simp [sqSL, sqMat, frickeD])

/-- **Fricke**: `W_M (W_M f) = (-1)^k M^(k-2) f`. -/
theorem frickeD_alOp_alOp (k : ℤ) (f : S1 M k) :
    (frickeD M).alOp k ((frickeD M).alOp k f) = (((-1 : ℂ) ^ k) * (M : ℂ) ^ (k - 2)) • f := by
  rw [alOp_alOp, frickeD_unit, diamond_neg_one, smul_smul, mul_comm]

/-! #### (4) Adjoint and unitarity -/

lemma adjD_gl_coe :
    ((D.adjD.gl : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      (D.gl : Matrix (Fin 2) (Fin 2) ℝ).adjugate := by
  rw [Matrix.adjugate_fin_two]
  ext i j
  rw [gl_apply, adjD_mat, Matrix.adjugate_fin_two]
  fin_cases i <;> fin_cases j <;> simp [gl_apply]

lemma gl_coe_adjD :
    ((D.gl : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      (D.adjD.gl : Matrix (Fin 2) (Fin 2) ℝ).adjugate := by
  rw [Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gl_apply, adjD_mat, Matrix.adjugate_fin_two]

lemma interConj_gl : Adjoint.interConj (Gamma1 M) D.gl = Gamma1 M := by
  ext δ
  refine ⟨fun h => h.1, fun h => ?_⟩
  obtain ⟨δ', hδ', he⟩ := D.exists_fwd_Gamma1 h
  exact Adjoint.mem_interConj_of h hδ' he

/-- **(4)** `⟪W f, g⟫ = ⟪f, W' g⟫` with `W'` the operator of the adjugate data. -/
theorem peterssonInner_alOp (k : ℤ) (f g : S1 M k) :
    peterssonInner (Gamma1 M) k ⇑(D.alOp k f) ⇑g =
      peterssonInner (Gamma1 M) k ⇑f ⇑(D.adjD.alOp k g) := by
  have h := Adjoint.peterssonInner_slash_adj (Γ := Gamma1 M) (k := k) D.gl D.adjD.gl D.gl_det_pos
    D.adjD_gl_coe (F := ⇑f) (G := ⇑g) (fun δ hδ => slash_Gamma1 k f hδ)
    (fun δ hδ => slash_Gamma1 k g hδ)
  rw [D.interConj_gl, D.adjD.interConj_gl] at h
  exact h

/-- `W' (W f) = Q^(k-2) f`. -/
theorem alOp_adjD_alOp (k : ℤ) (f : S1 M k) :
    D.adjD.alOp k (D.alOp k f) = ((Q : ℂ) ^ (k - 2)) • f := by
  apply DFunLike.coe_injective
  rw [coe_alOp, coe_alOp, ← SlashAction.slash_mul, Adjoint.adj_eq D.adjD_gl_coe,
    mul_inv_cancel_left, Adjoint.slash_scalar k _ D.gl_det_pos, D.gl_det, FunLike.coe_smul]
  push_cast
  rfl

/-- `W (W' f) = Q^(k-2) f`. -/
theorem alOp_alOp_adjD (k : ℤ) (f : S1 M k) :
    D.alOp k (D.adjD.alOp k f) = ((Q : ℂ) ^ (k - 2)) • f := by
  apply DFunLike.coe_injective
  rw [coe_alOp, coe_alOp, ← SlashAction.slash_mul, Adjoint.adj_eq D.gl_coe_adjD,
    mul_inv_cancel_left, Adjoint.slash_scalar k _ D.adjD.gl_det_pos, D.adjD.gl_det, FunLike.coe_smul]
  push_cast
  rfl

/-- **(4')** `W` is unitary up to the scalar `Q^(k-2)`: `⟪W f, W g⟫ = Q^(k-2) ⟪f, g⟫`. -/
theorem peterssonInner_alOp_alOp (k : ℤ) (f g : S1 M k) :
    peterssonInner (Gamma1 M) k ⇑(D.alOp k f) ⇑(D.alOp k g) =
      ((Q : ℂ) ^ (k - 2)) * peterssonInner (Gamma1 M) k ⇑f ⇑g := by
  rw [peterssonInner_alOp, alOp_adjD_alOp, peterssonInner_smul_right]

end op

end ALData

end RP.AtkinLehner


