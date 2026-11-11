-- Prove2me | Definitions.Def_InfoLossLAR_WorstCase_Rounding
-- name    : InfoLossLAR_WorstCase_Rounding
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T02:02:10.648647+00:00
-- url     : https://prove2.me/theorems/ca652b09-bbaa-4851-94cc-aab89b8b75f5
-- title:
--   Rounding matrices with Smith data, algebraic rounding $\mathrm{AR}_T$, quotient coordinates $P$, directions $J$, the label $f_T$
-- statement:
--   Let $q$ be an odd prime, $\mathbb F_q=\mathbb Z/q\mathbb Z$, $d\ge1$, $0\le r\le d$ and $\ell=d-r$. For $x\in\mathbb F_q^d$ the **canonical lift** $[x]_q\in\{0,\dots,q-1\}^d\subseteq\mathbb Z^d$ (Definition 2.7); the **carry** of an integer $k$ is $\lfloor k/q\rfloor$, also for $k<0$. The **image lattice** of $T\in\mathbb Z^{d\times d}$ is $\mathcal L(T)=T\mathbb Z^d$ and the **zero-sum lattice** is $A_{m-1}=\{z\in\mathbb Z^m:\mathbf 1^\top z=0\}$ (Definition 2.2).
--
--   $T$ is a **rounding matrix of modular rank $r$** (Definition 2.3) if there are unimodular $U,V\in\mathbb Z^{d\times d}$ with
--   $$UTV=\operatorname{diag}(I_r,\,qI_\ell).$$
--   The chosen $U,V$ are public data. With $E=\binom{0_{r\times\ell}}{I_\ell}$, the **quotient coordinates** are $P=E^\top U$ (Definition 3.2), the **rounding directions** $J=VE\bmod q$ (Definition 3.3), **algebraic rounding** is $\mathrm{AR}_T(x)=\lfloor Tx/q\rfloor$ computed over $\mathbb Q$ (Definition 3.1), and the **encoded label** is (Definition 3.4)
--   $$f_T(x)=P\,\mathrm{AR}_T([x]_q)\bmod q\in\mathbb F_q^\ell,\qquad x\in\mathbb F_q^d,$$
--   with zero fiber $\mathcal F_{T,0}=f_T^{-1}(0)$.
--
--   **Formalization Note.** Indices are $0$-based (`Fin d`); $\ell=d-r$ is natural subtraction, with $r\le d$ part of the Smith data. `SmithData q r d T` carries $U,V$; `IsRoundingMatrix` asserts that some exist.
-- source:
--   Chen Qian, Information Loss Is All You Need: TC⁰ Pseudorandomness from Worst-Case Lattices, arXiv:2611.05136 (held version, sha256 2ebdfbf3…), p. 13 Definitions 2.1–2.3, p. 16 Definition 2.7, pp. 18–19 Definitions 3.1–3.4, p. 21 (F_{T,0})

import Mathlib

set_option autoImplicit false

namespace InfoLossLAR.WorstCase

/-!
# Rounding matrices, algebraic rounding and the encoded label function

Chen Qian, *Information Loss Is All You Need: TC⁰ Pseudorandomness from Worst-Case Lattices*,
arXiv:2611.05136 (held version, sha256 2ebdfbf3…), p. 13 (Definitions 2.1–2.3), p. 16
(Definition 2.7), pp. 18–19 (Definitions 3.1–3.4), p. 21 (the zero fiber `F_{T,0}`).

Conventions.
* Vectors are functions `Fin d → _`, indices `0, …, d − 1` (the paper's `1, …, d`); matrices act
  on columns (`Matrix.mulVec`).
* `𝔽_q = ZMod q`. The canonical lift `[x]_q` takes each entry to its representative in
  `{0, …, q − 1}` (`ZMod.val`).
* Floors are taken over `ℚ`, exactly as the paper's "computed over `ℚ`": `⌊k / q⌋` for an integer
  `k` is the integer quotient, also for `k < 0` (Definition 2.7).
* `ℓ = d − r` (natural subtraction; a rounding matrix has `r ≤ d`, which is part of the data).
-/

/-- Definition 2.7 (p. 16): the canonical integer lift `[x]_q ∈ ℤ^d` of `x ∈ 𝔽_q^d`, with
entries in `{0, …, q − 1}`. -/
def lift {q d : ℕ} (x : Fin d → ZMod q) : Fin d → ℤ := fun i => ((x i).val : ℤ)

/-- Coordinatewise reduction `ℤ^d → 𝔽_q^d`. -/
def modq (q : ℕ) {d : ℕ} (z : Fin d → ℤ) : Fin d → ZMod q := fun i => (z i : ZMod q)

/-- Coordinatewise reduction of an integer matrix modulo `q`. -/
def matModq (q : ℕ) {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) : Matrix (Fin m) (Fin n) (ZMod q) :=
  A.map (Int.cast : ℤ → ZMod q)

/-- The carry `⌊k / q⌋` of an integer, computed over `ℚ` (Definition 2.7; §6.2), coordinatewise. -/
def carry (q : ℕ) {d : ℕ} (w : Fin d → ℤ) : Fin d → ℤ := fun i => ⌊((w i : ℚ) / (q : ℚ))⌋

/-- The image lattice `L(T) = Tℤ^d` of an integer matrix (Definition 2.1, p. 13), as a
`ℤ`-submodule of `ℤ^d`. -/
def imageLattice {d : ℕ} (T : Matrix (Fin d) (Fin d) ℤ) : Submodule ℤ (Fin d → ℤ) :=
  LinearMap.range (Matrix.mulVecLin T)

/-- Definition 2.2 (p. 13): the zero-sum integer lattice `A_{m−1} = {z ∈ ℤ^m : 1ᵀz = 0}`. -/
def zeroSumLattice (m : ℕ) : Submodule ℤ (Fin m → ℤ) where
  carrier := {z | ∑ i, z i = 0}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, Pi.add_apply, Finset.sum_add_distrib] at *
    rw [ha, hb, add_zero]
  zero_mem' := by simp
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_ofPred_eq, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum] at *
    rw [hx, mul_zero]

/-- The Smith diagonal `diag(I_r, q I_ℓ)` in dimension `d = r + ℓ`: entry `1` at the first `r`
indices and `q` at the remaining ones. -/
def smithDiag (q r d : ℕ) : Matrix (Fin d) (Fin d) ℤ :=
  Matrix.diagonal fun i => if (i : ℕ) < r then 1 else (q : ℤ)

/-- Definition 2.3 (p. 13), with the chosen Smith matrices: `T ∈ ℤ^{d×d}` is a rounding matrix
of modular rank `r` (`0 ≤ r ≤ d`, `ℓ = d − r`), witnessed by unimodular `U, V ∈ ℤ^{d×d}` with
`UTV = diag(I_r, q I_ℓ)`. The paper fixes such public `U, V` (§3, p. 18); they are part of the
data. (`q` an odd prime is a hypothesis of every statement.) -/
structure SmithData (q r d : ℕ) (T : Matrix (Fin d) (Fin d) ℤ) where
  /-- The left Smith matrix. -/
  U : Matrix (Fin d) (Fin d) ℤ
  /-- The right Smith matrix. -/
  V : Matrix (Fin d) (Fin d) ℤ
  /-- `0 ≤ r ≤ d`. -/
  r_le : r ≤ d
  /-- `U` is unimodular (`det U = ±1`). -/
  U_unimod : IsUnit U.det
  /-- `V` is unimodular (`det V = ±1`). -/
  V_unimod : IsUnit V.det
  /-- `UTV = diag(I_r, q I_ℓ)`. -/
  smith : U * T * V = smithDiag q r d

/-- Definition 2.3: `T` is a rounding matrix of modular rank `r` (some Smith matrices exist). -/
def IsRoundingMatrix (q r d : ℕ) (T : Matrix (Fin d) (Fin d) ℤ) : Prop :=
  Nonempty (SmithData q r d T)

/-- Definition 3.2 (p. 18): the coordinate embedding `E = (0_{r×ℓ}; I_ℓ) ∈ ℤ^{d×ℓ}`, `ℓ = d − r`:
column `j` is the standard basis vector at index `r + j`. -/
def embE (r d : ℕ) : Matrix (Fin d) (Fin (d - r)) ℤ :=
  fun i j => if (i : ℕ) = r + (j : ℕ) then 1 else 0

/-- Definition 3.2: the quotient coordinate matrix `P = EᵀU ∈ ℤ^{ℓ×d}` (the last `ℓ` rows of
`U`). -/
def SmithData.P {q r d : ℕ} {T : Matrix (Fin d) (Fin d) ℤ} (S : SmithData q r d T) :
    Matrix (Fin (d - r)) (Fin d) ℤ :=
  (embE r d).transpose * S.U

/-- Definition 3.3 (p. 18): the integer rounding directions `J_int = VE ∈ ℤ^{d×ℓ}`. -/
def SmithData.Jint {q r d : ℕ} {T : Matrix (Fin d) (Fin d) ℤ} (S : SmithData q r d T) :
    Matrix (Fin d) (Fin (d - r)) ℤ :=
  S.V * embE r d

/-- Definition 3.3: the rounding directions `J = J_int mod q ∈ 𝔽_q^{d×ℓ}`. -/
def SmithData.J {q r d : ℕ} {T : Matrix (Fin d) (Fin d) ℤ} (S : SmithData q r d T) :
    Matrix (Fin d) (Fin (d - r)) (ZMod q) :=
  matModq q S.Jint

/-- Definition 3.1 (p. 18): algebraic rounding `AR_T(x) = ⌊Tx / q⌋ ∈ ℤ^d` for `x ∈ ℤ^d`, the
product and division computed over `ℚ`, the floor coordinatewise. -/
def AR (q : ℕ) {d : ℕ} (T : Matrix (Fin d) (Fin d) ℤ) (x : Fin d → ℤ) : Fin d → ℤ :=
  carry q (T.mulVec x)

/-- Definition 3.4 (p. 19): the encoded label function
`f_T(x) = P · AR_T([x]_q) mod q ∈ 𝔽_q^ℓ` for `x ∈ 𝔽_q^d`. -/
def SmithData.fT {q r d : ℕ} {T : Matrix (Fin d) (Fin d) ℤ} (S : SmithData q r d T)
    (x : Fin d → ZMod q) : Fin (d - r) → ZMod q :=
  modq q (S.P.mulVec (AR q T (lift x)))

/-- §4 (p. 21): the zero fiber `F_{T,0} = f_T^{-1}(0) ⊆ 𝔽_q^d`. -/
def SmithData.zeroFiber {q r d : ℕ} {T : Matrix (Fin d) (Fin d) ℤ} (S : SmithData q r d T) :
    Set (Fin d → ZMod q) :=
  {e | S.fT e = 0}

end InfoLossLAR.WorstCase


