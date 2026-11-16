-- Prove2me | Definitions.Def_QuarticGap_Supplement_Pmat
-- name    : QuarticGap_Supplement_Pmat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:51:18.95901+00:00
-- url     : https://prove2.me/theorems/eb7a0ca8-e834-41db-8afb-9bf3763f4bcf
-- title:
--   The positive-definite family (18): $T_W$, $P_W = I - tT_W$, $b$, $\psi_0$, padding and access
-- statement:
--   Fix a rational $t$. For a power of four $n = 4^\ell$ and a sign matrix $W \in \{\pm1\}^{n\times n}$, with $R = W/\sqrt n$, the normalized Walsh–Hadamard matrix $H$ and the uniform unit vector $u$, the $3n\times 3n$ matrices of (18) are
--   $$
--   T_W = \begin{pmatrix} 0 & R^{\mathsf T} & 0\\ R & 0 & H\\ 0 & H & 0\end{pmatrix},\qquad P_W = I - tT_W,\qquad b = \begin{pmatrix} u\\ 0\\ 0\end{pmatrix}.
--   $$
--   Their entries are rational because $\sqrt n = 2^\ell$. The item also defines
--
--   1. the target $p_{P_W^{-1}b}$ of Theorem 5.3;
--   2. the initial vector $\psi_0 = (u,0,u)/\sqrt2$ and the evolved vector $e^{-iP_W}\psi_0 \in \mathbb C^{3n}$ of Theorem 5.6 (matrix exponential);
--   3. the classical input operations $\mathrm{SQ}(P_W)$ of Definition 2.1 on the $3n\times3n$ matrix;
--   4. zero padding of a matrix or vector to the $4n$ coordinates of a register with two block wires and $2\ell$ data wires (Remark 4.4: "the same padding applies to the tasks of Section 5"), and the quantum input operations of Definition 2.2 for the padded $P_W$, with the exact rational entry encoding (a sign bit, then numerator and denominator in $2\ell + 2 + \mathrm{size}(|\mathrm{num}\,t|\cdot \mathrm{den}\,t)$ bits each).
--
--   This is the symmetric family on which the lower bounds for positive-definite systems, matrix functions and Hamiltonian evolution are proved.
--
--   **Formalization Note** A coordinate is a block in $\{0,1,2\}$ and a position in $\{0,1\}^{2\ell}$. In the padded register the fourth block is zero padding; padded rows and columns are zero, have sampling weight zero, and the targets vanish on them.
-- source:
--   Chakrabarti, Herman, Kim, Ozgul, The Quartic Gap Between Quantum and Dequantized Algorithms for Linear Algebra Is Tight, arXiv:2610.42069 (file sha256 9f68aaf9…), (18), p.33; Theorem 5.6, p.37; Definitions 2.1–2.2, pp.15–16; Remark 4.4, p.32

import Mathlib
import Definitions.Def_QuarticGap_Ahat

open QAlgorithms

namespace QuarticGap.Supplement

/-- The `3n` coordinates of the positive-definite family (18): a block in `{0, 1, 2}` (the source's
first, second and third blocks) and a position in `{0,1}^k`, `n = 2^k = 4^ℓ`
(arXiv:2610.42069 (file sha256 9f68aaf9…), (18), p.33). -/
abbrev Ix3 (ℓ : ℕ) := Fin 3 × Bits ℓ

/-- The entries of `T_W` of (18) (arXiv:2610.42069, p.33), the symmetric block matrix
`[[0, Rᵀ, 0], [R, 0, H], [0, H, 0]]` with `R = W/√n` and `H` the normalized Walsh–Hadamard matrix.
They are rational because `√n = 2^ℓ`: entry (block 1 row `a`, block 0 column `b`) is `W_ab/√n`,
(block 0 row `a`, block 1 column `b`) is `(Rᵀ)_ab = W_ba/√n`, and the two `H` blocks have
entries `h_ab/√n`. -/
def TQ {ℓ : ℕ} (W : SignMat ℓ) (i j : Ix3 ℓ) : ℚ :=
  match i.1.val, j.1.val with
  | 0, 1 => ((W j.2 i.2 : ℤ) : ℚ) / 2 ^ ℓ
  | 1, 0 => ((W i.2 j.2 : ℤ) : ℚ) / 2 ^ ℓ
  | 1, 2 => ((hSign i.2 j.2 : ℤ) : ℚ) / 2 ^ ℓ
  | 2, 1 => ((hSign i.2 j.2 : ℤ) : ℚ) / 2 ^ ℓ
  | _, _ => 0

/-- `T_W` as a real matrix (arXiv:2610.42069, (18), p.33). -/
noncomputable def Tmat {ℓ : ℕ} (W : SignMat ℓ) : Matrix (Ix3 ℓ) (Ix3 ℓ) ℝ :=
  Matrix.of fun i j => (TQ W i j : ℝ)

/-- The entries of `P_W = I − tT_W` (arXiv:2610.42069, (18), p.33), rational for rational `t`. -/
def PQ {ℓ : ℕ} (t : ℚ) (W : SignMat ℓ) : Matrix (Ix3 ℓ) (Ix3 ℓ) ℚ :=
  Matrix.of fun i j => (if i = j then 1 else 0) - t * TQ W i j

/-- `P_W = I − tT_W` as a real matrix (arXiv:2610.42069, (18), p.33). -/
noncomputable def Pmat {ℓ : ℕ} (t : ℚ) (W : SignMat ℓ) : Matrix (Ix3 ℓ) (Ix3 ℓ) ℝ :=
  (PQ t W).map (fun q : ℚ => (q : ℝ))

/-- The right-hand side `b = (u, 0, 0)` of (18) (arXiv:2610.42069, p.33), a fixed unit vector. -/
noncomputable def bVec (ℓ : ℕ) (i : Ix3 ℓ) : ℝ :=
  if i.1 = 0 then uVec ℓ i.2 else 0

/-- The target `p_{P_W⁻¹b}` of Theorem 5.3 (arXiv:2610.42069, p.34). -/
noncomputable def linTarget {ℓ : ℕ} (t : ℚ) (W : SignMat ℓ) : Ix3 ℓ → ℝ :=
  lenSqDist ((Pmat t W)⁻¹.mulVec (bVec ℓ))

/-- The initial vector `ψ₀ = (u, 0, u)/√2` of Theorem 5.6 (arXiv:2610.42069, p.37). -/
noncomputable def psi0 (ℓ : ℕ) (i : Ix3 ℓ) : ℝ :=
  if i.1 = 1 then 0 else uVec ℓ i.2 / Real.sqrt 2

/-- The evolved vector `e^{−iP_W} ψ₀ ∈ ℂ^{3n}` of Theorem 5.6 (arXiv:2610.42069, p.37), with the
matrix exponential of `−i P_W`. -/
noncomputable def hamVec {ℓ : ℕ} (t : ℚ) (W : SignMat ℓ) : Ix3 ℓ → ℂ :=
  (NormedSpace.exp ((-Complex.I) • (Pmat t W).map (fun x : ℝ => (x : ℂ)))).mulVec
    (fun i => (psi0 ℓ i : ℂ))

/-- `SQ(P_W)` (arXiv:2610.42069, Definition 2.1, p.15) on the `3n × 3n` matrix itself. `P_W` has a
nonzero diagonal, so it has no zero row or column and the fixed index `default` is never returned. -/
noncomputable def pRespond {ℓ : ℕ} (t : ℚ) (W : SignMat ℓ) :
    SQQuery (Ix3 ℓ) (Ix3 ℓ) → PMF (SQAns (Ix3 ℓ) (Ix3 ℓ)) :=
  sqRespond (Pmat t W) default default

/-- Reading a coordinate of the `4n`-dimensional register `Idx ℓ` (two block wires, then `2ℓ` data
wires) as a coordinate of the `3n`-dimensional family: blocks `0, 1, 2` are the three blocks of (18),
and block `3` is zero padding (`none`). -/
def dec3 {ℓ : ℕ} (i : Idx ℓ) : Option (Ix3 ℓ) :=
  if h : blk i < 3 then some (⟨blk i, h⟩, dat i) else none

/-- Zero padding of a square matrix with index set `ι` to the register `Idx ℓ`, along a decoding
`dec` of register coordinates: rows and columns that decode to `none` are zero
(arXiv:2610.42069, Remark 4.4, p.32: "The same padding applies to the tasks of Section 5"). -/
def padMat {ℓ : ℕ} {ι R : Type*} [Zero R] (dec : Idx ℓ → Option ι) (A : Matrix ι ι R) :
    Matrix (Idx ℓ) (Idx ℓ) R :=
  Matrix.of fun i j =>
    match dec i, dec j with
    | some a, some b => A a b
    | _, _ => 0

/-- Zero padding of a vector with index set `ι` to the register `Idx ℓ`. -/
def padVec {ℓ : ℕ} {ι R : Type*} [Zero R] (dec : Idx ℓ → Option ι) (x : ι → R) : Idx ℓ → R :=
  fun i =>
    match dec i with
    | some a => x a
    | none => 0

/-- A bit count for the numerators and denominators of the entries of the §5 matrices: every
numerator and denominator is at most `2·4^ℓ + 1` or divides `|num t|·den t·2^ℓ`, so it fits in
`2ℓ + 2 + size(|num t|·den t)` bits; `O(log n)` bits for fixed `t` (arXiv:2610.42069, §2.4, p.17). -/
def supBits (ℓ : ℕ) (t : ℚ) : ℕ :=
  2 * ℓ + 2 + Nat.size (t.num.natAbs * t.den)

/-- Output width of the reversible entry query of the padded §5 matrices: a sign bit, then numerator
and denominator in `supBits ℓ t` bits each (the published `ratEnc`). -/
def supWidth (ℓ : ℕ) (t : ℚ) : ℕ :=
  1 + (supBits ℓ t + supBits ℓ t)

/-- The register sizes of the five quantum input operations of a padded §5 matrix on `2 + 2ℓ` row
and column wires (arXiv:2610.42069, Definition 2.2, pp.15–16). -/
def supArity (ℓ : ℕ) (t : ℚ) : Fin 5 → ℕ :=
  coherentArity (2 + 2 * ℓ) (2 + 2 * ℓ) (supWidth ℓ t)

/-- `orc` is a choice of the quantum input operations (Definition 2.2, pp.15–16) of `P_W`, zero padded
to `4n × 4n` (Remark 4.4, p.32), with the exact rational entry encoding `ratEnc`. -/
def IsPAccess {ℓ : ℕ} (t : ℚ) (W : SignMat ℓ)
    (orc : (k : Fin 5) → Matrix (Qubits (supArity ℓ t k)) (Qubits (supArity ℓ t k)) ℂ) : Prop :=
  IsCoherentAccess (padMat dec3 (Pmat t W))
    (fun i j => ratEnc (supBits ℓ t) (padMat dec3 (PQ t W) i j)) orc

end QuarticGap.Supplement


