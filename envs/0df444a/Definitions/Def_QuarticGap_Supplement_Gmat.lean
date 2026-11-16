-- Prove2me | Definitions.Def_QuarticGap_Supplement_Gmat
-- name    : QuarticGap_Supplement_Gmat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:53:12.119402+00:00
-- url     : https://prove2.me/theorems/8e1afd6f-5234-43f8-9d63-7e740bae5a9d
-- title:
--   The family (22): $G_W = I + \varphi\varphi^{\mathsf T} + t\widetilde T_W$, its top principal component and rank-one truncation
-- statement:
--   Fix a rational $t$. Adjoin a coordinate indexed by $0$ to the three blocks of (18) and define the $(3n+1)\times(3n+1)$ matrices
--   $$
--   \widetilde T_W = 0 \oplus T_W,\qquad \varphi = \frac{1}{\sqrt2}\begin{pmatrix}1\\ u\\ 0\\ 0\end{pmatrix},\qquad G_W = I + \varphi\varphi^{\mathsf T} + t\widetilde T_W .
--   $$
--   The entries of $G_W$ are rational. The item defines
--
--   1. the largest eigenvalue $\lambda_1$ of the symmetric matrix $G_W$ (the supremum of its spectrum);
--   2. the top principal component $w_W$: a unit eigenvector for $\lambda_1$ with $\varphi^{\mathsf T}w_W > 0$;
--   3. the rank-one spectral truncation $(G_W)_{\ge 3/2}$, which keeps the eigenvalues $\ge 3/2$ with their eigenvectors and drops the rest, defined spectrally;
--   4. the two sampling tasks of Theorem 5.9: from $p_{w_W}$, and from the squared entries of row $0$ of $(G_W)_{\ge3/2}$;
--   5. $\mathrm{SQ}(G_W)$ on the $(3n+1)\times(3n+1)$ matrix, and the quantum input operations of the zero-padded $G_W$, with the adjoined coordinate at position $0$ of the fourth block of the register.
--
--   This family carries the lower bounds for principal components and rank-one truncation.
--
--   **Formalization Note** The adjoined coordinate is `none` in `Option`. $w_W$ is unique for $W$ in the promise set (Lemmas 5.7, 5.8); the definition picks one such vector when one exists and is $0$ otherwise. The truncation is the continuous functional calculus of $x \mapsto x\,\mathbf 1[x \ge 3/2]$, so its identity with $\lambda_1 w_Ww_W^{\mathsf T}$ is a theorem, not a definition.
-- source:
--   Chakrabarti, Herman, Kim, Ozgul, The Quartic Gap Between Quantum and Dequantized Algorithms for Linear Algebra Is Tight, arXiv:2610.42069 (file sha256 9f68aaf9…), (22), pp.38–39; Theorem 5.9, p.39

import Mathlib
import Definitions.Def_QuarticGap_Supplement_Pmat

open QAlgorithms

namespace QuarticGap.Supplement

/-- The `3n + 1` coordinates of the family (22): the adjoined coordinate `0` (`none`) and the three
blocks of (18) (arXiv:2610.42069 (file sha256 9f68aaf9…), (22), p.38). -/
abbrev IxG (ℓ : ℕ) := Option (Ix3 ℓ)

/-- `√2 φ` for `φ = (1, u, 0, 0)/√2` of (22) (arXiv:2610.42069, p.38): `1` at the adjoined
coordinate, `u_a = 1/√n` on the first block, `0` elsewhere. Rational because `√n = 2^ℓ`. -/
def phiQ {ℓ : ℕ} : IxG ℓ → ℚ
  | none => 1
  | some i => if i.1 = 0 then 1 / 2 ^ ℓ else 0

/-- `φ = (1, u, 0, 0)/√2` of (22) (arXiv:2610.42069, p.38). -/
noncomputable def phiVec (ℓ : ℕ) (i : IxG ℓ) : ℝ :=
  (phiQ i : ℝ) / Real.sqrt 2

/-- The entries of `T̃_W = 0 ⊕ T_W` of (22) (arXiv:2610.42069, p.38): zero in the row and column of the
adjoined coordinate, `T_W` on the three blocks. -/
def TtQ {ℓ : ℕ} (W : SignMat ℓ) : IxG ℓ → IxG ℓ → ℚ
  | some i, some j => TQ W i j
  | _, _ => 0

/-- The entries of `G_W = I + φφᵀ + tT̃_W` of (22) (arXiv:2610.42069, p.38); `φ_iφ_j = (√2φ)_i(√2φ)_j/2`
is rational. -/
def GQ {ℓ : ℕ} (t : ℚ) (W : SignMat ℓ) : Matrix (IxG ℓ) (IxG ℓ) ℚ :=
  Matrix.of fun i j => (if i = j then 1 else 0) + phiQ i * phiQ j / 2 + t * TtQ W i j

/-- `G_W = I + φφᵀ + tT̃_W` as a real `(3n + 1) × (3n + 1)` matrix (arXiv:2610.42069, (22), p.38). -/
noncomputable def Gmat {ℓ : ℕ} (t : ℚ) (W : SignMat ℓ) : Matrix (IxG ℓ) (IxG ℓ) ℝ :=
  (GQ t W).map (fun q : ℚ => (q : ℝ))

/-- The largest eigenvalue `λ₁` of `G_W` (arXiv:2610.42069, p.38), the supremum of its real spectrum.
`G_W` is symmetric, so its real spectrum is its finite nonempty set of eigenvalues. -/
noncomputable def lam1 {ℓ : ℕ} (t : ℚ) (W : SignMat ℓ) : ℝ :=
  sSup (spectrum ℝ (Gmat t W))

/-- `w` is a unit eigenvector of `G_W` for `λ₁` with `φᵀw > 0` (arXiv:2610.42069, p.38). -/
def IsTopPC {ℓ : ℕ} (t : ℚ) (W : SignMat ℓ) (w : IxG ℓ → ℝ) : Prop :=
  ∑ i, w i ^ 2 = 1 ∧ (Gmat t W).mulVec w = lam1 t W • w ∧ 0 < ∑ i, phiVec ℓ i * w i

open Classical in
/-- The top principal component `w_W` of `G_W` (arXiv:2610.42069, p.38): a unit eigenvector for `λ₁`
with `φᵀw_W > 0`.

**Formalization Note** The source notes that for `W ∈ G` this vector is unique (Lemmas 5.7 and 5.8),
and every statement uses it only for `W ∈ G`; the definition picks one such vector when one exists
and is `0` otherwise. -/
noncomputable def topPC {ℓ : ℕ} (t : ℚ) (W : SignMat ℓ) : IxG ℓ → ℝ :=
  if h : ∃ w, IsTopPC t W w then h.choose else 0

/-- The rank-one spectral truncation `(G_W)_{≥3/2}` (arXiv:2610.42069, Theorem 5.9, p.39): keep the
eigenvalues `≥ 3/2` of the symmetric matrix `G_W` with their eigenvectors and drop the rest, by the
continuous functional calculus of `x ↦ x·1[x ≥ 3/2]`. Defined spectrally, independently of `w_W`. -/
noncomputable def truncG {ℓ : ℕ} (t : ℚ) (W : SignMat ℓ) : Matrix (IxG ℓ) (IxG ℓ) ℝ :=
  cfc (fun x : ℝ => if 3 / 2 ≤ x then x else 0) (Gmat t W)

/-- The two tasks of Theorem 5.9 (arXiv:2610.42069, p.39): sampling from the top principal component,
and from the squared entries of row `0` of the rank-one spectral truncation. -/
inductive PCTask where
  | topPC
  | row0

/-- The target vector of each task of Theorem 5.9 (arXiv:2610.42069, p.39): `w_W`, or row `0` (the
adjoined coordinate, fixed independently of `W`) of `(G_W)_{≥3/2}`. -/
noncomputable def pcVec {ℓ : ℕ} (task : PCTask) (t : ℚ) (W : SignMat ℓ) : IxG ℓ → ℝ :=
  match task with
  | .topPC => topPC t W
  | .row0 => fun j => truncG t W none j

/-- `SQ(G_W)` (arXiv:2610.42069, Definition 2.1, p.15) on the `(3n + 1) × (3n + 1)` matrix itself.
`G_W` has no zero row or column, so the fixed index `default` is never returned. -/
noncomputable def gRespond {ℓ : ℕ} (t : ℚ) (W : SignMat ℓ) :
    SQQuery (IxG ℓ) (IxG ℓ) → PMF (SQAns (IxG ℓ) (IxG ℓ)) :=
  sqRespond (Gmat t W) default default

/-- Reading a coordinate of the register `Idx ℓ` as a coordinate of the family (22): blocks `0, 1, 2`
are the three blocks of (18), the coordinate of block `3` at position `0^{2ℓ}` is the adjoined
coordinate `0`, and the rest of block `3` is zero padding (`none`). -/
def decG {ℓ : ℕ} (i : Idx ℓ) : Option (IxG ℓ) :=
  if h : blk i < 3 then some (some (⟨blk i, h⟩, dat i))
  else if dat i = zeros (2 * ℓ) then some none else none

/-- `orc` is a choice of the quantum input operations (Definition 2.2, pp.15–16) of `G_W`, zero padded
to `4n × 4n` (Remark 4.4, p.32), with the exact rational entry encoding `ratEnc`. -/
def IsGAccess {ℓ : ℕ} (t : ℚ) (W : SignMat ℓ)
    (orc : (k : Fin 5) → Matrix (Qubits (supArity ℓ t k)) (Qubits (supArity ℓ t k)) ℂ) : Prop :=
  IsCoherentAccess (padMat decG (Gmat t W))
    (fun i j => ratEnc (supBits ℓ t) (padMat decG (GQ t W) i j)) orc

end QuarticGap.Supplement


