-- Prove2me | Definitions.Def_RandTensorIso_Smoothed_Tensor
-- name    : RandTensorIso_Smoothed_Tensor
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T01:35:28.6719+00:00
-- url     : https://prove2.me/theorems/7888e8db-4776-4c9f-ad21-5f92d1b31421
-- title:
--   Complex 3-tensors, the $U(n)^3$ action, the Frobenius norm, the unitary orbit distance, Gaussian rationals and $\ell$-bit truncation
-- statement:
--   A **tensor** $A\in\mathbb C^{n\times n\times n}$ assigns a complex number $A(p)$ to every position $p=(p_1,p_2,p_3)\in[n]^3$. Its **Frobenius norm** is $\|A\|_F=\big(\sum_{p}|A(p)|^2\big)^{1/2}$. For $L,R,T\in U(n)$, the unitary group, the action is
--   $$((L,R,T)\curvearrowright A)_{ijk}=\sum_{p,q,r}L_{ip}R_{jq}T_{kr}A_{pqr},$$
--   with no complex conjugates, and the **unitary orbit distance** is
--   $$\operatorname{dist}_{\mathbb C}(A,B)=\inf_{L,R,T\in U(n)}\|(L,R,T)\curvearrowright A-B\|_F .$$
--   A **Gaussian rational** is $s+it$ with $s,t\in\mathbb Q$; the field $\mathbb Q(i)$ of them is used for exact inputs and witnesses. The **truncation** of a real $x$ to $\ell$ bits after the binary point cuts its binary expansion after $\ell$ fractional digits, i.e. rounds $x2^\ell$ toward zero to an integer $m$ and returns $m/2^\ell$, so $|x-m/2^\ell|<2^{-\ell}$; the truncation $\tilde A$ of a complex tensor truncates the real and imaginary part of every entry separately, so $\tilde A\in\mathbb Q(i)^{n\times n\times n}$.
--
--   **Formalization Note.** Positions are 0-based, `Fin n × Fin n × Fin n`; `U n` is Mathlib's `Matrix.unitaryGroup (Fin n) ℂ`; `distC` is a real `⨅` over the nonempty type `U n × U n × U n` of values bounded below by $0$, hence the true infimum (attained by compactness, although the definition uses the infimum). A Gaussian rational is a pair `(s, t) : ℚ × ℚ` (`GQ`), read in $\mathbb C$ by `GQ.toC`; `truncNum ℓ x` is the integer numerator $m$ and `truncT ℓ A` the truncated tensor.
-- source:
--   Chizewer, Everett, Mithal, Qiao, Random tensor isomorphism under orthogonal and unitary actions: Smoothed and average-case analysis, STOC 2027 submission (manuscript sha256 f4a12b77…), pp. 5, 14, 30 (PDF 7, 16, 32), §1.4 notation, §2 preamble (ℚ(i)), §2.3 (truncation to ℓ bits)

import Mathlib

namespace RandTensorIso.Smoothed

open Matrix

/-- Complex `n × n × n` tensors (paper: `ℂ^{n×n×n}`). A position is a triple
`p = (p₁, p₂, p₃) ∈ [n]³`, written 0-based as `Fin n × Fin n × Fin n`. -/
abbrev Tensor3 (n : ℕ) : Type := Fin n × Fin n × Fin n → ℂ

/-- The Frobenius norm `‖A‖_F = (∑_p |A(p)|²)^{1/2}`. -/
noncomputable def frob {n : ℕ} (A : Tensor3 n) : ℝ :=
  Real.sqrt (∑ p, ‖A p‖ ^ 2)

/-- The action `((L, R, T) ↷ A)_{ijk} = ∑_{p,q,r} L_{ip} R_{jq} T_{kr} A_{pqr}` (no conjugates). -/
def act {n : ℕ} (L R T : Matrix (Fin n) (Fin n) ℂ) (A : Tensor3 n) : Tensor3 n :=
  fun x => ∑ p : Fin n, ∑ q : Fin n, ∑ r : Fin n, L x.1 p * R x.2.1 q * T x.2.2 r * A (p, q, r)

/-- The unitary group `U(n)` (Mathlib's `Matrix.unitaryGroup`). -/
abbrev U (n : ℕ) : Type := Matrix.unitaryGroup (Fin n) ℂ

/-- The unitary orbit distance
`dist_ℂ(A, B) = inf_{L,R,T ∈ U(n)} ‖(L, R, T) ↷ A − B‖_F`
(an infimum over a nonempty set of nonnegative reals, so the real `⨅` is the true infimum). -/
noncomputable def distC {n : ℕ} (A B : Tensor3 n) : ℝ :=
  ⨅ g : U n × U n × U n,
    frob (act (g.1 : Matrix (Fin n) (Fin n) ℂ) (g.2.1 : Matrix (Fin n) (Fin n) ℂ)
      (g.2.2 : Matrix (Fin n) (Fin n) ℂ) A - B)

/-- A Gaussian rational `s + i t ∈ ℚ(i)` is stored as the pair `(s, t) : ℚ × ℚ`. -/
abbrev GQ : Type := ℚ × ℚ

/-- The complex number `s + i t` denoted by a Gaussian rational `(s, t)`. -/
def GQ.toC (z : GQ) : ℂ := ⟨(z.1 : ℝ), (z.2 : ℝ)⟩

/-- A tensor with entries in `ℚ(i)`. -/
abbrev GTensor (n : ℕ) : Type := Fin n × Fin n × Fin n → GQ

/-- The complex tensor denoted by a Gaussian-rational tensor. -/
def GTensor.toC {n : ℕ} (A : GTensor n) : Tensor3 n := fun p => GQ.toC (A p)

/-- The complex matrix denoted by a matrix with entries in `ℚ(i)`. -/
def gqMat {n : ℕ} (X : Matrix (Fin n) (Fin n) GQ) : Matrix (Fin n) (Fin n) ℂ :=
  X.map GQ.toC

/-- Truncation of a real number to `ℓ` bits after the binary point, as the integer numerator
over `2^ℓ`: the binary expansion of `x` is cut after `ℓ` fractional digits, i.e. rounding
toward zero, so `|x − truncNum ℓ x / 2^ℓ| < 2^{−ℓ}`. -/
noncomputable def truncNum (ℓ : ℕ) (x : ℝ) : ℤ :=
  if 0 ≤ x then ⌊x * 2 ^ ℓ⌋ else ⌈x * 2 ^ ℓ⌉

/-- The truncated value `truncNum ℓ x / 2^ℓ ∈ 2^{−ℓ} ℤ`. -/
noncomputable def truncR (ℓ : ℕ) (x : ℝ) : ℚ := (truncNum ℓ x : ℚ) / 2 ^ ℓ

/-- The truncation `Ã` of a complex tensor to `ℓ` bits after the binary point, real and
imaginary parts separately; its entries lie in `ℚ(i)`. -/
noncomputable def truncT {n : ℕ} (ℓ : ℕ) (A : Tensor3 n) : GTensor n :=
  fun p => (truncR ℓ (A p).re, truncR ℓ (A p).im)

end RandTensorIso.Smoothed


