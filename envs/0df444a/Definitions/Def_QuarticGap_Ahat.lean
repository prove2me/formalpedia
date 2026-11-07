-- Prove2me | Definitions.Def_QuarticGap_Ahat
-- name    : QuarticGap_Ahat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:45:10.70939+00:00
-- url     : https://prove2.me/theorems/3a13944b-bf35-40a1-bafb-d8fea09fae01
-- title:
--   The family $\widehat A_W$, $\widehat b$, the promise set $\mathcal G$, the solution $x_W$, and the entry encoding
-- statement:
--   Let $n = 4^\ell$, so that $k = 2\ell$, $\sqrt n = 2^\ell$, and rows and columns of $n \times n$ matrices are indexed by $\{0,1\}^k$. Let $h_{ja} = (-1)^{j\cdot a}$, let $H$ be the normalized Walsh–Hadamard matrix with entries $h_{ja}/\sqrt n$, let $u = n^{-1/2}(1,\dots,1)^{\mathsf T}$, and for a sign matrix $W \in \{\pm1\}^{n\times n}$ put
--   $$
--   R = \frac{W}{\sqrt n}, \quad v = Ru, \quad y = Hv, \quad \nu = \|v\|^2, \quad \omega = u^{\mathsf T} v .
--   $$
--   The promise set is $\mathcal G = \{W : \|R\| \le 8\}$, with the operator norm. For rational $\lambda, \alpha$ the family (15) is
--   $$
--   A_W = \begin{pmatrix} I & 0 & 0 \\ -\lambda R & I & 0 \\ 0 & -\lambda H & I \end{pmatrix}, \qquad \widehat A_W = (\alpha A_W) \oplus I_n, \qquad \widehat b = \tfrac12 (u,u,u,u)^{\mathsf T},
--   $$
--   of dimension $4n$. The item also defines the target $p_{\widehat A_W^{-1}\widehat b}$; the solution vector $x_W = (u,\ u+\lambda v,\ u+\lambda e_0+\lambda^2 y,\ \alpha u)$ of (16) with $D_W = \|x_W\|^2$; the constants $d_n$, $C_\lambda$ and $\varepsilon_{\mathrm{lin}}(\lambda,\alpha)$ of (17); the vectors $z_0$, $r_W$ and the number $L_n$ of the quantum upper bound; the sign matrices $W(s)$ of Lemma 2.11; and the identification $f(a,b) = W_{ab}$.
--
--   **Formalization Note** The parameter $\lambda$ is named `lam` in Lean. A coordinate of the output vector has two block wires followed by $2\ell$ data wires, block $0,1,2,3$ being the source's blocks $1,2,3,4$. Entries are rational because $\sqrt n = 2^\ell$. They are encoded as a sign bit and a numerator and denominator in $\ell + B(\lambda,\alpha)$ bits each, most significant bit first, with $B$ a fixed function of the parameters: the source's "fixed binary encoding" with $O(\log n)$ bits. Lean checks that it tells entries apart in `Solutions/verification`.
-- source:
--   Chakrabarti, Herman, Kim, Ozgul, The Quartic Gap Between Quantum and Dequantized Algorithms for Linear Algebra Is Tight, arXiv:2610.42069 (file sha256 9f68aaf9…), §2.4, p.17; (15), Lemma 4.2, pp.29–30; (17), p.30; Lemma 2.11, p.20; proof of Theorem 4.3, p.32

import Mathlib
import Definitions.Def_QuarticGap_IsCoherentAccess

open QAlgorithms

namespace QuarticGap

/-- `{0,1}^k` for `k = 2ℓ`, so that `n = 2^k = 4^ℓ` is a power of four and `√n = 2^ℓ`
(arXiv:2610.42069, §2.4, p.17). Wire `0` is the most significant bit. -/
abbrev Bits (ℓ : ℕ) := Qubits (2 * ℓ)

/-- The `4n` coordinates of the output vector: two block wires, then `2ℓ` data wires. -/
abbrev Idx (ℓ : ℕ) := Qubits (2 + 2 * ℓ)

/-- A sign matrix `W ∈ {±1}^{n×n}` (arXiv:2610.42069, §2.4, p.17). -/
abbrev SignMat (ℓ : ℕ) := Bits ℓ → Bits ℓ → ℤˣ

/-- The block of a coordinate, in `{0, 1, 2, 3}` (the source's blocks `1, 2, 3, 4` of (15)). -/
def blk {ℓ : ℕ} (i : Idx ℓ) : ℕ :=
  bitsToNat fun t : Fin 2 => i (Fin.castAdd (2 * ℓ) t)

/-- The position of a coordinate inside its block. -/
def dat {ℓ : ℕ} (i : Idx ℓ) : Bits ℓ :=
  fun t => i (Fin.natAdd 2 t)

/-- `h_ja = (−1)^{j·a}` (arXiv:2610.42069, §2.4, p.17). -/
def hSign {ℓ : ℕ} (j a : Bits ℓ) : ℤˣ :=
  if dotBits j a then -1 else 1

/-- The normalized Walsh–Hadamard matrix `H`, with entries `h_ja/√n` (arXiv:2610.42069, §2.4, p.17). -/
noncomputable def Hmat (ℓ : ℕ) : Matrix (Bits ℓ) (Bits ℓ) ℝ :=
  Matrix.of fun j a => sgn (hSign j a) / 2 ^ ℓ

/-- `R = W/√n` (arXiv:2610.42069, (1), p.17). -/
noncomputable def Rmat {ℓ : ℕ} (W : SignMat ℓ) : Matrix (Bits ℓ) (Bits ℓ) ℝ :=
  Matrix.of fun a b => sgn (W a b) / 2 ^ ℓ

/-- The uniform unit vector `u = n^{−1/2}(1, …, 1)ᵀ` (arXiv:2610.42069, §2.4, p.17). -/
noncomputable def uVec (ℓ : ℕ) : Bits ℓ → ℝ := fun _ => 1 / 2 ^ ℓ

/-- The standard basis vector at `a` (`e₀` is `eVec (zeros _)`). -/
noncomputable def eVec {ℓ : ℕ} (a : Bits ℓ) : Bits ℓ → ℝ := fun r => if r = a then 1 else 0

/-- `v = Ru` (arXiv:2610.42069, (1), p.17). -/
noncomputable def vVec {ℓ : ℕ} (W : SignMat ℓ) : Bits ℓ → ℝ := (Rmat W).mulVec (uVec ℓ)

/-- `y = Hv` (arXiv:2610.42069, (1), p.17). -/
noncomputable def yVec {ℓ : ℕ} (W : SignMat ℓ) : Bits ℓ → ℝ := (Hmat ℓ).mulVec (vVec W)

/-- `ν = ∥v∥²` (arXiv:2610.42069, (1), p.17). -/
noncomputable def nu {ℓ : ℕ} (W : SignMat ℓ) : ℝ := ∑ a, vVec W a ^ 2

/-- `ω = uᵀv` (arXiv:2610.42069, Lemma 4.2, p.30). -/
noncomputable def omega {ℓ : ℕ} (W : SignMat ℓ) : ℝ := ∑ a, uVec ℓ a * vVec W a

/-- The promise set `G = {W : ∥R∥ ≤ 8}`, with the operator norm (arXiv:2610.42069, (2), p.17). -/
def G (ℓ : ℕ) : Set (SignMat ℓ) := {W | specNorm (Rmat W) ≤ 8}

/-- The entries of `Â_W = (αA_W) ⊕ I_n` of (15) (arXiv:2610.42069, p.29), where `A_W` is block lower
triangular with diagonal `I` and subdiagonal blocks `−λR`, `−λH`. They are rational because
`√n = 2^ℓ`. In particular entry (row `n + a`, column `b`) is `−αλW_ab/√n`.

**Formalization Note** The parameter `lam` is the source's `λ`, a reserved word of Lean. -/
def AhatQ {ℓ : ℕ} (lam α : ℚ) (W : SignMat ℓ) (i j : Idx ℓ) : ℚ :=
  match blk i, blk j with
  | 0, 0 | 1, 1 | 2, 2 => if dat i = dat j then α else 0
  | 3, 3 => if dat i = dat j then 1 else 0
  | 1, 0 => -(α * lam * ((W (dat i) (dat j) : ℤ) : ℚ)) / 2 ^ ℓ
  | 2, 1 => -(α * lam * ((hSign (dat i) (dat j) : ℤ) : ℚ)) / 2 ^ ℓ
  | _, _ => 0

/-- `Â_W` as a real matrix (arXiv:2610.42069, (15), p.29). -/
noncomputable def Ahat {ℓ : ℕ} (lam α : ℚ) (W : SignMat ℓ) : Matrix (Idx ℓ) (Idx ℓ) ℝ :=
  Matrix.of fun i j => (AhatQ lam α W i j : ℝ)

/-- `b̂ = ½(u, u, u, u)`, the uniform unit vector of dimension `4n` (arXiv:2610.42069, (15), p.29). -/
noncomputable def bhat (ℓ : ℕ) : Idx ℓ → ℝ := fun _ => 1 / 2 ^ (ℓ + 1)

/-- The target distribution `p_{Â_W⁻¹b̂}` (arXiv:2610.42069, Theorem 4.3, p.30). -/
noncomputable def target {ℓ : ℕ} (lam α : ℚ) (W : SignMat ℓ) : Idx ℓ → ℝ :=
  lenSqDist ((Ahat lam α W)⁻¹.mulVec (bhat ℓ))

/-- `SQ(Â_W)` (arXiv:2610.42069, Definition 2.1, p.15). Â_W has no zero row or column, so the fixed
index of conditional sampling is never returned and the choice `default` is immaterial. -/
noncomputable def famRespond {ℓ : ℕ} (lam α : ℚ) (W : SignMat ℓ) :
    SQQuery (Idx ℓ) (Idx ℓ) → PMF (SQAns (Idx ℓ) (Idx ℓ)) :=
  sqRespond (Ahat lam α W) default default

/-- `x_W = (u, u + λv, u + λe₀ + λ²y, αu)` (arXiv:2610.42069, (16), p.30). -/
noncomputable def xW {ℓ : ℕ} (lam α : ℚ) (W : SignMat ℓ) (i : Idx ℓ) : ℝ :=
  match blk i with
  | 0 => uVec ℓ (dat i)
  | 1 => uVec ℓ (dat i) + lam * vVec W (dat i)
  | 2 => uVec ℓ (dat i) + lam * eVec (zeros _) (dat i) + (lam : ℝ) ^ 2 * yVec W (dat i)
  | _ => α * uVec ℓ (dat i)

/-- `D_W = ∥x_W∥²` (arXiv:2610.42069, Lemma 4.2, p.30). -/
noncomputable def DW {ℓ : ℕ} (lam α : ℚ) (W : SignMat ℓ) : ℝ := ∑ i, xW lam α W i ^ 2

/-- `d_n = 3 + α² + 2λ² + λ⁴ + 2λ/√n` (arXiv:2610.42069, Lemma 4.2, p.30). -/
noncomputable def dn (ℓ : ℕ) (lam α : ℚ) : ℝ :=
  3 + (α : ℝ) ^ 2 + 2 * (lam : ℝ) ^ 2 + (lam : ℝ) ^ 4 + 2 * lam / 2 ^ ℓ

/-- `C_λ = √2(λ² + λ⁴) + 2λ(1 + λ²) + 2λ²` (arXiv:2610.42069, Lemma 4.2, p.30). -/
noncomputable def Clam (lam : ℚ) : ℝ :=
  Real.sqrt 2 * ((lam : ℝ) ^ 2 + (lam : ℝ) ^ 4) + 2 * lam * (1 + (lam : ℝ) ^ 2) + 2 * (lam : ℝ) ^ 2

/-- `ε_lin(λ, α)` of (17) (arXiv:2610.42069, p.30). `√e` is `Real.exp (1/2)`. -/
noncomputable def εLin (lam α : ℚ) : ℝ :=
  min ((lam : ℝ) ^ 2 / (Real.exp (1 / 2) * (3 + (α : ℝ) ^ 2 + 2 * (lam : ℝ) ^ 2 + (lam : ℝ) ^ 4)))
    ((lam : ℝ) ^ 2 / (3 + (α : ℝ) ^ 2 + 5 * (lam : ℝ) ^ 2 + 2 * (lam : ℝ) ^ 4))

/-- `z₀ = (u, u, u + λe₀, αu)`, the part of `x_W` that does not depend on `W`
(arXiv:2610.42069, proof of Theorem 4.3, p.32). -/
noncomputable def z0 {ℓ : ℕ} (lam α : ℚ) (i : Idx ℓ) : ℝ :=
  match blk i with
  | 0 | 1 => uVec ℓ (dat i)
  | 2 => uVec ℓ (dat i) + lam * eVec (zeros _) (dat i)
  | _ => α * uVec ℓ (dat i)

/-- `r_W = (0, λv, λ²y, 0)` (arXiv:2610.42069, proof of Theorem 4.3, p.32). -/
noncomputable def rW {ℓ : ℕ} (lam : ℚ) (W : SignMat ℓ) (i : Idx ℓ) : ℝ :=
  match blk i with
  | 1 => lam * vVec W (dat i)
  | 2 => (lam : ℝ) ^ 2 * yVec W (dat i)
  | _ => 0

/-- `L_n = ∥z₀∥ + √((λ² + λ⁴)n)` (arXiv:2610.42069, proof of Theorem 4.3, p.32). -/
noncomputable def Ln (ℓ : ℕ) (lam α : ℚ) : ℝ :=
  Real.sqrt (∑ i : Idx ℓ, z0 lam α i ^ 2) + Real.sqrt (((lam : ℝ) ^ 2 + (lam : ℝ) ^ 4) * 4 ^ ℓ)

/-- The sign matrix `f(a, b) = W_ab` viewed as a Boolean function on `{0,1}^{2k}`: a point is the
concatenation of `a` and `b` (arXiv:2610.42069, §2.5, p.18). -/
def flatSign {ℓ : ℕ} (W : SignMat ℓ) : Qubits (2 * ℓ + 2 * ℓ) → ℤˣ :=
  fun σ => W (fun t => σ (Fin.castAdd _ t)) (fun t => σ (Fin.natAdd _ t))

/-- The inverse of `flatSign`: `W_ab = f(a, b)`. -/
def unflat {ℓ : ℕ} (f : Qubits (2 * ℓ + 2 * ℓ) → ℤˣ) : SignMat ℓ :=
  fun a b => f (Fin.append a b)

/-- The sign matrix `W(s)` of Lemma 2.11 (arXiv:2610.42069, p.20, proof p.21): `W(s)_ab` is `1` if
`a ≠ 0^k` and `s_a = 1`, and `h_ab` otherwise. `W(∅)` is `hardW` at the zero string, and `W(a)` is
`hardW` at the indicator of `a ≠ 0^k`, which replaces row `a` of `R` by `uᵀ`. -/
def hardW {ℓ : ℕ} (s : Bits ℓ → Bool) : SignMat ℓ :=
  fun a b => if a ≠ zeros _ ∧ s a = true then 1 else hSign a b

/-- A bit count `B(λ, α)` such that the numerator and denominator of every entry of `Â_W` fit in
`ℓ + B` bits: they divide `|num α|·|num λ|` and `den α·den λ·2^ℓ`, or are `1`. A fixed function of the
parameters, so entries have `O(log n)` bits (arXiv:2610.42069, §2.4, p.17). -/
def entryBits (lam α : ℚ) : ℕ :=
  Nat.size (α.num.natAbs * lam.num.natAbs * α.den * lam.den)

/-- The encoding of a rational in `1 + 2b` bits: sign bit, then numerator and denominator in `b` bits
each, most significant bit first (arXiv:2610.42069, Definition 2.2, p.15, "a fixed binary encoding";
§2.4, p.17, "numerator and denominator have O(log n) bits"). -/
def ratEnc (b : ℕ) (q : ℚ) : Qubits (1 + (b + b)) :=
  Fin.append (fun _ : Fin 1 => decide (q < 0))
    (Fin.append (natToBits b q.num.natAbs) (natToBits b q.den))

/-- The number of output bits of the reversible entry query of `Â_W`. -/
def entryWidth (ℓ : ℕ) (lam α : ℚ) : ℕ :=
  1 + ((ℓ + entryBits lam α) + (ℓ + entryBits lam α))

/-- The table of encoded entries of `Â_W`. -/
def entryTable {ℓ : ℕ} (lam α : ℚ) (W : SignMat ℓ) (i j : Idx ℓ) : Qubits (entryWidth ℓ lam α) :=
  ratEnc (ℓ + entryBits lam α) (AhatQ lam α W i j)

/-- The register sizes of the five quantum input operations of `Â_W`. -/
def famArity (ℓ : ℕ) (lam α : ℚ) : Fin 5 → ℕ :=
  coherentArity (2 + 2 * ℓ) (2 + 2 * ℓ) (entryWidth ℓ lam α)

/-- A choice of quantum input operations of `Â_W` (arXiv:2610.42069, Definition 2.2, pp.15–16). -/
def IsFamAccess {ℓ : ℕ} (lam α : ℚ) (W : SignMat ℓ)
    (orc : (k : Fin 5) → Matrix (Qubits (famArity ℓ lam α k)) (Qubits (famArity ℓ lam α k)) ℂ) :
    Prop :=
  IsCoherentAccess (Ahat lam α W) (entryTable lam α W) orc

/-- A circuit output that reads `2 + 2ℓ` designated wires, so that the output map does no computation
beyond the measurement. -/
def readWires {ℓ N : ℕ} (w : Fin (2 + 2 * ℓ) ↪ Fin N) (z : Qubits N) : Idx ℓ :=
  z ∘ w

end QuarticGap


