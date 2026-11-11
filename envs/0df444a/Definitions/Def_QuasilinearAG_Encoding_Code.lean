-- Prove2me | Definitions.Def_QuasilinearAG_Encoding_Code
-- name    : QuasilinearAG_Encoding_Code
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T15:40:57.518428+00:00
-- url     : https://prove2.me/theorems/c93446c4-4a75-4817-a62a-d10d92195865
-- title:
--   Coefficient encoder $E$, restriction $S_K$, recovery map $L=(S_KE)^{-1}S_K$, systematic encoder and Hamming weight
-- statement:
--   Let $R$ be a commutative ring (the field $\mathbb F_{q^2}$ in the paper) and $G$ an $N\times K$ matrix over $R$, the **coefficient generator**.
--
--   - The **coefficient encoder** is $E:R^K\to R^N$, $E c=Gc$; the **code** is its range $\{Gc : c\in R^K\}$.
--   - $S_K:R^N\to R^K$ restricts a word to its first $K$ ordered positions, and $S_K G$ is the $K\times K$ matrix of the first $K$ rows of $G$ (for $K\le N$).
--   - The **recovery map** is the full-domain linear map $L=(S_KE)^{-1}S_K:R^N\to R^K$, defined on every word: $Lw=(S_KG)^{-1}(w_1,\dots,w_K)$. It recovers the coefficient vector of a codeword.
--   - The **systematic encoder** sends $y\in R^K$ to $E\big((S_KE)^{-1}y\big)$, the codeword whose values at the first $K$ positions are $y$ (when $S_KG$ is invertible, i.e. the first $K$ positions are an **information set**).
--   - Transposes are ordinary transposes: $E^{\mathsf T}=G^{\mathsf T}$ and $L^{\mathsf T}$, with no conjugation.
--   - The **weight** of a word is the number of its nonzero coordinates.
--
--   These are the maps whose costs Theorem 1.1 bounds: $E$, the systematic encoder, $L$, membership in the code, $E^{\mathsf T}$ and $L^{\mathsf T}$.
--
--   **Formalization Note** For $K>N$ (never used) a missing row of $S_KG$ is read as $0$. The inverse is Mathlib's matrix inverse, which is the true inverse whenever $S_KG$ is invertible, as every statement below asserts.
-- source:
--   Chao, Liu, Li, Ma, Wang, Quasilinear Encoding at the Quadratic Alphabet Scale via Short Cartier Bases, STOC 2027 submission (manuscript sha256 355c15dc…), p. 1 (PDF 3) and p. 2 (PDF 4)

import Mathlib

namespace QuasilinearAG.Encoding

/-!
# Linear codes from a coefficient generator: `E`, `S_K`, `L = (S_K E)⁻¹ S_K`, transposes, weight

Chao, Liu, Li, Ma, Wang, *Quasilinear Encoding at the Quadratic Alphabet Scale via Short Cartier
Bases*, STOC 2027 submission (manuscript sha256 355c15dc…), p. 1 (PDF 3) and p. 2 (PDF 4).

A code of length `N` and dimension `K` over a commutative ring `R` (a field `F_{q²}` in the paper)
is given by its `N × K` coefficient generator `G`:

* the coefficient encoder is `E c = G c` (`G.mulVec c`); the code is its range `codeSpan G`;
* `S_K` restricts a word of length `N` to its first `K` ordered positions (`restrictK`), and
  `prefixRows G = S_K G` is the `K × K` matrix of the first `K` rows (both meaningful when `K ≤ N`;
  a missing row is read as `0`, which never happens in the uses below);
* `recoverMat G = (S_K G)⁻¹ S_K`, the `K × N` matrix of the full-domain recovery map
  `L = (S_K E)⁻¹ S_K` (defined on every word, not only on codewords);
* the systematic encoder sends `y ∈ R^K` to `E ((S_K E)⁻¹ y)`, the codeword whose first `K`
  values are `y` (when `S_K G` is invertible);
* transposes are ordinary transposes (`Eᵀ = Gᵀ`, `Lᵀ = (recoverMat G)ᵀ`), no conjugation;
* `weight w` is the Hamming weight, the number of nonzero coordinates.
-/

variable {R : Type*} [CommRing R]

/-- The code spanned by the columns of the generator `G`: the range of `c ↦ G c`. -/
def codeSpan {N K : ℕ} (G : Matrix (Fin N) (Fin K) R) : Submodule R (Fin N → R) :=
  LinearMap.range (Matrix.mulVecLin G)

/-- `S_K w`: the first `K` coordinates of the word `w ∈ R^N` (`0` past position `N`). -/
def restrictK {N : ℕ} (K : ℕ) (w : Fin N → R) : Fin K → R :=
  fun i => if h : (i : ℕ) < N then w ⟨i, h⟩ else 0

/-- `S_K G`: the `K × K` matrix of the first `K` rows of `G`. -/
def prefixRows {N K : ℕ} (G : Matrix (Fin N) (Fin K) R) : Matrix (Fin K) (Fin K) R :=
  fun i j => if h : (i : ℕ) < N then G ⟨i, h⟩ j else 0

/-- The `K × N` matrix of `S_K`: `1` at `(i, i)`, `0` elsewhere. -/
def selectK (N K : ℕ) : Matrix (Fin K) (Fin N) R :=
  fun i n => if (i : ℕ) = (n : ℕ) then 1 else 0

/-- The matrix of the full-domain recovery map `L = (S_K E)⁻¹ S_K`. -/
noncomputable def recoverMat {N K : ℕ} (G : Matrix (Fin N) (Fin K) R) : Matrix (Fin K) (Fin N) R :=
  (prefixRows G)⁻¹ * selectK N K

/-- The systematic encoder: `y ↦ E ((S_K E)⁻¹ y)`. -/
noncomputable def systematicEncode {N K : ℕ} (G : Matrix (Fin N) (Fin K) R) (y : Fin K → R) :
    Fin N → R :=
  G.mulVec ((prefixRows G)⁻¹.mulVec y)

/-- The Hamming weight of a word: the number of nonzero coordinates. -/
noncomputable def weight {N : ℕ} (w : Fin N → R) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i => w i ≠ 0)).card

end QuasilinearAG.Encoding


