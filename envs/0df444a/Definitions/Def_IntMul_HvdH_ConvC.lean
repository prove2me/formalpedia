-- Prove2me | Definitions.Def_IntMul_HvdH_ConvC
-- name    : IntMul_HvdH_ConvC
-- status  : Definition
-- author  : @xuanji
-- created : 2026-10-12T02:22:25.621916+00:00
-- url     : https://prove2.me/theorems/59702fee-24f4-49bc-a67e-be5394617317
-- title:
--   Complex multidimensional DFT and convolution via twisting and Bluestein (Harvey–van der Hoeven §3.2–3.3)

import Definitions.Def_IntMul_HvdH_ConvR
import Definitions.Def_IntMul_HvdH_Twiddle

/-! Convolution and DFT over `ℂ` via convolution over `R = ℂ[y]/(y^r + 1)` and Bluestein's trick
(Harvey–van der Hoeven Prop. 3.5 and Thm. 3.1). Arrays `x : (Fin (d+1) → ℕ) → β` have `d` axes of
length `tᵢ = 2^{eᵢ}` followed by a last axis of length `r`. Fixed-point arrays `U : … → ℤ × ℤ`
stand for `2^{-p} U`. -/

namespace IntMul.HvdH

/-- Fixed-point product of Gaussian integers at precision `p`: `ρ₀(a b / 2^p)`, rounding each
part towards zero. -/
def mulZ (p : ℕ) (a b : ℤ × ℤ) : ℤ × ℤ :=
  ((a.1 * b.1 - a.2 * b.2).tdiv (2 ^ p), (a.1 * b.2 + a.2 * b.1).tdiv (2 ^ p))

/-- An approximation of `2^p e^{2πij/n}` lying in the disc of radius `2^p` (Lemma 2.12, then
pulled back into the disc). -/
def twD (p n j : ℕ) : ℤ × ℤ := scaleZ p 0 (twiddle p n j)

/-- Fixed-point `T̃`: multiply the coefficient `c` (last axis) by `ζ^c`, `ζ = e^{πi/r}`. -/
def twistZ {d : ℕ} (p r : ℕ) (U : (Fin (d + 1) → ℕ) → ℤ × ℤ) (j : Fin (d + 1) → ℕ) : ℤ × ℤ :=
  mulZ p (twD p (2 * r) (j (Fin.last d))) (U j)

/-- Fixed-point `Ũ = T̃⁻¹`: multiply the coefficient `c < r` by `ζ^{-c} = e^{2πi(2r-c)/(2r)}`. -/
def untwistZ {d : ℕ} (p r : ℕ) (W : (Fin (d + 1) → ℕ) → ℤ × ℤ) (j : Fin (d + 1) → ℕ) : ℤ × ℤ :=
  mulZ p (twD p (2 * r) (2 * r - j (Fin.last d))) (W j)

/-- Proposition 3.5, algorithm: `M̃_ℂ(U, V) = Ũ(M̃_R(T̃U, T̃V))`. -/
def convCa {d : ℕ} (p r : ℕ) (e : Fin d → ℕ) (U V : (Fin (d + 1) → ℕ) → ℤ × ℤ) :
    (Fin (d + 1) → ℕ) → ℤ × ℤ :=
  untwistZ p r (convRa p r e (twistZ p r U) (twistZ p r V))

/-- The exact normalised `(d+1)`-dimensional cyclic convolution `M_ℂ(u, v) = (1/T) u ∗ v`, axis
lengths `2^{eᵢ}` and `r`, `T = r ∏ 2^{eᵢ}`. -/
noncomputable def convC {d : ℕ} (r : ℕ) (e : Fin d → ℕ) (u v : (Fin (d + 1) → ℕ) → ℂ)
    (j : Fin (d + 1) → ℕ) : ℂ :=
  (1 / (r * 2 ^ (∑ i, e i)) : ℂ) *
    ∑ k ∈ Fintype.piFinset (fun i : Fin d => Finset.range (2 ^ e i)), ∑ c ∈ Finset.range r,
      u (Fin.snoc (fun i => k i) c) *
        v (Fin.snoc (fun i => (j i.castSucc + 2 ^ e i - k i) % 2 ^ e i)
          ((j (Fin.last d) + r - c) % r))

/-- Bluestein's chirp `a_j = e^{πi(∑ jᵢ²/tᵢ + j_last²/r)} = e^{2πi η_j/(2r)}`, with
`η_j = ∑ (r/tᵢ) jᵢ² + j_last²` (needs `tᵢ ∣ r`). -/
def chirpIdx {d : ℕ} (r : ℕ) (e : Fin d → ℕ) (j : Fin (d + 1) → ℕ) : ℕ :=
  ∑ i : Fin d, r / 2 ^ e i * j i.castSucc ^ 2 + j (Fin.last d) ^ 2

/-- Theorem 3.1, algorithm (Bluestein): `F̃ U = ā · M̃_ℂ(ā · U, ã)`, with `ã` from Lemma 2.12. -/
def fftCa {d : ℕ} (p r : ℕ) (e : Fin d → ℕ) (U : (Fin (d + 1) → ℕ) → ℤ × ℤ) :
    (Fin (d + 1) → ℕ) → ℤ × ℤ :=
  let a : (Fin (d + 1) → ℕ) → ℤ × ℤ := fun j => twD p (2 * r) (chirpIdx r e j)
  fun j => mulZ p (conjZ (a j)) (convCa p r e (fun k => mulZ p (conjZ (a k)) (U k)) a j)

/-- The exact normalised `(d+1)`-dimensional DFT `F u = (1/T) û`, axis lengths `2^{eᵢ}` and `r`. -/
noncomputable def dftC {d : ℕ} (r : ℕ) (e : Fin d → ℕ) (u : (Fin (d + 1) → ℕ) → ℂ)
    (j : Fin (d + 1) → ℕ) : ℂ :=
  (1 / (r * 2 ^ (∑ i, e i)) : ℂ) *
    ∑ k ∈ Fintype.piFinset (fun i : Fin d => Finset.range (2 ^ e i)), ∑ c ∈ Finset.range r,
      Complex.exp (-(2 * Real.pi * Complex.I *
        (∑ i : Fin d, (j i.castSucc * k i : ℂ) / 2 ^ e i + (j (Fin.last d) * c : ℂ) / r))) *
      u (Fin.snoc (fun i => k i) c)

end IntMul.HvdH


