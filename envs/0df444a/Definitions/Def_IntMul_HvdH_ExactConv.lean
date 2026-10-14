-- Prove2me | Definitions.Def_IntMul_HvdH_ExactConv
-- name    : IntMul_HvdH_ExactConv
-- status  : Definition
-- author  : @xuanji
-- created : 2026-10-12T02:52:47.240216+00:00
-- url     : https://prove2.me/theorems/b2003833-2480-4674-8229-8e15ab3f347b
-- title:
--   Exact multidimensional integer convolution via approximate DFTs (Harvey–van der Hoeven §5.3)

import Definitions.Def_IntMul_HvdH_BApprox
import Definitions.Def_IntMul_HvdH_FPApprox
import Definitions.Def_IntMul_HvdH_ConvC

/-! Exact multidimensional cyclic convolution of integer arrays via approximate complex DFTs
(Harvey–van der Hoeven §5.3, with the power-of-two DFT supplied by an arbitrary fixed-point
oracle `Ft`). Arrays are functions `(Fin d → ℕ) → β`; the box `∏ᵢ [0, sᵢ)` is the in-range part.
Fixed-point arrays `U : … → ℤ × ℤ` stand for `2^{-p} U`. -/

namespace IntMul.HvdH

/-- Zero a fixed-point array outside the box `∏ᵢ [0, tᵢ)`. -/
def maskZ {d : ℕ} (t : Fin d → ℕ) (U : (Fin d → ℕ) → ℤ × ℤ) (j : Fin d → ℕ) : ℤ × ℤ :=
  if ∀ i, j i < t i then U j else (0, 0)

open Classical in
/-- The normalised `d`-dimensional DFT on the box `∏ᵢ [0, tᵢ)`, zero outside the box:
`(1/∏ tᵢ) ∑_k ∏ᵢ ωᵢ^{-jᵢkᵢ} x_k` with `ωᵢ = e^{2πi/tᵢ}`. -/
noncomputable def dftBox {d : ℕ} (t : Fin d → ℕ) (x : (Fin d → ℕ) → ℂ) (j : Fin d → ℕ) : ℂ :=
  if ∀ i, j i < t i then
    (1 / ∏ i, (t i : ℂ)) * ∑ k ∈ Fintype.piFinset (fun i => Finset.range (t i)),
      (∏ i, Complex.exp (2 * Real.pi * Complex.I / t i) ^ (-((j i * k i : ℕ) : ℤ))) * x k
  else 0

/-- Cyclic convolution on the box `∏ᵢ [0, sᵢ)`. -/
def convBox {d : ℕ} (s : Fin d → ℕ) (u v : (Fin d → ℕ) → ℤ) (j : Fin d → ℕ) : ℤ :=
  ∑ k ∈ Fintype.piFinset (fun i => Finset.range (s i)),
    u k * v (fun i => (j i + s i - k i) % s i)

/-- Approximate scaled DFT on the box `s`: Gaussian resampling `Ã` to the box `t`, the oracle
`Ft` for the DFT on `t`, then `B̃` back to `s` (Theorem 4.1). It approximates
`2^{-2dα²} 𝓕_s`. -/
def fwdZ {d : ℕ} (p α : ℕ) (s t : Fin d → ℕ)
    (Ft : ((Fin d → ℕ) → ℤ × ℤ) → ((Fin d → ℕ) → ℤ × ℤ)) (U : (Fin d → ℕ) → ℤ × ℤ) :
    (Fin d → ℕ) → ℤ × ℤ :=
  tensorMapZ (fun i => Bapprox p (s i) (t i) α)
    (maskZ t (Ft (tensorMapZ (fun i => Sapprox p (s i) (t i) α) U)))

/-- Division by `m > 0` rounded to the nearest integer. -/
def roundDiv (a : ℤ) (m : ℕ) : ℤ := (2 * a + m) / (2 * m)

/-- The full pipeline: scale the integer inputs (entries `< 2^b` in absolute value) to fixed point,
transform both, multiply pointwise, transform the conjugate, and rescale and round:
`u * v = S² 2^{2b} 2^{6dα²} · conj(2^{-2dα²}𝓕_s(conj(2^{-2dα²}𝓕_s u' · 2^{-2dα²}𝓕_s v')))`
with `S = ∏ sᵢ`, `u' = 2^{-b} u`. -/
def exactConv {d : ℕ} (p α b : ℕ) (s t : Fin d → ℕ)
    (Ft : ((Fin d → ℕ) → ℤ × ℤ) → ((Fin d → ℕ) → ℤ × ℤ)) (u v : (Fin d → ℕ) → ℤ) :
    (Fin d → ℕ) → ℤ :=
  let U : (Fin d → ℕ) → ℤ × ℤ := fun x => (u x * 2 ^ (p - b), 0)
  let V : (Fin d → ℕ) → ℤ × ℤ := fun x => (v x * 2 ^ (p - b), 0)
  let Ua := fwdZ p α s t Ft U
  let Va := fwdZ p α s t Ft V
  let W : (Fin d → ℕ) → ℤ × ℤ := fun x => conjZ (mulZ p (Ua x) (Va x))
  let Y := fwdZ p α s t Ft W
  fun j => roundDiv ((Y j).1 * ((∏ i, s i : ℕ) : ℤ) ^ 2 * 2 ^ (2 * b + 6 * d * α ^ 2)) (2 ^ p)

end IntMul.HvdH


