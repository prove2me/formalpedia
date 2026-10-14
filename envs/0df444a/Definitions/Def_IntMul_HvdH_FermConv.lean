-- Prove2me | Definitions.Def_IntMul_HvdH_FermConv
-- name    : IntMul_HvdH_FermConv
-- status  : Definition
-- author  : @xuanji
-- created : 2026-10-12T13:57:50.064585+00:00
-- url     : https://prove2.me/theorems/b6366f26-647e-492b-9624-b1b20703fea9
-- title:
--   Multidimensional cyclic convolution over the Fermat ring Z/(2^{2rP}+1)

import Definitions.Def_IntMul_HvdH_Fermat
import Definitions.Def_IntMul_HvdH_ConvC

/-! Exact cyclic convolution of integer arrays on `t₁ × ⋯ × t_d × r` (`tᵢ = 2^{eᵢ}`) through
synthetic transforms in `ℤ / (2^{2rP} + 1)`, where `ζ = 2^P` satisfies `ζ^{2r} = -1`, so
`ωᵢ = ζ^{4r/tᵢ}` is a principal `tᵢ`-th root of unity. Each row along the last axis is packed as a
polynomial of degree `< r` evaluated at `ζ`; products in `ℤ[y]/(y^{2r}+1)` then never wrap, and the
cyclic convolution along the last axis is recovered by folding `c ↦ c, c + r`. -/

namespace IntMul.HvdH

/-- The modulus `2^{2rP} + 1`. -/
def fermMod (P r : ℕ) : ℤ := 2 ^ (2 * r * P) + 1

/-- The row of `x` along the last axis at position `k`. -/
def rowList {d : ℕ} (r : ℕ) (x : (Fin (d + 1) → ℕ) → ℤ) (k : Fin d → ℕ) : List ℤ :=
  (List.range r).map (fun c => x (Fin.snoc k c))

/-- Pack each row: evaluate it at `2^P`, reduced modulo `2^{2rP} + 1`. -/
def fermPack {d : ℕ} (P r : ℕ) (x : (Fin (d + 1) → ℕ) → ℤ) (k : Fin d → ℕ) : ℤ :=
  kpack (2 ^ P) (rowList r x k) % fermMod P r

/-- Forward transform modulo `2^{2rP} + 1`: `X̂_m = ∑_k ∏ᵢ ωᵢ^{mᵢkᵢ} X_k`, `ωᵢ = 2^{P·4r/tᵢ}`. -/
def fermDft {d : ℕ} (P r : ℕ) (e : Fin d → ℕ) (X : (Fin d → ℕ) → ℤ) (m : Fin d → ℕ) : ℤ :=
  (∑ k ∈ Fintype.piFinset (fun i => Finset.range (2 ^ e i)),
    2 ^ (P * ∑ i, 4 * r / 2 ^ e i * (m i * k i)) * X k) % fermMod P r

/-- Inverse transform without normalisation: `∑_m ∏ᵢ ωᵢ^{-mᵢjᵢ} Z_m` with `ω⁻¹ = ω^{t-1}`. -/
def fermIdft {d : ℕ} (P r : ℕ) (e : Fin d → ℕ) (Z : (Fin d → ℕ) → ℤ) (j : Fin d → ℕ) : ℤ :=
  (∑ m ∈ Fintype.piFinset (fun i => Finset.range (2 ^ e i)),
    2 ^ (P * ∑ i, 4 * r / 2 ^ e i * (m i * j i * (2 ^ e i - 1))) * Z m) % fermMod P r

/-- Exact cyclic convolution of integer arrays: transform, multiply pointwise modulo
`2^{2rP} + 1`, transform back, unpack `2r` balanced base-`2^P` digits, fold the last axis
cyclically and divide by `∏ tᵢ`. -/
def fermConv {d : ℕ} (P r : ℕ) (e : Fin d → ℕ) (x y : (Fin (d + 1) → ℕ) → ℤ)
    (j : Fin (d + 1) → ℕ) : ℤ :=
  let F := fermMod P r
  let Z := fermIdft P r e
    (fun m => fermDft P r e (fermPack P r x) m * fermDft P r e (fermPack P r y) m % F) (Fin.init j)
  let l := kunpack (2 ^ P) (2 * r) (balMod F Z)
  (l.getD (j (Fin.last d)) 0 + l.getD (j (Fin.last d) + r) 0) / 2 ^ (∑ i, e i)

/-- Exact cyclic convolution of Gaussian-integer arrays (four integer convolutions). -/
def fermConvZ {d : ℕ} (P r : ℕ) (e : Fin d → ℕ) (U V : (Fin (d + 1) → ℕ) → ℤ × ℤ)
    (j : Fin (d + 1) → ℕ) : ℤ × ℤ :=
  (fermConv P r e (fun x => (U x).1) (fun x => (V x).1) j -
      fermConv P r e (fun x => (U x).2) (fun x => (V x).2) j,
    fermConv P r e (fun x => (U x).1) (fun x => (V x).2) j +
      fermConv P r e (fun x => (U x).2) (fun x => (V x).1) j)

/-- The fixed-point convolution oracle: exact convolution, then one division by `2^p ∏ tᵢ · r`
with rounding towards zero. -/
def fermConvRound {d : ℕ} (p P r : ℕ) (e : Fin d → ℕ) (U V : (Fin (d + 1) → ℕ) → ℤ × ℤ)
    (j : Fin (d + 1) → ℕ) : ℤ × ℤ :=
  let W := fermConvZ P r e U V j
  (W.1.tdiv ((2 ^ p * (r * 2 ^ (∑ i, e i)) : ℕ) : ℤ), W.2.tdiv ((2 ^ p * (r * 2 ^ (∑ i, e i)) : ℕ) : ℤ))

end IntMul.HvdH


