-- Prove2me | Definitions.Def_DDNNFNeg_Supplement_linearLift
-- name    : DDNNFNeg_Supplement_linearLift
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T21:43:52.496753+00:00
-- url     : https://prove2.me/theorems/71d2e13d-766f-4429-a89e-85adaf87e6ae
-- title:
--   Composition $F(x) = f(Ex)$ with a matrix over $\mathbb F_2$
-- statement:
--   For a matrix $E \in \mathbb F_2^{n \times N}$ and a Boolean function $f : \mathbb F_2^n \to \{0,1\}$, the function $F : \mathbb F_2^N \to \{0,1\}$ is
--
--   $$F(x) = f(Ex).$$
--
--   This is the lifted function of the Multi-Partition Lifting Theorem 6.1.
--
--   **Formalization Note** $\mathbb F_2$ is `ZMod 2` and $\mathbb F_2^m$ is identified with $\{0,1\}^m$ bitwise ($0 \leftrightarrow$ false, $1 \leftrightarrow$ true).
-- source:
--   Arenas–Broadrick–Liew–Van den Broeck, d-DNNF is Not Polynomially Closed Under Negation, STOC 2027 submission manuscript (sha256 64e4212767c37c44…fbb68), Theorem 6.1, p.16

import Mathlib

namespace DDNNFNeg.Supplement

/-- The composition `F(x) = f(Ex)` of a Boolean function `f : 𝔽₂ⁿ → {0,1}` with a matrix
`E ∈ 𝔽₂^{n×N}` (Arenas–Broadrick–Liew–Van den Broeck, *d-DNNF is Not Polynomially Closed Under Negation*, STOC 2027 submission manuscript (sha256 64e42127…fbb68), Theorem 6.1, p.16): `F : 𝔽₂ᴺ → {0,1}`.

**Formalization Note** `𝔽₂` is `ZMod 2`, and `𝔽₂ᵐ` is identified with `{0,1}^m = Fin m → Bool`
bitwise (`false ↦ 0`, `true ↦ 1`): `x` is sent to the vector with entries `1` where `x` is
`true`, multiplied by `E`, and the result is read back as the assignment that is `true` exactly
where the entry is `1`. -/
def linearLift {n N : ℕ} (E : Matrix (Fin n) (Fin N) (ZMod 2)) (f : (Fin n → Bool) → Bool) :
    (Fin N → Bool) → Bool :=
  fun x => f (fun i => decide (E.mulVec (fun j => if x j then (1 : ZMod 2) else 0) i = 1))

end DDNNFNeg.Supplement


