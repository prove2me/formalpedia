-- Prove2me | Definitions.Def_LowDepthPRF_AffineHash
-- name    : LowDepthPRF_AffineHash
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:39:22.920481+00:00
-- url     : https://prove2.me/theorems/acae605c-1831-4a9a-802d-6bd82b181029
-- title:
--   The affine hash of Lemma 4.5 over $\mathbb F_{2^\lambda}$
-- statement:
--   Identify $\{0,1\}^\lambda$ with $\mathbb F_{2^\lambda}$ through the coordinates in a fixed $\mathbb F_2$-basis. For a key $(a,b)\in\{0,1\}^\lambda\times\{0,1\}^\lambda$ and an input $x\in\{0,1\}^\lambda$, the hash outputs the first $\ell\log\Delta$ coordinates of
--
--   $$a\cdot x+b\in\mathbb F_{2^\lambda},$$
--
--   read as $\ell$ blocks of $\log\Delta$ bits, each block an element of $[\Delta]$.
--
--   This is the pairwise-independent hash with which the proof of Lemma 4.5 instantiates Construction 4.3. It gives exact pairwise independence, a uniform binary key and logarithmic evaluation depth.
--
--   **Formalization Note** $\mathbb F_{2^\lambda}$ is Mathlib's `GaloisField 2 λ` with a basis from `Module.finBasisOfFinrankEq`. Any basis works, because multiplication by $a$ is $\mathbb F_2$-bilinear in the coordinates of $a$ and $x$. The paper uses the hash only for large $\lambda$, where $\ell\log\Delta\le\lambda$. For the finitely many $\lambda$ with $\ell\log\Delta>\lambda$, the missing bits are $0$, and at $\lambda=0$ the output is $0$.
-- source:
--   Ding, Jain, Komargodski, Pseudorandom Functions in NC¹ from LWE/LPN/CDH, arXiv:2608.25213 (sha256 89a55849…), Proof of Lemma 4.5, p.18 (pdf 20)

import Mathlib
import Definitions.Def_LowDepthPRF_TaperingGGM

namespace LowDepthPRF

/-!
# The affine hash of Lemma 4.5

Ding, Jain, Komargodski, *Pseudorandom Functions in NC¹ from LWE/LPN/CDH*, arXiv:2608.25213
(sha256 89a55849…), proof of Lemma 4.5, p.18: "Choose `H_λ` by evaluating an affine polynomial
over `𝔽_{2^λ}` and taking `ℓ log Δ` output bits, grouped into `ℓ` blocks of `log Δ` bits."

**Formalization Note.**
* `𝔽_{2^λ}` is `GaloisField 2 λ`, identified with `{0,1}^λ` through the coordinates in a fixed
  `𝔽₂`-basis (`Module.finBasisOfFinrankEq`, any basis; bit `true ↦ 1`).
* The key is `(a, b) ∈ {0,1}^λ × {0,1}^λ` (`2λ` bits, `a` first) and
  `H_{a,b}(x)` is the first `ℓ · log Δ` coordinates of `a·x + b`. When `ℓ · log Δ > λ` (finitely
  many small `λ`) the missing bits are `false`, and for `λ = 0` the output is all `false`; the
  paper only uses the hash for large `λ` ("For sufficiently large `λ`, `ℓ log Δ ≤ λ`").
* The output is read by the construction as `ℓ` blocks of `log Δ` bits (`blockIdx`).
-/

/-- A fixed `𝔽₂`-basis of `GaloisField 2 n`, `n ≠ 0`, indexed by `Fin n`. -/
noncomputable def gfBasis (n : ℕ) (h : n ≠ 0) : Module.Basis (Fin n) (ZMod 2) (GaloisField 2 n) :=
  Module.finBasisOfFinrankEq (ZMod 2) (GaloisField 2 n) (GaloisField.finrank 2 h)

/-- `{0,1}^n → 𝔽_{2^n}` through the basis coordinates. -/
noncomputable def toGF (n : ℕ) (h : n ≠ 0) (x : Fin n → Bool) : GaloisField 2 n :=
  (gfBasis n h).equivFun.symm (fun i => if x i then 1 else 0)

/-- `𝔽_{2^n} → {0,1}^n` through the basis coordinates. -/
noncomputable def ofGF (n : ℕ) (h : n ≠ 0) (y : GaloisField 2 n) : Fin n → Bool :=
  fun i => decide ((gfBasis n h).equivFun y i = 1)

/-- The affine hash `H_{a,b}(x) = (a·x + b)_{1…ℓ log Δ}` with key `(a, b)` of `2λ` bits. -/
noncomputable def affineHash (lam : ℕ) : FunFam (Fin (lam + lam) → Bool) lam (ell lam * logDelta lam) :=
  fun k x j =>
    if h : lam = 0 then false
    else if hj : (j : ℕ) < lam then
      ofGF lam h (toGF lam h (fun i => k (Fin.castAdd lam i)) * toGF lam h x +
        toGF lam h (fun i => k (Fin.natAdd lam i))) ⟨j, hj⟩
    else false

end LowDepthPRF


