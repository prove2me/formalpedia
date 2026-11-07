-- Prove2me | Definitions.Def_FourierEntropyApprox_IsBoolean
-- name    : FourierEntropyApprox_IsBoolean
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:44:26.591934+00:00
-- url     : https://prove2.me/theorems/c3f10beb-8f2e-4837-ac68-32058d0747f4
-- title:
--   Boolean functions $f:\{-1,1\}^n\to\{-1,1\}$
-- statement:
--   A function $f:\{-1,1\}^n\to\mathbb R$ is **Boolean** if it takes only the values $\pm1$:
--
--   $$f(x)\in\{-1,1\}\quad\text{for every }x\in\{-1,1\}^n.$$
--
--   Boolean functions are the subject of the paper's main results; viewing them as real valued lets them be compared with real approximating polynomials.
--
--   **Formalization Note** The predicate is stated for real-valued functions on `Cube n`.
-- source:
--   Paraashar, Saurabh, Fourier Entropy Bounds via Approximations, arXiv:2611.06451 (held version, sha256 adc9c5fc…), Definition 2.2, p.9 (PDF p.9)

import Mathlib
import Definitions.Def_FourierEntropyApprox_Cube

namespace FourierEntropyApprox

/-!
# Boolean functions on the cube

M. Paraashar, N. Saurabh, *Fourier Entropy Bounds via Approximations*, arXiv:2611.06451 (held version,
sha256 adc9c5fc…), Definition 2.2, p.9: "a Boolean function f : {−1, 1}ⁿ → {−1, 1}".

**Formalization Note.** A Boolean function is a real-valued function on the cube taking only the values `1`
and `−1`, so that it can be compared with real approximating polynomials.
-/

/-- `f : {−1, 1}ⁿ → ℝ` is Boolean: every value is `1` or `−1` (p.9). -/
def IsBoolean {n : ℕ} (f : Cube n → ℝ) : Prop := ∀ x, f x = 1 ∨ f x = -1

end FourierEntropyApprox


