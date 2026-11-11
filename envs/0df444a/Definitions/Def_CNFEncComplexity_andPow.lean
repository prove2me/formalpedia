-- Prove2me | Definitions.Def_CNFEncComplexity_andPow
-- name    : CNFEncComplexity_andPow
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:29:51.576215+00:00
-- url     : https://prove2.me/theorems/d06ef099-7355-40a4-978c-867f853adab8
-- title:
--   The $b$-fold conjunction $f^{\wedge b}$
-- statement:
--   For $f:\{0,1\}^n\to\{0,1\}$ and $b\in\mathbb N$, the function $f^{\wedge b}:\{0,1\}^{bn}\to\{0,1\}$ evaluates $f$ on $b$ separate inputs and takes the conjunction:
--   $$f^{\wedge b}(\vec x_1,\dots,\vec x_b)=\bigwedge_{i\in[b]} f(\vec x_i),\qquad \vec x_1,\dots,\vec x_b\in\{0,1\}^n .$$
--
--   This is the "multiple queries" function of the mass-production Lemma 11, which checks $b$ advice queries against one truth table at once.
--
--   **Formalization Note** The $bn$ input bits are indexed $0,\dots,bn-1$; the block $\vec x_{i+1}$ consists of the bits $in,\dots,in+n-1$.
-- source:
--   Krapivin, Przybocki, Subercaseaux, The CNF Encoding Complexity of Boolean Functions, arXiv:2611.05614 (held version, sha256 97421ce1…), Lemma 11, p.11 (PDF 12)

import Mathlib

namespace CNFEncComplexity

/-- **The function f^∧b.** Krapivin, Przybocki, Subercaseaux, *The CNF Encoding Complexity of Boolean Functions*, arXiv:2611.05614 (held version, sha256 97421ce1…), Lemma 11, p.11 (PDF 12): "Let f^∧b : {0, 1}^{bn} → {0, 1} be such
that for every x⃗₁, . . . , x⃗_b ∈ {0, 1}ⁿ we have f^∧b(x⃗₁, . . . , x⃗_b) = ⋀_{i∈[b]} f(x⃗ᵢ)."

**Formalization Note.** The `b·n` input bits are indexed by `Fin (b * n)`; block `i` (the vector
x⃗ᵢ₊₁) is the coordinates `i·n, …, i·n + n − 1`, i.e. `finProdFinEquiv (i, j)` for `j : Fin n`. -/
def andPow {n : ℕ} (f : (Fin n → Bool) → Bool) (b : ℕ) : (Fin (b * n) → Bool) → Bool :=
  fun x => decide (∀ i : Fin b, f (fun j => x (finProdFinEquiv (i, j))) = true)

end CNFEncComplexity


