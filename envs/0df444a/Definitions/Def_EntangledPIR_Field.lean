-- Prove2me | Definitions.Def_EntangledPIR_Field
-- name    : EntangledPIR_Field
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:08:55.829198+00:00
-- url     : https://prove2.me/theorems/4ede8584-ae75-41a9-8ea1-ce6d4a1190c3
-- title:
--   Parameters $k$, $w$, $d$ and the concrete field $\mathbb F_{2^w}$
-- statement:
--   For integers $n,\lambda$:
--
--   $$k=n\lambda+1,\quad w=\lceil\log(k+1)\rceil,\quad d=nw.$$
--
--   The field $\mathbb F=\mathbb F_{2^w}$ is identified with $\{0,1\}^w$ through the polynomial basis of the first irreducible polynomial of degree $w$ over $\mathbb F_2$ in a fixed order. Addition is XOR, multiplication is multiplication of polynomials modulo that polynomial, and $a^{-1}=a^{2^w-2}$ for $a\ne0$. The map $\pi:\mathbb F\to\mathbb F_2$ is the coefficient of 1, and $\alpha_i$ is the element whose coordinates form the binary representation of $i$, for $1\le i\le k$.
--
--   **Formalization Note** A monic polynomial of degree $w$ is ordered by the number formed by its lower coefficients. `sInf` on $\mathbb N$ gives the least such code; the set is nonempty since $w\ge1$. Mathlib's `GaloisField` has no fixed basis, so it is not used.
-- source:
--   Mantri, Private Information Retrieval from Two Entangled Servers, manuscript (Nov. 2026; sha256 5cfce27c…51384), (5.1), p.24; App. C.2, p.57

import Definitions.Def_EntangledPIR_Bits

/-!
Mantri, *Private Information Retrieval from Two Entangled Servers*, manuscript (Nov. 2026), (5.1),
p.24, and Appendix C.2, p.57: the parameters and the concrete field `F = F_{2^w}`.
-/

open Polynomial

namespace EntangledPIR

/-- `k = nλ + 1` of (5.1), p.24. -/
def shareCount (n lam : ℕ) : ℕ := n * lam + 1

/-- `w = ⌈log(k + 1)⌉` of (5.1), p.24, logarithms to base two. `Nat.clog 2 a` is the least `w` with
`a ≤ 2^w`. -/
def fieldWidth (n lam : ℕ) : ℕ := Nat.clog 2 (shareCount n lam + 1)

/-- `d = nw` of (5.1), p.24. -/
def queryLen (n lam : ℕ) : ℕ := n * fieldWidth n lam

/-- The polynomial `X^w + ∑_{i<w} c_i X^i` over `F₂`, with `c_i` the bits of the code `c`. Monic
polynomials of degree `w` are thereby ordered by their code. -/
noncomputable def polyOfCode (w c : ℕ) : (ZMod 2)[X] :=
  X ^ w + ∑ i : Fin w, if c.testBit i then X ^ (i : ℕ) else 0

/-- The code of the first irreducible polynomial of degree `w` over `F₂`, App. C.2, p.57.
**Formalization Note.** `sInf` on `ℕ` gives the least element of a nonempty set. The set is nonempty
for `w ≥ 1`, and `w ≥ 1` always holds here since `k + 1 ≥ 2`. -/
noncomputable def firstIrredCode (w : ℕ) : ℕ :=
  sInf {c : ℕ | c < 2 ^ w ∧ Irreducible (polyOfCode w c)}

/-- The first irreducible polynomial of degree `w` over `F₂` in the fixed order, App. C.2, p.57. -/
noncomputable def fieldModulus (w : ℕ) : (ZMod 2)[X] := polyOfCode w (firstIrredCode w)

/-- The polynomial with coordinates `b` in the polynomial basis `1, X, …, X^{w-1}`, App. C.2. -/
noncomputable def polyOfBits {w : ℕ} (b : Bits w) : (ZMod 2)[X] :=
  ∑ i : Fin w, if b i then X ^ (i : ℕ) else 0

/-- The first `w` coordinates of a polynomial. -/
noncomputable def bitsOfPoly (w : ℕ) (p : (ZMod 2)[X]) : Bits w :=
  fun i => decide (p.coeff i = 1)

/-- Multiplication of `F = F_{2^w}`, identified with `{0,1}^w` through the polynomial basis, App.
C.2, p.57. Addition is `bxor`. -/
noncomputable def fMul {w : ℕ} (a b : Bits w) : Bits w :=
  bitsOfPoly w ((polyOfBits a * polyOfBits b) %ₘ fieldModulus w)

/-- The element `1` of `F`, which is the first vector of the polynomial basis. -/
def fOne (w : ℕ) : Bits w := fun i => decide ((i : ℕ) = 0)

/-- Powers in `F`. -/
noncomputable def fPow {w : ℕ} (a : Bits w) : ℕ → Bits w
  | 0 => fOne w
  | e + 1 => fMul (fPow a e) a

/-- The inverse in `F`: `a⁻¹ = a^{2^w − 2}` for `a ≠ 0`, since `F^×` has order `2^w − 1`. -/
noncomputable def fInv {w : ℕ} (a : Bits w) : Bits w := fPow a (2 ^ w - 2)

/-- The product `∏_{i} f i` over a `Fin`, in `F`. -/
noncomputable def fProd {w s : ℕ} (f : Fin s → Bits w) : Bits w :=
  (List.ofFn f).foldr fMul (fOne w)

/-- `π : F → F₂`, the coefficient of `1` in the basis, p.24. -/
def fCoeffOne {w : ℕ} (a : Bits w) : Bool := if h : 0 < w then a ⟨0, h⟩ else false

/-- The inclusion `F₂ ⊆ F`. -/
def fOfBool (w : ℕ) (b : Bool) : Bits w := if b then fOne w else bzero w

/-- The point `α_i`, p.57: the element whose coordinates form the binary representation of `i`,
for `1 ≤ i ≤ k`. With `Fin k` zero-based, `i` of the paper is `i.val + 1`. -/
def alpha (w : ℕ) {k : ℕ} (i : Fin k) : Bits w := fun b => (i.val + 1).testBit b

end EntangledPIR


