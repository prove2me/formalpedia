-- Prove2me | Definitions.Def_PlantedIQP_CubicPoly
-- name    : PlantedIQP_CubicPoly
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:18:28.317227+00:00
-- url     : https://prove2.me/theorems/cba30668-e272-428a-86a4-1917007bc577
-- title:
--   Cubic Boolean polynomials over $\mathbb F_2$ with constant term $0$
-- statement:
--   A **cubic Boolean polynomial** in $n$ variables with constant term $0$ is
--
--   $$
--   f(x)=\sum_{1\le i<j<k\le n}F_{ijk}\,x_ix_jx_k+\sum_{1\le i<j\le n}F_{ij}\,x_ix_j+\sum_{1\le i\le n}F_i\,x_i ,\qquad x\in\mathbb F_2^n,
--   $$
--
--   with coefficients $F_{ijk},F_{ij},F_i\in\mathbb F_2$ and all arithmetic modulo $2$. Since $x^2=x$ on $\mathbb F_2$, functions are identified with their unique multilinear representatives, so a polynomial is exactly its coefficient record. The module also provides evaluation $f(x)$, the coefficientwise sum of two polynomials, the cubic part $f^{(3)}$ and the lower-degree part $f^{(2)}+f^{(1)}$, the coefficient $F_{ijk}$ read for any order of three distinct indices (and $0$ on coinciding indices), the linear polynomial $y\mapsto\langle x,y\rangle$ and the standard basis vectors $e_i$.
--
--   These are the instances of every statement of the mission: the IQP circuit $C(f)$ acts as $C(f)|x\rangle=(-1)^{f(x)}|x\rangle$.
--
--   **Formalization Note** $\mathbb F_2$ is `ZMod 2` and $\mathbb F_2^n$ is `Fin n → ZMod 2`. The coefficient $F_{ijk}$ is indexed by the 3-element set $\{i,j,k\}$, $F_{ij}$ by the 2-element set, so distinct records are distinct polynomials and the uniform law on records is the uniform law on polynomials.
-- source:
--   Bläser, Gullans, Hangleiter, Liu, Qiao, Verifiable quantum advantage based on polynomials with planted structures, arXiv:2609.39918 (sha256 6e261694…), Eq. (1), p.4 and Section 2.1, Eq. (11), p.13

import Mathlib

set_option autoImplicit false

namespace PlantedIQP

/-!
# Cubic Boolean polynomials with constant term 0

M. Bläser, M. Gullans, D. Hangleiter, Y. Liu, Y. Qiao, *Verifiable quantum advantage based on
polynomials with planted structures*, arXiv:2609.39918 (sha256 6e261694…), Eq. (1), p.4 and
Section 2.1, Eq. (11), p.13:

  f(x) = Σ_{1≤i<j<k≤n} F_{ijk} x_i x_j x_k + Σ_{1≤i<j≤n} F_{ij} x_i x_j + Σ_{1≤i≤n} F_i x_i,

all arithmetic modulo 2, functions identified with their unique multilinear representatives.

**Formalization Note.**
* 𝔽₂ is `ZMod 2` and vectors of 𝔽₂ⁿ are `Vec n = Fin n → ZMod 2`; the source's index `i ∈ [n]` is
  `i : Fin n` (shifted by one).
* A polynomial is its coefficient record: `c3` on the 3-element subsets `{i, j, k}` of `Fin n`
  (the monomial `x_i x_j x_k`, `i < j < k`), `c2` on the 2-element subsets, `c1` on the indices.
  Distinct records are distinct multilinear polynomials, so the uniform distribution on records is
  the source's uniform distribution on polynomials. There is no constant term (p.4: "we work with
  cubic polynomials with constant term 0 unless otherwise stated").
* `coeff3 f i j k` is `F_{ijk}` read for any ordering of distinct `i, j, k` and `0` when two indices
  coincide; `coeff2 f i j` likewise for `F_{ij}`.
* `cubicPart` is `f^{(3)}`, `lowerPart` is `f^{(2)} + f^{(1)}`; `linear x` is the polynomial
  `y ↦ ⟨x, y⟩`. Addition is coefficientwise (sum of polynomials over 𝔽₂).
-/

/-- Vectors of 𝔽₂ⁿ. -/
abbrev Vec (n : ℕ) := Fin n → ZMod 2

/-- The multilinear monomials of degree `d` in `n` variables, as `d`-element index sets. -/
abbrev Mono (n d : ℕ) := {S : Finset (Fin n) // S.card = d}

/-- A cubic Boolean polynomial in `n` variables with constant term `0`, given by its coefficients
`F_{ijk}` (`c3`), `F_{ij}` (`c2`) and `F_i` (`c1`) (Bläser et al., Eq. (11), p.13). -/
@[ext] structure CubicPoly (n : ℕ) where
  /-- `F_{ijk}`, the coefficient of `x_i x_j x_k` for the index set `{i, j, k}`. -/
  c3 : Mono n 3 → ZMod 2
  /-- `F_{ij}`, the coefficient of `x_i x_j` for the index set `{i, j}`. -/
  c2 : Mono n 2 → ZMod 2
  /-- `F_i`, the coefficient of `x_i`. -/
  c1 : Fin n → ZMod 2

namespace CubicPoly

variable {n : ℕ}

/-- The coefficient record as a triple of functions. -/
def equivTriple (n : ℕ) :
    CubicPoly n ≃ (Mono n 3 → ZMod 2) × (Mono n 2 → ZMod 2) × (Fin n → ZMod 2) where
  toFun f := (f.c3, f.c2, f.c1)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype (CubicPoly n) := Fintype.ofEquiv _ (equivTriple n).symm

instance : DecidableEq (CubicPoly n) := (equivTriple n).decidableEq

instance : Zero (CubicPoly n) := ⟨⟨0, 0, 0⟩⟩

instance : Nonempty (CubicPoly n) := ⟨0⟩

/-- Coefficientwise sum: the sum of two polynomials over 𝔽₂. -/
instance : Add (CubicPoly n) := ⟨fun f g => ⟨f.c3 + g.c3, f.c2 + g.c2, f.c1 + g.c1⟩⟩

/-- Evaluation `f(x)` of the multilinear polynomial at `x ∈ 𝔽₂ⁿ` (Eq. (11)). -/
def eval (f : CubicPoly n) (x : Vec n) : ZMod 2 :=
  (∑ S : Mono n 3, f.c3 S * ∏ i ∈ S.1, x i) + (∑ S : Mono n 2, f.c2 S * ∏ i ∈ S.1, x i) +
    ∑ i, f.c1 i * x i

/-- `F_{ijk}` for pairwise distinct `i, j, k` (any order), and `0` if two indices coincide. -/
def coeff3 (f : CubicPoly n) (i j k : Fin n) : ZMod 2 :=
  if h : ({i, j, k} : Finset (Fin n)).card = 3 then f.c3 ⟨_, h⟩ else 0

/-- `F_{ij}` for `i ≠ j` (either order), and `0` if `i = j`. -/
def coeff2 (f : CubicPoly n) (i j : Fin n) : ZMod 2 :=
  if h : ({i, j} : Finset (Fin n)).card = 2 then f.c2 ⟨_, h⟩ else 0

/-- The cubic part `f^{(3)}`: the degree-3 monomials of `f` only. -/
def cubicPart (f : CubicPoly n) : CubicPoly n := ⟨f.c3, 0, 0⟩

/-- The lower-degree part `f^{(2)} + f^{(1)}`: the quadratic and linear monomials of `f`. -/
def lowerPart (f : CubicPoly n) : CubicPoly n := ⟨0, f.c2, f.c1⟩

end CubicPoly

/-- The linear polynomial `y ↦ ⟨x, y⟩ = Σ_i x_i y_i`. -/
def linear {n : ℕ} (x : Vec n) : CubicPoly n := ⟨0, 0, x⟩

/-- The standard basis vector `e_i` of 𝔽₂ⁿ. -/
def stdBasis {n : ℕ} (i : Fin n) : Vec n := Pi.single i 1

end PlantedIQP


