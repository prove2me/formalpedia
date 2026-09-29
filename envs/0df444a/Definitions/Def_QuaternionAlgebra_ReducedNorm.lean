-- Prove2me | Definitions.Def_QuaternionAlgebra_ReducedNorm
-- name    : QuaternionAlgebra_ReducedNorm
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/b79c86a6-f830-5df2-a760-b8d602b33567
-- title:
--   Reduced norm and trace on a generalised quaternion algebra
-- statement:
--   Fix a commutative ring $R$ and elements $a, b \in R$, and let $\mathbb{H}[R,a,b]$ be the generalised quaternion algebra, free of rank $4$ on $1, i, j, k$ with $i^2 = a$, $j^2 = b$, $k = ij = -ji$. Two functions on this algebra are defined. The reduced norm [`QuaternionAlgebra.nrd`](../def/QuaternionAlgebra_ReducedNorm.html#L11) sends $x$ with coordinates $(x_{\mathrm{re}}, x_{\mathrm{imI}}, x_{\mathrm{imJ}}, x_{\mathrm{imK}})$ to the value of the quaternary quadratic form
--   $$\mathrm{nrd}(x) = x_{\mathrm{re}}^2 - a\,x_{\mathrm{imI}}^2 - b\,x_{\mathrm{imJ}}^2 + ab\,x_{\mathrm{imK}}^2 \in R,$$
--   and the reduced trace [`QuaternionAlgebra.trd`](../def/QuaternionAlgebra_ReducedNorm.html#L14) sends $x$ to $2x_{\mathrm{re}}$. Both are plain $R$-valued functions, rather than bundled as a quadratic form, a monoid homomorphism or a linear map, and multiplicativity of the norm is left for elsewhere.
--
--   The accompanying lemmas record the values on a quadruple of coordinates, and that $\mathrm{nrd}$ vanishes at $0$, takes the value $1$ at $1$, is invariant under $x \mapsto -x$ and under the quaternion conjugation $\mathrm{star}$, and takes a scalar $r$ (viewed in $\mathbb{H}[R,a,b]$) to $r^2$. The three identities `mul_star_eq_coe_nrd`, `star_mul_eq_coe_nrd` and `add_star_eq_coe_trd` state that $x\,\bar{x}$ and $\bar{x}\,x$ both equal the image of $\mathrm{nrd}(x)$ under the structure map $R \to \mathbb{H}[R,a,b]$, and that $x + \bar{x}$ equals the image of $\mathrm{trd}(x)$; thus the two functions are the norm and trace of the degree-two relation satisfied by every element over the centre, with the conjugate $\bar{x}$ given by Mathlib's `star` on the quaternion algebra.
--
--   **Relation to Mathlib.** Mathlib supplies the algebra $\mathbb{H}[R,a,b]$ together with its conjugation `star`; the norm form `nrd` and trace `trd` for general parameters $a, b$ over an arbitrary commutative ring, with the identities $x\bar x = \bar x x = \mathrm{nrd}(x)$ and $x + \bar x = \mathrm{trd}(x)$, are introduced here under the `QuaternionAlgebra` namespace.
--
--   **Where it is used.** The reduced norm is the quadratic form in which orders and ideals in definite quaternion algebras are handled, and these basic identities underlie the construction of Brandt matrices and the quaternionic automorphic forms used on the Jacquet–Langlands side of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_QuaternionAlgebra_ReducedNorm.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Quaternion

namespace QuaternionAlgebra

section ReducedNorm

variable {R : Type*} [CommRing R] {a b : R}

def nrd (x : ℍ[R, a, b]) : R :=
  x.re ^ 2 - a * x.imI ^ 2 - b * x.imJ ^ 2 + a * b * x.imK ^ 2

def trd (x : ℍ[R, a, b]) : R := 2 * x.re

@[simp] theorem nrd_mk (x₀ x₁ x₂ x₃ : R) :
    nrd (⟨x₀, x₁, x₂, x₃⟩ : ℍ[R, a, b]) = x₀ ^ 2 - a * x₁ ^ 2 - b * x₂ ^ 2 + a * b * x₃ ^ 2 := rfl

@[simp] theorem trd_mk (x₀ x₁ x₂ x₃ : R) :
    trd (⟨x₀, x₁, x₂, x₃⟩ : ℍ[R, a, b]) = 2 * x₀ := rfl

@[simp] theorem nrd_zero : nrd (0 : ℍ[R, a, b]) = 0 := by simp [nrd]
@[simp] theorem nrd_one : nrd (1 : ℍ[R, a, b]) = 1 := by simp [nrd]
@[simp] theorem nrd_neg (x : ℍ[R, a, b]) : nrd (-x) = nrd x := by simp [nrd]
@[simp] theorem nrd_star (x : ℍ[R, a, b]) : nrd (star x) = nrd x := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x; simp only [star_mk, nrd_mk]; ring
@[simp] theorem nrd_coe (r : R) : nrd ((r : R) : ℍ[R, a, b]) = r ^ 2 := by simp [nrd]

theorem mul_star_eq_coe_nrd (x : ℍ[R, a, b]) : x * star x = ((nrd x : R) : ℍ[R, a, b]) := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  ext <;> simp only [star_mk, mk_mul_mk, nrd_mk, re_coe, imI_coe, imJ_coe, imK_coe] <;> ring

theorem star_mul_eq_coe_nrd (x : ℍ[R, a, b]) : star x * x = ((nrd x : R) : ℍ[R, a, b]) := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  ext <;> simp only [star_mk, mk_mul_mk, nrd_mk, re_coe, imI_coe, imJ_coe, imK_coe] <;> ring

theorem add_star_eq_coe_trd (x : ℍ[R, a, b]) : x + star x = ((trd x : R) : ℍ[R, a, b]) := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  ext <;> simp only [star_mk, mk_add_mk, trd_mk, re_coe, imI_coe, imJ_coe, imK_coe] <;> ring

end ReducedNorm

end QuaternionAlgebra


