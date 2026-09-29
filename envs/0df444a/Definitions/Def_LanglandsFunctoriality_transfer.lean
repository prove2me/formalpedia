-- Prove2me | Definitions.Def_LanglandsFunctoriality_transfer
-- name    : LanglandsFunctoriality_transfer
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-14T15:42:56.101419+00:00
-- url     : https://prove2.me/theorems/c00be4cf-c24b-4d3a-872b-c0d4ad445157
-- title:
--   Polynomial $L$-homomorphisms $GL(n,\mathbb{C})\to GL(N,\mathbb{C})$ and Satake transfer
-- statement:
--   For $H=GL(n)$ and $G=GL(N)$ the dual groups are $GL(n,\mathbb C)$ and $GL(N,\mathbb C)$, and an
--   $L$-homomorphism is a holomorphic homomorphism $r:GL(n,\mathbb C)\to GL(N,\mathbb C)$. Every such
--   homomorphism is rational, and after twisting by a power of the determinant it is **polynomial**:
--   its matrix entries are polynomial functions of the entries of the argument. This file records
--   polynomial representations in that sense — a unital multiplicative map on $n\times n$ complex
--   matrices whose entries are polynomials in the entries of the argument — and the matching condition
--   that defines a functorial transfer.
--
--   Given such an $r$, a datum $\pi$ of rank $n$ and a datum $\Pi$ of rank $N$, we say that $\Pi$ is a
--   **transfer** of $\pi$ along $r$ if there is a finite set $S$ of primes such that for every prime
--   $p\notin S$,
--
--   $$\det\bigl(X\cdot\mathrm{Id} - r(\operatorname{diag}(\alpha_{p,1},\dots,\alpha_{p,n}))\bigr)
--   =\prod_{j=1}^{N}\bigl(X-\beta_{p,j}\bigr),$$
--
--   where $\beta_{p,\bullet}$ are the Satake parameters of $\Pi$. This is the condition
--   $c(\Pi_p)=r(c(\pi_p))$ of the survey's equation (5.1), recorded as an equality of characteristic
--   polynomials, which is exactly equality of the two semisimple conjugacy classes and imposes no
--   ordering on the parameters.
--
--   The file also records the Satake multisets of the three lifts the survey singles out: the
--   symmetric power multiset $\{a^{m},a^{m-1}b,\dots,b^{m}\}$ of a rank-two datum, the tensor product
--   multiset $\{\alpha_i\beta_j\}$, and the exterior square multiset $\{\alpha_i\alpha_j : i<j\}$;
--   together with the predicate saying that a datum has a prescribed Satake multiset outside a finite
--   set of primes.
-- source:
--   J.-H. Yang, Langlands Functoriality Conjecture, arXiv:0808.0917 (2008), https://arxiv.org/abs/0808.0917, p. 17, Section 5, 'Langlands Functoriality Conjecture', equation (5.1)

import Mathlib
import Definitions.Def_LanglandsFunctoriality_automorphic_data

/-!
# `L`-homomorphisms between the dual groups of general linear groups, and Satake transfer

For `H = GL(n)` and `G = GL(N)` the `L`-groups are `GL(n, ℂ)` and `GL(N, ℂ)`, and an
`L`-homomorphism is a holomorphic homomorphism `r : GL(n, ℂ) → GL(N, ℂ)`.  Such a
homomorphism is *rational*, and after a twist by a power of the determinant it is
*polynomial*: its matrix entries are polynomials in the entries of the argument.  This file
records polynomial representations, and the Satake matching condition
`c(Πᵥ) = r(c(πᵥ))` that defines the functorial transfer at the unramified places.
-/

namespace LanglandsFunctoriality

open Polynomial

/-- A polynomial representation of the multiplicative monoid of `n × n` complex matrices in
dimension `N`: a multiplicative, unital map whose entries are polynomial functions of the
entries of the argument.  Restricted to `GL(n, ℂ)` these are exactly the `L`-homomorphisms
`GL(n, ℂ) → GL(N, ℂ)` that are polynomial (every holomorphic one becomes polynomial after a
twist by a power of the determinant). -/
structure PolyRep (n N : ℕ) where
  /-- The underlying map on matrices. -/
  toFun : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin N) (Fin N) ℂ
  map_one : toFun 1 = 1
  map_mul : ∀ A B : Matrix (Fin n) (Fin n) ℂ, toFun (A * B) = toFun A * toFun B
  isPolynomial : ∀ i j : Fin N, ∃ P : MvPolynomial (Fin n × Fin n) ℂ,
      ∀ A : Matrix (Fin n) (Fin n) ℂ,
        toFun A i j = MvPolynomial.eval (fun ij : Fin n × Fin n => A ij.1 ij.2) P

/-- `Π` is a functorial transfer of `π` along `r`: outside a finite set of primes, the Satake
class of `Π` at `p` is the image under `r` of the Satake class of `π` at `p`.  Equality of
semisimple conjugacy classes is recorded as equality of characteristic polynomials. -/
def IsTransfer {n N : ℕ} (r : PolyRep n N) (π : LData n) (Pi : LData N) : Prop :=
  ∃ S : Finset ℕ, ∀ p : ℕ, p.Prime → p ∉ S →
    (r.toFun (Matrix.diagonal (π.satake p))).charpoly = ∏ j : Fin N, (X - C (Pi.satake p j))

/-- `Π` has the Satake parameters prescribed by the multiset `α : ι → ℂ` outside a finite set
of primes: the local Euler factors of `Π` are `∏ᵢ (1 - α i · X)`. -/
def HasSatakeMultiset {N : ℕ} (Pi : LData N) (α : ℕ → Multiset ℂ) : Prop :=
  ∃ S : Finset ℕ, ∀ p : ℕ, p.Prime → p ∉ S →
    (∏ j : Fin N, (X - C (Pi.satake p j))) = ((α p).map fun z => X - C z).prod

/-- The Satake parameters of the `m`-th symmetric power lift of a `GL(2)` datum with
parameters `(a, b)`: the multiset `{aᵐ, a^{m-1} b, …, bᵐ}`. -/
noncomputable def symMultiset (m : ℕ) (a b : ℂ) : Multiset ℂ :=
  (Multiset.range (m + 1)).map fun i => a ^ (m - i) * b ^ i

/-- The Satake parameters of the tensor product lift of two data with parameters `α` and `β`:
the multiset `{αᵢ βⱼ}`. -/
noncomputable def tensorMultiset {m n : ℕ} (α : Fin m → ℂ) (β : Fin n → ℂ) : Multiset ℂ :=
  (Finset.univ : Finset (Fin m × Fin n)).val.map fun ij => α ij.1 * β ij.2

/-- The Satake parameters of the exterior square lift of a datum with parameters `α`: the
multiset `{αᵢ αⱼ : i < j}`. -/
noncomputable def extSquareMultiset {n : ℕ} (α : Fin n → ℂ) : Multiset ℂ :=
  ((Finset.univ : Finset (Fin n × Fin n)).filter fun ij => ij.1 < ij.2).val.map
    fun ij => α ij.1 * α ij.2

end LanglandsFunctoriality


