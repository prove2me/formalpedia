-- Prove2me | Definitions.Def_CosDensity_Stream
-- name    : CosDensity_Stream
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:37:44.322861+00:00
-- url     : https://prove2.me/theorems/28ddc4de-8646-46ed-ad90-56d15452fffd
-- title:
--   Cosine densities $D_i$, density moments $M_p$, $(1+\epsilon)$-approximation and the stream class $\mathcal C(d,K)$
-- statement:
--   A **stream** is a finite sequence $P=(x_1,\dots,x_n)$ of vectors of a real inner product space. Each vector is normalized on arrival, $u_i=x_i/\|x_i\|_2$, and the **cosine density** of position $i$ is
--
--   $$D_i=\sum_{j=1}^n\langle u_i,u_j\rangle .$$
--
--   The **$p$-th density moment** is $M_p(P)=\sum_{i=1}^n D_i^p$ for an integer $p\ge 0$. Sums run over positions, so a vector that occurs several times in the stream counts once per occurrence.
--
--   For $X\ge 0$, a number $\widetilde X$ is a **$(1+\epsilon)$-approximation** to $X$ if $(1-\epsilon)X\le \widetilde X\le(1+\epsilon)X$.
--
--   A stream is in the **nonnegative-cosine regime** if $\langle u_i,u_j\rangle\ge 0$ for all $i,j$. For integers $d,K$, the class $\mathcal C(d,K)$ consists of the nonempty streams of unit vectors of $\mathbb R^d$ with pairwise nonnegative inner products, of length at most $d^K$, whose coordinates are rationals $a/b$ with $|a|\le d^K$ and $1\le b\le d^K$ (so each coordinate is written with $O(K\log d)$ bits). Finally $\rho_p=p^2(p-1)/(2(p^2-2))$.
--
--   These are the objects in which the paper's lower bound (Theorem 8.1) is stated.
--
--   **Formalization Note** Streams are Lean lists. For a zero vector the normalization formula returns $0$; the paper's streams consist of nonzero vectors, and every stream in $\mathcal C(d,K)$ is a unit stream.
-- source:
--   Q. Zhang, Frequency Moments Beyond Equality: Streaming Cosine Density Moments, arXiv:2609.06925 (held version, sha256 f4d4df22…), §3, p.12 (Computation Model and Problem Setup), p.13 (Conventions: (1+ϵ)-approximation, bit model); Theorem 8.1, pp.28–29 (ρ_p, length polynomial in d, O_p(log d) bits)

import Mathlib

open scoped RealInnerProductSpace

namespace CosDensity

/-!
# Streams of vectors, cosine densities and density moments

Q. Zhang, *Frequency Moments Beyond Equality: Streaming Cosine Density Moments*, arXiv:2609.06925
(held version, sha256 f4d4df22…), §3 "Computation Model and Problem Setup" and "Conventions",
pp.12–13 (pdf_page 13–14); Theorem 8.1, pp.28–29.

**Formalization Note.**
* A stream is a `List E` of vectors of a real inner product space `E`; positions are `Fin P.length`,
  so a vector that occurs several times counts once per occurrence (sums run over positions).
* Every vector is normalized on arrival, `u_i = ‖x_i‖⁻¹ • x_i`, as on p.12. The paper's streams
  consist of nonzero vectors; for a zero vector the formula gives `0`. All streams used in the
  lower bound are unit streams, where normalization is the identity.
* The exponent `p` of the moment is a natural number (§8 treats integers `p > 2`).
* `IsApprox ε X Y` is the paper's "`Y` is a (1+ε)-approximation to `X`" (p.13).
* The stream class `InClass d K` encodes "unit vectors in ℝ^d with pairwise nonnegative cosine
  similarities", "length polynomial in d" (length ≤ d^K) and "coordinates representable with
  O(log d) bits" (each coordinate is a/b with |a| ≤ d^K and 1 ≤ b ≤ d^K), as in Theorem 8.1.
-/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The normalized vector `u = x / ‖x‖₂` (p.12). -/
noncomputable def unitize (x : E) : E := ‖x‖⁻¹ • x

/-- The cosine density `D_i = Σ_j ⟨u_i, u_j⟩` of position `i` in a stream `x : Fin n → E` of
length `n`, with `u_j = x_j / ‖x_j‖` (p.12, `D_i := D_i(n)`). -/
noncomputable def densityF {n : ℕ} (x : Fin n → E) (i : Fin n) : ℝ :=
  ∑ j : Fin n, ⟪unitize (x i), unitize (x j)⟫

/-- The cosine density of position `i` of a stream given as a list. -/
noncomputable def density (P : List E) (i : Fin P.length) : ℝ :=
  densityF P.get i

/-- The `p`-th cosine density moment `M_p(P) = Σ_i D_i^p` (p.12), over positions. -/
noncomputable def moment (p : ℕ) (P : List E) : ℝ :=
  ∑ i : Fin P.length, density P i ^ p

/-- `Y` is a `(1+ε)`-approximation to `X`: `(1 − ε) X ≤ Y ≤ (1 + ε) X` (p.13). -/
def IsApprox (ε X Y : ℝ) : Prop :=
  (1 - ε) * X ≤ Y ∧ Y ≤ (1 + ε) * X

/-- Every vector of the stream is a unit vector. -/
def IsUnitStream (P : List E) : Prop :=
  ∀ x ∈ P, ‖x‖ = 1

/-- The nonnegative-cosine regime (p.12): `⟨u_i, u_j⟩ ≥ 0` for every pair of stream vectors. -/
def NonnegCosine (P : List E) : Prop :=
  ∀ x ∈ P, ∀ y ∈ P, 0 ≤ ⟪unitize x, unitize y⟫

/-- Every coordinate of every stream vector is a rational `a / b` with `|a| ≤ H` and
`1 ≤ b ≤ H` (so it is written with `O(log H)` bits). -/
def IsBitBounded {d : ℕ} (H : ℕ) (P : List (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∀ x ∈ P, ∀ k : Fin d, ∃ a : ℤ, ∃ b : ℕ, 1 ≤ b ∧ |a| ≤ (H : ℤ) ∧ b ≤ H ∧ x k = (a : ℝ) / b

/-- The stream class `𝒞(d, K)` of Theorem 8.1: nonempty streams of unit vectors of `ℝ^d` with
pairwise nonnegative cosine similarities, of length at most `d^K`, whose coordinates are
rationals with numerator and denominator bounded by `d^K` in absolute value. -/
def InClass (d K : ℕ) (P : List (EuclideanSpace ℝ (Fin d))) : Prop :=
  P ≠ [] ∧ IsUnitStream P ∧ NonnegCosine P ∧ P.length ≤ d ^ K ∧ IsBitBounded (d ^ K) P

/-- The exponent `ρ_p = p²(p − 1) / (2(p² − 2))` of Theorem 8.1. -/
noncomputable def rho (p : ℕ) : ℝ :=
  (p : ℝ) ^ 2 * ((p : ℝ) - 1) / (2 * ((p : ℝ) ^ 2 - 2))

end CosDensity


