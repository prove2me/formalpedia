-- Prove2me | Definitions.Def_ExtremalForrelation_Nonadaptive_Basic
-- name    : ExtremalForrelation_Nonadaptive_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:54:45.383214+00:00
-- url     : https://prove2.me/theorems/8ebefe2c-898e-4aed-aca2-e618474dd208
-- title:
--   The space $\mathbb F_2^n$, its binary pairing, orthogonal complements, Fourier transform, forrelation and bent functions
-- statement:
--   Let $n\ge 0$ and $V=\mathbb F_2^n$, the vectors $x=(x_1,\dots,x_n)$ with entries in $\mathbb F_2$ and coordinatewise addition. The **binary pairing** is
--   $$\langle x,y\rangle=\sum_{k=1}^n x_ky_k\in\mathbb F_2 .$$
--   It is bilinear and nondegenerate but not an inner product: a nonzero vector can be orthogonal to itself. For a subspace $W$, its **orthogonal complement** is $W^\perp=\{y:\langle x,y\rangle=0\text{ for all }x\in W\}$.
--
--   1. **Subspaces of half dimension.** $\mathrm{Gr}(n)$ is the finite set of subspaces $K\le\mathbb F_2^n$ with $\dim K=m=\lfloor n/2\rfloor$ (the paper always has $4\mid n$, so $m=n/2$).
--   2. **Representatives.** A vector is read as the binary number $\sum_k x_k2^{n-k}$ (first coordinate most significant). The representative of a coset of $W$ is its element with the smallest binary value.
--   3. **Uniform averages.** For a finite set $A$ and $F:A\to\mathbb R$, $\mathrm{avg}_A F=|A|^{-1}\sum_{a\in A}F(a)$; the uniform probability of an event $P$ is $\mathrm{avg}_A\mathbf 1_P$.
--   4. **Total variation** of two functions $\mu,\nu$ on a finite set: $\|\mu-\nu\|_{TV}=\tfrac12\sum_a|\mu(a)-\nu(a)|$.
--   5. **Characters and Fourier transform.** For $f:\mathbb F_2^n\to\mathbb F_2$, $\chi_f=(-1)^f$. For $F:\mathbb F_2^n\to\mathbb R$,
--   $$\widehat F(y)=2^{-n}\sum_{x\in\mathbb F_2^n}F(x)(-1)^{\langle x,y\rangle}.$$
--   6. **Forrelation** of $F,G$: $\mathrm{forr}(F,G)=2^{-n/2}\sum_x\widehat F(x)G(x)$.
--   7. **Bent functions.** $F$ is bent if $|\widehat F(y)|=2^{-n/2}$ for every $y$.
--
--   These are the objects of the paper's notation paragraph (p. 3) and Definitions 1–3 (p. 7) and 5 (p. 8). The construction, the transcript laws and all lemmas are stated in terms of them.
--
--   **Formalization Note.** $\mathbb F_2^n$ is `Fin n → ZMod 2`, the pairing is `dot`, and $W^\perp$ is the submodule `orth W` (defined directly for this pairing). $2^{-n/2}$ is a real power. The finite set of half-dimensional subspaces carries a (noncomputable) `Fintype` instance, as do the quotients `V n ⧸ W`. `minBin` returns `0` on an empty set; it is only applied to nonempty sets.
-- source:
--   Clément Canonne, Kenny Chen, Julian Mestre, STOC 2027 submission #61 (October 2026), p. 3 (Notation), p. 4 (representatives, footnote 3), p. 7 (Definitions 1–3), p. 8 (Definition 5), p. 9 (uniform m-dimensional subspace), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/61.pdf

import Mathlib

open Classical

noncomputable section

namespace ExtremalForrelation.Nonadaptive

/-!
# Extremal Forrelation: the binary space, Fourier analysis and finite averages

Canonne–Chen–Mestre, *The Quantumly Fast and the Classically Forrious*, STOC 2027 submission #61
(October 2026), p. 3 (Notation), p. 4 (§1.1.1, representatives), p. 7 (Definitions 1–3),
p. 8 (Definition 5, orthogonal complement), p. 9 (uniform `m`-dimensional subspace).

`V n = 𝔽₂ⁿ` is the type of all functions `Fin n → ZMod 2`, with coordinatewise addition.
`dot x y = ∑ₖ xₖ yₖ ∈ 𝔽₂` is the binary pairing (not a real inner product: isotropic vectors
exist). `orth W` is the orthogonal complement of a subspace for this pairing.
-/

/-- The space `𝔽₂ⁿ`. -/
abbrev V (n : ℕ) : Type := Fin n → ZMod 2

/-- The pairing `⟨x, y⟩ = ∑_{k=1}^n x_k y_k`, computed in `𝔽₂` (p. 3). -/
def dot {n : ℕ} (x y : V n) : ZMod 2 := ∑ k, x k * y k

/-- The orthogonal complement `W^⊥ = {y : ⟨x, y⟩ = 0 for all x ∈ W}` for the binary pairing. -/
def orth {n : ℕ} (W : Submodule (ZMod 2) (V n)) : Submodule (ZMod 2) (V n) where
  carrier := {y | ∀ x ∈ W, dot x y = 0}
  add_mem' := by
    intro a b ha hb x hx
    have h1 := ha x hx
    have h2 := hb x hx
    simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib] at h1 h2 ⊢
    rw [h1, h2, add_zero]
  zero_mem' := by
    intro x _
    simp [dot]
  smul_mem' := by
    intro c a ha x hx
    have h1 := ha x hx
    simp only [dot, Pi.smul_apply, smul_eq_mul] at h1 ⊢
    calc ∑ k, x k * (c * a k) = c * ∑ k, x k * a k := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun k _ => by ring)
      _ = 0 := by rw [h1, mul_zero]

/-- `m`-dimensional subspaces of `𝔽₂ⁿ` with `m = n/2` (the sample space of `K`, p. 4). -/
def Grass (n : ℕ) : Type := {K : Submodule (ZMod 2) (V n) // Module.finrank (ZMod 2) K = n / 2}

instance (n : ℕ) : Finite (Submodule (ZMod 2) (V n)) :=
  Finite.of_injective (fun p : Submodule (ZMod 2) (V n) => (p : Set (V n))) SetLike.coe_injective

instance (n : ℕ) : Fintype (Grass n) := by
  unfold Grass; exact Fintype.ofFinite _

instance (n : ℕ) (W : Submodule (ZMod 2) (V n)) : Fintype (V n ⧸ W) := Fintype.ofFinite _

/-- The value of a vector read as a binary number, first coordinate most significant. -/
def binVal {n : ℕ} (x : V n) : ℕ := ∑ k : Fin n, (x k).val * 2 ^ (n - 1 - k.val)

/-- The element of a nonempty finite set of vectors with the smallest binary value
(`0` for the empty set; only used on nonempty sets). -/
def minBin {n : ℕ} (s : Finset (V n)) : V n :=
  if h : s.Nonempty then (s.exists_min_image binVal h).choose else 0

/-- The representative of a coset `c` of `W`: its smallest element, reading vectors as binary
numbers (p. 4, item 1). -/
def rep {n : ℕ} (W : Submodule (ZMod 2) (V n)) (c : V n ⧸ W) : V n :=
  minBin (Finset.univ.filter (fun x : V n => Submodule.Quotient.mk x = c))

/-- Uniform average of a real function over a finite type. -/
def uavg (α : Type*) [Fintype α] (f : α → ℝ) : ℝ := (∑ a, f a) / Fintype.card α

/-- Probability of an event under the uniform distribution on a finite type. -/
def uprob {α : Type*} [Fintype α] (P : α → Prop) : ℝ := uavg α (fun a => if P a then 1 else 0)

/-- Total variation distance `½ ∑_τ |μ(τ) − ν(τ)|` of two functions on a finite type (p. 3). -/
def tv {α : Type*} [Fintype α] (μ ν : α → ℝ) : ℝ := (1 / 2) * ∑ a, |μ a - ν a|

/-- The `{−1, 1}`-valued function `χ_f = (−1)^f` of `f : 𝔽₂ⁿ → 𝔽₂` (p. 3). -/
def chi {n : ℕ} (f : V n → ZMod 2) : V n → ℝ := fun x => (-1 : ℝ) ^ (f x).val

/-- Definition 1 (p. 7): `F̂(y) = 2^{−n} ∑_x F(x) (−1)^{⟨x,y⟩}`. -/
def fourier {n : ℕ} (F : V n → ℝ) (y : V n) : ℝ :=
  ((2 : ℝ) ^ n)⁻¹ * ∑ x, F x * (-1 : ℝ) ^ (dot x y).val

/-- Definition 2 (p. 7): `forr(F, G) = 2^{−n/2} ∑_x F̂(x) G(x)`. -/
def forr {n : ℕ} (F G : V n → ℝ) : ℝ :=
  (2 : ℝ) ^ (-(n : ℝ) / 2) * ∑ x, fourier F x * G x

/-- Definition 3 (p. 7): `F` is bent if `|F̂(y)| = 2^{−n/2}` for every `y`. -/
def IsBent {n : ℕ} (F : V n → ℝ) : Prop :=
  ∀ y, |fourier F y| = (2 : ℝ) ^ (-(n : ℝ) / 2)

end ExtremalForrelation.Nonadaptive


