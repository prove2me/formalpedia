-- Prove2me | Definitions.Def_NMAffExt_LBP_NonMalleable
-- name    : NMAffExt_LBP_NonMalleable
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T04:28:34.082843+00:00
-- url     : https://prove2.me/theorems/50ae7dbd-7d25-4c6b-ac2f-ce6d428cf490
-- title:
--   $(k,\varepsilon)$ non-malleable affine extractors, and non-malleability against globally fixed-point-free affine involutions
-- statement:
--   An **affine source** on $n$ bits is the uniform distribution on an affine subspace $x_0+V$ of $\mathbb F_2^n$; its dimension $\dim V$ equals its min-entropy $H_\infty(X)=-\log_2\max_x\Pr[X=x]$. An **affine map** $T:\mathbb F_2^n\to\mathbb F_2^n$ has the form $T(x)=Mx+b$ (not necessarily invertible). For distributions $P,Q$ on a finite set, the statistical distance is $\Delta(P,Q)=\frac12\sum_\omega|P(\omega)-Q(\omega)|$.
--
--   **Definition 1.1.** $F:\mathbb F_2^n\to\mathbb F_2^m$ is a **$(k,\varepsilon)$ non-malleable affine extractor** if for every affine source $X$ of dimension at least $k$ and every affine map $T$ with $T(x)\neq x$ for every $x\in\mathbb F_2^n$,
--   $$\Delta\bigl((F(X),F(T(X))),\ (U_m,F(T(X)))\bigr)\le\varepsilon,$$
--   where on the right $U_m$ is uniform on $\mathbb F_2^m$ and independent of $F(T(X))$.
--
--   $F$ is **$(k,\varepsilon)$ non-malleable against globally fixed-point-free affine involutions** if the same inequality holds for every affine source of dimension at least $k$ and every affine $T$ with $T(T(x))=x$ and $T(x)\ne x$ for every $x\in\mathbb F_2^n$. Every $(k,\varepsilon)$ non-malleable affine extractor has this property (the structural lemma `IsNMAffExt.toInv`); the paper's Lemma 4.4, Theorem 4.11, Lemma A.3, Theorem A.4 and Theorem 1.6 all state that it suffices.
--
--   **Formalization Note.** Affine sources, affine maps and $U_m$ are the published `QuadExt.Main.IsAffineSource`, `QuadExt.Main.IsAffineMap` and `QuadExt.Main.unif`; "dimension at least $k$" is `(k : ℝ) ≤ SSNonExt.minEntropy P`; $\Delta$ is the published `SSNonExt.TV`. `nmError F P T` is the distance between the law of $(F(X),F(T(X)))$, $X\sim P$, and `prodLaw (unif (Fin m)) (law of F(T(X)))`, the product law. The definitions are `IsNMAffExt k ε F` and `IsNMAffExtInv k ε F`.
-- source:
--   Xin Li, Yan Zhong, Non-Malleable Affine Extractors with Small Error and Complexity Lower Bounds, arXiv:2610.02407 (version of 2026-11-02, sha256 e80dad4d…), p. 4 (PDF 6), Definition 1.1; p. 22 (PDF 24), Definition 2.10 (t = 1); p. 6 (PDF 8), last sentence of Theorem 1.6

import Mathlib
import Definitions.Def_QuadExt_Main_Sources
import Definitions.Def_SSNonExt_TV

/-!
# Non-malleable affine extractors, and non-malleability against affine involutions

Xin Li, Yan Zhong, *Non-Malleable Affine Extractors with Small Error and Complexity Lower Bounds*,
arXiv:2610.02407 (version of 2026-11-02, sha256 e80dad4d…), p. 4 (PDF 6), Definition 1.1;
p. 22 (PDF 24), Definition 2.10 with t = 1; p. 6 (PDF 8), last sentence of Theorem 1.6.

"A function F : 𝔽₂ⁿ → 𝔽₂ᵐ is a (k, ε) non-malleable affine extractor if, for every affine source X
of dimension at least k and every affine map T : 𝔽₂ⁿ → 𝔽₂ⁿ with no fixed points,
(F(X), F(T(X))) ≈ε (U_m, F(T(X)))."

Conventions.
* Affine sources, affine maps and the uniform law `U_m` are the published
  `QuadExt.Main.IsAffineSource`, `QuadExt.Main.IsAffineMap` (x ↦ ℓ(x) + b) and `QuadExt.Main.unif`.
* "Dimension at least k" is `k ≤ H∞(X)` with the published `SSNonExt.minEntropy`; for an affine
  source the min-entropy is the dimension of its affine subspace (p. 4, p. 21).
* `≈ε` is `SSNonExt.TV ≤ ε` (statistical distance ½ ∑ |P(ω) − Q(ω)|, p. 18).
* The left side is the joint law of `(F(X), F(T(X)))`; the right side is the product of `U_m` with
  the law of `F(T(X))` (the uniform variable is independent of the other coordinate, p. 4).
* `IsNMAffExtInv` is the same requirement restricted to globally fixed-point-free affine
  involutions: `T(T(x)) = x` and `T(x) ≠ x` for every `x ∈ 𝔽₂ⁿ`.
-/

namespace NMAffExt.LBP

/-- The product law of two distributions: independent draws `(a, b)` with `a ∼ μ`, `b ∼ ν`. -/
noncomputable def prodLaw {α β : Type} (μ : PMF α) (ν : PMF β) : PMF (α × β) :=
  μ.bind fun a => ν.map fun b => (a, b)

/-- The **non-malleability error** of `F` on the source law `P` under tampering `T`: the statistical
distance between the law of `(F(X), F(T(X)))` and the law of `(U_m, F(T(X)))`, `U_m` independent,
for `X ∼ P`. -/
noncomputable def nmError {n m : ℕ} (F : (Fin n → ZMod 2) → (Fin m → ZMod 2))
    (P : PMF (Fin n → ZMod 2)) (T : (Fin n → ZMod 2) → (Fin n → ZMod 2)) : ℝ :=
  SSNonExt.TV (P.map fun x => (F x, F (T x)))
    (prodLaw (QuadExt.Main.unif (Fin m)) (P.map fun x => F (T x)))

/-- **Definition 1.1.** `F : 𝔽₂ⁿ → 𝔽₂ᵐ` is a `(k, ε)` non-malleable affine extractor: for every affine
source `X` of dimension at least `k` and every affine map `T : 𝔽₂ⁿ → 𝔽₂ⁿ` without fixed points,
`(F(X), F(T(X))) ≈ε (U_m, F(T(X)))`. -/
def IsNMAffExt {n m : ℕ} (k : ℕ) (ε : ℝ) (F : (Fin n → ZMod 2) → (Fin m → ZMod 2)) : Prop :=
  ∀ P : PMF (Fin n → ZMod 2), QuadExt.Main.IsAffineSource P → (k : ℝ) ≤ SSNonExt.minEntropy P →
    ∀ T : (Fin n → ZMod 2) → (Fin n → ZMod 2), QuadExt.Main.IsAffineMap T → (∀ x, T x ≠ x) →
      nmError F P T ≤ ε

/-- `F` is `(k, ε)` non-malleable against **globally fixed-point-free affine involutions**: the
requirement of Definition 1.1 for every affine `T` with `T (T x) = x` and `T x ≠ x` for all `x`. -/
def IsNMAffExtInv {n m : ℕ} (k : ℕ) (ε : ℝ) (F : (Fin n → ZMod 2) → (Fin m → ZMod 2)) : Prop :=
  ∀ P : PMF (Fin n → ZMod 2), QuadExt.Main.IsAffineSource P → (k : ℝ) ≤ SSNonExt.minEntropy P →
    ∀ T : (Fin n → ZMod 2) → (Fin n → ZMod 2), QuadExt.Main.IsAffineMap T → (∀ x, T x ≠ x) →
      (∀ x, T (T x) = x) → nmError F P T ≤ ε

/-- Every `(k, ε)` non-malleable affine extractor is non-malleable against globally
fixed-point-free affine involutions. -/
theorem IsNMAffExt.toInv {n m : ℕ} {k : ℕ} {ε : ℝ} {F : (Fin n → ZMod 2) → (Fin m → ZMod 2)}
    (h : IsNMAffExt k ε F) : IsNMAffExtInv k ε F :=
  fun P hP hk T hT hfix _ => h P hP hk T hT hfix

end NMAffExt.LBP


