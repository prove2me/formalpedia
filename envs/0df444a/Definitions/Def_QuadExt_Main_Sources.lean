-- Prove2me | Definitions.Def_QuadExt_Main_Sources
-- name    : QuadExt_Main_Sources
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T07:02:52.895711+00:00
-- url     : https://prove2.me/theorems/7090dccb-c946-4ed3-8b17-92c309b30544
-- title:
--   Quadratic and affine maps over $\mathbb F_2$, the sources $f(U_s)$ they sample, and directional derivatives
-- statement:
--   Write $\mathbb F_2 = \{0,1\}$ and let $U_s$ be the uniform distribution on $\mathbb F_2^s$. A map $f : \mathbb F_2^s \to \mathbb F_2^n$ is **quadratic** if every coordinate $f_i$ is the evaluation of a polynomial over $\mathbb F_2$ of total degree at most $2$ in the $s$ input bits; affine maps (degree at most $1$) are quadratic. The map $f$ samples the **source** $f(U_s)$, the distribution of $f(Y)$ for $Y$ uniform; $f$ is the **generating map** and its inputs are the **generating bits** (Definitions 4.1–4.2). A **quadratic source** is a source $f(U_s)$ with $f$ quadratic, for any number $s$ of generating bits.
--
--   A map $g$ is **affine** if $g(x) = \ell(x) + b$ with $\ell$ linear over $\mathbb F_2$. An **affine source** on $n$ bits is $\ell(U_s) + b$ for some $s$, a linear $\ell : \mathbb F_2^s \to \mathbb F_2^n$ and a fixed $b \in \mathbb F_2^n$. For a finite set $S$, $U_S$ is the uniform distribution on $S$.
--
--   The **directional derivative** of $g$ in direction $a$ is
--   $$\partial_a g(x) = g(x) + g(x + a).$$
--   For quadratic $g$ and $a \neq 0$, $\partial_a g(U_s)$ is an affine source; the condition "$H_\infty(\partial_a g(U_s)) \ge r$ for every $a \ne 0$" is the derivative-entropy hypothesis of §§5–8. A map $g_2(y, z)$ of two blocks of bits is **bilinear** if it is linear in $y$ for fixed $z$ and linear in $z$ for fixed $y$.
--
--   **Formalization Note.** Bits are `ZMod 2`; strings are `σ → ZMod 2` for a finite index type `σ` (`Fin s`, or `Fin s ⊕ Fin z` when the generating bits are split into blocks $(Y, Z)$, joined by `join y z`). `source f` is `PMF.map f` of the uniform distribution. A subsource $f(U_V)$ on an affine subspace $V$ of the generating bits is written `source (f ∘ L)` for an injective affine `L : 𝔽₂^{dim V} → 𝔽₂^s` with image $V$ (`IsInjAffine L`). `unifOn S` is $U_S$ for non-empty $S$ (on the empty set, where $U_S$ is undefined, it is an arbitrary fixed distribution; statements only use it on non-empty sets).
-- source:
--   Chandrasekaran, Goodman, Zuckerman, Quadratic Extractors, STOC 2027 submission (manuscript sha256 ddc80a9a…), p. 13 (PDF 14), Definitions 4.1–4.3; p. 1 (PDF 2), affine sources; p. 7 (PDF 8), directional derivative; p. 3 (PDF 4), notation

import Mathlib

namespace QuadExt.Main

/-!
# Quadratic and affine maps over 𝔽₂, the sources they sample, and directional derivatives

Chandrasekaran, Goodman, Zuckerman, *Quadratic Extractors*, STOC 2027 submission (manuscript
sha256 ddc80a9a…), p. 13 (PDF 14), Definitions 4.1–4.3; p. 1 (PDF 2) affine sources; p. 7 (PDF 8)
directional derivative; p. 3 (PDF 4) notation `U_S`.

Bits are elements of `ZMod 2` (= 𝔽₂), a string of `n` bits is `Fin n → ZMod 2`, and a generating
string is `σ → ZMod 2` for a finite index type `σ` (`Fin s`, or `Fin s ⊕ Fin z` when the generating
bits are split into two blocks `(Y, Z)`).
-/

/-- The uniform distribution `U_σ` on bit strings indexed by a finite type `σ` (`U_s` for `σ = Fin s`). -/
noncomputable def unif (σ : Type) [Fintype σ] [DecidableEq σ] : PMF (σ → ZMod 2) :=
  PMF.uniformOfFintype (σ → ZMod 2)

/-- The **sampled source** `f(U_σ)`: the law of `f` applied to uniform generating bits
(Definition 4.1: `f` is the generating map). -/
noncomputable def source {σ : Type} [Fintype σ] [DecidableEq σ] {n : ℕ}
    (f : (σ → ZMod 2) → (Fin n → ZMod 2)) : PMF (Fin n → ZMod 2) :=
  (unif σ).map f

/-- `U_S`: the uniform distribution on a finite set `S` (p. 3); on the empty set, where `U_S` is
undefined, it is (arbitrarily) the uniform distribution on the whole type. -/
noncomputable def unifOn {α : Type} [Fintype α] [Nonempty α] (S : Finset α) : PMF α :=
  if h : S.Nonempty then PMF.uniformOfFinset S h else PMF.uniformOfFintype α

/-- A **quadratic map** over 𝔽₂ (Definition 4.2): every output coordinate `f(x)_i` is the
evaluation at `x` of a polynomial over 𝔽₂ of total degree at most `2` in the generating bits.
Affine maps (degree ≤ 1) are included. -/
def IsQuadraticMap {σ : Type} {n : ℕ} (f : (σ → ZMod 2) → (Fin n → ZMod 2)) : Prop :=
  ∀ i : Fin n, ∃ p : MvPolynomial σ (ZMod 2), p.totalDegree ≤ 2 ∧ ∀ x, f x i = MvPolynomial.eval x p

/-- An **affine map** `g(x) = ℓ(x) + b` with `ℓ` linear over 𝔽₂. -/
def IsAffineMap {σ τ : Type} (g : (σ → ZMod 2) → (τ → ZMod 2)) : Prop :=
  ∃ (ℓ : (σ → ZMod 2) →ₗ[ZMod 2] (τ → ZMod 2)) (b : τ → ZMod 2), ∀ x, g x = ℓ x + b

/-- An **injective affine map**. Its image is an affine subspace of dimension `|σ|`, and every
non-empty affine subspace of `𝔽₂^τ` is the image of one; `f(U_V)` for an affine subspace `V` of the
generating bits is `(f ∘ L)(U_{dim V})` for such an `L` with image `V`. -/
def IsInjAffine {σ τ : Type} (L : (σ → ZMod 2) → (τ → ZMod 2)) : Prop :=
  IsAffineMap L ∧ Function.Injective L

/-- An **affine source** on `n` bits (p. 1): `X = ℓ(U_s) + b` for some `s`, a linear
`ℓ : 𝔽₂^s → 𝔽₂^n` and a fixed `b ∈ 𝔽₂^n`. -/
def IsAffineSource {n : ℕ} (P : PMF (Fin n → ZMod 2)) : Prop :=
  ∃ (s : ℕ) (g : (Fin s → ZMod 2) → (Fin n → ZMod 2)), IsAffineMap g ∧ P = source g

/-- The **directional derivative** `∂_a g(x) = g(x) + g(x + a)` (p. 7). -/
def dirDeriv {σ : Type} {n : ℕ} (a : σ → ZMod 2) (g : (σ → ZMod 2) → (Fin n → ZMod 2)) :
    (σ → ZMod 2) → (Fin n → ZMod 2) :=
  fun x => g x + g (x + a)

/-- A map of two blocks of bits is **bilinear**: linear in each block when the other is fixed. -/
def IsBilinear {σ τ : Type} {n : ℕ} (g : (σ → ZMod 2) → (τ → ZMod 2) → (Fin n → ZMod 2)) : Prop :=
  (∀ z, IsLinearMap (ZMod 2) (fun y => g y z)) ∧ (∀ y, IsLinearMap (ZMod 2) (g y))

/-- Generating bits split into two blocks `(y, z)`: the string indexed by `Fin s ⊕ Fin z`. -/
def join {s z : ℕ} (y : Fin s → ZMod 2) (w : Fin z → ZMod 2) : Fin s ⊕ Fin z → ZMod 2 :=
  Sum.elim y w

end QuadExt.Main


