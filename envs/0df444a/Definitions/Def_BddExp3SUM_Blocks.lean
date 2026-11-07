-- Prove2me | Definitions.Def_BddExp3SUM_Blocks
-- name    : BddExp3SUM_Blocks
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:59:53.62714+00:00
-- url     : https://prove2.me/theorems/4367acf4-c535-4fe5-a873-1f6251ce0dc0
-- title:
--   Blocks of size at most $\sigma$, probes, the support matrices (12)–(13), and $A, b_0, g_0, g\prime, N$
-- statement:
--   A **block cut** of $U$ along a labelling $\varphi$ with cap $\sigma$ is a partition of $U$ into nonempty blocks, each inside one $\varphi$-class and of size at most $\sigma$, with exactly $\lceil a/\sigma\rceil$ blocks in a class of size $a$.
--
--   A **probe** is $Q=(x_1;b_2,b_3)$ with $x_1\in U_1$, $b_2,b_3$ blocks of lists 2 and 3, and $\pi(x_1)+\pi(z_{b_2})+\pi(z_{b_3})=0$, for representatives $z_b\in b$. Its middle element is $w_Q=K(x_1)+K(z_{b_2})+K(z_{b_3})$.
--
--   The support matrices are 0/1 with
--
--   $$X[(b_2,\mu_1),\lambda]=1\iff\exists x_2\in b_2: K(x_2)-K(z_{b_2})+(\mu_1,0)=\lambda,$$
--
--   $$Y[\lambda,(b_3,\mu_2)]=1\iff\exists x_3\in b_3: -(K(x_3)-K(z_{b_3}))-(0,\mu_2)=\lambda.$$
--
--   A probe is **positive** if $XY$ is positive at the position given by $w_Q=\mu_1+\mu_2$. The parameters of the matrix call are $A=M^2+3+24L$, $b_0=M^2+1$, $g_0=M(A+b_0+3)$, $g'=\lceil g_0n/\sigma\rceil$ and $N=g'p^{\lceil q/2\rceil}$.
--
--   **Formalization Note** The padding of $X,Y$ to size $N$ is not represented; the room for it is a clause of the (14)–(16) milestone. An arbitrary partition into small pieces would make the count in Lemma 3 false, hence the exact number of blocks per class.
-- source:
--   Zeng, Wang, Cao, Dai, Wang, Truly Subquadratic 3SUM over Every Bounded-Exponent Abelian Group, STOC 2027 submission (manuscript sha256 19546c9a…), Lemma 3, p.4; §5, pp.5–6

import Mathlib
import Definitions.Def_BddExp3SUM_Hash

namespace BddExp3SUM

/-!
# Blocks, probes, the support matrices `X, Y`, and the parameters of the matrix call

Zeng, Wang, Cao, Dai, Wang, STOC 2027 submission (manuscript sha256 19546c9a…), Lemma 3, p.4; §5,
pp.5–6; (12), (13), p.5.

**Formalization Note.**
* **The cut into blocks.** A class of size `a` becomes exactly `⌈a/σ⌉` blocks of size at most `σ`
  (`IsBlockCut`). An arbitrary partition into small pieces (say singletons) has `|U|` blocks, and the
  count in Lemma 3 fails for it; the paper's proof bounds the number of blocks by "the number of classes
  plus `|U_i|/σ`", which is this cut.
* **Matrices.** `X` and `Y` are 0/1 functions on `(block × B₁) × B` and `B × (block × B₂)`, over `ℤ`.
  The padding to size `N` is not represented here; it is the role of the room bound in (14)–(16).
  The product entry is a sum over the finite group `B`, written as a `finsum`.
* **Probes.** A representative `z_b` is any element of `b`: a function `z` with `z b ∈ b`.
-/

variable {M r : ℕ}

open Classical in
/-- `parts` cuts `U` into blocks: a partition of `U` into nonempty blocks, each inside one class of
the labelling `φ` and of size at most `σ`, with exactly `⌈a/σ⌉` blocks in a class of size `a`. -/
structure IsBlockCut {T : Type*} (φ : Grp M r → T) (U : Finset (Grp M r)) (σ : ℕ)
    (parts : Finset (Finset (Grp M r))) : Prop where
  nonempty : ∀ b ∈ parts, b.Nonempty
  subset : ∀ b ∈ parts, b ⊆ U
  cover : ∀ x ∈ U, ∃ b ∈ parts, x ∈ b
  disjoint : ∀ b ∈ parts, ∀ b' ∈ parts, b ≠ b' → Disjoint b b'
  card_le : ∀ b ∈ parts, b.card ≤ σ
  same_label : ∀ b ∈ parts, ∀ x ∈ b, ∀ y ∈ b, φ x = φ y
  count : ∀ y : T, (parts.filter fun b => ∀ x ∈ b, φ x = y).card =
    ⌈((U.filter fun x => φ x = y).card : ℝ) / σ⌉₊

open Classical in
/-- The set `𝒫` of probes `(x₁; b₂, b₃)`: `x₁ ∈ U₁` and `π(x₁) + π(z_{b₂}) + π(z_{b₃}) = 0`. -/
noncomputable def probes {T : Type*} [AddCommGroup T] (φ : Grp M r →+ T)
    (U₁ : Finset (Grp M r)) (parts₂ parts₃ : Finset (Finset (Grp M r)))
    (z : Finset (Grp M r) → Grp M r) : Finset (Grp M r × Finset (Grp M r) × Finset (Grp M r)) :=
  (U₁ ×ˢ parts₂ ×ˢ parts₃).filter fun Q => φ Q.1 + φ (z Q.2.1) + φ (z Q.2.2) = 0

/-- `A = M² + 3 + 24L` (Lemma 5). -/
def Acoef (M : ℕ) : ℕ := M ^ 2 + 3 + 24 * Lcard M

/-- `w_Q = K(x₁) + K(z_{b₂}) + K(z_{b₃})`. -/
def wProbe {T : Type*} [AddCommGroup T] (K : Grp M r →+ T) (z : Finset (Grp M r) → Grp M r)
    (Q : Grp M r × Finset (Grp M r) × Finset (Grp M r)) : T :=
  K Q.1 + K (z Q.2.1) + K (z Q.2.2)

open Classical in
/-- (12): `X[(b₂, μ₁), λ] = 1 ⇔ ∃ x₂ ∈ b₂, K(x₂) - K(z_{b₂}) + (μ₁, 0) = λ`, and `0` otherwise. -/
noncomputable def supportX {T : Type*} [AddCommGroup T] (K : Grp M r →+ T)
    (z : Finset (Grp M r) → Grp M r) (A₁ A : AddSubgroup T)
    (v : Finset (Grp M r) × A₁) (lam : A) : ℤ :=
  if ∃ x₂ ∈ v.1, K x₂ - K (z v.1) + (v.2 : T) = lam then 1 else 0

open Classical in
/-- (13): `Y[λ, (b₃, μ₂)] = 1 ⇔ ∃ x₃ ∈ b₃, -(K(x₃) - K(z_{b₃})) - (0, μ₂) = λ`, and `0` otherwise. -/
noncomputable def supportY {T : Type*} [AddCommGroup T] (K : Grp M r →+ T)
    (z : Finset (Grp M r) → Grp M r) (A₂ A : AddSubgroup T)
    (lam : A) (v : Finset (Grp M r) × A₂) : ℤ :=
  if ∃ x₃ ∈ v.1, -(K x₃ - K (z v.1)) - (v.2 : T) = lam then 1 else 0

/-- The entry `(XY)[(b₂, μ₁), (b₃, μ₂)]` of the support product, summed over `λ ∈ B`. -/
noncomputable def supportEntry {T : Type*} [AddCommGroup T] (K : Grp M r →+ T)
    (z : Finset (Grp M r) → Grp M r) (A₁ A₂ A : AddSubgroup T)
    (v₁ : Finset (Grp M r) × A₁) (v₂ : Finset (Grp M r) × A₂) : ℤ :=
  ∑ᶠ lam : A, supportX K z A₁ A v₁ lam * supportY K z A₂ A lam v₂

/-- The probe `Q` is positive: the product is positive at the position `((b₂, μ₁), (b₃, μ₂))` given
by the decomposition `w_Q = μ₁ + μ₂`. -/
def IsPositiveProbe {T : Type*} [AddCommGroup T] (K : Grp M r →+ T)
    (z : Finset (Grp M r) → Grp M r) (A₁ A₂ A : AddSubgroup T)
    (Q : Grp M r × Finset (Grp M r) × Finset (Grp M r)) : Prop :=
  ∃ (μ₁ : A₁) (μ₂ : A₂), (μ₁ : T) + μ₂ = wProbe K z Q ∧
    0 < supportEntry K z A₁ A₂ A (Q.2.1, μ₁) (Q.2.2, μ₂)

/-- `b₀ = M² + 1`. -/
def b₀ (M : ℕ) : ℕ := M ^ 2 + 1

/-- `g₀ = M(A + b₀ + 3)`. -/
def g₀ (M : ℕ) : ℕ := M * (Acoef M + b₀ M + 3)

/-- `g′ = ⌈g₀ n/σ⌉`. -/
noncomputable def g' (M n : ℕ) : ℕ := ⌈(g₀ M * n : ℝ) / σ M n⌉₊

/-- `N = g′ p^{⌈q/2⌉}`. -/
noncomputable def NN (M n p q : ℕ) : ℕ := g' M n * p ^ ((q + 1) / 2)

end BddExp3SUM


