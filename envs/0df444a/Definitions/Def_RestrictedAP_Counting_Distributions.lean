-- Prove2me | Definitions.Def_RestrictedAP_Counting_Distributions
-- name    : RestrictedAP_Counting_Distributions
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T06:19:06.525228+00:00
-- url     : https://prove2.me/theorems/1a07f6b6-2cbf-48e6-8a01-de2e991a4120
-- title:
--   Distributions on finite alphabets, tensor powers, marginals and $(G,+)$-embeddings
-- statement:
--   A **distribution** on a finite alphabet $\Omega$ is a function $\mu:\Omega\to\mathbb R$ with $\mu\ge 0$ and $\sum_x\mu(x)=1$; its **support** is $\mathrm{supp}(\mu)=\{x : \mu(x)\ne0\}$, whose points are its **atoms**. "Each atom has probability at least $\alpha$" means $\mu(x)\ge\alpha$ for every $x\in\mathrm{supp}(\mu)$, and "$\alpha$ is the minimum non-zero probability" means in addition $\alpha>0$ and $\alpha$ is attained. The **tensor power** is $\mu^{\otimes n}(x)=\prod_{i=1}^n\mu(x_i)$ on $\Omega^n$; expectations are finite sums $\mathbb E_\mu f=\sum_x\mu(x)f(x)$ and $\|f\|_{L^2(\mu)}=(\sum_x\mu(x)|f(x)|^2)^{1/2}$. For $\mu$ on $\Sigma^3$, its **marginals** $\mu_x,\mu_y,\mu_z$ are the laws of the three coordinates, and
--   $$\Pr_{(x,y,z)\sim\mu^{\otimes n}}[x,y,z\in A]=\sum_{t\in(\Sigma^3)^n}\mu^{\otimes n}(t)\,\mathbf 1[x(t)\in A,\ y(t)\in A,\ z(t)\in A].$$
--
--   **Definition 1.3.** Let $\mu$ be a distribution on $\Sigma\times\Gamma\times\Phi$ and $(G,+)$ an abelian group. $\mu$ has a **$(G,+)$-embedding** if there are maps $\sigma:\Sigma\to G$, $\gamma:\Gamma\to G$, $\phi:\Phi\to G$, not all constant, with
--   $$\sigma(x)+\gamma(y)+\phi(z)=0_G\quad\text{for all }(x,y,z)\in\mathrm{supp}(\mu).$$
--
--   **Formalization Note.** Distributions are weight functions with the predicate `IsDist`; `AtomsAtLeast μ α` and `IsMinAtom μ α` are the two atom conditions; `marginal μ i` ($i=0,1,2$) uses `coord3`; `HasEmbedding G S` is Definition 1.3 for a support set $S$ ("not all constant" = not all three maps constant on their whole alphabets) and `DistHasEmbedding G μ` applies it to $\mathrm{supp}(\mu)$; `tripleProb μ n A` is the probability displayed above.
-- source:
--   Bhangale, Khot, Liu, Minzer, A Counting Lemma for Somewhat Restricted 3-APs, arXiv:2608.17365 (copy sha256 de0b96c1…), p. 3, Definition 1.3 and Theorem 1.4; p. 6 (notation); p. 31 (§5.2)

import Mathlib

namespace RestrictedAP.Counting

/-!
# Distributions on finite alphabets, tensor powers, marginals and `(G,+)`-embeddings

Bhangale, Khot, Liu, Minzer, *A Counting Lemma for Somewhat Restricted 3-APs*,
arXiv:2608.17365 (copy sha256 de0b96c1…), p. 3, Definition 1.3 and Theorem 1.4; p. 6
(notation); p. 31 (§5.2: the minimum atom probability).

* A distribution on a finite alphabet `Ω` is a weight function `μ : Ω → ℝ` that is nonnegative
  and sums to `1` (`IsDist`). Its support is `{x | μ x ≠ 0}`; its *atoms* are the points of the
  support.
* `tensorPow μ n` is the product distribution `μ^{⊗n}` on `Fin n → Ω`.
* For `μ` on `Sig × Sig × Sig`, `coord3 i t` is the `i`-th coordinate of `t`
  (`i = 0, 1, 2` for `x, y, z`) and `marginal μ i` is the marginal of `μ` on that coordinate.
* `HasEmbedding G S` is Definition 1.3 for the support `S`: maps `σ, γ, φ` into the abelian
  group `G`, **not all constant** (as maps on the whole alphabets), with
  `σ x + γ y + φ z = 0` for every `(x, y, z) ∈ S`. A distribution has a `(G,+)`-embedding when
  its support has one (`DistHasEmbedding`).
-/

/-- `μ` is a probability distribution on the finite alphabet `Ω`. -/
def IsDist {Ω : Type*} [Fintype Ω] (μ : Ω → ℝ) : Prop :=
  (∀ x, 0 ≤ μ x) ∧ ∑ x, μ x = 1

/-- The support of `μ`: the atoms `{x | μ x ≠ 0}`. -/
def supp {Ω : Type*} (μ : Ω → ℝ) : Set Ω := {x | μ x ≠ 0}

/-- "The probability of each atom of `μ` is at least `α`." -/
def AtomsAtLeast {Ω : Type*} (μ : Ω → ℝ) (α : ℝ) : Prop :=
  ∀ x, μ x ≠ 0 → α ≤ μ x

/-- "`α > 0` is the minimum non-zero probability of an atom of `μ`." -/
def IsMinAtom {Ω : Type*} (μ : Ω → ℝ) (α : ℝ) : Prop :=
  0 < α ∧ AtomsAtLeast μ α ∧ ∃ x, μ x = α

/-- The tensor power `μ^{⊗n}`: `μ^{⊗n}(x) = ∏_i μ(x_i)`. -/
def tensorPow {Ω : Type*} (μ : Ω → ℝ) (n : ℕ) : (Fin n → Ω) → ℝ :=
  fun x => ∏ i, μ (x i)

/-- Expectation of a real function under the weight function `μ`. -/
def expect {Ω : Type*} [Fintype Ω] (μ : Ω → ℝ) (f : Ω → ℝ) : ℝ :=
  ∑ x, μ x * f x

/-- Expectation of a complex function under the weight function `μ`. -/
noncomputable def expectC {Ω : Type*} [Fintype Ω] (μ : Ω → ℝ) (f : Ω → ℂ) : ℂ :=
  ∑ x, (μ x : ℂ) * f x

/-- The `L²(μ)` norm `‖f‖₂ = (E_μ |f|²)^{1/2}`. -/
noncomputable def l2Norm {Ω : Type*} [Fintype Ω] (μ : Ω → ℝ) (f : Ω → ℂ) : ℝ :=
  Real.sqrt (∑ x, μ x * ‖f x‖ ^ 2)

/-- The `i`-th coordinate (`i = 0, 1, 2`) of a triple in `Sig × Sig × Sig`. -/
def coord3 {Sig : Type*} (i : Fin 3) (t : Sig × Sig × Sig) : Sig :=
  if i = 0 then t.1 else if i = 1 then t.2.1 else t.2.2

/-- The marginal of `μ` on coordinate `i` of `Sig × Sig × Sig`. -/
noncomputable def marginal {Sig : Type*} [Fintype Sig] [DecidableEq Sig]
    (μ : Sig × Sig × Sig → ℝ) (i : Fin 3) : Sig → ℝ :=
  fun a => ∑ t, if coord3 i t = a then μ t else 0

/-- Definition 1.3 on a support set `S ⊆ Sig × Γ × Φ`: there are maps `σ, γ, φ` into `G`,
not all constant, with `σ x + γ y + φ z = 0` for every `(x, y, z) ∈ S`. -/
def HasEmbedding (G : Type*) [AddCommGroup G] {Sig Γ Φ : Type*}
    (S : Set (Sig × Γ × Φ)) : Prop :=
  ∃ (σ : Sig → G) (γ : Γ → G) (φ : Φ → G),
    ¬ ((∀ a a', σ a = σ a') ∧ (∀ b b', γ b = γ b') ∧ (∀ c c', φ c = φ c')) ∧
    ∀ t ∈ S, σ t.1 + γ t.2.1 + φ t.2.2 = 0

/-- `μ` has a `(G,+)`-embedding (Definition 1.3): its support has one. -/
def DistHasEmbedding (G : Type*) [AddCommGroup G] {Sig Γ Φ : Type*}
    (μ : Sig × Γ × Φ → ℝ) : Prop :=
  HasEmbedding G (supp μ)

/-- `Pr_{(x,y,z) ∼ μ^{⊗n}} [x, y, z ∈ A]` for `μ` on `Sig × Sig × Sig`; a sample of `μ^{⊗n}` is
`t : Fin n → Sig × Sig × Sig` and `x = (t i).1`, `y = (t i).2.1`, `z = (t i).2.2`. -/
noncomputable def tripleProb {Sig : Type*} [Fintype Sig] [DecidableEq Sig]
    (μ : Sig × Sig × Sig → ℝ) (n : ℕ) (A : Finset (Fin n → Sig)) : ℝ :=
  ∑ t : Fin n → Sig × Sig × Sig,
    if (fun i => (t i).1) ∈ A ∧ (fun i => (t i).2.1) ∈ A ∧ (fun i => (t i).2.2) ∈ A
    then tensorPow μ n t else 0

end RestrictedAP.Counting


