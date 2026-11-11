-- Prove2me | Definitions.Def_DistQuantumQuery_liftUp
-- name    : DistQuantumQuery_liftUp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:15:21.40083+00:00
-- url     : https://prove2.me/theorems/2253c233-d5ea-4eb0-9de9-7946807366bd
-- title:
--   Lifting map $E^\uparrow_\Gamma(X)=\mathbf G^\dagger X\mathbf G\circ(\Gamma+I)^{\otimes n}$, its adjoint form $E^\downarrow_\Gamma$, and extension by zero
-- statement:
--   Let $g:\Sigma_g\to\{0,1\}$ be a decision problem and $G:=\sum_{x\in\Sigma_g}|g(x)\rangle\langle x|$, so that $\mathbf G:=G^{\otimes n}$ maps $|x\rangle\mapsto|\mathbf g(x)\rangle$ for $x\in\Sigma_g^n$. For $\Gamma\in L(\Sigma_g)$ the **lifting map** $E^\uparrow_\Gamma:L(\{0,1\}^n)\to L(\Sigma_g^n)$ is
--   $$
--   E^\uparrow_\Gamma(X):=\mathbf G^\dagger X\mathbf G\circ(\Gamma+I)^{\otimes n},
--   $$
--   and
--   $$
--   E^\downarrow_\Gamma(Y):=\mathbf G\big(Y\circ(\Gamma+I)^{\otimes n}\big)\mathbf G^\dagger ,
--   $$
--   which Lemma 7.5(ii) identifies as its adjoint. The module also fixes $\Gamma^{\otimes n}$ (entries $\prod_i\Gamma(x_i,y_i)$), the composed distribution on all of $\Sigma_g^n$ for an outer distribution on all of $\{0,1\}^n$, the bit string of a tuple in $\Sigma_g^n$ (for the filters $\Delta_{ij}$), and the extensions by zero of matrices indexed by $\Sigma$ and by $\mathbf g^{-1}(\Sigma)$ to $\{0,1\}^n$ and $\Sigma_g^n$.
--
--   The lifting map turns a hardness certificate for the outer problem into one for the composed problem.
--
--   **Formalization Note** The definitions are the formulas. The conditions of Definition 7.4 on $\Gamma$ (real symmetric, $\|\Gamma\|\le1$, $\Gamma\circ\Delta_g=\Gamma$) are hypotheses of the lemmas. $\{0,1\}^n$ is `ι → Bool` and $\Sigma_g^n$ is `ι → Σ_g` for a finite type of blocks.
-- source:
--   Ben-David, Ebtehaj, Distributional Quantum Query Complexity, arXiv:2610.06835 (held version, sha256 6334ffaf…), Definition 7.2 p.56, Definition 7.4 p.56, Lemma 7.5(ii) p.57, Lemma 7.6 p.59 (extension by zero)

import Mathlib
import Definitions.Def_DistQuantumQuery_compose

open scoped Matrix

namespace DistQuantumQuery

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The matrix `**G** := G^{⊗n} ∈ L(Σ_g^n, {0,1}^n)`, `**G**|x⟩ = |g(x)⟩` with
`G := Σ_{x∈Σ_g} |g(x)⟩⟨x|` (Ben-David, Ebtehaj, *Distributional Quantum Query Complexity*,
arXiv:2610.06835, held version, sha256 6334ffaf…, Definition 7.2, p.56).

**Formalization Note** `{0,1}^n` is `ι → Bool` and `Σ_g^n` is `ι → Σ_g` for a finite type `ι` of
blocks; the entry at `(x̃, x)` is `1[x̃ = (g(x_1), …, g(x_n))]`. -/
def liftG (ι : Type*) [Fintype ι] [DecidableEq ι] {Sg : Finset (κ → Bool)} (g : Sg → Bool) :
    Matrix (ι → Bool) (ι → Sg) ℂ :=
  Matrix.of fun xt x => if xt = (fun i => g (x i)) then 1 else 0

/-- The tensor power `Γ^{⊗n}` of a matrix on `Σ_g`, a matrix on `Σ_g^n` with entries
`Π_i Γ(x_i, y_i)` (arXiv:2610.06835, held version, Definition 7.4, p.56). -/
def tensorPow (ι : Type*) [Fintype ι] {X : Type*} (Γ : Matrix X X ℂ) : Matrix (ι → X) (ι → X) ℂ :=
  Matrix.of fun x y => ∏ i, Γ (x i) (y i)

/-- The **lifting map** `E↑_Γ : L({0,1}^n) → L(Σ_g^n)`,
`E↑_Γ(X) := **G**† X **G** ∘ (Γ + I)^{⊗n}` (arXiv:2610.06835, held version, sha256 6334ffaf…,
Definition 7.4, p.56).

**Formalization Note** The definition is the formula; the conditions of Definition 7.4 on `Γ`
(real symmetric, `‖Γ‖ ≤ 1`, `Γ ∘ Δ_g = Γ`) are hypotheses of the lemmas that use it. -/
def liftUp {Sg : Finset (κ → Bool)} (g : Sg → Bool) (Γ : Matrix Sg Sg ℂ)
    (X : Matrix (ι → Bool) (ι → Bool) ℂ) : Matrix (ι → Sg) (ι → Sg) ℂ :=
  ((liftG ι g)ᴴ * X * liftG ι g) ⊙ tensorPow ι (Γ + 1)

/-- The map `E↓_Γ(Y) := **G**(Y ∘ (Γ + I)^{⊗n})**G**†`, `L(Σ_g^n) → L({0,1}^n)`, which
Lemma 7.5(ii) identifies as the adjoint of `E↑_Γ` (arXiv:2610.06835, held version,
sha256 6334ffaf…, Lemma 7.5(ii), p.57). -/
def liftDown {Sg : Finset (κ → Bool)} (g : Sg → Bool) (Γ : Matrix Sg Sg ℂ)
    (Y : Matrix (ι → Sg) (ι → Sg) ℂ) : Matrix (ι → Bool) (ι → Bool) ℂ :=
  liftG ι g * (Y ⊙ tensorPow ι (Γ + 1)) * (liftG ι g)ᴴ

/-- The bits of a tuple `x ∈ Σ_g^n` as a string on the positions `ι × κ` (block `i`, bit `j`);
the query filters `Δ_{ij}` of the composed input are `qfilt innerBits (i, j)`
(arXiv:2610.06835, held version, p.61). -/
def innerBits {Sg : Finset (κ → Bool)} (x : ι → Sg) : ι × κ → Bool :=
  fun p => (x p.1).1 p.2

/-- The composed distribution `η = μ ∘ (ν₀, ν₁)` on all of `Σ_g^n` for an outer distribution
`μ` on all of `{0,1}^n`, `η(x) = μ(g(x)) Π_i ν_{g(x_i)}(x_i)` (arXiv:2610.06835, held version,
§2.4.3, p.18; Lemma 7.5(iv), p.57). -/
noncomputable def compDistFull {Sg : Finset (κ → Bool)} (g : Sg → Bool)
    (μ : (ι → Bool) → ℝ) (ν₀ ν₁ : Sg → ℝ) : (ι → Sg) → ℝ :=
  fun x => μ (fun i => g (x i)) * ∏ i, (if g (x i) then ν₁ else ν₀) (x i)

/-- Extension by zero of a matrix indexed by `Σ ⊆ {0,1}^n` to `{0,1}^n` (arXiv:2610.06835,
held version, Lemma 7.6, p.59: "matrices indexed by Σ and g⁻¹(Σ) are implicitly extended by
zero"). -/
def extOuter (S : Finset (ι → Bool)) (M : Matrix S S ℂ) : Matrix (ι → Bool) (ι → Bool) ℂ :=
  Matrix.of fun a b => if ha : a ∈ S then (if hb : b ∈ S then M ⟨a, ha⟩ ⟨b, hb⟩ else 0) else 0

/-- Extension by zero of a matrix indexed by the composed domain `g⁻¹(Σ)` to `Σ_g^n`
(arXiv:2610.06835, held version, Lemma 7.6, p.59). -/
noncomputable def extComp {S : Finset (ι → Bool)} {Sg : Finset (κ → Bool)} {g : Sg → Bool}
    (M : Matrix (compDomain S Sg g) (compDomain S Sg g) ℂ) : Matrix (ι → Sg) (ι → Sg) ℂ :=
  Matrix.of fun x y => by
    classical
    exact if hx : innerBits x ∈ compDomain S Sg g then
      (if hy : innerBits y ∈ compDomain S Sg g then M ⟨_, hx⟩ ⟨_, hy⟩ else 0) else 0

end DistQuantumQuery


