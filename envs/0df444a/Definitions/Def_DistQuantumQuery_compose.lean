-- Prove2me | Definitions.Def_DistQuantumQuery_compose
-- name    : DistQuantumQuery_compose
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:14:04.397412+00:00
-- url     : https://prove2.me/theorems/5ee28a9d-217e-415f-a8b9-fb2597d37ec1
-- title:
--   Composed problem $f\circ g$ on $g^{-1}(\Sigma)$, composed distribution $\mu\circ(\nu_0,\nu_1)$, and $\mathrm{TRIV}\circ g$ with $(\nu_0^{\otimes n}+\nu_1^{\otimes n})/2$
-- statement:
--   Let $f:\Sigma\to\Omega$ be functional on $\Sigma\subseteq\{0,1\}^n$ and $g:\Sigma_g\to\{0,1\}$ a decision problem on $\Sigma_g\subseteq\{0,1\}^m$. For $x=(x_1,\dots,x_n)\in\Sigma_g^n$ write $\mathbf g(x)=(g(x_1),\dots,g(x_n))$. The **composed problem** is
--   $$
--   f\circ g:\ \mathbf g^{-1}(\Sigma)\to\Omega,\qquad (f\circ g)(x):=f(\mathbf g(x)),
--   $$
--   and for distributions $\nu_b$ on $\Sigma_g$ with $\mathrm{supp}(\nu_b)\subseteq g^{-1}(b)$ and $\mu$ on $\Sigma$ the **composed distribution** $\eta=\mu\circ(\nu_0,\nu_1)$ on $\mathbf g^{-1}(\Sigma)$ is
--   $$
--   \eta(x_1,\dots,x_n):=\mu(g(x_1),\dots,g(x_n))\prod_{i=1}^n\nu_{g(x_i)}(x_i).
--   $$
--   $\mathrm{TRIV}:\{0^n,1^n\}\to\{0,1\}$ is $\mathrm{TRIV}(b^n)=b$; $F_n=\mathrm{TRIV}\circ\mathbf g$ has domain $D_n=g^{-1}(0)^n\cup g^{-1}(1)^n$, carrying the correlated distribution $\mu_n=(\nu_0^{\otimes n}+\nu_1^{\otimes n})/2$, i.e. $\mu_n(x)=\tfrac12\big(\prod_i\nu_0(x_i)+\prod_i\nu_1(x_i)\big)$.
--
--   These are the objects of the composition theorem and of the characterization of $\mathrm{sfAdv}$ in the limit $n\to\infty$.
--
--   **Formalization Note** The composed input is a bit string on the positions $\iota\times\kappa$ (block $i$, bit $j$), and $\mathbf g^{-1}(\Sigma)$ is a finite set of such strings. $\mathrm{TRIV}(x)$ is written as $[x=1^n]$, which is $b$ on $b^n$ when there is at least one position. The TRIV sequence is indexed by $n+1$ blocks, since TRIV on zero bits is undefined.
-- source:
--   Ben-David, Ebtehaj, Distributional Quantum Query Complexity, arXiv:2610.06835 (held version, sha256 6334ffaf…), §2.4.3 p.18 (composition), §6.2 p.53 and §7.1.5 p.63 (TRIV), Theorem 7.12 p.67 and p.65 (µn, Dn)

import Mathlib

namespace DistQuantumQuery

/-- Block `i` of a composed input `x ∈ {0,1}^{n·m}`, i.e. the inner input `x_i ∈ {0,1}^m`
(Ben-David, Ebtehaj, *Distributional Quantum Query Complexity*, arXiv:2610.06835, held version,
sha256 6334ffaf…, §2.4.3, p.18). Positions of the composed input are pairs `(i, j)`: block `i`,
bit `j`. -/
def blockOf {ι κ : Type*} (x : ι × κ → Bool) (i : ι) : κ → Bool :=
  fun j => x (i, j)

/-- `x` lies in the domain `g⁻¹(Σ)` of the composed problem: every block `x_i` lies in `Σ_g` and
`g(x) = (g(x_1), …, g(x_n)) ∈ Σ` (arXiv:2610.06835, held version, §2.4.3, p.18). -/
def InCompDomain {ι κ : Type*} (S : Finset (ι → Bool)) (Sg : Finset (κ → Bool))
    (g : Sg → Bool) (x : ι × κ → Bool) : Prop :=
  ∃ h : ∀ i, blockOf x i ∈ Sg, (fun i => g ⟨blockOf x i, h i⟩) ∈ S

/-- The domain `g⁻¹(Σ) ⊆ Σ_g^n ⊆ {0,1}^{n·m}` of the composed problem `f ∘ g`
(arXiv:2610.06835, held version, sha256 6334ffaf…, §2.4.3, p.18), as a `Finset` of bit strings
on the positions `ι × κ`. -/
noncomputable def compDomain {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (S : Finset (ι → Bool))
    (Sg : Finset (κ → Bool)) (g : Sg → Bool) : Finset (ι × κ → Bool) :=
  @Finset.filter _ (InCompDomain S Sg g) (Classical.decPred _) Finset.univ

/-- Membership in the composed domain. -/
theorem mem_compDomain {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {S : Finset (ι → Bool)} {Sg : Finset (κ → Bool)} {g : Sg → Bool} {x : ι × κ → Bool} :
    x ∈ compDomain S Sg g ↔ InCompDomain S Sg g x := by
  unfold compDomain
  exact (@Finset.mem_filter _ _ (Classical.decPred _) _ _).trans (and_iff_right (Finset.mem_univ _))

/-- The `i`-th inner input `x_i ∈ Σ_g` of a point of the composed domain. -/
def compBlock {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {S : Finset (ι → Bool)}
    {Sg : Finset (κ → Bool)} {g : Sg → Bool} (x : compDomain S Sg g) (i : ι) : Sg :=
  ⟨blockOf x.1 i, (mem_compDomain.1 x.2).fst i⟩

/-- The outer input `g(x) = (g(x_1), …, g(x_n)) ∈ Σ` of a point of the composed domain
(arXiv:2610.06835, held version, §2.4.3, p.18). -/
def compOuter {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {S : Finset (ι → Bool)}
    {Sg : Finset (κ → Bool)} {g : Sg → Bool} (x : compDomain S Sg g) : S :=
  ⟨fun i => g (compBlock x i), (mem_compDomain.1 x.2).snd⟩

/-- The **composed problem** `f ∘ g : g⁻¹(Σ) → Ω`, `(f ∘ g)(x) := f(g(x))` (Ben-David, Ebtehaj,
arXiv:2610.06835, held version, sha256 6334ffaf…, §2.4.3, p.18).

**Formalization Note** The outer positions are a finite type `ι` (the paper's `[n]`), the inner
positions a finite type `κ` (the paper's `[m]`); the composed input lives on `ι × κ`. -/
def compose {ι κ Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {S : Finset (ι → Bool)}
    {Sg : Finset (κ → Bool)} (f : S → Ω) (g : Sg → Bool) : compDomain S Sg g → Ω :=
  fun x => f (compOuter x)

/-- The **composed distribution** `η := μ ∘ (ν₀, ν₁)` on `g⁻¹(Σ)`,
`η(x_1, …, x_n) := μ(g(x_1), …, g(x_n)) · Π_{i=1}^n ν_{g(x_i)}(x_i)` (arXiv:2610.06835, held
version, sha256 6334ffaf…, §2.4.3, p.18), exactly the printed product formula. -/
noncomputable def compDist {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {S : Finset (ι → Bool)}
    {Sg : Finset (κ → Bool)} (g : Sg → Bool) (μ : S → ℝ) (ν₀ ν₁ : Sg → ℝ) :
    compDomain S Sg g → ℝ :=
  fun x => μ (compOuter x) * ∏ i, (if g (compBlock x i) then ν₁ else ν₀) (compBlock x i)

/-- The domain `{0^n, 1^n}` of `TRIV` (arXiv:2610.06835, held version, §7.1.5, p.63). -/
def trivSet (ι : Type*) [Fintype ι] [DecidableEq ι] : Finset (ι → Bool) :=
  {fun _ => false, fun _ => true}

/-- `TRIV : {0^n, 1^n} → {0,1}`, `TRIV(b^n) = b` (arXiv:2610.06835, held version,
sha256 6334ffaf…, §6.2, p.53 and §7.1.5, p.63).

**Formalization Note** Written as `TRIV(x) = [x = 1^n]`, which is `b` on `b^n` whenever the
number of positions is at least one. -/
def triv {ι : Type*} [Fintype ι] [DecidableEq ι] (x : trivSet ι) : Bool :=
  decide (x.1 = fun _ => true)

/-- The domain `D_n = g⁻¹(0)^n ∪ g⁻¹(1)^n` of `F_n = TRIV ∘ g` with `n + 1` blocks
(arXiv:2610.06835, held version, sha256 6334ffaf…, Theorem 7.12, p.67 and p.65).

**Formalization Note** The sequence is indexed by `n + 1` (`Fin (n + 1)` blocks), because
`TRIV` on zero bits is not defined; limits are unchanged. -/
noncomputable def trivDomain {κ : Type*} [Fintype κ] [DecidableEq κ] (n : ℕ) (Sg : Finset (κ → Bool))
    (g : Sg → Bool) : Finset (Fin (n + 1) × κ → Bool) :=
  compDomain (trivSet (Fin (n + 1))) Sg g

/-- `F_n = TRIV ∘ g` on `n + 1` blocks (arXiv:2610.06835, held version, Theorem 7.12, p.67). -/
def trivComp {κ : Type*} [Fintype κ] [DecidableEq κ] (n : ℕ) {Sg : Finset (κ → Bool)} (g : Sg → Bool) :
    trivDomain n Sg g → Bool :=
  compose triv g

/-- The correlated distribution `μ_n = (ν₀^{⊗n} + ν₁^{⊗n})/2` on `D_n`, i.e.
`μ_n(x) = (Π_i ν₀(x_i) + Π_i ν₁(x_i))/2` (arXiv:2610.06835, held version, sha256 6334ffaf…,
Theorem 7.12, p.67 and p.65), with `n + 1` blocks. -/
noncomputable def trivDist {κ : Type*} [Fintype κ] [DecidableEq κ] (n : ℕ) {Sg : Finset (κ → Bool)}
    {g : Sg → Bool} (ν₀ ν₁ : Sg → ℝ) : trivDomain n Sg g → ℝ :=
  fun x => ((∏ i, ν₀ (compBlock x i)) + ∏ i, ν₁ (compBlock x i)) / 2

end DistQuantumQuery


