-- Prove2me | Definitions.Def_SubsetConvFPRAS_ReversibleChain
-- name    : SubsetConvFPRAS_ReversibleChain
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:18:47.179347+00:00
-- url     : https://prove2.me/theorems/561d1e5f-44a3-4bd3-861e-83906c885e93
-- title:
--   Finite reversible continuous-time chains: Laplacian, Dirichlet form, Poincaré inequality, induced chain
-- statement:
--   Let $\Omega$ be a finite set, $\pi$ a probability law on $\Omega$ with $\pi(x)>0$ for every $x$, and $r(x,y)\ge0$ ($x\ne y$) transition rates (§3.3). This file defines, algebraically in the rates:
--
--   1. $\langle f,g\rangle_\pi=\sum_x\pi(x)f(x)g(x)$, $\mathbb E_\pi f$, and $\operatorname{Var}_\pi[f]=\|f-\mathbb E_\pi f\|^2_\pi$.
--   2. The **positive Laplacian** (8) $(L_rf)(x)=\sum_{y\ne x}r(x,y)(f(x)-f(y))$ and the **Dirichlet form** (9) $\mathcal E_r(f,g)=\langle f,L_rg\rangle_\pi$.
--   3. **Reversibility**: $\pi$ positive, summing to $1$, nonnegative off-diagonal rates, and detailed balance (7) $\pi(x)r(x,y)=\pi(y)r(y,x)$.
--   4. **Irreducibility**: every $y$ is reachable from every $x$ along moves of positive rate.
--   5. The **Poincaré inequality** (11) with constant $\gamma$: $\gamma\operatorname{Var}_\pi[f]\le\mathcal E_r(f,f)$ for every $f$; i.e. the spectral gap (10) is at least $\gamma$. The two sets of ratios $\mathcal E_r(f,f)/\operatorname{Var}_\pi[f]$ and $\langle L_rf,L_rf\rangle_\pi/\mathcal E_r(f,f)$ over nonconstant $f$ (Proposition 2.1).
--   6. For $\emptyset\ne B\subseteq\Omega$ (Definition 5.10): the **hitting law** $h(u,y)=\Pr[X_{\tau_B}=y\mid X_0=u]$, characterized by its first-step equations ($h(\cdot,y)=\mathbf 1_y$ on $B$ and $L_r h(\cdot,y)=0$ off $B$); the **induced rates** $r_B(x,y)=r(x,y)+\sum_{u\notin B}r(x,u)h(u,y)$; and the conditioned law $\pi_B(x)=\pi(x)/\pi(B)$.
--
--   Every Markov-chain statement of the mission is phrased through these objects: the Poisson-clock process itself is never needed.
--
--   **Formalization Note** The Laplacian sums over all $y$; the term $y=x$ vanishes, so the diagonal of $r$ plays no role, as in (8). The hitting law is any solution of the first-step system; Proposition 5.11's statement asserts that the system has exactly one solution, so this is the probability the page defines.
-- source:
--   Chen, Liu, An FPRAS for Counting Common Bases of Two Matroids, arXiv:2610.06724 (version held, sha256 6c1d68c2…919476), §3.3, (7)–(11), pp.16–17; Proposition 2.1, p.11; Definition 5.10 and Proposition 5.11, p.23

import Mathlib

open scoped Classical

namespace SubsetConvFPRAS

/-!
# Finite reversible continuous-time chains, algebraically

X. Chen, K. Liu, *An FPRAS for Counting Common Bases of Two Matroids*, arXiv:2610.06724 (version held,
sha256 6c1d68c2…), §3.3, (7)–(11), pp.16–17; Definition 5.10, p.23.

**Formalization Note.**
* A chain is a family of rates `r : Ω → Ω → ℝ`; the Poisson-clock process is not built, since every
  statement on the path of this mission is algebraic in the rates.
* `lapl` sums over all `y`: the term `y = x` vanishes because `f x - f x = 0`, so the diagonal of `r`
  has no effect, in agreement with the sum over `y ≠ x` in (8).
* `dirichlet` is `⟨f, L_r g⟩_π`, the first expression of (9).
* The hitting law `Pr[X_{τ_B} = y | X₀ = u]` of Definition 5.10 is characterized by its first-step
  linear system (`IsHittingLaw`).
-/

variable {Ω : Type} [Fintype Ω]

/-- `⟨f, g⟩_π = ∑_x π(x) f(x) g(x)`, §3.3, p.16. -/
noncomputable def innerPi (π f g : Ω → ℝ) : ℝ := ∑ x, π x * f x * g x

/-- `E_π[f]`. -/
noncomputable def expect (π f : Ω → ℝ) : ℝ := ∑ x, π x * f x

/-- `Var_π[f] = ‖f - E_π[f]‖²_π`, §3.3, p.16. -/
noncomputable def variance (π f : Ω → ℝ) : ℝ := ∑ x, π x * (f x - expect π f) ^ 2

/-- The positive Laplacian (8), p.17: `(L_r f)(x) = ∑_{y ≠ x} r(x,y) (f(x) - f(y))`. -/
noncomputable def lapl (r : Ω → Ω → ℝ) (f : Ω → ℝ) : Ω → ℝ :=
  fun x => ∑ y, r x y * (f x - f y)

/-- The Dirichlet form (9), p.17: `E_r(f,g) = ⟨f, L_r g⟩_π`. -/
noncomputable def dirichlet (π : Ω → ℝ) (r : Ω → Ω → ℝ) (f g : Ω → ℝ) : ℝ :=
  innerPi π f (lapl r g)

/-- §3.3, pp.16–17: `π` is a probability law with `π(x) > 0` for every `x`, the rates are nonnegative
off the diagonal, and detailed balance (7) holds. -/
structure IsReversibleChain (π : Ω → ℝ) (r : Ω → Ω → ℝ) : Prop where
  pos : ∀ x, 0 < π x
  sum_one : ∑ x, π x = 1
  rate_nonneg : ∀ x y, x ≠ y → 0 ≤ r x y
  detailed_balance : ∀ x y, x ≠ y → π x * r x y = π y * r y x

/-- Irreducibility, p.17: every `y` is reached from every `x` along moves of positive rate. -/
def IsIrreducible (r : Ω → Ω → ℝ) : Prop :=
  ∀ x y, Relation.ReflTransGen (fun a b => a ≠ b ∧ 0 < r a b) x y

/-- The Poincaré inequality (11), p.17: the spectral gap (10) is at least `γ`. -/
def HasPoincare (π : Ω → ℝ) (r : Ω → Ω → ℝ) (γ : ℝ) : Prop :=
  ∀ f : Ω → ℝ, γ * variance π f ≤ dirichlet π r f f

/-- The ratios `⟨f, L f⟩_π / Var_π[f]` over nonconstant `f` (Proposition 2.1, (10)). -/
def gapRatiosVar (π : Ω → ℝ) (r : Ω → Ω → ℝ) : Set ℝ :=
  {c | ∃ f : Ω → ℝ, (∃ a b, f a ≠ f b) ∧ c = dirichlet π r f f / variance π f}

/-- The ratios `⟨L f, L f⟩_π / ⟨f, L f⟩_π` over nonconstant `f` (Proposition 2.1). -/
def gapRatiosSq (π : Ω → ℝ) (r : Ω → Ω → ℝ) : Set ℝ :=
  {c | ∃ f : Ω → ℝ, (∃ a b, f a ≠ f b) ∧ c = innerPi π (lapl r f) (lapl r f) / dirichlet π r f f}

/-- `h u y = Pr[X_{τ_B} = y | X₀ = u]`, for `y ∈ B`, characterized by first-step analysis: on `B` it is
the indicator of `y`, and off `B` the function `u ↦ h u y` is harmonic for `L_r`. -/
def IsHittingLaw (r : Ω → Ω → ℝ) (B : Finset Ω) (h : Ω → Ω → ℝ) : Prop :=
  (∀ x ∈ B, ∀ y ∈ B, h x y = if x = y then 1 else 0) ∧
    ∀ u, u ∉ B → ∀ y ∈ B, lapl r (fun v => h v y) u = 0

/-- The induced rates of Definition 5.10, p.23:
`r_B(x,y) = r(x,y) + ∑_{u ∉ B} r(x,u) Pr[X_{τ_B} = y | X₀ = u]`. -/
noncomputable def inducedRate (r : Ω → Ω → ℝ) (B : Finset Ω) (h : Ω → Ω → ℝ) :
    {x // x ∈ B} → {x // x ∈ B} → ℝ :=
  fun x y => r x.1 y.1 + ∑ u, if u ∈ B then 0 else r x.1 u * h u y.1

/-- `π_B(x) = π(x)/π(B)` for `x ∈ B`, Proposition 5.11, p.23. -/
noncomputable def conditionedLaw (π : Ω → ℝ) (B : Finset Ω) : {x // x ∈ B} → ℝ :=
  fun x => π x.1 / ∑ b ∈ B, π b

/-- The support of a weight on `α`, as a state space. -/
abbrev Supp {α : Type} (π : α → ℝ) : Type := {x : α // 0 < π x}

/-- A law restricted to its support. -/
def onSupp {α : Type} (π : α → ℝ) : Supp π → ℝ := fun x => π x.1

/-- Rates restricted to the support of `π`. -/
def onSuppRate {α : Type} (π : α → ℝ) (q : α → α → ℝ) : Supp π → Supp π → ℝ :=
  fun x y => q x.1 y.1

end SubsetConvFPRAS


