-- Prove2me | Definitions.Def_OptAbstention_TLA_Sandwiching
-- name    : OptAbstention_TLA_Sandwiching
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T20:06:16.22665+00:00
-- url     : https://prove2.me/theorems/221efd44-4cfc-4316-b406-128be32936ec
-- title:
--   Concepts on $X\subseteq\mathbb R^d$, L1 sandwiching polynomials, the sandwiching degree $L_1(\varepsilon,B,\mathcal C,D)$ and the moment bound $M_{D,\ell}$
-- statement:
--   Fix $d\in\mathbb N$ and an arbitrary set $X\subseteq\mathbb R^d$ of points $x=(x_1,\dots,x_d)$. A **distribution** $D$ on $X$ is a probability measure on $X$ (subspace $\sigma$-algebra). A **concept** is a measurable $f:X\to\{-1,1\}$; a **concept class** $\mathcal C$ is a set of concepts. For a multi-index $\alpha\in\mathbb N^d$ write $\|\alpha\|_1=\sum_i\alpha_i$ and $x^\alpha=\prod_i x_i^{\alpha_i}$. $\mathcal P_{d,\ell,B}$ is the set of real polynomials in $d$ variables of total degree at most $\ell$ whose monomial coefficients are all at most $B$ in absolute value.
--
--   Polynomials $p_{\mathrm{up}},p_{\mathrm{down}}$ are **$\varepsilon$-approximate L1 sandwiching polynomials** for $f$ under $D$ if
--   $$p_{\mathrm{down}}(x)\le f(x)\le p_{\mathrm{up}}(x)\ \ \forall x\in X,\qquad \mathbb E_{x\sim D}[p_{\mathrm{up}}(x)-p_{\mathrm{down}}(x)]\le\varepsilon .$$
--   The **sandwiching degree** $L_1(\varepsilon,B,\mathcal C,D)$ is the least $\ell\in\mathbb N$ such that every $f\in\mathcal C$ has $\varepsilon$-approximate sandwiching polynomials in $\mathcal P_{d,\ell,B}$; `IsL1Degree D ε B C ℓ` says that $\ell$ is this minimum (so in particular that one exists). The **moment bound** is
--   $$M_{D,\ell}=\max_{\alpha\in\mathbb N^d,\ \|\alpha\|_1\le\ell}\ \mathbb E_{x\sim D}[x^{2\alpha}]\in[1,\infty].$$
--
--   These are the quantities that fix the degree and the sample sizes of every statement of the mission.
--
--   **Formalization Note.** Points are `Fin d → ℝ`, labels $\pm1$ are reals. Expectations of the nonnegative functions $p_{\mathrm{up}}-p_{\mathrm{down}}$ and $x^{2\alpha}$ are lower Lebesgue integrals in $[0,\infty]$, so an infinite moment gives $M_{D,\ell}=\infty$ rather than a junk value.
-- source:
--   Chandrasekaran, Gkrinias, Klivans, Stavropoulos, Vasilyan, Achieving the Optimal Abstention Rate for Learning with Distribution Shift, STOC 2027 submission (manuscript sha256 0fb30af1…), p. 4, Definition 2.1; p. 12, §5 Polynomials; p. 13, Definition 5.1

import Mathlib

/-!
# Points, concepts, L1 sandwiching polynomials, the sandwiching degree and the moment bound

Chandrasekaran, Gkrinias, Klivans, Stavropoulos, Vasilyan, *Achieving the Optimal Abstention Rate
for Learning with Distribution Shift*, STOC 2027 submission (manuscript sha256 0fb30af1…):
§5 "Basic Notation" and "Polynomials" (p. 12), Definition 2.1 (p. 4), Definition 5.1 (p. 13).

Conventions.
* A point of `ℝ^d` is `Fin d → ℝ`; the domain `X ⊆ ℝ^d` is an arbitrary set, and a distribution on
  `X` is a probability measure on the subtype `X` (subspace σ-algebra).
* Labels `±1` are real numbers `1` and `-1`; a concept is a measurable function `X → ℝ` with values
  in `{-1, 1}` (the paper's `Pr_D[f(x) ≠ y]` and `E_D[f p]` are defined only for measurable `f`).
* A multi-index is `α : Fin d → ℕ`, `‖α‖₁ = ∑ i, α i`, and `x^α = ∏ i, x_i^{α_i}`.
* `P_{d,ℓ,B}`: real polynomials in `d` variables of total degree `≤ ℓ` whose monomial coefficients
  are all at most `B` in absolute value.
* Expectations of nonnegative functions (`p_up − p_down` on `X`, `x^{2α}`) are lower Lebesgue
  integrals in `ℝ≥0∞`, so they are never junk values: an infinite moment is `⊤`.
-/

open MeasureTheory

namespace OptAbstention.TLA

/-- A point of `ℝ^d`. -/
abbrev Pt (d : ℕ) := Fin d → ℝ

/-- The `ℓ₁` norm `‖α‖₁ = ∑ i, α i` of a multi-index. -/
def degOf {d : ℕ} (α : Fin d → ℕ) : ℕ := ∑ i, α i

/-- The monomial `x^α = ∏ i, x_i^{α_i}`. -/
def mono {d : ℕ} (α : Fin d → ℕ) (x : Pt d) : ℝ := ∏ i, x i ^ α i

/-- A real number is a label `±1`. -/
def IsSign (y : ℝ) : Prop := y = 1 ∨ y = -1

/-- The real value `±1` of a Boolean label (`true ↦ 1`, `false ↦ -1`). -/
def signOf (b : Bool) : ℝ := if b then 1 else -1

/-- A concept (or classifier) on `X`: a measurable function with values in `{-1, 1}`. -/
def IsConcept {d : ℕ} (X : Set (Pt d)) (f : X → ℝ) : Prop :=
  Measurable f ∧ ∀ x, IsSign (f x)

/-- A concept class `C ⊆ {±1}^X`: every member is a concept. -/
def IsConceptClass {d : ℕ} (X : Set (Pt d)) (C : Set (X → ℝ)) : Prop :=
  ∀ f ∈ C, IsConcept X f

/-- `P_{d,ℓ,B}`: polynomials of total degree at most `ℓ` with every monomial coefficient
absolutely bounded by `B` (`‖p‖_{coef,∞} ≤ B`). -/
def PolyB (d ℓ : ℕ) (B : ℝ) : Set (MvPolynomial (Fin d) ℝ) :=
  {p | p.totalDegree ≤ ℓ ∧ ∀ m, |p.coeff m| ≤ B}

/-- Evaluation of a polynomial at a point of `ℝ^d`. -/
noncomputable def peval {d : ℕ} (p : MvPolynomial (Fin d) ℝ) (x : Pt d) : ℝ :=
  MvPolynomial.eval x p

/-- Definition 2.1: `p_up, p_down` are `ε`-approximate L1 sandwiching polynomials for `f` under
`D`: `p_down ≤ f ≤ p_up` on all of `X`, and `E_{x∼D}[p_up(x) − p_down(x)] ≤ ε`. -/
def IsSandwiching {d : ℕ} {X : Set (Pt d)} (D : Measure X) (ε : ℝ) (f : X → ℝ)
    (pup pdown : MvPolynomial (Fin d) ℝ) : Prop :=
  (∀ x : X, peval pdown x ≤ f x ∧ f x ≤ peval pup x) ∧
    ∫⁻ x, ENNReal.ofReal (peval pup x - peval pdown x) ∂D ≤ ENNReal.ofReal ε

/-- Every `f ∈ C` has `ε`-approximate sandwiching polynomials under `D` of degree at most `ℓ`
with coefficients absolutely bounded by `B`. -/
def SandwichingAtDegree {d : ℕ} {X : Set (Pt d)} (D : Measure X) (ε B : ℝ) (C : Set (X → ℝ))
    (ℓ : ℕ) : Prop :=
  ∀ f ∈ C, ∃ pup ∈ PolyB d ℓ B, ∃ pdown ∈ PolyB d ℓ B, IsSandwiching D ε f pup pdown

/-- Definition 2.1: `ℓ = L1(ε, B, C, D)`, the minimum `ℓ ∈ ℕ` at which every concept of `C` has
`ε`-approximate sandwiching polynomials of degree at most `ℓ` with coefficients bounded by `B`.
The predicate holds exactly when such an `ℓ` exists and `ℓ` is the least one. -/
def IsL1Degree {d : ℕ} {X : Set (Pt d)} (D : Measure X) (ε B : ℝ) (C : Set (X → ℝ))
    (ℓ : ℕ) : Prop :=
  SandwichingAtDegree D ε B C ℓ ∧ ∀ ℓ' < ℓ, ¬ SandwichingAtDegree D ε B C ℓ'

/-- Definition 5.1: the degree-`ℓ` moment bound `M_{D,ℓ} = max_{‖α‖₁ ≤ ℓ} E_{x∼D}[x^{2α}]`,
valued in `ℝ≥0∞` (it is `⊤` when some such moment is infinite). -/
noncomputable def momentBound {d : ℕ} {X : Set (Pt d)} (D : Measure X) (ℓ : ℕ) : ENNReal :=
  ⨆ (α : Fin d → ℕ) (_ : degOf α ≤ ℓ),
    ∫⁻ x, ENNReal.ofReal (mono (fun i => 2 * α i) (x : Pt d)) ∂D

end OptAbstention.TLA


