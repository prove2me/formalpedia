-- Prove2me | Definitions.Def_SubadditiveMMS580_Amplification_Supplement_Reservation
-- name    : SubadditiveMMS580_Amplification_Supplement_Reservation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:54:17.635254+00:00
-- url     : https://prove2.me/theorems/0537b75d-5652-43d9-9be4-28538602c1eb
-- title:
--   Sup norm of additive coefficients, choices $(H,\tilde v,\tau)$ and condition (16), and the exponential comparison $R_V(x)=\mathbb E(xZ-V)^+$
-- statement:
--   Goods form a finite set $M=\{0,\dots,m-1\}$. Nonnegative additive coefficients are a vector $\tilde v=(\tilde v(g))_{g\in M}$, valued on a bundle by $\tilde v(B)=\sum_{g\in B}\tilde v(g)$.
--
--   1. The **sup norm** $\|\tilde v\|_\infty=\max_{g\in M}\tilde v(g)$, with value zero when $M$ is empty.
--   2. A **choice** is a triple $(H,\tilde v,\tau)$ of a reserved set $H\subseteq M$, auxiliary coefficients $\tilde v$ and a threshold $\tau\in\mathbb R$. The **empty choice** is $(\emptyset,0,0)$.
--   3. **Condition (16)** for a valuation $v$ and a target $\beta$: for every $B\subseteq M\setminus H$,
--   $$\tilde v(B)>\tau-\|\tilde v\|_\infty\ \Longrightarrow\ v(H\cup B)\ge\beta.$$
--   A choice **for** $(v,\beta)$ is one whose coefficients are nonnegative, vanish on $H$, and satisfy (16).
--   4. **Exponential comparison.** Let $Z,Z_1,\dots,Z_k$ be independent mean-one exponential random variables ($\mathbb P(Z>t)=e^{-t}$ for $t\ge0$). For coefficients $b_1,\dots,b_k$ put $V=\max_j b_jZ_j$, with an empty maximum equal to zero, and
--   $$R_V(x)=\mathbb E\,(xZ-V)^+ .$$
--
--   These objects state the reservation theorem (Theorem 5.2) and the supporting results of §5.2–5.3 and Appendix C.
--
--   **Formalization Note** The competitors are indexed by an arbitrary finite type $\iota$; the variables $Z$ and $Z_j$ are the coordinates `none` and `some j` of the product probability space $\mathbb R^{\mathrm{Option}\,\iota}$ under the product of the mean-one exponential laws (Mathlib's `expMeasure 1`). $R_V(x)$ is the Bochner integral of $(xZ-V)^+$; for $x\ge0$ and $b_j\ge0$ this function is integrable (it is at most $xZ$ almost surely), so the integral is the expectation. The file also registers the instance that `expMeasure 1` is a probability measure.
-- source:
--   Bo Li, Ankang Sun, Toward Constant-Factor Maximin Share Guarantees for Subadditive Valuations, STOC 2027 submission #580 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/580.pdf, sha256 7de124b5706e9e49301a281a1eb418a8ae32d04bf4cf0941b969cc3cde85e485, §5.2, pp. 30–31 (‖ṽ‖∞, fractional allocations, choices, condition (16), Z, V, R_V)

import Mathlib

/-!
# Additive coefficients, choices `(H, ṽ, τ)`, condition (16) and the exponential comparison `R_V`

Bo Li, Ankang Sun, *Toward Constant-Factor Maximin Share Guarantees for Subadditive
Valuations*, STOC 2027 submission #580 (October 2026), §5.2, pp. 30–31: the sup norm `‖ṽ‖∞` of
nonnegative additive coefficients (zero on an empty ground set), choices `(H, ṽ, τ)` and the
reservation condition (16), the mean-one exponential variables `Z, Z_1, …, Z_k`,
`V = max_j b_j Z_j` (empty maximum zero) and `R_V(x) = E (xZ − V)^+`.

Conventions. Goods are `Fin m`. Additive coefficients are vectors `a : Fin m → ℝ`, valued on a
bundle by `∑_{g ∈ B} a g`. The variables `Z` and `Z_j` (`j ∈ ι`) are the coordinates of the
product probability space `Option ι → ℝ` under `Measure.pi` of the mean-one exponential law
`ProbabilityTheory.expMeasure 1` (coordinate `none ↦ Z`, `some j ↦ Z_j`).
-/

set_option autoImplicit false

namespace SubadditiveMMS580.Amplification.Supplement

open MeasureTheory ProbabilityTheory

/-- §5.2 (p. 30): `‖ṽ‖∞ = max_{g ∈ M} ṽ(g)`, with value zero when `M` is empty. -/
noncomputable def supNorm {m : ℕ} (a : Fin m → ℝ) : ℝ :=
  if h : (Finset.univ : Finset (Fin m)).Nonempty then Finset.univ.sup' h a else 0

/-- §5.2 (p. 31): a triple `(H, ṽ, τ)`: a reserved set `H ⊆ M`, auxiliary additive coefficients
`ṽ` and a threshold `τ ∈ ℝ`. -/
structure Choice (m : ℕ) where
  /-- The reserved set `H`. -/
  H : Finset (Fin m)
  /-- The auxiliary coefficients `ṽ(g)`. -/
  coef : Fin m → ℝ
  /-- The threshold `τ`. -/
  τ : ℝ

/-- §5.2 (p. 31): the empty choice `(∅, 0, 0)`. -/
def emptyChoice (m : ℕ) : Choice m := ⟨∅, fun _ => 0, 0⟩

/-- Condition (16) (p. 31) for a valuation `v` and a target `β`: for every `B ⊆ M \ H`,
`ṽ(B) > τ − ‖ṽ‖∞` implies `v(H ∪ B) ≥ β`. -/
def SatisfiesReservation {m : ℕ} (v : Finset (Fin m) → ℝ) (β : ℝ) (c : Choice m) : Prop :=
  ∀ B : Finset (Fin m), Disjoint B c.H →
    c.τ - supNorm c.coef < ∑ g ∈ B, c.coef g → β ≤ v (c.H ∪ B)

/-- §5.2 (p. 31): `(H, ṽ, τ)` is a choice for `(v, β)`: the auxiliary coefficients are
nonnegative and supported outside `H`, and (16) holds. -/
def IsChoice {m : ℕ} (v : Finset (Fin m) → ℝ) (β : ℝ) (c : Choice m) : Prop :=
  (∀ g, 0 ≤ c.coef g) ∧ (∀ g ∈ c.H, c.coef g = 0) ∧ SatisfiesReservation v β c

/-- The mean-one exponential law is a probability measure (`P(Z > t) = e^{-t}`, `t ≥ 0`). -/
instance : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos

/-- §5.2 (p. 31): the joint law of independent mean-one exponential variables `Z` (coordinate
`none`) and `Z_j`, `j ∈ ι` (coordinate `some j`). -/
noncomputable def expPi (ι : Type) [Fintype ι] : Measure (Option ι → ℝ) :=
  Measure.pi fun _ : Option ι => expMeasure 1

/-- §5.2 (p. 31): `V = max_j b_j Z_j` at the outcome `ω`, with an empty maximum equal to zero. -/
noncomputable def maxProd {ι : Type} [Fintype ι] (b : ι → ℝ) (ω : Option ι → ℝ) : ℝ :=
  if h : (Finset.univ : Finset ι).Nonempty then
    Finset.univ.sup' h (fun j => b j * ω (some j)) else 0

/-- §5.2 (p. 31): `R_V(x) = E (xZ − V)^+` for `V = max_j b_j Z_j`, with `Z` independent of the
`Z_j`. -/
noncomputable def expComparison {ι : Type} [Fintype ι] (b : ι → ℝ) (x : ℝ) : ℝ :=
  ∫ ω, max (x * ω none - maxProd b ω) 0 ∂(expPi ι)

end SubadditiveMMS580.Amplification.Supplement


