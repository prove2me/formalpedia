-- Prove2me | solution 1 for AaronsonAmbainis.aaronson_ambainis_conjecture
-- status  : ACCEPTED   (prove)
-- author  : @Abhishek Anand
-- created : 2026-11-06T21:56:57.809294+00:00
-- url     : https://prove2.me/submissions/2f9b896a-d7e3-4492-bb66-c92bf0924ce4

import Mathlib
import Definitions.Def_AaronsonAmbainis

/-
Copyright 2026 David Turturean.

This is an attributed packaging/adaptation of the Lean proof in
https://github.com/physical-superintelligence/aaronson-ambainis
release commit 2a6ceaef872ae993708950f951989134084b851a.

MODIFICATIONS, 6 November 2026: the dependency closure is concatenated in
topological order, with a section around each original module to preserve
module-local variable and notation scopes; project imports are replaced
by preceding source; the final adapter unfolds the Prove2Me definitions
and witnesses the existential exponent with 7. The upstream mathematical
proof and formalization are due to David Turturean / PSI. This adaptation
does not claim an independent proof or a simplification of that proof.

Licensed under the Apache License, Version 2.0. A copy of the full license
and upstream NOTICE is included at the end of this file.
-/

set_option autoImplicit false


/- BEGIN UPSTREAM MODULE: AaronsonAmbainis.Defs -/
section
/-!
# Definitions

The definitions of Section 2 of the paper: the cube, the points `x^S`, the antipode and the set
`Δ(x,y)`; the numbers `b_j(g)` and the zone of a Boolean function; 1-wings and rows; the
influences of Boolean and of real functions, mean and variance, the mean absolute increments; the
characters and the degree.

Points of the cube are functions `ι → Bool` for a finite index type `ι` (the paper's `[n]`).
The paper writes the cube as `Q_n = {-1,1}^n`, and as `{0,1}^n` in Corollary 1.2; the
identification is `false ↦ 0 ↦ +1`, `true ↦ 1 ↦ -1`.
-/

namespace AaronsonAmbainis

open Finset

/-- The Boolean cube `{0,1}^n`. -/
abbrev Cube (ι : Type*) := ι → Bool

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `flipSet x S` is the point `x` with exactly the coordinates in `S` flipped
(written `x^S` in the paper). -/
def flipSet (x : Cube ι) (S : Finset ι) : Cube ι :=
  fun i => if i ∈ S then !(x i) else x i

/-- The antipode of `x` (all coordinates flipped). -/
def antipode (x : Cube ι) : Cube ι := fun i => !(x i)

/-- `diffSet x y` is the set of coordinates in which `x` and `y` differ
(written `Δ(x,y)` in the paper). -/
def diffSet (x y : Cube ι) : Finset ι := univ.filter fun i => x i ≠ y i

/-- `bdry g j = b_j(g)`: the number of bichromatic `j`-edges of `g`; each such
edge is counted once, at its endpoint where `g = true`. -/
def bdry (g : Cube ι → Bool) (j : ι) : ℕ :=
  (univ.filter fun x : Cube ι => g x = true ∧ g (flipSet x {j}) = false).card

/-- `zone g = Z(g)`: the points `u` with `g u = true` and `g (antipode u) = false`. -/
def zone (g : Cube ι → Bool) : Finset (Cube ι) :=
  univ.filter fun u => g u = true ∧ g (antipode u) = false

/-- `A` is a 1-wing of `g` at `u`: flipping any subset of `A` at `u` keeps `g = true`. -/
def IsWing (g : Cube ι → Bool) (u : Cube ι) (A : Finset ι) : Prop :=
  ∀ S : Finset ι, S ⊆ A → g (flipSet u S) = true

/-- `lam` is a row (fractional certificate) of `g` at `x`: it is nonnegative and has
total weight at least one on every sensitive block of `g` at `x`. -/
def IsRow (g : Cube ι → Bool) (x : Cube ι) (lam : ι → ℝ) : Prop :=
  (∀ j, 0 ≤ lam j) ∧ ∀ S : Finset ι, g (flipSet x S) ≠ g x → 1 ≤ ∑ j ∈ S, lam j

/-- Influence of coordinate `j` on a Boolean function, uniform measure: the fraction
of points `x` with `g (x^j) ≠ g x` (written `I_j(g)` in the paper). -/
noncomputable def infl (g : Cube ι → Bool) (j : ι) : ℝ :=
  ((univ.filter fun x : Cube ι => g (flipSet x {j}) ≠ g x).card : ℝ) / 2 ^ Fintype.card ι

/-- Mean of a real function on the cube. -/
noncomputable def mean (f : Cube ι → ℝ) : ℝ := (∑ x, f x) / 2 ^ Fintype.card ι

/-- Variance of a real function on the cube. -/
noncomputable def variance (f : Cube ι → ℝ) : ℝ := (∑ x, (f x - mean f) ^ 2) / 2 ^ Fintype.card ι

/-- Influence of coordinate `j` on a real function: `E[((f(x) - f(x^j))/2)^2]`
(written `Inf_j(f)` in the paper). -/
noncomputable def inflR (f : Cube ι → ℝ) (j : ι) : ℝ :=
  (∑ x, ((f x - f (flipSet x {j})) / 2) ^ 2) / 2 ^ Fintype.card ι

/-- The mean absolute increment of a real function in the coordinate `j`: `E_x |f(x) - f(x^j)|`
(written `L_j(f)` in the paper; their sum over `j` is written `L(f)`). There is no factor `1/2`
here, so that `L_j(f)^2 ≤ 4 Inf_j(f)`. -/
noncomputable def meanAbsIncr (f : Cube ι → ℝ) (j : ι) : ℝ :=
  (∑ x, |f x - f (flipSet x {j})|) / 2 ^ Fintype.card ι

/-- The character `χ_S(x) = ∏_{i ∈ S} (-1)^{x_i}`. -/
noncomputable def chi (S : Finset ι) (x : Cube ι) : ℝ :=
  ∏ i ∈ S, (if x i then (-1 : ℝ) else 1)

/-- `f` is the restriction to the cube of a multilinear polynomial of degree at most `d`:
its expansion in characters uses only sets of size at most `d`. -/
def HasDegreeLE (f : Cube ι → ℝ) (d : ℕ) : Prop :=
  ∃ c : Finset ι → ℝ, (∀ S, d < S.card → c S = 0) ∧ ∀ x, f x = ∑ S, c S * chi S x

end AaronsonAmbainis

end
/- END UPSTREAM MODULE: AaronsonAmbainis.Defs -/

/- BEGIN UPSTREAM MODULE: AaronsonAmbainis.Statements -/
section
/-!
# The statements of the chain, as propositions

The links of the proof are stated here as propositions. All of them except `RowBound` and
`MainTheoremImproved` are proved, with no hypothesis, in the directories `DetLow`, `DetBij`,
`TwoSided`, `Level`, `Average` and `Row` and in `MainTheorem.lean`; the proofs are assembled in
`Chain.lean`. Numbering refers to the paper.

* `DetInequality`       — the determinant inequality (Corollary 3.2)
* `AntipodalInequality` — the antipodal inequality (Theorem 4.3)
* `TwoSidedInequality`  — the two-sided inequality (Theorem 5.4)
* `IntegratedAllPairsInequality` — the integrated all-pairs inequality, for a real function with
                          a row at every point (Proposition 7.4)
* `ThirdMomentInequality` — the third-moment inequality (Theorem 7.6)
* `MeanIncrementBound`  — the bound for the mean absolute increments of a function with rows of
                          cost at most `K` (Theorem 7.10)
* `InfluenceBound`      — the bound for the influences of a function with rows of cost at most
                          `K` (Theorem 8.3)
* `SensitivityBound`    — the sensitivity of a bounded function of degree at most `d`, at every
                          point (Corollary 6.10)
* `MainTheorem`         — the main theorem (Theorem 1.1)
* `MeanIncrementDegreeBound` — the bound for the mean absolute increments of a bounded function
                          of degree at most `d` (Corollary 7.11)
* `RowBound`            — the row bound of Agarwal and Ben-David (Theorem 1.7 of
                          arXiv:2410.19062); it is not proved in this project and is used
                          only as a named hypothesis, never as an axiom
* `MainTheoremImproved` — the main theorem with the constant that `RowBound` gives
                          (Remark 8.4); it is proved from `RowBound`

The all-pairs inequality for Boolean functions (Proposition 5.2) is stated in
`AllPairsDefs.lean`, the two halves of the proof of the determinant inequality in `DetDefs.lean`,
and the links of the proof of the row bound (Theorem 6.8) in `RowDefs.lean`.

A row of a real function `f` at every point is given as a family `a : Cube ι → ι → ℝ` with
`0 ≤ a x j` and `|f x - f y| ≤ ∑_{j ∈ Δ(x,y)} a x j` for all `x`, `y`; its cost at `x` is
`∑_j a x j`. (This is Definition 2.3 of the paper, with `y = x^S` and `S = Δ(x,y)`.) The mean
absolute increment of `f` in the coordinate `j` is `L_j(f) = meanAbsIncr f j = E_x |f x - f (x^j)|`,
and `L(f) = ∑_j L_j(f)`.
-/

namespace AaronsonAmbainis

open Finset

/-- The determinant inequality (Corollary 3.2 of the paper).
For every Boolean `g`, all positive lengths `ℓ`, and every choice of
1-wings `A u` at the points `u` of `zone g`: if `d u` is at most the length of every
`G` disjoint from `A u` with `g ((antipode u)^G) = true`, then `∑_{u ∈ zone g} d u`
is at most `∑_j ℓ_j b_j(g)`.  (So `d u` may be taken to be the minimum `D_g(u, A u; ℓ)`.) -/
def DetInequality : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (g : Cube ι → Bool) (ℓ : ι → ℝ), (∀ j, 0 < ℓ j) →
  ∀ (A : Cube ι → Finset ι), (∀ u ∈ zone g, IsWing g u (A u)) →
  ∀ (d : Cube ι → ℝ),
    (∀ u ∈ zone g, ∀ G : Finset ι, Disjoint G (A u) →
        g (flipSet (antipode u) G) = true → d u ≤ ∑ j ∈ G, ℓ j) →
    ∑ u ∈ zone g, d u ≤ ∑ j, ℓ j * (bdry g j : ℝ)

/-- The antipodal inequality (the inequality of Theorem 4.3 of the paper).
For every Boolean `g`, all positive weights `w` and every row field `lam`:
`∑_{u ∈ zone g} 1 / (∑_j w_j lam^u_j lam^{ū}_j) ≤ ∑_j b_j(g) / w_j`.
(The reciprocal is `⁻¹`, with `0⁻¹ = 0` in Lean; that the denominators are positive is the other
assertion of Theorem 4.3 and is not part of this proposition.) -/
def AntipodalInequality : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (g : Cube ι → Bool) (w : ι → ℝ), (∀ j, 0 < w j) →
  ∀ (lam : Cube ι → ι → ℝ), (∀ x, IsRow g x (lam x)) →
    ∑ u ∈ zone g, (∑ j, w j * lam u j * lam (antipode u) j)⁻¹ ≤ ∑ j, (bdry g j : ℝ) / w j

/-- The two-sided inequality (the inequality of Theorem 5.4 of the paper).
For every Boolean `g` and every row field `lam`, with `v x = 1 / ‖lam x‖₁`:
`4 · E[v · 1_{g = true}] · E[v · 1_{g = false}] ≤ τ` whenever `τ ≥ 0` bounds all influences
`I_j(g)`. (In the paper `g` is not constant and `τ = max_j I_j(g)`.) -/
def TwoSidedInequality : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (g : Cube ι → Bool) (lam : Cube ι → ι → ℝ), (∀ x, IsRow g x (lam x)) →
  ∀ τ : ℝ, 0 ≤ τ → (∀ j, infl g j ≤ τ) →
    4 * ((∑ x ∈ univ.filter (fun x : Cube ι => g x = true), (∑ j, lam x j)⁻¹) / 2 ^ Fintype.card ι)
      * ((∑ x ∈ univ.filter (fun x : Cube ι => g x = false), (∑ j, lam x j)⁻¹) / 2 ^ Fintype.card ι) ≤ τ

/-- The integrated all-pairs inequality (the inequality of Proposition 7.4 of the paper). For a
real function `f` on the cube, a row `a x` of `f` at every point `x` and all positive weights `w`:
`∑_{(x,y) : f y < f x} (f x - f y)^3 / (6 s_xy) ≤ 4^(n-1) ∑_j L_j(f) / w_j`, where
`s_xy = ∑_{j ∈ Δ(x,y)} w_j a^x_j a^y_j` and `L_j(f) = meanAbsIncr f j = E_x |f x - f (x^j)|`.
(That the sums `s_xy` in the denominators are positive is the other assertion of
Proposition 7.4: `Level.pairSum_pos`. The exponent `n - 1` is a difference of natural numbers;
for `n = 0` it is `0`, and both sides of the inequality are `0`.) -/
def IntegratedAllPairsInequality : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (f : Cube ι → ℝ) (a : Cube ι → ι → ℝ),
    (∀ x j, 0 ≤ a x j) → (∀ x y, |f x - f y| ≤ ∑ j ∈ diffSet x y, a x j) →
  ∀ (w : ι → ℝ), (∀ j, 0 < w j) →
    ∑ x, ∑ y ∈ univ.filter (fun y : Cube ι => f y < f x),
        (f x - f y) ^ 3 / (6 * ∑ j ∈ diffSet x y, w j * a x j * a y j)
      ≤ 4 ^ (Fintype.card ι - 1) * ∑ j, meanAbsIncr f j / w j

/-- The third-moment inequality (the first inequality of Theorem 7.6 of the paper). If `f` has a
row of cost at most `K` at every point and `M ≥ 0` bounds all the mean absolute increments
`L_j(f) = meanAbsIncr f j`, then for every real `r`
`E[((f - r)⁺)^3] · Pr[f ≤ r] ≤ (3/2) K² M`. (The second inequality of Theorem 7.6, for `(r - f)⁺`
and `Pr[f ≥ r]`, is this one for `-f` and `-r`: `Level.thirdMoment_lower`.) -/
def ThirdMomentInequality : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (f : Cube ι → ℝ) (K : ℝ) (a : Cube ι → ι → ℝ),
    (∀ x j, 0 ≤ a x j) → (∀ x, ∑ j, a x j ≤ K) →
    (∀ x y, |f x - f y| ≤ ∑ j ∈ diffSet x y, a x j) →
  ∀ (M : ℝ), 0 ≤ M → (∀ j, meanAbsIncr f j ≤ M) → ∀ r : ℝ,
    (∑ x, max (f x - r) 0 ^ 3) / 2 ^ Fintype.card ι
        * (((univ.filter (fun y : Cube ι => f y ≤ r)).card : ℝ) / 2 ^ Fintype.card ι)
      ≤ 3 / 2 * K ^ 2 * M

/-- The bound for the mean absolute increments (Theorem 7.10 of the paper). If `f` has a row of
cost at most `K` at every point and `Var(f) > 0`, then some coordinate `j` has
`Var(f)^3 ≤ 36 K^4 L_j(f)^2`, that is, `E_x |f(x) - f(x^j)| ≥ Var(f)^{3/2} / (6 K²)`. No bound on
the values of `f` is assumed. (The other assertions of Theorem 7.10, `n ≥ 1` and `K > 0`, hold
because the variance is positive; `K > 0` is `Level.cost_pos`. The statement of the paper with
all its assertions is `Bridge.MeanIncrementPrinted`.) -/
def MeanIncrementBound : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (f : Cube ι → ℝ) (K : ℝ) (a : Cube ι → ι → ℝ),
    (∀ x j, 0 ≤ a x j) → (∀ x, ∑ j, a x j ≤ K) →
    (∀ x y, |f x - f y| ≤ ∑ j ∈ diffSet x y, a x j) → 0 < variance f →
    ∃ j, variance f ^ 3 ≤ 36 * K ^ 4 * meanAbsIncr f j ^ 2

/-- The bound for the influences (Theorem 8.3 of the paper). If `f` has a row of cost at most `K`
at every point and `Var(f) > 0`, then some coordinate `j` has
`3 Var(f)^5 ≤ 3125 L(f)² K^4 Inf_j(f)^2`, where `L(f) = ∑_k L_k(f)` is the sum of the mean
absolute increments; that is, `Inf_j(f) ≥ (√15 / 125) Var(f)^{5/2} / (L(f) K²)`. No bound on the
values of `f` is assumed. (The other assertions of Theorem 8.3: `0 < L(f)` is
`Average.sum_meanAbsIncr_pos`, and `L(f) ≤ K` is `Level.sum_meanAbsIncr_le_cost`. The statement
of the paper with all its assertions is `Bridge.InfluencePrinted`.) -/
def InfluenceBound : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (f : Cube ι → ℝ) (K : ℝ) (a : Cube ι → ι → ℝ),
    (∀ x j, 0 ≤ a x j) → (∀ x, ∑ j, a x j ≤ K) →
    (∀ x y, |f x - f y| ≤ ∑ j ∈ diffSet x y, a x j) → 0 < variance f →
    ∃ j, 3 * variance f ^ 5 ≤ 3125 * (∑ k, meanAbsIncr f k) ^ 2 * K ^ 4 * inflR f j ^ 2

/-- The sensitivity bound at every point (Corollary 6.10 of the paper). If `|f| ≤ 1` and `f` has
degree at most `d`, then `∑_j |f(x) - f(x^j)| ≤ 4 d²` at every point `x`. (Consequently
`L(f) ≤ 4 d²`: `Level.sum_meanAbsIncr_le`.) -/
def SensitivityBound : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (d : ℕ) (f : Cube ι → ℝ), (∀ x, |f x| ≤ 1) →
    HasDegreeLE f d → ∀ x : Cube ι, ∑ j, |f x - f (flipSet x {j})| ≤ 4 * (d : ℝ) ^ 2

/-- The main theorem (Theorem 1.1 of the paper). Every `f` on the cube with `|f| ≤ 1`, degree at
most `d` and positive variance has a coordinate `j` with
`3 Var(f)^5 ≤ 50000 π^8 d^12 Inf_j(f)^2`, that is,
`Inf_j(f) ≥ (√15 / (500 π^4)) Var(f)^{5/2} / d^6`. (The paper assumes `n ≥ 1` and `d ≥ 1` in place
of positive variance; these hold when the variance is positive, and for variance `0` there is
nothing to prove.) -/
def MainTheorem : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (d : ℕ) (f : Cube ι → ℝ), (∀ x, |f x| ≤ 1) →
    HasDegreeLE f d → 0 < variance f →
    ∃ j, 3 * variance f ^ 5 ≤ 50000 * Real.pi ^ 8 * (d : ℝ) ^ 12 * inflR f j ^ 2

/-- The bound for the mean absolute increments of a bounded function of low degree
(Corollary 7.11 of the paper). Every `f` on the cube with `|f| ≤ 1`, degree at most `d` and
positive variance has a coordinate `j` with `Var(f)^3 ≤ 36 π^8 d^8 L_j(f)^2`, that is,
`E_x |f(x) - f(x^j)| ≥ Var(f)^{3/2} / (6 π^4 d^4)`. -/
def MeanIncrementDegreeBound : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (d : ℕ) (f : Cube ι → ℝ), (∀ x, |f x| ≤ 1) →
    HasDegreeLE f d → 0 < variance f →
    ∃ j, variance f ^ 3 ≤ 36 * Real.pi ^ 8 * (d : ℝ) ^ 8 * meanAbsIncr f j ^ 2

/-- The row bound of Agarwal and Ben-David (Theorem 1.7 of arXiv:2410.19062): every
`f : {0,1}^n → [0,1]` of degree at most `d` has weights `c x i` with
`∑_{i : x_i ≠ y_i} c x i ≥ |f x - f y|` for all `x, y` and `∑_i c x i ≤ (π²/4) d²` for all `x`.
(Nonnegativity of the weights is not required: it follows from the first condition
with `y = x^i`.) This proposition is not proved in the project; it occurs only as a
hypothesis. -/
def RowBound : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (d : ℕ) (f : Cube ι → ℝ), (∀ x, 0 ≤ f x ∧ f x ≤ 1) → HasDegreeLE f d →
    ∃ c : Cube ι → ι → ℝ,
      (∀ x y, |f x - f y| ≤ ∑ i ∈ diffSet x y, c x i) ∧
      (∀ x, ∑ i, c x i ≤ Real.pi ^ 2 / 4 * (d : ℝ) ^ 2)

/-- The main theorem with the constant that the row bound of Agarwal and Ben-David gives
(Remark 8.4 of the paper). Every `f` on the cube with `|f| ≤ 1`, degree at most `d` and positive
variance has a coordinate `j` with `3 Var(f)^5 ≤ 3125 π^8 d^12 Inf_j(f)^2`, that is,
`Inf_j(f) ≥ (√15 / (125 π^4)) Var(f)^{5/2} / d^6`. It is proved from the hypothesis `RowBound`. -/
def MainTheoremImproved : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (d : ℕ) (f : Cube ι → ℝ), (∀ x, |f x| ≤ 1) →
    HasDegreeLE f d → 0 < variance f →
    ∃ j, 3 * variance f ^ 5 ≤ 3125 * Real.pi ^ 8 * (d : ℝ) ^ 12 * inflR f j ^ 2

end AaronsonAmbainis

end
/- END UPSTREAM MODULE: AaronsonAmbainis.Statements -/

/- BEGIN UPSTREAM MODULE: AaronsonAmbainis.DetDefs -/
section
/-!
# Interface for the proof of the determinant inequality

This file defines the lowest monomials of a polynomial (`IsLowest`, Section 3.2 of the paper)
and the agreement matrix (`agMatrix`, Section 3.3), and splits the proof of `DetInequality`
(Corollary 3.2) into two independent parts:

* `LowestUnit`  — multiplying by a polynomial with constant coefficient `1` does not change
                   the monomials of least total degree (Lemma 3.3);
* `LowestBound` — the determinant of the agreement matrix on the ones of `g` is nonzero, and
                   each of its monomials of least total degree has exponent at most
                   `bdry g j` in every variable `j` (Lemma 3.4 and Lemma 3.6).

The directory `DetLow` proves `LowestUnit` and `LowestBound`.
The directory `DetBij` proves `LowestUnit → LowestBound → DetInequality`.
-/

namespace AaronsonAmbainis

open Finset MvPolynomial

section
variable {ι : Type} [Fintype ι]

/-- `m` is a monomial of `q` of least total degree. -/
def IsLowest (q : MvPolynomial ι ℤ) (m : ι →₀ ℕ) : Prop :=
  m ∈ q.support ∧ ∀ m' ∈ q.support, ∑ i, m i ≤ ∑ i, m' i

/-- `agMon x z = ∏_{i : x_i = z_i} s_i`: the monomial of the agreement set of `x` and `z`. -/
noncomputable def agMon (x z : Cube ι) : MvPolynomial ι ℤ :=
  ∏ i, if x i = z i then X i else 1

end

section
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The ones of `g`, as a type. -/
abbrev Ones (g : Cube ι → Bool) := {x : Cube ι // g x = true}

/-- The agreement matrix `M[x,z] = s^{ag(x,z)}` on the ones of `g`. -/
noncomputable def agMatrix (g : Cube ι → Bool) :
    Matrix (Ones g) (Ones g) (MvPolynomial ι ℤ) :=
  fun x z => agMon x.1 z.1

end

/-- Multiplying by a polynomial with constant coefficient `1` does not change the
monomials of least total degree. -/
def LowestUnit : Prop :=
  ∀ (ι : Type) [Fintype ι] (u q : MvPolynomial ι ℤ), constantCoeff u = 1 →
    ∀ m : ι →₀ ℕ, IsLowest (u * q) m ↔ IsLowest q m

/-- The determinant of the agreement matrix is nonzero, and each of its monomials of least
total degree has exponent at most `bdry g j` in every variable `j`. -/
def LowestBound : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (g : Cube ι → Bool),
    (agMatrix g).det ≠ 0 ∧
      ∀ m : ι →₀ ℕ, IsLowest (agMatrix g).det m → ∀ j, m j ≤ bdry g j

end AaronsonAmbainis

end
/- END UPSTREAM MODULE: AaronsonAmbainis.DetDefs -/

/- BEGIN UPSTREAM MODULE: AaronsonAmbainis.DetLow.Unit -/
section
/-!
# DetLow: multiplication by a polynomial with constant coefficient 1

Multiplying by a polynomial with constant coefficient `1` does not change the monomials of
least total degree. This is Lemma 3.3 of the paper.
-/

namespace AaronsonAmbainis
namespace DetLow

open Finset MvPolynomial

/-- Key computation: if every monomial of `q` has total degree at least that of `m`, then
`u * q` and `q` have the same coefficient at `m` (when `u` has constant coefficient `1`). -/
theorem coeff_unit_mul {ι : Type} [Fintype ι] (u q : MvPolynomial ι ℤ)
    (hu : constantCoeff u = 1) (m : ι →₀ ℕ)
    (hm : ∀ m' ∈ q.support, ∑ i, m i ≤ ∑ i, m' i) :
    coeff m (u * q) = coeff m q := by
  classical
  rw [coeff_mul, Finset.sum_eq_single (0, m)]
  · have h0 : coeff 0 u = 1 := hu
    simp [h0]
  · rintro ⟨a, b⟩ hab hne
    have hsum : a + b = m := by simpa using hab
    have ha : a ≠ 0 := by
      rintro rfl
      apply hne
      rw [zero_add] at hsum
      rw [hsum]
    have hb : coeff b q = 0 := by
      by_contra h
      have h1 := hm b (mem_support_iff.mpr h)
      obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact ha (Finsupp.ext hcon)
      have h2 : 1 ≤ ∑ i, a i :=
        (Nat.one_le_iff_ne_zero.mpr hi).trans
          (Finset.single_le_sum (f := fun i => a i) (fun _ _ => Nat.zero_le _)
            (Finset.mem_univ i))
      have h3 : ∑ i, m i = ∑ i, a i + ∑ i, b i := by
        rw [← hsum]
        simp [Finset.sum_add_distrib]
      omega
    simp [hb]
  · intro h
    exact absurd (by simp) h

/-- Forward direction of `LowestUnit`. -/
theorem isLowest_unit_mul {ι : Type} [Fintype ι] (u q : MvPolynomial ι ℤ)
    (hu : constantCoeff u = 1) (m : ι →₀ ℕ) (h : IsLowest q m) : IsLowest (u * q) m := by
  obtain ⟨hmem, hmin⟩ := h
  refine ⟨?_, ?_⟩
  · rw [mem_support_iff, coeff_unit_mul u q hu m hmin]
    exact mem_support_iff.mp hmem
  · intro m' hm'
    by_contra hlt
    push Not at hlt
    have hmin' : ∀ m'' ∈ q.support, ∑ i, m' i ≤ ∑ i, m'' i := fun m'' h'' =>
      hlt.le.trans (hmin m'' h'')
    have h1 := coeff_unit_mul u q hu m' hmin'
    have h2 : coeff m' q = 0 := by
      by_contra hne
      have := hmin m' (mem_support_iff.mpr hne)
      omega
    rw [mem_support_iff, h1] at hm'
    exact hm' h2

/-- A nonzero polynomial has a monomial of least total degree. -/
theorem exists_isLowest {ι : Type} [Fintype ι] (q : MvPolynomial ι ℤ) (hq : q ≠ 0) :
    ∃ m, IsLowest q m := by
  have hne : q.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    exact hq (support_eq_empty.mp h)
  obtain ⟨m, hm, hmin⟩ := Finset.exists_min_image q.support (fun m => ∑ i, m i) hne
  exact ⟨m, hm, hmin⟩

/-- Backward direction of `LowestUnit`. -/
theorem isLowest_of_unit_mul {ι : Type} [Fintype ι] (u q : MvPolynomial ι ℤ)
    (hu : constantCoeff u = 1) (m : ι →₀ ℕ) (h : IsLowest (u * q) m) : IsLowest q m := by
  have hq : q ≠ 0 := by
    rintro rfl
    have h0 := h.1
    simp at h0
  obtain ⟨m0, hm0⟩ := exists_isLowest q hq
  have hm0' := isLowest_unit_mul u q hu m0 hm0
  have hle1 : ∑ i, m i ≤ ∑ i, m0 i := h.2 m0 hm0'.1
  have hmin : ∀ m' ∈ q.support, ∑ i, m i ≤ ∑ i, m' i := fun m' hm' =>
    hle1.trans (hm0.2 m' hm')
  refine ⟨?_, hmin⟩
  have h1 := h.1
  rw [mem_support_iff, coeff_unit_mul u q hu m hmin] at h1
  exact mem_support_iff.mpr h1

end DetLow
end AaronsonAmbainis

end
/- END UPSTREAM MODULE: AaronsonAmbainis.DetLow.Unit -/

/- BEGIN UPSTREAM MODULE: AaronsonAmbainis.DetLow.Basic -/
section
/-!
# DetLow: basic definitions

`Up g j` is the set of ones `x` of `g` with `x j = true` whose `j`-neighbour is also a one
(the upper endpoints of the `j`-edges inside the ones of `g`); its cardinality is the number
`e_j` of Section 3.3 of the paper. (With the identification `true ↦ -1` of `Defs.lean`, the set
`Up_j` of the paper consists of the other endpoints of the same edges; it is `Dn g j` of
`Count.lean`, and it has the same cardinality.)
-/

namespace AaronsonAmbainis
namespace DetLow

open Finset MvPolynomial

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The upper endpoints of the `j`-edges inside the ones of `g`. -/
def Up (g : Cube ι → Bool) (j : ι) : Finset (Ones g) :=
  univ.filter fun x => x.1 j = true ∧ g (flipSet x.1 {j}) = true

theorem mem_Up {g : Cube ι → Bool} {j : ι} {x : Ones g} :
    x ∈ Up g j ↔ x.1 j = true ∧ g (flipSet x.1 {j}) = true := by
  simp [Up]

omit [Fintype ι] in
@[simp] theorem flipSet_singleton_self (x : Cube ι) (j : ι) :
    flipSet x {j} j = !(x j) := by
  simp [flipSet]

omit [Fintype ι] in
theorem flipSet_singleton_of_ne (x : Cube ι) {i j : ι} (h : i ≠ j) :
    flipSet x {j} i = x i := by
  simp [flipSet, h]

omit [Fintype ι] in
@[simp] theorem flipSet_flipSet_singleton (x : Cube ι) (j : ι) :
    flipSet (flipSet x {j}) {j} = x := by
  funext i
  by_cases h : i = j
  · subst h; simp [flipSet]
  · simp [flipSet, h]

end DetLow
end AaronsonAmbainis

end
/- END UPSTREAM MODULE: AaronsonAmbainis.DetLow.Basic -/

/- BEGIN UPSTREAM MODULE: AaronsonAmbainis.DetLow.NonZero -/
section
/-!
# DetLow: the determinant of the agreement matrix is nonzero

This is Lemma 3.4 of the paper.
Evaluate every variable at the real number `c = 2 ^ n` (`n = Fintype.card ι`). The evaluated
matrix has diagonal entries `c ^ n` and off-diagonal entries `c ^ k` with `k + 1 ≤ n`, and a row
has fewer than `2 ^ n = c` off-diagonal entries, so the matrix is strictly diagonally dominant
and its determinant is nonzero (Gershgorin: `det_ne_zero_of_sum_row_lt_diag`).
-/

namespace AaronsonAmbainis
namespace DetLow

open Finset MvPolynomial

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Evaluation of all variables at the real number `c`. -/
noncomputable def evalAt (c : ℝ) : MvPolynomial ι ℤ →+* ℝ :=
  eval₂Hom (Int.castRingHom ℝ) (fun _ => c)

/-- The number of coordinates in which `x` and `z` agree. -/
def agCount (x z : Cube ι) : ℕ := (univ.filter fun i => x i = z i).card

omit [DecidableEq ι] in
theorem evalAt_agMon (c : ℝ) (x z : Cube ι) :
    evalAt c (agMon x z) = c ^ agCount x z := by
  have h : ∀ i, evalAt c (if x i = z i then (X i : MvPolynomial ι ℤ) else 1)
      = if x i = z i then c else 1 := by
    intro i
    by_cases hi : x i = z i
    · rw [if_pos hi, if_pos hi]
      simp [evalAt]
    · rw [if_neg hi, if_neg hi, map_one]
  unfold agMon agCount
  rw [map_prod]
  simp_rw [h]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]

omit [DecidableEq ι] in
theorem agCount_self (x : Cube ι) : agCount x x = Fintype.card ι := by
  simp [agCount]

omit [DecidableEq ι] in
theorem agCount_lt (x z : Cube ι) (h : x ≠ z) : agCount x z < Fintype.card ι := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp h
  unfold agCount
  rw [← Finset.card_univ]
  apply Finset.card_lt_card
  rw [Finset.filter_ssubset]
  exact ⟨i, mem_univ i, hi⟩

theorem evalMat_apply (c : ℝ) (g : Cube ι → Bool) (x z : Ones g) :
    (evalAt c).mapMatrix (agMatrix g) x z = c ^ agCount x.1 z.1 :=
  evalAt_agMon c x.1 z.1

/-- A row of the ones of `g` has fewer than `2 ^ n` off-diagonal entries. -/
theorem card_erase_succ_le (g : Cube ι → Bool) (x : Ones g) :
    (univ.erase x).card + 1 ≤ 2 ^ Fintype.card ι := by
  have h2 : (univ.erase x).card < (univ : Finset (Ones g)).card :=
    Finset.card_erase_lt_of_mem (mem_univ x)
  have h3 : (univ : Finset (Ones g)).card ≤ 2 ^ Fintype.card ι := by
    rw [Finset.card_univ]
    calc Fintype.card (Ones g) ≤ Fintype.card (Cube ι) := Fintype.card_subtype_le _
      _ = 2 ^ Fintype.card ι := by simp
  omega

/-- The evaluated matrix is strictly diagonally dominant when `c = 2 ^ n`. -/
theorem evalMat_dominant (g : Cube ι → Bool) (c : ℝ) (hc : c = 2 ^ Fintype.card ι)
    (x : Ones g) :
    ∑ z ∈ univ.erase x, ‖(evalAt c).mapMatrix (agMatrix g) x z‖
      < ‖(evalAt c).mapMatrix (agMatrix g) x x‖ := by
  have hc1 : (1 : ℝ) ≤ c := by
    rw [hc]
    exact one_le_pow₀ (by norm_num)
  have hcpos : 0 < c := lt_of_lt_of_le one_pos hc1
  have hcard : ((univ.erase x).card : ℝ) + 1 ≤ c := by
    rw [hc]
    exact_mod_cast card_erase_succ_le g x
  have hpow : 0 < c ^ Fintype.card ι := pow_pos hcpos _
  have hdiag : ‖(evalAt c).mapMatrix (agMatrix g) x x‖ = c ^ Fintype.card ι := by
    rw [evalMat_apply, agCount_self, Real.norm_of_nonneg (pow_nonneg hcpos.le _)]
  have hsum : (∑ z ∈ univ.erase x, ‖(evalAt c).mapMatrix (agMatrix g) x z‖) * c
      ≤ ((univ.erase x).card : ℝ) * c ^ Fintype.card ι := by
    rw [Finset.sum_mul]
    calc ∑ z ∈ univ.erase x, ‖(evalAt c).mapMatrix (agMatrix g) x z‖ * c
        ≤ ∑ _z ∈ univ.erase x, c ^ Fintype.card ι := by
          apply Finset.sum_le_sum
          intro z hz
          have hzx : x.1 ≠ z.1 := fun h => (Finset.ne_of_mem_erase hz) (Subtype.ext h.symm)
          rw [evalMat_apply, Real.norm_of_nonneg (pow_nonneg hcpos.le _), ← pow_succ]
          exact pow_le_pow_right₀ hc1 (agCount_lt x.1 z.1 hzx)
      _ = ((univ.erase x).card : ℝ) * c ^ Fintype.card ι := by
          rw [Finset.sum_const, nsmul_eq_mul]
  rw [hdiag]
  have hlt : (∑ z ∈ univ.erase x, ‖(evalAt c).mapMatrix (agMatrix g) x z‖) * c
      < c ^ Fintype.card ι * c := by
    calc (∑ z ∈ univ.erase x, ‖(evalAt c).mapMatrix (agMatrix g) x z‖) * c
        ≤ ((univ.erase x).card : ℝ) * c ^ Fintype.card ι := hsum
      _ < c * c ^ Fintype.card ι := by
          apply mul_lt_mul_of_pos_right _ hpow
          linarith
      _ = c ^ Fintype.card ι * c := mul_comm _ _
  exact lt_of_mul_lt_mul_right hlt hcpos.le

/-- Lemma 3.4 of the paper: the determinant of the agreement matrix is nonzero. -/
theorem agMatrix_det_ne_zero (g : Cube ι → Bool) : (agMatrix g).det ≠ 0 := by
  intro h0
  have hne : ((evalAt ((2 : ℝ) ^ Fintype.card ι)).mapMatrix (agMatrix g)).det ≠ 0 :=
    det_ne_zero_of_sum_row_lt_diag (fun x => evalMat_dominant g _ rfl x)
  apply hne
  rw [← RingHom.map_det, h0, map_zero]

end DetLow
end AaronsonAmbainis

end
/- END UPSTREAM MODULE: AaronsonAmbainis.DetLow.NonZero -/

/- BEGIN UPSTREAM MODULE: AaronsonAmbainis.DetLow.RowOps -/
section
/-!
# DetLow: `(1 - s_j^2)^(e_j)` divides the determinant of the agreement matrix

This is Lemma 3.5 of the paper.
Row operations: with `P[x,y] = 1` if `x j = true` and `y = x^j` (and `0` otherwise),
`(1 + s_j P) (1 - s_j P) = 1` and `(1 - s_j P) M = D N`, where `D` is diagonal with entry
`1 - s_j^2` at the rows `x ∈ Up g j` and `1` elsewhere. (In the proof of the paper the matrices
`P`, `D`, `N` are called `E`, `Λ`, `M̃`.)
-/

namespace AaronsonAmbainis
namespace DetLow

open Finset MvPolynomial

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Splitting off the `j`-th factor of `agMon`. -/
theorem agMon_eq_mul_erase (x z : Cube ι) (j : ι) :
    agMon x z = (if x j = z j then X j else 1) *
      ∏ i ∈ univ.erase j, (if x i = z i then (X i : MvPolynomial ι ℤ) else 1) := by
  unfold agMon
  exact (Finset.mul_prod_erase univ _ (mem_univ j)).symm

theorem prod_erase_flipSet (x z : Cube ι) (j : ι) :
    ∏ i ∈ univ.erase j, (if flipSet x {j} i = z i then (X i : MvPolynomial ι ℤ) else 1)
      = ∏ i ∈ univ.erase j, (if x i = z i then (X i : MvPolynomial ι ℤ) else 1) := by
  apply Finset.prod_congr rfl
  intro i hi
  rw [flipSet_singleton_of_ne x (Finset.ne_of_mem_erase hi)]

/-- If `x` and `z` agree at `j` then `M[x,z] = s_j * M[x^j,z]`. -/
theorem agMon_of_eq (x z : Cube ι) (j : ι) (h : x j = z j) :
    agMon x z = X j * agMon (flipSet x {j}) z := by
  have hne : ¬ (flipSet x {j} j = z j) := by
    rw [flipSet_singleton_self, ← h]
    cases x j <;> simp
  rw [agMon_eq_mul_erase x z j, agMon_eq_mul_erase (flipSet x {j}) z j, prod_erase_flipSet,
    if_pos h, if_neg hne, one_mul]

/-- If `x` and `z` disagree at `j` then `M[x^j,z] = s_j * M[x,z]`. -/
theorem agMon_of_ne (x z : Cube ι) (j : ι) (h : x j ≠ z j) :
    agMon (flipSet x {j}) z = X j * agMon x z := by
  have heq : flipSet x {j} j = z j := by
    rw [flipSet_singleton_self]
    revert h
    cases x j <;> cases z j <;> simp
  rw [agMon_eq_mul_erase x z j, agMon_eq_mul_erase (flipSet x {j}) z j, prod_erase_flipSet,
    if_neg h, if_pos heq, one_mul]

/-- `P[x,y] = 1` if `x j = true` and `y = x^j`, and `0` otherwise. -/
noncomputable def pairMat (g : Cube ι → Bool) (j : ι) :
    Matrix (Ones g) (Ones g) (MvPolynomial ι ℤ) :=
  fun x y => if x.1 j = true ∧ y.1 = flipSet x.1 {j} then 1 else 0

/-- `N[x,z] = 0` if `x ∈ Up g j` and `z j = x j`, and `M[x,z]` otherwise. -/
noncomputable def redMat (g : Cube ι → Bool) (j : ι) :
    Matrix (Ones g) (Ones g) (MvPolynomial ι ℤ) :=
  fun x z => if x ∈ Up g j ∧ z.1 j = x.1 j then 0 else agMon x.1 z.1

/-- The diagonal of `D`: `1 - s_j^2` on `Up g j`, `1` elsewhere. -/
noncomputable def diagVec (g : Cube ι → Bool) (j : ι) : Ones g → MvPolynomial ι ℤ :=
  fun x => if x ∈ Up g j then 1 - X j ^ 2 else 1

theorem pairMat_apply (g : Cube ι → Bool) (j : ι) (x y : Ones g) :
    pairMat g j x y = if x.1 j = true ∧ y.1 = flipSet x.1 {j} then 1 else 0 := rfl

omit [DecidableEq ι] in
theorem agMatrix_apply (g : Cube ι → Bool) (x z : Ones g) :
    agMatrix g x z = agMon x.1 z.1 := rfl

theorem pairMat_mul_pairMat (g : Cube ι → Bool) (j : ι) : pairMat g j * pairMat g j = 0 := by
  apply Matrix.ext
  intro x z
  rw [Matrix.mul_apply, Matrix.zero_apply]
  apply Finset.sum_eq_zero
  intro y _
  rw [pairMat_apply, pairMat_apply]
  by_cases h : x.1 j = true ∧ y.1 = flipSet x.1 {j}
  · have hy : ¬ (y.1 j = true ∧ z.1 = flipSet y.1 {j}) := by
      rintro ⟨hy1, -⟩
      have hf : y.1 j = false := by
        rw [h.2, flipSet_singleton_self, h.1]
        rfl
      rw [hf] at hy1
      exact Bool.false_ne_true hy1
    rw [if_neg hy, mul_zero]
  · rw [if_neg h, zero_mul]

theorem pairMat_mul_agMatrix (g : Cube ι → Bool) (j : ι) (x z : Ones g) :
    (pairMat g j * agMatrix g) x z =
      if x ∈ Up g j then agMon (flipSet x.1 {j}) z.1 else 0 := by
  rw [Matrix.mul_apply]
  by_cases hx : x ∈ Up g j
  · rw [if_pos hx]
    have hx' := mem_Up.mp hx
    rw [Finset.sum_eq_single (⟨flipSet x.1 {j}, hx'.2⟩ : Ones g)]
    · rw [pairMat_apply, agMatrix_apply, if_pos ⟨hx'.1, rfl⟩, one_mul]
    · intro y _ hy
      rw [pairMat_apply, if_neg, zero_mul]
      rintro ⟨-, h2⟩
      exact hy (Subtype.ext h2)
    · intro h
      exact absurd (mem_univ _) h
  · rw [if_neg hx]
    apply Finset.sum_eq_zero
    intro y _
    rw [pairMat_apply, if_neg, zero_mul]
    rintro ⟨h1, h2⟩
    apply hx
    rw [mem_Up]
    refine ⟨h1, ?_⟩
    rw [← h2]
    exact y.2

theorem unipotent_mul (g : Cube ι → Bool) (j : ι) :
    (1 + (X j : MvPolynomial ι ℤ) • pairMat g j) * (1 - (X j : MvPolynomial ι ℤ) • pairMat g j)
      = 1 := by
  have h : ((X j : MvPolynomial ι ℤ) • pairMat g j) * ((X j : MvPolynomial ι ℤ) • pairMat g j)
      = 0 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, pairMat_mul_pairMat, smul_zero, smul_zero]
  rw [mul_sub, mul_one, add_mul, one_mul, h, add_zero, add_sub_cancel_right]

theorem rowop_eq (g : Cube ι → Bool) (j : ι) :
    (1 - (X j : MvPolynomial ι ℤ) • pairMat g j) * agMatrix g
      = Matrix.diagonal (diagVec g j) * redMat g j := by
  apply Matrix.ext
  intro x z
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.sub_apply, Matrix.smul_apply,
    pairMat_mul_agMatrix, Matrix.diagonal_mul, smul_eq_mul, agMatrix_apply]
  simp only [diagVec, redMat]
  by_cases hx : x ∈ Up g j
  · by_cases hz : z.1 j = x.1 j
    · rw [if_pos hx, if_pos hx, if_pos ⟨hx, hz⟩, mul_zero, agMon_of_eq x.1 z.1 j hz.symm,
        sub_self]
    · rw [if_pos hx, if_pos hx, if_neg (fun h => hz h.2),
        agMon_of_ne x.1 z.1 j (fun h => hz h.symm)]
      ring
  · rw [if_neg hx, if_neg hx, if_neg (fun h => hx h.1), mul_zero, sub_zero, one_mul]

theorem prod_diagVec (g : Cube ι → Bool) (j : ι) :
    ∏ x, diagVec g j x = (1 - X j ^ 2) ^ (Up g j).card := by
  unfold diagVec
  rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]

/-- Lemma 3.5 of the paper: `det M = (1 - s_j^2)^(e_j) * R` for some polynomial `R`. -/
theorem det_factor (g : Cube ι → Bool) (j : ι) :
    ∃ R : MvPolynomial ι ℤ, (agMatrix g).det = (1 - X j ^ 2) ^ (Up g j).card * R := by
  refine ⟨(1 + (X j : MvPolynomial ι ℤ) • pairMat g j).det * (redMat g j).det, ?_⟩
  have h1 := congrArg Matrix.det (unipotent_mul g j)
  have h2 := congrArg Matrix.det (rowop_eq g j)
  rw [Matrix.det_mul, Matrix.det_one] at h1
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, prod_diagVec] at h2
  calc (agMatrix g).det
      = (1 + (X j : MvPolynomial ι ℤ) • pairMat g j).det *
          ((1 - (X j : MvPolynomial ι ℤ) • pairMat g j).det * (agMatrix g).det) := by
        rw [← mul_assoc, h1, one_mul]
    _ = (1 - X j ^ 2) ^ (Up g j).card *
          ((1 + (X j : MvPolynomial ι ℤ) • pairMat g j).det * (redMat g j).det) := by
        rw [h2]
        ring

end DetLow
end AaronsonAmbainis

end
/- END UPSTREAM MODULE: AaronsonAmbainis.DetLow.RowOps -/

/- BEGIN UPSTREAM MODULE: AaronsonAmbainis.DetLow.Degree -/
section
/-!
# DetLow: the degree of the determinant of the agreement matrix in each variable

In each variable the determinant of the agreement matrix has degree at most the number of ones
of `g`. This is a step of the proof of Lemma 3.6 of the paper.
-/

namespace AaronsonAmbainis
namespace DetLow

open Finset MvPolynomial

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Each entry of the agreement matrix has degree at most one in each variable. -/
theorem degreeOf_agMon_le (x z : Cube ι) (j : ι) : degreeOf j (agMon x z) ≤ 1 := by
  unfold agMon
  refine (degreeOf_prod_le j univ _).trans ?_
  calc ∑ i, degreeOf j (if x i = z i then (X i : MvPolynomial ι ℤ) else 1)
      ≤ ∑ i, (if j = i then 1 else 0) := by
        apply Finset.sum_le_sum
        intro i _
        by_cases h : x i = z i
        · rw [if_pos h, degreeOf_X]
        · rw [if_neg h, degreeOf_one]
          exact Nat.zero_le _
    _ = 1 := by simp

/-- In the variable `s_j` the determinant of the agreement matrix has degree at most the number
of ones of `g` (proof of Lemma 3.6 of the paper). -/
theorem degreeOf_det_le (g : Cube ι → Bool) (j : ι) :
    degreeOf j (agMatrix g).det ≤ Fintype.card (Ones g) := by
  have hc : ∀ n : ℤ, degreeOf j ((n : MvPolynomial ι ℤ)) = 0 := by
    intro n
    rw [← eq_intCast (C : ℤ →+* MvPolynomial ι ℤ) n, degreeOf_C]
  rw [Matrix.det_apply']
  refine (degreeOf_sum_le j univ _).trans ?_
  apply Finset.sup_le
  intro σ _
  refine (degreeOf_mul_le j _ _).trans ?_
  rw [hc, zero_add]
  refine (degreeOf_prod_le j univ _).trans ?_
  calc ∑ i : Ones g, degreeOf j (agMatrix g (σ i) i) ≤ ∑ _i : Ones g, 1 :=
        Finset.sum_le_sum (fun i _ => degreeOf_agMon_le _ _ j)
    _ = Fintype.card (Ones g) := by simp

end DetLow
end AaronsonAmbainis

end
/- END UPSTREAM MODULE: AaronsonAmbainis.DetLow.Degree -/

/- BEGIN UPSTREAM MODULE: AaronsonAmbainis.DetLow.Count -/
section
/-!
# DetLow: the number of ones of `g` is `2 e_j + b_j(g)`

This is a step of the proof of Lemma 3.6 of the paper.
The ones of `g` split into the upper endpoints `Up g j` of the `j`-edges inside the ones,
the lower endpoints `Dn g j` (in bijection with `Up g j` by flipping `j`), and the points
`Bd g j` whose `j`-neighbour is a zero of `g` (there are `bdry g j` of them).
-/

namespace AaronsonAmbainis
namespace DetLow

open Finset MvPolynomial

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The lower endpoints of the `j`-edges inside the ones of `g`. -/
def Dn (g : Cube ι → Bool) (j : ι) : Finset (Ones g) :=
  univ.filter fun x => x.1 j = false ∧ g (flipSet x.1 {j}) = true

/-- The ones of `g` whose `j`-neighbour is a zero of `g`. -/
def Bd (g : Cube ι → Bool) (j : ι) : Finset (Ones g) :=
  univ.filter fun x => g (flipSet x.1 {j}) = false

theorem mem_Dn {g : Cube ι → Bool} {j : ι} {x : Ones g} :
    x ∈ Dn g j ↔ x.1 j = false ∧ g (flipSet x.1 {j}) = true := by
  simp [Dn]

theorem mem_Bd {g : Cube ι → Bool} {j : ι} {x : Ones g} :
    x ∈ Bd g j ↔ g (flipSet x.1 {j}) = false := by
  simp [Bd]

theorem card_Dn (g : Cube ι → Bool) (j : ι) : (Dn g j).card = (Up g j).card := by
  apply Finset.card_bij
    (fun x hx => (⟨flipSet x.1 {j}, (mem_Dn.mp hx).2⟩ : Ones g))
  · intro x hx
    rw [mem_Up]
    have hx' := mem_Dn.mp hx
    simp [hx'.1, x.2]
  · intro x hx y hy hxy
    have h := congrArg (fun w : Ones g => flipSet w.1 {j}) hxy
    simp only [flipSet_flipSet_singleton] at h
    exact Subtype.ext h
  · intro y hy
    rw [mem_Up] at hy
    refine ⟨⟨flipSet y.1 {j}, hy.2⟩, ?_, ?_⟩
    · rw [mem_Dn]
      simp [hy.1, y.2]
    · exact Subtype.ext (by simp)

theorem card_Bd (g : Cube ι → Bool) (j : ι) : (Bd g j).card = bdry g j := by
  unfold bdry
  apply Finset.card_bij (fun x _ => x.1)
  · intro x hx
    have h := mem_Bd.mp hx
    simp [x.2, h]
  · intro x _ y _ hxy
    exact Subtype.ext hxy
  · intro b hb
    have hb' : g b = true ∧ g (flipSet b {j}) = false := by simpa using hb
    exact ⟨⟨b, hb'.1⟩, mem_Bd.mpr hb'.2, rfl⟩

/-- The number of ones of `g` is `2 e_j + b_j(g)` (proof of Lemma 3.6 of the paper). -/
theorem card_ones_eq (g : Cube ι → Bool) (j : ι) :
    Fintype.card (Ones g) = 2 * (Up g j).card + bdry g j := by
  have h3 : (univ : Finset (Ones g)) = (Up g j ∪ Dn g j) ∪ Bd g j := by
    ext x
    simp only [mem_univ, mem_union, mem_Up, mem_Dn, mem_Bd, true_iff]
    cases h : x.1 j <;> cases h' : g (flipSet x.1 {j}) <;> simp
  have h4 : Disjoint (Up g j) (Dn g j) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    have h1 := (mem_Up.mp hx).1
    have h2 := (mem_Dn.mp hx').1
    rw [h1] at h2
    exact Bool.noConfusion h2
  have h5 : Disjoint (Up g j ∪ Dn g j) (Bd g j) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    have hb := mem_Bd.mp hx'
    rw [Finset.mem_union, mem_Up, mem_Dn] at hx
    rcases hx with hx | hx
    · rw [hx.2] at hb
      exact Bool.noConfusion hb
    · rw [hx.2] at hb
      exact Bool.noConfusion hb
  rw [← Finset.card_univ, h3, Finset.card_union_of_disjoint h5,
    Finset.card_union_of_disjoint h4, card_Dn, card_Bd]
  ring

end DetLow
end AaronsonAmbainis

end
/- END UPSTREAM MODULE: AaronsonAmbainis.DetLow.Count -/

/- BEGIN UPSTREAM MODULE: AaronsonAmbainis.DetLow.Main -/
section
/-!
# DetLow: the theorems `lowestUnit : LowestUnit` and `lowestBound : LowestBound`

`lowestUnit` is Lemma 3.3 of the paper; `lowestBound` is Lemma 3.4 and Lemma 3.6.
-/

namespace AaronsonAmbainis
namespace DetLow

open Finset MvPolynomial

/-- Lemma 3.3 of the paper: multiplying by a polynomial with constant coefficient `1` does not
change the monomials of least total degree. -/
theorem lowestUnit : AaronsonAmbainis.LowestUnit := by
  intro ι _ u q hu m
  exact ⟨isLowest_of_unit_mul u q hu m, isLowest_unit_mul u q hu m⟩

/-- The cofactor `R` of `(1 - s_j^2)^(e_j)` has degree at most `b_j(g)` in `s_j` (proof of
Lemma 3.6 of the paper). -/
theorem degreeOf_cofactor_le {ι : Type} [Fintype ι] [DecidableEq ι] (g : Cube ι → Bool) (j : ι)
    (R : MvPolynomial ι ℤ) (hR : (agMatrix g).det = (1 - X j ^ 2) ^ (Up g j).card * R) :
    degreeOf j R ≤ bdry g j := by
  have hp : (agMatrix g).det ≠ 0 := agMatrix_det_ne_zero g
  have hu0 : ((1 : MvPolynomial ι ℤ) - X j ^ 2) ≠ 0 := by
    intro h
    have h' := congrArg constantCoeff h
    simp at h'
  have hR0 : R ≠ 0 := by
    rintro rfl
    exact hp (by rw [hR, mul_zero])
  have hdeg1 : degreeOf j ((1 : MvPolynomial ι ℤ) - X j ^ 2) = 2 := by
    have h : (1 : MvPolynomial ι ℤ) - X j ^ 2 = -(X j ^ 2) + 1 := by ring
    have hlt : degreeOf j (1 : MvPolynomial ι ℤ) < degreeOf j (-(X j ^ 2 : MvPolynomial ι ℤ)) := by
      rw [degreeOf_neg, degreeOf_X_self_pow, degreeOf_one]
      norm_num
    rw [h, degreeOf_add_eq_of_degreeOf_lt hlt, degreeOf_neg, degreeOf_X_self_pow]
  have h1 := degreeOf_det_le g j
  rw [hR, degreeOf_mul_eq (pow_ne_zero _ hu0) hR0, degreeOf_pow_eq j _ _ hu0, hdeg1,
    card_ones_eq g j] at h1
  omega

/-- Lemma 3.4 and Lemma 3.6 of the paper: the determinant of the agreement matrix is nonzero, and
each of its monomials of least total degree has exponent at most `b_j(g)` in every variable
`s_j`. -/
theorem lowestBound : AaronsonAmbainis.LowestBound := by
  intro ι _ _ g
  refine ⟨agMatrix_det_ne_zero g, ?_⟩
  intro m hm j
  obtain ⟨R, hR⟩ := det_factor g j
  have hu : constantCoeff ((1 - X j ^ 2 : MvPolynomial ι ℤ) ^ (Up g j).card) = 1 := by
    simp
  rw [hR] at hm
  have hlow : IsLowest R m := isLowest_of_unit_mul _ R hu m hm
  exact (monomial_le_degreeOf j hlow.1).trans (degreeOf_cofactor_le g j R hR)

end DetLow
end AaronsonAmbainis

end
/- END UPSTREAM MODULE: AaronsonAmbainis.DetLow.Main -/

/- BEGIN UPSTREAM MODULE: AaronsonAmbainis.DetBij.Basic -/
section
/-!
# DetBij / Basic: cube lemmas and the agreement monomial

Elementary facts on `flipSet`, `diffSet`, `antipode`, the agreement set `agSet`, and the
exponent vector `agExp` of the agreement monomial `agMon`.
-/

namespace AaronsonAmbainis.DetBij

open Finset MvPolynomial

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The agreement set of `x` and `z` (written `ag(x,z)` in the paper). -/
def agSet (x z : Cube ι) : Finset ι := univ.filter fun i => x i = z i

omit [DecidableEq ι] in
theorem mem_agSet {x z : Cube ι} {i : ι} : i ∈ agSet x z ↔ x i = z i := by
  simp [agSet]

omit [DecidableEq ι] in
theorem mem_diffSet {x z : Cube ι} {i : ι} : i ∈ diffSet x z ↔ x i ≠ z i := by
  simp [diffSet]

omit [Fintype ι] in
theorem flipSet_apply (x : Cube ι) (S : Finset ι) (i : ι) :
    flipSet x S i = if i ∈ S then !(x i) else x i := rfl

omit [Fintype ι] in
theorem flipSet_empty (x : Cube ι) : flipSet x ∅ = x := by
  funext i
  simp [flipSet_apply]

/-- A point `w` with `diffSet x w = S` is `flipSet x S`: first half. -/
theorem diffSet_flipSet (x : Cube ι) (S : Finset ι) : diffSet x (flipSet x S) = S := by
  ext i
  rw [mem_diffSet, flipSet_apply]
  by_cases h : i ∈ S <;> cases x i <;> simp [h]

/-- A point `w` with `diffSet x w = S` is `flipSet x S`: second half. -/
theorem flipSet_diffSet (x w : Cube ι) : flipSet x (diffSet x w) = w := by
  funext i
  rw [flipSet_apply]
  by_cases h : x i = w i
  · have hi : i ∉ diffSet x w := fun hh => (mem_diffSet.mp hh) h
    rw [if_neg hi, h]
  · have hi : i ∈ diffSet x w := mem_diffSet.mpr h
    rw [if_pos hi]
    revert h
    cases x i <;> cases w i <;> simp

omit [DecidableEq ι] in
theorem diffSet_eq_empty_iff {x w : Cube ι} : diffSet x w = ∅ ↔ x = w := by
  constructor
  · intro h
    funext i
    by_contra hne
    have hi : i ∈ diffSet x w := mem_diffSet.mpr hne
    rw [h] at hi
    simp at hi
  · rintro rfl
    ext i
    simp [mem_diffSet]

/-- `z` is the antipode of `u` flipped on the agreement set of `u` and `z`. -/
theorem flipSet_antipode_agSet (u z : Cube ι) : flipSet (antipode u) (agSet u z) = z := by
  funext i
  rw [flipSet_apply]
  by_cases h : u i = z i
  · rw [if_pos (mem_agSet.mpr h)]
    simp [antipode, h]
  · rw [if_neg (fun hh => h (mem_agSet.mp hh))]
    revert h
    simp only [antipode]
    cases u i <;> cases z i <;> simp

/-- The exponent vector of `agMon x z`: the indicator of the agreement set. -/
noncomputable def agExp (x z : Cube ι) : ι →₀ ℕ :=
  ∑ i, if x i = z i then Finsupp.single i 1 else 0

omit [DecidableEq ι] in
theorem agExp_apply (x z : Cube ι) (j : ι) : agExp x z j = if x j = z j then 1 else 0 := by
  rw [agExp, Finsupp.finsetSum_apply, Finset.sum_eq_single j]
  · split_ifs <;> simp
  · intro i _ hij
    split_ifs
    · simp [hij]
    · simp
  · intro h
    exact absurd (Finset.mem_univ j) h

omit [DecidableEq ι] in
/-- `agMon x z` is the monomial with exponent vector `agExp x z` and coefficient `1`. -/
theorem agMon_eq_monomial (x z : Cube ι) :
    agMon x z = monomial (agExp x z) (1 : ℤ) := by
  rw [agExp, monomial_sum_one]
  unfold agMon
  refine Finset.prod_congr rfl fun i _ => ?_
  split_ifs
  · rfl
  · simp

end AaronsonAmbainis.DetBij

end
/- END UPSTREAM MODULE: AaronsonAmbainis.DetBij.Basic -/

/- BEGIN UPSTREAM MODULE: AaronsonAmbainis.DetBij.Identity -/
section
/-!
# DetBij / Identity: the matrices `P`, `U`, `Q'` and the identity `P * M = U * Q'`

`A : Cube ι → Finset ι` is a field of sets; the identity needs `A x` to be a 1-wing of `g` at
every `x` with `g x = true` (this is the only use of the wing property).

The file proves the wing identity (Lemma 3.7 of the paper, `wing_sum`) and parts (i) and (ii)
of Lemma 3.8 (`Pmat_mul_agMatrix`, `constantCoeff_det_Pmat`, `constantCoeff_det_Umat`). The
matrix `Q'` (`Qmat`) is the matrix `Q` of the paper.
-/

namespace AaronsonAmbainis.DetBij

open Finset MvPolynomial

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `P[x,w] = ∏_{i ∈ Δ(x,w)} (-s_i)` if `Δ(x,w) ⊆ A x`, and `0` otherwise. -/
noncomputable def Pmat (g : Cube ι → Bool) (A : Cube ι → Finset ι) :
    Matrix (Ones g) (Ones g) (MvPolynomial ι ℤ) :=
  fun x w => if diffSet x.1 w.1 ⊆ A x.1 then ∏ i ∈ diffSet x.1 w.1, -(X i) else 0

/-- `U` is diagonal with entry `∏_{i ∈ A x} (1 - s_i^2)` at `x`. -/
noncomputable def Umat (g : Cube ι → Bool) (A : Cube ι → Finset ι) :
    Matrix (Ones g) (Ones g) (MvPolynomial ι ℤ) :=
  Matrix.diagonal fun x => ∏ i ∈ A x.1, (1 - X i ^ 2)

/-- `Q'[x,z] = M[x,z]` if the agreement set of `x` and `z` is disjoint from `A x`, else `0`. -/
noncomputable def Qmat (g : Cube ι → Bool) (A : Cube ι → Finset ι) :
    Matrix (Ones g) (Ones g) (MvPolynomial ι ℤ) :=
  fun x z => if Disjoint (agSet x.1 z.1) (A x.1) then agMon x.1 z.1 else 0

theorem Pmat_apply (g : Cube ι → Bool) (A : Cube ι → Finset ι) (x w : Ones g) :
    Pmat g A x w
      = if diffSet x.1 w.1 ⊆ A x.1 then ∏ i ∈ diffSet x.1 w.1, -(X i) else 0 := rfl

theorem Qmat_apply (g : Cube ι → Bool) (A : Cube ι → Finset ι) (x z : Ones g) :
    Qmat g A x z = if Disjoint (agSet x.1 z.1) (A x.1) then agMon x.1 z.1 else 0 := rfl

omit [DecidableEq ι] in
theorem agMatrix_apply (g : Cube ι → Bool) (x z : Ones g) :
    agMatrix g x z = agMon x.1 z.1 := rfl

/-! ### The wing identity, coordinate by coordinate -/

/-- The factor of `agMon x z` at coordinate `i`. -/
noncomputable def fAg (x z : Cube ι) (i : ι) : MvPolynomial ι ℤ := if x i = z i then X i else 1

/-- The factor at coordinate `i` of `agMon x' z`, where `x'` is `x` flipped at `i`. -/
noncomputable def gAg (x z : Cube ι) (i : ι) : MvPolynomial ι ℤ := if x i = z i then 1 else X i

omit [DecidableEq ι] in
theorem agMon_eq_prod (x z : Cube ι) : agMon x z = ∏ i, fAg x z i := rfl

omit [Fintype ι] in
theorem fAg_flipSet_of_mem (x z : Cube ι) {S : Finset ι} {i : ι} (hi : i ∈ S) :
    fAg (flipSet x S) z i = gAg x z i := by
  unfold fAg gAg
  rw [flipSet_apply, if_pos hi]
  cases x i <;> cases z i <;> simp

omit [Fintype ι] in
theorem fAg_flipSet_of_notMem (x z : Cube ι) {S : Finset ι} {i : ι} (hi : i ∉ S) :
    fAg (flipSet x S) z i = fAg x z i := by
  unfold fAg
  rw [flipSet_apply, if_neg hi]

omit [Fintype ι] [DecidableEq ι] in
/-- A coordinate of the wing contributes `0` if `x_i = z_i` and `1 - s_i^2` otherwise. -/
theorem neg_X_mul_gAg_add_fAg (x z : Cube ι) (i : ι) :
    -(X i : MvPolynomial ι ℤ) * gAg x z i + fAg x z i
      = if x i = z i then 0 else 1 - (X i : MvPolynomial ι ℤ) ^ 2 := by
  unfold fAg gAg
  split_ifs <;> ring

/-- One term of the wing sum, split into the coordinates in `S`, in `A \ S` and outside `A`. -/
theorem wing_term (x z : Cube ι) {A S : Finset ι} (hSA : S ⊆ A) :
    (∏ i ∈ S, -(X i : MvPolynomial ι ℤ)) * agMon (flipSet x S) z
      = ((∏ i ∈ S, -(X i : MvPolynomial ι ℤ) * gAg x z i) * ∏ i ∈ A \ S, fAg x z i)
          * ∏ i ∈ Aᶜ, fAg x z i := by
  have h1 : agMon (flipSet x S) z
      = (∏ i ∈ A, fAg (flipSet x S) z i) * ∏ i ∈ Aᶜ, fAg (flipSet x S) z i :=
    (Finset.prod_mul_prod_compl A (fAg (flipSet x S) z)).symm
  have h2 : ∏ i ∈ Aᶜ, fAg (flipSet x S) z i = ∏ i ∈ Aᶜ, fAg x z i :=
    Finset.prod_congr rfl fun i hi =>
      fAg_flipSet_of_notMem x z fun h => (Finset.mem_compl.mp hi) (hSA h)
  have h3 : ∏ i ∈ A, fAg (flipSet x S) z i
      = (∏ i ∈ A \ S, fAg x z i) * ∏ i ∈ S, gAg x z i := by
    rw [← Finset.prod_sdiff hSA]
    congr 1
    · exact Finset.prod_congr rfl fun i hi =>
        fAg_flipSet_of_notMem x z (Finset.mem_sdiff.mp hi).2
    · exact Finset.prod_congr rfl fun i hi => fAg_flipSet_of_mem x z hi
  rw [h1, h2, h3, Finset.prod_mul_distrib]
  ring

/-- The wing identity (Lemma 3.7 of the paper), for an arbitrary set `A` and points `x`, `z`
of the cube. -/
theorem wing_sum (x z : Cube ι) (A : Finset ι) :
    ∑ S ∈ A.powerset, (∏ i ∈ S, -(X i : MvPolynomial ι ℤ)) * agMon (flipSet x S) z
      = (∏ i ∈ A, (1 - (X i : MvPolynomial ι ℤ) ^ 2))
          * (if Disjoint (agSet x z) A then agMon x z else 0) := by
  have h0 : ∑ S ∈ A.powerset, (∏ i ∈ S, -(X i : MvPolynomial ι ℤ)) * agMon (flipSet x S) z
      = ∑ S ∈ A.powerset, ((∏ i ∈ S, -(X i : MvPolynomial ι ℤ) * gAg x z i)
          * ∏ i ∈ A \ S, fAg x z i) * ∏ i ∈ Aᶜ, fAg x z i :=
    Finset.sum_congr rfl fun S hS => wing_term x z (Finset.mem_powerset.mp hS)
  rw [h0, ← Finset.sum_mul, ← Finset.prod_add]
  by_cases hd : Disjoint (agSet x z) A
  · have hne : ∀ i ∈ A, ¬ x i = z i := fun i hi h =>
      (Finset.disjoint_left.mp hd (mem_agSet.mpr h)) hi
    have e1 : ∏ i ∈ A, (-(X i : MvPolynomial ι ℤ) * gAg x z i + fAg x z i)
        = ∏ i ∈ A, (1 - (X i : MvPolynomial ι ℤ) ^ 2) :=
      Finset.prod_congr rfl fun i hi => by
        rw [neg_X_mul_gAg_add_fAg, if_neg (hne i hi)]
    have e2 : agMon x z = ∏ i ∈ Aᶜ, fAg x z i := by
      have e3 : ∏ i ∈ A, fAg x z i = 1 :=
        Finset.prod_eq_one fun i hi => by
          unfold fAg
          rw [if_neg (hne i hi)]
      rw [agMon_eq_prod, ← Finset.prod_mul_prod_compl A (fAg x z), e3, one_mul]
    rw [if_pos hd, e1, e2]
  · obtain ⟨i, hi1, hi2⟩ := Finset.not_disjoint_iff.mp hd
    have e1 : ∏ i ∈ A, (-(X i : MvPolynomial ι ℤ) * gAg x z i + fAg x z i) = 0 :=
      Finset.prod_eq_zero hi2 (by rw [neg_X_mul_gAg_add_fAg, if_pos (mem_agSet.mp hi1)])
    rw [if_neg hd, mul_zero, e1, zero_mul]

/-! ### The matrix identity -/

/-- `P * M = U * Q'` (Lemma 3.8 (i) of the paper), using the wing property. -/
theorem Pmat_mul_agMatrix (g : Cube ι → Bool) (A : Cube ι → Finset ι)
    (hA : ∀ x : Ones g, IsWing g x.1 (A x.1)) :
    Pmat g A * agMatrix g = Umat g A * Qmat g A := by
  refine Matrix.ext fun x z => ?_
  have hR : (Umat g A * Qmat g A) x z
      = (∏ i ∈ A x.1, (1 - (X i : MvPolynomial ι ℤ) ^ 2))
          * (if Disjoint (agSet x.1 z.1) (A x.1) then agMon x.1 z.1 else 0) := by
    unfold Umat
    rw [Matrix.diagonal_mul, Qmat_apply]
  have hL : (Pmat g A * agMatrix g) x z
      = ∑ w ∈ univ.filter (fun w : Ones g => diffSet x.1 w.1 ⊆ A x.1),
          (∏ i ∈ diffSet x.1 w.1, -(X i : MvPolynomial ι ℤ)) * agMon w.1 z.1 := by
    rw [Matrix.mul_apply, Finset.sum_filter]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Pmat_apply, agMatrix_apply, ite_mul, zero_mul]
  rw [hL, hR, ← wing_sum]
  refine Finset.sum_bij (fun (w : Ones g) _ => diffSet x.1 w.1) ?_ ?_ ?_ ?_
  · intro w hw
    exact Finset.mem_powerset.mpr (Finset.mem_filter.mp hw).2
  · intro w₁ _ w₂ _ h
    have h' : diffSet x.1 w₁.1 = diffSet x.1 w₂.1 := h
    apply Subtype.ext
    calc w₁.1 = flipSet x.1 (diffSet x.1 w₁.1) := (flipSet_diffSet x.1 w₁.1).symm
      _ = flipSet x.1 (diffSet x.1 w₂.1) := by rw [h']
      _ = w₂.1 := flipSet_diffSet x.1 w₂.1
  · intro S hS
    have hS' : S ⊆ A x.1 := Finset.mem_powerset.mp hS
    refine ⟨⟨flipSet x.1 S, hA x S hS'⟩, ?_, diffSet_flipSet x.1 S⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [diffSet_flipSet]
    exact hS'
  · intro w _
    simp only [flipSet_diffSet]

/-! ### Constant coefficients of `det P` and `det U` -/

theorem constantCoeff_Pmat (g : Cube ι → Bool) (A : Cube ι → Finset ι) (x w : Ones g) :
    constantCoeff (Pmat g A x w) = if x = w then 1 else 0 := by
  by_cases hxw : x = w
  · subst hxw
    rw [if_pos rfl, Pmat_apply, diffSet_eq_empty_iff.mpr rfl, if_pos (Finset.empty_subset _),
      Finset.prod_empty, map_one]
  · rw [if_neg hxw, Pmat_apply]
    split_ifs with h
    · have hne : (diffSet x.1 w.1).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        exact fun h0 => hxw (Subtype.ext (diffSet_eq_empty_iff.mp h0))
      obtain ⟨i, hi⟩ := hne
      rw [map_prod]
      exact Finset.prod_eq_zero hi (by simp)
    · exact map_zero _

theorem constantCoeff_det_Pmat (g : Cube ι → Bool) (A : Cube ι → Finset ι) :
    constantCoeff (Pmat g A).det = 1 := by
  have h1 : (constantCoeff : MvPolynomial ι ℤ →+* ℤ).mapMatrix (Pmat g A) = 1 := by
    refine Matrix.ext fun x w => ?_
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.one_apply]
    exact constantCoeff_Pmat g A x w
  rw [RingHom.map_det, h1, Matrix.det_one]

theorem constantCoeff_det_Umat (g : Cube ι → Bool) (A : Cube ι → Finset ι) :
    constantCoeff (Umat g A).det = 1 := by
  unfold Umat
  rw [Matrix.det_diagonal, map_prod]
  refine Finset.prod_eq_one fun x _ => ?_
  rw [map_prod]
  refine Finset.prod_eq_one fun i _ => ?_
  simp

end AaronsonAmbainis.DetBij

end
/- END UPSTREAM MODULE: AaronsonAmbainis.DetBij.Identity -/

/- BEGIN UPSTREAM MODULE: AaronsonAmbainis.DetBij.Perm -/
section
/-!
# DetBij / Perm: the bijection theorem

From `LowestUnit` and `LowestBound`: for every field of 1-wings `A x` at the ones of `g` there
is a permutation `σ` of the ones of `g` such that the agreement set of `σ x` and `x` is
disjoint from `A (σ x)` for every `x`, and `#{x : (σ x)_j = x_j} ≤ bdry g j` for every `j`
simultaneously.

This is the bijection theorem (Theorem 3.1 of the paper) for the inverse `σ` of the bijection
`τ` of the paper; `Bijection.lean` states it for `τ`. The proof is that of the paper: a monomial of
`det Q'` with exponents at most `bdry g j` (`exists_lowest_Qmat`, by the argument of
Lemma 3.8 (iii)), and the Leibniz formula for `det Q'` (`exists_perm_of_mem_support`).
-/

namespace AaronsonAmbainis.DetBij

open Finset MvPolynomial

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- A nonzero polynomial has a monomial of least total degree. -/
theorem exists_isLowest (q : MvPolynomial ι ℤ) (hq : q ≠ 0) : ∃ m, IsLowest q m := by
  have hne : q.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    exact fun h => hq (MvPolynomial.support_eq_empty.mp h)
  obtain ⟨m, hm, hmin⟩ :=
    Finset.exists_min_image q.support (fun m : ι →₀ ℕ => ∑ i, m i) hne
  exact ⟨m, hm, hmin⟩

/-- `det P * det M = det U * det Q'`. -/
theorem det_Pmat_mul_det_agMatrix (g : Cube ι → Bool) (A : Cube ι → Finset ι)
    (hA : ∀ x : Ones g, IsWing g x.1 (A x.1)) :
    (Pmat g A).det * (agMatrix g).det = (Umat g A).det * (Qmat g A).det := by
  rw [← Matrix.det_mul, ← Matrix.det_mul, Pmat_mul_agMatrix g A hA]

/-- `det Q'` has a monomial `m` with `m j ≤ bdry g j` for all `j`. -/
theorem exists_lowest_Qmat (hU : LowestUnit) (hB : LowestBound) (g : Cube ι → Bool)
    (A : Cube ι → Finset ι) (hA : ∀ x : Ones g, IsWing g x.1 (A x.1)) :
    ∃ m : ι →₀ ℕ, m ∈ (Qmat g A).det.support ∧ ∀ j, m j ≤ bdry g j := by
  obtain ⟨hp, hbound⟩ := hB ι g
  have hdet := det_Pmat_mul_det_agMatrix g A hA
  have hP : (Pmat g A).det ≠ 0 := by
    intro h
    have h1 := constantCoeff_det_Pmat g A
    rw [h, map_zero] at h1
    exact zero_ne_one h1
  have hQ : (Qmat g A).det ≠ 0 := by
    intro h
    rw [h, mul_zero] at hdet
    exact (mul_ne_zero hP hp) hdet
  obtain ⟨m, hm⟩ := exists_isLowest _ hQ
  refine ⟨m, hm.1, hbound m ?_⟩
  have h1 : IsLowest ((Umat g A).det * (Qmat g A).det) m :=
    (hU ι _ _ (constantCoeff_det_Umat g A) m).mpr hm
  rw [← hdet] at h1
  exact (hU ι _ _ (constantCoeff_det_Pmat g A) m).mp h1

/-- A product of entries of `Q'` along a permutation is `0` or a single monomial. -/
theorem Qmat_prod_eq (g : Cube ι → Bool) (A : Cube ι → Finset ι) (σ : Equiv.Perm (Ones g)) :
    ∏ x : Ones g, Qmat g A (σ x) x
      = if ∀ x : Ones g, Disjoint (agSet (σ x).1 x.1) (A (σ x).1)
        then monomial (∑ x : Ones g, agExp (σ x).1 x.1) (1 : ℤ) else 0 := by
  split_ifs with h
  · rw [monomial_sum_one]
    refine Finset.prod_congr rfl fun x _ => ?_
    rw [Qmat_apply, if_pos (h x), agMon_eq_monomial]
  · have h' : ∃ x : Ones g, ¬ Disjoint (agSet (σ x).1 x.1) (A (σ x).1) := not_forall.mp h
    obtain ⟨x, hx⟩ := h'
    refine Finset.prod_eq_zero (Finset.mem_univ x) ?_
    rw [Qmat_apply, if_neg hx]

omit [Fintype ι] [DecidableEq ι] in
/-- A sign does not change whether a coefficient vanishes. -/
theorem coeff_units_smul_ne_zero (m : ι →₀ ℕ) (u : ℤˣ) (p : MvPolynomial ι ℤ)
    (h : coeff m (u • p) ≠ 0) : coeff m p ≠ 0 := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · simpa using h
  · simpa using h

/-- Leibniz: every monomial of `det Q'` comes from a permutation all of whose entries are
nonzero. -/
theorem exists_perm_of_mem_support (g : Cube ι → Bool) (A : Cube ι → Finset ι) (m : ι →₀ ℕ)
    (hm : m ∈ (Qmat g A).det.support) :
    ∃ σ : Equiv.Perm (Ones g), (∀ x : Ones g, Disjoint (agSet (σ x).1 x.1) (A (σ x).1)) ∧
      m = ∑ x : Ones g, agExp (σ x).1 x.1 := by
  rw [MvPolynomial.mem_support_iff, Matrix.det_apply, MvPolynomial.coeff_sum] at hm
  obtain ⟨σ, -, hσ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
  have hσ' := coeff_units_smul_ne_zero m _ _ hσ
  rw [Qmat_prod_eq] at hσ'
  refine ⟨σ, ?_⟩
  by_cases h : ∀ x : Ones g, Disjoint (agSet (σ x).1 x.1) (A (σ x).1)
  · refine ⟨h, ?_⟩
    rw [if_pos h, MvPolynomial.coeff_monomial] at hσ'
    by_contra hne
    rw [if_neg (fun h' => hne h'.symm)] at hσ'
    exact hσ' rfl
  · rw [if_neg h, MvPolynomial.coeff_zero] at hσ'
    exact absurd rfl hσ'

theorem sum_agExp_apply (g : Cube ι → Bool) (σ : Equiv.Perm (Ones g)) (j : ι) :
    (∑ x : Ones g, agExp (σ x).1 x.1) j
      = (univ.filter fun x : Ones g => (σ x).1 j = x.1 j).card := by
  rw [Finsupp.finsetSum_apply, Finset.card_filter]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [agExp_apply]

/-- The bijection theorem (Theorem 3.1 of the paper, for the inverse `σ` of the bijection `τ` of
the paper), from `LowestUnit` and `LowestBound`. -/
theorem exists_perm (hU : LowestUnit) (hB : LowestBound) (g : Cube ι → Bool)
    (A : Cube ι → Finset ι) (hA : ∀ x : Ones g, IsWing g x.1 (A x.1)) :
    ∃ σ : Equiv.Perm (Ones g), (∀ x : Ones g, Disjoint (agSet (σ x).1 x.1) (A (σ x).1)) ∧
      ∀ j, (univ.filter fun x : Ones g => (σ x).1 j = x.1 j).card ≤ bdry g j := by
  obtain ⟨m, hm, hmb⟩ := exists_lowest_Qmat hU hB g A hA
  obtain ⟨σ, hσ, rfl⟩ := exists_perm_of_mem_support g A m hm
  refine ⟨σ, hσ, fun j => ?_⟩
  rw [← sum_agExp_apply]
  exact hmb j

end AaronsonAmbainis.DetBij

end
/- END UPSTREAM MODULE: AaronsonAmbainis.DetBij.Perm -/

/- BEGIN UPSTREAM MODULE: AaronsonAmbainis.DetBij.Main -/
section
/-!
# DetBij / Main: `LowestUnit → LowestBound → DetInequality`

The determinant inequality (Corollary 3.2 of the paper) from the two interface propositions of
`AaronsonAmbainis.DetDefs`, through the bijection theorem in the form of `Perm.lean`. The
argument is the proof of Corollary 3.2 from Theorem 3.1 in the paper.
-/

namespace AaronsonAmbainis.DetBij

open Finset MvPolynomial

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The wings extended to all points: `A x` on `zone g`, the empty set elsewhere. -/
def extWing (g : Cube ι → Bool) (A : Cube ι → Finset ι) (x : Cube ι) : Finset ι :=
  if x ∈ zone g then A x else ∅

theorem extWing_of_mem (g : Cube ι → Bool) (A : Cube ι → Finset ι) {x : Cube ι}
    (hx : x ∈ zone g) : extWing g A x = A x := by
  unfold extWing
  rw [if_pos hx]

theorem extWing_of_notMem (g : Cube ι → Bool) (A : Cube ι → Finset ι) {x : Cube ι}
    (hx : x ∉ zone g) : extWing g A x = ∅ := by
  unfold extWing
  rw [if_neg hx]

/-- The extended wings are 1-wings at every one of `g` (the empty set is a 1-wing). -/
theorem isWing_extWing (g : Cube ι → Bool) (A : Cube ι → Finset ι)
    (hA : ∀ u ∈ zone g, IsWing g u (A u)) (x : Ones g) :
    IsWing g x.1 (extWing g A x.1) := by
  by_cases hx : x.1 ∈ zone g
  · rw [extWing_of_mem g A hx]
    exact hA x.1 hx
  · intro S hS
    rw [extWing_of_notMem g A hx] at hS
    rw [Finset.subset_empty.mp hS, flipSet_empty]
    exact x.2

/-- The weighted inequality for one instance, from a permutation as in `exists_perm`. -/
theorem det_inequality_of_perm (g : Cube ι → Bool) (ℓ : ι → ℝ) (hℓ : ∀ j, 0 < ℓ j)
    (A : Cube ι → Finset ι) (d : Cube ι → ℝ)
    (hd : ∀ u ∈ zone g, ∀ G : Finset ι, Disjoint G (A u) →
        g (flipSet (antipode u) G) = true → d u ≤ ∑ j ∈ G, ℓ j)
    (σ : Equiv.Perm (Ones g))
    (hσ : ∀ x : Ones g, Disjoint (agSet (σ x).1 x.1) (extWing g A (σ x).1))
    (hcard : ∀ j, (univ.filter fun x : Ones g => (σ x).1 j = x.1 j).card ≤ bdry g j) :
    ∑ u ∈ zone g, d u ≤ ∑ j, ℓ j * (bdry g j : ℝ) := by
  -- Step 1: the sum over the zone as a sum over the ones of `g`
  have hz : zone g ⊆ univ.filter (fun x : Cube ι => g x = true) := by
    intro u hu
    simp only [zone, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
    exact hu.1
  have e0 : ∑ u ∈ univ.filter (fun x : Cube ι => g x = true), (if u ∈ zone g then d u else 0)
      = ∑ y : Ones g, (if y.1 ∈ zone g then d y.1 else 0) :=
    Finset.sum_subtype _ (fun x => by simp) (fun u => if u ∈ zone g then d u else 0)
  have h1 : ∑ u ∈ zone g, d u = ∑ y : Ones g, (if y.1 ∈ zone g then d y.1 else 0) := by
    rw [← e0, Finset.sum_ite_mem, Finset.inter_eq_right.mpr hz]
  -- Step 2: the bound at each point (the hypothesis on `d` at `G = ag(y, σ⁻¹ y)`)
  have h2 : ∀ y : Ones g,
      (if y.1 ∈ zone g then d y.1 else 0) ≤ ∑ j ∈ agSet y.1 (σ.symm y).1, ℓ j := by
    intro y
    split_ifs with hy
    · refine hd y.1 hy _ ?_ ?_
      · have h := hσ (σ.symm y)
        rw [Equiv.apply_symm_apply, extWing_of_mem g A hy] at h
        exact h
      · rw [flipSet_antipode_agSet]
        exact (σ.symm y).2
    · exact Finset.sum_nonneg fun j _ => (hℓ j).le
  -- Step 3: reindex by `σ`
  have h3 : ∑ y : Ones g, ∑ j ∈ agSet y.1 (σ.symm y).1, ℓ j
      = ∑ x : Ones g, ∑ j ∈ agSet (σ x).1 x.1, ℓ j := by
    refine (Equiv.sum_comp σ
      (fun y : Ones g => ∑ j ∈ agSet y.1 (σ.symm y).1, ℓ j)).symm.trans ?_
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [Equiv.symm_apply_apply]
  -- Step 4: exchange the two sums
  have h4 : ∑ x : Ones g, ∑ j ∈ agSet (σ x).1 x.1, ℓ j
      = ∑ j, ℓ j * ((univ.filter fun x : Ones g => (σ x).1 j = x.1 j).card : ℝ) := by
    have e1 : ∀ x : Ones g, ∑ j ∈ agSet (σ x).1 x.1, ℓ j
        = ∑ j, if (σ x).1 j = x.1 j then ℓ j else 0 := by
      intro x
      unfold agSet
      rw [Finset.sum_filter]
    have e2 : ∑ x : Ones g, ∑ j ∈ agSet (σ x).1 x.1, ℓ j
        = ∑ x : Ones g, ∑ j, if (σ x).1 j = x.1 j then ℓ j else 0 :=
      Finset.sum_congr rfl fun x _ => e1 x
    rw [e2, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  -- Step 5: the bound on the multiplicities
  have h5 : ∑ j, ℓ j * ((univ.filter fun x : Ones g => (σ x).1 j = x.1 j).card : ℝ)
      ≤ ∑ j, ℓ j * (bdry g j : ℝ) :=
    Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (hcard j)) (hℓ j).le
  calc ∑ u ∈ zone g, d u
      = ∑ y : Ones g, (if y.1 ∈ zone g then d y.1 else 0) := h1
    _ ≤ ∑ y : Ones g, ∑ j ∈ agSet y.1 (σ.symm y).1, ℓ j :=
        Finset.sum_le_sum fun y _ => h2 y
    _ = ∑ x : Ones g, ∑ j ∈ agSet (σ x).1 x.1, ℓ j := h3
    _ = ∑ j, ℓ j * ((univ.filter fun x : Ones g => (σ x).1 j = x.1 j).card : ℝ) := h4
    _ ≤ ∑ j, ℓ j * (bdry g j : ℝ) := h5

/-- The determinant inequality (Corollary 3.2 of the paper) from `LowestUnit` and
`LowestBound`. -/
theorem detInequality_of_lowest :
    AaronsonAmbainis.LowestUnit → AaronsonAmbainis.LowestBound → AaronsonAmbainis.DetInequality := by
  intro hU hB
  unfold DetInequality
  intro ι _ _ g ℓ hℓ A hA d hd
  obtain ⟨σ, hσ, hcard⟩ := exists_perm hU hB g (extWing g A) (isWing_extWing g A hA)
  exact det_inequality_of_perm g ℓ hℓ A d hd σ hσ hcard

end AaronsonAmbainis.DetBij

end
/- END UPSTREAM MODULE: AaronsonAmbainis.DetBij.Main -/

/- BEGIN UPSTREAM MODULE: AaronsonAmbainis.DetTheorem -/
section
/-!
# The determinant inequality, assembled

The determinant inequality (Corollary 3.2 of the paper), from the two halves of its proof:

* `AaronsonAmbainis.DetLow.lowestUnit`, `AaronsonAmbainis.DetLow.lowestBound`
  (directory `DetLow`),
* `AaronsonAmbainis.DetBij.detInequality_of_lowest` (directory `DetBij`).
-/

namespace AaronsonAmbainis

/-- The determinant inequality (Corollary 3.2 of the paper), with no hypothesis. -/
theorem detInequality : DetInequality :=
  DetBij.detInequality_of_lowest DetLow.lowestUnit DetLow.lowestBound

end AaronsonAmbainis

end
/- END UPSTREAM MODULE: AaronsonAmbainis.DetTheorem -/

/- BEGIN UPSTREAM MODULE: AaronsonAmbainis.AllPairsDefs -/
section
/-!
# Interface for the proof of the two-sided inequality from the antipodal inequality

`AllPairsInequality` is the all-pairs inequality (the inequality of Proposition 5.2 of the paper:
the sum over all pairs of a one and a zero of `g`), multiplied by `2` so that `2^(n-1)` does not
appear.

It splits the proof of `AntipodalInequality → TwoSidedInequality` into two independent parts:

* `AntipodalInequality → AllPairsInequality` — apply the antipodal inequality (Theorem 4.3) on
  every subcube and add up (Section 5.1);
* `AllPairsInequality → TwoSidedInequality` — the overlap lemma (Lemma 4.1) and the
  Cauchy–Schwarz inequality (Section 5.2).

The all-pairs inequality is also the starting point of the statements on real functions:
applied to the level functions `1_{f > t}` of a real function `f` and integrated over the level
`t`, it gives the integrated all-pairs inequality (`Level/Integrated.lean`).
-/

namespace AaronsonAmbainis

open Finset

/-- The all-pairs inequality (the inequality of Proposition 5.2 of the paper, multiplied by `2`).
For every Boolean `g`, all positive weights `w` and every row field `lam`:
`2 · ∑_{x : g x = true} ∑_{y : g y = false} 1 / (∑_{j ∈ Δ(x,y)} w_j lam^x_j lam^y_j)
  ≤ 2^n · ∑_j b_j(g) / w_j`. -/
def AllPairsInequality : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (g : Cube ι → Bool) (w : ι → ℝ), (∀ j, 0 < w j) →
  ∀ (lam : Cube ι → ι → ℝ), (∀ x, IsRow g x (lam x)) →
    2 * ∑ x ∈ univ.filter (fun x : Cube ι => g x = true),
          ∑ y ∈ univ.filter (fun y : Cube ι => g y = false),
            (∑ j ∈ diffSet x y, w j * lam x j * lam y j)⁻¹
      ≤ 2 ^ Fintype.card ι * ∑ j, (bdry g j : ℝ) / w j

end AaronsonAmbainis

end
/- END UPSTREAM MODULE: AaronsonAmbainis.AllPairsDefs -/

/- BEGIN UPSTREAM MODULE: AaronsonAmbainis.TwoSided.Basic -/
section
/-!
# Basic lemmas on `flipSet`, `antipode`, `diffSet`, `zone`
-/

namespace AaronsonAmbainis

open Finset

section NoFintype

variable {ι : Type*} [DecidableEq ι]

lemma flipSet_apply (x : Cube ι) (S : Finset ι) (i : ι) :
    flipSet x S i = if i ∈ S then !(x i) else x i := rfl

lemma flipSet_empty (x : Cube ι) : flipSet x ∅ = x := by
  funext i
  simp [flipSet]

lemma flipSet_flipSet_self (x : Cube ι) (S : Finset ι) : flipSet (flipSet x S) S = x := by
  funext i
  by_cases h : i ∈ S <;> simp [flipSet, h]

end NoFintype

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma antipode_eq_flipSet_univ (x : Cube ι) : antipode x = flipSet x univ := by
  funext i
  simp [flipSet, antipode]

lemma diffSet_flipSet (x : Cube ι) (S : Finset ι) : diffSet x (flipSet x S) = S := by
  ext i
  by_cases h : i ∈ S <;> simp [diffSet, flipSet, h]

lemma flipSet_diffSet (x y : Cube ι) : flipSet x (diffSet x y) = y := by
  funext i
  by_cases h : x i = y i
  · simp [flipSet, diffSet, h]
  · have h' : (!(x i)) = y i := by
      cases hx : x i <;> cases hy : y i <;> simp_all
    simp [flipSet, diffSet, h, h']

omit [DecidableEq ι] in
lemma mem_diffSet {x y : Cube ι} {i : ι} : i ∈ diffSet x y ↔ x i ≠ y i := by
  simp [diffSet]

lemma mem_zone {g : Cube ι → Bool} {u : Cube ι} :
    u ∈ zone g ↔ g u = true ∧ g (antipode u) = false := by
  simp [zone]

lemma card_cube : Fintype.card (Cube ι) = 2 ^ Fintype.card ι := by
  simp [Cube]

end AaronsonAmbainis

end
/- END UPSTREAM MODULE: AaronsonAmbainis.TwoSided.Basic -/

/- BEGIN UPSTREAM MODULE: AaronsonAmbainis.TwoSided.Antipodal -/
section
/-!
# The antipodal inequality from the determinant inequality (`antipodal_of_det`)

The pointwise step (Lemma 4.2 of the paper) and the proof of the antipodal inequality
(Theorem 4.3) from the determinant inequality (Corollary 3.2).

With `ℓ j = 1 / w j`, `x = lam u`, `y = lam (antipode u)`, `S = ∑ j, w j * x j * y j` and
`D = S⁻¹` (Lean: `0⁻¹ = 0`), the wing at `u` is `wingSet w x y`: empty if `S = 0`, and
`{j : ℓ j < D * y j}` otherwise.  (By the overlap lemma, Lemma 4.1 of the paper, `S > 0` on the
zone; the case `S = 0` is treated directly here, so that the overlap lemma is not needed in this
file.)
-/

namespace AaronsonAmbainis

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Steps 1 and 2 of the proof of Lemma 4.2 of the paper: if `x` is a row at `u`, `g u = true`
and `S = ∑ j, w j * x j * y j > 0`, then `{j : 1 / w j < S⁻¹ * y j}` is a 1-wing at `u`. -/
lemma wing_of_row {g : Cube ι → Bool} {u : Cube ι} {x y w : ι → ℝ} (hu : g u = true)
    (hw : ∀ j, 0 < w j) (hx : IsRow g u x) (hy : ∀ j, 0 ≤ y j)
    (hpos : 0 < ∑ j, w j * x j * y j) :
    IsWing g u (univ.filter fun j => (w j)⁻¹ < (∑ j, w j * x j * y j)⁻¹ * y j) := by
  intro T hT
  by_contra hne
  have hne' : g (flipSet u T) ≠ g u := by rw [hu]; exact hne
  have h1 : 1 ≤ ∑ j ∈ T, x j := hx.2 T hne'
  set Sm := ∑ j, w j * x j * y j with hSm
  have hD : 0 < Sm⁻¹ := inv_pos.mpr hpos
  -- every `j ∈ T` has `1 < w j * (Sm⁻¹ * y j)`
  have hA : ∀ j ∈ T, 1 < w j * (Sm⁻¹ * y j) := by
    intro j hj
    have hj' := (Finset.mem_filter.mp (hT hj)).2
    have h2 := mul_lt_mul_of_pos_left hj' (hw j)
    rwa [mul_inv_cancel₀ (hw j).ne'] at h2
  have hle : ∀ j ∈ T, x j ≤ x j * (w j * (Sm⁻¹ * y j)) := by
    intro j hj
    have h3 := hA j hj
    nlinarith [hx.1 j]
  obtain ⟨j0, hj0T, hj0⟩ : ∃ j ∈ T, 0 < x j := by
    by_contra hcon
    have h4 : ∑ j ∈ T, x j ≤ 0 :=
      Finset.sum_nonpos fun j hj => not_lt.mp fun hp => hcon ⟨j, hj, hp⟩
    linarith
  have hlt : ∑ j ∈ T, x j < ∑ j ∈ T, x j * (w j * (Sm⁻¹ * y j)) := by
    apply Finset.sum_lt_sum hle
    refine ⟨j0, hj0T, ?_⟩
    have h5 := hA j0 hj0T
    nlinarith
  have hsub : ∑ j ∈ T, x j * (w j * (Sm⁻¹ * y j)) ≤ ∑ j, x j * (w j * (Sm⁻¹ * y j)) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T)
    intro j _ _
    exact mul_nonneg (hx.1 j) (mul_nonneg (hw j).le (mul_nonneg hD.le (hy j)))
  have htot : ∑ j, x j * (w j * (Sm⁻¹ * y j)) = 1 := by
    have h6 : ∑ j, x j * (w j * (Sm⁻¹ * y j)) = Sm⁻¹ * Sm := by
      rw [hSm, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [h6, inv_mul_cancel₀ hpos.ne']
  linarith

omit [Fintype ι] in
/-- Step 3 of the proof of Lemma 4.2 of the paper: if `y` is a row at `u'`, `g u' = false`,
`g (u'^G) = true` and `D * y j ≤ ℓ j` on `G`, then `D ≤ ℓ(G)`. -/
lemma lower_of_row {g : Cube ι → Bool} {u' : Cube ι} {y ℓ : ι → ℝ} {D : ℝ} (hD : 0 ≤ D)
    (hy : IsRow g u' y) (hu' : g u' = false) (G : Finset ι)
    (hG : ∀ j ∈ G, D * y j ≤ ℓ j) (hgG : g (flipSet u' G) = true) :
    D ≤ ∑ j ∈ G, ℓ j := by
  have hne : g (flipSet u' G) ≠ g u' := by rw [hgG, hu']; simp
  have h1 : 1 ≤ ∑ j ∈ G, y j := hy.2 G hne
  calc D = D * 1 := (mul_one D).symm
    _ ≤ D * ∑ j ∈ G, y j := mul_le_mul_of_nonneg_left h1 hD
    _ = ∑ j ∈ G, D * y j := Finset.mul_sum _ _ _
    _ ≤ ∑ j ∈ G, ℓ j := Finset.sum_le_sum hG

/-- The wing used at a point with rows `x` (at the point) and `y` (at its antipode). -/
noncomputable def wingSet (w x y : ι → ℝ) : Finset ι :=
  if ∑ j, w j * x j * y j = 0 then ∅
  else univ.filter fun j => (w j)⁻¹ < (∑ j, w j * x j * y j)⁻¹ * y j

lemma wingSet_isWing {g : Cube ι → Bool} {u : Cube ι} {x y w : ι → ℝ} (hu : g u = true)
    (hw : ∀ j, 0 < w j) (hx : IsRow g u x) (hy : ∀ j, 0 ≤ y j) :
    IsWing g u (wingSet w x y) := by
  unfold wingSet
  split_ifs with h0
  · intro S hS
    rw [Finset.subset_empty.mp hS, flipSet_empty]
    exact hu
  · have hnn : 0 ≤ ∑ j, w j * x j * y j :=
      Finset.sum_nonneg fun j _ => mul_nonneg (mul_nonneg (hw j).le (hx.1 j)) (hy j)
    exact wing_of_row hu hw hx hy (lt_of_le_of_ne hnn (Ne.symm h0))

lemma wingSet_lower {g : Cube ι → Bool} {u' : Cube ι} {x y w : ι → ℝ}
    (hw : ∀ j, 0 < w j) (hx : ∀ j, 0 ≤ x j) (hy : IsRow g u' y) (hu' : g u' = false)
    (G : Finset ι) (hG : Disjoint G (wingSet w x y)) (hgG : g (flipSet u' G) = true) :
    (∑ j, w j * x j * y j)⁻¹ ≤ ∑ j ∈ G, (w j)⁻¹ := by
  have hnn : 0 ≤ ∑ j, w j * x j * y j :=
    Finset.sum_nonneg fun j _ => mul_nonneg (mul_nonneg (hw j).le (hx j)) (hy.1 j)
  by_cases h0 : ∑ j, w j * x j * y j = 0
  · rw [h0, inv_zero]
    exact Finset.sum_nonneg fun j _ => (inv_pos.mpr (hw j)).le
  · unfold wingSet at hG
    rw [if_neg h0] at hG
    refine lower_of_row (inv_nonneg.mpr hnn) hy hu' G ?_ hgG
    intro j hj
    have hjA := Finset.disjoint_left.mp hG hj
    exact not_lt.mp fun hlt => hjA (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hlt⟩)

/-- The antipodal inequality (the inequality of Theorem 4.3 of the paper) from the determinant
inequality (Corollary 3.2). -/
theorem antipodal_of_det : DetInequality → AntipodalInequality := by
  intro hDet ι _ _ g w hw lam hlam
  have key := hDet ι g (fun j => (w j)⁻¹) (fun j => inv_pos.mpr (hw j))
    (fun u => wingSet w (lam u) (lam (antipode u)))
    (fun u hu => wingSet_isWing (mem_zone.mp hu).1 hw (hlam u) (hlam (antipode u)).1)
    (fun u => (∑ j, w j * lam u j * lam (antipode u) j)⁻¹)
    (fun u hu G hG hgG =>
      wingSet_lower hw (hlam u).1 (hlam (antipode u)) (mem_zone.mp hu).2 G hG hgG)
  calc ∑ u ∈ zone g, (∑ j, w j * lam u j * lam (antipode u) j)⁻¹
      ≤ ∑ j, (w j)⁻¹ * (bdry g j : ℝ) := key
    _ = ∑ j, (bdry g j : ℝ) / w j := by
        apply Finset.sum_congr rfl
        intro j _
        rw [div_eq_mul_inv, mul_comm]

end AaronsonAmbainis

end
/- END UPSTREAM MODULE: AaronsonAmbainis.TwoSided.Antipodal -/

/- BEGIN UPSTREAM MODULE: AaronsonAmbainis.TwoSided.Glue -/
section
/-!
# Gluing two points along a set of coordinates

`glue F z u` agrees with `u` on `F` and with `z` off `F`; it is the point `γ_F(z,u)` of
Section 5.1 of the paper.  For fixed `F` and `z` the map `u ↦ glue F z u` parametrises the
subcube through `z` with free coordinates `F` (with multiplicity `2 ^ (n - |F|)`), and
`(z, u) ↦ (glue F z u, glue F u z)` is an involution of `Cube ι × Cube ι`.

The file proves the gluing lemma (Lemma 5.1 of the paper): part (i) is `glue_flipSet`, with the
special cases `glue_antipode`, `glue_flipSet_singleton_of_mem` and
`glue_flipSet_singleton_of_not_mem`; part (ii) is `sum_sum_glue`.
-/

namespace AaronsonAmbainis

open Finset

section NoFintype

variable {ι : Type*} [DecidableEq ι]

/-- `glue F z u` agrees with `u` on `F` and with `z` off `F`. -/
def glue (F : Finset ι) (z u : Cube ι) : Cube ι := fun i => if i ∈ F then u i else z i

lemma glue_flipSet (F : Finset ι) (z u : Cube ι) (S : Finset ι) :
    glue F z (flipSet u S) = flipSet (glue F z u) (S ∩ F) := by
  funext i
  by_cases hF : i ∈ F <;> by_cases hS : i ∈ S <;> simp [glue, flipSet, hF, hS]

lemma glue_antipode (F : Finset ι) (z u : Cube ι) :
    glue F z (antipode u) = flipSet (glue F z u) F := by
  funext i
  by_cases hF : i ∈ F <;> simp [glue, flipSet, antipode, hF]

lemma glue_flipSet_singleton_of_mem {F : Finset ι} {j : ι} (hj : j ∈ F) (z u : Cube ι) :
    glue F z (flipSet u {j}) = flipSet (glue F z u) {j} := by
  rw [glue_flipSet, Finset.singleton_inter_of_mem hj]

lemma glue_flipSet_singleton_of_not_mem {F : Finset ι} {j : ι} (hj : j ∉ F) (z u : Cube ι) :
    glue F z (flipSet u {j}) = glue F z u := by
  rw [glue_flipSet, Finset.singleton_inter_of_notMem hj, flipSet_empty]

lemma glue_glue_swap (F : Finset ι) (z u : Cube ι) :
    glue F (glue F z u) (glue F u z) = z := by
  funext i
  by_cases hF : i ∈ F <;> simp [glue, hF]

/-- The double-counting involution `(z, u) ↦ (glue F z u, glue F u z)`. -/
def glueEquiv (F : Finset ι) : (Cube ι × Cube ι) ≃ (Cube ι × Cube ι) where
  toFun p := (glue F p.1 p.2, glue F p.2 p.1)
  invFun q := (glue F q.1 q.2, glue F q.2 q.1)
  left_inv p := Prod.ext (glue_glue_swap F p.1 p.2) (glue_glue_swap F p.2 p.1)
  right_inv p := Prod.ext (glue_glue_swap F p.1 p.2) (glue_glue_swap F p.2 p.1)

end NoFintype

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Every point `x` is `glue F z u` for exactly `2 ^ n` pairs `(z, u)`. -/
lemma sum_sum_glue (F : Finset ι) (φ : Cube ι → ℝ) :
    ∑ z, ∑ u, φ (glue F z u) = 2 ^ Fintype.card ι * ∑ x, φ x := by
  calc ∑ z, ∑ u, φ (glue F z u)
      = ∑ p : Cube ι × Cube ι, φ ((glueEquiv F p).1) :=
        (Fintype.sum_prod_type (fun p : Cube ι × Cube ι => φ ((glueEquiv F p).1))).symm
    _ = ∑ q : Cube ι × Cube ι, φ q.1 :=
        Equiv.sum_comp (glueEquiv F) (fun q : Cube ι × Cube ι => φ q.1)
    _ = ∑ x : Cube ι, ∑ _x' : Cube ι, φ x :=
        Fintype.sum_prod_type (fun q : Cube ι × Cube ι => φ q.1)
    _ = 2 ^ Fintype.card ι * ∑ x, φ x := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.sum_const, Finset.card_univ, card_cube, nsmul_eq_mul]
        push_cast
        ring

end AaronsonAmbainis

end
/- END UPSTREAM MODULE: AaronsonAmbainis.TwoSided.Glue -/

/- BEGIN UPSTREAM MODULE: AaronsonAmbainis.TwoSided.AllPairsCore -/
section
/-!
# The all-pairs inequality for one set `F` of free coordinates (`allPairs_core`)

Step 1 of the proof of Proposition 5.2 of the paper: the antipodal inequality (Theorem 4.3)
applied to all subcubes with free coordinates `F`, added up:

  `∑ x, allPairsTerm g w lam F x ≤ ∑ j ∈ F, bdry g j / w j`,

where `allPairsTerm g w lam F x = (∑ j ∈ F, w j * lam x j * lam (x^F) j)⁻¹` if `g x = true` and
`g (x^F) = false`, and `0` otherwise (the term `T_F(x)` of the paper).

The subcube through `z` with free coordinates `F` is parametrised by `u ↦ glue F z u`
(`u : Cube ι`; the coordinates of `u` off `F` are dummies).  The antipodal inequality is applied
to `u ↦ g (glue F z u)` with the rows `lam (glue F z u)` restricted to `F`, for every `z`,
and the results are added over all `z`; `sum_sum_glue` removes the multiplicity `2 ^ n`.
-/

namespace AaronsonAmbainis

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The term `T_F(x)` of the paper: `(∑ j ∈ F, w j * lam x j * lam (x^F) j)⁻¹` if `g x = true`
and `g (x^F) = false`, and `0` otherwise. -/
noncomputable def allPairsTerm (g : Cube ι → Bool) (w : ι → ℝ) (lam : Cube ι → ι → ℝ)
    (F : Finset ι) (x : Cube ι) : ℝ :=
  if g x = true ∧ g (flipSet x F) = false then
    (∑ j ∈ F, w j * lam x j * lam (flipSet x F) j)⁻¹ else 0

omit [Fintype ι] in
/-- The restriction of a row to the free coordinates is a row of the restricted function. -/
lemma isRow_glue {g : Cube ι → Bool} {lam : Cube ι → ι → ℝ} (hlam : ∀ x, IsRow g x (lam x))
    (F : Finset ι) (z u : Cube ι) :
    IsRow (fun u => g (glue F z u)) u (fun j => if j ∈ F then lam (glue F z u) j else 0) := by
  constructor
  · intro j
    dsimp only
    split_ifs
    · exact (hlam _).1 j
    · exact le_rfl
  · intro S hS
    have hS' : g (flipSet (glue F z u) (S ∩ F)) ≠ g (glue F z u) := by
      rw [← glue_flipSet]
      exact hS
    calc (1 : ℝ) ≤ ∑ j ∈ S ∩ F, lam (glue F z u) j := (hlam (glue F z u)).2 (S ∩ F) hS'
      _ = ∑ j ∈ S, if j ∈ F then lam (glue F z u) j else 0 :=
          (Finset.sum_ite_mem S F (fun j => lam (glue F z u) j)).symm

/-- A sum of products of two restricted vectors is a sum over the restriction set. -/
lemma sum_ite_ite_mem (F : Finset ι) (w a b : ι → ℝ) :
    ∑ j, w j * (if j ∈ F then a j else 0) * (if j ∈ F then b j else 0)
      = ∑ j ∈ F, w j * a j * b j := by
  have h1 : ∑ j ∈ F, w j * (if j ∈ F then a j else 0) * (if j ∈ F then b j else 0)
      = ∑ j, w j * (if j ∈ F then a j else 0) * (if j ∈ F then b j else 0) := by
    apply Finset.sum_subset (Finset.subset_univ F)
    intro j _ hj
    simp [hj]
  rw [← h1]
  apply Finset.sum_congr rfl
  intro j hj
  simp [hj]

/-- The left side of the antipodal inequality for the restricted function, in terms of
`allPairsTerm`. -/
lemma zone_sum_glue (g : Cube ι → Bool) (w : ι → ℝ) (lam : Cube ι → ι → ℝ)
    (F : Finset ι) (z : Cube ι) :
    ∑ u ∈ zone (fun u => g (glue F z u)),
        (∑ j, w j * (if j ∈ F then lam (glue F z u) j else 0)
          * (if j ∈ F then lam (glue F z (antipode u)) j else 0))⁻¹
      = ∑ u, allPairsTerm g w lam F (glue F z u) := by
  unfold zone
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro u _
  simp only [glue_antipode, sum_ite_ite_mem, allPairsTerm]

/-- `bdry` as a real sum of indicators. -/
lemma bdry_eq_sum (g : Cube ι → Bool) (j : ι) :
    (bdry g j : ℝ) = ∑ x, (if g x = true ∧ g (flipSet x {j}) = false then (1 : ℝ) else 0) := by
  unfold bdry
  rw [Finset.sum_boole]

/-- A coordinate that is not free has no bichromatic edge in the subcube. -/
lemma bdry_glue_of_not_mem (g : Cube ι → Bool) {F : Finset ι} {j : ι} (hj : j ∉ F)
    (z : Cube ι) : bdry (fun u => g (glue F z u)) j = 0 := by
  unfold bdry
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro u _
  simp only [glue_flipSet_singleton_of_not_mem hj]
  rintro ⟨h1, h2⟩
  rw [h1] at h2
  exact Bool.noConfusion h2

/-- A free coordinate: the bichromatic `j`-edges of all subcubes with free coordinates `F`
are the bichromatic `j`-edges of `g`, each `2 ^ n` times. -/
lemma sum_bdry_glue_of_mem (g : Cube ι → Bool) {F : Finset ι} {j : ι} (hj : j ∈ F) :
    ∑ z, (bdry (fun u => g (glue F z u)) j : ℝ) = 2 ^ Fintype.card ι * (bdry g j : ℝ) := by
  have h1 : ∀ z, (bdry (fun u => g (glue F z u)) j : ℝ)
      = ∑ u, (fun x => if g x = true ∧ g (flipSet x {j}) = false then (1 : ℝ) else 0)
          (glue F z u) := by
    intro z
    rw [bdry_eq_sum]
    apply Finset.sum_congr rfl
    intro u _
    simp only [glue_flipSet_singleton_of_mem hj]
  rw [Finset.sum_congr rfl (fun z _ => h1 z), bdry_eq_sum]
  exact sum_sum_glue F (fun x => if g x = true ∧ g (flipSet x {j}) = false then (1 : ℝ) else 0)

/-- The inequality for one set `F` of free coordinates (Step 1 of the proof of Proposition 5.2
of the paper), from the antipodal inequality. -/
lemma allPairs_core (hAntipodal : AntipodalInequality) {ι : Type} [Fintype ι] [DecidableEq ι]
    (g : Cube ι → Bool) (w : ι → ℝ) (hw : ∀ j, 0 < w j)
    (lam : Cube ι → ι → ℝ) (hlam : ∀ x, IsRow g x (lam x)) (F : Finset ι) :
    ∑ x, allPairsTerm g w lam F x ≤ ∑ j ∈ F, (bdry g j : ℝ) / w j := by
  -- the antipodal inequality on the subcube through `z`
  have hz : ∀ z : Cube ι, ∑ u, allPairsTerm g w lam F (glue F z u)
      ≤ ∑ j, (bdry (fun u => g (glue F z u)) j : ℝ) / w j := by
    intro z
    have h := hAntipodal ι (fun u => g (glue F z u)) w hw
      (fun u j => if j ∈ F then lam (glue F z u) j else 0) (fun u => isRow_glue hlam F z u)
    rw [← zone_sum_glue]
    exact h
  -- add over all `z`
  have hsum : ∑ z, ∑ u, allPairsTerm g w lam F (glue F z u)
      ≤ ∑ z, ∑ j, (bdry (fun u => g (glue F z u)) j : ℝ) / w j :=
    Finset.sum_le_sum fun z _ => hz z
  rw [sum_sum_glue] at hsum
  have hj : ∀ j, ∑ z, (bdry (fun u => g (glue F z u)) j : ℝ) / w j
      = if j ∈ F then 2 ^ Fintype.card ι * ((bdry g j : ℝ) / w j) else 0 := by
    intro j
    split_ifs with hjF
    · rw [← Finset.sum_div, sum_bdry_glue_of_mem g hjF, mul_div_assoc]
    · apply Finset.sum_eq_zero
      intro z _
      rw [bdry_glue_of_not_mem g hjF z]
      simp
  have hR : ∑ z, ∑ j, (bdry (fun u => g (glue F z u)) j : ℝ) / w j
      = 2 ^ Fintype.card ι * ∑ j ∈ F, (bdry g j : ℝ) / w j := by
    rw [Finset.sum_comm, Finset.sum_congr rfl (fun j _ => hj j), Fintype.sum_ite_mem,
      Finset.mul_sum]
  rw [hR] at hsum
  exact le_of_mul_le_mul_left hsum (by positivity)

end AaronsonAmbainis

end
/- END UPSTREAM MODULE: AaronsonAmbainis.TwoSided.AllPairsCore -/

/- BEGIN UPSTREAM MODULE: AaronsonAmbainis.TwoSided.AllPairs -/
section
/-!
# The all-pairs inequality from the antipodal inequality (`allPairs_of_antipodal`)

Step 2 of the proof of Proposition 5.2 of the paper (all sets of free coordinates).

`allPairs_core` (file `AllPairsCore.lean`) is the sum of the antipodal inequality over all
subcubes with a fixed set `F` of free coordinates.  Here the inequalities `allPairs_core` are
added over all `F`:

* left side: for fixed `x`, `F ↦ x^F` is a bijection from sets of coordinates to points,
  with inverse `y ↦ diffSet x y` (`sum_allPairsTerm`);
* right side: each coordinate lies in exactly half of all sets (`two_mul_sum_finset_sum`).
-/

namespace AaronsonAmbainis

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- For fixed `x`, `F ↦ x^F` is a bijection from sets of coordinates to points. -/
def flipEquiv (x : Cube ι) : Finset ι ≃ Cube ι where
  toFun F := flipSet x F
  invFun y := diffSet x y
  left_inv F := diffSet_flipSet x F
  right_inv y := flipSet_diffSet x y

/-- The terms of `x` in all the inequalities `allPairs_core` are the terms of the pairs `(x, y)`. -/
lemma sum_allPairsTerm (g : Cube ι → Bool) (w : ι → ℝ) (lam : Cube ι → ι → ℝ) (x : Cube ι) :
    ∑ F : Finset ι, allPairsTerm g w lam F x
      = ∑ y, if g x = true ∧ g y = false then
          (∑ j ∈ diffSet x y, w j * lam x j * lam y j)⁻¹ else 0 := by
  apply Fintype.sum_equiv (flipEquiv x)
  intro F
  show allPairsTerm g w lam F x = if g x = true ∧ g (flipSet x F) = false then
    (∑ j ∈ diffSet x (flipSet x F), w j * lam x j * lam (flipSet x F) j)⁻¹ else 0
  rw [diffSet_flipSet]
  rfl

/-- Each coordinate lies in exactly half of all sets. -/
lemma two_mul_sum_finset_sum (β : ι → ℝ) :
    2 * ∑ F : Finset ι, ∑ j ∈ F, β j = 2 ^ Fintype.card ι * ∑ j, β j := by
  have hcompl : ∑ F : Finset ι, ∑ j ∈ Fᶜ, β j = ∑ F : Finset ι, ∑ j ∈ F, β j :=
    Fintype.sum_bijective (compl : Finset ι → Finset ι) compl_bijective
      (fun F => ∑ j ∈ Fᶜ, β j) (fun F => ∑ j ∈ F, β j) (fun _ => rfl)
  calc 2 * ∑ F : Finset ι, ∑ j ∈ F, β j
      = ∑ F : Finset ι, ∑ j ∈ F, β j + ∑ F : Finset ι, ∑ j ∈ Fᶜ, β j := by
        rw [hcompl]; ring
    _ = ∑ F : Finset ι, (∑ j ∈ F, β j + ∑ j ∈ Fᶜ, β j) := Finset.sum_add_distrib.symm
    _ = ∑ _F : Finset ι, ∑ j, β j := by
        apply Finset.sum_congr rfl
        intro F _
        exact Finset.sum_add_sum_compl F β
    _ = 2 ^ Fintype.card ι * ∑ j, β j := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_finset, nsmul_eq_mul]
        push_cast
        ring

/-- The all-pairs inequality (the inequality of Proposition 5.2 of the paper, multiplied by `2`)
from the antipodal inequality (Theorem 4.3). -/
theorem allPairs_of_antipodal : AntipodalInequality → AllPairsInequality := by
  intro hAntipodal ι _ _ g w hw lam hlam
  -- the left side as a sum of the terms of all the inequalities `allPairs_core`
  have hL : ∑ x ∈ univ.filter (fun x : Cube ι => g x = true),
        ∑ y ∈ univ.filter (fun y : Cube ι => g y = false),
          (∑ j ∈ diffSet x y, w j * lam x j * lam y j)⁻¹
      = ∑ x, ∑ F : Finset ι, allPairsTerm g w lam F x := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : g x = true
    · rw [if_pos hx, sum_allPairsTerm, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy : g y = false
      · rw [if_pos hy, if_pos ⟨hx, hy⟩]
      · rw [if_neg hy, if_neg (fun h => hy h.2)]
    · rw [if_neg hx, sum_allPairsTerm]
      symm
      apply Finset.sum_eq_zero
      intro y _
      rw [if_neg (fun h => hx h.1)]
  -- `allPairs_core` for every `F`, added up
  have hF : ∑ F : Finset ι, ∑ x, allPairsTerm g w lam F x
      ≤ ∑ F : Finset ι, ∑ j ∈ F, (bdry g j : ℝ) / w j :=
    Finset.sum_le_sum fun F _ => allPairs_core hAntipodal g w hw lam hlam F
  rw [hL, Finset.sum_comm]
  calc 2 * ∑ F : Finset ι, ∑ x, allPairsTerm g w lam F x
      ≤ 2 * ∑ F : Finset ι, ∑ j ∈ F, (bdry g j : ℝ) / w j := by linarith
    _ = 2 ^ Fintype.card ι * ∑ j, (bdry g j : ℝ) / w j :=
        two_mul_sum_finset_sum (fun j => (bdry g j : ℝ) / w j)

end AaronsonAmbainis

end
/- END UPSTREAM MODULE: AaronsonAmbainis.TwoSided.AllPairs -/

/- BEGIN UPSTREAM MODULE: AaronsonAmbainis.TwoSided.Overlap -/
section
/-!
# The overlap lemma and the boundary/influence identity

The overlap lemma (Lemma 4.1 of the paper; `overlap`, `overlap_pos`) and the identity
`b_j(g) = 2^(n-1) I_j(g)` (Lemma 2.1; `two_mul_bdry`).
-/

namespace AaronsonAmbainis

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The overlap lemma (Lemma 4.1 of the paper): rows at points with different values overlap on
the difference set. -/
lemma overlap {g : Cube ι → Bool} {p q : Cube ι} (hpq : g p ≠ g q) {x y : ι → ℝ}
    (hx : IsRow g p x) (hy : IsRow g q y) :
    1 ≤ ∑ j ∈ diffSet p q, min (x j) (y j) := by
  -- `T` is the set `S` of the proof in the paper: `{j ∈ Δ : x_j ≤ y_j}`
  obtain ⟨T, hT⟩ : ∃ T : Finset ι, T = (diffSet p q).filter (fun j => x j ≤ y j) := ⟨_, rfl⟩
  have hTsub : T ⊆ diffSet p q := by
    rw [hT]
    exact Finset.filter_subset _ _
  -- `p^T = q^(Δ \ T)`
  have hr : flipSet p T = flipSet q (diffSet p q \ T) := by
    funext i
    simp only [flipSet]
    by_cases hi : i ∈ diffSet p q
    · have hpi : p i ≠ q i := mem_diffSet.mp hi
      by_cases hiT : i ∈ T
      · have hiT' : i ∉ diffSet p q \ T := fun h => (Finset.mem_sdiff.mp h).2 hiT
        rw [if_pos hiT, if_neg hiT']
        cases hp : p i <;> cases hq : q i <;> simp_all
      · have hiT' : i ∈ diffSet p q \ T := Finset.mem_sdiff.mpr ⟨hi, hiT⟩
        rw [if_neg hiT, if_pos hiT']
        cases hp : p i <;> cases hq : q i <;> simp_all
    · have hpi : p i = q i := by
        by_contra h
        exact hi (mem_diffSet.mpr h)
      have h1 : i ∉ T := fun h => hi (hTsub h)
      have h2 : i ∉ diffSet p q \ T := fun h => hi (Finset.mem_sdiff.mp h).1
      rw [if_neg h1, if_neg h2, hpi]
  -- the sum of minima is `y(Δ \ T) + x(T)`
  have hsplit : ∑ j ∈ diffSet p q \ T, y j + ∑ j ∈ T, x j
      = ∑ j ∈ diffSet p q, min (x j) (y j) := by
    rw [← Finset.sum_sdiff hTsub]
    congr 1
    · apply Finset.sum_congr rfl
      intro j hj
      obtain ⟨hjΔ, hjT⟩ := Finset.mem_sdiff.mp hj
      have hnot : ¬ x j ≤ y j := fun h => hjT (by rw [hT]; exact Finset.mem_filter.mpr ⟨hjΔ, h⟩)
      exact (min_eq_right (le_of_not_ge hnot)).symm
    · apply Finset.sum_congr rfl
      intro j hj
      rw [hT] at hj
      exact (min_eq_left (Finset.mem_filter.mp hj).2).symm
  rw [← hsplit]
  have hxT : 0 ≤ ∑ j ∈ T, x j := Finset.sum_nonneg fun j _ => hx.1 j
  have hyT : 0 ≤ ∑ j ∈ diffSet p q \ T, y j := Finset.sum_nonneg fun j _ => hy.1 j
  by_cases hg : g (flipSet p T) = g p
  · have hne : g (flipSet q (diffSet p q \ T)) ≠ g q := by
      rw [← hr, hg]
      exact hpq
    have h1 := hy.2 _ hne
    linarith
  · have h1 := hx.2 T hg
    linarith

/-- Consequence of the overlap lemma: the weighted overlap is positive. -/
lemma overlap_pos {g : Cube ι → Bool} {p q : Cube ι} (hpq : g p ≠ g q) {x y : ι → ℝ}
    (hx : IsRow g p x) (hy : IsRow g q y) {w : ι → ℝ} (hw : ∀ j, 0 < w j) :
    0 < ∑ j ∈ diffSet p q, w j * x j * y j := by
  have h1 := overlap hpq hx hy
  obtain ⟨j, hj, hjpos⟩ : ∃ j ∈ diffSet p q, 0 < min (x j) (y j) := by
    by_contra hcon
    have h2 : ∑ j ∈ diffSet p q, min (x j) (y j) ≤ 0 :=
      Finset.sum_nonpos fun j hj => not_lt.mp fun hp => hcon ⟨j, hj, hp⟩
    linarith
  have hxj : 0 < x j := lt_of_lt_of_le hjpos (min_le_left _ _)
  have hyj : 0 < y j := lt_of_lt_of_le hjpos (min_le_right _ _)
  apply Finset.sum_pos'
  · intro i _
    exact mul_nonneg (mul_nonneg (hw i).le (hx.1 i)) (hy.1 i)
  · exact ⟨j, hj, mul_pos (mul_pos (hw j) hxj) hyj⟩

/-- The points where flipping `j` changes `g` are twice the bichromatic `j`-edges. -/
lemma card_sensitive (g : Cube ι → Bool) (j : ι) :
    (univ.filter fun x : Cube ι => g (flipSet x {j}) ≠ g x).card = 2 * bdry g j := by
  have hsplit : (univ.filter fun x : Cube ι => g (flipSet x {j}) ≠ g x)
      = (univ.filter fun x : Cube ι => g x = true ∧ g (flipSet x {j}) = false)
        ∪ (univ.filter fun x : Cube ι => g x = false ∧ g (flipSet x {j}) = true) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    cases hx : g x <;> cases hy : g (flipSet x {j}) <;> simp
  have hdisj : Disjoint (univ.filter fun x : Cube ι => g x = true ∧ g (flipSet x {j}) = false)
      (univ.filter fun x : Cube ι => g x = false ∧ g (flipSet x {j}) = true) := by
    rw [Finset.disjoint_filter]
    intro x _ h1 h2
    rw [h1.1] at h2
    exact Bool.noConfusion h2.1
  have hB : (univ.filter fun x : Cube ι => g x = false ∧ g (flipSet x {j}) = true).card
      = (univ.filter fun x : Cube ι => g x = true ∧ g (flipSet x {j}) = false).card := by
    apply Finset.card_bij (fun x _ => flipSet x {j})
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      rw [flipSet_flipSet_self]
      exact ⟨hx.2, hx.1⟩
    · intro x _ y _ h
      have h' := congrArg (fun z => flipSet z {j}) h
      simpa [flipSet_flipSet_self] using h'
    · intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
      refine ⟨flipSet y {j}, ?_, flipSet_flipSet_self y {j}⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [flipSet_flipSet_self]
      exact ⟨hy.2, hy.1⟩
  rw [hsplit, Finset.card_union_of_disjoint hdisj, hB]
  unfold bdry
  ring

/-- Lemma 2.1 of the paper: `2 b_j(g) = 2^n I_j(g)`, that is, `b_j(g) = 2^(n-1) I_j(g)`. -/
lemma two_mul_bdry (g : Cube ι → Bool) (j : ι) :
    2 * (bdry g j : ℝ) = 2 ^ Fintype.card ι * infl g j := by
  have h2 : (2 : ℝ) ^ Fintype.card ι ≠ 0 := by positivity
  unfold infl
  rw [card_sensitive]
  push_cast
  field_simp

end AaronsonAmbainis

end
/- END UPSTREAM MODULE: AaronsonAmbainis.TwoSided.Overlap -/

/- BEGIN UPSTREAM MODULE: AaronsonAmbainis.TwoSided.CauchySchwarz -/
section
/-!
# Cauchy–Schwarz and the choice of weights

The lemma that removes the weights (Lemma 5.3 of the paper, Section 5.2), for two finite
families of non-negative vectors (no cube). The steps of its proof: the Cauchy–Schwarz inequality
over the pairs (Step 1, `pair_cs`), the choice of the weights `w j = 1 / (√(X j * Y j) + ε)` with
`ε → 0` (Step 2, `weight_choice`), the Cauchy–Schwarz inequality over the coordinates (Step 3, in
`cs_core`), and the conclusion (`le_of_sq_le_mul`).

`abstract_cs` (Lemma 5.3): if the sums `∑_{j ∈ D x y} w j * a x j * b y j` are positive and
`∑_{x ∈ O} ∑_{y ∈ N} (∑_{j ∈ D x y} w j * a x j * b y j)⁻¹ ≤ C * ∑ j, (w j)⁻¹`
for every positive weight vector `w`, then
`(∑_{x ∈ O} (∑ j, a x j)⁻¹) * (∑_{y ∈ N} (∑ j, b y j)⁻¹) ≤ C`.

The lemma `abstract_cs` is used twice: for the two-sided inequality (`RemoveWeights.lean`) and
for the third-moment inequality (`Level/ThirdMoment.lean`).
-/

namespace AaronsonAmbainis

open Finset

/-- `s⁻¹ ^ 2 * s = s⁻¹` for every real `s` (also for `s = 0`). -/
lemma inv_sq_mul_self (s : ℝ) : s⁻¹ ^ 2 * s = s⁻¹ := by
  by_cases hs : s = 0
  · simp [hs]
  · rw [pow_two, mul_assoc, inv_mul_cancel₀ hs, mul_one]

/-- Expanding a weighted sum of products of two combinations of rows. -/
lemma sum_mul_rows {α β ι : Type*} [Fintype ι] (O : Finset α) (N : Finset β)
    (w : ι → ℝ) (u : α → ℝ) (v : β → ℝ) (f : α → ι → ℝ) (h : β → ι → ℝ) :
    ∑ j, w j * (∑ x ∈ O, u x * f x j) * (∑ y ∈ N, v y * h y j)
      = ∑ x ∈ O, ∑ y ∈ N, (u x * v y) * ∑ j, w j * f x j * h y j := by
  have h1 : ∀ j, w j * (∑ x ∈ O, u x * f x j) * (∑ y ∈ N, v y * h y j)
      = ∑ x ∈ O, ∑ y ∈ N, (u x * v y) * (w j * f x j * h y j) := by
    intro j
    rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    ring
  rw [Finset.sum_congr rfl (fun j _ => h1 j), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  exact (Finset.mul_sum _ _ _).symm

/-- Cauchy–Schwarz over pairs. -/
lemma pair_cs {α β : Type*} (O : Finset α) (N : Finset β) (c s : α → β → ℝ)
    (hs : ∀ x ∈ O, ∀ y ∈ N, 0 < s x y) :
    (∑ x ∈ O, ∑ y ∈ N, c x y) ^ 2
      ≤ (∑ x ∈ O, ∑ y ∈ N, c x y ^ 2 * s x y) * (∑ x ∈ O, ∑ y ∈ N, (s x y)⁻¹) := by
  rw [← Finset.sum_product' O N (fun x y => c x y),
    ← Finset.sum_product' O N (fun x y => c x y ^ 2 * s x y),
    ← Finset.sum_product' O N (fun x y => (s x y)⁻¹)]
  refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (O ×ˢ N) ?_ ?_ ?_
  · intro p hp
    obtain ⟨hx, hy⟩ := Finset.mem_product.mp hp
    exact mul_nonneg (sq_nonneg _) (hs p.1 hx p.2 hy).le
  · intro p hp
    obtain ⟨hx, hy⟩ := Finset.mem_product.mp hp
    exact (inv_pos.mpr (hs p.1 hx p.2 hy)).le
  · intro p hp
    obtain ⟨hx, hy⟩ := Finset.mem_product.mp hp
    have h := hs p.1 hx p.2 hy
    have he : c p.1 p.2 ^ 2 * s p.1 p.2 * (s p.1 p.2)⁻¹ = c p.1 p.2 ^ 2 := by
      rw [mul_assoc, mul_inv_cancel₀ h.ne', mul_one]
    exact he.ge

/-- If `Q ≤ S * (C * (S + c * ε))` for every `ε > 0`, then `Q ≤ C * S ^ 2`. -/
lemma le_of_forall_eps {Q S C c : ℝ} (hS : 0 ≤ S) (hC : 0 ≤ C) (hc : 0 ≤ c)
    (h : ∀ ε : ℝ, 0 < ε → Q ≤ S * (C * (S + c * ε))) : Q ≤ C * S ^ 2 := by
  apply le_of_forall_pos_le_add
  intro δ hδ
  have hK : 0 ≤ C * S * c := mul_nonneg (mul_nonneg hC hS) hc
  have hK1 : 0 < C * S * c + 1 := by linarith
  have h2 := h (δ / (C * S * c + 1)) (div_pos hδ hK1)
  have h3 : C * S * c * (δ / (C * S * c + 1)) ≤ δ := by
    rw [← mul_div_assoc, div_le_iff₀ hK1]
    nlinarith
  calc Q ≤ S * (C * (S + c * (δ / (C * S * c + 1)))) := h2
    _ = C * S ^ 2 + C * S * c * (δ / (C * S * c + 1)) := by ring
    _ ≤ C * S ^ 2 + δ := by linarith

/-- The choice of the weights `w j = 1 / (√(X j * Y j) + ε)`, `ε → 0`
(Step 2 of the proof of Lemma 5.3 of the paper). -/
lemma weight_choice {ι : Type*} [Fintype ι] (X Y : ι → ℝ) (hX : ∀ j, 0 ≤ X j)
    (hY : ∀ j, 0 ≤ Y j) (C Q : ℝ) (hC : 0 ≤ C)
    (h : ∀ w : ι → ℝ, (∀ j, 0 < w j) →
      Q ≤ (∑ j, w j * X j * Y j) * (C * ∑ j, (w j)⁻¹)) :
    Q ≤ C * (∑ j, Real.sqrt (X j * Y j)) ^ 2 := by
  have hr : ∀ j, 0 ≤ Real.sqrt (X j * Y j) := fun j => Real.sqrt_nonneg _
  have hS : 0 ≤ ∑ j, Real.sqrt (X j * Y j) := Finset.sum_nonneg fun j _ => hr j
  have hcard : (0 : ℝ) ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
  refine le_of_forall_eps hS hC hcard ?_
  intro ε hε
  have hw : ∀ j, 0 < (Real.sqrt (X j * Y j) + ε)⁻¹ := fun j =>
    inv_pos.mpr (add_pos_of_nonneg_of_pos (hr j) hε)
  have h1 := h (fun j => (Real.sqrt (X j * Y j) + ε)⁻¹) hw
  have hA : ∑ j, (Real.sqrt (X j * Y j) + ε)⁻¹ * X j * Y j
      ≤ ∑ j, Real.sqrt (X j * Y j) := by
    apply Finset.sum_le_sum
    intro j _
    have hpos : 0 < Real.sqrt (X j * Y j) + ε := add_pos_of_nonneg_of_pos (hr j) hε
    have hsq : Real.sqrt (X j * Y j) * Real.sqrt (X j * Y j) = X j * Y j :=
      Real.mul_self_sqrt (mul_nonneg (hX j) (hY j))
    rw [mul_assoc, inv_mul_le_iff₀ hpos]
    nlinarith [mul_nonneg (hr j) hε.le]
  have hB : ∑ j, ((Real.sqrt (X j * Y j) + ε)⁻¹)⁻¹
      = ∑ j, Real.sqrt (X j * Y j) + (Fintype.card ι : ℝ) * ε := by
    simp only [inv_inv]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hD : 0 ≤ C * (∑ j, Real.sqrt (X j * Y j) + (Fintype.card ι : ℝ) * ε) :=
    mul_nonneg hC (add_nonneg hS (mul_nonneg hcard hε.le))
  calc Q ≤ (∑ j, (Real.sqrt (X j * Y j) + ε)⁻¹ * X j * Y j)
        * (C * ∑ j, ((Real.sqrt (X j * Y j) + ε)⁻¹)⁻¹) := h1
    _ = (∑ j, (Real.sqrt (X j * Y j) + ε)⁻¹ * X j * Y j)
        * (C * (∑ j, Real.sqrt (X j * Y j) + (Fintype.card ι : ℝ) * ε)) := by rw [hB]
    _ ≤ (∑ j, Real.sqrt (X j * Y j))
        * (C * (∑ j, Real.sqrt (X j * Y j) + (Fintype.card ι : ℝ) * ε)) :=
        mul_le_mul_of_nonneg_right hA hD

/-- `P ^ 2 ≤ C * P` and `0 ≤ C` give `P ≤ C`. -/
lemma le_of_sq_le_mul {P C : ℝ} (hC : 0 ≤ C) (h : P ^ 2 ≤ C * P) : P ≤ C := by
  by_contra hcon
  have hlt : C < P := not_le.mp hcon
  have hPpos : 0 < P := lt_of_le_of_lt hC hlt
  nlinarith [mul_pos (sub_pos.mpr hlt) hPpos]

/-- The Cauchy–Schwarz argument with general coefficients `u`, `v` satisfying
`u x ^ 2 * ∑ j, a x j = u x` and `v y ^ 2 * ∑ j, b y j = v y`. -/
lemma cs_core {α β ι : Type*} [Fintype ι] (O : Finset α) (N : Finset β)
    (a : α → ι → ℝ) (b : β → ι → ℝ) (ha : ∀ x j, 0 ≤ a x j) (hb : ∀ y j, 0 ≤ b y j)
    (u : α → ℝ) (v : β → ℝ)
    (hua : ∀ x, u x ^ 2 * ∑ j, a x j = u x) (hvb : ∀ y, v y ^ 2 * ∑ j, b y j = v y)
    (D : α → β → Finset ι) (C : ℝ) (hC : 0 ≤ C)
    (hpos : ∀ x ∈ O, ∀ y ∈ N, ∀ w : ι → ℝ, (∀ j, 0 < w j) →
      0 < ∑ j ∈ D x y, w j * a x j * b y j)
    (hpairs : ∀ w : ι → ℝ, (∀ j, 0 < w j) →
      ∑ x ∈ O, ∑ y ∈ N, (∑ j ∈ D x y, w j * a x j * b y j)⁻¹ ≤ C * ∑ j, (w j)⁻¹) :
    (∑ x ∈ O, u x) * (∑ y ∈ N, v y) ≤ C := by
  have hX : ∀ j, 0 ≤ ∑ x ∈ O, u x ^ 2 * a x j := fun j =>
    Finset.sum_nonneg fun x _ => mul_nonneg (sq_nonneg _) (ha x j)
  have hY : ∀ j, 0 ≤ ∑ y ∈ N, v y ^ 2 * b y j := fun j =>
    Finset.sum_nonneg fun y _ => mul_nonneg (sq_nonneg _) (hb y j)
  have hXsum : ∑ j, ∑ x ∈ O, u x ^ 2 * a x j = ∑ x ∈ O, u x := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    rw [← Finset.mul_sum, hua x]
  have hYsum : ∑ j, ∑ y ∈ N, v y ^ 2 * b y j = ∑ y ∈ N, v y := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    rw [← Finset.mul_sum, hvb y]
  -- Cauchy–Schwarz over pairs, for every weight vector
  have hB : ∀ w : ι → ℝ, (∀ j, 0 < w j) →
      ((∑ x ∈ O, u x) * (∑ y ∈ N, v y)) ^ 2
        ≤ (∑ j, w j * (∑ x ∈ O, u x ^ 2 * a x j) * (∑ y ∈ N, v y ^ 2 * b y j))
          * (C * ∑ j, (w j)⁻¹) := by
    intro w hw
    have h1 := pair_cs O N (fun x y => u x * v y)
      (fun x y => ∑ j ∈ D x y, w j * a x j * b y j) (fun x hx y hy => hpos x hx y hy w hw)
    have h2 : ∑ x ∈ O, ∑ y ∈ N, (u x * v y) ^ 2 * ∑ j ∈ D x y, w j * a x j * b y j
        ≤ ∑ j, w j * (∑ x ∈ O, u x ^ 2 * a x j) * (∑ y ∈ N, v y ^ 2 * b y j) := by
      rw [sum_mul_rows O N w (fun x => u x ^ 2) (fun y => v y ^ 2) a b]
      apply Finset.sum_le_sum
      intro x _
      apply Finset.sum_le_sum
      intro y _
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun j _ _ => mul_nonneg (mul_nonneg (hw j).le (ha x j)) (hb y j)))
        (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    have h3 : 0 ≤ ∑ x ∈ O, ∑ y ∈ N, (∑ j ∈ D x y, w j * a x j * b y j)⁻¹ :=
      Finset.sum_nonneg fun x hx => Finset.sum_nonneg fun y hy =>
        (inv_pos.mpr (hpos x hx y hy w hw)).le
    have h4 : 0 ≤ ∑ j, w j * (∑ x ∈ O, u x ^ 2 * a x j) * (∑ y ∈ N, v y ^ 2 * b y j) :=
      Finset.sum_nonneg fun j _ => mul_nonneg (mul_nonneg (hw j).le (hX j)) (hY j)
    calc ((∑ x ∈ O, u x) * (∑ y ∈ N, v y)) ^ 2
        = (∑ x ∈ O, ∑ y ∈ N, u x * v y) ^ 2 := by rw [Finset.sum_mul_sum]
      _ ≤ (∑ x ∈ O, ∑ y ∈ N, (u x * v y) ^ 2 * ∑ j ∈ D x y, w j * a x j * b y j)
          * (∑ x ∈ O, ∑ y ∈ N, (∑ j ∈ D x y, w j * a x j * b y j)⁻¹) := h1
      _ ≤ (∑ j, w j * (∑ x ∈ O, u x ^ 2 * a x j) * (∑ y ∈ N, v y ^ 2 * b y j))
          * (C * ∑ j, (w j)⁻¹) := mul_le_mul h2 (hpairs w hw) h3 h4
  -- the choice of the weights
  have hW := weight_choice (fun j => ∑ x ∈ O, u x ^ 2 * a x j)
    (fun j => ∑ y ∈ N, v y ^ 2 * b y j) hX hY C
    (((∑ x ∈ O, u x) * (∑ y ∈ N, v y)) ^ 2) hC hB
  -- Cauchy–Schwarz over the coordinates
  have hCS : (∑ j, Real.sqrt ((∑ x ∈ O, u x ^ 2 * a x j) * (∑ y ∈ N, v y ^ 2 * b y j))) ^ 2
      ≤ (∑ j, ∑ x ∈ O, u x ^ 2 * a x j) * (∑ j, ∑ y ∈ N, v y ^ 2 * b y j) :=
    Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ (fun j _ => hX j) (fun j _ => hY j)
      (fun j _ => (Real.sq_sqrt (mul_nonneg (hX j) (hY j))).le)
  rw [hXsum, hYsum] at hCS
  exact le_of_sq_le_mul hC (le_trans hW (mul_le_mul_of_nonneg_left hCS hC))

/-- The lemma that removes the weights (Lemma 5.3 of the paper): Steps 1–3 and the conclusion of
its proof. The reciprocals are `⁻¹`, with `0⁻¹ = 0` in Lean, and the sets `O` and `N` may be
empty; so the first assertion of Lemma 5.3, that the sums `∑ j, a x j` and `∑ j, b y j` are
positive, is not part of this statement. -/
lemma abstract_cs {α β ι : Type*} [Fintype ι] (O : Finset α) (N : Finset β)
    (a : α → ι → ℝ) (b : β → ι → ℝ) (ha : ∀ x j, 0 ≤ a x j) (hb : ∀ y j, 0 ≤ b y j)
    (D : α → β → Finset ι) (C : ℝ) (hC : 0 ≤ C)
    (hpos : ∀ x ∈ O, ∀ y ∈ N, ∀ w : ι → ℝ, (∀ j, 0 < w j) →
      0 < ∑ j ∈ D x y, w j * a x j * b y j)
    (hpairs : ∀ w : ι → ℝ, (∀ j, 0 < w j) →
      ∑ x ∈ O, ∑ y ∈ N, (∑ j ∈ D x y, w j * a x j * b y j)⁻¹ ≤ C * ∑ j, (w j)⁻¹) :
    (∑ x ∈ O, (∑ j, a x j)⁻¹) * (∑ y ∈ N, (∑ j, b y j)⁻¹) ≤ C :=
  cs_core O N a b ha hb (fun x => (∑ j, a x j)⁻¹) (fun y => (∑ j, b y j)⁻¹)
    (fun x => inv_sq_mul_self (∑ j, a x j)) (fun y => inv_sq_mul_self (∑ j, b y j))
    D C hC hpos hpairs

end AaronsonAmbainis

end
/- END UPSTREAM MODULE: AaronsonAmbainis.TwoSided.CauchySchwarz -/

/- BEGIN UPSTREAM MODULE: AaronsonAmbainis.TwoSided.RemoveWeights -/
section
/-!
# The two-sided inequality from the all-pairs inequality (`twoSided_of_allPairs`)

Section 5.2 of the paper (the proof of Theorem 5.4).

From the all-pairs inequality and `bdry g j = 2 ^ n * infl g j / 2 ≤ 2 ^ n * τ / 2`:

  `∑_{x ∈ O} ∑_{y ∈ N} (∑_{j ∈ Δ(x,y)} w j * lam x j * lam y j)⁻¹ ≤ (4 ^ n * τ / 4) * ∑ j, (w j)⁻¹`

for every positive weight vector `w` (`O = {g = true}`, `N = {g = false}`).  The lemma that
removes the weights (Lemma 5.3, `abstract_cs` in the file `CauchySchwarz.lean`) gives
`(∑_{x ∈ O} ‖lam x‖₁⁻¹) * (∑_{y ∈ N} ‖lam y‖₁⁻¹) ≤ 4 ^ n * τ / 4`; the overlap lemma
(file `Overlap.lean`) supplies the positivity of the denominators.
-/

namespace AaronsonAmbainis

open Finset

/-- The final arithmetic: `VO * VN ≤ T * T * τ / 4` gives `4 * (VO / T) * (VN / T) ≤ τ`. -/
lemma final_arith {VO VN T τ : ℝ} (hT : 0 < T) (h : VO * VN ≤ T * T * τ / 4) :
    4 * (VO / T) * (VN / T) ≤ τ := by
  have h1 : 4 * (VO / T) * (VN / T) = 4 * (VO * VN) / (T * T) := by ring
  rw [h1, div_le_iff₀ (mul_pos hT hT)]
  linarith

/-- The two-sided inequality (the inequality of Theorem 5.4 of the paper) from the all-pairs
inequality (Proposition 5.2). -/
theorem twoSided_of_allPairs : AllPairsInequality → TwoSidedInequality := by
  intro hAllPairs ι _ _ g lam hlam τ hτ hinfl
  have h2n : (0 : ℝ) < 2 ^ Fintype.card ι := by positivity
  have hC : 0 ≤ (2 : ℝ) ^ Fintype.card ι * 2 ^ Fintype.card ι * τ / 4 :=
    div_nonneg (mul_nonneg (mul_nonneg h2n.le h2n.le) hτ) (by norm_num)
  -- every boundary is at most `2 ^ n * τ / 2`
  have hb : ∀ j, (bdry g j : ℝ) ≤ 2 ^ Fintype.card ι * τ / 2 := by
    intro j
    have h1 := two_mul_bdry g j
    have h2 := mul_le_mul_of_nonneg_left (hinfl j) h2n.le
    linarith
  -- the all-pairs inequality with the influence bound
  have hpairs : ∀ w : ι → ℝ, (∀ j, 0 < w j) →
      ∑ x ∈ univ.filter (fun x : Cube ι => g x = true),
        ∑ y ∈ univ.filter (fun y : Cube ι => g y = false),
          (∑ j ∈ diffSet x y, w j * lam x j * lam y j)⁻¹
        ≤ (2 : ℝ) ^ Fintype.card ι * 2 ^ Fintype.card ι * τ / 4 * ∑ j, (w j)⁻¹ := by
    intro w hw
    have h1 := hAllPairs ι g w hw lam hlam
    have h3 : ∑ j, (bdry g j : ℝ) / w j ≤ 2 ^ Fintype.card ι * τ / 2 * ∑ j, (w j)⁻¹ := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j _
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (hb j) (inv_pos.mpr (hw j)).le
    have h4 : (2 : ℝ) ^ Fintype.card ι * ∑ j, (bdry g j : ℝ) / w j
        ≤ 2 ^ Fintype.card ι * (2 ^ Fintype.card ι * τ / 2 * ∑ j, (w j)⁻¹) :=
      mul_le_mul_of_nonneg_left h3 h2n.le
    have h5 : (2 : ℝ) ^ Fintype.card ι * (2 ^ Fintype.card ι * τ / 2 * ∑ j, (w j)⁻¹)
        = 2 * ((2 : ℝ) ^ Fintype.card ι * 2 ^ Fintype.card ι * τ / 4 * ∑ j, (w j)⁻¹) := by
      ring
    linarith
  -- positivity of the denominators: the overlap lemma
  have hpos : ∀ x ∈ univ.filter (fun x : Cube ι => g x = true),
      ∀ y ∈ univ.filter (fun y : Cube ι => g y = false),
      ∀ w : ι → ℝ, (∀ j, 0 < w j) → 0 < ∑ j ∈ diffSet x y, w j * lam x j * lam y j := by
    intro x hx y hy w hw
    have hgx : g x = true := (Finset.mem_filter.mp hx).2
    have hgy : g y = false := (Finset.mem_filter.mp hy).2
    have hne : g x ≠ g y := by
      intro h
      rw [hgx, hgy] at h
      exact Bool.noConfusion h
    exact overlap_pos hne (hlam x) (hlam y) hw
  have key := abstract_cs (univ.filter fun x : Cube ι => g x = true)
    (univ.filter fun y : Cube ι => g y = false) lam lam
    (fun x j => (hlam x).1 j) (fun y j => (hlam y).1 j) diffSet
    ((2 : ℝ) ^ Fintype.card ι * 2 ^ Fintype.card ι * τ / 4) hC hpos hpairs
  exact final_arith h2n key

end AaronsonAmbainis

end
/- END UPSTREAM MODULE: AaronsonAmbainis.TwoSided.RemoveWeights -/

/- BEGIN UPSTREAM MODULE: AaronsonAmbainis.TwoSided.Main -/
section
/-!
# From the determinant inequality to the two-sided inequality: the three implications

* `AaronsonAmbainis.antipodal_of_det : DetInequality → AntipodalInequality`
  (the antipodal inequality, Theorem 4.3 of the paper, from the determinant inequality,
  Corollary 3.2);
* `AaronsonAmbainis.allPairs_of_antipodal : AntipodalInequality → AllPairsInequality`
  (the all-pairs inequality, Proposition 5.2, from the antipodal inequality);
* `AaronsonAmbainis.twoSided_of_allPairs : AllPairsInequality → TwoSidedInequality`
  (the two-sided inequality, Theorem 5.4, from the all-pairs inequality and the lemma that
  removes the weights, Lemma 5.3).
-/

end
/- END UPSTREAM MODULE: AaronsonAmbainis.TwoSided.Main -/

/- BEGIN UPSTREAM MODULE: AaronsonAmbainis.Level.Basic -/
section
/-!
# Mean, variance, mean absolute increments, rows: elementary facts

Helper lemmas about real functions on the cube, with no reference to the degree:

* the cube has `2 ^ n` points (`card_cube`, `sum_const_cube`, `four_pow_card`);
* the variance is nonnegative (`variance_nonneg`); it is `0` for a function with all values
  equal, in particular on the empty index type (`variance_eq_zero_of_const`,
  `variance_eq_zero_of_isEmpty`); the mean minimises the mean square distance to a constant
  (`variance_le_sq_dist`);
* `Inf_j(f)` is nonnegative and is one quarter of `E[(f(x) - f(x^j))^2]` (`inflR_nonneg`,
  `inflR_eq_quarter`);
* the mean absolute increments `L_j(f) = meanAbsIncr f j` are nonnegative (`meanAbsIncr_nonneg`)
  and satisfy `L_j(f)^2 ≤ 4 Inf_j(f)` (`meanAbsIncr_sq_le`; Section 2 of the paper);
* rows of a real function `f`: the cost of a row at `x` is at least `|f(x) - f(y)|` for every `y`
  (`abs_sub_le_rowSum`), so it is positive if `f` is not constant (`rowSum_pos`), and a number
  `K` that bounds the costs of rows at all points is positive if `Var(f) > 0` (`cost_pos`); every
  function has a row at every point (`exists_rows_cost`; Remark 7.12 of the paper);
* a row `a` of cost at most `K` at `u` gives `|f(u) - f(u^j)| ≤ a_j` and
  `∑_j |f(u) - f(u^j)| ≤ K` (`abs_incr_le_of_rows`, `sum_abs_incr_le_of_rows`); a bound `G` for
  these sums at all points `u` gives `L(f) = ∑_j L_j(f) ≤ G` (`sum_meanAbsIncr_le`); so
  `L(f) ≤ K` for a function with rows of cost at most `K` (`sum_meanAbsIncr_le_cost`).
-/

namespace AaronsonAmbainis
namespace Level

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The cube has `2 ^ n` points. -/
theorem card_cube : ((Fintype.card (Cube ι) : ℕ) : ℝ) = 2 ^ Fintype.card ι := by
  have h : Fintype.card (Cube ι) = 2 ^ Fintype.card ι := by
    rw [Fintype.card_fun, Fintype.card_bool]
  rw [h]
  push_cast
  rfl

/-- Sum of a constant over the cube. -/
theorem sum_const_cube (c : ℝ) : ∑ _x : Cube ι, c = 2 ^ Fintype.card ι * c := by
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_cube]

omit [DecidableEq ι] in
/-- `4 ^ n = 4 · 4 ^ (n - 1)` for `n ≥ 1`. -/
theorem four_pow_card [Nonempty ι] :
    (4 : ℝ) ^ Fintype.card ι = 4 * 4 ^ (Fintype.card ι - 1) := by
  have hn : 0 < Fintype.card ι := Fintype.card_pos
  rw [← pow_succ']
  congr 1
  omega

/-! ### Mean and variance -/

theorem variance_nonneg (f : Cube ι → ℝ) : 0 ≤ variance f := by
  unfold variance
  exact div_nonneg (Finset.sum_nonneg (fun x _ => sq_nonneg _)) (by positivity)

/-- A function with all values equal has variance zero. -/
theorem variance_eq_zero_of_const (f : Cube ι → ℝ) (h : ∀ x y, f x = f y) : variance f = 0 := by
  have hm : ∀ x, f x = mean f := by
    intro x
    unfold mean
    rw [Finset.sum_congr rfl (fun y _ => h y x), sum_const_cube,
      mul_div_cancel_left₀ _ (by positivity)]
  unfold variance
  rw [Finset.sum_eq_zero (fun x _ => by rw [hm x, sub_self]; norm_num), zero_div]

/-- On the empty index type every variance is `0`. -/
theorem variance_eq_zero_of_isEmpty [IsEmpty ι] (f : Cube ι → ℝ) : variance f = 0 :=
  variance_eq_zero_of_const f (fun x y => congrArg f (Subsingleton.elim x y))

/-- `E (f - E f) = 0`, unnormalised. -/
theorem sum_sub_mean (f : Cube ι → ℝ) : ∑ x, (f x - mean f) = 0 := by
  rw [Finset.sum_sub_distrib, sum_const_cube]
  unfold mean
  rw [mul_div_cancel₀ _ (by positivity), sub_self]

/-- The mean minimises the mean square distance to a constant. -/
theorem variance_le_sq_dist (f : Cube ι → ℝ) (c : ℝ) :
    variance f ≤ (∑ x, (f x - c) ^ 2) / 2 ^ Fintype.card ι := by
  have hpos : (0 : ℝ) < 2 ^ Fintype.card ι := by positivity
  have h1 : ∑ x, (f x - c) ^ 2
      = ∑ x, (f x - mean f) ^ 2 + 2 * (mean f - c) * ∑ x, (f x - mean f)
        + ∑ _x : Cube ι, (mean f - c) ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    ring
  have h2 : 0 ≤ ∑ _x : Cube ι, (mean f - c) ^ 2 := Finset.sum_nonneg (fun x _ => sq_nonneg _)
  unfold variance
  refine div_le_div_of_nonneg_right ?_ hpos.le
  rw [h1, sum_sub_mean, mul_zero, add_zero]
  exact le_add_of_nonneg_right h2

/-! ### Influences and mean absolute increments -/

theorem inflR_nonneg (f : Cube ι → ℝ) (j : ι) : 0 ≤ inflR f j := by
  unfold inflR
  exact div_nonneg (Finset.sum_nonneg (fun x _ => sq_nonneg _)) (by positivity)

/-- `inflR` is one quarter of the unnormalised L2 influence `E[(f(x) - f(x^j))^2]`. -/
theorem inflR_eq_quarter (f : Cube ι → ℝ) (j : ι) :
    inflR f j = (∑ x, (f x - f (flipSet x {j})) ^ 2) / 2 ^ Fintype.card ι / 4 := by
  have h : ∀ x : Cube ι,
      ((f x - f (flipSet x {j})) / 2) ^ 2 = (f x - f (flipSet x {j})) ^ 2 / 4 :=
    fun x => by ring
  simp only [inflR, h]
  rw [← Finset.sum_div, div_right_comm]

theorem meanAbsIncr_nonneg (f : Cube ι → ℝ) (j : ι) : 0 ≤ meanAbsIncr f j :=
  div_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) (by positivity)

/-- `L_j(f)^2 ≤ 4 Inf_j(f)` (the Cauchy–Schwarz inequality; Section 2 of the paper). -/
theorem meanAbsIncr_sq_le (f : Cube ι → ℝ) (j : ι) : meanAbsIncr f j ^ 2 ≤ 4 * inflR f j := by
  have h2 : (0 : ℝ) < 2 ^ Fintype.card ι := by positivity
  have h := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Cube ι)))
    (f := fun x => |f x - f (flipSet x {j})|)
  simp only [sq_abs] at h
  rw [Finset.card_univ, card_cube] at h
  have e : 4 * inflR f j
      = (2 ^ Fintype.card ι * ∑ x, (f x - f (flipSet x {j})) ^ 2) / (2 ^ Fintype.card ι) ^ 2 := by
    rw [inflR_eq_quarter]
    field_simp
  unfold meanAbsIncr
  rw [e, div_pow]
  exact div_le_div_of_nonneg_right h (by positivity)

/-! ### Rows of a real function -/

omit [DecidableEq ι] in
/-- The cost of a row of `f` at `x` is at least `|f(x) - f(y)|`, for every `y`. -/
theorem abs_sub_le_rowSum {f : Cube ι → ℝ} {a : Cube ι → ι → ℝ} (ha : ∀ x j, 0 ≤ a x j)
    (hrow : ∀ x y, |f x - f y| ≤ ∑ j ∈ diffSet x y, a x j) (x y : Cube ι) :
    |f x - f y| ≤ ∑ j, a x j :=
  le_trans (hrow x y)
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun j _ _ => ha x j))

omit [DecidableEq ι] in
/-- A row at `x` has positive cost if `f` takes another value somewhere. -/
theorem rowSum_pos {f : Cube ι → ℝ} {a : Cube ι → ι → ℝ} (ha : ∀ x j, 0 ≤ a x j)
    (hrow : ∀ x y, |f x - f y| ≤ ∑ j ∈ diffSet x y, a x j) {x y : Cube ι} (hxy : f x ≠ f y) :
    0 < ∑ j, a x j :=
  lt_of_lt_of_le (abs_pos.mpr (sub_ne_zero.mpr hxy)) (abs_sub_le_rowSum ha hrow x y)

/-- If `f` has a row of cost at most `K` at every point and `Var(f) > 0`, then `K > 0`. -/
theorem cost_pos {f : Cube ι → ℝ} {a : Cube ι → ι → ℝ} {K : ℝ} (ha : ∀ x j, 0 ≤ a x j)
    (hsum : ∀ x, ∑ j, a x j ≤ K) (hrow : ∀ x y, |f x - f y| ≤ ∑ j ∈ diffSet x y, a x j)
    (hvar : 0 < variance f) : 0 < K := by
  by_contra hK
  have hconst : ∀ x y, f x = f y := by
    intro x y
    by_contra hxy
    exact hK (lt_of_lt_of_le (rowSum_pos ha hrow hxy) (hsum x))
  rw [variance_eq_zero_of_const f hconst] at hvar
  exact lt_irrefl 0 hvar

/-- A row at `u` bounds each increment of `f` at `u`: `|f(u) - f(u^j)| ≤ a u j`. -/
theorem abs_incr_le_of_rows {f : Cube ι → ℝ} {a : Cube ι → ι → ℝ}
    (hrow : ∀ x y, |f x - f y| ≤ ∑ j ∈ diffSet x y, a x j) (u : Cube ι) (j : ι) :
    |f u - f (flipSet u {j})| ≤ a u j := by
  have h := hrow u (flipSet u {j})
  rwa [diffSet_flipSet, Finset.sum_singleton] at h

/-- A row at `u` of cost at most `K` bounds the sum of the increments of `f` at `u`:
`∑_j |f(u) - f(u^j)| ≤ K`. -/
theorem sum_abs_incr_le_of_rows {f : Cube ι → ℝ} {a : Cube ι → ι → ℝ} {K : ℝ}
    (hsum : ∀ x, ∑ j, a x j ≤ K) (hrow : ∀ x y, |f x - f y| ≤ ∑ j ∈ diffSet x y, a x j)
    (u : Cube ι) : ∑ j, |f u - f (flipSet u {j})| ≤ K :=
  le_trans (Finset.sum_le_sum fun j _ => abs_incr_le_of_rows hrow u j) (hsum u)

/-- If `∑_j |f(u) - f(u^j)| ≤ G` at every point `u`, then `L(f) = ∑_j L_j(f) ≤ G`. -/
theorem sum_meanAbsIncr_le (f : Cube ι → ℝ) {G : ℝ}
    (hG : ∀ u, ∑ j, |f u - f (flipSet u {j})| ≤ G) : ∑ j, meanAbsIncr f j ≤ G := by
  have h2 : (0 : ℝ) < 2 ^ Fintype.card ι := by positivity
  unfold meanAbsIncr
  rw [← Finset.sum_div, div_le_iff₀ h2, Finset.sum_comm]
  calc ∑ x, ∑ j, |f x - f (flipSet x {j})| ≤ ∑ _x : Cube ι, G :=
        Finset.sum_le_sum (fun x _ => hG x)
    _ = G * 2 ^ Fintype.card ι := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_cube, mul_comm]

/-- The sum `L(f)` of the mean absolute increments of a function with rows of cost at most `K`
is at most `K`. -/
theorem sum_meanAbsIncr_le_cost {f : Cube ι → ℝ} {a : Cube ι → ι → ℝ} {K : ℝ}
    (hsum : ∀ x, ∑ j, a x j ≤ K) (hrow : ∀ x y, |f x - f y| ≤ ∑ j ∈ diffSet x y, a x j) :
    ∑ j, meanAbsIncr f j ≤ K :=
  sum_meanAbsIncr_le f (sum_abs_incr_le_of_rows hsum hrow)

/-- Every real function on the cube has a row at every point, of cost at most some `K`: the
hypotheses on rows can be met for every function (Remark 7.12 of the paper). -/
theorem exists_rows_cost (f : Cube ι → ℝ) :
    ∃ (K : ℝ) (a : Cube ι → ι → ℝ), (∀ x j, 0 ≤ a x j) ∧ (∀ x, ∑ j, a x j ≤ K) ∧
      ∀ x y, |f x - f y| ≤ ∑ j ∈ diffSet x y, a x j := by
  have hnn : ∀ x : Cube ι, 0 ≤ ∑ z, |f x - f z| := fun x =>
    Finset.sum_nonneg (fun z _ => abs_nonneg _)
  refine ⟨∑ x : Cube ι, ∑ _j : ι, ∑ z, |f x - f z|, fun x _ => ∑ z, |f x - f z|,
    fun x _ => hnn x, fun x => ?_, fun x y => ?_⟩
  · exact Finset.single_le_sum (f := fun x : Cube ι => ∑ _j : ι, ∑ z, |f x - f z|)
      (fun x _ => Finset.sum_nonneg (fun _ _ => hnn x)) (Finset.mem_univ x)
  · by_cases hxy : x = y
    · rw [hxy, sub_self, abs_zero]
      exact Finset.sum_nonneg (fun _ _ => hnn y)
    · obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
        by_contra hcon
        exact hxy (funext (fun i => by_contra (fun h => hcon ⟨i, h⟩)))
      have hmem : i ∈ diffSet x y := mem_diffSet.mpr hi
      calc |f x - f y| ≤ ∑ z, |f x - f z| :=
            Finset.single_le_sum (f := fun z => |f x - f z|) (fun z _ => abs_nonneg _)
              (Finset.mem_univ y)
        _ ≤ ∑ _j ∈ diffSet x y, ∑ z, |f x - f z| :=
            Finset.single_le_sum (f := fun _ : ι => ∑ z, |f x - f z|) (fun _ _ => hnn x) hmem

end Level
end AaronsonAmbainis

end
/- END UPSTREAM MODULE: AaronsonAmbainis.Level.Basic -/

/- BEGIN UPSTREAM MODULE: AaronsonAmbainis.Level.Integral -/
section
/-!
# Integration over the level

Real-variable lemmas with no cube in them. The main statement is `level_integration`: an
inequality between a combination of the functions `t ↦ (u - t)⁺ (t - v)⁺` and a combination of
indicators of intervals `[p, q)`, valid at every level `t`, can be integrated over `t`:
`∫ (u - t)⁺ (t - v)⁺ dt = ((u - v)⁺)^3 / 6` and `∫ 1_{[p,q)}(t) dt = (q - p)⁺` (Lemma 7.3 (i)
and (ii) of the paper).
-/

namespace AaronsonAmbainis
namespace Level

open Finset

/-- `∫_v^u (u - t)(t - v) dt = (u - v)^3 / 6`. -/
lemma integral_quad (v u : ℝ) : ∫ t in v..u, (u - t) * (t - v) = (u - v) ^ 3 / 6 := by
  have hd : ∀ t ∈ Set.uIcc v u, HasDerivAt
      (fun t : ℝ => -1 / 3 * t ^ 3 + (u + v) / 2 * t ^ 2 - u * v * t) ((u - t) * (t - v)) t := by
    intro t _
    have h3 : HasDerivAt (fun t : ℝ => t ^ 3) (3 * t ^ 2) t := by
      simpa using hasDerivAt_pow 3 t
    have h2 : HasDerivAt (fun t : ℝ => t ^ 2) (2 * t) t := by
      simpa using hasDerivAt_pow 2 t
    have h1 : HasDerivAt (fun t : ℝ => t) 1 t := hasDerivAt_id' t
    have h : HasDerivAt (fun t : ℝ => -1 / 3 * t ^ 3 + (u + v) / 2 * t ^ 2 - u * v * t)
        (-1 / 3 * (3 * t ^ 2) + (u + v) / 2 * (2 * t) - u * v * 1) t :=
      ((h3.const_mul (-1 / 3)).add (h2.const_mul ((u + v) / 2))).sub (h1.const_mul (u * v))
    convert h using 1
    ring
  have hc : Continuous fun t : ℝ => (u - t) * (t - v) := by fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable _ _)]
  ring

/-- `∫_a^b (u - t)⁺ (t - v)⁺ dt = ((u - v)⁺)^3 / 6` when `a ≤ v` and `u ≤ b`
(Lemma 7.3 (i) of the paper). -/
lemma integral_posParts {a b u v : ℝ} (hub : u ≤ b) (hav : a ≤ v) :
    ∫ t in a..b, max (u - t) 0 * max (t - v) 0 = max (u - v) 0 ^ 3 / 6 := by
  have hc : Continuous fun t : ℝ => max (u - t) 0 * max (t - v) 0 := by fun_prop
  rcases le_or_gt u v with h | h
  · have h0 : ∀ t : ℝ, max (u - t) 0 * max (t - v) 0 = 0 := by
      intro t
      rcases le_or_gt u t with ht | ht
      · rw [max_eq_right (by linarith : u - t ≤ 0), zero_mul]
      · rw [max_eq_right (by linarith : t - v ≤ 0), mul_zero]
    simp only [h0]
    rw [intervalIntegral.integral_zero, max_eq_right (by linarith : u - v ≤ 0)]
    norm_num
  · have e1 : ∫ t in a..v, max (u - t) 0 * max (t - v) 0 = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)),
        intervalIntegral.integral_zero]
      intro t ht
      rw [Set.uIcc_of_le hav] at ht
      show max (u - t) 0 * max (t - v) 0 = 0
      rw [max_eq_right (by linarith [ht.2] : t - v ≤ 0), mul_zero]
    have e2 : ∫ t in v..u, max (u - t) 0 * max (t - v) 0 = (u - v) ^ 3 / 6 := by
      rw [intervalIntegral.integral_congr (g := fun t => (u - t) * (t - v)), integral_quad]
      intro t ht
      rw [Set.uIcc_of_le h.le] at ht
      show max (u - t) 0 * max (t - v) 0 = (u - t) * (t - v)
      rw [max_eq_left (by linarith [ht.2] : 0 ≤ u - t),
        max_eq_left (by linarith [ht.1] : 0 ≤ t - v)]
    have e3 : ∫ t in u..b, max (u - t) 0 * max (t - v) 0 = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)),
        intervalIntegral.integral_zero]
      intro t ht
      rw [Set.uIcc_of_le hub] at ht
      show max (u - t) 0 * max (t - v) 0 = 0
      rw [max_eq_right (by linarith [ht.1] : u - t ≤ 0), zero_mul]
    have s1 := intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable a v) (hc.intervalIntegrable (μ := MeasureTheory.volume) v b)
    have s2 := intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable v u) (hc.intervalIntegrable (μ := MeasureTheory.volume) u b)
    rw [← s1, ← s2, e1, e2, e3, max_eq_left (by linarith : 0 ≤ u - v)]
    ring

/-- The step function `1_{c ≤ t}`. -/
noncomputable def stp (c t : ℝ) : ℝ := if c ≤ t then 1 else 0

lemma stp_mono (c : ℝ) : Monotone (stp c) := by
  intro s t hst
  unfold stp
  by_cases h : c ≤ s
  · rw [if_pos h, if_pos (h.trans hst)]
  · rw [if_neg h]
    split_ifs <;> norm_num

lemma stp_intervalIntegrable (c a b : ℝ) :
    IntervalIntegrable (stp c) MeasureTheory.volume a b :=
  (stp_mono c).intervalIntegrable

/-- `∫_a^b 1_{c ≤ t} dt = b - c` for `c` in `[a, b]` (this gives Lemma 7.3 (ii) of the paper). -/
lemma integral_stp {a b c : ℝ} (hac : a ≤ c) (hcb : c ≤ b) : ∫ t in a..b, stp c t = b - c := by
  have e1 : ∫ t in a..c, stp c t = 0 := by
    rw [intervalIntegral.integral_congr_Ioo_of_le hac (g := fun _ => (0 : ℝ)),
      intervalIntegral.integral_zero]
    intro t ht
    show stp c t = 0
    unfold stp
    rw [if_neg (not_le.mpr ht.2)]
  have e2 : ∫ t in c..b, stp c t = b - c := by
    rw [intervalIntegral.integral_congr (g := fun _ => (1 : ℝ)), integral_one]
    intro t ht
    rw [Set.uIcc_of_le hcb] at ht
    show stp c t = 1
    unfold stp
    rw [if_pos ht.1]
  rw [← intervalIntegral.integral_add_adjacent_intervals (stp_intervalIntegrable c a c)
    (stp_intervalIntegrable c c b), e1, e2, zero_add]

/-- The indicator of `[p, q)` as a difference of two step functions. -/
lemma ind_eq_stp (p q t : ℝ) :
    (if p ≤ t ∧ t < q then (1 : ℝ) else 0) = stp p t - stp (max p q) t := by
  unfold stp
  by_cases h1 : p ≤ t
  · by_cases h2 : t < q
    · have h3 : ¬ max p q ≤ t := fun h => absurd ((le_max_right p q).trans h) (not_le.mpr h2)
      rw [if_pos ⟨h1, h2⟩, if_pos h1, if_neg h3, sub_zero]
    · rw [if_neg (fun h => h2 h.2), if_pos h1, if_pos (max_le h1 (not_lt.mp h2)), sub_self]
  · rw [if_neg (fun h => h1 h.1), if_neg h1,
      if_neg (fun h => h1 ((le_max_left p q).trans h)), sub_self]

/-- **Integration over the level.** If
`∑_i c_i (u_i - t)⁺ (t - v_i)⁺ ≤ ∑_k d_k 1_{[p_k, q_k)}(t)` for every real `t`, then
`∑_i c_i ((u_i - v_i)⁺)^3 / 6 ≤ ∑_k d_k (q_k - p_k)⁺`. No sign condition on `c`, `d`. -/
theorem level_integration {α β : Type*} (s : Finset α) (r : Finset β)
    (c u v : α → ℝ) (d p q : β → ℝ)
    (h : ∀ t : ℝ, ∑ i ∈ s, c i * (max (u i - t) 0 * max (t - v i) 0)
        ≤ ∑ k ∈ r, d k * (if p k ≤ t ∧ t < q k then (1 : ℝ) else 0)) :
    ∑ i ∈ s, c i * (max (u i - v i) 0 ^ 3 / 6) ≤ ∑ k ∈ r, d k * max (q k - p k) 0 := by
  -- a bound `R` for all the levels that occur
  obtain ⟨R, hRs, hRr⟩ : ∃ R : ℝ, (∀ i ∈ s, |u i| ≤ R ∧ |v i| ≤ R) ∧
      (∀ k ∈ r, |p k| ≤ R ∧ |q k| ≤ R) := by
    refine ⟨∑ i ∈ s, (|u i| + |v i|) + ∑ k ∈ r, (|p k| + |q k|), ?_, ?_⟩
    · intro i hi
      have h1 : |u i| + |v i| ≤ ∑ i ∈ s, (|u i| + |v i|) :=
        Finset.single_le_sum (f := fun i => |u i| + |v i|)
          (fun i _ => add_nonneg (abs_nonneg _) (abs_nonneg _)) hi
      have h2 : 0 ≤ ∑ k ∈ r, (|p k| + |q k|) :=
        Finset.sum_nonneg (fun k _ => add_nonneg (abs_nonneg _) (abs_nonneg _))
      constructor <;> linarith [abs_nonneg (u i), abs_nonneg (v i)]
    · intro k hk
      have h1 : |p k| + |q k| ≤ ∑ k ∈ r, (|p k| + |q k|) :=
        Finset.single_le_sum (f := fun k => |p k| + |q k|)
          (fun k _ => add_nonneg (abs_nonneg _) (abs_nonneg _)) hk
      have h2 : 0 ≤ ∑ i ∈ s, (|u i| + |v i|) :=
        Finset.sum_nonneg (fun i _ => add_nonneg (abs_nonneg _) (abs_nonneg _))
      constructor <;> linarith [abs_nonneg (p k), abs_nonneg (q k)]
  -- we integrate over `[-R', R']` with `R' = |R|`, so that `-R' ≤ R'` also if `s`, `r` are empty
  have hR0 : -|R| ≤ |R| := by linarith [abs_nonneg R]
  have hRR : R ≤ |R| := le_abs_self R
  -- the left side
  have hLc : ∀ i, Continuous fun t : ℝ => c i * (max (u i - t) 0 * max (t - v i) 0) := by
    intro i
    fun_prop
  have hL : ∫ t in (-|R|)..|R|, ∑ i ∈ s, c i * (max (u i - t) 0 * max (t - v i) 0)
      = ∑ i ∈ s, c i * (max (u i - v i) 0 ^ 3 / 6) := by
    rw [intervalIntegral.integral_finsetSum (fun i _ => (hLc i).intervalIntegrable _ _)]
    apply Finset.sum_congr rfl
    intro i hi
    have hu := abs_le.mp ((hRs i hi).1.trans hRR)
    have hv := abs_le.mp ((hRs i hi).2.trans hRR)
    rw [intervalIntegral.integral_const_mul, integral_posParts hu.2 hv.1]
  have hLi : IntervalIntegrable
      (fun t : ℝ => ∑ i ∈ s, c i * (max (u i - t) 0 * max (t - v i) 0))
      MeasureTheory.volume (-|R|) |R| := by
    have hcont : Continuous fun t : ℝ => ∑ i ∈ s, c i * (max (u i - t) 0 * max (t - v i) 0) :=
      continuous_finsetSum s (fun i _ => hLc i)
    exact hcont.intervalIntegrable _ _
  -- the right side
  have hstep : ∀ k, IntervalIntegrable
      (fun t : ℝ => d k * (if p k ≤ t ∧ t < q k then (1 : ℝ) else 0))
      MeasureTheory.volume (-|R|) |R| := by
    intro k
    simp only [ind_eq_stp]
    exact ((stp_intervalIntegrable (p k) _ _).sub
      (stp_intervalIntegrable (max (p k) (q k)) _ _)).const_mul (d k)
  have hRint : ∫ t in (-|R|)..|R|, ∑ k ∈ r, d k * (if p k ≤ t ∧ t < q k then (1 : ℝ) else 0)
      = ∑ k ∈ r, d k * max (q k - p k) 0 := by
    rw [intervalIntegral.integral_finsetSum (fun k _ => hstep k)]
    apply Finset.sum_congr rfl
    intro k hk
    have hp := abs_le.mp ((hRr k hk).1.trans hRR)
    have hq := abs_le.mp ((hRr k hk).2.trans hRR)
    have hm1 : -|R| ≤ max (p k) (q k) := le_trans hp.1 (le_max_left _ _)
    have hm2 : max (p k) (q k) ≤ |R| := max_le hp.2 hq.2
    rw [intervalIntegral.integral_const_mul]
    simp only [ind_eq_stp]
    rw [intervalIntegral.integral_sub (stp_intervalIntegrable _ _ _)
      (stp_intervalIntegrable _ _ _), integral_stp hp.1 hp.2, integral_stp hm1 hm2]
    congr 1
    rcases le_total (p k) (q k) with hpq | hpq
    · rw [max_eq_right hpq, max_eq_left (by linarith : 0 ≤ q k - p k)]
      ring
    · rw [max_eq_left hpq, max_eq_right (by linarith : q k - p k ≤ 0)]
      ring
  have hRi : IntervalIntegrable
      (fun t : ℝ => ∑ k ∈ r, d k * (if p k ≤ t ∧ t < q k then (1 : ℝ) else 0))
      MeasureTheory.volume (-|R|) |R| := by
    have h1 := IntervalIntegrable.sum r
      (f := fun k (t : ℝ) => d k * (if p k ≤ t ∧ t < q k then (1 : ℝ) else 0))
      (μ := MeasureTheory.volume) (a := -|R|) (b := |R|) (fun k _ => hstep k)
    have e : (∑ k ∈ r, fun t : ℝ => d k * (if p k ≤ t ∧ t < q k then (1 : ℝ) else 0))
        = fun t : ℝ => ∑ k ∈ r, d k * (if p k ≤ t ∧ t < q k then (1 : ℝ) else 0) := by
      funext t
      rw [Finset.sum_apply]
    rw [e] at h1
    exact h1
  have hmono := intervalIntegral.integral_mono_on hR0 hLi hRi (fun t _ => h t)
  rw [hL, hRint] at hmono
  exact hmono

end Level
end AaronsonAmbainis

end
/- END UPSTREAM MODULE: AaronsonAmbainis.Level.Integral -/

/- BEGIN UPSTREAM MODULE: AaronsonAmbainis.Level.Rows -/
section
/-!
# Level functions and their rows

For a real function `f` on the cube and a real number `t`, `lev f t` is the level function
`g_t = 1_{f > t}`. If `a x` is a row of `f` at `x`, then `levRow f a t x`, which is
`a x / |f x - t|` (and the all-ones vector when `f x = t`), is a row of `g_t` at `x`
(`isRow_levRow`; the cases `f x ≠ t` and `f x = t` are parts (iii) and (i) of Lemma 2.4 of the
paper). These are the rows `λ^{t,x}` of Section 7.1 of the paper.
-/

namespace AaronsonAmbainis
namespace Level

open Finset

/-- The level function `g_t = 1_{f > t}`. -/
noncomputable def lev {ι : Type*} (f : Cube ι → ℝ) (t : ℝ) : Cube ι → Bool :=
  fun x => decide (t < f x)

/-- The row of `g_t` at `x` built from the row `a x` of `f`: `a x / |f x - t|`
(and the all-ones vector when `f x = t`). -/
noncomputable def levRow {ι : Type*} (f : Cube ι → ℝ) (a : Cube ι → ι → ℝ) (t : ℝ) :
    Cube ι → ι → ℝ :=
  fun x j => if f x = t then 1 else a x j / |f x - t|

/-- If `g_t` separates `x` and `y` then `t` lies weakly between `f x` and `f y`. -/
theorem abs_sub_le_of_lev_ne {ι : Type*} {f : Cube ι → ℝ} {t : ℝ} {x y : Cube ι}
    (h : lev f t y ≠ lev f t x) : |f x - t| ≤ |f x - f y| := by
  unfold lev at h
  by_cases h1 : t < f x <;> by_cases h2 : t < f y
  · simp [h1, h2] at h
  · rw [abs_of_pos (sub_pos.mpr h1)]
    exact le_trans (by linarith) (le_abs_self _)
  · rw [abs_sub_comm (f x) t, abs_sub_comm (f x) (f y), abs_of_nonneg (by linarith)]
    exact le_trans (by linarith) (le_abs_self _)
  · simp [h1, h2] at h

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `levRow f a t x` is a row of `g_t` at `x`. -/
theorem isRow_levRow {f : Cube ι → ℝ} {a : Cube ι → ι → ℝ} (ha : ∀ x j, 0 ≤ a x j)
    (hrow : ∀ x y, |f x - f y| ≤ ∑ j ∈ diffSet x y, a x j) (t : ℝ) (x : Cube ι) :
    IsRow (lev f t) x (levRow f a t x) := by
  refine ⟨fun j => ?_, fun S hS => ?_⟩
  · unfold levRow
    split_ifs
    · exact zero_le_one
    · exact div_nonneg (ha x j) (abs_nonneg _)
  · by_cases hx : f x = t
    · have hne : S.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        rintro rfl
        rw [flipSet_empty] at hS
        exact hS rfl
      have h1 : ∀ j ∈ S, levRow f a t x j = 1 := fun j _ => by simp [levRow, hx]
      rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, mul_one]
      exact_mod_cast hne.card_pos
    · have hpos : 0 < |f x - t| := abs_pos.mpr (sub_ne_zero.mpr hx)
      have h1 : |f x - t| ≤ ∑ j ∈ S, a x j := by
        have h2 := hrow x (flipSet x S)
        rw [diffSet_flipSet] at h2
        exact le_trans (abs_sub_le_of_lev_ne hS) h2
      have h3 : ∀ j ∈ S, levRow f a t x j = a x j / |f x - t| :=
        fun j _ => by simp [levRow, hx]
      rw [Finset.sum_congr rfl h3, ← Finset.sum_div, le_div_iff₀ hpos, one_mul]
      exact h1

end Level
end AaronsonAmbainis

end
/- END UPSTREAM MODULE: AaronsonAmbainis.Level.Rows -/

/- BEGIN UPSTREAM MODULE: AaronsonAmbainis.Level.AllPairs -/
section
/-!
# The all-pairs inequality at one level

Let `f` be a real function on the cube with a row `a x` at every point `x`, and let `t` be a
real number. The all-pairs inequality (Proposition 5.2 of the paper), applied to the level
function `g_t = 1_{f > t}` with the rows `a x / |f x - t|` (`levRow`, Lemma 2.4 (iii) of the
paper), reads

`2 ∑_x ∑_y (f x - t)⁺ (t - f y)⁺ / s_xy ≤ 2^n ∑_j b_j(g_t) / w_j`,
`s_xy = ∑_{j ∈ Δ(x,y)} w_j a^x_j a^y_j`

(`level_allPairs`; Lemma 7.2 of the paper, multiplied by `2`), for every real `t`. Also:
`s_xy > 0` when `f y < f x` (`pairSum_pos`; Lemma 7.1), and `b_j(g_t)` is the number of points
`x` with `f(x^j) ≤ t < f(x)` (`bdry_lev`).
-/

namespace AaronsonAmbainis
namespace Level

open Finset

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- The overlap sum of the level rows at a point above the level and a point below it
(Lemma 7.1 (i) of the paper). -/
lemma sum_levRow (f : Cube ι → ℝ) (a : Cube ι → ι → ℝ) (w : ι → ℝ) {t : ℝ} {x y : Cube ι}
    (hx : t < f x) (hy : f y < t) :
    ∑ j ∈ diffSet x y, w j * levRow f a t x j * levRow f a t y j
      = (∑ j ∈ diffSet x y, w j * a x j * a y j) / ((f x - t) * (t - f y)) := by
  have hxne : f x ≠ t := ne_of_gt hx
  have hyne : f y ≠ t := ne_of_lt hy
  have h1 : f x - t ≠ 0 := sub_ne_zero.mpr hxne
  have h2 : t - f y ≠ 0 := sub_ne_zero.mpr hyne.symm
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  have e1 : levRow f a t x j = a x j / (f x - t) := by
    show (if f x = t then 1 else a x j / |f x - t|) = a x j / (f x - t)
    rw [if_neg hxne, abs_of_pos (sub_pos.mpr hx)]
  have e2 : levRow f a t y j = a y j / (t - f y) := by
    show (if f y = t then 1 else a y j / |f y - t|) = a y j / (t - f y)
    rw [if_neg hyne, abs_of_neg (sub_neg.mpr hy), neg_sub]
  rw [e1, e2]
  field_simp

/-- Rows at two points with different values overlap on the difference set: `s_xy > 0`
(Lemma 7.1 (ii) of the paper). -/
theorem pairSum_pos {f : Cube ι → ℝ} {a : Cube ι → ι → ℝ} (ha : ∀ x j, 0 ≤ a x j)
    (hrow : ∀ x y, |f x - f y| ≤ ∑ j ∈ diffSet x y, a x j) {w : ι → ℝ} (hw : ∀ j, 0 < w j)
    {x y : Cube ι} (hxy : f y < f x) :
    0 < ∑ j ∈ diffSet x y, w j * a x j * a y j := by
  have hx : (f x + f y) / 2 < f x := by linarith
  have hy : f y < (f x + f y) / 2 := by linarith
  have hne : lev f ((f x + f y) / 2) x ≠ lev f ((f x + f y) / 2) y := by
    simp [lev, hx, not_lt.mpr hy.le]
  have h := overlap_pos hne (isRow_levRow ha hrow ((f x + f y) / 2) x)
    (isRow_levRow ha hrow ((f x + f y) / 2) y) hw
  rw [sum_levRow f a w hx hy] at h
  have hden : 0 < (f x - (f x + f y) / 2) * ((f x + f y) / 2 - f y) :=
    mul_pos (by linarith) (by linarith)
  by_contra hcon
  have h0 : (∑ j ∈ diffSet x y, w j * a x j * a y j)
      / ((f x - (f x + f y) / 2) * ((f x + f y) / 2 - f y)) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (not_lt.mp hcon) hden.le
  linarith

/-- The all-pairs inequality at the level `t` (Lemma 7.2 of the paper, multiplied by `2`), from
the all-pairs inequality for Boolean functions. -/
theorem level_allPairs (hAllPairs : AllPairsInequality) (f : Cube ι → ℝ) (a : Cube ι → ι → ℝ)
    (ha : ∀ x j, 0 ≤ a x j) (hrow : ∀ x y, |f x - f y| ≤ ∑ j ∈ diffSet x y, a x j)
    (w : ι → ℝ) (hw : ∀ j, 0 < w j) (t : ℝ) :
    2 * ∑ x, ∑ y, max (f x - t) 0 * max (t - f y) 0
          * (∑ j ∈ diffSet x y, w j * a x j * a y j)⁻¹
      ≤ 2 ^ Fintype.card ι * ∑ j, (bdry (lev f t) j : ℝ) / w j := by
  have hrows := isRow_levRow ha hrow t
  have h := hAllPairs ι (lev f t) w hw (levRow f a t) hrows
  refine le_trans ?_ h
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  rw [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : t < f x
  · have hlx : lev f t x = true := by simp [lev, hx]
    rw [if_pos hlx, Finset.sum_filter]
    apply Finset.sum_le_sum
    intro y _
    by_cases hy : t < f y
    · have hly : ¬ lev f t y = false := by simp [lev, hy]
      rw [if_neg hly, max_eq_right (by linarith : t - f y ≤ 0), mul_zero, zero_mul]
    · have hly : lev f t y = false := by simp [lev, hy]
      rw [if_pos hly]
      rcases lt_or_eq_of_le (not_lt.mp hy) with hyt | hyt
      · rw [sum_levRow f a w hx hyt, inv_div, max_eq_left (by linarith : 0 ≤ f x - t),
          max_eq_left (by linarith : 0 ≤ t - f y), div_eq_mul_inv]
      · rw [max_eq_right (by linarith : t - f y ≤ 0), mul_zero, zero_mul]
        exact inv_nonneg.mpr (Finset.sum_nonneg fun j _ =>
          mul_nonneg (mul_nonneg (hw j).le ((hrows x).1 j)) ((hrows y).1 j))
  · have hlx : ¬ lev f t x = true := by simp [lev, hx]
    rw [if_neg hlx]
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro y _
    rw [max_eq_right (by linarith [not_lt.mp hx] : f x - t ≤ 0), zero_mul, zero_mul]

/-- `b_j(g_t)` is the number of points `x` with `f(x^j) ≤ t < f(x)`. -/
lemma bdry_lev (f : Cube ι → ℝ) (t : ℝ) (j : ι) :
    (bdry (lev f t) j : ℝ)
      = ∑ x, if f (flipSet x {j}) ≤ t ∧ t < f x then (1 : ℝ) else 0 := by
  unfold bdry
  rw [Finset.natCast_card_filter]
  apply Finset.sum_congr rfl
  intro x _
  apply if_congr _ rfl rfl
  simp only [lev, decide_eq_true_eq, decide_eq_false_iff_not, not_lt]
  exact and_comm

end Level
end AaronsonAmbainis

end
/- END UPSTREAM MODULE: AaronsonAmbainis.Level.AllPairs -/

/- BEGIN UPSTREAM MODULE: AaronsonAmbainis.Level.Integrated -/
section
/-!
# The integrated all-pairs inequality

Let `f` be a real function on the cube with a row `a x` at every point `x`, and let `w > 0`.
Integrating the all-pairs inequality at the level `t` (`level_allPairs`) over all real `t`
(`level_integration`) gives the integrated all-pairs inequality (Proposition 7.4 of the paper):

`∑_{(x,y) : f y < f x} (f x - f y)^3 / (6 s_xy) ≤ 4^(n-1) ∑_j L_j / w_j`,
`s_xy = ∑_{j ∈ Δ(x,y)} w_j a^x_j a^y_j`,  `L_j = meanAbsIncr f j = E_x |f x - f (x^j)|`.

* `Level.integrated_core` — the form that comes out of the integration;
* `Level.integrated_four_mul` — multiplied by `4`, so that `4^n` appears;
* `integratedAllPairs_of_allPairs : AllPairsInequality → IntegratedAllPairsInequality` — with
  `4^(n-1)` as printed above (for `n = 0` both sides are `0`).

The denominators are positive: `Level.pairSum_pos` in `Level/AllPairs.lean`.
-/

namespace AaronsonAmbainis

open Finset

namespace Level

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The integrated all-pairs inequality, in the form that comes out of the integration over the
level. -/
theorem integrated_core (hAllPairs : AllPairsInequality) (f : Cube ι → ℝ) (a : Cube ι → ι → ℝ)
    (ha : ∀ x j, 0 ≤ a x j) (hrow : ∀ x y, |f x - f y| ≤ ∑ j ∈ diffSet x y, a x j)
    (w : ι → ℝ) (hw : ∀ j, 0 < w j) :
    2 * ∑ x, ∑ y, max (f x - f y) 0 ^ 3 / 6 * (∑ j ∈ diffSet x y, w j * a x j * a y j)⁻¹
      ≤ 2 ^ Fintype.card ι * ∑ j, (∑ x, max (f x - f (flipSet x {j})) 0) / w j := by
  have key := level_integration (univ : Finset (Cube ι × Cube ι)) (univ : Finset (ι × Cube ι))
    (fun z => 2 * (∑ j ∈ diffSet z.1 z.2, w j * a z.1 j * a z.2 j)⁻¹)
    (fun z => f z.1) (fun z => f z.2)
    (fun k => 2 ^ Fintype.card ι / w k.1) (fun k => f (flipSet k.2 {k.1})) (fun k => f k.2) ?_
  · rw [Fintype.sum_prod_type, Fintype.sum_prod_type] at key
    calc 2 * ∑ x, ∑ y, max (f x - f y) 0 ^ 3 / 6 * (∑ j ∈ diffSet x y, w j * a x j * a y j)⁻¹
        = ∑ x, ∑ y, 2 * (∑ j ∈ diffSet x y, w j * a x j * a y j)⁻¹
            * (max (f x - f y) 0 ^ 3 / 6) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro y _
          ring
      _ ≤ ∑ j, ∑ x, 2 ^ Fintype.card ι / w j * max (f x - f (flipSet x {j})) 0 := key
      _ = 2 ^ Fintype.card ι * ∑ j, (∑ x, max (f x - f (flipSet x {j})) 0) / w j := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.sum_div, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _
          ring
  · intro t
    have h := level_allPairs hAllPairs f a ha hrow w hw t
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    calc ∑ x, ∑ y, 2 * (∑ j ∈ diffSet x y, w j * a x j * a y j)⁻¹
            * (max (f x - t) 0 * max (t - f y) 0)
        = 2 * ∑ x, ∑ y, max (f x - t) 0 * max (t - f y) 0
            * (∑ j ∈ diffSet x y, w j * a x j * a y j)⁻¹ := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro y _
          ring
      _ ≤ 2 ^ Fintype.card ι * ∑ j, (bdry (lev f t) j : ℝ) / w j := h
      _ = ∑ j, ∑ x, 2 ^ Fintype.card ι / w j
            * (if f (flipSet x {j}) ≤ t ∧ t < f x then (1 : ℝ) else 0) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          rw [bdry_lev, Finset.sum_div, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _
          ring

/-- `∑_x (f x - f (x^j))⁺ = (1/2) ∑_x |f x - f (x^j)|` (Lemma 7.3 (iii) of the paper). -/
lemma sum_posPart_incr (f : Cube ι → ℝ) (j : ι) :
    ∑ x, max (f x - f (flipSet x {j})) 0 = (∑ x, |f x - f (flipSet x {j})|) / 2 := by
  have hinv : Function.Involutive (fun x : Cube ι => flipSet x {j}) :=
    fun x => flipSet_flipSet_self x {j}
  have hflip : ∑ x, max (f (flipSet x {j}) - f x) 0 = ∑ x, max (f x - f (flipSet x {j})) 0 := by
    have h := Equiv.sum_comp hinv.toPerm (fun x => max (f x - f (flipSet x {j})) 0)
    rw [← h]
    apply Finset.sum_congr rfl
    intro x _
    show max (f (flipSet x {j}) - f x) 0
      = max (f (flipSet x {j}) - f (flipSet (flipSet x {j}) {j})) 0
    rw [flipSet_flipSet_self]
  have h2 : ∀ x, |f x - f (flipSet x {j})|
      = max (f x - f (flipSet x {j})) 0 + max (f (flipSet x {j}) - f x) 0 := by
    intro x
    rcases le_total 0 (f x - f (flipSet x {j})) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith : f (flipSet x {j}) - f x ≤ 0),
        abs_of_nonneg h, add_zero]
    · rw [max_eq_right h, max_eq_left (by linarith : 0 ≤ f (flipSet x {j}) - f x),
        abs_of_nonpos h, zero_add]
      ring
  rw [Finset.sum_congr rfl (fun x _ => h2 x), Finset.sum_add_distrib, hflip]
  ring

/-- The integrated all-pairs inequality, multiplied by `4`: for a real function `f` on the cube,
rows `a x` of `f` and weights `w > 0`,
`4 ∑_{(x,y) : f y < f x} (f x - f y)^3 / (6 ∑_{j ∈ Δ(x,y)} w_j a^x_j a^y_j) ≤ 4^n ∑_j L_j / w_j`,
where `L_j = meanAbsIncr f j = E_x |f x - f (x^j)|`. -/
theorem integrated_four_mul (hAllPairs : AllPairsInequality) (f : Cube ι → ℝ)
    (a : Cube ι → ι → ℝ) (ha : ∀ x j, 0 ≤ a x j)
    (hrow : ∀ x y, |f x - f y| ≤ ∑ j ∈ diffSet x y, a x j) (w : ι → ℝ) (hw : ∀ j, 0 < w j) :
    4 * ∑ x, ∑ y ∈ univ.filter (fun y => f y < f x),
        (f x - f y) ^ 3 / (6 * ∑ j ∈ diffSet x y, w j * a x j * a y j)
      ≤ 4 ^ Fintype.card ι * ∑ j, meanAbsIncr f j / w j := by
  have h := integrated_core hAllPairs f a ha hrow w hw
  have hL : ∑ x, ∑ y ∈ univ.filter (fun y => f y < f x),
        (f x - f y) ^ 3 / (6 * ∑ j ∈ diffSet x y, w j * a x j * a y j)
      = ∑ x, ∑ y, max (f x - f y) 0 ^ 3 / 6
          * (∑ j ∈ diffSet x y, w j * a x j * a y j)⁻¹ := by
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro y _
    by_cases hxy : f y < f x
    · rw [if_pos hxy, max_eq_left (by linarith : 0 ≤ f x - f y)]
      ring
    · rw [if_neg hxy, max_eq_right (by linarith [not_lt.mp hxy] : f x - f y ≤ 0)]
      ring
  have hRt : ∀ j, (∑ x, max (f x - f (flipSet x {j})) 0) / w j
      = 2 ^ Fintype.card ι / 2 * (meanAbsIncr f j / w j) := by
    intro j
    have h2 : (2 : ℝ) ^ Fintype.card ι ≠ 0 := by positivity
    rw [sum_posPart_incr]
    unfold meanAbsIncr
    field_simp
  have h4 : (4 : ℝ) ^ Fintype.card ι = 2 ^ Fintype.card ι * 2 ^ Fintype.card ι := by
    rw [← mul_pow]
    norm_num
  rw [hL]
  calc 4 * ∑ x, ∑ y, max (f x - f y) 0 ^ 3 / 6
          * (∑ j ∈ diffSet x y, w j * a x j * a y j)⁻¹
      ≤ 2 * (2 ^ Fintype.card ι * ∑ j, (∑ x, max (f x - f (flipSet x {j})) 0) / w j) := by
        linarith
    _ = 4 ^ Fintype.card ι * ∑ j, meanAbsIncr f j / w j := by
        rw [Finset.sum_congr rfl (fun j _ => hRt j), ← Finset.mul_sum, h4]
        ring

end Level

/-- The integrated all-pairs inequality (Proposition 7.4 of the paper) from the all-pairs
inequality for Boolean functions (Proposition 5.2). -/
theorem integratedAllPairs_of_allPairs : AllPairsInequality → IntegratedAllPairsInequality := by
  intro hAllPairs ι _ _ f a ha hrow w hw
  have h := Level.integrated_four_mul hAllPairs f a ha hrow w hw
  rcases isEmpty_or_nonempty ι with hι | hι
  · have hL : ∑ x, ∑ y ∈ univ.filter (fun y => f y < f x),
        (f x - f y) ^ 3 / (6 * ∑ j ∈ diffSet x y, w j * a x j * a y j) = 0 := by
      apply Finset.sum_eq_zero
      intro x _
      apply Finset.sum_eq_zero
      intro y hy
      have hlt := (Finset.mem_filter.mp hy).2
      rw [Subsingleton.elim y x] at hlt
      exact absurd hlt (lt_irrefl _)
    rw [hL, Finset.univ_eq_empty (α := ι), Finset.sum_empty, mul_zero]
  · rw [Level.four_pow_card, mul_assoc] at h
    linarith

end AaronsonAmbainis

end
/- END UPSTREAM MODULE: AaronsonAmbainis.Level.Integrated -/

/- BEGIN UPSTREAM MODULE: AaronsonAmbainis.Level.Median -/
section
/-!
# A median, and a power-mean inequality

Two elementary facts with no cube in them:

* `exists_median` — a real function on a nonempty finite type has a median `m`: at least half of
  the points have `f ≤ m`, and at least half have `m ≤ f` (Lemma 7.8 of the paper);
* `sum_sq_cube_le` — `(∑ z²)^3 ≤ #s · (∑ |z|^3)^2`, that is, `(E z²)^3 ≤ (E |z|^3)^2`
  (Lemma 7.9 of the paper).
-/

namespace AaronsonAmbainis
namespace Level

open Finset

/-- A real function on a nonempty finite type has a median (Lemma 7.8 of the paper). -/
theorem exists_median {X : Type*} [Fintype X] [Nonempty X] (f : X → ℝ) :
    ∃ m : ℝ, Fintype.card X ≤ 2 * (univ.filter (fun x => f x ≤ m)).card ∧
      Fintype.card X ≤ 2 * (univ.filter (fun x => m ≤ f x)).card := by
  classical
  -- the values `v` of `f` with `#X ≤ 2 #{f ≤ v}`
  obtain ⟨S, hS⟩ : ∃ S : Finset ℝ, S = (univ.image f).filter
      (fun v => Fintype.card X ≤ 2 * (univ.filter (fun x => f x ≤ v)).card) := ⟨_, rfl⟩
  have hmem : ∀ v, v ∈ S ↔ (∃ x, f x = v) ∧
      Fintype.card X ≤ 2 * (univ.filter (fun x => f x ≤ v)).card := by
    intro v
    rw [hS, Finset.mem_filter, Finset.mem_image]
    simp
  -- the largest value of `f` belongs to `S`
  obtain ⟨x1, -, hx1⟩ := Finset.exists_max_image univ f univ_nonempty
  have hne : S.Nonempty := by
    refine ⟨f x1, (hmem _).mpr ⟨⟨x1, rfl⟩, ?_⟩⟩
    have hall : univ.filter (fun x => f x ≤ f x1) = univ :=
      Finset.filter_true_of_mem (fun x _ => hx1 x (mem_univ _))
    rw [hall, Finset.card_univ]
    omega
  -- the least element of `S` is a median
  refine ⟨S.min' hne, ((hmem _).mp (S.min'_mem hne)).2, ?_⟩
  by_contra hcon
  have hsplit : (univ.filter (fun x => f x < S.min' hne)).card
      + (univ.filter (fun x => S.min' hne ≤ f x)).card = Fintype.card X := by
    have h := Finset.card_filter_add_card_filter_not (s := (univ : Finset X))
      (fun x => f x < S.min' hne)
    simp only [not_lt, Finset.card_univ] at h
    exact h
  have hlow : (univ.filter (fun x => f x < S.min' hne)).Nonempty := by
    rw [← Finset.card_pos]
    omega
  obtain ⟨x2, hx2, hx2max⟩ := Finset.exists_max_image _ f hlow
  have hx2lt : f x2 < S.min' hne := (Finset.mem_filter.mp hx2).2
  have hsub : univ.filter (fun x => f x < S.min' hne) ⊆ univ.filter (fun x => f x ≤ f x2) := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨mem_univ _, hx2max x hx⟩
  have hcard := Finset.card_le_card hsub
  have hx2S : f x2 ∈ S := (hmem _).mpr ⟨⟨x2, rfl⟩, by omega⟩
  exact absurd (S.min'_le _ hx2S) (not_le.mpr hx2lt)

/-- A power-mean inequality: `(∑ z²)^3 ≤ #s · (∑ |z|^3)^2` (Lemma 7.9 of the paper). -/
theorem sum_sq_cube_le {α : Type*} (s : Finset α) (z : α → ℝ) :
    (∑ i ∈ s, z i ^ 2) ^ 3 ≤ (s.card : ℝ) * (∑ i ∈ s, |z i| ^ 3) ^ 2 := by
  have hA : 0 ≤ ∑ i ∈ s, z i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  -- `(∑ z²)² ≤ (∑ |z|)(∑ |z|^3)`
  have h1 : (∑ i ∈ s, z i ^ 2) ^ 2 ≤ (∑ i ∈ s, |z i|) * (∑ i ∈ s, |z i| ^ 3) :=
    Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s (fun i _ => abs_nonneg _)
      (fun i _ => pow_nonneg (abs_nonneg _) 3)
      (fun i _ => by
        rw [← sq_abs (z i)]
        exact le_of_eq (by ring))
  -- `(∑ |z|)² ≤ #s ∑ z²`
  have h2 : (∑ i ∈ s, |z i|) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, z i ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := s) (f := fun i => |z i|)
    simp only [sq_abs] at h
    exact h
  rcases hA.eq_or_lt with h0 | hpos
  · rw [← h0]
    have : (0 : ℝ) ≤ (s.card : ℝ) * (∑ i ∈ s, |z i| ^ 3) ^ 2 := by positivity
    simpa using this
  · have h3 : ((∑ i ∈ s, z i ^ 2) ^ 2) ^ 2
        ≤ ((∑ i ∈ s, |z i|) * (∑ i ∈ s, |z i| ^ 3)) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) h1 2
    have h4 : ((∑ i ∈ s, |z i|) * (∑ i ∈ s, |z i| ^ 3)) ^ 2
        ≤ ((s.card : ℝ) * ∑ i ∈ s, z i ^ 2) * (∑ i ∈ s, |z i| ^ 3) ^ 2 := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
    have h5 : (∑ i ∈ s, z i ^ 2) * (∑ i ∈ s, z i ^ 2) ^ 3
        ≤ (∑ i ∈ s, z i ^ 2) * ((s.card : ℝ) * (∑ i ∈ s, |z i| ^ 3) ^ 2) := by
      calc (∑ i ∈ s, z i ^ 2) * (∑ i ∈ s, z i ^ 2) ^ 3
          = ((∑ i ∈ s, z i ^ 2) ^ 2) ^ 2 := by ring
        _ ≤ ((s.card : ℝ) * ∑ i ∈ s, z i ^ 2) * (∑ i ∈ s, |z i| ^ 3) ^ 2 := h3.trans h4
        _ = (∑ i ∈ s, z i ^ 2) * ((s.card : ℝ) * (∑ i ∈ s, |z i| ^ 3) ^ 2) := by ring
    exact le_of_mul_le_mul_left h5 hpos

end Level
end AaronsonAmbainis

end
/- END UPSTREAM MODULE: AaronsonAmbainis.Level.Median -/

/- BEGIN UPSTREAM MODULE: AaronsonAmbainis.Level.ThirdMoment -/
section
/-!
# The third-moment inequality

Let `f` be a real function on the cube with rows of cost at most `K` at every point, and let
`M ≥ 0` bound all the mean absolute increments `L_j = meanAbsIncr f j`. Then, for every real `s`,

`E[((f - s)⁺)^3] · Pr[f ≤ s] ≤ (3/2) K² M`

(Theorem 7.6 of the paper; `thirdMoment_of_integratedAllPairs :
IntegratedAllPairsInequality → ThirdMomentInequality`; the unnormalised form is
`Level.thirdMoment_core`).

Proof: in the integrated all-pairs inequality (Proposition 7.4) keep the pairs `(x, y)` with
`f y ≤ s < f x`, where `(f x - f y)^3 ≥ (f x - s)^3`. Dividing the row at `x` by `(f x - s)^3`
turns the inequality into the hypothesis of the lemma that removes the weights (Lemma 5.3 of the
paper; `abstract_cs` in `TwoSided/CauchySchwarz.lean`), whose conclusion is the claim.

Two consequences of the third-moment inequality:

* `Level.thirdMoment_lower` — the inequality on the other side,
  `E[((s - f)⁺)^3] · Pr[f ≥ s] ≤ (3/2) K² M` (the second inequality of Theorem 7.6);
* `Level.separated_sets` — if `f ≥ s + θ` on `A` and `f ≤ s` on `B`, then
  `2 θ^3 μ(A) μ(B) ≤ 3 K² M` (Corollary 7.7).
-/

namespace AaronsonAmbainis

open Finset

namespace Level

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The integrated all-pairs inequality multiplied by `4`, so that `4^n` appears in place of
`4^(n-1)` (for `n = 0` both sides are `0`). -/
lemma four_mul_integrated (hInt : IntegratedAllPairsInequality) (f : Cube ι → ℝ)
    (a : Cube ι → ι → ℝ) (ha : ∀ x j, 0 ≤ a x j)
    (hrow : ∀ x y, |f x - f y| ≤ ∑ j ∈ diffSet x y, a x j) (w : ι → ℝ) (hw : ∀ j, 0 < w j) :
    4 * ∑ x, ∑ y ∈ univ.filter (fun y : Cube ι => f y < f x),
        (f x - f y) ^ 3 / (6 * ∑ j ∈ diffSet x y, w j * a x j * a y j)
      ≤ 4 ^ Fintype.card ι * ∑ j, meanAbsIncr f j / w j := by
  have h := hInt ι f a ha hrow w hw
  rcases isEmpty_or_nonempty ι with hι | hι
  · rw [Finset.univ_eq_empty (α := ι), Finset.sum_empty, mul_zero] at h ⊢
    linarith
  · rw [four_pow_card, mul_assoc]
    linarith

/-- The third-moment inequality, unnormalised:
`(∑_x ((f x - s)⁺)^3) · #{y : f y ≤ s} ≤ (3/2) 4^n M K²`. -/
theorem thirdMoment_core (hInt : IntegratedAllPairsInequality) (f : Cube ι → ℝ)
    (a : Cube ι → ι → ℝ) (ha : ∀ x j, 0 ≤ a x j) {K : ℝ} (hsum : ∀ x, ∑ j, a x j ≤ K)
    (hrow : ∀ x y, |f x - f y| ≤ ∑ j ∈ diffSet x y, a x j)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ j, meanAbsIncr f j ≤ M) (s : ℝ) :
    (∑ x, max (f x - s) 0 ^ 3) * ((univ.filter (fun y : Cube ι => f y ≤ s)).card : ℝ)
      ≤ 3 / 2 * 4 ^ Fintype.card ι * M * K ^ 2 := by
  have hC : 0 ≤ 3 / 2 * (4 : ℝ) ^ Fintype.card ι * M := by positivity
  have hRHS : 0 ≤ 3 / 2 * (4 : ℝ) ^ Fintype.card ι * M * K ^ 2 := by positivity
  -- the two sets
  obtain ⟨A, hA⟩ : ∃ A : Finset (Cube ι), A = univ.filter (fun x : Cube ι => s < f x) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Finset (Cube ι), B = univ.filter (fun y : Cube ι => f y ≤ s) := ⟨_, rfl⟩
  have hmemA : ∀ x, x ∈ A ↔ s < f x := by
    intro x
    rw [hA]
    simp
  have hmemB : ∀ y, y ∈ B ↔ f y ≤ s := by
    intro y
    rw [hB]
    simp
  -- the third moment as a sum over `A`
  have hsumA : ∑ x, max (f x - s) 0 ^ 3 = ∑ x ∈ A, (f x - s) ^ 3 := by
    rw [hA, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : s < f x
    · rw [if_pos hx, max_eq_left (by linarith : 0 ≤ f x - s)]
    · rw [if_neg hx, max_eq_right (by linarith [not_lt.mp hx] : f x - s ≤ 0)]
      norm_num
  rw [← hB, hsumA]
  -- the trivial cases
  rcases A.eq_empty_or_nonempty with hAe | ⟨x0, hx0⟩
  · rw [hAe, Finset.sum_empty, zero_mul]
    exact hRHS
  rcases B.eq_empty_or_nonempty with hBe | ⟨y0, hy0⟩
  · rw [hBe, Finset.card_empty, Nat.cast_zero, mul_zero]
    exact hRHS
  have hx0' := (hmemA x0).mp hx0
  have hy0' := (hmemB y0).mp hy0
  -- positivity of the costs
  have hposA : ∀ x ∈ A, 0 < ∑ j, a x j := fun x hx =>
    rowSum_pos ha hrow (ne_of_gt (lt_of_le_of_lt hy0' ((hmemA x).mp hx)))
  have hposB : ∀ y ∈ B, 0 < ∑ j, a y j := fun y hy =>
    rowSum_pos ha hrow (ne_of_lt (lt_of_le_of_lt ((hmemB y).mp hy) hx0'))
  have hK : 0 < K := lt_of_lt_of_le (hposA x0 hx0) (hsum x0)
  -- the rows on `A`, divided by `(f x - s)^3`
  have hscal : ∀ x ∈ A, ∀ (y : Cube ι) (w : ι → ℝ),
      ∑ j ∈ diffSet x y, w j * (a x j / max (f x - s) 0 ^ 3) * a y j
        = (∑ j ∈ diffSet x y, w j * a x j * a y j) / (f x - s) ^ 3 := by
    intro x hx y w
    have hxs : 0 < f x - s := sub_pos.mpr ((hmemA x).mp hx)
    rw [max_eq_left hxs.le, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have key := abstract_cs A B (fun x j => a x j / max (f x - s) 0 ^ 3) a
    (fun x j => div_nonneg (ha x j) (pow_nonneg (le_max_right _ _) 3)) ha diffSet
    (3 / 2 * 4 ^ Fintype.card ι * M) hC ?_ ?_
  · -- the conclusion of the Cauchy–Schwarz lemma
    have h1 : ∑ x ∈ A, (f x - s) ^ 3 / K
        ≤ ∑ x ∈ A, (∑ j, a x j / max (f x - s) 0 ^ 3)⁻¹ := by
      apply Finset.sum_le_sum
      intro x hx
      have hxs : 0 < f x - s := sub_pos.mpr ((hmemA x).mp hx)
      rw [max_eq_left hxs.le, ← Finset.sum_div, inv_div]
      exact div_le_div_of_nonneg_left (pow_pos hxs 3).le (hposA x hx) (hsum x)
    have h2 : (B.card : ℝ) / K ≤ ∑ y ∈ B, (∑ j, a y j)⁻¹ := by
      have h := Finset.sum_le_sum (s := B) (f := fun _ => K⁻¹) (g := fun y => (∑ j, a y j)⁻¹)
        (fun y hy => inv_anti₀ (hposB y hy) (hsum y))
      rw [Finset.sum_const, nsmul_eq_mul] at h
      rw [div_eq_mul_inv]
      exact h
    have h3 : 0 ≤ ∑ x ∈ A, (f x - s) ^ 3 / K := Finset.sum_nonneg (fun x hx =>
      div_nonneg (pow_nonneg (sub_nonneg.mpr ((hmemA x).mp hx).le) 3) hK.le)
    have h4 : (0 : ℝ) ≤ (B.card : ℝ) / K := div_nonneg (Nat.cast_nonneg _) hK.le
    have h5 := le_trans (mul_le_mul h1 h2 h4 (le_trans h3 h1)) key
    rw [← Finset.sum_div] at h5
    have h6 : (∑ x ∈ A, (f x - s) ^ 3) / K * ((B.card : ℝ) / K)
        = (∑ x ∈ A, (f x - s) ^ 3) * (B.card : ℝ) / K ^ 2 := by ring
    rw [h6, div_le_iff₀ (by positivity)] at h5
    exact h5
  · -- the denominators are positive
    intro x hx y hy w hw
    rw [hscal x hx y w]
    exact div_pos
      (pairSum_pos ha hrow hw (lt_of_le_of_lt ((hmemB y).mp hy) ((hmemA x).mp hx)))
      (pow_pos (sub_pos.mpr ((hmemA x).mp hx)) 3)
  · -- the inequality for the pairs in `A × B`, from the integrated all-pairs inequality
    intro w hw
    have hT1 := four_mul_integrated hInt f a ha hrow w hw
    have hterm : ∀ x ∈ A, ∀ y ∈ B,
        (∑ j ∈ diffSet x y, w j * (a x j / max (f x - s) 0 ^ 3) * a y j)⁻¹
          ≤ 6 * ((f x - f y) ^ 3 / (6 * ∑ j ∈ diffSet x y, w j * a x j * a y j)) := by
      intro x hx y hy
      have hxs : 0 < f x - s := sub_pos.mpr ((hmemA x).mp hx)
      have hys : f y ≤ s := (hmemB y).mp hy
      have hS := pairSum_pos ha hrow hw (lt_of_le_of_lt hys ((hmemA x).mp hx))
      have e : 6 * ((f x - f y) ^ 3 / (6 * ∑ j ∈ diffSet x y, w j * a x j * a y j))
          = (f x - f y) ^ 3 / ∑ j ∈ diffSet x y, w j * a x j * a y j := by
        field_simp
      rw [hscal x hx y w, inv_div, e]
      exact div_le_div_of_nonneg_right
        (pow_le_pow_left₀ hxs.le (by linarith : f x - s ≤ f x - f y) 3) hS.le
    have hsub : ∀ x ∈ A, B ⊆ univ.filter (fun y : Cube ι => f y < f x) := by
      intro x hx y hy
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, lt_of_le_of_lt ((hmemB y).mp hy) ((hmemA x).mp hx)⟩
    have hGnn : ∀ x : Cube ι, ∀ y ∈ univ.filter (fun y : Cube ι => f y < f x),
        0 ≤ 6 * ((f x - f y) ^ 3 / (6 * ∑ j ∈ diffSet x y, w j * a x j * a y j)) := by
      intro x y hy
      have hlt := (Finset.mem_filter.mp hy).2
      exact mul_nonneg (by norm_num) (div_nonneg (pow_nonneg (by linarith) 3)
        (mul_nonneg (by norm_num) (pairSum_pos ha hrow hw hlt).le))
    have h7 : ∑ j, meanAbsIncr f j / w j ≤ M * ∑ j, (w j)⁻¹ := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j _
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (hM j) (inv_pos.mpr (hw j)).le
    have h8 : (0 : ℝ) ≤ 4 ^ Fintype.card ι := by positivity
    have h9 := mul_le_mul_of_nonneg_left h7 h8
    calc ∑ x ∈ A, ∑ y ∈ B,
          (∑ j ∈ diffSet x y, w j * (a x j / max (f x - s) 0 ^ 3) * a y j)⁻¹
        ≤ ∑ x ∈ A, ∑ y ∈ B,
            6 * ((f x - f y) ^ 3 / (6 * ∑ j ∈ diffSet x y, w j * a x j * a y j)) :=
          Finset.sum_le_sum (fun x hx => Finset.sum_le_sum (fun y hy => hterm x hx y hy))
      _ ≤ ∑ x ∈ A, ∑ y ∈ univ.filter (fun y : Cube ι => f y < f x),
            6 * ((f x - f y) ^ 3 / (6 * ∑ j ∈ diffSet x y, w j * a x j * a y j)) :=
          Finset.sum_le_sum (fun x hx => Finset.sum_le_sum_of_subset_of_nonneg (hsub x hx)
            (fun y hy _ => hGnn x y hy))
      _ ≤ ∑ x, ∑ y ∈ univ.filter (fun y : Cube ι => f y < f x),
            6 * ((f x - f y) ^ 3 / (6 * ∑ j ∈ diffSet x y, w j * a x j * a y j)) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun x _ _ => Finset.sum_nonneg (fun y hy => hGnn x y hy))
      _ = 6 * ∑ x, ∑ y ∈ univ.filter (fun y : Cube ι => f y < f x),
            (f x - f y) ^ 3 / (6 * ∑ j ∈ diffSet x y, w j * a x j * a y j) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.mul_sum]
      _ ≤ 3 / 2 * 4 ^ Fintype.card ι * M * ∑ j, (w j)⁻¹ := by linarith

end Level

/-- The third-moment inequality (Theorem 7.6 of the paper, first inequality) from the integrated
all-pairs inequality (Proposition 7.4). -/
theorem thirdMoment_of_integratedAllPairs :
    IntegratedAllPairsInequality → ThirdMomentInequality := by
  intro hInt ι _ _ f K a ha hsum hrow M hM0 hM s
  have h := Level.thirdMoment_core hInt f a ha hsum hrow hM0 hM s
  have h4 : (4 : ℝ) ^ Fintype.card ι = 2 ^ Fintype.card ι * 2 ^ Fintype.card ι := by
    rw [← mul_pow]
    norm_num
  have h2 : (0 : ℝ) < 2 ^ Fintype.card ι := by positivity
  rw [div_mul_div_comm, div_le_iff₀ (mul_pos h2 h2)]
  rw [h4] at h
  linarith

namespace Level

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The third-moment inequality on the other side (Theorem 7.6 of the paper, second inequality):
`E[((s - f)⁺)^3] · Pr[f ≥ s] ≤ (3/2) K² M`. It is the third-moment inequality for `-f` and `-s`. -/
theorem thirdMoment_lower (hTM : ThirdMomentInequality) (f : Cube ι → ℝ) (a : Cube ι → ι → ℝ)
    (ha : ∀ x j, 0 ≤ a x j) {K : ℝ} (hsum : ∀ x, ∑ j, a x j ≤ K)
    (hrow : ∀ x y, |f x - f y| ≤ ∑ j ∈ diffSet x y, a x j)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ j, meanAbsIncr f j ≤ M) (s : ℝ) :
    (∑ x, max (s - f x) 0 ^ 3) / 2 ^ Fintype.card ι
        * (((univ.filter (fun y : Cube ι => s ≤ f y)).card : ℝ) / 2 ^ Fintype.card ι)
      ≤ 3 / 2 * K ^ 2 * M := by
  have hrow' : ∀ x y, |(fun x => -f x) x - (fun x => -f x) y| ≤ ∑ j ∈ diffSet x y, a x j := by
    intro x y
    show |-f x - -f y| ≤ ∑ j ∈ diffSet x y, a x j
    rw [neg_sub_neg, abs_sub_comm]
    exact hrow x y
  have hM' : ∀ j, meanAbsIncr (fun x => -f x) j ≤ M := by
    intro j
    have e : meanAbsIncr (fun x => -f x) j = meanAbsIncr f j := by
      unfold meanAbsIncr
      congr 1
      apply Finset.sum_congr rfl
      intro x _
      show |-f x - -f (flipSet x {j})| = |f x - f (flipSet x {j})|
      rw [neg_sub_neg, abs_sub_comm]
    rw [e]
    exact hM j
  have h := hTM ι (fun x => -f x) K a ha hsum hrow' M hM0 hM' (-s)
  have e1 : ∀ x, max ((fun x => -f x) x - -s) 0 = max (s - f x) 0 := by
    intro x
    show max (-f x - -s) 0 = max (s - f x) 0
    rw [neg_sub_neg]
  have e2 : (univ.filter (fun y : Cube ι => (fun x => -f x) y ≤ -s))
      = univ.filter (fun y : Cube ι => s ≤ f y) := by
    apply Finset.filter_congr
    intro y _
    show -f y ≤ -s ↔ s ≤ f y
    exact neg_le_neg_iff
  simp only [e1] at h
  rw [e2] at h
  exact h

/-- Two separated sets (Corollary 7.7 of the paper). If `f` has rows of cost at most `K`
everywhere, `M ≥ 0` bounds all `L_j = meanAbsIncr f j`, and `f ≥ s + θ` on `A`, `f ≤ s` on `B`
with `θ ≥ 0`, then `2 θ^3 μ(A) μ(B) ≤ 3 K² M` (`μ` the uniform probability on the cube). -/
theorem separated_sets (hTM : ThirdMomentInequality) (f : Cube ι → ℝ) (a : Cube ι → ι → ℝ)
    (ha : ∀ x j, 0 ≤ a x j) {K : ℝ} (hsum : ∀ x, ∑ j, a x j ≤ K)
    (hrow : ∀ x y, |f x - f y| ≤ ∑ j ∈ diffSet x y, a x j)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ j, meanAbsIncr f j ≤ M)
    (A B : Finset (Cube ι)) (s θ : ℝ) (hθ : 0 ≤ θ)
    (hA : ∀ x ∈ A, s + θ ≤ f x) (hB : ∀ y ∈ B, f y ≤ s) :
    2 * θ ^ 3 * ((A.card : ℝ) / 2 ^ Fintype.card ι) * ((B.card : ℝ) / 2 ^ Fintype.card ι)
      ≤ 3 * K ^ 2 * M := by
  have h := hTM ι f K a ha hsum hrow M hM0 hM s
  have h2 : (0 : ℝ) < 2 ^ Fintype.card ι := by positivity
  -- `θ^3 #A ≤ ∑_x ((f x - s)⁺)^3`
  have h1 : θ ^ 3 * (A.card : ℝ) ≤ ∑ x, max (f x - s) 0 ^ 3 := by
    calc θ ^ 3 * (A.card : ℝ) = ∑ _x ∈ A, θ ^ 3 := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ ∑ x ∈ A, max (f x - s) 0 ^ 3 := by
          apply Finset.sum_le_sum
          intro x hx
          exact pow_le_pow_left₀ hθ (le_max_of_le_left (by linarith [hA x hx])) 3
      _ ≤ ∑ x, max (f x - s) 0 ^ 3 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun x _ _ => pow_nonneg (le_max_right _ _) 3)
  -- `#B ≤ #{f ≤ s}`
  have h3 : (B.card : ℝ) ≤ ((univ.filter (fun y : Cube ι => f y ≤ s)).card : ℝ) := by
    have hsub : B ⊆ univ.filter (fun y : Cube ι => f y ≤ s) := by
      intro y hy
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hB y hy⟩
    exact_mod_cast Finset.card_le_card hsub
  have h5 : θ ^ 3 * (A.card : ℝ) / 2 ^ Fintype.card ι * ((B.card : ℝ) / 2 ^ Fintype.card ι)
      ≤ (∑ x, max (f x - s) 0 ^ 3) / 2 ^ Fintype.card ι
        * (((univ.filter (fun y : Cube ι => f y ≤ s)).card : ℝ) / 2 ^ Fintype.card ι) :=
    mul_le_mul (div_le_div_of_nonneg_right h1 h2.le) (div_le_div_of_nonneg_right h3 h2.le)
      (div_nonneg (Nat.cast_nonneg _) h2.le)
      (div_nonneg (Finset.sum_nonneg fun x _ => pow_nonneg (le_max_right _ _) 3) h2.le)
  have h6 : 2 * θ ^ 3 * ((A.card : ℝ) / 2 ^ Fintype.card ι) * ((B.card : ℝ) / 2 ^ Fintype.card ι)
      = 2 * (θ ^ 3 * (A.card : ℝ) / 2 ^ Fintype.card ι
          * ((B.card : ℝ) / 2 ^ Fintype.card ι)) := by ring
  rw [h6]
  linarith

end Level

end AaronsonAmbainis

end
/- END UPSTREAM MODULE: AaronsonAmbainis.Level.ThirdMoment -/

/- BEGIN UPSTREAM MODULE: AaronsonAmbainis.Level.Increments -/
section
/-!
# The mean absolute increments: from the third-moment inequality to the variance

Let `f` be a real function on the cube with rows of cost at most `K` at every point, and let
`M ≥ 0` bound all the mean absolute increments `L_j = meanAbsIncr f j`. With a median `m` of `f`,
the third-moment inequality and the inequality on the other side (`Level.thirdMoment_lower`) give
`E|f - m|^3 ≤ 6 K² M` (`Level.exists_abs_cube_le`). Since `Var f ≤ E (f - m)²` and
`(E z²)^3 ≤ (E |z|^3)^2`, it follows that

`Var(f)^3 ≤ 36 K^4 M²`                                  (`Level.variance_cube_le`).

Taking `M = max_j L_j` (Theorem 7.10 of the paper):

* `meanIncrement_of_thirdMoment : ThirdMomentInequality → MeanIncrementBound` — some `j` has
  `Var(f)^3 ≤ 36 K^4 L_j²`;
* `Level.exists_meanAbsIncr_ge_sqrt` — the same with the power `3/2` written as `Var · √Var`:
  `Var(f)^{3/2} ≤ 6 K² L_j` (the two forms are equivalent: `Level.cube_le_iff_mul_sqrt_le`).

No bound on the values of `f` is used. That `K > 0` under these hypotheses is `Level.cost_pos`.
-/

namespace AaronsonAmbainis

open Finset

namespace Level

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `E|f - m|^3 ≤ 6 K² M` for a median `m` of `f`. -/
theorem exists_abs_cube_le (hTM : ThirdMomentInequality) (f : Cube ι → ℝ) (a : Cube ι → ι → ℝ)
    (ha : ∀ x j, 0 ≤ a x j) {K : ℝ} (hsum : ∀ x, ∑ j, a x j ≤ K)
    (hrow : ∀ x y, |f x - f y| ≤ ∑ j ∈ diffSet x y, a x j)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ j, meanAbsIncr f j ≤ M) :
    ∃ m : ℝ, (∑ x, |f x - m| ^ 3) / 2 ^ Fintype.card ι ≤ 6 * K ^ 2 * M := by
  obtain ⟨m, hm1, hm2⟩ := exists_median f
  refine ⟨m, ?_⟩
  have h2 : (0 : ℝ) < 2 ^ Fintype.card ι := by positivity
  have hcard : ((Fintype.card (Cube ι) : ℕ) : ℝ) = 2 ^ Fintype.card ι := card_cube
  -- each of the two sets `{f ≤ m}`, `{m ≤ f}` has measure at least `1/2`
  have hB1 : (1 : ℝ) / 2
      ≤ ((univ.filter (fun y : Cube ι => f y ≤ m)).card : ℝ) / 2 ^ Fintype.card ι := by
    rw [le_div_iff₀ h2]
    have h : ((Fintype.card (Cube ι) : ℕ) : ℝ)
        ≤ 2 * ((univ.filter (fun y : Cube ι => f y ≤ m)).card : ℝ) := by exact_mod_cast hm1
    rw [hcard] at h
    linarith
  have hB2 : (1 : ℝ) / 2
      ≤ ((univ.filter (fun y : Cube ι => m ≤ f y)).card : ℝ) / 2 ^ Fintype.card ι := by
    rw [le_div_iff₀ h2]
    have h : ((Fintype.card (Cube ι) : ℕ) : ℝ)
        ≤ 2 * ((univ.filter (fun y : Cube ι => m ≤ f y)).card : ℝ) := by exact_mod_cast hm2
    rw [hcard] at h
    linarith
  have hup := hTM ι f K a ha hsum hrow M hM0 hM m
  have hlo := thirdMoment_lower hTM f a ha hsum hrow hM0 hM m
  have hPnn : 0 ≤ (∑ x, max (f x - m) 0 ^ 3) / 2 ^ Fintype.card ι :=
    div_nonneg (Finset.sum_nonneg fun x _ => pow_nonneg (le_max_right _ _) 3) h2.le
  have hQnn : 0 ≤ (∑ x, max (m - f x) 0 ^ 3) / 2 ^ Fintype.card ι :=
    div_nonneg (Finset.sum_nonneg fun x _ => pow_nonneg (le_max_right _ _) 3) h2.le
  have hP : (∑ x, max (f x - m) 0 ^ 3) / 2 ^ Fintype.card ι ≤ 3 * K ^ 2 * M := by
    have h := mul_le_mul_of_nonneg_left hB1 hPnn
    linarith
  have hQ : (∑ x, max (m - f x) 0 ^ 3) / 2 ^ Fintype.card ι ≤ 3 * K ^ 2 * M := by
    have h := mul_le_mul_of_nonneg_left hB2 hQnn
    linarith
  have hsplit : ∑ x, |f x - m| ^ 3
      = ∑ x, max (f x - m) 0 ^ 3 + ∑ x, max (m - f x) 0 ^ 3 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    rcases le_total 0 (f x - m) with h | h
    · rw [abs_of_nonneg h, max_eq_left h, max_eq_right (by linarith : m - f x ≤ 0)]
      ring
    · rw [abs_of_nonpos h, max_eq_right h, max_eq_left (by linarith : 0 ≤ m - f x)]
      ring
  rw [hsplit, add_div]
  linarith

/-- `Var(f)^3 ≤ 36 K^4 M²` when `f` has rows of cost at most `K` everywhere and `M ≥ 0` bounds
all the mean absolute increments `L_j = meanAbsIncr f j`. -/
theorem variance_cube_le (hTM : ThirdMomentInequality) (f : Cube ι → ℝ) (a : Cube ι → ι → ℝ)
    (ha : ∀ x j, 0 ≤ a x j) {K : ℝ} (hsum : ∀ x, ∑ j, a x j ≤ K)
    (hrow : ∀ x y, |f x - f y| ≤ ∑ j ∈ diffSet x y, a x j)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ j, meanAbsIncr f j ≤ M) :
    variance f ^ 3 ≤ 36 * K ^ 4 * M ^ 2 := by
  obtain ⟨m, hm⟩ := exists_abs_cube_le hTM f a ha hsum hrow hM0 hM
  have h2 : (0 : ℝ) < 2 ^ Fintype.card ι := by positivity
  have hV0 : 0 ≤ variance f := variance_nonneg f
  have hV := variance_le_sq_dist f m
  have hpm := sum_sq_cube_le (univ : Finset (Cube ι)) (fun x => f x - m)
  rw [Finset.card_univ, card_cube] at hpm
  have hT0 : 0 ≤ (∑ x, |f x - m| ^ 3) / 2 ^ Fintype.card ι :=
    div_nonneg (Finset.sum_nonneg fun x _ => pow_nonneg (abs_nonneg _) 3) h2.le
  calc variance f ^ 3 ≤ ((∑ x, (f x - m) ^ 2) / 2 ^ Fintype.card ι) ^ 3 :=
        pow_le_pow_left₀ hV0 hV 3
    _ ≤ ((∑ x, |f x - m| ^ 3) / 2 ^ Fintype.card ι) ^ 2 := by
        rw [div_pow, div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
        have h7 := mul_le_mul_of_nonneg_right hpm (sq_nonneg ((2 : ℝ) ^ Fintype.card ι))
        calc (∑ x, (f x - m) ^ 2) ^ 3 * ((2 : ℝ) ^ Fintype.card ι) ^ 2
            ≤ 2 ^ Fintype.card ι * (∑ x, |f x - m| ^ 3) ^ 2 * ((2 : ℝ) ^ Fintype.card ι) ^ 2 := h7
          _ = (∑ x, |f x - m| ^ 3) ^ 2 * ((2 : ℝ) ^ Fintype.card ι) ^ 3 := by ring
    _ ≤ (6 * K ^ 2 * M) ^ 2 := pow_le_pow_left₀ hT0 hm 2
    _ = 36 * K ^ 4 * M ^ 2 := by ring

end Level

/-- The bound for the mean absolute increments (Theorem 7.10 of the paper) from the third-moment
inequality (Theorem 7.6): if `Var(f) > 0` and `f` has rows of cost at most `K` everywhere, then
some coordinate `j` has `Var(f)^3 ≤ 36 K^4 L_j²`, where
`L_j = meanAbsIncr f j = E|f(x) - f(x^j)|`. -/
theorem meanIncrement_of_thirdMoment : ThirdMomentInequality → MeanIncrementBound := by
  intro hTM ι _ _ f K a ha hsum hrow hvar
  have hne : Nonempty ι := by
    by_contra hemp
    have hι : IsEmpty ι := not_nonempty_iff.mp hemp
    rw [Level.variance_eq_zero_of_isEmpty f] at hvar
    exact lt_irrefl 0 hvar
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image univ (meanAbsIncr f) univ_nonempty
  exact ⟨j, Level.variance_cube_le hTM f a ha hsum hrow (Level.meanAbsIncr_nonneg f j)
    (fun j' => hj j' (mem_univ _))⟩

namespace Level

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- For `V, L ≥ 0`: `V^3 ≤ 36 K^4 L²` if and only if `V^{3/2} ≤ 6 K² L`, where `V^{3/2}` is written
`V · √V`. -/
theorem cube_le_iff_mul_sqrt_le {V K L : ℝ} (hV : 0 ≤ V) (hL : 0 ≤ L) :
    V ^ 3 ≤ 36 * K ^ 4 * L ^ 2 ↔ V * Real.sqrt V ≤ 6 * K ^ 2 * L := by
  have ha : 0 ≤ V * Real.sqrt V := mul_nonneg hV (Real.sqrt_nonneg V)
  have hb : 0 ≤ 6 * K ^ 2 * L := mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg K)) hL
  have e1 : (V * Real.sqrt V) ^ 2 = V ^ 3 := by
    rw [mul_pow, Real.sq_sqrt hV]
    ring
  have e2 : (6 * K ^ 2 * L) ^ 2 = 36 * K ^ 4 * L ^ 2 := by ring
  constructor
  · intro h
    apply le_of_pow_le_pow_left₀ two_ne_zero hb
    rw [e1, e2]
    exact h
  · intro h
    have h2 := pow_le_pow_left₀ ha h 2
    rw [e1, e2] at h2
    exact h2

/-- The bound for the mean absolute increments with the power `3/2` written as `Var · √Var`:
some coordinate `j` has `Var(f)^{3/2} ≤ 6 K² L_j`, that is, `L_j ≥ Var(f)^{3/2} / (6 K²)`. -/
theorem exists_meanAbsIncr_ge_sqrt (hMI : MeanIncrementBound) (f : Cube ι → ℝ)
    (a : Cube ι → ι → ℝ) (ha : ∀ x j, 0 ≤ a x j) {K : ℝ} (hsum : ∀ x, ∑ j, a x j ≤ K)
    (hrow : ∀ x y, |f x - f y| ≤ ∑ j ∈ diffSet x y, a x j) (hvar : 0 < variance f) :
    ∃ j, variance f * Real.sqrt (variance f) ≤ 6 * K ^ 2 * meanAbsIncr f j := by
  obtain ⟨j, hj⟩ := hMI ι f K a ha hsum hrow hvar
  exact ⟨j, (cube_le_iff_mul_sqrt_le hvar.le (meanAbsIncr_nonneg f j)).mp hj⟩

end Level

end AaronsonAmbainis

end
/- END UPSTREAM MODULE: AaronsonAmbainis.Level.Increments -/

/- BEGIN UPSTREAM MODULE: AaronsonAmbainis.Level.Main -/
section
/-!
# Real functions with a row at every point: the three implications

Section 7 of the paper.

* `AaronsonAmbainis.integratedAllPairs_of_allPairs :
  AllPairsInequality → IntegratedAllPairsInequality`
  (the integrated all-pairs inequality, Proposition 7.4 of the paper, from the all-pairs
  inequality for Boolean functions, Proposition 5.2, applied to the level functions `1_{f > t}`
  and integrated over the level `t`; file `Integrated.lean`, helpers in `Rows`, `AllPairs`,
  `Integral`)
* `AaronsonAmbainis.thirdMoment_of_integratedAllPairs :
  IntegratedAllPairsInequality → ThirdMomentInequality`
  (the third-moment inequality, Theorem 7.6, from the integrated all-pairs inequality and the
  lemma that removes the weights, Lemma 5.3, which is in `TwoSided/CauchySchwarz.lean`; file
  `ThirdMoment.lean`)
* `AaronsonAmbainis.meanIncrement_of_thirdMoment : ThirdMomentInequality → MeanIncrementBound`
  (the bound for the mean absolute increments, Theorem 7.10, from the third-moment inequality at
  a median; file `Increments.lean`, helpers in `Basic`, `Median`)
-/

end
/- END UPSTREAM MODULE: AaronsonAmbainis.Level.Main -/

/- BEGIN UPSTREAM MODULE: AaronsonAmbainis.Average.Coordinate -/
section
/-!
# Averaging a function over one coordinate

For a coordinate `j` let `avg j f x = (f x + f (x^j)) / 2`. Then (Lemma 8.1 of the paper)

* `variance_avg`         — `Var f = Var (avg j f) + Inf_j f` (`f = avg j f + (f - f ∘ flip_j)/2`,
                           and the two parts are even and odd under the flip of `j`);
* `inflR_avg_le`         — `Inf_k (avg j f) ≤ Inf_k f` for every `k`;
* `meanAbsIncr_avg_le`   — `L_k (avg j f) ≤ L_k f` for every `k`;
* `meanAbsIncr_avg_self` — `L_j (avg j f) = 0`;
* `rows_avg`             — if `a x` is a row of `f` at `x` for every `x`, of cost at most `K`,
                           then `(a x + a (x^j)) / 2` is a row of `avg j f` at `x`, of cost at
                           most `K`.

Here `L_k(f) = meanAbsIncr f k` is the mean absolute increment of `f` in the coordinate `k`.
-/

namespace AaronsonAmbainis
namespace Average

open Finset

section NoFintype

variable {ι : Type*} [DecidableEq ι]

/-- Flips commute. -/
lemma flipSet_comm (x : Cube ι) (S T : Finset ι) :
    flipSet (flipSet x S) T = flipSet (flipSet x T) S := by
  funext i
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;> simp [flipSet, hS, hT]

end NoFintype

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Flipping the same coordinates in two points does not change the set where they differ. -/
lemma diffSet_flip (x y : Cube ι) (S : Finset ι) :
    diffSet (flipSet x S) (flipSet y S) = diffSet x y := by
  ext i
  rw [mem_diffSet, mem_diffSet, flipSet_apply, flipSet_apply]
  by_cases hS : i ∈ S
  · rw [if_pos hS, if_pos hS]
    cases x i <;> cases y i <;> simp
  · rw [if_neg hS, if_neg hS]

/-- The flip of the coordinate `j` is a bijection of the cube. -/
lemma sum_flip (j : ι) (F : Cube ι → ℝ) : ∑ x, F (flipSet x {j}) = ∑ x, F x := by
  have hinv : Function.Involutive (fun x : Cube ι => flipSet x {j}) :=
    fun x => flipSet_flipSet_self x {j}
  exact Equiv.sum_comp hinv.toPerm F

/-- The average of `f` over the coordinate `j`. -/
noncomputable def avg (j : ι) (f : Cube ι → ℝ) : Cube ι → ℝ :=
  fun x => (f x + f (flipSet x {j})) / 2

omit [Fintype ι] in
lemma avg_flip (j : ι) (f : Cube ι → ℝ) (x : Cube ι) : avg j f (flipSet x {j}) = avg j f x := by
  unfold avg
  rw [flipSet_flipSet_self]
  ring

theorem mean_avg (j : ι) (f : Cube ι → ℝ) : mean (avg j f) = mean f := by
  unfold mean avg
  congr 1
  rw [← Finset.sum_div, Finset.sum_add_distrib, sum_flip j f]
  ring

/-- `Var f = Var (avg j f) + Inf_j f`. -/
theorem variance_avg (j : ι) (f : Cube ι → ℝ) :
    variance f = variance (avg j f) + inflR f j := by
  have hm := mean_avg j f
  have hre : ∑ x, (f (flipSet x {j}) - mean f) ^ 2 = ∑ x, (f x - mean f) ^ 2 :=
    sum_flip j (fun x => (f x - mean f) ^ 2)
  have hpt : ∀ x, (f x - mean f) ^ 2 + (f (flipSet x {j}) - mean f) ^ 2
      = 2 * ((avg j f x - mean f) ^ 2 + ((f x - f (flipSet x {j})) / 2) ^ 2) := by
    intro x
    unfold avg
    ring
  have hsum : ∑ x, (f x - mean f) ^ 2 + ∑ x, (f (flipSet x {j}) - mean f) ^ 2
      = 2 * (∑ x, (avg j f x - mean f) ^ 2 + ∑ x, ((f x - f (flipSet x {j})) / 2) ^ 2) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun x _ => hpt x)
  rw [hre] at hsum
  have hkey : ∑ x, (f x - mean f) ^ 2
      = ∑ x, (avg j f x - mean f) ^ 2 + ∑ x, ((f x - f (flipSet x {j})) / 2) ^ 2 := by
    linarith
  unfold variance inflR
  rw [hm, ← add_div, hkey]

/-- `Inf_k (avg j f) ≤ Inf_k f` for every `k`. -/
theorem inflR_avg_le (j k : ι) (f : Cube ι → ℝ) : inflR (avg j f) k ≤ inflR f k := by
  have hcomm : ∀ x : Cube ι, flipSet (flipSet x {k}) {j} = flipSet (flipSet x {j}) {k} :=
    fun x => flipSet_comm x {k} {j}
  have hpt : ∀ x, ((avg j f x - avg j f (flipSet x {k})) / 2) ^ 2
      ≤ (((f x - f (flipSet x {k})) / 2) ^ 2
        + ((f (flipSet x {j}) - f (flipSet (flipSet x {j}) {k})) / 2) ^ 2) / 2 := by
    intro x
    unfold avg
    rw [hcomm x]
    nlinarith [sq_nonneg ((f x - f (flipSet x {k}))
      - (f (flipSet x {j}) - f (flipSet (flipSet x {j}) {k})))]
  have hre : ∑ x, ((f (flipSet x {j}) - f (flipSet (flipSet x {j}) {k})) / 2) ^ 2
      = ∑ x, ((f x - f (flipSet x {k})) / 2) ^ 2 :=
    sum_flip j (fun x => ((f x - f (flipSet x {k})) / 2) ^ 2)
  unfold inflR
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc ∑ x, ((avg j f x - avg j f (flipSet x {k})) / 2) ^ 2
      ≤ ∑ x, (((f x - f (flipSet x {k})) / 2) ^ 2
          + ((f (flipSet x {j}) - f (flipSet (flipSet x {j}) {k})) / 2) ^ 2) / 2 :=
        Finset.sum_le_sum (fun x _ => hpt x)
    _ = ∑ x, ((f x - f (flipSet x {k})) / 2) ^ 2 := by
        rw [← Finset.sum_div, Finset.sum_add_distrib, hre]
        ring

/-- `L_k (avg j f) ≤ L_k f` for every `k`. -/
theorem meanAbsIncr_avg_le (j k : ι) (f : Cube ι → ℝ) :
    meanAbsIncr (avg j f) k ≤ meanAbsIncr f k := by
  have hcomm : ∀ x : Cube ι, flipSet (flipSet x {k}) {j} = flipSet (flipSet x {j}) {k} :=
    fun x => flipSet_comm x {k} {j}
  have hpt : ∀ x, |avg j f x - avg j f (flipSet x {k})|
      ≤ (|f x - f (flipSet x {k})|
        + |f (flipSet x {j}) - f (flipSet (flipSet x {j}) {k})|) / 2 := by
    intro x
    have e : avg j f x - avg j f (flipSet x {k})
        = ((f x - f (flipSet x {k}))
          + (f (flipSet x {j}) - f (flipSet (flipSet x {j}) {k}))) / 2 := by
      unfold avg
      rw [hcomm x]
      ring
    rw [e, abs_div, abs_two]
    exact div_le_div_of_nonneg_right (abs_add_le _ _) (by norm_num)
  have hre : ∑ x, |f (flipSet x {j}) - f (flipSet (flipSet x {j}) {k})|
      = ∑ x, |f x - f (flipSet x {k})| :=
    sum_flip j (fun x => |f x - f (flipSet x {k})|)
  unfold meanAbsIncr
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc ∑ x, |avg j f x - avg j f (flipSet x {k})|
      ≤ ∑ x, (|f x - f (flipSet x {k})|
          + |f (flipSet x {j}) - f (flipSet (flipSet x {j}) {k})|) / 2 :=
        Finset.sum_le_sum (fun x _ => hpt x)
    _ = ∑ x, |f x - f (flipSet x {k})| := by
        rw [← Finset.sum_div, Finset.sum_add_distrib, hre]
        ring

/-- `L_j (avg j f) = 0`. -/
theorem meanAbsIncr_avg_self (j : ι) (f : Cube ι → ℝ) : meanAbsIncr (avg j f) j = 0 := by
  unfold meanAbsIncr
  rw [Finset.sum_eq_zero (fun x _ => by rw [avg_flip, sub_self, abs_zero]), zero_div]

/-- Rows of `f` give rows of `avg j f` of the same cost. -/
theorem rows_avg (j : ι) {f : Cube ι → ℝ} {a : Cube ι → ι → ℝ} {K : ℝ}
    (ha : ∀ x i, 0 ≤ a x i) (hsum : ∀ x, ∑ i, a x i ≤ K)
    (hrow : ∀ x y, |f x - f y| ≤ ∑ i ∈ diffSet x y, a x i) :
    (∀ x i, 0 ≤ (a x i + a (flipSet x {j}) i) / 2) ∧
    (∀ x, ∑ i, (a x i + a (flipSet x {j}) i) / 2 ≤ K) ∧
    ∀ x y, |avg j f x - avg j f y| ≤ ∑ i ∈ diffSet x y, (a x i + a (flipSet x {j}) i) / 2 := by
  refine ⟨fun x i => div_nonneg (add_nonneg (ha x i) (ha _ i)) (by norm_num), fun x => ?_,
    fun x y => ?_⟩
  · rw [← Finset.sum_div, Finset.sum_add_distrib]
    linarith [hsum x, hsum (flipSet x {j})]
  · have h1 := hrow x y
    have h2 := hrow (flipSet x {j}) (flipSet y {j})
    rw [diffSet_flip] at h2
    have e : avg j f x - avg j f y
        = ((f x - f y) + (f (flipSet x {j}) - f (flipSet y {j}))) / 2 := by
      unfold avg
      ring
    rw [e, abs_div, abs_two, ← Finset.sum_div, Finset.sum_add_distrib]
    exact div_le_div_of_nonneg_right (le_trans (abs_add_le _ _) (add_le_add h1 h2))
      (by norm_num)

end Average
end AaronsonAmbainis

end
/- END UPSTREAM MODULE: AaronsonAmbainis.Average.Coordinate -/

/- BEGIN UPSTREAM MODULE: AaronsonAmbainis.Average.Iterate -/
section
/-!
# Averaging over a set of coordinates

`exists_avg_set` (Lemma 8.2 of the paper): let `f` have a row of cost at most `K` at every
point, and let `R` be a set of coordinates. Averaging `f` over the coordinates of `R`, one after
the other, gives a function `g` with rows of cost at most `K` such that

* `Var f ≤ Var g + ∑_{j ∈ R} Inf_j f`,
* `Inf_k g ≤ Inf_k f` and `L_k g ≤ L_k f` for every coordinate `k`,
* `L_j g = 0` for `j ∈ R`.

(`g` is the average of `f` over the coordinates in `R`, that is, the conditional expectation of
`f` given the coordinates outside `R`; only the listed properties are used, so the function is
not named.) Induction on `R` with the lemmas of `Coordinate.lean`.
-/

namespace AaronsonAmbainis
namespace Average

open Finset

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Averaging over the coordinates of a set `R` (Lemma 8.2 of the paper): a function `g` with
rows of the same cost, with `Var f ≤ Var g + ∑_{j ∈ R} Inf_j f`, with influences and mean
absolute increments not larger than those of `f`, and with `L_j g = 0` for `j ∈ R`. -/
theorem exists_avg_set (f : Cube ι → ℝ) (a : Cube ι → ι → ℝ) {K : ℝ} (ha : ∀ x i, 0 ≤ a x i)
    (hsum : ∀ x, ∑ i, a x i ≤ K) (hrow : ∀ x y, |f x - f y| ≤ ∑ i ∈ diffSet x y, a x i)
    (R : Finset ι) :
    ∃ (g : Cube ι → ℝ) (b : Cube ι → ι → ℝ),
      (∀ x i, 0 ≤ b x i) ∧ (∀ x, ∑ i, b x i ≤ K) ∧
      (∀ x y, |g x - g y| ≤ ∑ i ∈ diffSet x y, b x i) ∧
      variance f ≤ variance g + ∑ j ∈ R, inflR f j ∧
      (∀ k, inflR g k ≤ inflR f k) ∧ (∀ k, meanAbsIncr g k ≤ meanAbsIncr f k) ∧
      (∀ j ∈ R, meanAbsIncr g j = 0) := by
  induction R using Finset.induction_on with
  | empty =>
    refine ⟨f, a, ha, hsum, hrow, ?_, fun k => le_refl _, fun k => le_refl _,
      fun j hj => absurd hj (Finset.notMem_empty j)⟩
    rw [Finset.sum_empty, add_zero]
  | insert j R hjR ih =>
    obtain ⟨g, b, hb0, hbK, hbrow, hvar, hR2, hL1, hzero⟩ := ih
    obtain ⟨hb0', hbK', hbrow'⟩ := rows_avg j hb0 hbK hbrow
    refine ⟨avg j g, fun x i => (b x i + b (flipSet x {j}) i) / 2, hb0', hbK', hbrow',
      ?_, ?_, ?_, ?_⟩
    · rw [Finset.sum_insert hjR]
      have h1 := variance_avg j g
      have h2 := hR2 j
      linarith
    · intro k
      exact le_trans (inflR_avg_le j k g) (hR2 k)
    · intro k
      exact le_trans (meanAbsIncr_avg_le j k g) (hL1 k)
    · intro i hi
      rcases Finset.mem_insert.mp hi with h | hiR
      · rw [h]
        exact meanAbsIncr_avg_self j g
      · exact le_antisymm (le_trans (meanAbsIncr_avg_le j i g) (le_of_eq (hzero i hiR)))
          (Level.meanAbsIncr_nonneg _ _)

end Average
end AaronsonAmbainis

end
/- END UPSTREAM MODULE: AaronsonAmbainis.Average.Iterate -/

/- BEGIN UPSTREAM MODULE: AaronsonAmbainis.Average.Influence -/
section
/-!
# The influences of a function with rows of bounded cost

Let `f` have a row of cost at most `K` at every point and `V = Var f > 0`. Let
`L = L(f) = ∑_k L_k(f)` be the sum of the mean absolute increments (it is positive, by the bound
for the mean absolute increments) and `R = {j : 5 L · Inf_j f < 2 V · L_j f}` (the coordinates
whose influence is small compared with the mean absolute increment). Then
`∑_{j ∈ R} Inf_j f ≤ (2/5) V`, so the average `g` of `f` over the coordinates of `R`
(`Average.exists_avg_set`) has `Var g ≥ (3/5) V`. The bound for the mean absolute increments,
applied to `g`, gives `j` with `Var(g)^3 ≤ 36 K^4 L_j(g)²` and `L_j(g) > 0`; so `j ∉ R`, and
`2 V L_j(g) ≤ 2 V L_j(f) ≤ 5 L · Inf_j f`. Together (Theorem 8.3 of the paper):

`3 V^5 ≤ 3125 L(f)² K^4 (Inf_j f)²`
(`influence_of_meanIncrement : MeanIncrementBound → InfluenceBound`),

that is, `Inf_j f ≥ (√15 / 125) · V^{5/2} / (L(f) K²)`.

Further statements of this file:

* `Average.sum_meanAbsIncr_pos` — `L(f) > 0` (and `L(f) ≤ K` is
  `Level.sum_meanAbsIncr_le_cost`);
* `Average.influence_of_incr` — if `∑_j |f(u) - f(u^j)| ≤ G` at every point `u`, then
  `L(f) ≤ G` and `3 V^5 ≤ 3125 G² K^4 (Inf_j f)²`;
* `Average.influence_cost` — in particular, since `L(f) ≤ K`: `3 V^5 ≤ 3125 K^6 (Inf_j f)²`;
* `Average.exists_inflR_ge_sqrt` — the bound for the influences with the power `5/2` written as
  `V² · √V`: `√15 V^{5/2} ≤ 125 L(f) K² Inf_j f` (the two forms are equivalent:
  `Average.pow_le_iff_sqrt_mul_le`).
-/

namespace AaronsonAmbainis

open Finset

namespace Average

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The bound for the mean absolute increments, with the positivity of the increment that it
gives. -/
lemma exists_meanAbsIncr_pos (hMI : MeanIncrementBound) (g : Cube ι → ℝ) (b : Cube ι → ι → ℝ)
    {K : ℝ} (hb0 : ∀ x i, 0 ≤ b x i) (hbK : ∀ x, ∑ i, b x i ≤ K)
    (hbrow : ∀ x y, |g x - g y| ≤ ∑ i ∈ diffSet x y, b x i) (hg : 0 < variance g) :
    ∃ j, 0 < meanAbsIncr g j ∧ variance g ^ 3 ≤ 36 * K ^ 4 * meanAbsIncr g j ^ 2 := by
  obtain ⟨j, hj⟩ := hMI ι g K b hb0 hbK hbrow hg
  refine ⟨j, ?_, hj⟩
  by_contra h
  have h0 : meanAbsIncr g j = 0 := le_antisymm (not_lt.mp h) (Level.meanAbsIncr_nonneg g j)
  have h3 : 0 < variance g ^ 3 := pow_pos hg 3
  have e : 36 * K ^ 4 * (0 : ℝ) ^ 2 = 0 := by ring
  rw [h0, e] at hj
  linarith

/-- The sum `L(f)` of the mean absolute increments of a function with rows of cost at most `K`
and positive variance is positive. -/
lemma sum_meanAbsIncr_pos (hMI : MeanIncrementBound) (f : Cube ι → ℝ) (a : Cube ι → ι → ℝ)
    {K : ℝ} (ha : ∀ x i, 0 ≤ a x i) (hsum : ∀ x, ∑ i, a x i ≤ K)
    (hrow : ∀ x y, |f x - f y| ≤ ∑ i ∈ diffSet x y, a x i) (hvar : 0 < variance f) :
    0 < ∑ k, meanAbsIncr f k := by
  obtain ⟨j0, hj0, -⟩ := exists_meanAbsIncr_pos hMI f a ha hsum hrow hvar
  exact lt_of_lt_of_le hj0 (Finset.single_le_sum (f := meanAbsIncr f)
    (fun k _ => Level.meanAbsIncr_nonneg f k) (Finset.mem_univ j0))

end Average

/-- The bound for the influences (Theorem 8.3 of the paper) from the bound for the mean absolute
increments (Theorem 7.10): if `f` has a row of cost at most `K` at every point and `Var f > 0`,
then some coordinate `j` has `3 Var(f)^5 ≤ 3125 L(f)² K^4 (Inf_j f)²`, where
`L(f) = ∑_k L_k(f)`. -/
theorem influence_of_meanIncrement : MeanIncrementBound → InfluenceBound := by
  intro hMI ι _ _ f K a ha hsum hrow hvar
  classical
  -- the sum `L` of the mean absolute increments is positive
  have hLpos : 0 < ∑ k, meanAbsIncr f k :=
    Average.sum_meanAbsIncr_pos hMI f a ha hsum hrow hvar
  obtain ⟨V, hV⟩ : ∃ V : ℝ, V = variance f := ⟨_, rfl⟩
  obtain ⟨L, hLf⟩ : ∃ L : ℝ, L = ∑ k, meanAbsIncr f k := ⟨_, rfl⟩
  rw [← hV] at hvar
  rw [← hLf] at hLpos
  rw [← hV, ← hLf]
  -- the average over the coordinates of small influence
  obtain ⟨g, b, hb0, hbK, hbrow, hvarg, -, hL1, hzero⟩ := Average.exists_avg_set f a ha hsum hrow
    (univ.filter (fun j => 5 * L * inflR f j < 2 * V * meanAbsIncr f j))
  rw [← hV] at hvarg
  have h5 : 5 * L * ∑ j ∈ univ.filter (fun j => 5 * L * inflR f j < 2 * V * meanAbsIncr f j),
      inflR f j ≤ 2 * V * L := by
    rw [Finset.mul_sum]
    calc ∑ j ∈ univ.filter (fun j => 5 * L * inflR f j < 2 * V * meanAbsIncr f j),
          5 * L * inflR f j
        ≤ ∑ j ∈ univ.filter (fun j => 5 * L * inflR f j < 2 * V * meanAbsIncr f j),
          2 * V * meanAbsIncr f j :=
          Finset.sum_le_sum (fun j hj => (Finset.mem_filter.mp hj).2.le)
      _ ≤ ∑ j, 2 * V * meanAbsIncr f j :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun j _ _ => mul_nonneg (mul_nonneg (by norm_num) hvar.le)
              (Level.meanAbsIncr_nonneg f j))
      _ = 2 * V * L := by rw [← Finset.mul_sum, hLf]
  have hsumR : 5 * ∑ j ∈ univ.filter
      (fun j => 5 * L * inflR f j < 2 * V * meanAbsIncr f j), inflR f j ≤ 2 * V := by
    have h6 : L * (5 * ∑ j ∈ univ.filter
        (fun j => 5 * L * inflR f j < 2 * V * meanAbsIncr f j), inflR f j)
        ≤ L * (2 * V) := by linarith
    exact le_of_mul_le_mul_left h6 hLpos
  have hVg : 3 / 5 * V ≤ variance g := by linarith
  -- the bound for the mean absolute increments of the average
  obtain ⟨j, hgj, hj⟩ :=
    Average.exists_meanAbsIncr_pos hMI g b hb0 hbK hbrow (by linarith : 0 < variance g)
  refine ⟨j, ?_⟩
  have hjR : j ∉ univ.filter (fun j => 5 * L * inflR f j < 2 * V * meanAbsIncr f j) := by
    intro h
    rw [hzero j h] at hgj
    exact lt_irrefl 0 hgj
  have h4 : 2 * V * meanAbsIncr f j ≤ 5 * L * inflR f j := by
    by_contra h
    exact hjR (Finset.mem_filter.mpr ⟨Finset.mem_univ _, not_le.mp h⟩)
  have h2V : (0 : ℝ) ≤ 2 * V := by linarith
  have h7 : 2 * V * meanAbsIncr g j ≤ 5 * L * inflR f j :=
    le_trans (mul_le_mul_of_nonneg_left (hL1 j) h2V) h4
  have h8 : (2 * V * meanAbsIncr g j) ^ 2 ≤ (5 * L * inflR f j) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg h2V hgj.le) h7 2
  have h9 : (3 / 5 * V) ^ 3 ≤ 36 * K ^ 4 * meanAbsIncr g j ^ 2 :=
    le_trans (pow_le_pow_left₀ (by linarith) hVg 3) hj
  have hK4 : (0 : ℝ) ≤ 36 * K ^ 4 := by positivity
  calc 3 * V ^ 5 = 125 / 36 * ((3 / 5 * V) ^ 3 * (2 * V) ^ 2) := by ring
    _ ≤ 125 / 36 * (36 * K ^ 4 * meanAbsIncr g j ^ 2 * (2 * V) ^ 2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h9 (sq_nonneg _)) (by norm_num)
    _ = 125 / 36 * (36 * K ^ 4 * (2 * V * meanAbsIncr g j) ^ 2) := by ring
    _ ≤ 125 / 36 * (36 * K ^ 4 * (5 * L * inflR f j) ^ 2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h8 hK4) (by norm_num)
    _ = 3125 * L ^ 2 * K ^ 4 * inflR f j ^ 2 := by ring

namespace Average

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The bound for the influences with a bound `G` for the sums of the increments at the points:
`3 Var(f)^5 ≤ 3125 G² K^4 (Inf_j f)²`. -/
theorem influence_of_incr (hI : InfluenceBound) (f : Cube ι → ℝ) (a : Cube ι → ι → ℝ) {K G : ℝ}
    (ha : ∀ x i, 0 ≤ a x i) (hsum : ∀ x, ∑ i, a x i ≤ K)
    (hrow : ∀ x y, |f x - f y| ≤ ∑ i ∈ diffSet x y, a x i)
    (hG : ∀ u, ∑ j, |f u - f (flipSet u {j})| ≤ G) (hvar : 0 < variance f) :
    ∃ j, 3 * variance f ^ 5 ≤ 3125 * G ^ 2 * K ^ 4 * inflR f j ^ 2 := by
  obtain ⟨j, hj⟩ := hI ι f K a ha hsum hrow hvar
  refine ⟨j, le_trans hj ?_⟩
  have hL0 : 0 ≤ ∑ k, meanAbsIncr f k :=
    Finset.sum_nonneg fun k _ => Level.meanAbsIncr_nonneg f k
  have hL2 : (∑ k, meanAbsIncr f k) ^ 2 ≤ G ^ 2 :=
    pow_le_pow_left₀ hL0 (Level.sum_meanAbsIncr_le f hG) 2
  have hX : 0 ≤ K ^ 4 * inflR f j ^ 2 := by positivity
  have h := mul_le_mul_of_nonneg_right hL2 hX
  linarith

/-- The bound for the influences in terms of the cost alone: if `f` has a row of cost at most
`K` at every point and `Var f > 0`, then some coordinate `j` has
`3 Var(f)^5 ≤ 3125 K^6 (Inf_j f)²`. -/
theorem influence_cost (hI : InfluenceBound) (f : Cube ι → ℝ) (a : Cube ι → ι → ℝ) {K : ℝ}
    (ha : ∀ x i, 0 ≤ a x i) (hsum : ∀ x, ∑ i, a x i ≤ K)
    (hrow : ∀ x y, |f x - f y| ≤ ∑ i ∈ diffSet x y, a x i) (hvar : 0 < variance f) :
    ∃ j, 3 * variance f ^ 5 ≤ 3125 * K ^ 6 * inflR f j ^ 2 := by
  obtain ⟨j, hj⟩ := influence_of_incr hI f a ha hsum hrow
    (Level.sum_abs_incr_le_of_rows hsum hrow) hvar
  refine ⟨j, le_trans hj (le_of_eq ?_)⟩
  ring

/-- For `V, L, I ≥ 0`: `3 V^5 ≤ 3125 L² K^4 I²` if and only if `√15 V^{5/2} ≤ 125 L K² I`, where
`V^{5/2}` is written `V² · √V`. -/
theorem pow_le_iff_sqrt_mul_le {V L K I : ℝ} (hV : 0 ≤ V) (hL : 0 ≤ L) (hI : 0 ≤ I) :
    3 * V ^ 5 ≤ 3125 * L ^ 2 * K ^ 4 * I ^ 2
      ↔ Real.sqrt 15 * (V ^ 2 * Real.sqrt V) ≤ 125 * L * K ^ 2 * I := by
  have ha : 0 ≤ Real.sqrt 15 * (V ^ 2 * Real.sqrt V) := by positivity
  have hb : 0 ≤ 125 * L * K ^ 2 * I :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hL) (sq_nonneg K)) hI
  have e1 : (Real.sqrt 15 * (V ^ 2 * Real.sqrt V)) ^ 2 = 15 * V ^ 5 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 15), Real.sq_sqrt hV]
    ring
  have e2 : (125 * L * K ^ 2 * I) ^ 2 = 5 * (3125 * L ^ 2 * K ^ 4 * I ^ 2) := by ring
  constructor
  · intro h
    apply le_of_pow_le_pow_left₀ two_ne_zero hb
    rw [e1, e2]
    linarith
  · intro h
    have h2 := pow_le_pow_left₀ ha h 2
    rw [e1, e2] at h2
    linarith

/-- The bound for the influences with the power `5/2` written as `Var² · √Var`: some coordinate
`j` has `√15 Var(f)^{5/2} ≤ 125 L(f) K² Inf_j(f)`, that is,
`Inf_j(f) ≥ (√15 / 125) Var(f)^{5/2} / (L(f) K²)`, where `L(f) = ∑_k L_k(f)`. -/
theorem exists_inflR_ge_sqrt (hI : InfluenceBound) (f : Cube ι → ℝ) (a : Cube ι → ι → ℝ)
    {K : ℝ} (ha : ∀ x i, 0 ≤ a x i) (hsum : ∀ x, ∑ i, a x i ≤ K)
    (hrow : ∀ x y, |f x - f y| ≤ ∑ i ∈ diffSet x y, a x i) (hvar : 0 < variance f) :
    ∃ j, Real.sqrt 15 * (variance f ^ 2 * Real.sqrt (variance f))
      ≤ 125 * (∑ k, meanAbsIncr f k) * K ^ 2 * inflR f j := by
  obtain ⟨j, hj⟩ := hI ι f K a ha hsum hrow hvar
  exact ⟨j, (pow_le_iff_sqrt_mul_le hvar.le
    (Finset.sum_nonneg fun k _ => Level.meanAbsIncr_nonneg f k) (Level.inflR_nonneg f j)).mp hj⟩

end Average

end AaronsonAmbainis

end
/- END UPSTREAM MODULE: AaronsonAmbainis.Average.Influence -/

/- BEGIN UPSTREAM MODULE: AaronsonAmbainis.Average.Main -/
section
/-!
# Averaging over coordinates: from the mean absolute increments to the influences

Section 8 of the paper.

* `AaronsonAmbainis.influence_of_meanIncrement : MeanIncrementBound → InfluenceBound`
  (the bound for the influences of a function with rows of cost at most `K`, Theorem 8.3 of the
  paper, from the bound for the mean absolute increments, Theorem 7.10, applied to the average
  of the function over a set of coordinates; file `Influence.lean`, helpers in `Coordinate`,
  `Iterate`)
-/

end
/- END UPSTREAM MODULE: AaronsonAmbainis.Average.Main -/

/- BEGIN UPSTREAM MODULE: AaronsonAmbainis.RowDefs -/
section
/-!
# Interface for the proof of the row bound

The row bound of Agarwal and Ben-David (`RowBound` in `Statements.lean`) enters `Chain.lean`
as a named hypothesis. This file states the links of the proof of the row bound of the paper
(Section 6: cost at most `π² d²` for functions with values in `[-1,1]`, where the bound of
Agarwal and Ben-David gives `π² d² / 2`), which has no hypothesis:

* `MarkovEndpoint`  — A. A. Markov's inequality at an endpoint of the interval `[0,2]`
                      (Lemma 6.1);
* `BlockInequality` — the block inequality for a family of blocks in which every coordinate
                      lies in at most `N` blocks (Lemma 6.4);
* `PackingBound`    — the packing bound, for fractional packings (Lemma 6.5);
* `CoverDuality`    — linear-programming duality between packings and rows
                      (Proposition 6.7);
* `RowBoundPM`      — the row bound (Theorem 6.8).

Chain: `MarkovEndpoint → BlockInequality → PackingBound`, then
`PackingBound → CoverDuality → RowBoundPM`. The block inequality also gives `SensitivityBound`
(`Statements.lean`), and `RowBoundPM` and `SensitivityBound` enter the main theorem
(`MainTheorem.lean`).
-/

namespace AaronsonAmbainis

open Finset

/-- Markov's inequality at an endpoint: a real polynomial of degree at most `D` which is bounded
by `1` in absolute value on `[0,2]` has `|p'(0)| ≤ D²`. -/
def MarkovEndpoint : Prop :=
  ∀ (D : ℕ) (p : Polynomial ℝ), p.natDegree ≤ D →
    (∀ s : ℝ, 0 ≤ s → s ≤ 2 → |p.eval s| ≤ 1) → |p.derivative.eval 0| ≤ (D : ℝ) ^ 2

/-- The block inequality. `f` is bounded by `1` and has degree at most `d`; `S b` (`b : β`) is a
finite family of blocks such that every coordinate lies in at most `N` blocks; `m ≥ 1` satisfies
`N (1 - cos (π / m)) ≤ 2`. Then `∑_b |f(x) - f(x^{S b})| ≤ 4 d² m²`. -/
def BlockInequality : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (d : ℕ) (f : Cube ι → ℝ), (∀ x, |f x| ≤ 1) →
    HasDegreeLE f d →
  ∀ (x : Cube ι) (β : Type) [Fintype β] (S : β → Finset ι) (N m : ℕ), 0 < m →
    (∀ i, (univ.filter fun b : β => i ∈ S b).card ≤ N) →
    (N : ℝ) * (1 - Real.cos (Real.pi / (m : ℝ))) ≤ 2 →
    ∑ b, |f x - f (flipSet x (S b))| ≤ 4 * (d : ℝ) ^ 2 * (m : ℝ) ^ 2

/-- The packing bound. `f` is bounded by `1` and has degree at most `d`. If `κ ≥ 0` and
`∑_{S ∋ i} κ_S ≤ 1` for every coordinate `i`, then `∑_S κ_S |f(x) - f(x^S)| ≤ π² d²`. -/
def PackingBound : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (d : ℕ) (f : Cube ι → ℝ), (∀ x, |f x| ≤ 1) →
    HasDegreeLE f d →
  ∀ (x : Cube ι) (κ : Finset ι → ℝ), (∀ S, 0 ≤ κ S) →
    (∀ i, ∑ S ∈ univ.filter (fun S : Finset ι => i ∈ S), κ S ≤ 1) →
    ∑ S, κ S * |f x - f (flipSet x S)| ≤ Real.pi ^ 2 * (d : ℝ) ^ 2

/-- Duality between packings and rows: if every fractional packing `κ` has `∑_S κ_S t_S ≤ K`,
then there is a vector `a ≥ 0` of total mass at most `K` with `t_S ≤ a(S)` for every `S`.
(The hypotheses `0 ≤ K` and `t ∅ ≤ 0` follow from the hypothesis on packings: take `κ = 0`,
and take `κ` with `κ_∅` arbitrarily large and `κ_S = 0` for `S ≠ ∅`.) -/
def CoverDuality : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (t : Finset ι → ℝ) (K : ℝ), 0 ≤ K → t ∅ ≤ 0 →
    (∀ κ : Finset ι → ℝ, (∀ S, 0 ≤ κ S) →
        (∀ i, ∑ S ∈ univ.filter (fun S : Finset ι => i ∈ S), κ S ≤ 1) →
        ∑ S, κ S * t S ≤ K) →
    ∃ a : ι → ℝ, (∀ i, 0 ≤ a i) ∧ ∑ i, a i ≤ K ∧ ∀ S : Finset ι, t S ≤ ∑ i ∈ S, a i

/-- The row bound (Theorem 6.8 of the paper): a function with values in `[-1,1]` and of
degree at most `d` has, at every point, a row of cost at most `π² d²`. -/
def RowBoundPM : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (d : ℕ) (f : Cube ι → ℝ), (∀ x, |f x| ≤ 1) →
    HasDegreeLE f d →
    ∃ a : Cube ι → ι → ℝ, (∀ x i, 0 ≤ a x i) ∧
      (∀ x, ∑ i, a x i ≤ Real.pi ^ 2 * (d : ℝ) ^ 2) ∧
      ∀ x y, |f x - f y| ≤ ∑ i ∈ diffSet x y, a x i

end AaronsonAmbainis

end
/- END UPSTREAM MODULE: AaronsonAmbainis.RowDefs -/

/- BEGIN UPSTREAM MODULE: AaronsonAmbainis.Row.Markov -/
section
/-!
# Markov's inequality at an endpoint

This file proves `markovEndpoint : MarkovEndpoint`: a real polynomial `p` of degree at most `D`
with `|p| ≤ 1` on `[0,2]` satisfies `|p'(0)| ≤ D²`. This is the second assertion of Lemma 6.1 of
the paper. The paper proves the lemma directly, by interpolation at the points `cos (k π / D)`;
here the assertion is deduced from Mathlib's extremal property of the Chebyshev polynomials
(`Polynomial.Chebyshev.eval_iterate_derivative_le_of_forall_abs_le_one`, with `k = 1`, `x = 1`),
applied to `p.comp (1 - X)` and to its negative.
-/

namespace AaronsonAmbainis
namespace Row

open Polynomial

/-- One-sided form: `-p'(0) ≤ D²` if `|p| ≤ 1` on `[0,2]` and `natDegree p ≤ D`. -/
theorem neg_derivative_eval_zero_le (D : ℕ) (p : ℝ[X]) (hdeg : p.natDegree ≤ D)
    (hbnd : ∀ s : ℝ, 0 ≤ s → s ≤ 2 → |p.eval s| ≤ 1) :
    -(p.derivative.eval 0) ≤ (D : ℝ) ^ 2 := by
  have h1X : (1 - X : ℝ[X]).natDegree ≤ 1 :=
    (natDegree_sub_le _ _).trans (by simp)
  have hnat : (p.comp (1 - X)).natDegree ≤ D :=
    calc (p.comp (1 - X)).natDegree ≤ p.natDegree * (1 - X : ℝ[X]).natDegree := natDegree_comp_le
      _ ≤ p.natDegree * 1 := Nat.mul_le_mul_left _ h1X
      _ ≤ D := by simpa using hdeg
  have hP : (p.comp (1 - X)).degree ≤ (D : WithBot ℕ) := degree_le_of_natDegree_le hnat
  have hb : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |(p.comp (1 - X)).eval x| ≤ 1 := by
    intro x hx
    rw [eval_comp]
    simp only [eval_sub, eval_one, eval_X]
    exact hbnd (1 - x) (by linarith [hx.2]) (by linarith [hx.1])
  have h := Chebyshev.eval_iterate_derivative_le_of_forall_abs_le_one (k := 1) (x := 1)
    le_rfl hP hb
  simp only [Function.iterate_one] at h
  rw [derivative_comp_one_sub_X, Chebyshev.derivative_T_eval_one] at h
  simpa using h

end Row

open Polynomial in
/-- Markov's inequality at the endpoint `0` of `[0,2]`. -/
theorem markovEndpoint : MarkovEndpoint := by
  intro D p hdeg hbnd
  have h1 := Row.neg_derivative_eval_zero_le D p hdeg hbnd
  have h2 := Row.neg_derivative_eval_zero_le D (-p) (by simpa using hdeg)
    (fun s hs0 hs2 => by simpa using hbnd s hs0 hs2)
  rw [derivative_neg, eval_neg, neg_neg] at h2
  exact abs_le.mpr ⟨by linarith, h2⟩

end AaronsonAmbainis

end
/- END UPSTREAM MODULE: AaronsonAmbainis.Row.Markov -/

/- BEGIN UPSTREAM MODULE: AaronsonAmbainis.Row.Chi -/
section
/-!
# Characters at special points

`Row.sgn b = (-1)^b`, the all-false point `Row.zero`, the unit points `Row.unit b`, the value of a
character at these points and at a flipped point, and `chi S * chi T = chi (S ∆ T)`.

Since `false` stands for `+1` and `true` for `-1`, the point `Row.zero β` is the point `(1,…,1)` of
Section 6.3 of the paper, and `Row.unit b` is obtained from it by changing the sign of the
coordinate `b`.
-/

namespace AaronsonAmbainis
namespace Row

open Finset

/-- The sign `(-1)^b` of a bit. -/
noncomputable def sgn (b : Bool) : ℝ := if b then -1 else 1

@[simp] lemma sgn_true : sgn true = -1 := by simp [sgn]

@[simp] lemma sgn_false : sgn false = 1 := by simp [sgn]

lemma sgn_mul_self (b : Bool) : sgn b * sgn b = 1 := by cases b <;> simp

lemma abs_sgn (b : Bool) : |sgn b| = 1 := by cases b <;> simp

lemma sgn_not (b : Bool) : sgn (!b) = -sgn b := by cases b <;> simp

/-- The all-false point of a cube. -/
def zero (β : Type*) : Cube β := fun _ => false

/-- The point with exactly the coordinate `b` equal to `true`. -/
def unit {β : Type*} [DecidableEq β] (b : β) : Cube β := fun b' => decide (b' = b)

variable {ι : Type*}

lemma chi_eq_prod_sgn (T : Finset ι) (x : Cube ι) : chi T x = ∏ i ∈ T, sgn (x i) := rfl

lemma chi_zero (U : Finset ι) : chi U (zero ι) = 1 := by
  simp [chi, zero]

lemma chi_unit [DecidableEq ι] (U : Finset ι) (b : ι) :
    chi U (unit b) = if b ∈ U then -1 else 1 := by
  simp [chi, unit, Finset.prod_ite_eq']

/-- The sign of a coordinate of a flipped point. -/
lemma sgn_flipSet [DecidableEq ι] (x : Cube ι) (U : Finset ι) (i : ι) :
    sgn (flipSet x U i) = sgn (x i) * (if i ∈ U then -1 else 1) := by
  by_cases h : i ∈ U <;> simp [flipSet, h, sgn_not]

/-- The character at a flipped point. -/
lemma chi_flipSet [DecidableEq ι] (T U : Finset ι) (x : Cube ι) :
    chi T (flipSet x U) = ∏ i ∈ T, (sgn (x i) * (if i ∈ U then -1 else 1)) := by
  rw [chi_eq_prod_sgn]
  exact Finset.prod_congr rfl (fun i _ => sgn_flipSet x U i)

/-- Characters multiply by symmetric difference. -/
lemma chi_mul_chi [Fintype ι] [DecidableEq ι] (S T : Finset ι) (x : Cube ι) :
    chi S x * chi T x = chi (symmDiff S T) x := by
  rw [chi_eq_prod_sgn, chi_eq_prod_sgn, chi_eq_prod_sgn,
    ← Fintype.prod_ite_mem S (fun i => sgn (x i)), ← Fintype.prod_ite_mem T (fun i => sgn (x i)),
    ← Fintype.prod_ite_mem (symmDiff S T) (fun i => sgn (x i)), ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;>
    simp [Finset.mem_symmDiff, hS, hT, sgn_mul_self]

end Row
end AaronsonAmbainis

end
/- END UPSTREAM MODULE: AaronsonAmbainis.Row.Chi -/

/- BEGIN UPSTREAM MODULE: AaronsonAmbainis.Row.Extension -/
section
/-!
# Bounded multilinear extension

Lemma 6.2 (Extension) of the paper, `Row.abs_multilinear_le_one`: if `∑_T a_T chi_T` is bounded
by `1` in absolute value on the cube, then `∑_T a_T ∏_{i ∈ T} u_i` is bounded by `1` for every
real vector `u` with `|u_i| ≤ 1`. The proof averages over the product measure `weight u`.
-/

namespace AaronsonAmbainis
namespace Row

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The product weight `W_u(z) = ∏_i (1 + sgn(z_i) u_i) / 2`. -/
noncomputable def weight (u : ι → ℝ) (z : Cube ι) : ℝ := ∏ i, (1 + sgn (z i) * u i) / 2

omit [DecidableEq ι] in
lemma weight_nonneg (u : ι → ℝ) (hu : ∀ i, |u i| ≤ 1) (z : Cube ι) : 0 ≤ weight u z := by
  refine Finset.prod_nonneg (fun i _ => ?_)
  have h1 : |sgn (z i) * u i| ≤ 1 := by
    rw [abs_mul, abs_sgn, one_mul]
    exact hu i
  have h2 := abs_le.mp h1
  linarith [h2.1]

/-- The `weight u`-average of the character `chi T` is `∏_{i ∈ T} u_i`. -/
lemma sum_weight_mul_chi (u : ι → ℝ) (T : Finset ι) :
    ∑ z : Cube ι, weight u z * chi T z = ∏ i ∈ T, u i := by
  have h1 : ∀ z : Cube ι, weight u z * chi T z
      = ∏ i, ((1 + sgn (z i) * u i) / 2 * (if i ∈ T then sgn (z i) else 1)) := by
    intro z
    rw [Finset.prod_mul_distrib, Fintype.prod_ite_mem T (fun i => sgn (z i))]
    rfl
  have h2 : ∑ z : Cube ι, ∏ i, ((1 + sgn (z i) * u i) / 2 * (if i ∈ T then sgn (z i) else 1))
      = ∏ i, ∑ b : Bool, ((1 + sgn b * u i) / 2 * (if i ∈ T then sgn b else 1)) :=
    (Fintype.prod_sum
      (fun i (b : Bool) => (1 + sgn b * u i) / 2 * (if i ∈ T then sgn b else 1))).symm
  rw [Finset.sum_congr rfl (fun z _ => h1 z), h2, ← Fintype.prod_ite_mem T u]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [Fintype.sum_bool]
  by_cases hi : i ∈ T <;> simp [hi] <;> ring

lemma sum_weight (u : ι → ℝ) : ∑ z : Cube ι, weight u z = 1 := by
  have h := sum_weight_mul_chi u (∅ : Finset ι)
  simpa [chi] using h

/-- Bounded multilinear extension (Lemma 6.2 of the paper). -/
theorem abs_multilinear_le_one (a : Finset ι → ℝ)
    (h : ∀ z : Cube ι, |∑ T, a T * chi T z| ≤ 1) (u : ι → ℝ) (hu : ∀ i, |u i| ≤ 1) :
    |∑ T, a T * ∏ i ∈ T, u i| ≤ 1 := by
  have key : ∑ T, a T * ∏ i ∈ T, u i = ∑ z : Cube ι, weight u z * ∑ T, a T * chi T z := by
    calc ∑ T, a T * ∏ i ∈ T, u i
        = ∑ T, a T * ∑ z : Cube ι, weight u z * chi T z := by
          refine Finset.sum_congr rfl (fun T _ => ?_)
          rw [sum_weight_mul_chi]
      _ = ∑ T, ∑ z : Cube ι, weight u z * (a T * chi T z) := by
          refine Finset.sum_congr rfl (fun T _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun z _ => ?_)
          ring
      _ = ∑ z : Cube ι, ∑ T, weight u z * (a T * chi T z) := Finset.sum_comm
      _ = ∑ z : Cube ι, weight u z * ∑ T, a T * chi T z := by
          refine Finset.sum_congr rfl (fun z _ => ?_)
          rw [Finset.mul_sum]
  rw [key]
  calc |∑ z : Cube ι, weight u z * ∑ T, a T * chi T z|
      ≤ ∑ z : Cube ι, |weight u z * ∑ T, a T * chi T z| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ z : Cube ι, weight u z := by
        refine Finset.sum_le_sum (fun z _ => ?_)
        rw [abs_mul, abs_of_nonneg (weight_nonneg u hu z)]
        exact mul_le_of_le_one_right (weight_nonneg u hu z) (h z)
    _ = 1 := sum_weight u

end Row
end AaronsonAmbainis

end
/- END UPSTREAM MODULE: AaronsonAmbainis.Row.Extension -/

/- BEGIN UPSTREAM MODULE: AaronsonAmbainis.Row.Sensitivity -/
section
/-!
# The sensitivity lemma

Lemma 6.3 (Sensitivity) of the paper, `Row.sum_abs_sub_unit_le`: if `G` on a cube is bounded by
`1` and has degree at most `D`, then `∑_b |G(0) - G(e_b)| ≤ 4 D²`. Here `0 = Row.zero β` and
`e_b = Row.unit b` are the points `(1,…,1)` and `(1,…,1)^b` of the paper. Markov's inequality at
an endpoint enters as the hypothesis `MarkovEndpoint`, which is proved in `Row/Markov.lean`.
-/

namespace AaronsonAmbainis
namespace Row

open Finset Polynomial

/-- If every partial sum of `d` is bounded by `K` in absolute value, then `∑ |d| ≤ 2 K`. -/
lemma sum_abs_le_of_abs_sum_le {β : Type*} [Fintype β] (d : β → ℝ) (K : ℝ)
    (h : ∀ R : Finset β, |∑ b ∈ R, d b| ≤ K) : ∑ b, |d b| ≤ 2 * K := by
  have hA : ∑ b ∈ univ.filter (fun b => 0 ≤ d b), |d b|
      = ∑ b ∈ univ.filter (fun b => 0 ≤ d b), d b :=
    Finset.sum_congr rfl (fun b hb => abs_of_nonneg (Finset.mem_filter.mp hb).2)
  have hB : ∑ b ∈ univ.filter (fun b => ¬ 0 ≤ d b), |d b|
      = -∑ b ∈ univ.filter (fun b => ¬ 0 ≤ d b), d b := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun b hb => abs_of_neg (not_le.mp (Finset.mem_filter.mp hb).2))
  have hsplit := Finset.sum_filter_add_sum_filter_not univ (fun b => 0 ≤ d b) (fun b => |d b|)
  have h1 := (abs_le.mp (h (univ.filter (fun b => 0 ≤ d b)))).2
  have h2 := (abs_le.mp (h (univ.filter (fun b => ¬ 0 ≤ d b)))).1
  linarith

variable {β : Type*} [Fintype β] [DecidableEq β]

/-- The restriction polynomial `φ_R(s) = ∑_U g_U (1 - s)^{|U ∩ R|}`. -/
noncomputable def phi (g : Finset β → ℝ) (R : Finset β) : ℝ[X] :=
  ∑ U : Finset β, C (g U) * (1 - X) ^ (U ∩ R).card

lemma natDegree_phi_le (g : Finset β → ℝ) (R : Finset β) (D : ℕ)
    (hg : ∀ U : Finset β, D < U.card → g U = 0) : (phi g R).natDegree ≤ D := by
  refine natDegree_sum_le_of_forall_le _ _ (fun U _ => ?_)
  by_cases hU : U.card ≤ D
  · have h1X : (1 - X : ℝ[X]).natDegree ≤ 1 := (natDegree_sub_le _ _).trans (by simp)
    calc (C (g U) * (1 - X) ^ (U ∩ R).card).natDegree
        ≤ ((1 - X : ℝ[X]) ^ (U ∩ R).card).natDegree := natDegree_C_mul_le _ _
      _ ≤ (U ∩ R).card * (1 - X : ℝ[X]).natDegree := natDegree_pow_le
      _ ≤ (U ∩ R).card * 1 := Nat.mul_le_mul_left _ h1X
      _ ≤ D := by
          rw [mul_one]
          exact (Finset.card_le_card Finset.inter_subset_left).trans hU
  · rw [hg U (not_le.mp hU)]
    simp

lemma eval_phi (g : Finset β → ℝ) (R : Finset β) (s : ℝ) :
    (phi g R).eval s = ∑ U : Finset β, g U * ∏ b ∈ U, (if b ∈ R then 1 - s else 1) := by
  unfold phi
  rw [eval_finsetSum]
  refine Finset.sum_congr rfl (fun U _ => ?_)
  rw [eval_mul, eval_C, eval_pow, eval_sub, eval_one, eval_X, Finset.prod_ite_mem,
    Finset.prod_const]

lemma derivative_phi_eval_zero (g : Finset β → ℝ) (R : Finset β) :
    (phi g R).derivative.eval 0 = -∑ U : Finset β, g U * ((U ∩ R).card : ℝ) := by
  unfold phi
  rw [derivative_sum, eval_finsetSum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun U _ => ?_)
  rw [derivative_C_mul, derivative_pow, derivative_sub, derivative_one, derivative_X]
  simp only [eval_mul, eval_C, eval_pow, eval_sub, eval_one, eval_X, eval_zero, sub_zero,
    one_pow]
  ring

/-- `∑_{b ∈ R} (G(0) - G(e_b)) = 2 ∑_U g_U |U ∩ R|` for `G = ∑_U g_U chi_U`. -/
lemma sum_sub_unit (g : Finset β → ℝ) (R : Finset β) :
    ∑ b ∈ R, ((∑ U : Finset β, g U * chi U (zero β)) - ∑ U : Finset β, g U * chi U (unit b))
      = 2 * ∑ U : Finset β, g U * ((U ∩ R).card : ℝ) := by
  have h1 : ∀ b : β,
      (∑ U : Finset β, g U * chi U (zero β)) - ∑ U : Finset β, g U * chi U (unit b)
        = ∑ U : Finset β, g U * (if b ∈ U then 2 else 0) := by
    intro b
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun U _ => ?_)
    rw [chi_zero, chi_unit]
    split_ifs <;> ring
  have h2 : ∀ U : Finset β, ∑ b ∈ R, (if b ∈ U then (2 : ℝ) else 0) = 2 * ((U ∩ R).card : ℝ) := by
    intro U
    rw [Finset.sum_ite_mem, Finset.sum_const, Finset.inter_comm, nsmul_eq_mul]
    ring
  rw [Finset.sum_congr rfl (fun b _ => h1 b), Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun U _ => ?_)
  rw [← Finset.mul_sum, h2 U]
  ring

/-- For every set `R` of coordinates, `|∑_{b ∈ R} (G(0) - G(e_b))| ≤ 2 D²`. -/
lemma abs_sum_sub_unit_le (hM : MarkovEndpoint) (G : Cube β → ℝ) (D : ℕ)
    (hG : ∀ w, |G w| ≤ 1) (hdeg : HasDegreeLE G D) (R : Finset β) :
    |∑ b ∈ R, (G (zero β) - G (unit b))| ≤ 2 * (D : ℝ) ^ 2 := by
  obtain ⟨g, hg, hGg⟩ := hdeg
  have hbound : ∀ s : ℝ, 0 ≤ s → s ≤ 2 → |(phi g R).eval s| ≤ 1 := by
    intro s hs0 hs2
    rw [eval_phi]
    refine abs_multilinear_le_one g (fun z => ?_) (fun b => if b ∈ R then 1 - s else 1)
      (fun b => ?_)
    · rw [← hGg z]
      exact hG z
    · split_ifs
      · rw [abs_le]
        constructor <;> linarith
      · simp
  have hmark := hM D (phi g R) (natDegree_phi_le g R D hg) hbound
  rw [derivative_phi_eval_zero, abs_neg] at hmark
  have hsum : ∑ b ∈ R, (G (zero β) - G (unit b))
      = 2 * ∑ U : Finset β, g U * ((U ∩ R).card : ℝ) := by
    rw [← sum_sub_unit g R]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [hGg (zero β), hGg (unit b)]
  rw [hsum, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  linarith

/-- The sensitivity lemma (Lemma 6.3 of the paper), given Markov's inequality at an endpoint. -/
theorem sum_abs_sub_unit_le (hM : MarkovEndpoint) (G : Cube β → ℝ) (D : ℕ)
    (hG : ∀ w, |G w| ≤ 1) (hdeg : HasDegreeLE G D) :
    ∑ b, |G (zero β) - G (unit b)| ≤ 4 * (D : ℝ) ^ 2 := by
  have h := sum_abs_le_of_abs_sum_le (fun b => G (zero β) - G (unit b)) (2 * (D : ℝ) ^ 2)
    (fun R => abs_sum_sub_unit_le hM G D hG hdeg R)
  linarith

end Row
end AaronsonAmbainis

end
/- END UPSTREAM MODULE: AaronsonAmbainis.Row.Sensitivity -/

/- BEGIN UPSTREAM MODULE: AaronsonAmbainis.Row.Degree -/
section
/-!
# Degree calculus for `HasDegreeLE`

Rules for the predicate `HasDegreeLE` of `Defs.lean`: characters, constants, sums, constant
multiples, monotonicity in the bound, products (the degrees add), powers, finite products, a real
polynomial of a function of degree at most `1`, and the indicator of a coordinate. They serve
step (b) of the proof of the block inequality (Lemma 6.4 of the paper): the function `G`
constructed there has degree at most `d m` (`Row.hasDegreeLE_gadget` in `Row/Gadget.lean`).
-/

namespace AaronsonAmbainis
namespace Row

open Finset

variable {β : Type*} [Fintype β]

lemma hasDegreeLE_congr {f g : Cube β → ℝ} {k : ℕ} (h : HasDegreeLE f k)
    (hfg : ∀ w, g w = f w) : HasDegreeLE g k := by
  obtain ⟨c, hc, hf⟩ := h
  exact ⟨c, hc, fun w => (hfg w).trans (hf w)⟩

lemma hasDegreeLE_chi (S : Finset β) {k : ℕ} (h : S.card ≤ k) : HasDegreeLE (chi S) k := by
  classical
  refine ⟨fun T => if T = S then 1 else 0, fun T hT => ?_, fun w => ?_⟩
  · have hne : T ≠ S := by
      rintro rfl
      omega
    simp [hne]
  · simp

lemma hasDegreeLE_zero (k : ℕ) : HasDegreeLE (fun _ : Cube β => (0 : ℝ)) k :=
  ⟨fun _ => 0, fun _ _ => rfl, fun w => by simp⟩

lemma hasDegreeLE_add {f g : Cube β → ℝ} {k : ℕ} (hf : HasDegreeLE f k) (hg : HasDegreeLE g k) :
    HasDegreeLE (fun w => f w + g w) k := by
  obtain ⟨c, hc, hf⟩ := hf
  obtain ⟨c', hc', hg⟩ := hg
  refine ⟨fun T => c T + c' T, fun T hT => by simp [hc T hT, hc' T hT], fun w => ?_⟩
  show f w + g w = ∑ T, (c T + c' T) * chi T w
  rw [hf w, hg w, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun T _ => by ring)

lemma hasDegreeLE_const_mul (a : ℝ) {f : Cube β → ℝ} {k : ℕ} (hf : HasDegreeLE f k) :
    HasDegreeLE (fun w => a * f w) k := by
  obtain ⟨c, hc, hf⟩ := hf
  refine ⟨fun T => a * c T, fun T hT => by simp [hc T hT], fun w => ?_⟩
  show a * f w = ∑ T, a * c T * chi T w
  rw [hf w, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun T _ => by ring)

lemma hasDegreeLE_const (a : ℝ) (k : ℕ) : HasDegreeLE (fun _ : Cube β => a) k := by
  have h := hasDegreeLE_const_mul a (hasDegreeLE_chi (∅ : Finset β) (Nat.zero_le k))
  exact hasDegreeLE_congr h (fun w => by simp [chi])

lemma hasDegreeLE_sum {α : Type*} (s : Finset α) (F : α → Cube β → ℝ) {k : ℕ}
    (h : ∀ j ∈ s, HasDegreeLE (F j) k) : HasDegreeLE (fun w => ∑ j ∈ s, F j w) k := by
  classical
  induction s using Finset.induction_on with
  | empty => exact hasDegreeLE_congr (hasDegreeLE_zero k) (fun w => by simp)
  | insert j s hj ih =>
    have h1 := hasDegreeLE_add (h j (Finset.mem_insert_self j s))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))
    exact hasDegreeLE_congr h1 (fun w => by rw [Finset.sum_insert hj])

lemma hasDegreeLE_mono {f : Cube β → ℝ} {k l : ℕ} (hkl : k ≤ l) (hf : HasDegreeLE f k) :
    HasDegreeLE f l := by
  obtain ⟨c, hc, hf⟩ := hf
  exact ⟨c, fun T hT => hc T (lt_of_le_of_lt hkl hT), hf⟩

/-- Products add degrees. -/
lemma hasDegreeLE_mul {f g : Cube β → ℝ} {k l : ℕ} (hf : HasDegreeLE f k)
    (hg : HasDegreeLE g l) : HasDegreeLE (fun w => f w * g w) (k + l) := by
  classical
  obtain ⟨c, hc, hf⟩ := hf
  obtain ⟨c', hc', hg⟩ := hg
  have key : HasDegreeLE (fun w => ∑ S ∈ (univ : Finset (Finset β)),
      ∑ T ∈ (univ : Finset (Finset β)), c S * c' T * chi (symmDiff S T) w) (k + l) := by
    apply hasDegreeLE_sum
    intro S _
    apply hasDegreeLE_sum
    intro T _
    by_cases hST : S.card ≤ k ∧ T.card ≤ l
    · refine hasDegreeLE_const_mul _ (hasDegreeLE_chi _ ?_)
      have hsub : symmDiff S T ⊆ S ∪ T := by
        intro i hi
        rw [Finset.mem_symmDiff] at hi
        rw [Finset.mem_union]
        tauto
      calc (symmDiff S T).card ≤ (S ∪ T).card := Finset.card_le_card hsub
        _ ≤ S.card + T.card := Finset.card_union_le S T
        _ ≤ k + l := Nat.add_le_add hST.1 hST.2
    · have h0 : c S * c' T = 0 := by
        rcases not_and_or.mp hST with h | h
        · rw [hc S (not_le.mp h), zero_mul]
        · rw [hc' T (not_le.mp h), mul_zero]
      exact hasDegreeLE_congr (hasDegreeLE_zero _) (fun w => by rw [h0, zero_mul])
  refine hasDegreeLE_congr key (fun w => ?_)
  show f w * g w = ∑ S, ∑ T, c S * c' T * chi (symmDiff S T) w
  rw [hf w, hg w, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun S _ => Finset.sum_congr rfl (fun T _ => ?_))
  rw [← chi_mul_chi]
  ring

lemma hasDegreeLE_pow {f : Cube β → ℝ} {k : ℕ} (hf : HasDegreeLE f k) (n : ℕ) :
    HasDegreeLE (fun w => f w ^ n) (n * k) := by
  induction n with
  | zero => exact hasDegreeLE_congr (hasDegreeLE_const 1 _) (fun w => by simp)
  | succ n ih =>
    have h := hasDegreeLE_mul ih hf
    have h' : n * k + k = (n + 1) * k := by ring
    rw [← h']
    exact hasDegreeLE_congr h (fun w => by rw [pow_succ])

lemma hasDegreeLE_prod {α : Type*} (s : Finset α) (F : α → Cube β → ℝ) {k : ℕ}
    (h : ∀ j ∈ s, HasDegreeLE (F j) k) :
    HasDegreeLE (fun w => ∏ j ∈ s, F j w) (s.card * k) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact hasDegreeLE_congr (hasDegreeLE_const 1 _) (fun w => by simp)
  | insert j s hj ih =>
    have h1 := hasDegreeLE_mul (h j (Finset.mem_insert_self j s))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))
    have h' : k + s.card * k = (insert j s).card * k := by
      rw [Finset.card_insert_of_notMem hj]
      ring
    rw [← h']
    exact hasDegreeLE_congr h1 (fun w => by rw [Finset.prod_insert hj])

/-- A real polynomial of a function of degree at most `1` has degree at most its `natDegree`. -/
lemma hasDegreeLE_polyEval (Q : Polynomial ℝ) {g : Cube β → ℝ} (hg : HasDegreeLE g 1) :
    HasDegreeLE (fun w => Q.eval (g w)) Q.natDegree := by
  have key : HasDegreeLE
      (fun w => ∑ n ∈ Finset.range (Q.natDegree + 1), Q.coeff n * g w ^ n) Q.natDegree := by
    apply hasDegreeLE_sum
    intro n hn
    refine hasDegreeLE_const_mul _ (hasDegreeLE_mono ?_ (hasDegreeLE_pow hg n))
    have := Finset.mem_range.mp hn
    omega
  exact hasDegreeLE_congr key (fun w => Polynomial.eval_eq_sum_range (g w))

/-- The indicator of a coordinate has degree at most `1`. -/
lemma hasDegreeLE_indicator (b : β) :
    HasDegreeLE (fun w : Cube β => if w b then (1 : ℝ) else 0) 1 := by
  have h1 : HasDegreeLE (fun w : Cube β => 1 / 2 + (-1 / 2) * chi {b} w) 1 :=
    hasDegreeLE_add (hasDegreeLE_const _ _)
      (hasDegreeLE_const_mul _ (hasDegreeLE_chi {b} (by simp)))
  refine hasDegreeLE_congr h1 (fun w => ?_)
  cases h : w b <;> simp [chi, h] <;> norm_num

end Row
end AaronsonAmbainis

end
/- END UPSTREAM MODULE: AaronsonAmbainis.Row.Degree -/

/- BEGIN UPSTREAM MODULE: AaronsonAmbainis.Row.Gadget -/
section
/-!
# The Chebyshev gadget

The function `G` of the proof of the block inequality (Lemma 6.4 of the paper).
For blocks `S b ⊆ ι` (`b : β`), a point `x` and coefficients `a_T`:
`cnt S i w = #{b : i ∈ S b, w b = true}`, `gate S m c i w = T_m (1 - c * cnt S i w)` and
`gadget a x S m c w = ∑_T a_T ∏_{i ∈ T} (sgn (x i) * gate S m c i w)`.
In the paper these are written `cnt_i(w)`, `θ_i(w)` and `G(w)`.

The lemmas `abs_gadget_le_one`, `hasDegreeLE_gadget`, `gadget_zero` and `gadget_unit` are the
properties (a)–(d) of `G` in that proof, each under the hypotheses it needs: `G` is bounded by
`1`, it has degree at most `d * m`, and it takes the value `∑_T a_T chi_T(x)` at `Row.zero β` and,
for `m ≥ 1` and `c = 1 - cos (π / m)`, the value `∑_T a_T chi_T(x^{S b})` at `Row.unit b`.
-/

namespace AaronsonAmbainis
namespace Row

open Finset Polynomial

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {β : Type*} [Fintype β]

/-- `cnt_i(w)`: the number of blocks `b ∋ i` with `w b = true`, as a real number. -/
noncomputable def cnt (S : β → Finset ι) (i : ι) (w : Cube β) : ℝ :=
  ∑ b ∈ univ.filter (fun b : β => i ∈ S b), (if w b then (1 : ℝ) else 0)

/-- `θ_i(w) = T_m (1 - c cnt_i(w))`. -/
noncomputable def gate (S : β → Finset ι) (m : ℕ) (c : ℝ) (i : ι) (w : Cube β) : ℝ :=
  (Chebyshev.T ℝ m).eval (1 - c * cnt S i w)

/-- `G(w) = ∑_T a_T ∏_{i ∈ T} (sgn (x i) θ_i(w))`. -/
noncomputable def gadget (a : Finset ι → ℝ) (x : Cube ι) (S : β → Finset ι) (m : ℕ) (c : ℝ)
    (w : Cube β) : ℝ :=
  ∑ T : Finset ι, a T * ∏ i ∈ T, (sgn (x i) * gate S m c i w)

omit [Fintype ι] in
lemma cnt_nonneg (S : β → Finset ι) (i : ι) (w : Cube β) : 0 ≤ cnt S i w := by
  unfold cnt
  refine Finset.sum_nonneg (fun b _ => ?_)
  split_ifs <;> norm_num

omit [Fintype ι] in
lemma cnt_le (S : β → Finset ι) (N : ℕ)
    (hN : ∀ i, (univ.filter fun b : β => i ∈ S b).card ≤ N) (i : ι) (w : Cube β) :
    cnt S i w ≤ N := by
  unfold cnt
  calc ∑ b ∈ univ.filter (fun b : β => i ∈ S b), (if w b then (1 : ℝ) else 0)
      ≤ ∑ b ∈ univ.filter (fun b : β => i ∈ S b), (1 : ℝ) := by
        refine Finset.sum_le_sum (fun b _ => ?_)
        split_ifs <;> norm_num
    _ = ((univ.filter fun b : β => i ∈ S b).card : ℝ) := by simp
    _ ≤ N := by exact_mod_cast hN i

omit [Fintype ι] in
lemma cnt_zero (S : β → Finset ι) (i : ι) : cnt S i (zero β) = 0 := by
  simp [cnt, zero]

omit [Fintype ι] in
lemma cnt_unit [DecidableEq β] (S : β → Finset ι) (i : ι) (b : β) :
    cnt S i (unit b) = if i ∈ S b then 1 else 0 := by
  simp [cnt, unit]

omit [Fintype ι] in
lemma hasDegreeLE_cnt (S : β → Finset ι) (i : ι) : HasDegreeLE (cnt S i) 1 :=
  hasDegreeLE_congr
    (hasDegreeLE_sum (univ.filter (fun b : β => i ∈ S b))
      (fun b w => if w b then (1 : ℝ) else 0) (fun b _ => hasDegreeLE_indicator b))
    (fun _ => rfl)

omit [Fintype ι] in
lemma abs_gate_le_one (S : β → Finset ι) (N m : ℕ) (c : ℝ) (hc : 0 ≤ c)
    (hN : ∀ i, (univ.filter fun b : β => i ∈ S b).card ≤ N) (hNc : (N : ℝ) * c ≤ 2)
    (i : ι) (w : Cube β) : |gate S m c i w| ≤ 1 := by
  unfold gate
  have h0 := cnt_nonneg S i w
  have h1 := cnt_le S N hN i w
  have h2 : c * cnt S i w ≤ c * N := mul_le_mul_of_nonneg_left h1 hc
  have h3 : 0 ≤ c * cnt S i w := mul_nonneg hc h0
  exact Chebyshev.abs_eval_T_real_le_one _ (abs_le.mpr ⟨by linarith, by linarith⟩)

omit [Fintype ι] in
lemma hasDegreeLE_gate (S : β → Finset ι) (m : ℕ) (c : ℝ) (i : ι) :
    HasDegreeLE (gate S m c i) m := by
  have h1 : HasDegreeLE (fun w : Cube β => 1 + (-c) * cnt S i w) 1 :=
    hasDegreeLE_add (hasDegreeLE_const 1 1) (hasDegreeLE_const_mul (-c) (hasDegreeLE_cnt S i))
  have h2 := hasDegreeLE_polyEval (Chebyshev.T ℝ (m : ℤ)) h1
  have h3 : (Chebyshev.T ℝ (m : ℤ)).natDegree = m := by
    rw [Chebyshev.natDegree_T]
    simp
  rw [h3] at h2
  refine hasDegreeLE_congr h2 (fun w => ?_)
  unfold gate
  congr 1
  ring

omit [Fintype ι] in
lemma gate_zero (S : β → Finset ι) (m : ℕ) (c : ℝ) (i : ι) : gate S m c i (zero β) = 1 := by
  unfold gate
  rw [cnt_zero, mul_zero, sub_zero, Chebyshev.T_eval_one]

omit [Fintype ι] in
lemma gate_unit [DecidableEq β] (S : β → Finset ι) (m : ℕ) (hm : 0 < m) (i : ι) (b : β) :
    gate S m (1 - Real.cos (Real.pi / (m : ℝ))) i (unit b) = if i ∈ S b then -1 else 1 := by
  unfold gate
  rw [cnt_unit]
  split_ifs with h
  · have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
    have harg : ((m : ℤ) : ℝ) * (Real.pi / (m : ℝ)) = Real.pi := by
      push_cast
      field_simp
    rw [mul_one, sub_sub_cancel, Chebyshev.T_real_cos, harg, Real.cos_pi]
  · rw [mul_zero, sub_zero, Chebyshev.T_eval_one]

lemma abs_gadget_le_one (a : Finset ι → ℝ) (ha : ∀ z : Cube ι, |∑ T, a T * chi T z| ≤ 1)
    (x : Cube ι) (S : β → Finset ι) (N m : ℕ) (c : ℝ) (hc : 0 ≤ c)
    (hN : ∀ i, (univ.filter fun b : β => i ∈ S b).card ≤ N) (hNc : (N : ℝ) * c ≤ 2)
    (w : Cube β) : |gadget a x S m c w| ≤ 1 := by
  refine abs_multilinear_le_one a ha (fun i => sgn (x i) * gate S m c i w) (fun i => ?_)
  rw [abs_mul, abs_sgn, one_mul]
  exact abs_gate_le_one S N m c hc hN hNc i w

lemma hasDegreeLE_gadget (a : Finset ι → ℝ) (d : ℕ) (ha : ∀ T : Finset ι, d < T.card → a T = 0)
    (x : Cube ι) (S : β → Finset ι) (m : ℕ) (c : ℝ) :
    HasDegreeLE (gadget a x S m c) (d * m) := by
  have key : HasDegreeLE (fun w : Cube β => ∑ T ∈ (univ : Finset (Finset ι)),
      a T * ∏ i ∈ T, (sgn (x i) * gate S m c i w)) (d * m) := by
    apply hasDegreeLE_sum
    intro T _
    by_cases hT : T.card ≤ d
    · refine hasDegreeLE_const_mul _ (hasDegreeLE_mono (Nat.mul_le_mul_right m hT) ?_)
      exact hasDegreeLE_prod T (fun i w => sgn (x i) * gate S m c i w)
        (fun i _ => hasDegreeLE_const_mul _ (hasDegreeLE_gate S m c i))
    · exact hasDegreeLE_congr (hasDegreeLE_zero _)
        (fun w => by simp [ha T (not_le.mp hT)])
  exact hasDegreeLE_congr key (fun _ => rfl)

lemma gadget_zero (a : Finset ι → ℝ) (x : Cube ι) (S : β → Finset ι) (m : ℕ) (c : ℝ) :
    gadget a x S m c (zero β) = ∑ T, a T * chi T x := by
  unfold gadget
  refine Finset.sum_congr rfl (fun T _ => ?_)
  rw [chi_eq_prod_sgn]
  congr 1
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [gate_zero, mul_one]

lemma gadget_unit [DecidableEq β] (a : Finset ι → ℝ) (x : Cube ι) (S : β → Finset ι) (m : ℕ)
    (hm : 0 < m) (b : β) :
    gadget a x S m (1 - Real.cos (Real.pi / (m : ℝ))) (unit b)
      = ∑ T, a T * chi T (flipSet x (S b)) := by
  unfold gadget
  refine Finset.sum_congr rfl (fun T _ => ?_)
  rw [chi_flipSet]
  congr 1
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [gate_unit S m hm]

end Row
end AaronsonAmbainis

end
/- END UPSTREAM MODULE: AaronsonAmbainis.Row.Gadget -/

/- BEGIN UPSTREAM MODULE: AaronsonAmbainis.Row.Block -/
section
/-!
# The block inequality from Markov's inequality

`blockInequality_of_markov : MarkovEndpoint → BlockInequality` is the block inequality (Lemma 6.4
of the paper), with Markov's inequality at an endpoint as a hypothesis.

The gadget `G = Row.gadget a x S m c` with `c = 1 - cos (π / m)` is bounded by `1`, has degree at
most `d * m`, and satisfies `G(0) = f x`, `G(e_b) = f (flipSet x (S b))`; the sensitivity lemma
(`Row.sum_abs_sub_unit_le`) then gives the bound `4 (d m)²`.
-/

namespace AaronsonAmbainis

open Finset

/-- The block inequality, given Markov's inequality at an endpoint. -/
theorem blockInequality_of_markov : MarkovEndpoint → BlockInequality := by
  intro hM ι _ _ d f hf hdeg x β _ S N m hm hN hNc
  classical
  obtain ⟨a, ha, hfa⟩ := hdeg
  have hc : (0 : ℝ) ≤ 1 - Real.cos (Real.pi / (m : ℝ)) := by
    linarith [Real.cos_le_one (Real.pi / (m : ℝ))]
  have hbd : ∀ z : Cube ι, |∑ T, a T * chi T z| ≤ 1 := fun z => by
    rw [← hfa z]
    exact hf z
  have key := Row.sum_abs_sub_unit_le hM
    (Row.gadget a x S m (1 - Real.cos (Real.pi / (m : ℝ)))) (d * m)
    (Row.abs_gadget_le_one a hbd x S N m _ hc hN hNc)
    (Row.hasDegreeLE_gadget a d ha x S m _)
  have hterm : ∀ b : β, |f x - f (flipSet x (S b))|
      = |Row.gadget a x S m (1 - Real.cos (Real.pi / (m : ℝ))) (Row.zero β)
          - Row.gadget a x S m (1 - Real.cos (Real.pi / (m : ℝ))) (Row.unit b)| := by
    intro b
    rw [Row.gadget_zero, Row.gadget_unit a x S m hm b, ← hfa x, ← hfa (flipSet x (S b))]
  rw [Finset.sum_congr rfl (fun b _ => hterm b)]
  calc ∑ b, |Row.gadget a x S m (1 - Real.cos (Real.pi / (m : ℝ))) (Row.zero β)
          - Row.gadget a x S m (1 - Real.cos (Real.pi / (m : ℝ))) (Row.unit b)|
      ≤ 4 * ((d * m : ℕ) : ℝ) ^ 2 := key
    _ = 4 * (d : ℝ) ^ 2 * (m : ℝ) ^ 2 := by
        push_cast
        ring

end AaronsonAmbainis

end
/- END UPSTREAM MODULE: AaronsonAmbainis.Row.Block -/

/- BEGIN UPSTREAM MODULE: AaronsonAmbainis.Row.Main -/
section
/-!
# The block inequality

`blockInequality : BlockInequality` is the block inequality (Lemma 6.4 of the paper). It follows
from `blockInequality_of_markov` (`Row/Block.lean`) and `markovEndpoint` (`Row/Markov.lean`).
-/

namespace AaronsonAmbainis

/-- The block inequality (`BlockInequality` of `RowDefs.lean`). -/
theorem blockInequality : BlockInequality := blockInequality_of_markov markovEndpoint

end AaronsonAmbainis

end
/- END UPSTREAM MODULE: AaronsonAmbainis.Row.Main -/

/- BEGIN UPSTREAM MODULE: AaronsonAmbainis.Row.DisjointBlocks -/
section
/-!
# Pairwise disjoint blocks, and the sensitivity at every point

For pairwise disjoint blocks the block inequality (`BlockInequality`, Lemma 6.4 of the paper)
applies with `N = 1` and `m = 1`, where `1 - cos (π / 1) = 2`, and gives the bound `4 d²`
(`Row.disjoint_blocks_of_block`). For the blocks `{j}` this is the sensitivity bound at every
point (Corollary 6.10 of the paper), `∑_j |f(x) - f(x^j)| ≤ 4 d²`
(`sensitivity_of_block : BlockInequality → SensitivityBound`).
-/

namespace AaronsonAmbainis

open Finset

namespace Row

/-- For pairwise disjoint blocks `S b`, `∑_b |f(x) - f(x^{S b})| ≤ 4 d²`. -/
theorem disjoint_blocks_of_block (hBlock : BlockInequality) (ι : Type) [Fintype ι]
    [DecidableEq ι] (d : ℕ) (f : Cube ι → ℝ) (hf : ∀ x, |f x| ≤ 1) (hdeg : HasDegreeLE f d)
    (x : Cube ι) (β : Type) [Fintype β] (S : β → Finset ι)
    (hS : ∀ b b' : β, b ≠ b' → Disjoint (S b) (S b')) :
    ∑ b, |f x - f (flipSet x (S b))| ≤ 4 * (d : ℝ) ^ 2 := by
  have hN : ∀ i, (univ.filter fun b : β => i ∈ S b).card ≤ 1 := by
    intro i
    rw [Finset.card_le_one]
    intro b hb b' hb'
    by_contra hne
    exact Finset.disjoint_left.mp (hS b b' hne) (Finset.mem_filter.mp hb).2
      (Finset.mem_filter.mp hb').2
  have hc : ((1 : ℕ) : ℝ) * (1 - Real.cos (Real.pi / ((1 : ℕ) : ℝ))) ≤ 2 := by
    rw [Nat.cast_one, div_one, Real.cos_pi]
    norm_num
  have h := hBlock ι d f hf hdeg x β S 1 1 Nat.one_pos hN hc
  simpa using h

end Row

/-- The sensitivity bound at every point (Corollary 6.10 of the paper), from the block inequality
(Lemma 6.4): the blocks `{j}` are pairwise disjoint. -/
theorem sensitivity_of_block : BlockInequality → SensitivityBound := by
  intro hBlock ι _ _ d f hf hdeg x
  exact Row.disjoint_blocks_of_block hBlock ι d f hf hdeg x ι (fun j => {j})
    (fun b b' hne => Finset.disjoint_singleton.mpr hne)

end AaronsonAmbainis

end
/- END UPSTREAM MODULE: AaronsonAmbainis.Row.DisjointBlocks -/

/- BEGIN UPSTREAM MODULE: AaronsonAmbainis.Pack.Gate -/
section
/-!
# The Chebyshev gate parameters

For `N = M ^ 2` (the bound for the number of blocks through a coordinate) and `m = ⌈π M / 2⌉₊`,
this file proves the three numerical facts used in the proof of the packing bound (Lemma 6.5 of
the paper):

* `gate_pos` : `0 < m` (for `M ≥ 1`);
* `gate_cos` : `N (1 - cos (π / m)) ≤ 2` (for `M ≥ 1`);
* `gate_sq`  : `4 m² ≤ (π M + 2)²`.
-/

namespace AaronsonAmbainis.Pack

/-- `m = ⌈π M / 2⌉₊` is positive when `M` is. -/
theorem gate_pos (M : ℕ) (hM : 0 < M) : 0 < ⌈Real.pi * (M : ℝ) / 2⌉₊ := by
  have hMr : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hM
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  exact Nat.ceil_pos.mpr (div_pos (mul_pos hpi hMr) two_pos)

/-- The hypothesis `N (1 - cos (π / m)) ≤ 2` of the block inequality for `N = M ^ 2` and
`m = ⌈π M / 2⌉₊`. -/
theorem gate_cos (M : ℕ) (hM : 0 < M) :
    ((M ^ 2 : ℕ) : ℝ) * (1 - Real.cos (Real.pi / ((⌈Real.pi * (M : ℝ) / 2⌉₊ : ℕ) : ℝ))) ≤ 2 := by
  have hMr : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hM
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  -- abbreviate the real number `m`
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = ((⌈Real.pi * (M : ℝ) / 2⌉₊ : ℕ) : ℝ) := ⟨_, rfl⟩
  rw [← hm]
  have hle : Real.pi * (M : ℝ) / 2 ≤ m := by
    rw [hm]; exact Nat.le_ceil _
  have hmpos : (0 : ℝ) < m := lt_of_lt_of_le (div_pos (mul_pos hpi hMr) two_pos) hle
  -- the cosine bound
  have hcos : 1 - (Real.pi / m) ^ 2 / 2 ≤ Real.cos (Real.pi / m) :=
    Real.one_sub_sq_div_two_le_cos
  have h1 : 1 - Real.cos (Real.pi / m) ≤ (Real.pi / m) ^ 2 / 2 := by linarith
  -- `M π / m ≤ 2`
  have h3 : (M : ℝ) * Real.pi / m ≤ 2 := by
    rw [div_le_iff₀ hmpos]; linarith
  have h4 : 0 ≤ (M : ℝ) * Real.pi / m :=
    div_nonneg (mul_nonneg hMr.le hpi.le) hmpos.le
  have h5 : ((M : ℝ) * Real.pi / m) ^ 2 ≤ 2 ^ 2 := pow_le_pow_left₀ h4 h3 2
  have h6 : (M : ℝ) ^ 2 * ((Real.pi / m) ^ 2 / 2) = ((M : ℝ) * Real.pi / m) ^ 2 / 2 := by
    ring
  have hM2 : (0 : ℝ) ≤ (M : ℝ) ^ 2 := sq_nonneg _
  have hcast : ((M ^ 2 : ℕ) : ℝ) = (M : ℝ) ^ 2 := by push_cast; ring
  rw [hcast]
  calc (M : ℝ) ^ 2 * (1 - Real.cos (Real.pi / m))
      ≤ (M : ℝ) ^ 2 * ((Real.pi / m) ^ 2 / 2) := mul_le_mul_of_nonneg_left h1 hM2
    _ = ((M : ℝ) * Real.pi / m) ^ 2 / 2 := h6
    _ ≤ 2 := by linarith

/-- `4 m² ≤ (π M + 2)²` for `m = ⌈π M / 2⌉₊`. -/
theorem gate_sq (M : ℕ) :
    4 * (((⌈Real.pi * (M : ℝ) / 2⌉₊ : ℕ) : ℝ)) ^ 2 ≤ (Real.pi * (M : ℝ) + 2) ^ 2 := by
  have hMr : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have h0 : (0 : ℝ) ≤ Real.pi * (M : ℝ) / 2 := div_nonneg (mul_nonneg hpi.le hMr) two_pos.le
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = ((⌈Real.pi * (M : ℝ) / 2⌉₊ : ℕ) : ℝ) := ⟨_, rfl⟩
  rw [← hm]
  have hlt : m < Real.pi * (M : ℝ) / 2 + 1 := by
    rw [hm]; exact Nat.ceil_lt_add_one h0
  have hm0 : (0 : ℝ) ≤ m := by
    rw [hm]; exact Nat.cast_nonneg _
  have h2 : 2 * m ≤ Real.pi * (M : ℝ) + 2 := by linarith
  have h3 : (2 * m) ^ 2 ≤ (Real.pi * (M : ℝ) + 2) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg two_pos.le hm0) h2 2
  calc 4 * m ^ 2 = (2 * m) ^ 2 := by ring
    _ ≤ (Real.pi * (M : ℝ) + 2) ^ 2 := h3

end AaronsonAmbainis.Pack

end
/- END UPSTREAM MODULE: AaronsonAmbainis.Pack.Gate -/

/- BEGIN UPSTREAM MODULE: AaronsonAmbainis.Pack.Blocks -/
section
/-!
# The block family of an integer packing

Given multiplicities `k S : ℕ` (`S : Finset ι`), the block family is indexed by
`Σ S : Finset ι, Fin (k S)` with block map `b ↦ b.1`: the set `S` occurs `k S` times.
It is the list of blocks used in the proof of the packing bound (Lemma 6.5 of the paper).

* `card_blocks` : the number of blocks containing `i` is `∑_{S ∋ i} k S`;
* `sum_blocks`  : a sum over the family of a function of the block is `∑_S k S * g S`.
-/

namespace AaronsonAmbainis.Pack

open Finset

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The number of blocks of the family `Σ S, Fin (k S)` which contain `i`. -/
theorem card_blocks (k : Finset ι → ℕ) (i : ι) :
    (univ.filter fun b : (Σ S : Finset ι, Fin (k S)) => i ∈ b.1).card
      = ∑ S ∈ univ.filter (fun S : Finset ι => i ∈ S), k S := by
  rw [Finset.card_filter, Fintype.sum_sigma, Finset.sum_filter]
  refine Finset.sum_congr rfl fun S _ => ?_
  by_cases h : i ∈ S
  · simp [h]
  · simp [h]

omit [DecidableEq ι] in
/-- A sum over the family `Σ S, Fin (k S)` of a function of the block. -/
theorem sum_blocks (k : Finset ι → ℕ) (g : Finset ι → ℝ) :
    ∑ b : (Σ S : Finset ι, Fin (k S)), g b.1 = ∑ S, (k S : ℝ) * g S := by
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun S _ => ?_
  show ∑ _y : Fin (k S), g S = (k S : ℝ) * g S
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end AaronsonAmbainis.Pack

end
/- END UPSTREAM MODULE: AaronsonAmbainis.Pack.Blocks -/

/- BEGIN UPSTREAM MODULE: AaronsonAmbainis.Pack.Scaled -/
section
/-!
# The packing bound before the limit

`scaled_bound`: from the block inequality, for a fractional packing `κ` and every natural number
`M ≥ 1`,
`M² ∑_S κ_S |f x - f (x^S)| ≤ d² (π M + 2)² + ∑_S |f x - f (x^S)|`.
This is the inequality `M² Λ ≤ d² (π M + 2)² + C₀` in the proof of the packing bound (Lemma 6.5 of
the paper).

Proof: `N = M²`, `k S = ⌊N κ S⌋₊`, block family `Σ S, Fin (k S)`, `m = ⌈π M / 2⌉₊`.
-/

namespace AaronsonAmbainis.Pack

open Finset

/-- For `k S = ⌊N κ S⌋₊` and a fractional packing `κ`, every coordinate lies in at most `N`
blocks of the family `Σ S, Fin (k S)`. -/
theorem card_blocks_le {ι : Type} [Fintype ι] [DecidableEq ι] (κ : Finset ι → ℝ)
    (hκ : ∀ S, 0 ≤ κ S)
    (hpack : ∀ i, ∑ S ∈ univ.filter (fun S : Finset ι => i ∈ S), κ S ≤ 1) (N : ℕ) (i : ι) :
    (univ.filter fun b : (Σ S : Finset ι, Fin ⌊(N : ℝ) * κ S⌋₊) => i ∈ b.1).card ≤ N := by
  have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  rw [card_blocks (fun S : Finset ι => ⌊(N : ℝ) * κ S⌋₊) i]
  have hreal : ((∑ S ∈ univ.filter (fun S : Finset ι => i ∈ S), ⌊(N : ℝ) * κ S⌋₊ : ℕ) : ℝ)
      ≤ (N : ℝ) := by
    rw [Nat.cast_sum]
    calc ∑ S ∈ univ.filter (fun S : Finset ι => i ∈ S), ((⌊(N : ℝ) * κ S⌋₊ : ℕ) : ℝ)
        ≤ ∑ S ∈ univ.filter (fun S : Finset ι => i ∈ S), (N : ℝ) * κ S :=
          Finset.sum_le_sum fun S _ => Nat.floor_le (mul_nonneg hN (hκ S))
      _ = (N : ℝ) * ∑ S ∈ univ.filter (fun S : Finset ι => i ∈ S), κ S := by
          rw [Finset.mul_sum]
      _ ≤ (N : ℝ) * 1 := mul_le_mul_of_nonneg_left (hpack i) hN
      _ = (N : ℝ) := mul_one _
  exact Nat.cast_le.mp hreal

/-- The packing bound before the limit, from the block inequality with `N = M ^ 2` and
`m = ⌈π M / 2⌉₊`. -/
theorem scaled_bound (hB : BlockInequality) (ι : Type) [Fintype ι] [DecidableEq ι] (d : ℕ)
    (f : Cube ι → ℝ) (hf : ∀ x, |f x| ≤ 1) (hd : HasDegreeLE f d) (x : Cube ι)
    (κ : Finset ι → ℝ) (hκ : ∀ S, 0 ≤ κ S)
    (hpack : ∀ i, ∑ S ∈ univ.filter (fun S : Finset ι => i ∈ S), κ S ≤ 1)
    (M : ℕ) (hM : 0 < M) :
    (M : ℝ) ^ 2 * ∑ S, κ S * |f x - f (flipSet x S)|
      ≤ (d : ℝ) ^ 2 * (Real.pi * (M : ℝ) + 2) ^ 2 + ∑ S, |f x - f (flipSet x S)| := by
  -- the block inequality for the family `Σ S, Fin ⌊M² κ S⌋₊` and `m = ⌈π M / 2⌉₊`
  have hblock := hB ι d f hf hd x (Σ S : Finset ι, Fin ⌊((M ^ 2 : ℕ) : ℝ) * κ S⌋₊)
    (fun b => b.1) (M ^ 2) ⌈Real.pi * (M : ℝ) / 2⌉₊ (gate_pos M hM)
    (card_blocks_le κ hκ hpack (M ^ 2)) (gate_cos M hM)
  rw [sum_blocks (fun S : Finset ι => ⌊((M ^ 2 : ℕ) : ℝ) * κ S⌋₊)
    (fun S : Finset ι => |f x - f (flipSet x S)|)] at hblock
  have hcast : ((M ^ 2 : ℕ) : ℝ) = (M : ℝ) ^ 2 := by push_cast; ring
  have hd2 : (0 : ℝ) ≤ (d : ℝ) ^ 2 := sq_nonneg _
  -- the right side of the block inequality
  have hright : 4 * (d : ℝ) ^ 2 * (((⌈Real.pi * (M : ℝ) / 2⌉₊ : ℕ) : ℝ)) ^ 2
      ≤ (d : ℝ) ^ 2 * (Real.pi * (M : ℝ) + 2) ^ 2 := by
    calc 4 * (d : ℝ) ^ 2 * (((⌈Real.pi * (M : ℝ) / 2⌉₊ : ℕ) : ℝ)) ^ 2
        = (d : ℝ) ^ 2 * (4 * (((⌈Real.pi * (M : ℝ) / 2⌉₊ : ℕ) : ℝ)) ^ 2) := by ring
      _ ≤ (d : ℝ) ^ 2 * (Real.pi * (M : ℝ) + 2) ^ 2 :=
          mul_le_mul_of_nonneg_left (gate_sq M) hd2
  -- termwise: `M² κ S < ⌊M² κ S⌋₊ + 1`
  have hterm : ∀ S : Finset ι, (M : ℝ) ^ 2 * (κ S * |f x - f (flipSet x S)|)
      ≤ ((⌊((M ^ 2 : ℕ) : ℝ) * κ S⌋₊ : ℕ) : ℝ) * |f x - f (flipSet x S)|
        + |f x - f (flipSet x S)| := by
    intro S
    have hlt : ((M ^ 2 : ℕ) : ℝ) * κ S < ((⌊((M ^ 2 : ℕ) : ℝ) * κ S⌋₊ : ℕ) : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    have habs : (0 : ℝ) ≤ |f x - f (flipSet x S)| := abs_nonneg _
    calc (M : ℝ) ^ 2 * (κ S * |f x - f (flipSet x S)|)
        = (((M ^ 2 : ℕ) : ℝ) * κ S) * |f x - f (flipSet x S)| := by rw [hcast]; ring
      _ ≤ (((⌊((M ^ 2 : ℕ) : ℝ) * κ S⌋₊ : ℕ) : ℝ) + 1) * |f x - f (flipSet x S)| :=
          mul_le_mul_of_nonneg_right hlt.le habs
      _ = ((⌊((M ^ 2 : ℕ) : ℝ) * κ S⌋₊ : ℕ) : ℝ) * |f x - f (flipSet x S)|
            + |f x - f (flipSet x S)| := by ring
  calc (M : ℝ) ^ 2 * ∑ S, κ S * |f x - f (flipSet x S)|
      = ∑ S, (M : ℝ) ^ 2 * (κ S * |f x - f (flipSet x S)|) := by rw [Finset.mul_sum]
    _ ≤ ∑ S, (((⌊((M ^ 2 : ℕ) : ℝ) * κ S⌋₊ : ℕ) : ℝ) * |f x - f (flipSet x S)|
          + |f x - f (flipSet x S)|) := Finset.sum_le_sum fun S _ => hterm S
    _ = ∑ S, ((⌊((M ^ 2 : ℕ) : ℝ) * κ S⌋₊ : ℕ) : ℝ) * |f x - f (flipSet x S)|
          + ∑ S, |f x - f (flipSet x S)| := Finset.sum_add_distrib
    _ ≤ (d : ℝ) ^ 2 * (Real.pi * (M : ℝ) + 2) ^ 2 + ∑ S, |f x - f (flipSet x S)| :=
        add_le_add (hblock.trans hright) le_rfl

end AaronsonAmbainis.Pack

end
/- END UPSTREAM MODULE: AaronsonAmbainis.Pack.Scaled -/

/- BEGIN UPSTREAM MODULE: AaronsonAmbainis.Pack.Packing -/
section
/-!
# From the block inequality to the bound for fractional packings

`AaronsonAmbainis.packingBound_of_block : BlockInequality → PackingBound`: the packing bound
(Lemma 6.5 of the paper) follows from the block inequality (Lemma 6.4). This file contains the
limit `M → ∞` (`Pack.le_of_scaled`); the inequality for a fixed `M` is `Pack.scaled_bound` in
`Pack/Scaled.lean`.
-/

namespace AaronsonAmbainis.Pack

/-- The limit step: if `M² L ≤ d² (π M + 2)² + C` for every natural `M ≥ 1`, then
`L ≤ π² d²`. -/
theorem le_of_scaled (L C : ℝ) (d : ℕ)
    (key : ∀ M : ℕ, 0 < M → (M : ℝ) ^ 2 * L ≤ (d : ℝ) ^ 2 * (Real.pi * (M : ℝ) + 2) ^ 2 + C) :
    L ≤ Real.pi ^ 2 * (d : ℝ) ^ 2 := by
  by_contra hcon
  have hεpos : 0 < L - Real.pi ^ 2 * (d : ℝ) ^ 2 := by linarith [not_le.mp hcon]
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hd2 : (0 : ℝ) ≤ (d : ℝ) ^ 2 := sq_nonneg _
  -- `C ≥ 0` is not assumed; `|C|` is used instead
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 4 * (d : ℝ) ^ 2 * Real.pi + 4 * (d : ℝ) ^ 2 + |C| := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by
    rw [hK]
    have h1 : (0 : ℝ) ≤ 4 * (d : ℝ) ^ 2 * Real.pi :=
      mul_nonneg (mul_nonneg (by norm_num) hd2) hpi.le
    have h2 : (0 : ℝ) ≤ 4 * (d : ℝ) ^ 2 := mul_nonneg (by norm_num) hd2
    linarith [abs_nonneg C]
  obtain ⟨M, hMgt⟩ := exists_nat_gt (K / (L - Real.pi ^ 2 * (d : ℝ) ^ 2))
  have hMr : (0 : ℝ) < (M : ℝ) := lt_of_le_of_lt (div_nonneg hK0 hεpos.le) hMgt
  have hMpos : 0 < M := Nat.cast_pos.mp hMr
  have hM1 : (1 : ℝ) ≤ (M : ℝ) := Nat.one_le_cast.mpr hMpos
  have h1 := key M hMpos
  -- `M² ε ≤ 4 d² π M + 4 d² + C`
  have h2 : (M : ℝ) ^ 2 * (L - Real.pi ^ 2 * (d : ℝ) ^ 2)
      ≤ 4 * (d : ℝ) ^ 2 * Real.pi * (M : ℝ) + 4 * (d : ℝ) ^ 2 + C := by
    have hexp : (d : ℝ) ^ 2 * (Real.pi * (M : ℝ) + 2) ^ 2 + C
        = (M : ℝ) ^ 2 * (Real.pi ^ 2 * (d : ℝ) ^ 2)
          + (4 * (d : ℝ) ^ 2 * Real.pi * (M : ℝ) + 4 * (d : ℝ) ^ 2 + C) := by ring
    rw [hexp] at h1
    calc (M : ℝ) ^ 2 * (L - Real.pi ^ 2 * (d : ℝ) ^ 2)
        = (M : ℝ) ^ 2 * L - (M : ℝ) ^ 2 * (Real.pi ^ 2 * (d : ℝ) ^ 2) := by ring
      _ ≤ 4 * (d : ℝ) ^ 2 * Real.pi * (M : ℝ) + 4 * (d : ℝ) ^ 2 + C := by linarith
  -- `4 d² π M + 4 d² + C ≤ K M` because `M ≥ 1`
  have h3 : 4 * (d : ℝ) ^ 2 * Real.pi * (M : ℝ) + 4 * (d : ℝ) ^ 2 + C ≤ K * (M : ℝ) := by
    have ha : 4 * (d : ℝ) ^ 2 ≤ 4 * (d : ℝ) ^ 2 * (M : ℝ) :=
      le_mul_of_one_le_right (mul_nonneg (by norm_num) hd2) hM1
    have hb : C ≤ |C| * (M : ℝ) :=
      (le_abs_self C).trans (le_mul_of_one_le_right (abs_nonneg C) hM1)
    have hc : K * (M : ℝ) = 4 * (d : ℝ) ^ 2 * Real.pi * (M : ℝ) + 4 * (d : ℝ) ^ 2 * (M : ℝ)
        + |C| * (M : ℝ) := by rw [hK]; ring
    rw [hc]; linarith
  -- divide by `M`
  have h4 : (M : ℝ) * ((M : ℝ) * (L - Real.pi ^ 2 * (d : ℝ) ^ 2)) ≤ (M : ℝ) * K := by
    calc (M : ℝ) * ((M : ℝ) * (L - Real.pi ^ 2 * (d : ℝ) ^ 2))
        = (M : ℝ) ^ 2 * (L - Real.pi ^ 2 * (d : ℝ) ^ 2) := by ring
      _ ≤ K * (M : ℝ) := h2.trans h3
      _ = (M : ℝ) * K := mul_comm _ _
  have h5 : (M : ℝ) * (L - Real.pi ^ 2 * (d : ℝ) ^ 2) ≤ K := le_of_mul_le_mul_left h4 hMr
  have h6 : K < (M : ℝ) * (L - Real.pi ^ 2 * (d : ℝ) ^ 2) := (div_lt_iff₀ hεpos).mp hMgt
  exact absurd h5 (not_le.mpr h6)

end AaronsonAmbainis.Pack

namespace AaronsonAmbainis

/-- The bound for fractional packings follows from the block inequality. -/
theorem packingBound_of_block : BlockInequality → PackingBound := by
  intro hB ι _ _ d f hf hd x κ hκ hpack
  exact Pack.le_of_scaled _ (∑ S, |f x - f (flipSet x S)|) d
    (fun M hM => Pack.scaled_bound hB ι d f hf hd x κ hκ hpack M hM)

end AaronsonAmbainis

end
/- END UPSTREAM MODULE: AaronsonAmbainis.Pack.Packing -/

/- BEGIN UPSTREAM MODULE: AaronsonAmbainis.Pack.Main -/
section
/-!
# From the block inequality to the packing bound

* `AaronsonAmbainis.packingBound_of_block : BlockInequality → PackingBound`
  (Lemma 6.5 of the paper from Lemma 6.4; the proof is in `Pack/Packing.lean`)
-/

end
/- END UPSTREAM MODULE: AaronsonAmbainis.Pack.Main -/

/- BEGIN UPSTREAM MODULE: AaronsonAmbainis.Dual.Sets -/
section
/-!
# Duality between packings and rows: the three sets

* `massSet ι K`  — the polytope `P = {a ≥ 0, ∑ a ≤ K}` in `ι → ℝ` (compact, convex);
* `slack t`      — the affine map `a ↦ (S ↦ a(S) - t S)` into `Finset ι → ℝ`;
* `orthant ι`    — the closed convex cone `V₊ = {v ≥ 0}` in `Finset ι → ℝ`.

They are used in the proof of the duality statement (Proposition 6.7 of the paper), which is
`Dual.exists_cover` in `Dual/Cover.lean`. The image of `P` under the slack map is the set `C` of
the proof in the paper.
-/

namespace AaronsonAmbainis
namespace Dual

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `P = {a : a ≥ 0, ∑ a ≤ K}`. -/
def massSet (ι : Type*) [Fintype ι] (K : ℝ) : Set (ι → ℝ) :=
  {a | (∀ i, 0 ≤ a i) ∧ ∑ i, a i ≤ K}

/-- The slack of `a` against the demands `t`: `S ↦ a(S) - t S`. -/
def slack (t : Finset ι → ℝ) (a : ι → ℝ) : Finset ι → ℝ :=
  fun S => ∑ i ∈ S, a i - t S

/-- The nonnegative orthant of `Finset ι → ℝ`. -/
def orthant (ι : Type*) : Set (Finset ι → ℝ) := {v | ∀ S, 0 ≤ v S}

omit [DecidableEq ι] in
theorem massSet_convex (K : ℝ) : Convex ℝ (massSet ι K) := by
  rintro a ⟨ha0, haK⟩ b ⟨hb0, hbK⟩ s r hs hr hsr
  refine ⟨fun i => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg hs (ha0 i)) (mul_nonneg hr (hb0 i))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    calc s * ∑ i, a i + r * ∑ i, b i
        ≤ s * K + r * K :=
          add_le_add (mul_le_mul_of_nonneg_left haK hs) (mul_le_mul_of_nonneg_left hbK hr)
      _ = K := by rw [← add_mul, hsr, one_mul]

omit [DecidableEq ι] in
theorem massSet_isClosed (K : ℝ) : IsClosed (massSet ι K) := by
  have h : massSet ι K = (⋂ i, {a : ι → ℝ | 0 ≤ a i}) ∩ {a : ι → ℝ | ∑ i, a i ≤ K} := by
    ext a
    simp [massSet]
  rw [h]
  exact IsClosed.inter
    (isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i))
    (isClosed_le (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const)

omit [DecidableEq ι] in
theorem massSet_isCompact (K : ℝ) : IsCompact (massSet ι K) := by
  have hsub : massSet ι K ⊆ Set.pi Set.univ (fun _ : ι => Set.Icc (0 : ℝ) K) := by
    intro a ha i _
    exact ⟨ha.1 i,
      le_trans (Finset.single_le_sum (fun j _ => ha.1 j) (Finset.mem_univ i)) ha.2⟩
  exact IsCompact.of_isClosed_subset (isCompact_univ_pi fun _ => isCompact_Icc)
    (massSet_isClosed K) hsub

omit [Fintype ι] [DecidableEq ι] in
theorem slack_continuous (t : Finset ι → ℝ) : Continuous (slack t) :=
  continuous_pi fun _ =>
    (continuous_finsetSum _ fun i _ => continuous_apply i).sub continuous_const

omit [DecidableEq ι] in
theorem slackImage_convex (t : Finset ι → ℝ) (K : ℝ) :
    Convex ℝ (slack t '' massSet ι K) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ s r hs hr hsr
  refine ⟨s • a + r • b, massSet_convex K ha hb hs hr hsr, ?_⟩
  funext S
  simp only [slack, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  linear_combination (t S) * hsr

omit [DecidableEq ι] in
theorem slackImage_isCompact (t : Finset ι → ℝ) (K : ℝ) :
    IsCompact (slack t '' massSet ι K) :=
  (massSet_isCompact K).image (slack_continuous t)

omit [Fintype ι] [DecidableEq ι] in
theorem orthant_convex : Convex ℝ (orthant ι) := by
  intro v hv w hw s r hs hr _ S
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  exact add_nonneg (mul_nonneg hs (hv S)) (mul_nonneg hr (hw S))

omit [Fintype ι] [DecidableEq ι] in
theorem orthant_isClosed : IsClosed (orthant ι) := by
  have h : orthant ι = ⋂ S : Finset ι, {v : Finset ι → ℝ | 0 ≤ v S} := by
    ext v
    simp [orthant]
  rw [h]
  exact isClosed_iInter fun S => isClosed_le continuous_const (continuous_apply S)

end Dual
end AaronsonAmbainis

end
/- END UPSTREAM MODULE: AaronsonAmbainis.Dual.Sets -/

/- BEGIN UPSTREAM MODULE: AaronsonAmbainis.Dual.Functional -/
section
/-!
# Linear functionals on `β → ℝ` for a finite index type `β`

* `functional_eq_sum` — `φ v = ∑ b, φ (e_b) * v b`;
* `coeff_nonneg`      — if `φ` is bounded below on the nonnegative orthant, its coefficients
                        `φ (e_b)` are nonnegative.

Both are used in `Dual/Cover.lean`, where they turn the separating functional given by the
Hahn–Banach theorem into a vector `κ ≥ 0` with `φ v = ∑_S κ_S v_S`.
-/

namespace AaronsonAmbainis
namespace Dual

open Finset

variable {β : Type*} [Fintype β] [DecidableEq β]

/-- Every vector is the sum of its coordinates times the unit vectors. -/
theorem eq_sum_single (v : β → ℝ) : v = ∑ b, v b • (Pi.single b (1 : ℝ) : β → ℝ) := by
  funext c
  rw [Finset.sum_apply, Finset.sum_eq_single c]
  · simp
  · intro b _ hb
    simp [hb.symm]
  · intro h
    exact absurd (Finset.mem_univ c) h

theorem functional_eq_sum (φ : (β → ℝ) →L[ℝ] ℝ) (v : β → ℝ) :
    φ v = ∑ b, φ (Pi.single b 1) * v b := by
  conv_lhs => rw [eq_sum_single v]
  rw [map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm]

omit [Fintype β] in
theorem coeff_nonneg (φ : (β → ℝ) →L[ℝ] ℝ) (r : ℝ)
    (h : ∀ v : β → ℝ, (∀ b, 0 ≤ v b) → r < φ v) (b : β) :
    0 ≤ φ (Pi.single b 1) := by
  by_contra hneg
  rw [not_le] at hneg
  -- `v = 0` gives `r < 0`
  have hr : r < 0 := by
    have h0 := h 0 (fun _ => le_rfl)
    rwa [map_zero] at h0
  -- `v = (r / φ e_b) • e_b` lies in the orthant and has `φ v = r`
  have hx := h ((r / φ (Pi.single b 1)) • (Pi.single b (1 : ℝ) : β → ℝ)) (fun c => by
    simp only [Pi.smul_apply, smul_eq_mul]
    refine mul_nonneg (div_nonneg_of_nonpos hr.le hneg.le) ?_
    rw [Pi.single_apply]
    split_ifs <;> norm_num)
  rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hneg.ne] at hx
  exact lt_irrefl _ hx

end Dual
end AaronsonAmbainis

end
/- END UPSTREAM MODULE: AaronsonAmbainis.Dual.Functional -/

/- BEGIN UPSTREAM MODULE: AaronsonAmbainis.Dual.Core -/
section
/-!
# Duality between packings and rows: the finite core

* `sum_mul_sum_mem` — double counting `∑_S κ_S a(S) = ∑_i a_i ∑_{S ∋ i} κ_S`;
* `no_separator`    — if every fractional packing has value at most `K`, then no `κ ≥ 0` has
                      `∑_S κ_S (a(S) - t_S) < 0` for all `a ≥ 0` of mass at most `K`.

In `no_separator`, write `c = ∑_S κ_S t_S` and `M_i = ∑_{S ∋ i} κ_S`. The hypothesis reads
`∑_i a_i M_i < c` for all admissible `a`; `a = 0` gives `c > 0`.
Case A (no `M_i` is positive): `((K+1)/c) κ` is a packing of value `K + 1 > K`.
Case B (`M_j = max_i M_i > 0`): `κ / M_j` is a packing, so `c ≤ K M_j`, while `a = K e_j` gives
`K M_j < c`.

This is the part of the proof of Proposition 6.7 (Duality) of the paper which follows the
separation step; there `c` and `M_i` are written `ϑ` and `σ_i`.
-/

namespace AaronsonAmbainis
namespace Dual

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem sum_mul_sum_mem (κ : Finset ι → ℝ) (a : ι → ℝ) :
    ∑ S, κ S * ∑ i ∈ S, a i
      = ∑ i, a i * ∑ S ∈ univ.filter (fun S : Finset ι => i ∈ S), κ S := by
  have h1 : ∀ S : Finset ι, κ S * ∑ i ∈ S, a i = ∑ i, if i ∈ S then a i * κ S else 0 := by
    intro S
    rw [Fintype.sum_ite_mem, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have h2 : ∀ i : ι, a i * ∑ S ∈ univ.filter (fun S : Finset ι => i ∈ S), κ S
      = ∑ S : Finset ι, if i ∈ S then a i * κ S else 0 := by
    intro i
    rw [Finset.mul_sum, Finset.sum_filter]
  rw [Finset.sum_congr rfl fun S _ => h1 S, Finset.sum_congr rfl fun i _ => h2 i]
  exact Finset.sum_comm

theorem no_separator (t : Finset ι → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hpack : ∀ κ : Finset ι → ℝ, (∀ S, 0 ≤ κ S) →
        (∀ i, ∑ S ∈ univ.filter (fun S : Finset ι => i ∈ S), κ S ≤ 1) →
        ∑ S, κ S * t S ≤ K)
    (κ : Finset ι → ℝ) (hκ : ∀ S, 0 ≤ κ S)
    (hsep : ∀ a : ι → ℝ, (∀ i, 0 ≤ a i) → ∑ i, a i ≤ K →
        ∑ S, κ S * (∑ i ∈ S, a i - t S) < 0) : False := by
  -- `c = ∑_S κ_S t_S` and `M_i = ∑_{S ∋ i} κ_S`
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = ∑ S, κ S * t S := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : ι → ℝ,
      ∀ i, M i = ∑ S ∈ univ.filter (fun S : Finset ι => i ∈ S), κ S := ⟨_, fun _ => rfl⟩
  -- the separation hypothesis in the form `∑_i a_i M_i < c`
  have hsep' : ∀ a : ι → ℝ, (∀ i, 0 ≤ a i) → ∑ i, a i ≤ K → ∑ i, a i * M i < c := by
    intro a ha0 haK
    have h := hsep a ha0 haK
    have h1 : ∑ i, a i * M i = ∑ S, κ S * ∑ i ∈ S, a i := by
      rw [sum_mul_sum_mem κ a]
      exact Finset.sum_congr rfl fun i _ => by rw [hM i]
    have h2 : ∑ S, κ S * (∑ i ∈ S, a i - t S)
        = ∑ S, κ S * ∑ i ∈ S, a i - ∑ S, κ S * t S := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun S _ => mul_sub _ _ _
    rw [h2, ← h1, ← hc] at h
    linarith
  -- `a = 0` gives `c > 0`
  have hcpos : 0 < c := by
    have h := hsep' 0 (fun _ => le_rfl) (by simpa using hK)
    simpa using h
  by_cases hex : ∃ i, 0 < M i
  · -- Case B: the largest load `M j` is positive
    obtain ⟨i0, hi0⟩ := hex
    obtain ⟨j, -, hj⟩ := Finset.exists_max_image univ M ⟨i0, Finset.mem_univ i0⟩
    have hMj : 0 < M j := lt_of_lt_of_le hi0 (hj i0 (Finset.mem_univ i0))
    -- `κ / M j` is a packing
    have h1 := hpack (fun S => κ S / M j) (fun S => div_nonneg (hκ S) hMj.le)
      (fun i => by
        rw [← Finset.sum_div, ← hM i]
        exact (div_le_one hMj).mpr (hj i (Finset.mem_univ i)))
    have h2 : c ≤ K * M j := by
      have h3 : ∑ S, κ S / M j * t S = c / M j := by
        rw [hc, Finset.sum_div]
        exact Finset.sum_congr rfl fun S _ => by ring
      rw [h3, div_le_iff₀ hMj] at h1
      exact h1
    -- `a = K e_j` is admissible
    have hsum : ∑ i, (Pi.single j K : ι → ℝ) i = K := by
      rw [Finset.sum_eq_single j]
      · rw [Pi.single_eq_same]
      · intro i _ hi
        rw [Pi.single_eq_of_ne hi]
      · intro h
        exact absurd (Finset.mem_univ j) h
    have h4 := hsep' (Pi.single j K)
      (fun i => by
        rw [Pi.single_apply]
        split_ifs
        · exact hK
        · exact le_rfl)
      hsum.le
    have h5 : ∑ i, (Pi.single j K : ι → ℝ) i * M i = K * M j := by
      rw [Finset.sum_eq_single j]
      · rw [Pi.single_eq_same]
      · intro i _ hi
        rw [Pi.single_eq_of_ne hi, zero_mul]
      · intro h
        exact absurd (Finset.mem_univ j) h
    rw [h5] at h4
    linarith
  · -- Case A: no load is positive, so every nonnegative multiple of `κ` is a packing
    have hM0 : ∀ i, M i ≤ 0 := fun i => not_lt.mp fun h => hex ⟨i, h⟩
    have hs : 0 ≤ (K + 1) / c := div_nonneg (by linarith) hcpos.le
    have h1 := hpack (fun S => (K + 1) / c * κ S) (fun S => mul_nonneg hs (hκ S))
      (fun i => by
        rw [← Finset.mul_sum, ← hM i]
        have h6 : (K + 1) / c * M i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hs (hM0 i)
        linarith)
    have h2 : ∑ S, (K + 1) / c * κ S * t S = K + 1 := by
      have h3 : ∑ S, (K + 1) / c * κ S * t S = (K + 1) / c * c := by
        rw [hc, Finset.mul_sum]
        exact Finset.sum_congr rfl fun S _ => by ring
      rw [h3, div_mul_cancel₀ _ hcpos.ne']
    rw [h2] at h1
    linarith

end Dual
end AaronsonAmbainis

end
/- END UPSTREAM MODULE: AaronsonAmbainis.Dual.Core -/

/- BEGIN UPSTREAM MODULE: AaronsonAmbainis.Dual.Cover -/
section
/-!
# Duality between packings and rows

`Dual.exists_cover` is Proposition 6.7 (Duality) of the paper. `coverDuality : CoverDuality`
follows from it: `CoverDuality` is the same statement with the two side hypotheses `0 ≤ K` and
`t ∅ ≤ 0` (neither is needed: the zero packing gives `0 ≤ K`, and `t ∅ ≤ 0` is the conclusion at
`S = ∅`).

Proof of `Dual.exists_cover`. Let `P = Dual.massSet ι K = {a ≥ 0, ∑ a ≤ K}` and
`Q = Dual.slack t '' P`, the set of all slack vectors `S ↦ a(S) - t S`; the claim is that `Q`
meets the nonnegative orthant of `Finset ι → ℝ`. If not, the geometric Hahn–Banach theorem
(`geometric_hahn_banach_compact_closed`: `Q` is compact and convex, the orthant is closed and
convex) gives a continuous linear functional `φ` and reals `u < r` with `φ < u` on `Q` and
`r < φ` on the orthant. Then `r < 0`, the coefficients `κ_S = φ (e_S)` are nonnegative
(`Dual.coeff_nonneg`), `φ v = ∑_S κ_S v_S` (`Dual.functional_eq_sum`), and
`∑_S κ_S (a(S) - t_S) < u < 0` for all `a ∈ P`, which `Dual.no_separator` excludes.

In the paper the set `Q` is called `C`, and the vector `κ` is obtained from Lemma 6.6 (Separation
from the orthant), for which the paper gives a short direct proof; here Mathlib's geometric
Hahn–Banach theorem takes the place of that lemma.
-/

namespace AaronsonAmbainis

open Finset

namespace Dual

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Linear-programming duality between fractional packings and rows: if every fractional packing
`κ` has `∑_S κ_S t_S ≤ K`, then some `a ≥ 0` of total mass at most `K` has `t_S ≤ a(S)` for
every `S`. -/
theorem exists_cover (t : Finset ι → ℝ) (K : ℝ)
    (hpack : ∀ κ : Finset ι → ℝ, (∀ S, 0 ≤ κ S) →
        (∀ i, ∑ S ∈ univ.filter (fun S : Finset ι => i ∈ S), κ S ≤ 1) →
        ∑ S, κ S * t S ≤ K) :
    ∃ a : ι → ℝ, (∀ i, 0 ≤ a i) ∧ ∑ i, a i ≤ K ∧ ∀ S : Finset ι, t S ≤ ∑ i ∈ S, a i := by
  -- the zero packing gives `0 ≤ K`
  have hK : 0 ≤ K := by
    have h := hpack 0 (fun _ => le_rfl) (fun i => by simp)
    simpa using h
  by_contra hne
  -- the set `Q` of slack vectors misses the orthant
  have hdisj : Disjoint (slack t '' massSet ι K) (orthant ι) := by
    rw [Set.disjoint_left]
    rintro _ ⟨a, ⟨ha0, haK⟩, rfl⟩ hv
    refine hne ⟨a, ha0, haK, fun S => ?_⟩
    have h : 0 ≤ ∑ i ∈ S, a i - t S := hv S
    linarith
  -- strict separation of the compact convex `Q` from the closed convex orthant
  obtain ⟨φ, u, r, hQ, hur, hV⟩ :=
    geometric_hahn_banach_compact_closed (slackImage_convex t K)
      (slackImage_isCompact t K) orthant_convex orthant_isClosed hdisj
  -- `0` lies in the orthant, so `r < 0`
  have hr : r < 0 := by
    have h0 := hV 0 (fun _ => le_rfl)
    rwa [map_zero] at h0
  -- the coefficients of `φ` are nonnegative
  have hκ : ∀ S : Finset ι, 0 ≤ φ (Pi.single S 1) :=
    fun S => coeff_nonneg φ r hV S
  -- the finite core
  refine no_separator t K hK hpack (fun S => φ (Pi.single S 1)) hκ (fun a ha0 haK => ?_)
  have h1 : φ (slack t a) < u := hQ (slack t a) ⟨a, ⟨ha0, haK⟩, rfl⟩
  rw [functional_eq_sum φ (slack t a)] at h1
  have h2 : ∑ S, φ (Pi.single S 1) * slack t a S
      = ∑ S, φ (Pi.single S 1) * (∑ i ∈ S, a i - t S) := rfl
  rw [h2] at h1
  linarith

end Dual

theorem coverDuality : CoverDuality :=
  fun _ _ _ t K _ _ hpack => Dual.exists_cover t K hpack

end AaronsonAmbainis

end
/- END UPSTREAM MODULE: AaronsonAmbainis.Dual.Cover -/

/- BEGIN UPSTREAM MODULE: AaronsonAmbainis.Dual.RowAux -/
section
/-!
# The row bound from the packing bound and duality

`Dual.rowBoundPM_of_packing_of_cover : PackingBound → CoverDuality → RowBoundPM`
(Theorem 6.8 of the paper from Lemma 6.5 and linear-programming duality, Proposition 6.7). As in
the paper, at each point `x` duality is applied to the demands `t S = |f x - f (x^S)|` with
`K = π² d²`; then `S = Δ(x,y)`.
-/

namespace AaronsonAmbainis
namespace Dual

open Finset

theorem rowBoundPM_of_packing_of_cover : PackingBound → CoverDuality → RowBoundPM := by
  intro hPB hCD ι _ _ d f hf hdeg
  have key : ∀ x : Cube ι, ∃ a : ι → ℝ, (∀ i, 0 ≤ a i) ∧
      ∑ i, a i ≤ Real.pi ^ 2 * (d : ℝ) ^ 2 ∧
      ∀ S : Finset ι, |f x - f (flipSet x S)| ≤ ∑ i ∈ S, a i := by
    intro x
    refine hCD ι (fun S => |f x - f (flipSet x S)|) (Real.pi ^ 2 * (d : ℝ) ^ 2)
      (by positivity) ?_ ?_
    · -- `t ∅ = 0`
      rw [flipSet_empty, sub_self, abs_zero]
    · -- the hypothesis of `CoverDuality` is `PackingBound` at `x`
      intro κ hκ hpack
      exact hPB ι d f hf hdeg x κ hκ hpack
  choose a ha0 haK hacov using key
  refine ⟨a, ha0, haK, fun x y => ?_⟩
  have h := hacov x (diffSet x y)
  rwa [flipSet_diffSet] at h

end Dual
end AaronsonAmbainis

end
/- END UPSTREAM MODULE: AaronsonAmbainis.Dual.RowAux -/

/- BEGIN UPSTREAM MODULE: AaronsonAmbainis.Dual.Row -/
section
/-!
# The row bound from the packing bound

`rowBoundPM_of_packing : PackingBound → RowBoundPM` (Theorem 6.8 of the paper from Lemma 6.5), by
`Dual.rowBoundPM_of_packing_of_cover` and `coverDuality`.
-/

namespace AaronsonAmbainis

theorem rowBoundPM_of_packing : PackingBound → RowBoundPM :=
  fun hPB => Dual.rowBoundPM_of_packing_of_cover hPB coverDuality

end AaronsonAmbainis

end
/- END UPSTREAM MODULE: AaronsonAmbainis.Dual.Row -/

/- BEGIN UPSTREAM MODULE: AaronsonAmbainis.Dual.Main -/
section
/-!
# Duality and the row bound

* `coverDuality : CoverDuality`
  (linear-programming duality between fractional packings and rows; it corresponds to
  Proposition 6.7 of the paper, which is `Dual.exists_cover`; file `Cover.lean`, helpers in
  `Sets`, `Functional`, `Core`)
* `rowBoundPM_of_packing : PackingBound → RowBoundPM`
  (the row bound, Theorem 6.8 of the paper, from the packing bound, Lemma 6.5; file `Row.lean`,
  helper in `RowAux`)
-/

end
/- END UPSTREAM MODULE: AaronsonAmbainis.Dual.Main -/

/- BEGIN UPSTREAM MODULE: AaronsonAmbainis.MainTheorem -/
section
/-!
# The theorems for functions of bounded degree, from the links

A function `f` on the cube with `|f| ≤ 1` and degree at most `d` has a row of cost at most
`π² d²` at every point (`RowBoundPM`, Theorem 6.8 of the paper), and
`∑_j |f(x) - f(x^j)| ≤ 4 d²` at every point `x` (`SensitivityBound`, Corollary 6.10). With these
two inputs:

* `mainTheorem_of_influence : InfluenceBound → SensitivityBound → RowBoundPM → MainTheorem` —
  the main theorem (Theorem 1.1 of the paper). The bound for the influences (Theorem 8.3) with
  `K = π² d²` and `L(f) ≤ 4 d²` reads
  `3 Var(f)^5 ≤ 3125 (4 d²)² (π² d²)^4 Inf_j(f)² = 50000 π^8 d^12 Inf_j(f)²`.
* `meanIncrementDegree_of_meanIncrement :
  MeanIncrementBound → RowBoundPM → MeanIncrementDegreeBound` —
  the bound for the mean absolute increments (Theorem 7.10) with `K = π² d²`, which is
  Corollary 7.11 of the paper: `Var(f)^3 ≤ 36 (π² d²)^4 L_j(f)² = 36 π^8 d^8 L_j(f)²`.
* `mainTheoremImproved_of_influence :
  InfluenceBound → SensitivityBound → RowBound → MainTheoremImproved` —
  the main theorem with the constant `3125 π^8` in place of `50000 π^8` (Remark 8.4 of the
  paper). Its hypothesis `RowBound` is the row bound of Agarwal and Ben-David (Theorem 1.7 of
  arXiv:2410.19062), which is not proved in this project; it gives rows of cost at most
  `π² d² / 2` (`rows_of_rowBound`), and `3125 (4 d²)² (π² d² / 2)^4 = 3125 π^8 d^12`.
-/

namespace AaronsonAmbainis

open Finset

/-- The main theorem (Theorem 1.1 of the paper) from the bound for the influences (Theorem 8.3),
the sensitivity bound (Corollary 6.10) and the row bound (Theorem 6.8). -/
theorem mainTheorem_of_influence :
    InfluenceBound → SensitivityBound → RowBoundPM → MainTheorem := by
  intro hI hS hR ι _ _ d f hf hdeg hvar
  obtain ⟨a, ha0, haK, hacov⟩ := hR ι d f hf hdeg
  obtain ⟨j, hj⟩ := Average.influence_of_incr hI f a ha0 haK hacov (hS ι d f hf hdeg) hvar
  refine ⟨j, le_trans hj (le_of_eq ?_)⟩
  ring

/-- The bound for the mean absolute increments of a bounded function of degree at most `d`
(Corollary 7.11 of the paper), from the bound for functions with rows of cost at most `K`
(Theorem 7.10) and the row bound (Theorem 6.8). -/
theorem meanIncrementDegree_of_meanIncrement :
    MeanIncrementBound → RowBoundPM → MeanIncrementDegreeBound := by
  intro hM hR ι _ _ d f hf hdeg hvar
  obtain ⟨a, ha0, haK, hacov⟩ := hR ι d f hf hdeg
  obtain ⟨j, hj⟩ := hM ι f (Real.pi ^ 2 * (d : ℝ) ^ 2) a ha0 haK hacov hvar
  refine ⟨j, le_trans hj (le_of_eq ?_)⟩
  ring

/-- The row bound of Agarwal and Ben-David (the hypothesis `RowBound`) for a function `f` with
values in `[-1,1]`: applied to `(1 + f)/2`, with the weights doubled, it gives rows of `f` of
cost at most `π² d² / 2`. -/
theorem rows_of_rowBound (hRB : RowBound) {ι : Type} [Fintype ι] [DecidableEq ι] (d : ℕ)
    (f : Cube ι → ℝ) (hf : ∀ x, |f x| ≤ 1) (hdeg : HasDegreeLE f d) :
    ∃ a : Cube ι → ι → ℝ, (∀ x i, 0 ≤ a x i) ∧
      (∀ x, ∑ i, a x i ≤ Real.pi ^ 2 * (d : ℝ) ^ 2 / 2) ∧
      ∀ x y, |f x - f y| ≤ ∑ i ∈ diffSet x y, a x i := by
  -- `(1 + f)/2` has degree at most `d` and takes values in `[0,1]`
  have hdeg' : HasDegreeLE (fun x => 1 / 2 + 1 / 2 * f x) d :=
    Row.hasDegreeLE_add (Row.hasDegreeLE_const (1 / 2) d)
      (Row.hasDegreeLE_const_mul (1 / 2) hdeg)
  have hr : ∀ x, 0 ≤ 1 / 2 + 1 / 2 * f x ∧ 1 / 2 + 1 / 2 * f x ≤ 1 := by
    intro x
    have h1 := abs_le.mp (hf x)
    constructor <;> linarith [h1.1, h1.2]
  obtain ⟨c, hc1, hc2⟩ := hRB ι d (fun x => 1 / 2 + 1 / 2 * f x) hr hdeg'
  -- the weights are nonnegative: take `y = x^i`
  have hnn : ∀ x i, 0 ≤ c x i := fun x i =>
    le_trans (abs_nonneg _) (Level.abs_incr_le_of_rows hc1 x i)
  refine ⟨fun x i => 2 * c x i, fun x i => mul_nonneg (by norm_num) (hnn x i),
    fun x => ?_, fun x y => ?_⟩
  · have h2 := hc2 x
    rw [← Finset.mul_sum]
    linarith
  · have h1 : |(1 / 2 + 1 / 2 * f x) - (1 / 2 + 1 / 2 * f y)| ≤ ∑ i ∈ diffSet x y, c x i :=
      hc1 x y
    have e : (1 / 2 + 1 / 2 * f x) - (1 / 2 + 1 / 2 * f y) = (f x - f y) / 2 := by ring
    rw [e, abs_div, abs_two] at h1
    rw [← Finset.mul_sum]
    linarith

/-- The main theorem with the constant that the row bound of Agarwal and Ben-David gives
(Remark 8.4 of the paper), from the bound for the influences, the sensitivity bound and the
hypothesis `RowBound`. -/
theorem mainTheoremImproved_of_influence :
    InfluenceBound → SensitivityBound → RowBound → MainTheoremImproved := by
  intro hI hS hRB ι _ _ d f hf hdeg hvar
  obtain ⟨a, ha0, haK, hacov⟩ := rows_of_rowBound hRB d f hf hdeg
  obtain ⟨j, hj⟩ := Average.influence_of_incr hI f a ha0 haK hacov (hS ι d f hf hdeg) hvar
  refine ⟨j, le_trans hj (le_of_eq ?_)⟩
  ring

end AaronsonAmbainis

end
/- END UPSTREAM MODULE: AaronsonAmbainis.MainTheorem -/

/- BEGIN UPSTREAM MODULE: AaronsonAmbainis.Chain -/
section
/-!
# The chain

This file chains the links of the proof of the paper: every theorem below is one implication,
applied to theorems that precede it.

Boolean functions (directories `DetLow`, `DetBij`, `TwoSided`):

* `detInequality`         — the determinant inequality (Corollary 3.2), in `DetTheorem.lean`;
* `antipodal_of_det`      — the antipodal inequality (Theorem 4.3);
* `allPairs_of_antipodal` — the all-pairs inequality (Proposition 5.2);
* `twoSided_of_allPairs`  — the two-sided inequality (Theorem 5.4).

Real functions with a row of cost at most `K` at every point (directories `Level`, `Average`):

* `integratedAllPairs_of_allPairs`    — the integrated all-pairs inequality (Proposition 7.4);
* `thirdMoment_of_integratedAllPairs` — the third-moment inequality (Theorem 7.6);
* `meanIncrement_of_thirdMoment`      — the bound for the mean absolute increments
                                        (Theorem 7.10);
* `influence_of_meanIncrement`        — the bound for the influences (Theorem 8.3).

Bounded functions of degree at most `d` (directories `Row`, `Pack`, `Dual`):

* `blockInequality`       — the block inequality (Lemma 6.4), in `Row/Main.lean`;
* `sensitivity_of_block`  — the sensitivity bound at every point (Corollary 6.10);
* `packingBound_of_block` — the packing bound (Lemma 6.5);
* `rowBoundPM_of_packing` — the row bound (Theorem 6.8: rows of cost at most `π² d²`).

The theorems for bounded functions of degree at most `d` (`MainTheorem.lean`):

* `mainTheorem_of_influence`             — the main theorem (Theorem 1.1);
* `meanIncrementDegree_of_meanIncrement` — the bound for the mean absolute increments
                                           (Corollary 7.11);
* `mainTheoremImproved_of_influence`     — the main theorem with the constant that the row bound
                                           of Agarwal and Ben-David gives (Remark 8.4).

All theorems of this file except the last one have no hypothesis. The hypothesis of the last
one, `mainTheoremImproved_of_rowBound : RowBound → MainTheoremImproved`, is `RowBound`, the row
bound of Agarwal and Ben-David (Theorem 1.7 of arXiv:2410.19062), which is not proved in this
project. The two-sided inequality is a result of the paper in its own right; the main theorem
does not use it.
-/

namespace AaronsonAmbainis

/-! ### Boolean functions -/

/-- The antipodal inequality (the inequality of Theorem 4.3 of the paper), with no hypothesis. -/
theorem antipodalInequality : AntipodalInequality := antipodal_of_det detInequality

/-- The all-pairs inequality (the inequality of Proposition 5.2 of the paper), with no
hypothesis. -/
theorem allPairsInequality : AllPairsInequality := allPairs_of_antipodal antipodalInequality

/-- The two-sided inequality (the inequality of Theorem 5.4 of the paper), with no hypothesis. -/
theorem twoSidedInequality : TwoSidedInequality := twoSided_of_allPairs allPairsInequality

/-! ### Real functions with a row at every point -/

/-- The integrated all-pairs inequality (the inequality of Proposition 7.4 of the paper), with no
hypothesis. -/
theorem integratedAllPairsInequality : IntegratedAllPairsInequality :=
  integratedAllPairs_of_allPairs allPairsInequality

/-- The third-moment inequality (Theorem 7.6 of the paper), with no hypothesis. -/
theorem thirdMomentInequality : ThirdMomentInequality :=
  thirdMoment_of_integratedAllPairs integratedAllPairsInequality

/-- The bound for the mean absolute increments (Theorem 7.10 of the paper), with no
hypothesis. -/
theorem meanIncrementBound : MeanIncrementBound :=
  meanIncrement_of_thirdMoment thirdMomentInequality

/-- The bound for the influences (Theorem 8.3 of the paper), with no hypothesis. -/
theorem influenceBound : InfluenceBound := influence_of_meanIncrement meanIncrementBound

/-! ### Bounded functions of degree at most `d` -/

/-- The sensitivity bound at every point (Corollary 6.10 of the paper), with no hypothesis. -/
theorem sensitivityBound : SensitivityBound := sensitivity_of_block blockInequality

/-- The packing bound (Lemma 6.5 of the paper), with no hypothesis. -/
theorem packingBound : PackingBound := packingBound_of_block blockInequality

/-- The row bound (Theorem 6.8 of the paper: rows of cost at most `π² d²`), with no
hypothesis. -/
theorem rowBoundPM : RowBoundPM := rowBoundPM_of_packing packingBound

/-! ### The theorems for bounded functions of degree at most `d` -/

/-- The main theorem (Theorem 1.1 of the paper), with no hypothesis. -/
theorem mainTheorem : MainTheorem :=
  mainTheorem_of_influence influenceBound sensitivityBound rowBoundPM

/-- The bound for the mean absolute increments of a bounded function of degree at most `d`
(Corollary 7.11 of the paper), with no hypothesis. -/
theorem meanIncrementDegreeBound : MeanIncrementDegreeBound :=
  meanIncrementDegree_of_meanIncrement meanIncrementBound rowBoundPM

/-- The row bound of Agarwal and Ben-David, which is a hypothesis here, implies the main theorem
with the constant `3125 π^8` (Remark 8.4 of the paper). -/
theorem mainTheoremImproved_of_rowBound : RowBound → MainTheoremImproved :=
  mainTheoremImproved_of_influence influenceBound sensitivityBound

end AaronsonAmbainis

end
/- END UPSTREAM MODULE: AaronsonAmbainis.Chain -/

/- BEGIN UPSTREAM MODULE: AaronsonAmbainis.Bridge.Basic -/
section
/-!
# Checks of the definitions: flips, degree zero, the dictator

`flipSet` / `diffSet` are mutually inverse, `HasDegreeLE` is monotone, degree `0` means constant,
and the dictator `x ↦ (-1)^{x_j}` has degree exactly `1`, variance `1` and influence `1`; so the
hypotheses of `MainTheorem` are satisfiable (`aa_hyps_satisfiable`).
These are checks of the definitions of `Defs.lean`; the proofs of `Chain.lean` do not depend on
them.
-/

namespace AaronsonAmbainis.Bridge

open Finset

section NoFintype

variable {ι : Type*} [DecidableEq ι]

theorem flipSet_flipSet (x : Cube ι) (S : Finset ι) : flipSet (flipSet x S) S = x := by
  funext i
  by_cases h : i ∈ S <;> simp [flipSet, h]

theorem flipSet_empty (x : Cube ι) : flipSet x ∅ = x := by
  funext i
  simp [flipSet]

theorem flipSet_singleton_self (x : Cube ι) (j : ι) : flipSet x {j} j = !(x j) := by
  simp [flipSet]

theorem flipSet_singleton_ne (x : Cube ι) {i j : ι} (h : i ≠ j) : flipSet x {j} i = x i := by
  simp [flipSet, h]

end NoFintype

section DictPlain

variable {ι : Type*}

/-- The dictator `x ↦ (-1)^{x_j}`. -/
noncomputable def dict (j : ι) : Cube ι → ℝ := fun x => if x j then -1 else 1

theorem dict_abs_le_one (j : ι) (x : Cube ι) : |dict j x| ≤ 1 := by
  unfold dict
  split_ifs <;> simp

theorem dict_sq (j : ι) (x : Cube ι) : dict j x ^ 2 = 1 := by
  unfold dict
  split_ifs <;> norm_num

theorem dict_flip [DecidableEq ι] (j : ι) (x : Cube ι) : dict j (flipSet x {j}) = -dict j x := by
  unfold dict
  rw [flipSet_singleton_self]
  cases x j <;> simp

end DictPlain

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `Δ(x, x^S) = S`. -/
theorem diffSet_flipSet (x : Cube ι) (S : Finset ι) : diffSet x (flipSet x S) = S := by
  ext i
  by_cases h : i ∈ S <;> simp [diffSet, flipSet, h]

/-- `x^{Δ(x,y)} = y`. -/
theorem flipSet_diffSet (x y : Cube ι) : flipSet x (diffSet x y) = y := by
  funext i
  by_cases h : x i = y i
  · simp [flipSet, diffSet, h]
  · have h' : (!(x i)) = y i := by
      cases hx : x i <;> cases hy : y i <;> simp_all
    simp [flipSet, diffSet, h, h']

/-- `antipode x = x^{[n]}`. -/
theorem antipode_eq_flipSet_univ (x : Cube ι) : antipode x = flipSet x univ := by
  funext i
  simp [antipode, flipSet]

/-- The cube over `ι` has `2^n` points. -/
theorem card_cube : (Fintype.card (Cube ι) : ℝ) = 2 ^ Fintype.card ι := by
  show (Fintype.card (ι → Bool) : ℝ) = 2 ^ Fintype.card ι
  rw [Fintype.card_fun, Fintype.card_bool]
  norm_num

omit [DecidableEq ι] in
/-- Monotonicity of `HasDegreeLE` in the degree. -/
theorem hasDegreeLE_mono {f : Cube ι → ℝ} {d d' : ℕ} (h : HasDegreeLE f d) (hdd : d ≤ d') :
    HasDegreeLE f d' := by
  obtain ⟨c, hc, hf⟩ := h
  exact ⟨c, fun S hS => hc S (lt_of_le_of_lt hdd hS), hf⟩

omit [Fintype ι] [DecidableEq ι] in
theorem chi_empty (x : Cube ι) : chi (∅ : Finset ι) x = 1 := by
  simp [chi]

/-- Degree at most `0` is the same as constant. -/
theorem hasDegreeLE_zero_iff {f : Cube ι → ℝ} : HasDegreeLE f 0 ↔ ∃ a : ℝ, ∀ x, f x = a := by
  constructor
  · rintro ⟨c, hc, hf⟩
    refine ⟨c ∅, fun x => ?_⟩
    rw [hf x, Finset.sum_eq_single (∅ : Finset ι)]
    · simp [chi]
    · intro S _ hS
      rw [hc S (Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hS)), zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rintro ⟨a, ha⟩
    refine ⟨fun S => if S = ∅ then a else 0, ?_, fun x => ?_⟩
    · intro S hS
      have hne : S ≠ ∅ := by
        rintro rfl
        simp at hS
      simp [hne]
    · rw [ha x, Finset.sum_eq_single (∅ : Finset ι)]
      · simp [chi]
      · intro S _ hS
        simp [hS]
      · intro h
        exact absurd (Finset.mem_univ _) h

/-- `HasDegreeLE f 0` implies `f` constant. -/
theorem hasDegreeLE_zero_const {f : Cube ι → ℝ} (h : HasDegreeLE f 0) (x y : Cube ι) :
    f x = f y := by
  obtain ⟨a, ha⟩ := hasDegreeLE_zero_iff.mp h
  rw [ha x, ha y]

/-! ### The dictator -/

omit [Fintype ι] [DecidableEq ι] in
theorem dict_eq_chi (j : ι) (x : Cube ι) : dict j x = chi {j} x := by
  simp [dict, chi]

theorem dict_hasDegreeLE_one (j : ι) : HasDegreeLE (dict j) 1 := by
  refine ⟨fun S => if S = {j} then 1 else 0, ?_, fun x => ?_⟩
  · intro S hS
    have hne : S ≠ {j} := by
      rintro rfl
      simp at hS
    simp [hne]
  · rw [Finset.sum_eq_single ({j} : Finset ι)]
    · simp [dict_eq_chi]
    · intro S _ hS
      simp [hS]
    · intro h
      exact absurd (Finset.mem_univ _) h

/-- A dictator does not have degree at most `0`. -/
theorem dict_not_hasDegreeLE_zero (j : ι) : ¬ HasDegreeLE (dict j) 0 := by
  intro h
  have h1 := hasDegreeLE_zero_const h (fun _ => false) (flipSet (fun _ => false) {j})
  rw [dict_flip] at h1
  have h2 : dict j (fun _ => false) = 1 := by simp [dict]
  rw [h2] at h1
  norm_num at h1

theorem sum_dict (j : ι) : ∑ x : Cube ι, dict j x = 0 := by
  have h : ∑ x : Cube ι, dict j (flipSet x {j}) = ∑ x : Cube ι, dict j x :=
    Equiv.sum_comp
      (Function.Involutive.toPerm (fun x : Cube ι => flipSet x {j})
        (fun x => flipSet_flipSet x {j})) (dict j)
  simp only [dict_flip, Finset.sum_neg_distrib] at h
  linarith

theorem mean_dict (j : ι) : mean (dict j) = 0 := by
  simp [mean, sum_dict]

theorem variance_dict (j : ι) : variance (dict j) = 1 := by
  simp only [variance, mean_dict, sub_zero, dict_sq, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one]
  rw [card_cube]
  exact div_self (by positivity)

theorem inflR_dict_self (j : ι) : inflR (dict j) j = 1 := by
  have h : ∀ x : Cube ι, ((dict j x - dict j (flipSet x {j})) / 2) ^ 2 = 1 := by
    intro x
    rw [dict_flip]
    have h2 : (dict j x - -dict j x) / 2 = dict j x := by ring
    rw [h2, dict_sq]
  simp only [inflR, h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [card_cube]
  exact div_self (by positivity)

/-- Non-vacuity of `MainTheorem`: on any index type with a chosen coordinate `j`, the dictator
satisfies all three hypotheses with `d = 1`, has variance `1` and influence `1` at `j`. -/
theorem aa_hyps_dict (j : ι) :
    (∀ x, |dict j x| ≤ 1) ∧ HasDegreeLE (dict j) 1 ∧ 0 < variance (dict j) ∧
      variance (dict j) = 1 ∧ inflR (dict j) j = 1 :=
  ⟨dict_abs_le_one j, dict_hasDegreeLE_one j, by rw [variance_dict]; norm_num,
    variance_dict j, inflR_dict_self j⟩

/-- Same, on the concrete index type `Fin 1`. -/
theorem aa_hyps_satisfiable :
    ∃ f : Cube (Fin 1) → ℝ, (∀ x, |f x| ≤ 1) ∧ HasDegreeLE f 1 ∧ 0 < variance f ∧
      variance f = 1 ∧ inflR f 0 = 1 :=
  ⟨dict 0, aa_hyps_dict 0⟩

/-- The conclusion of `MainTheorem` (with `d = 1`) is true for the dictator. -/
theorem aa_conclusion_dict (j : ι) :
    ∃ j', 3 * variance (dict j) ^ 5
      ≤ 50000 * Real.pi ^ 8 * ((1 : ℕ) : ℝ) ^ 12 * inflR (dict j) j' ^ 2 := by
  refine ⟨j, ?_⟩
  rw [variance_dict, inflR_dict_self]
  have hpi : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  have h1 : (1 : ℝ) ≤ Real.pi ^ 8 := one_le_pow₀ hpi
  simp only [Nat.cast_one, one_pow, mul_one]
  linarith

/-- The conclusion of `RowBound` (with `d = 1`) is true for `h = (1 + dictator)/2`,
with the weights `c x i = [i = j]`. -/
theorem rowBound_conclusion_dict (j : ι) :
    ∃ c : Cube ι → ι → ℝ,
      (∀ x y, |(1 + dict j x) / 2 - (1 + dict j y) / 2| ≤ ∑ i ∈ diffSet x y, c x i) ∧
      (∀ x, ∑ i, c x i ≤ Real.pi ^ 2 / 4 * ((1 : ℕ) : ℝ) ^ 2) := by
  refine ⟨fun _ i => if i = j then 1 else 0, fun x y => ?_, fun x => ?_⟩
  · by_cases h : x j = y j
    · have hxy : dict j x = dict j y := by simp [dict, h]
      rw [hxy, sub_self, abs_zero]
      refine Finset.sum_nonneg (fun i _ => ?_)
      show (0 : ℝ) ≤ if i = j then 1 else 0
      split_ifs <;> norm_num
    · have hj : j ∈ diffSet x y := by simp [diffSet, h]
      rw [Finset.sum_ite_eq', if_pos hj]
      unfold dict
      split_ifs <;> norm_num
  · rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ j)]
    have hpi := Real.pi_gt_three
    norm_num
    nlinarith

end AaronsonAmbainis.Bridge

end
/- END UPSTREAM MODULE: AaronsonAmbainis.Bridge.Basic -/

/- BEGIN UPSTREAM MODULE: AaronsonAmbainis.Bridge.Fourier -/
section
/-!
# The Fourier expansion on the cube and the meaning of `HasDegreeLE`

The characters `chi S` are an orthogonal basis of the functions on the cube. Consequences:

* every `f` has `HasDegreeLE f (Fintype.card ι)`                       (`hasDegreeLE_card`);
* the coefficients in `HasDegreeLE` are unique                          (`fourier_unique`);
* `HasDegreeLE f d ↔` all Fourier coefficients above level `d` vanish   (`hasDegreeLE_iff_fourier`);
* `HasDegreeLE (chi S) d ↔ S.card ≤ d`                                  (`hasDegreeLE_chi_iff`),
  so `HasDegreeLE` separates every degree level and is not accidentally trivial.
-/

namespace AaronsonAmbainis.Bridge

open Finset

/-- Sign of a bit: `false ↦ 1`, `true ↦ -1`. -/
noncomputable def sg (b : Bool) : ℝ := if b then -1 else 1

theorem sg_mul_self (b : Bool) : sg b * sg b = 1 := by
  cases b <;> simp [sg]

theorem sg_not (b : Bool) : sg (!b) = -sg b := by
  cases b <;> simp [sg]

theorem sg_mul_of_ne {a b : Bool} (h : a ≠ b) : sg a * sg b = -1 := by
  cases a <;> cases b <;> simp_all [sg]

theorem chi_eq_prod_sg {ι : Type*} (S : Finset ι) (x : Cube ι) : chi S x = ∏ i ∈ S, sg (x i) :=
  rfl

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem chi_eq_prod_univ (S : Finset ι) (x : Cube ι) :
    chi S x = ∏ i, (if i ∈ S then sg (x i) else 1) := by
  rw [chi_eq_prod_sg, Fintype.prod_ite_mem]

/-- `χ_S χ_T = χ_{S Δ T}`. -/
theorem chi_mul_chi (S T : Finset ι) (x : Cube ι) :
    chi S x * chi T x = chi (symmDiff S T) x := by
  rw [chi_eq_prod_univ S, chi_eq_prod_univ T, chi_eq_prod_univ (symmDiff S T),
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;>
    simp [Finset.mem_symmDiff, hS, hT, sg_mul_self]

omit [Fintype ι] in
/-- Flipping a coordinate in `U` negates `χ_U`. -/
theorem chi_flip_mem {U : Finset ι} {j : ι} (hj : j ∈ U) (x : Cube ι) :
    chi U (flipSet x {j}) = -chi U x := by
  have h : ∏ i ∈ U.erase j, sg (flipSet x {j} i) = ∏ i ∈ U.erase j, sg (x i) :=
    Finset.prod_congr rfl
      (fun i hi => by rw [flipSet_singleton_ne x (Finset.ne_of_mem_erase hi)])
  rw [chi_eq_prod_sg, chi_eq_prod_sg,
    ← Finset.mul_prod_erase U (fun i => sg (flipSet x {j} i)) hj,
    ← Finset.mul_prod_erase U (fun i => sg (x i)) hj, h, flipSet_singleton_self, sg_not, neg_mul]

omit [DecidableEq ι] in
/-- Orthogonality, summing over the characters. -/
theorem sum_chi_mul_chi (x y : Cube ι) :
    ∑ S : Finset ι, chi S x * chi S y = if x = y then (2 : ℝ) ^ Fintype.card ι else 0 := by
  have h1 : ∑ S : Finset ι, chi S x * chi S y = ∏ i : ι, (1 + sg (x i) * sg (y i)) := by
    rw [Finset.prod_one_add, Finset.powerset_univ]
    refine Finset.sum_congr rfl (fun S _ => ?_)
    rw [chi_eq_prod_sg, chi_eq_prod_sg, ← Finset.prod_mul_distrib]
  rw [h1]
  split_ifs with h
  · have h2 : ∀ i : ι, (1 + sg (x i) * sg (y i)) = 2 := fun i => by
      rw [← h, sg_mul_self]
      norm_num
    simp only [h2, Finset.prod_const, Finset.card_univ]
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    rw [sg_mul_of_ne hi]
    norm_num

/-- `∑_x χ_U(x) = 2^n [U = ∅]`. -/
theorem sum_chi (U : Finset ι) :
    ∑ x : Cube ι, chi U x = if U = ∅ then (2 : ℝ) ^ Fintype.card ι else 0 := by
  split_ifs with h
  · subst h
    simp only [chi_empty, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    exact card_cube
  · obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr h
    have h1 : ∑ x : Cube ι, chi U (flipSet x {j}) = ∑ x : Cube ι, chi U x :=
      Equiv.sum_comp
        (Function.Involutive.toPerm (fun x : Cube ι => flipSet x {j})
          (fun x => flipSet_flipSet x {j})) (chi U)
    simp only [chi_flip_mem hj, Finset.sum_neg_distrib] at h1
    linarith

/-- Orthogonality, summing over the cube. -/
theorem sum_chi_mul_chi_cube (S T : Finset ι) :
    ∑ x : Cube ι, chi S x * chi T x = if S = T then (2 : ℝ) ^ Fintype.card ι else 0 := by
  simp only [chi_mul_chi, sum_chi, Finset.symmDiff_eq_empty]

/-- The Fourier coefficient of `f` at `S`. -/
noncomputable def fourier (f : Cube ι → ℝ) (S : Finset ι) : ℝ :=
  (∑ y, f y * chi S y) / 2 ^ Fintype.card ι

/-- Fourier inversion. -/
theorem fourier_inversion (f : Cube ι → ℝ) (x : Cube ι) :
    ∑ S, fourier f S * chi S x = f x := by
  have hne : (2 : ℝ) ^ Fintype.card ι ≠ 0 := by positivity
  calc ∑ S : Finset ι, fourier f S * chi S x
      = ∑ S : Finset ι, (∑ y, f y * (chi S x * chi S y)) / 2 ^ Fintype.card ι := by
        refine Finset.sum_congr rfl (fun S _ => ?_)
        rw [fourier, div_mul_eq_mul_div, Finset.sum_mul]
        congr 1
        refine Finset.sum_congr rfl (fun y _ => ?_)
        ring
    _ = (∑ y, ∑ S : Finset ι, f y * (chi S x * chi S y)) / 2 ^ Fintype.card ι := by
        rw [← Finset.sum_div, Finset.sum_comm]
    _ = (∑ y, f y * (if x = y then (2 : ℝ) ^ Fintype.card ι else 0)) / 2 ^ Fintype.card ι := by
        congr 1
        refine Finset.sum_congr rfl (fun y _ => ?_)
        rw [← Finset.mul_sum, sum_chi_mul_chi]
    _ = f x := by
        rw [Finset.sum_eq_single x]
        · rw [if_pos rfl, mul_div_assoc, div_self hne, mul_one]
        · intro y _ hy
          rw [if_neg (Ne.symm hy), mul_zero]
        · intro h
          exact absurd (Finset.mem_univ x) h

/-- Every function on the cube has degree at most the number of coordinates. -/
theorem hasDegreeLE_card (f : Cube ι → ℝ) : HasDegreeLE f (Fintype.card ι) :=
  ⟨fourier f, fun S hS => absurd (Finset.card_le_univ S) (not_le.mpr hS),
    fun x => (fourier_inversion f x).symm⟩

/-- The coefficients of a character expansion are unique: they are the Fourier coefficients. -/
theorem fourier_unique {f : Cube ι → ℝ} {c : Finset ι → ℝ}
    (hf : ∀ x, f x = ∑ S, c S * chi S x) (T : Finset ι) : c T = fourier f T := by
  have hne : (2 : ℝ) ^ Fintype.card ι ≠ 0 := by positivity
  have h1 : ∑ y, f y * chi T y = c T * 2 ^ Fintype.card ι := by
    calc ∑ y, f y * chi T y
        = ∑ y, ∑ S : Finset ι, c S * (chi S y * chi T y) := by
          refine Finset.sum_congr rfl (fun y _ => ?_)
          rw [hf y, Finset.sum_mul]
          refine Finset.sum_congr rfl (fun S _ => ?_)
          ring
      _ = ∑ S : Finset ι, c S * ∑ y, chi S y * chi T y := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun S _ => ?_)
          rw [Finset.mul_sum]
      _ = ∑ S : Finset ι, c S * (if S = T then (2 : ℝ) ^ Fintype.card ι else 0) := by
          simp only [sum_chi_mul_chi_cube]
      _ = c T * 2 ^ Fintype.card ι := by
          rw [Finset.sum_eq_single T]
          · rw [if_pos rfl]
          · intro S _ hS
            rw [if_neg hS, mul_zero]
          · intro h
            exact absurd (Finset.mem_univ T) h
  rw [fourier, h1, mul_div_assoc, div_self hne, mul_one]

/-- `HasDegreeLE f d` says exactly that the Fourier coefficients above level `d` vanish. -/
theorem hasDegreeLE_iff_fourier {f : Cube ι → ℝ} {d : ℕ} :
    HasDegreeLE f d ↔ ∀ S : Finset ι, d < S.card → fourier f S = 0 := by
  constructor
  · rintro ⟨c, hc, hf⟩ S hS
    rw [← fourier_unique hf S]
    exact hc S hS
  · intro h
    exact ⟨fourier f, h, fun x => (fourier_inversion f x).symm⟩

theorem fourier_chi (S T : Finset ι) : fourier (chi S) T = if S = T then 1 else 0 := by
  rw [fourier, sum_chi_mul_chi_cube]
  split_ifs
  · exact div_self (by positivity)
  · exact zero_div _

/-- A character `χ_S` has degree at most `d` exactly when `|S| ≤ d`. -/
theorem hasDegreeLE_chi_iff (S : Finset ι) (d : ℕ) : HasDegreeLE (chi S) d ↔ S.card ≤ d := by
  rw [hasDegreeLE_iff_fourier]
  constructor
  · intro h
    by_contra hlt
    have h1 := h S (not_le.mp hlt)
    rw [fourier_chi, if_pos rfl] at h1
    exact one_ne_zero h1
  · intro h T hT
    rw [fourier_chi, if_neg]
    rintro rfl
    exact absurd h (not_le.mpr hT)

/-- The full parity does not have degree `< n`: `HasDegreeLE` is not trivially true. -/
theorem parity_not_hasDegreeLE {d : ℕ} (hd : d < Fintype.card ι) :
    ¬ HasDegreeLE (chi (univ : Finset ι)) d := by
  rw [hasDegreeLE_chi_iff, Finset.card_univ]
  exact not_le.mpr hd

end AaronsonAmbainis.Bridge

end
/- END UPSTREAM MODULE: AaronsonAmbainis.Bridge.Fourier -/

/- BEGIN UPSTREAM MODULE: AaronsonAmbainis.Bridge.Algebra -/
section
/-!
# Closure properties of `HasDegreeLE`

`HasDegreeLE` is closed under constants, sums, scalar multiples, products (degrees add), powers
and finite products; the coordinate functions have degree at most `1`.
These are what makes `HasDegreeLE` a degree in the usual sense.
-/

namespace AaronsonAmbainis.Bridge

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem hasDegreeLE_const (a : ℝ) (d : ℕ) : HasDegreeLE (fun _ : Cube ι => a) d :=
  hasDegreeLE_mono (hasDegreeLE_zero_iff.mpr ⟨a, fun _ => rfl⟩) (Nat.zero_le d)

omit [DecidableEq ι] in
theorem hasDegreeLE_add {f g : Cube ι → ℝ} {d : ℕ} (hf : HasDegreeLE f d)
    (hg : HasDegreeLE g d) : HasDegreeLE (fun x => f x + g x) d := by
  obtain ⟨a, ha, hfa⟩ := hf
  obtain ⟨b, hb, hgb⟩ := hg
  refine ⟨fun S => a S + b S, fun S hS => by show a S + b S = 0; rw [ha S hS, hb S hS, add_zero], fun x => ?_⟩
  show f x + g x = ∑ S, (a S + b S) * chi S x
  simp only [add_mul, Finset.sum_add_distrib]
  rw [← hfa x, ← hgb x]

omit [DecidableEq ι] in
theorem hasDegreeLE_smul (r : ℝ) {f : Cube ι → ℝ} {d : ℕ} (hf : HasDegreeLE f d) :
    HasDegreeLE (fun x => r * f x) d := by
  obtain ⟨a, ha, hfa⟩ := hf
  refine ⟨fun S => r * a S, fun S hS => by show r * a S = 0; rw [ha S hS, mul_zero], fun x => ?_⟩
  show r * f x = ∑ S, r * a S * chi S x
  rw [hfa x, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  ring

theorem hasDegreeLE_sum {α : Type*} (s : Finset α) {F : α → Cube ι → ℝ} {d : ℕ}
    (h : ∀ k ∈ s, HasDegreeLE (F k) d) : HasDegreeLE (fun x => ∑ k ∈ s, F k x) d := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hasDegreeLE_const (ι := ι) 0 d
  | insert k s hk ih =>
    have h1 : HasDegreeLE (fun x => F k x + ∑ k ∈ s, F k x) d :=
      hasDegreeLE_add (h k (Finset.mem_insert_self k s))
        (ih (fun k' hk' => h k' (Finset.mem_insert_of_mem hk')))
    have h2 : (fun x => ∑ k ∈ insert k s, F k x) = fun x => F k x + ∑ k ∈ s, F k x := by
      funext x
      rw [Finset.sum_insert hk]
    rw [h2]
    exact h1

theorem hasDegreeLE_chi (S : Finset ι) : HasDegreeLE (chi S) S.card :=
  (hasDegreeLE_chi_iff S S.card).mpr le_rfl

omit [Fintype ι] in
theorem card_symmDiff_le (S T : Finset ι) : (symmDiff S T).card ≤ S.card + T.card := by
  refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le S T)
  intro i hi
  rw [Finset.mem_symmDiff] at hi
  rw [Finset.mem_union]
  rcases hi with ⟨h, _⟩ | ⟨h, _⟩
  · exact Or.inl h
  · exact Or.inr h

/-- Degrees add under multiplication. -/
theorem hasDegreeLE_mul {f g : Cube ι → ℝ} {d e : ℕ} (hf : HasDegreeLE f d)
    (hg : HasDegreeLE g e) : HasDegreeLE (fun x => f x * g x) (d + e) := by
  obtain ⟨a, ha, hfa⟩ := hf
  obtain ⟨b, hb, hgb⟩ := hg
  have h1 : (fun x => f x * g x)
      = fun x => ∑ S : Finset ι, ∑ T : Finset ι, (a S * b T) * chi (symmDiff S T) x := by
    funext x
    rw [hfa x, hgb x, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun S _ => Finset.sum_congr rfl (fun T _ => ?_))
    rw [← chi_mul_chi]
    ring
  rw [h1]
  refine hasDegreeLE_sum _ (fun S _ => hasDegreeLE_sum _ (fun T _ => ?_))
  by_cases hS : d < S.card
  · have h0 : (fun x => a S * b T * chi (symmDiff S T) x) = fun _ => 0 := by
      funext x
      rw [ha S hS]
      ring
    rw [h0]
    exact hasDegreeLE_const 0 _
  · by_cases hT : e < T.card
    · have h0 : (fun x => a S * b T * chi (symmDiff S T) x) = fun _ => 0 := by
        funext x
        rw [hb T hT]
        ring
      rw [h0]
      exact hasDegreeLE_const 0 _
    · refine hasDegreeLE_smul _ (hasDegreeLE_mono (hasDegreeLE_chi _) ?_)
      exact (card_symmDiff_le S T).trans (Nat.add_le_add (not_lt.mp hS) (not_lt.mp hT))

theorem hasDegreeLE_pow {g : Cube ι → ℝ} {k : ℕ} (hg : HasDegreeLE g k) (m : ℕ) :
    HasDegreeLE (fun x => g x ^ m) (m * k) := by
  induction m with
  | zero => simpa using hasDegreeLE_const (ι := ι) 1 0
  | succ m ih =>
    have h2 : (fun x => g x ^ (m + 1)) = fun x => g x ^ m * g x := by
      funext x
      rw [pow_succ]
    rw [h2, add_one_mul]
    exact hasDegreeLE_mul ih hg

theorem hasDegreeLE_prod {α : Type*} (s : Finset α) {F : α → Cube ι → ℝ} {k : α → ℕ}
    (h : ∀ a ∈ s, HasDegreeLE (F a) (k a)) :
    HasDegreeLE (fun x => ∏ a ∈ s, F a x) (∑ a ∈ s, k a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hasDegreeLE_const (ι := ι) 1 0
  | insert a s ha ih =>
    have h2 : (fun x => ∏ a ∈ insert a s, F a x) = fun x => F a x * ∏ a ∈ s, F a x := by
      funext x
      rw [Finset.prod_insert ha]
    rw [h2, Finset.sum_insert ha]
    exact hasDegreeLE_mul (h a (Finset.mem_insert_self a s))
      (ih (fun a' ha' => h a' (Finset.mem_insert_of_mem ha')))

/-- The `±1` coordinate function has degree at most `1`. -/
theorem hasDegreeLE_pm_coord (i : ι) :
    HasDegreeLE (fun x : Cube ι => if x i then (-1 : ℝ) else 1) 1 :=
  dict_hasDegreeLE_one i

/-- The `0/1` coordinate function has degree at most `1`. -/
theorem hasDegreeLE_zo_coord (i : ι) :
    HasDegreeLE (fun x : Cube ι => if x i then (1 : ℝ) else 0) 1 := by
  have h : (fun x : Cube ι => if x i then (1 : ℝ) else 0)
      = fun x => (1 / 2 : ℝ) + (-1 / 2) * dict i x := by
    funext x
    unfold dict
    split_ifs <;> norm_num
  rw [h]
  exact hasDegreeLE_add (hasDegreeLE_const _ 1) (hasDegreeLE_smul _ (dict_hasDegreeLE_one i))

end AaronsonAmbainis.Bridge

end
/- END UPSTREAM MODULE: AaronsonAmbainis.Bridge.Algebra -/

/- BEGIN UPSTREAM MODULE: AaronsonAmbainis.Bridge.Poly -/
section
/-!
# `HasDegreeLE` and polynomials of bounded total degree

`HasDegreeLE f d` holds exactly when `f` is the restriction to the cube of a real polynomial
(`MvPolynomial ι ℝ`, not necessarily multilinear) of total degree at most `d`;
this is proved for both encodings of the cube (`hasDegreeLE_iff_poly_zo`,
`hasDegreeLE_iff_poly_pm`):

* `zoPt x`: `true ↦ 1`, `false ↦ 0`   (the cube `{0,1}^n` of Conjecture 6 of arXiv:0911.0996 and
  of Theorem 1.7 of arXiv:2410.19062);
* `pmPt x`: `true ↦ -1`, `false ↦ 1`  (the cube `{1,-1}^n` in the convention of `Defs.lean`; the
  statement `ExplicitBoundPM` of `Conjecture.lean` sends `true` to `1`, see `PrintedAA.lean`).
-/

namespace AaronsonAmbainis.Bridge

open Finset MvPolynomial

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The point of `{0,1}^ι` attached to a point of the cube (`true ↦ 1`, `false ↦ 0`). -/
noncomputable def zoPt (x : Cube ι) : ι → ℝ := fun i => if x i then 1 else 0

/-- The point of `{1,-1}^ι` attached to a point of the cube (`true ↦ -1`, `false ↦ 1`). -/
noncomputable def pmPt (x : Cube ι) : ι → ℝ := fun i => if x i then -1 else 1

/-- Restricting a polynomial of total degree `≤ d` along a point map whose coordinates have
degree `≤ 1` gives a function of degree `≤ d`. -/
theorem hasDegreeLE_eval {v : Cube ι → ι → ℝ} (hv : ∀ i, HasDegreeLE (fun x => v x i) 1)
    (p : MvPolynomial ι ℝ) {d : ℕ} (hp : p.totalDegree ≤ d) :
    HasDegreeLE (fun x => MvPolynomial.eval (v x) p) d := by
  have h1 : (fun x => MvPolynomial.eval (v x) p)
      = fun x => ∑ m ∈ p.support, p.coeff m * ∏ i, v x i ^ m i := by
    funext x
    exact MvPolynomial.eval_eq' (v x) p
  rw [h1]
  refine hasDegreeLE_sum _ (fun m hm => hasDegreeLE_smul _ ?_)
  have h2 : ∑ i, m i ≤ d := by
    have h3 := MvPolynomial.le_totalDegree hm
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)] at h3
    exact h3.trans hp
  refine hasDegreeLE_mono ?_ h2
  have h4 : HasDegreeLE (fun x => ∏ i, v x i ^ m i) (∑ i, m i * 1) :=
    hasDegreeLE_prod (univ : Finset ι) (F := fun i x => v x i ^ m i) (k := fun i => m i * 1)
      (fun i _ => hasDegreeLE_pow (hv i) (m i))
  simpa only [mul_one] using h4

theorem hasDegreeLE_eval_zo (p : MvPolynomial ι ℝ) {d : ℕ} (hp : p.totalDegree ≤ d) :
    HasDegreeLE (fun x : Cube ι => MvPolynomial.eval (zoPt x) p) d :=
  hasDegreeLE_eval (v := zoPt) hasDegreeLE_zo_coord p hp

theorem hasDegreeLE_eval_pm (p : MvPolynomial ι ℝ) {d : ℕ} (hp : p.totalDegree ≤ d) :
    HasDegreeLE (fun x : Cube ι => MvPolynomial.eval (pmPt x) p) d :=
  hasDegreeLE_eval (v := pmPt) hasDegreeLE_pm_coord p hp

omit [Fintype ι] [DecidableEq ι] in
theorem totalDegree_letter (a b : ℝ) (i : ι) :
    (C a + C b * X i : MvPolynomial ι ℝ).totalDegree ≤ 1 := by
  refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
  · rw [MvPolynomial.totalDegree_C]
    exact Nat.zero_le 1
  · refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X, zero_add]

omit [DecidableEq ι] in
/-- A function of degree `≤ d` is the restriction of a polynomial of total degree `≤ d` in the
coordinates `v x i`, as soon as the sign `(-1)^{x_i}` is an affine function of `v x i`. -/
theorem exists_poly_of_hasDegreeLE {v : Cube ι → ι → ℝ} {a b : ℝ}
    (hv : ∀ x i, (if x i then (-1 : ℝ) else 1) = a + b * v x i)
    {f : Cube ι → ℝ} {d : ℕ} (h : HasDegreeLE f d) :
    ∃ p : MvPolynomial ι ℝ, p.totalDegree ≤ d ∧ ∀ x, f x = MvPolynomial.eval (v x) p := by
  obtain ⟨c, hc, hf⟩ := h
  refine ⟨∑ S : Finset ι, C (c S) * ∏ i ∈ S, (C a + C b * X i), ?_, fun x => ?_⟩
  · refine MvPolynomial.totalDegree_finsetSum_le (fun S _ => ?_)
    by_cases hS : d < S.card
    · rw [hc S hS, C_0, zero_mul, MvPolynomial.totalDegree_zero]
      exact Nat.zero_le d
    · refine (MvPolynomial.totalDegree_mul _ _).trans ?_
      rw [MvPolynomial.totalDegree_C, zero_add]
      refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
      refine (Finset.sum_le_sum (fun i _ => totalDegree_letter a b i)).trans ?_
      rw [Finset.sum_const, smul_eq_mul, mul_one]
      exact not_lt.mp hS
  · rw [hf x, map_sum]
    refine Finset.sum_congr rfl (fun S _ => ?_)
    rw [map_mul, MvPolynomial.eval_C, map_prod]
    congr 1
    unfold chi
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [map_add, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_C, MvPolynomial.eval_X]
    exact hv x i

/-- `HasDegreeLE f d` ⟺ `f` is a polynomial of total degree `≤ d` in the `0/1` coordinates. -/
theorem hasDegreeLE_iff_poly_zo {f : Cube ι → ℝ} {d : ℕ} :
    HasDegreeLE f d ↔
      ∃ p : MvPolynomial ι ℝ, p.totalDegree ≤ d ∧ ∀ x, f x = MvPolynomial.eval (zoPt x) p := by
  constructor
  · exact exists_poly_of_hasDegreeLE (a := 1) (b := -2)
      (fun x i => by unfold zoPt; split_ifs <;> norm_num)
  · rintro ⟨p, hp, hf⟩
    have h : f = fun x => MvPolynomial.eval (zoPt x) p := funext hf
    rw [h]
    exact hasDegreeLE_eval_zo p hp

/-- `HasDegreeLE f d` ⟺ `f` is a polynomial of total degree `≤ d` in the `±1` coordinates. -/
theorem hasDegreeLE_iff_poly_pm {f : Cube ι → ℝ} {d : ℕ} :
    HasDegreeLE f d ↔
      ∃ p : MvPolynomial ι ℝ, p.totalDegree ≤ d ∧ ∀ x, f x = MvPolynomial.eval (pmPt x) p := by
  constructor
  · exact exists_poly_of_hasDegreeLE (a := 0) (b := 1)
      (fun x i => by unfold pmPt; split_ifs <;> norm_num)
  · rintro ⟨p, hp, hf⟩
    have h : f = fun x => MvPolynomial.eval (pmPt x) p := funext hf
    rw [h]
    exact hasDegreeLE_eval_pm p hp

end AaronsonAmbainis.Bridge

end
/- END UPSTREAM MODULE: AaronsonAmbainis.Bridge.Poly -/

/- BEGIN UPSTREAM MODULE: AaronsonAmbainis.Bridge.Transport -/
section
/-!
# `RowBound` on the index types `Fin n`

`RowBound` quantifies over all finite index types `ι : Type`; Theorem 1.7 of arXiv:2410.19062 is
about `[n]`. The statement restricted to the index types `Fin n` (`RowBoundFin`) already implies
`RowBound` (transport along `Fintype.equivFin`). So the generality of `RowBound` in the index type
asks for nothing beyond the `[n]` statement (`rowBound_iff_fin`).
-/

namespace AaronsonAmbainis.Bridge

open Finset

/-- `RowBound`, restricted to the index types `Fin n`. -/
def RowBoundFin : Prop :=
  ∀ (n d : ℕ) (f : Cube (Fin n) → ℝ), (∀ x, 0 ≤ f x ∧ f x ≤ 1) → HasDegreeLE f d →
    ∃ c : Cube (Fin n) → Fin n → ℝ,
      (∀ x y, |f x - f y| ≤ ∑ i ∈ diffSet x y, c x i) ∧
      (∀ x, ∑ i, c x i ≤ Real.pi ^ 2 / 4 * (d : ℝ) ^ 2)

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
theorem chi_comp_equiv (e : ι ≃ κ) (S : Finset ι) (y : Cube κ) :
    chi S (fun i => y (e i)) = chi (S.map e.toEmbedding) y := by
  simp [chi, Finset.prod_map]

omit [DecidableEq ι] [DecidableEq κ] in
/-- `HasDegreeLE` is invariant under relabelling the coordinates. -/
theorem hasDegreeLE_comp_equiv (e : ι ≃ κ) {f : Cube ι → ℝ} {d : ℕ} (h : HasDegreeLE f d) :
    HasDegreeLE (fun y : Cube κ => f (fun i => y (e i))) d := by
  obtain ⟨c, hc, hf⟩ := h
  refine ⟨fun T => c (T.map e.symm.toEmbedding),
    fun T hT => hc _ (by rwa [Finset.card_map]), fun y => ?_⟩
  show f (fun i => y (e i)) = ∑ T : Finset κ, c (T.map e.symm.toEmbedding) * chi T y
  rw [hf]
  refine Fintype.sum_equiv e.finsetCongr _ _ (fun S => ?_)
  show c S * chi S (fun i => y (e i))
    = c ((e.finsetCongr S).map e.symm.toEmbedding) * chi (e.finsetCongr S) y
  have h1 : (e.finsetCongr S).map e.symm.toEmbedding = S := e.finsetCongr.left_inv S
  rw [h1, chi_comp_equiv]
  rfl

omit [DecidableEq ι] [DecidableEq κ] in
theorem diffSet_comp_equiv (e : ι ≃ κ) (x y : Cube ι) :
    diffSet (fun k => x (e.symm k)) (fun k => y (e.symm k))
      = (diffSet x y).map e.toEmbedding := by
  ext k
  simp only [diffSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
    Equiv.coe_toEmbedding]
  constructor
  · intro h
    exact ⟨e.symm k, h, e.apply_symm_apply k⟩
  · rintro ⟨i, hi, rfl⟩
    simpa using hi

omit [DecidableEq ι] [DecidableEq κ] in
/-- The conclusion of `RowBound` transports along an equivalence of index types. -/
theorem rowBound_concl_transport (e : ι ≃ κ) (f : Cube ι → ℝ) (B : ℝ)
    (h : ∃ c : Cube κ → κ → ℝ,
      (∀ x y, |f (fun i => x (e i)) - f (fun i => y (e i))| ≤ ∑ k ∈ diffSet x y, c x k) ∧
      (∀ x, ∑ k, c x k ≤ B)) :
    ∃ c : Cube ι → ι → ℝ,
      (∀ x y, |f x - f y| ≤ ∑ i ∈ diffSet x y, c x i) ∧ (∀ x, ∑ i, c x i ≤ B) := by
  obtain ⟨c, hc1, hc2⟩ := h
  refine ⟨fun x i => c (fun k => x (e.symm k)) (e i), fun x y => ?_, fun x => ?_⟩
  · have h1 := hc1 (fun k => x (e.symm k)) (fun k => y (e.symm k))
    simp only [Equiv.symm_apply_apply] at h1
    rw [diffSet_comp_equiv, Finset.sum_map] at h1
    exact h1
  · have h2 := hc2 (fun k => x (e.symm k))
    rw [← Equiv.sum_comp e] at h2
    exact h2

/-- The `[n]` statement implies the statement for all finite index types. -/
theorem rowBound_of_fin (h : RowBoundFin) : RowBound := by
  intro ι _ _ d f hf hdeg
  refine rowBound_concl_transport (Fintype.equivFin ι) f _ ?_
  exact h (Fintype.card ι) d (fun y => f (fun i => y (Fintype.equivFin ι i)))
    (fun y => hf _) (hasDegreeLE_comp_equiv (Fintype.equivFin ι) hdeg)

theorem rowBoundFin_of_rowBound (h : RowBound) : RowBoundFin :=
  fun n d f hf hdeg => h (Fin n) d f hf hdeg

/-- `RowBound` is equivalent to its restriction to the index types `Fin n`. -/
theorem rowBound_iff_fin : RowBound ↔ RowBoundFin :=
  ⟨rowBoundFin_of_rowBound, rowBound_of_fin⟩

end AaronsonAmbainis.Bridge

end
/- END UPSTREAM MODULE: AaronsonAmbainis.Bridge.Transport -/

/- BEGIN UPSTREAM MODULE: AaronsonAmbainis.Bridge.ZeroOne -/
section
/-!
# `HasDegreeLE` with `0/1` monomials

`HasDegreeLE` is defined with the characters `∏_{i∈S} (-1)^{x_i}`. Theorem 1.7 of
arXiv:2410.19062 and Conjecture 6 of arXiv:0911.0996 speak of polynomials in the `0/1` variables.
The definition with the `0/1` monomials `∏_{i∈S} x_i` is equivalent (`hasDegreeLE_iff_01`).
-/

namespace AaronsonAmbainis.Bridge

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Monomial in the letters `φ (x i)`. -/
noncomputable def mon (φ : Bool → ℝ) (S : Finset ι) (x : Cube ι) : ℝ := ∏ i ∈ S, φ (x i)

/-- Degree at most `d` with respect to the monomials built from the letter `φ`. -/
def HasDegLE (φ : Bool → ℝ) (f : Cube ι → ℝ) (d : ℕ) : Prop :=
  ∃ c : Finset ι → ℝ, (∀ S, d < S.card → c S = 0) ∧ ∀ x, f x = ∑ S, c S * mon φ S x

/-- The analogue of `HasDegreeLE` with the `0/1` monomials `∏_{i∈S} x_i`. -/
def HasDegreeLE01 (f : Cube ι → ℝ) (d : ℕ) : Prop :=
  ∃ c : Finset ι → ℝ, (∀ S, d < S.card → c S = 0) ∧
    ∀ x, f x = ∑ S, c S * ∏ i ∈ S, (if x i then (1 : ℝ) else 0)

omit [DecidableEq ι] in
theorem hasDegreeLE_iff_hasDegLE {f : Cube ι → ℝ} {d : ℕ} :
    HasDegreeLE f d ↔ HasDegLE (fun b => if b then (-1 : ℝ) else 1) f d :=
  Iff.rfl

omit [DecidableEq ι] in
theorem hasDegreeLE01_iff_hasDegLE {f : Cube ι → ℝ} {d : ℕ} :
    HasDegreeLE01 f d ↔ HasDegLE (fun b => if b then (1 : ℝ) else 0) f d :=
  Iff.rfl

/-- Expansion of a monomial after an affine change of letter `ψ = β φ + α`. -/
theorem mon_affine {φ ψ : Bool → ℝ} {α β : ℝ} (hψ : ∀ b, ψ b = β * φ b + α) (S : Finset ι)
    (x : Cube ι) :
    mon ψ S x
      = ∑ T : Finset ι, if T ⊆ S then β ^ T.card * α ^ (S \ T).card * mon φ T x else 0 := by
  have hpow : S.powerset = univ.filter (fun T => T ⊆ S) := by
    ext T
    simp [Finset.mem_powerset]
  unfold mon
  simp only [hψ]
  rw [Finset.prod_add, hpow, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun T _ => ?_)
  split_ifs with hT
  · rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_const]
    ring
  · rfl

/-- An affine change of letter does not raise the degree. -/
theorem hasDegLE_of_affine {φ ψ : Bool → ℝ} {α β : ℝ} (hψ : ∀ b, ψ b = β * φ b + α)
    {f : Cube ι → ℝ} {d : ℕ} (h : HasDegLE ψ f d) : HasDegLE φ f d := by
  obtain ⟨c, hc, hf⟩ := h
  refine ⟨fun T => ∑ S : Finset ι, if T ⊆ S then c S * (β ^ T.card * α ^ (S \ T).card) else 0,
    fun T hT => ?_, fun x => ?_⟩
  · refine Finset.sum_eq_zero (fun S _ => ?_)
    split_ifs with hTS
    · rw [hc S (lt_of_lt_of_le hT (Finset.card_le_card hTS)), zero_mul]
    · rfl
  · rw [hf x]
    simp only [mon_affine hψ, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun T _ => Finset.sum_congr rfl (fun S _ => ?_))
    split_ifs <;> ring

/-- `HasDegreeLE` (characters) is equivalent to the definition with `0/1` monomials. -/
theorem hasDegreeLE_iff_01 {f : Cube ι → ℝ} {d : ℕ} : HasDegreeLE f d ↔ HasDegreeLE01 f d := by
  rw [hasDegreeLE_iff_hasDegLE, hasDegreeLE01_iff_hasDegLE]
  constructor
  · -- `(-1)^b = (-2) * b + 1`
    exact hasDegLE_of_affine (α := 1) (β := -2) (fun b => by cases b <;> norm_num)
  · -- `b = (-1/2) * (-1)^b + 1/2`
    exact hasDegLE_of_affine (α := 1 / 2) (β := -1 / 2) (fun b => by cases b <;> norm_num)

end AaronsonAmbainis.Bridge

end
/- END UPSTREAM MODULE: AaronsonAmbainis.Bridge.ZeroOne -/

/- BEGIN UPSTREAM MODULE: AaronsonAmbainis.Bridge.PrintedRow -/
section
/-!
# `RowBound` and Theorem 1.7 of arXiv:2410.19062 as printed

Source: A. Agarwal and S. Ben-David, *Oracle separations for the quantum-classical polynomial
hierarchy*, arXiv:2410.19062 (version 2), Theorem 1.7:

  Let `f : {0,1}^n → [0,1]` be a real-valued function which can be expressed as a polynomial of
  degree at most `d`. Then there is an assignment of weights `{c_{x,i}}_{x∈{0,1}^n, i∈[n]}` to
  inputs `x` and positions `i ∈ [n]` such that for all `x, y ∈ {0,1}^n`, we have
  `∑_{i : x_i ≠ y_i} c_{x,i} ≥ |f(x) - f(y)|`  and  `∑_{i=1}^n c_{x,i} ≤ (π²/4) d²`.

`FbsDegPrinted` transcribes this sentence with Mathlib notions only (no definition of `Defs.lean`
is used) and in its weakest reading: only `n ≥ 1`, only `d ≥ 1`, no sign condition on the weights
in the conclusion. `FbsDegPrintedML` is the same with the narrowest reading of the hypothesis (a
multilinear polynomial in the `0/1` variables with no monomial of size `> d`).

Result: `RowBound ↔ FbsDegPrinted ↔ FbsDegPrintedML`. So the hypothesis `RowBound` asks for
nothing beyond the printed theorem. Also: a `RowBound` weight system is automatically nonnegative
(`weights_nonneg_of_row`).
-/

namespace AaronsonAmbainis.Bridge

open Finset MvPolynomial

/-- The conclusion of the printed theorem for one function, written with Mathlib notions only. -/
def PrintedConcl {n : ℕ} (f : (Fin n → Bool) → ℝ) (d : ℕ) : Prop :=
  ∃ c : (Fin n → Bool) → Fin n → ℝ,
    (∀ x y, ∑ i ∈ univ.filter (fun i => x i ≠ y i), c x i ≥ |f x - f y|) ∧
    (∀ x, ∑ i, c x i ≤ Real.pi ^ 2 / 4 * (d : ℝ) ^ 2)

/-- Theorem 1.7 of arXiv:2410.19062 as printed, for `n ≥ 1` and `d ≥ 1` ("can be expressed as a
polynomial of degree at most `d`": some real polynomial of total degree `≤ d` agrees with `f` on
`{0,1}^n`). -/
def FbsDegPrinted : Prop :=
  ∀ (n d : ℕ), 1 ≤ n → 1 ≤ d → ∀ f : (Fin n → Bool) → ℝ, (∀ x, 0 ≤ f x ∧ f x ≤ 1) →
    (∃ p : MvPolynomial (Fin n) ℝ, p.totalDegree ≤ d ∧
      ∀ x, f x = MvPolynomial.eval (fun i => if x i then (1 : ℝ) else 0) p) →
    PrintedConcl f d

/-- Theorem 1.7 of arXiv:2410.19062 with the narrowest reading of the hypothesis: `f` is a
multilinear polynomial in the `0/1` variables with no monomial of size `> d`. -/
def FbsDegPrintedML : Prop :=
  ∀ (n d : ℕ), 1 ≤ n → 1 ≤ d → ∀ f : (Fin n → Bool) → ℝ, (∀ x, 0 ≤ f x ∧ f x ≤ 1) →
    (∃ a : Finset (Fin n) → ℝ, (∀ S, d < S.card → a S = 0) ∧
      ∀ x, f x = ∑ S, a S * ∏ i ∈ S, (if x i then (1 : ℝ) else 0)) →
    PrintedConcl f d

/-- The printed conclusion is literally the conclusion of `RowBound`. -/
theorem printedConcl_iff {n : ℕ} (f : Cube (Fin n) → ℝ) (d : ℕ) :
    PrintedConcl f d ↔ ∃ c : Cube (Fin n) → Fin n → ℝ,
      (∀ x y, |f x - f y| ≤ ∑ i ∈ diffSet x y, c x i) ∧
      (∀ x, ∑ i, c x i ≤ Real.pi ^ 2 / 4 * (d : ℝ) ^ 2) :=
  Iff.rfl

/-- For a constant function the conclusion holds with zero weights, for every `d`. -/
theorem printedConcl_of_const {n : ℕ} {f : (Fin n → Bool) → ℝ} (h : ∀ x y, f x = f y) (d : ℕ) :
    PrintedConcl f d := by
  refine ⟨fun _ _ => 0, fun x y => ?_, fun x => ?_⟩
  · rw [h x y, sub_self, abs_zero]
    simp
  · simp only [Finset.sum_const_zero]
    positivity

/-- The cases `n = 0` and `d = 0` of `RowBoundFin` are trivially true, so the statement
restricted to `n ≥ 1`, `d ≥ 1` already gives `RowBoundFin`. -/
theorem rowBoundFin_of_restricted
    (h : ∀ (n d : ℕ), 1 ≤ n → 1 ≤ d → ∀ f : Cube (Fin n) → ℝ, (∀ x, 0 ≤ f x ∧ f x ≤ 1) →
      HasDegreeLE f d → PrintedConcl f d) : RowBoundFin := by
  intro n d f hf hdeg
  refine (printedConcl_iff f d).mp ?_
  by_cases hd : d = 0
  · subst hd
    exact printedConcl_of_const (hasDegreeLE_zero_const hdeg) 0
  by_cases hn : n = 0
  · subst hn
    exact printedConcl_of_const (fun x y => congrArg f (Subsingleton.elim x y)) d
  exact h n d (Nat.one_le_iff_ne_zero.mpr hn) (Nat.one_le_iff_ne_zero.mpr hd) f hf hdeg

/-- The printed theorem implies the hypothesis `RowBound`. -/
theorem rowBound_of_printed (h : FbsDegPrinted) : RowBound :=
  rowBound_of_fin (rowBoundFin_of_restricted
    (fun n d hn hd f hf hdeg => h n d hn hd f hf (hasDegreeLE_iff_poly_zo.mp hdeg)))

/-- The printed theorem in its narrowest reading implies the hypothesis `RowBound`. -/
theorem rowBound_of_printedML (h : FbsDegPrintedML) : RowBound :=
  rowBound_of_fin (rowBoundFin_of_restricted
    (fun n d hn hd f hf hdeg => h n d hn hd f hf (hasDegreeLE_iff_01.mp hdeg)))

/-- Conversely `RowBound` gives the printed theorem (so it says neither more nor less). -/
theorem printed_of_rowBound (h : RowBound) : FbsDegPrinted :=
  fun n d _ _ f hf hp =>
    (printedConcl_iff f d).mpr (h (Fin n) d f hf (hasDegreeLE_iff_poly_zo.mpr hp))

theorem printedML_of_rowBound (h : RowBound) : FbsDegPrintedML :=
  fun n d _ _ f hf hp =>
    (printedConcl_iff f d).mpr (h (Fin n) d f hf (hasDegreeLE_iff_01.mpr hp))

/-- `RowBound` is equivalent to Theorem 1.7 of arXiv:2410.19062 as printed. -/
theorem rowBound_iff_printed : RowBound ↔ FbsDegPrinted :=
  ⟨printed_of_rowBound, rowBound_of_printed⟩

/-- `RowBound` is equivalent to the printed theorem in its narrowest reading. -/
theorem rowBound_iff_printedML : RowBound ↔ FbsDegPrintedML :=
  ⟨printedML_of_rowBound, rowBound_of_printedML⟩

/-- Weights satisfying the first condition of `RowBound` are nonnegative (take `y = x^i`). -/
theorem weights_nonneg_of_row {ι : Type*} [Fintype ι] [DecidableEq ι] {f : Cube ι → ℝ}
    {c : Cube ι → ι → ℝ} (h : ∀ x y, |f x - f y| ≤ ∑ i ∈ diffSet x y, c x i) (x : Cube ι)
    (i : ι) : 0 ≤ c x i := by
  have h1 := h x (flipSet x {i})
  rw [diffSet_flipSet, Finset.sum_singleton] at h1
  exact (abs_nonneg _).trans h1

/-- So `RowBound` implies its own strengthening with nonnegative weights. -/
theorem rowBound_nonneg (h : RowBound) (ι : Type) [Fintype ι] [DecidableEq ι] (d : ℕ)
    (f : Cube ι → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (hdeg : HasDegreeLE f d) :
    ∃ c : Cube ι → ι → ℝ, (∀ x i, 0 ≤ c x i) ∧
      (∀ x y, |f x - f y| ≤ ∑ i ∈ diffSet x y, c x i) ∧
      (∀ x, ∑ i, c x i ≤ Real.pi ^ 2 / 4 * (d : ℝ) ^ 2) := by
  obtain ⟨c, h1, h2⟩ := h ι d f hf hdeg
  exact ⟨c, weights_nonneg_of_row h1, h1, h2⟩

end AaronsonAmbainis.Bridge

end
/- END UPSTREAM MODULE: AaronsonAmbainis.Bridge.PrintedRow -/

/- BEGIN UPSTREAM MODULE: AaronsonAmbainis.Bridge.Affine -/
section
/-!
# `mean`, `variance`, `inflR` under affine maps; degenerate cases

* `mean`, `variance`, `inflR` of `a + b * g`                  (`mean_affine`, `variance_affine`,
  `inflR_affine`): the change of normalisation `[0,1] ↔ [-1,1]` multiplies variance and
  influence by the same factor `4`.
* The hypothesis `0 < variance f` of `MainTheorem` forces `1 ≤ d` and a nonempty index type
  (`aa_hyps_force`): the instances `d = 0` and `ι = ∅` of `MainTheorem` are vacuous, and these
  are exactly the instances in which no coordinate can have positive influence.
* `variance f ≤ 1` if `|f| ≤ 1`, `variance P ≤ 1/4` if `0 ≤ P ≤ 1`.

The elementary facts on the variance that are used here are in `Level/Basic.lean`.
-/

namespace AaronsonAmbainis.Bridge

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem mean_affine (a b : ℝ) (g : Cube ι → ℝ) :
    mean (fun x => a + b * g x) = a + b * mean g := by
  have hne : (2 : ℝ) ^ Fintype.card ι ≠ 0 := by positivity
  simp only [mean]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_cube,
    ← Finset.mul_sum, add_div, mul_div_cancel_left₀ a hne, mul_div_assoc]

theorem variance_affine (a b : ℝ) (g : Cube ι → ℝ) :
    variance (fun x => a + b * g x) = b ^ 2 * variance g := by
  have h : ∀ x : Cube ι, (a + b * g x - (a + b * mean g)) ^ 2 = b ^ 2 * (g x - mean g) ^ 2 :=
    fun x => by ring
  simp only [variance, mean_affine, h]
  rw [← Finset.mul_sum, mul_div_assoc]

theorem inflR_affine (a b : ℝ) (g : Cube ι → ℝ) (j : ι) :
    inflR (fun x => a + b * g x) j = b ^ 2 * inflR g j := by
  have h : ∀ x : Cube ι, ((a + b * g x - (a + b * g (flipSet x {j}))) / 2) ^ 2
      = b ^ 2 * ((g x - g (flipSet x {j})) / 2) ^ 2 := fun x => by ring
  simp only [inflR, h]
  rw [← Finset.mul_sum, mul_div_assoc]

/-! ### Degenerate cases -/

/-- Degree `0` forces variance `0`: the `d = 0` instance of `MainTheorem` is vacuous. -/
theorem variance_eq_zero_of_degree_zero {f : Cube ι → ℝ} (h : HasDegreeLE f 0) :
    variance f = 0 :=
  Level.variance_eq_zero_of_const f (hasDegreeLE_zero_const h)

/-- The hypotheses of `MainTheorem` force `d ≥ 1` and a nonempty index type. In particular the
division by a power of `d` in the printed forms of the bounds is never a division by zero under
the hypotheses. -/
theorem aa_hyps_force {f : Cube ι → ℝ} {d : ℕ} (hdeg : HasDegreeLE f d) (hv : 0 < variance f) :
    1 ≤ d ∧ Nonempty ι := by
  constructor
  · rcases Nat.eq_zero_or_pos d with rfl | hd
    · rw [variance_eq_zero_of_degree_zero hdeg] at hv
      exact absurd hv (lt_irrefl 0)
    · exact hd
  · by_contra hne
    have : IsEmpty ι := not_nonempty_iff.mp hne
    rw [Level.variance_eq_zero_of_isEmpty f] at hv
    exact lt_irrefl 0 hv

/-! ### Size of the variance -/

/-- A `[0,1]`-valued function has variance at most `1/4`. -/
theorem variance_le_quarter {P : Cube ι → ℝ} (h : ∀ x, 0 ≤ P x ∧ P x ≤ 1) :
    variance P ≤ 1 / 4 := by
  have hpos : (0 : ℝ) < 2 ^ Fintype.card ι := by positivity
  refine (Level.variance_le_sq_dist P (1 / 2)).trans ?_
  rw [div_le_iff₀ hpos]
  have h1 : ∑ x : Cube ι, (P x - 1 / 2) ^ 2 ≤ ∑ _x : Cube ι, (1 / 4 : ℝ) :=
    Finset.sum_le_sum (fun x _ => by
      obtain ⟨h0, h1⟩ := h x
      nlinarith [mul_nonneg h0 (sub_nonneg.mpr h1)])
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_cube] at h1
  linarith

/-- A `[-1,1]`-valued function has variance at most `1`. -/
theorem variance_le_one {f : Cube ι → ℝ} (h : ∀ x, |f x| ≤ 1) : variance f ≤ 1 := by
  have hpos : (0 : ℝ) < 2 ^ Fintype.card ι := by positivity
  refine (Level.variance_le_sq_dist f 0).trans ?_
  rw [div_le_iff₀ hpos]
  have h1 : ∑ x : Cube ι, (f x - 0) ^ 2 ≤ ∑ _x : Cube ι, (1 : ℝ) :=
    Finset.sum_le_sum (fun x _ => by
      have h2 := abs_le.mp (h x)
      have h3 : 0 ≤ 1 - f x := by linarith [h2.2]
      have h4 : 0 ≤ 1 + f x := by linarith [h2.1]
      nlinarith [mul_nonneg h3 h4])
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_cube] at h1
  linarith

end AaronsonAmbainis.Bridge

end
/- END UPSTREAM MODULE: AaronsonAmbainis.Bridge.Affine -/

/- BEGIN UPSTREAM MODULE: AaronsonAmbainis.Bridge.PrintedAA -/
section
/-!
# The main theorem and the conjecture as printed

Source.

S. Aaronson and A. Ambainis, *The need for structure in quantum speedups*, arXiv:0911.0996,
Conjecture 6 (Conjecture 1.7 of the journal version, Theory of Computing 10 (2014), 133–166):

  Let `p : R^N → R` be a polynomial of degree `d`. Suppose that `0 ≤ p(X) ≤ 1` for all
  `X ∈ {0,1}^N`, and `E_X[(p(X) − E[p])²] ≥ ε`. Then there exists an `i` such that
  `Inf_i[p] ≥ (ε/d)^{O(1)}`,   where   `Inf_i[p] := E_X[(p(X) − p(X^i))²]`.

The conjecture, and its form on the cube `{1,-1}^n` (`problem_statement.md`), are transcribed
without the definitions of `Defs.lean`: `Ex`, `flipBit`, `ev01`, `evPM` spell out the expectation,
the bit flip and the evaluation of a polynomial on the two cubes. `evPM` sends `true` to `-1`, as
`Defs.lean` does; the statement `ExplicitBoundPM` of `Conjecture.lean` sends `true` to `1`
(`evPMt`, in the last section).

`MainBound C` is a bound of the kind of the main theorem with a constant `C`:
`3 Var(f)^5 ≤ C d^12 Inf_j(f)²`. So `MainTheorem` is `MainBound (50000 π^8)` and
`MainTheoremImproved` is `MainBound (3125 π^8)`. Every such bound is carried over to
polynomials:

* `pm_of_mainBound` — on the cube `{1,-1}^n`, for `|p| ≤ 1`: `3 ε^5 ≤ C d^12 Inf_i(p)²`;
* `zo_of_mainBound` — on the cube `{0,1}^N`, for `0 ≤ p ≤ 1` (the bound is applied to
  `1 − 2p`, whose variance is `4 Var[p]`): `3072 ε^5 ≤ C d^12 Inf_i[p]²`.

The bounds are then put in the form in which the paper prints them, with the power `5/2`
written as `ε² √ε` (`sqrt_form_iff`). From `MainTheorem`:

* `pm_sq_of_mainTheorem`, `pm_sqrt_of_mainTheorem` — `3 ε^5 ≤ 50000 π^8 d^12 Inf_i(p)²`, that is,
  `Inf_i(p) ≥ (√15 / (500 π^4)) ε^{5/2} / d^6`;
* `zo_sq_of_mainTheorem`, `zo_sqrt_of_mainTheorem` — `192 ε^5 ≤ 3125 π^8 d^12 Inf_i[p]²`, that
  is, `Inf_i[p] ≥ (8 √15 / (125 π^4)) ε^{5/2} / d^6`;
* `zo_pow_of_mainTheorem` — `Inf_i[p] ≥ (ε/d)^7`, the conjecture as printed (`ratio_pow_le`).

From `MainTheoremImproved`:

* `zo_sq_of_mainTheoremImproved`, `zo_sqrt_of_mainTheoremImproved` —
  `3072 ε^5 ≤ 3125 π^8 d^12 Inf_i[p]²`, that is, `Inf_i[p] ≥ (32 √15 / (125 π^4)) ε^{5/2} / d^6`.

In these theorems `MainTheorem` and `MainTheoremImproved` are hypotheses; `Chain.lean` proves the
first with no hypothesis and the second from the hypothesis `RowBound`.

The last section treats the real power `ε^{5/2}` and the bit encoding of `ExplicitBoundPM`, as
`Conjecture.lean` writes the power and the encoding: `ε ^ ((5 : ℝ) / 2)` equals `ε² √ε`
(`rpow_five_halves`), and `pmt_sq_of_mainTheorem`, `pmt_sqrt_of_mainTheorem` are the bounds on
the cube `{-1,1}^n` with `true ↦ 1` and `false ↦ -1` (`evPMt`), obtained from
`pm_sq_of_mainTheorem` and `pm_sqrt_of_mainTheorem` by negating every bit.
-/

namespace AaronsonAmbainis.Bridge

open Finset MvPolynomial

/-- Uniform expectation over `{0,1}^N`, spelled out. -/
noncomputable def Ex {N : ℕ} (F : (Fin N → Bool) → ℝ) : ℝ := (∑ X, F X) / 2 ^ N

/-- `X` with the `i`-th bit flipped, spelled out (`X^i` in the sources). -/
def flipBit {N : ℕ} (X : Fin N → Bool) (i : Fin N) : Fin N → Bool := Function.update X i (!X i)

/-- The value of the polynomial `p` at the `0/1` point `X ∈ {0,1}^N`. -/
noncomputable def ev01 {N : ℕ} (p : MvPolynomial (Fin N) ℝ) (X : Fin N → Bool) : ℝ :=
  MvPolynomial.eval (fun i => if X i then (1 : ℝ) else 0) p

/-- The value of the polynomial `p` at the `±1` point attached to `X` (`true ↦ −1`). -/
noncomputable def evPM {N : ℕ} (p : MvPolynomial (Fin N) ℝ) (X : Fin N → Bool) : ℝ :=
  MvPolynomial.eval (fun i => if X i then (-1 : ℝ) else 1) p

/-! ### `mean`, `variance`, `inflR`, `flipSet` of `Defs.lean` are the spelled-out notions -/

theorem mean_eq_Ex {N : ℕ} (F : Cube (Fin N) → ℝ) : mean F = Ex F := by
  unfold mean Ex
  rw [Fintype.card_fin]

theorem flipSet_singleton_eq_flipBit {N : ℕ} (X : Cube (Fin N)) (i : Fin N) :
    flipSet X {i} = flipBit X i := by
  funext k
  by_cases hk : k = i
  · subst hk
    rw [flipSet_singleton_self]
    simp [flipBit]
  · rw [flipSet_singleton_ne X hk]
    simp [flipBit, Function.update_of_ne hk]

theorem variance_eq_Ex {N : ℕ} (F : Cube (Fin N) → ℝ) :
    variance F = Ex (fun X => (F X - Ex F) ^ 2) := by
  have h : variance F = (∑ x, (F x - mean F) ^ 2) / 2 ^ Fintype.card (Fin N) := rfl
  rw [h, mean_eq_Ex, Fintype.card_fin]
  rfl

theorem inflR_eq_Ex {N : ℕ} (F : Cube (Fin N) → ℝ) (i : Fin N) :
    inflR F i = Ex (fun X => ((F X - F (flipBit X i)) / 2) ^ 2) := by
  have h : inflR F i
      = (∑ x, ((F x - F (flipSet x {i})) / 2) ^ 2) / 2 ^ Fintype.card (Fin N) := rfl
  rw [h, Fintype.card_fin]
  simp only [flipSet_singleton_eq_flipBit]
  rfl

theorem Ex_nonneg {N : ℕ} {F : (Fin N → Bool) → ℝ} (hF : ∀ X, 0 ≤ F X) : 0 ≤ Ex F :=
  div_nonneg (Finset.sum_nonneg fun X _ => hF X) (by positivity)

/-! ### Bounds of the kind of the main theorem, for polynomials -/

/-- A bound of the kind of the main theorem, with the constant `C`: every `f` on the cube with
`|f| ≤ 1`, degree at most `d` and positive variance has a coordinate `j` with
`3 Var(f)^5 ≤ C d^12 Inf_j(f)²`. `MainTheorem` is `MainBound (50000 * π^8)`, and
`MainTheoremImproved` is `MainBound (3125 * π^8)`. -/
def MainBound (C : ℝ) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (d : ℕ) (f : Cube ι → ℝ), (∀ x, |f x| ≤ 1) →
    HasDegreeLE f d → 0 < variance f →
    ∃ j, 3 * variance f ^ 5 ≤ C * (d : ℝ) ^ 12 * inflR f j ^ 2

theorem mainBound_of_mainTheorem (h : MainTheorem) : MainBound (50000 * Real.pi ^ 8) := h

theorem mainBound_of_mainTheoremImproved (h : MainTheoremImproved) :
    MainBound (3125 * Real.pi ^ 8) := h

/-- A bound of the kind of the main theorem, translated to `[0,1]`-valued functions `P` (apply it
to `1 − 2P`), with the unnormalised L2 influence `E[(P(X) − P(X^i))²]` of Aaronson–Ambainis on
the right: `3072 Var[P]^5 ≤ C d^12 Inf_i[P]²`. -/
theorem zero_one_of_mainBound {C : ℝ} (h : MainBound C) {ι : Type} [Fintype ι]
    [DecidableEq ι] (d : ℕ) (P : Cube ι → ℝ) (hrange : ∀ X, 0 ≤ P X ∧ P X ≤ 1)
    (hdeg : HasDegreeLE P d) (hpos : 0 < variance P) :
    ∃ i, 3072 * variance P ^ 5 ≤ C * (d : ℝ) ^ 12
      * ((∑ X : Cube ι, (P X - P (flipSet X {i})) ^ 2) / 2 ^ Fintype.card ι) ^ 2 := by
  have hdeg' : HasDegreeLE (fun X => 1 + (-2) * P X) d :=
    hasDegreeLE_add (hasDegreeLE_const 1 d) (hasDegreeLE_smul (-2) hdeg)
  have hbd : ∀ X, |1 + (-2) * P X| ≤ 1 := by
    intro X
    obtain ⟨h0, h1⟩ := hrange X
    rw [abs_le]
    constructor <;> linarith
  have hV : variance (fun X => 1 + (-2) * P X) = 4 * variance P := by
    rw [variance_affine]
    norm_num
  have hVpos : 0 < variance (fun X => 1 + (-2) * P X) := by
    rw [hV]
    linarith
  obtain ⟨i, hi⟩ := h ι d (fun X => 1 + (-2) * P X) hbd hdeg' hVpos
  refine ⟨i, ?_⟩
  have hI : inflR (fun X => 1 + (-2) * P X) i
      = (∑ X : Cube ι, (P X - P (flipSet X {i})) ^ 2) / 2 ^ Fintype.card ι := by
    rw [inflR_affine, Level.inflR_eq_quarter]
    ring
  rw [hV, hI] at hi
  have e : 3 * (4 * variance P) ^ 5 = 3072 * variance P ^ 5 := by ring
  rw [e] at hi
  exact hi

/-- A bound of the kind of the main theorem for polynomials on the cube `{0,1}^N` with values in
`[0,1]`: `3072 ε^5 ≤ C d^12 Inf_i[p]²`. -/
theorem zo_of_mainBound {C : ℝ} (h : MainBound C) (N d : ℕ) (p : MvPolynomial (Fin N) ℝ)
    (hp : p.totalDegree ≤ d) (hrange : ∀ X, 0 ≤ ev01 p X ∧ ev01 p X ≤ 1) (ε : ℝ) (hε : 0 < ε)
    (hvar : Ex (fun X => (ev01 p X - Ex (ev01 p)) ^ 2) ≥ ε) :
    ∃ i, 3072 * ε ^ 5 ≤ C * (d : ℝ) ^ 12
      * Ex (fun X => (ev01 p X - ev01 p (flipBit X i)) ^ 2) ^ 2 := by
  have hdeg : HasDegreeLE (ev01 p) d := hasDegreeLE_eval_zo p hp
  have hvar' : ε ≤ variance (ev01 p) := by
    rw [variance_eq_Ex]
    exact hvar
  obtain ⟨i, hi⟩ := zero_one_of_mainBound h d (ev01 p) hrange hdeg (lt_of_lt_of_le hε hvar')
  refine ⟨i, ?_⟩
  have hI : (∑ X : Cube (Fin N), (ev01 p X - ev01 p (flipSet X {i})) ^ 2)
        / 2 ^ Fintype.card (Fin N)
      = Ex (fun X => (ev01 p X - ev01 p (flipBit X i)) ^ 2) := by
    rw [Fintype.card_fin]
    simp only [flipSet_singleton_eq_flipBit]
    rfl
  rw [hI] at hi
  have h5 : ε ^ 5 ≤ variance (ev01 p) ^ 5 := pow_le_pow_left₀ hε.le hvar' 5
  linarith

/-- A bound of the kind of the main theorem for polynomials on the cube `{1,-1}^n` which are
bounded by `1`: `3 ε^5 ≤ C d^12 Inf_i(p)²`. -/
theorem pm_of_mainBound {C : ℝ} (h : MainBound C) (n d : ℕ) (p : MvPolynomial (Fin n) ℝ)
    (hp : p.totalDegree ≤ d) (hbd : ∀ X, |evPM p X| ≤ 1) (ε : ℝ) (hε : 0 < ε)
    (hvar : Ex (fun X => (evPM p X - Ex (evPM p)) ^ 2) ≥ ε) :
    ∃ i, 3 * ε ^ 5 ≤ C * (d : ℝ) ^ 12
      * Ex (fun X => ((evPM p X - evPM p (flipBit X i)) / 2) ^ 2) ^ 2 := by
  have hdeg : HasDegreeLE (evPM p) d := hasDegreeLE_eval_pm p hp
  have hvar' : ε ≤ variance (evPM p) := by
    rw [variance_eq_Ex]
    exact hvar
  have hpos : 0 < variance (evPM p) := lt_of_lt_of_le hε hvar'
  obtain ⟨i, hi⟩ := h (Fin n) d (evPM p) hbd hdeg hpos
  refine ⟨i, ?_⟩
  rw [← inflR_eq_Ex (evPM p) i]
  have h5 : ε ^ 5 ≤ variance (evPM p) ^ 5 := pow_le_pow_left₀ hε.le hvar' 5
  linarith

/-- Under the hypotheses of the statements on the cube `{0,1}^N`: `d ≥ 1` and `ε ≤ 1/4`. -/
theorem zo_hyps_force (N d : ℕ) (p : MvPolynomial (Fin N) ℝ) (hp : p.totalDegree ≤ d)
    (hrange : ∀ X, 0 ≤ ev01 p X ∧ ev01 p X ≤ 1) (ε : ℝ) (hε : 0 < ε)
    (hvar : Ex (fun X => (ev01 p X - Ex (ev01 p)) ^ 2) ≥ ε) :
    (1 : ℝ) ≤ (d : ℝ) ∧ ε ≤ 1 / 4 := by
  have hdeg : HasDegreeLE (ev01 p) d := hasDegreeLE_eval_zo p hp
  have hvar' : ε ≤ variance (ev01 p) := by
    rw [variance_eq_Ex]
    exact hvar
  have hd : 1 ≤ d := (aa_hyps_force hdeg (lt_of_lt_of_le hε hvar')).1
  exact ⟨by exact_mod_cast hd, hvar'.trans (variance_le_quarter hrange)⟩

/-- Under the hypotheses of the statement on the cube `{1,-1}^n`, in the encoding of `evPM`:
`d ≥ 1`. -/
theorem pm_hyps_force (n d : ℕ) (p : MvPolynomial (Fin n) ℝ) (hp : p.totalDegree ≤ d)
    (ε : ℝ) (hε : 0 < ε) (hvar : Ex (fun X => (evPM p X - Ex (evPM p)) ^ 2) ≥ ε) :
    (1 : ℝ) ≤ (d : ℝ) := by
  have hdeg : HasDegreeLE (evPM p) d := hasDegreeLE_eval_pm p hp
  have hvar' : ε ≤ variance (evPM p) := by
    rw [variance_eq_Ex]
    exact hvar
  have hd : 1 ≤ d := (aa_hyps_force hdeg (lt_of_lt_of_le hε hvar')).1
  exact_mod_cast hd

/-! ### The arithmetic of the printed forms -/

/-- A bound without square roots and its printed form: if `ε, I, c₁ ≥ 0`, `D, c₂, m > 0` and
`15 c₁² m = k c₂²`, then `I ≥ (c₁ √15 / (c₂ π^4)) ε^{5/2} / D^6` if and only if
`k ε^5 ≤ m π^8 D^12 I²`. The power `ε^{5/2}` is written `ε² √ε`. -/
theorem sqrt_form_iff {c₁ c₂ k m ε D I : ℝ} (hc₁ : 0 ≤ c₁) (hc₂ : 0 < c₂) (hm : 0 < m)
    (hkm : 15 * c₁ ^ 2 * m = k * c₂ ^ 2) (hε : 0 ≤ ε) (hD : 0 < D) (hI : 0 ≤ I) :
    c₁ * Real.sqrt 15 / (c₂ * Real.pi ^ 4) * (ε ^ 2 * Real.sqrt ε) / D ^ 6 ≤ I
      ↔ k * ε ^ 5 ≤ m * Real.pi ^ 8 * D ^ 12 * I ^ 2 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hden : 0 < c₂ * Real.pi ^ 4 * D ^ 6 := by positivity
  have hL : 0 ≤ c₁ * Real.sqrt 15 * (ε ^ 2 * Real.sqrt ε) := by positivity
  have e : c₁ * Real.sqrt 15 / (c₂ * Real.pi ^ 4) * (ε ^ 2 * Real.sqrt ε) / D ^ 6
      = c₁ * Real.sqrt 15 * (ε ^ 2 * Real.sqrt ε) / (c₂ * Real.pi ^ 4 * D ^ 6) := by
    field_simp
  have e1 : (c₁ * Real.sqrt 15 * (ε ^ 2 * Real.sqrt ε)) ^ 2 = 15 * c₁ ^ 2 * ε ^ 5 := by
    rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 15), Real.sq_sqrt hε]
    ring
  have e2 : (I * (c₂ * Real.pi ^ 4 * D ^ 6)) ^ 2
      = c₂ ^ 2 * (Real.pi ^ 8 * D ^ 12 * I ^ 2) := by ring
  have e3 : m * (15 * c₁ ^ 2 * ε ^ 5) = c₂ ^ 2 * (k * ε ^ 5) := by
    linear_combination ε ^ 5 * hkm
  have e4 : m * (c₂ ^ 2 * (Real.pi ^ 8 * D ^ 12 * I ^ 2))
      = c₂ ^ 2 * (m * Real.pi ^ 8 * D ^ 12 * I ^ 2) := by ring
  rw [e, div_le_iff₀ hden]
  constructor
  · intro h
    have h2 := pow_le_pow_left₀ hL h 2
    rw [e1, e2] at h2
    have h3 := mul_le_mul_of_nonneg_left h2 hm.le
    rw [e3, e4] at h3
    exact le_of_mul_le_mul_left h3 (pow_pos hc₂ 2)
  · intro h
    apply le_of_pow_le_pow_left₀ two_ne_zero (mul_nonneg hI hden.le)
    rw [e1, e2]
    have h3 := mul_le_mul_of_nonneg_left h (sq_nonneg c₂)
    rw [← e3, ← e4] at h3
    exact le_of_mul_le_mul_left h3 hm

/-- If `192 ε^5 ≤ 3125 π^8 D^12 I²` with `0 < ε ≤ 1/4`, `D ≥ 1` and `I ≥ 0`, then
`(ε/D)^7 ≤ I`: indeed `3125 π^8 ε^9 ≤ 192` for `ε ≤ 1/4`, and `D^12 ≤ D^14`. -/
theorem ratio_pow_le {ε D I : ℝ} (hε : 0 < ε) (hε4 : ε ≤ 1 / 4) (hD : 1 ≤ D) (hI : 0 ≤ I)
    (h : 192 * ε ^ 5 ≤ 3125 * Real.pi ^ 8 * D ^ 12 * I ^ 2) : (ε / D) ^ 7 ≤ I := by
  have hD0 : 0 < D := lt_of_lt_of_le one_pos hD
  apply le_of_pow_le_pow_left₀ two_ne_zero hI
  have h1 : ε ^ 9 ≤ (1 / 4) ^ 9 := pow_le_pow_left₀ hε.le hε4 9
  have hpi : Real.pi ^ 8 ≤ (3.15 : ℝ) ^ 8 :=
    pow_le_pow_left₀ Real.pi_pos.le Real.pi_lt_d2.le 8
  have hB : 3125 * Real.pi ^ 8 * ε ^ 9 ≤ 192 := by
    have h4 : 3125 * Real.pi ^ 8 * ε ^ 9 ≤ 3125 * (3.15 : ℝ) ^ 8 * (1 / 4) ^ 9 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hpi (by norm_num)) h1 (by positivity)
        (by positivity)
    have h5 : 3125 * (3.15 : ℝ) ^ 8 * (1 / 4) ^ 9 ≤ 192 := by norm_num
    linarith
  have hD12 : D ^ 12 ≤ D ^ 14 := pow_le_pow_right₀ hD (by norm_num)
  have hc : 0 < 3125 * Real.pi ^ 8 := by positivity
  have h6 : (3125 * Real.pi ^ 8) * ε ^ 14 ≤ (3125 * Real.pi ^ 8) * (D ^ 14 * I ^ 2) := by
    calc (3125 * Real.pi ^ 8) * ε ^ 14 = (3125 * Real.pi ^ 8 * ε ^ 9) * ε ^ 5 := by ring
      _ ≤ 192 * ε ^ 5 := mul_le_mul_of_nonneg_right hB (by positivity)
      _ ≤ 3125 * Real.pi ^ 8 * D ^ 12 * I ^ 2 := h
      _ ≤ 3125 * Real.pi ^ 8 * D ^ 14 * I ^ 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hD12 hc.le) (sq_nonneg I)
      _ = (3125 * Real.pi ^ 8) * (D ^ 14 * I ^ 2) := by ring
  have h7 : ε ^ 14 ≤ D ^ 14 * I ^ 2 := le_of_mul_le_mul_left h6 hc
  have e : ((ε / D) ^ 7) ^ 2 = ε ^ 14 / D ^ 14 := by
    rw [← pow_mul, div_pow]
  rw [e, div_le_iff₀ (pow_pos hD0 14)]
  linarith

/-! ### The form on the cube `{1,-1}^n`, from `MainTheorem` -/

/-- `3 ε^5 ≤ 50000 π^8 d^12 Inf_i(p)²`, from `MainTheorem`. -/
theorem pm_sq_of_mainTheorem (h : MainTheorem) (n d : ℕ) (p : MvPolynomial (Fin n) ℝ)
    (hp : p.totalDegree ≤ d) (hbd : ∀ X, |evPM p X| ≤ 1) (ε : ℝ) (hε : 0 < ε)
    (hvar : Ex (fun X => (evPM p X - Ex (evPM p)) ^ 2) ≥ ε) :
    ∃ i, 3 * ε ^ 5 ≤ 50000 * Real.pi ^ 8 * (d : ℝ) ^ 12
      * Ex (fun X => ((evPM p X - evPM p (flipBit X i)) / 2) ^ 2) ^ 2 :=
  pm_of_mainBound (mainBound_of_mainTheorem h) n d p hp hbd ε hε hvar

/-- `Inf_i(p) ≥ (√15 / (500 π^4)) ε^{5/2} / d^6`, from `MainTheorem`. -/
theorem pm_sqrt_of_mainTheorem (h : MainTheorem) (n d : ℕ) (p : MvPolynomial (Fin n) ℝ)
    (hp : p.totalDegree ≤ d) (hbd : ∀ X, |evPM p X| ≤ 1) (ε : ℝ) (hε : 0 < ε)
    (hvar : Ex (fun X => (evPM p X - Ex (evPM p)) ^ 2) ≥ ε) :
    ∃ i, Ex (fun X => ((evPM p X - evPM p (flipBit X i)) / 2) ^ 2)
      ≥ Real.sqrt 15 / (500 * Real.pi ^ 4) * (ε ^ 2 * Real.sqrt ε) / (d : ℝ) ^ 6 := by
  obtain ⟨i, hi⟩ := pm_sq_of_mainTheorem h n d p hp hbd ε hε hvar
  have hD : (0 : ℝ) < (d : ℝ) := lt_of_lt_of_le one_pos (pm_hyps_force n d p hp ε hε hvar)
  have h1 := (sqrt_form_iff (c₁ := 1) (c₂ := 500) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hε.le hD (Ex_nonneg fun X => sq_nonneg _)).mpr hi
  rw [one_mul] at h1
  exact ⟨i, h1⟩

/-! ### The conjecture, from `MainTheorem` -/

/-- `192 ε^5 ≤ 3125 π^8 d^12 Inf_i[p]²`, from `MainTheorem`. -/
theorem zo_sq_of_mainTheorem (h : MainTheorem) (N d : ℕ) (p : MvPolynomial (Fin N) ℝ)
    (hp : p.totalDegree ≤ d) (hrange : ∀ X, 0 ≤ ev01 p X ∧ ev01 p X ≤ 1) (ε : ℝ) (hε : 0 < ε)
    (hvar : Ex (fun X => (ev01 p X - Ex (ev01 p)) ^ 2) ≥ ε) :
    ∃ i, 192 * ε ^ 5 ≤ 3125 * Real.pi ^ 8 * (d : ℝ) ^ 12
      * Ex (fun X => (ev01 p X - ev01 p (flipBit X i)) ^ 2) ^ 2 := by
  obtain ⟨i, hi⟩ := zo_of_mainBound (mainBound_of_mainTheorem h) N d p hp hrange ε hε hvar
  exact ⟨i, by linarith⟩

/-- `Inf_i[p] ≥ (8 √15 / (125 π^4)) ε^{5/2} / d^6`, from `MainTheorem`. -/
theorem zo_sqrt_of_mainTheorem (h : MainTheorem) (N d : ℕ) (p : MvPolynomial (Fin N) ℝ)
    (hp : p.totalDegree ≤ d) (hrange : ∀ X, 0 ≤ ev01 p X ∧ ev01 p X ≤ 1) (ε : ℝ) (hε : 0 < ε)
    (hvar : Ex (fun X => (ev01 p X - Ex (ev01 p)) ^ 2) ≥ ε) :
    ∃ i, Ex (fun X => (ev01 p X - ev01 p (flipBit X i)) ^ 2)
      ≥ 8 * Real.sqrt 15 / (125 * Real.pi ^ 4) * (ε ^ 2 * Real.sqrt ε) / (d : ℝ) ^ 6 := by
  obtain ⟨i, hi⟩ := zo_sq_of_mainTheorem h N d p hp hrange ε hε hvar
  have hD : (0 : ℝ) < (d : ℝ) :=
    lt_of_lt_of_le one_pos (zo_hyps_force N d p hp hrange ε hε hvar).1
  exact ⟨i, (sqrt_form_iff (by norm_num) (by norm_num) (by norm_num) (by norm_num) hε.le hD
    (Ex_nonneg fun X => sq_nonneg _)).mpr hi⟩

/-- `Inf_i[p] ≥ (ε/d)^7`, from `MainTheorem`. -/
theorem zo_pow_of_mainTheorem (h : MainTheorem) (N d : ℕ) (p : MvPolynomial (Fin N) ℝ)
    (hp : p.totalDegree ≤ d) (hrange : ∀ X, 0 ≤ ev01 p X ∧ ev01 p X ≤ 1) (ε : ℝ) (hε : 0 < ε)
    (hvar : Ex (fun X => (ev01 p X - Ex (ev01 p)) ^ 2) ≥ ε) :
    ∃ i, Ex (fun X => (ev01 p X - ev01 p (flipBit X i)) ^ 2) ≥ (ε / (d : ℝ)) ^ 7 := by
  obtain ⟨i, hi⟩ := zo_sq_of_mainTheorem h N d p hp hrange ε hε hvar
  obtain ⟨hD, hε4⟩ := zo_hyps_force N d p hp hrange ε hε hvar
  exact ⟨i, ratio_pow_le hε hε4 hD (Ex_nonneg fun X => sq_nonneg _) hi⟩

/-! ### The conjecture with the constant of `MainTheoremImproved` -/

/-- `3072 ε^5 ≤ 3125 π^8 d^12 Inf_i[p]²`, from `MainTheoremImproved`. -/
theorem zo_sq_of_mainTheoremImproved (h : MainTheoremImproved) (N d : ℕ)
    (p : MvPolynomial (Fin N) ℝ) (hp : p.totalDegree ≤ d)
    (hrange : ∀ X, 0 ≤ ev01 p X ∧ ev01 p X ≤ 1) (ε : ℝ) (hε : 0 < ε)
    (hvar : Ex (fun X => (ev01 p X - Ex (ev01 p)) ^ 2) ≥ ε) :
    ∃ i, 3072 * ε ^ 5 ≤ 3125 * Real.pi ^ 8 * (d : ℝ) ^ 12
      * Ex (fun X => (ev01 p X - ev01 p (flipBit X i)) ^ 2) ^ 2 :=
  zo_of_mainBound (mainBound_of_mainTheoremImproved h) N d p hp hrange ε hε hvar

/-- `Inf_i[p] ≥ (32 √15 / (125 π^4)) ε^{5/2} / d^6`, from `MainTheoremImproved`. -/
theorem zo_sqrt_of_mainTheoremImproved (h : MainTheoremImproved) (N d : ℕ)
    (p : MvPolynomial (Fin N) ℝ) (hp : p.totalDegree ≤ d)
    (hrange : ∀ X, 0 ≤ ev01 p X ∧ ev01 p X ≤ 1) (ε : ℝ) (hε : 0 < ε)
    (hvar : Ex (fun X => (ev01 p X - Ex (ev01 p)) ^ 2) ≥ ε) :
    ∃ i, Ex (fun X => (ev01 p X - ev01 p (flipBit X i)) ^ 2)
      ≥ 32 * Real.sqrt 15 / (125 * Real.pi ^ 4) * (ε ^ 2 * Real.sqrt ε) / (d : ℝ) ^ 6 := by
  obtain ⟨i, hi⟩ := zo_sq_of_mainTheoremImproved h N d p hp hrange ε hε hvar
  have hD : (0 : ℝ) < (d : ℝ) :=
    lt_of_lt_of_le one_pos (zo_hyps_force N d p hp hrange ε hε hvar).1
  exact ⟨i, (sqrt_form_iff (by norm_num) (by norm_num) (by norm_num) (by norm_num) hε.le hD
    (Ex_nonneg fun X => sq_nonneg _)).mpr hi⟩

/-! ### The power `5/2` and the encoding of `ExplicitBoundPM`

`Conjecture.lean` writes the power `ε^{5/2}` as the real power `ε ^ ((5 : ℝ) / 2)`, and
`ε ^ ((5 : ℝ) / 2) = ε² √ε` for `ε ≥ 0` (`rpow_five_halves`). The statement `ExplicitBoundPM` of
`Conjecture.lean`, on the cube `{-1,1}^n`, encodes the bit `true` as `1` and the bit `false` as
`-1` (`evPMt`), while `evPM`, like `Defs.lean`, sends `true` to `-1`. Negating every bit
(`negBits`) is a bijection of the cube: `evPMt p X = evPM p (negBits X)`, and `negBits` commutes
with the bit flips, so `evPMt p` and `evPM p` have the same expectation, the same variance and the
same influences. -/

/-- The real power `ε^{5/2}` is `ε² √ε`. -/
theorem rpow_five_halves {ε : ℝ} (hε : 0 ≤ ε) : ε ^ ((5 : ℝ) / 2) = ε ^ 2 * Real.sqrt ε := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_add' hε (by norm_num)]
  norm_num

/-- The value of the polynomial `p` at the `±1` point attached to `X` with `true ↦ 1` and
`false ↦ -1`, the encoding of `ExplicitBoundPM`. -/
noncomputable def evPMt {N : ℕ} (p : MvPolynomial (Fin N) ℝ) (X : Fin N → Bool) : ℝ :=
  MvPolynomial.eval (fun i => if X i then (1 : ℝ) else -1) p

/-- Every bit of `X` negated. -/
def negBits {N : ℕ} (X : Fin N → Bool) : Fin N → Bool := fun i => !X i

theorem negBits_negBits {N : ℕ} (X : Fin N → Bool) : negBits (negBits X) = X := by
  funext i
  simp [negBits]

/-- Negating every bit, as a bijection of the cube. -/
def negBitsEquiv (N : ℕ) : (Fin N → Bool) ≃ (Fin N → Bool) :=
  ⟨negBits, negBits, negBits_negBits, negBits_negBits⟩

theorem Ex_comp_negBits {N : ℕ} (F : (Fin N → Bool) → ℝ) :
    Ex (fun X => F (negBits X)) = Ex F := by
  unfold Ex
  congr 1
  exact Equiv.sum_comp (negBitsEquiv N) F

theorem negBits_flipBit {N : ℕ} (X : Fin N → Bool) (i : Fin N) :
    negBits (flipBit X i) = flipBit (negBits X) i := by
  funext k
  by_cases hk : k = i
  · subst hk
    simp [negBits, flipBit]
  · simp [negBits, flipBit, Function.update_of_ne hk]

theorem evPMt_eq {N : ℕ} (p : MvPolynomial (Fin N) ℝ) (X : Fin N → Bool) :
    evPMt p X = evPM p (negBits X) := by
  have hpt : (fun i => if X i then (1 : ℝ) else -1)
      = fun i => if negBits X i then (-1 : ℝ) else 1 := by
    funext i
    rcases Bool.eq_false_or_eq_true (X i) with h | h <;> simp [negBits, h]
  unfold evPMt evPM
  rw [hpt]

theorem evPMt_bound_iff {N : ℕ} (p : MvPolynomial (Fin N) ℝ) :
    (∀ X, |evPMt p X| ≤ 1) ↔ ∀ X, |evPM p X| ≤ 1 := by
  constructor
  · intro h X
    have hX := h (negBits X)
    rwa [evPMt_eq, negBits_negBits] at hX
  · intro h X
    rw [evPMt_eq]
    exact h (negBits X)

theorem Ex_evPMt {N : ℕ} (p : MvPolynomial (Fin N) ℝ) : Ex (evPMt p) = Ex (evPM p) := by
  have e : evPMt p = fun X => evPM p (negBits X) := funext (evPMt_eq p)
  rw [e]
  exact Ex_comp_negBits (evPM p)

theorem variance_evPMt {N : ℕ} (p : MvPolynomial (Fin N) ℝ) :
    Ex (fun X => (evPMt p X - Ex (evPMt p)) ^ 2) = Ex (fun X => (evPM p X - Ex (evPM p)) ^ 2) := by
  rw [Ex_evPMt]
  simp only [evPMt_eq]
  exact Ex_comp_negBits (fun X => (evPM p X - Ex (evPM p)) ^ 2)

theorem infl_evPMt {N : ℕ} (p : MvPolynomial (Fin N) ℝ) (i : Fin N) :
    Ex (fun X => ((evPMt p X - evPMt p (flipBit X i)) / 2) ^ 2)
      = Ex (fun X => ((evPM p X - evPM p (flipBit X i)) / 2) ^ 2) := by
  simp only [evPMt_eq, negBits_flipBit]
  exact Ex_comp_negBits (fun X => ((evPM p X - evPM p (flipBit X i)) / 2) ^ 2)

/-- `3 ε^5 ≤ 50000 π^8 d^12 Inf_i(p)²` on `{-1,1}^n` with `true ↦ 1`, from `MainTheorem`. -/
theorem pmt_sq_of_mainTheorem (h : MainTheorem) (n d : ℕ) (p : MvPolynomial (Fin n) ℝ)
    (hp : p.totalDegree ≤ d) (hbd : ∀ X, |evPMt p X| ≤ 1) (ε : ℝ) (hε : 0 < ε)
    (hvar : Ex (fun X => (evPMt p X - Ex (evPMt p)) ^ 2) ≥ ε) :
    ∃ i, 3 * ε ^ 5 ≤ 50000 * Real.pi ^ 8 * (d : ℝ) ^ 12
      * Ex (fun X => ((evPMt p X - evPMt p (flipBit X i)) / 2) ^ 2) ^ 2 := by
  rw [variance_evPMt] at hvar
  obtain ⟨i, hi⟩ :=
    pm_sq_of_mainTheorem h n d p hp ((evPMt_bound_iff p).mp hbd) ε hε hvar
  exact ⟨i, by rwa [infl_evPMt]⟩

/-- `Inf_i(p) ≥ (√15 / (500 π^4)) ε^{5/2} / d^6` on `{-1,1}^n` with `true ↦ 1`, from
`MainTheorem`, with the power `5/2` written `ε² √ε`. -/
theorem pmt_sqrt_of_mainTheorem (h : MainTheorem) (n d : ℕ) (p : MvPolynomial (Fin n) ℝ)
    (hp : p.totalDegree ≤ d) (hbd : ∀ X, |evPMt p X| ≤ 1) (ε : ℝ) (hε : 0 < ε)
    (hvar : Ex (fun X => (evPMt p X - Ex (evPMt p)) ^ 2) ≥ ε) :
    ∃ i, Ex (fun X => ((evPMt p X - evPMt p (flipBit X i)) / 2) ^ 2)
      ≥ Real.sqrt 15 / (500 * Real.pi ^ 4) * (ε ^ 2 * Real.sqrt ε) / (d : ℝ) ^ 6 := by
  rw [variance_evPMt] at hvar
  obtain ⟨i, hi⟩ :=
    pm_sqrt_of_mainTheorem h n d p hp ((evPMt_bound_iff p).mp hbd) ε hε hvar
  exact ⟨i, by rwa [infl_evPMt]⟩

end AaronsonAmbainis.Bridge

end
/- END UPSTREAM MODULE: AaronsonAmbainis.Bridge.PrintedAA -/

/- BEGIN UPSTREAM MODULE: AaronsonAmbainis.Conjecture -/
section
/-!
# The Aaronson–Ambainis conjecture: the statements, written with nothing but Mathlib

This file imports only Mathlib and uses no definition, instance or notation of this project, so
the meaning of the statements below depends on Mathlib alone: `MvPolynomial.eval`,
`MvPolynomial.totalDegree`, finite sums over `Fin N → Bool`, `Finset.filter`, `Function.update`,
`Real.pi`, `Real.sqrt`, real powers `x ^ (y : ℝ)`, the absolute value, and the field operations of
`ℝ`.

It contains statements only (`def … : Prop`); nothing is proved here. The theorems are in
`AaronsonAmbainis/Main.lean`. To know what has been proved it is enough to read this file.

The first definition, `PrintedConjecture`, is the conjecture as printed, in the normalisation of
Aaronson and Ambainis, with the number `7` for `O(1)`. `PrintedConjecture` is the statement of
the theorem `aaronson_ambainis` of `Main.lean`, so to check that the statement proved is the
conjecture, a reader needs to read only `PrintedConjecture`. Like `PrintedConjecture`,
`ExplicitBound` and `ExplicitBoundImproved` are stated on the cube `{0,1}^N` in the normalisation
of Aaronson and Ambainis; `FbsDegreeBound` is stated on the cube `{0,1}^n`. The last definition,
`ExplicitBoundPM`, is the main theorem (Theorem 1.1) of the paper of this repository,
`paper/aaronson_ambainis_paper.pdf`, on the cube `{-1,1}^n`, in the form with a lower bound `ε`
for the variance; a reader who checks `PrintedConjecture` does not need `ExplicitBoundPM`.

## Encoding

A point of either cube is `X : Fin N → Bool`, and the bit `true` is the number `1`. On the cube
`{0,1}^N` the bit `false` is the number `0`; on the cube `{-1,1}^n` of `ExplicitBoundPM` the bit
`false` is the number `-1`. The point `X^i` (the point `X` with the `i`-th bit flipped) is
`Function.update X i (!X i)`. The expectation over either cube is `(∑ X, …) / 2 ^ N`, with `N`
the number of variables (`n` in `ExplicitBoundPM`). The power
`ε^{5/2}` is the real power `ε ^ ((5 : ℝ) / 2)`.

## Sources

* S. Aaronson and A. Ambainis, *The need for structure in quantum speedups*, arXiv:0911.0996v3,
  Conjecture 6 (Conjecture 1.7 of the journal version, Theory of Computing 10 (2014), 133–166):
  "Let p : R^N → R be a polynomial of degree d. Suppose that 0 ≤ p(X) ≤ 1 for all X ∈ {0,1}^N,
  and E_{X∈{0,1}^N}[(p(X) − E[p])²] ≥ ε. Then there exists an i such that
  Inf_i[p] ≥ (ε/d)^{O(1)}", where "Inf_i[p] := E_{X∈{0,1}^N}[(p(X) − p(X^i))²]".
* A. Agarwal and S. Ben-David, *Oracle separations for the quantum-classical polynomial
  hierarchy*, arXiv:2410.19062 (version 2), Theorem 1.7: "Let f : {0,1}^n → [0,1] be a
  real-valued function which can be expressed as a polynomial of degree at most d. Then there is
  an assignment of weights {c_{x,i}}_{x∈{0,1}^n, i∈[n]} to inputs x and positions i ∈ [n] such
  that for all x, y ∈ {0,1}^n, we have  Σ_{i : x_i ≠ y_i} c_{x,i} ≥ |f(x) − f(y)|,
  Σ_{i=1}^n c_{x,i} ≤ (π²/4) d²."
-/

namespace AaronsonAmbainis

/-- The conjecture of Aaronson and Ambainis as printed (Conjecture 6 of arXiv:0911.0996v3, quoted
above), in the normalisation of Aaronson and Ambainis, with the absolute constant `7` for `O(1)`:
`Inf_i[p] ≥ (ε/d)^7`. "A polynomial of degree `d`" is read as a polynomial of total degree at
most `d`; the statement for total degree at most `d` is equivalent to the statement for degree
exactly `d`, because `(ε/d)^7` decreases in `d` and a polynomial of degree `0` has variance `0`.
The condition `ε > 0` is written out. -/
def PrintedConjecture : Prop :=
  ∀ (N d : ℕ) (p : MvPolynomial (Fin N) ℝ), p.totalDegree ≤ d →
    (∀ X : Fin N → Bool,
      0 ≤ MvPolynomial.eval (fun i => if X i then (1 : ℝ) else 0) p ∧
        MvPolynomial.eval (fun i => if X i then (1 : ℝ) else 0) p ≤ 1) →
    ∀ ε : ℝ, 0 < ε →
      (∑ X : Fin N → Bool,
          (MvPolynomial.eval (fun i => if X i then (1 : ℝ) else 0) p
            - (∑ Y : Fin N → Bool, MvPolynomial.eval (fun i => if Y i then (1 : ℝ) else 0) p)
                / 2 ^ N) ^ 2) / 2 ^ N ≥ ε →
      ∃ i : Fin N,
        (∑ X : Fin N → Bool,
          (MvPolynomial.eval (fun k => if X k then (1 : ℝ) else 0) p
            - MvPolynomial.eval
                (fun k => if Function.update X i (!X i) k then (1 : ℝ) else 0) p) ^ 2) / 2 ^ N
          ≥ (ε / (d : ℝ)) ^ 7

/-- `PrintedConjecture` with the explicit lower bound `(8 √15 / (125 π^4)) ε^{5/2} / d^6` in place
of `(ε/d)^7`. -/
def ExplicitBound : Prop :=
  ∀ (N d : ℕ) (p : MvPolynomial (Fin N) ℝ), p.totalDegree ≤ d →
    (∀ X : Fin N → Bool,
      0 ≤ MvPolynomial.eval (fun i => if X i then (1 : ℝ) else 0) p ∧
        MvPolynomial.eval (fun i => if X i then (1 : ℝ) else 0) p ≤ 1) →
    ∀ ε : ℝ, 0 < ε →
      (∑ X : Fin N → Bool,
          (MvPolynomial.eval (fun i => if X i then (1 : ℝ) else 0) p
            - (∑ Y : Fin N → Bool, MvPolynomial.eval (fun i => if Y i then (1 : ℝ) else 0) p)
                / 2 ^ N) ^ 2) / 2 ^ N ≥ ε →
      ∃ i : Fin N,
        (∑ X : Fin N → Bool,
          (MvPolynomial.eval (fun k => if X k then (1 : ℝ) else 0) p
            - MvPolynomial.eval
                (fun k => if Function.update X i (!X i) k then (1 : ℝ) else 0) p) ^ 2) / 2 ^ N
          ≥ 8 * Real.sqrt 15 / (125 * Real.pi ^ 4) * ε ^ ((5 : ℝ) / 2) / (d : ℝ) ^ 6

/-- Theorem 1.7 of arXiv:2410.19062 as printed (for `n ≥ 1` and `d ≥ 1`), as a proposition. It
is used only as the hypothesis of `aaronson_ambainis_of_fbsDegreeBound`: this project does not
prove it with the constant `π²/4`. (The unconditional theorems use a bound of the same kind with
a constant twice as large, which is proved in the directories `Row`, `Pack` and `Dual`.) -/
def FbsDegreeBound : Prop :=
  ∀ (n d : ℕ), 1 ≤ n → 1 ≤ d → ∀ f : (Fin n → Bool) → ℝ, (∀ x, 0 ≤ f x ∧ f x ≤ 1) →
    (∃ p : MvPolynomial (Fin n) ℝ, p.totalDegree ≤ d ∧
      ∀ x, f x = MvPolynomial.eval (fun i => if x i then (1 : ℝ) else 0) p) →
    ∃ c : (Fin n → Bool) → Fin n → ℝ,
      (∀ x y, ∑ i ∈ Finset.univ.filter (fun i => x i ≠ y i), c x i ≥ |f x - f y|) ∧
      (∀ x, ∑ i, c x i ≤ Real.pi ^ 2 / 4 * (d : ℝ) ^ 2)

/-- The conjecture of Aaronson and Ambainis with the explicit lower bound
`(32 √15 / (125 π^4)) ε^{5/2} / d^6`: the conclusion of `aaronson_ambainis_of_fbsDegreeBound`,
whose hypothesis is `FbsDegreeBound`. -/
def ExplicitBoundImproved : Prop :=
  ∀ (N d : ℕ) (p : MvPolynomial (Fin N) ℝ), p.totalDegree ≤ d →
    (∀ X : Fin N → Bool,
      0 ≤ MvPolynomial.eval (fun i => if X i then (1 : ℝ) else 0) p ∧
        MvPolynomial.eval (fun i => if X i then (1 : ℝ) else 0) p ≤ 1) →
    ∀ ε : ℝ, 0 < ε →
      (∑ X : Fin N → Bool,
          (MvPolynomial.eval (fun i => if X i then (1 : ℝ) else 0) p
            - (∑ Y : Fin N → Bool, MvPolynomial.eval (fun i => if Y i then (1 : ℝ) else 0) p)
                / 2 ^ N) ^ 2) / 2 ^ N ≥ ε →
      ∃ i : Fin N,
        (∑ X : Fin N → Bool,
          (MvPolynomial.eval (fun k => if X k then (1 : ℝ) else 0) p
            - MvPolynomial.eval
                (fun k => if Function.update X i (!X i) k then (1 : ℝ) else 0) p) ^ 2) / 2 ^ N
          ≥ 32 * Real.sqrt 15 / (125 * Real.pi ^ 4) * ε ^ ((5 : ℝ) / 2) / (d : ℝ) ^ 6

/-- The main theorem (Theorem 1.1) of the paper of this repository, on the cube `{-1,1}^n`, in the
form with a lower bound `ε` for the variance (Theorem 1.1 with `Var(p) > 0` is the case
`ε = Var(p)`): range `[-1,1]`, influence `Inf_i(p) = E[((p(x) − p(x^i))/2)²]`, explicit lower
bound `(√15 / (500 π^4)) ε^{5/2} / d^6`. The bit `true` is the number `1`, and the bit `false` is
the number `-1`. -/
def ExplicitBoundPM : Prop :=
  ∀ (n d : ℕ) (p : MvPolynomial (Fin n) ℝ), p.totalDegree ≤ d →
    (∀ X : Fin n → Bool, |MvPolynomial.eval (fun i => if X i then (1 : ℝ) else -1) p| ≤ 1) →
    ∀ ε : ℝ, 0 < ε →
      (∑ X : Fin n → Bool,
          (MvPolynomial.eval (fun i => if X i then (1 : ℝ) else -1) p
            - (∑ Y : Fin n → Bool, MvPolynomial.eval (fun i => if Y i then (1 : ℝ) else -1) p)
                / 2 ^ n) ^ 2) / 2 ^ n ≥ ε →
      ∃ i : Fin n,
        (∑ X : Fin n → Bool,
          ((MvPolynomial.eval (fun k => if X k then (1 : ℝ) else -1) p
            - MvPolynomial.eval
                (fun k => if Function.update X i (!X i) k then (1 : ℝ) else -1) p) / 2) ^ 2)
            / 2 ^ n
          ≥ Real.sqrt 15 / (500 * Real.pi ^ 4) * ε ^ ((5 : ℝ) / 2) / (d : ℝ) ^ 6

end AaronsonAmbainis

end
/- END UPSTREAM MODULE: AaronsonAmbainis.Conjecture -/

/- BEGIN UPSTREAM MODULE: AaronsonAmbainis.Bridge.Capstone -/
section
/-!
# From the statements of the project to the Mathlib-only statements of `Conjecture.lean`

`Conjecture.lean` states the conjecture, and the hypothesis `FbsDegreeBound`, with nothing but
Mathlib. Here the theorems of `Chain.lean` are carried over to its propositions:

* `explicitBound : ExplicitBound`, `printedConjecture : PrintedConjecture`,
  `explicitBoundPM : ExplicitBoundPM`
  from `AaronsonAmbainis.mainTheorem : MainTheorem`, which has no hypothesis;
* `explicitBoundImproved_of_fbsDegreeBound : FbsDegreeBound → ExplicitBoundImproved`
  from `AaronsonAmbainis.mainTheoremImproved_of_rowBound : RowBound → MainTheoremImproved`.
  The hypothesis `FbsDegreeBound` is Theorem 1.7 of arXiv:2410.19062 as printed; it gives
  `RowBound` (`rowBound_of_printed` in `PrintedRow.lean`). Nothing here says that it holds.

The theorems of `Main.lean` are these four theorems under their final names. The same bounds
without square roots are `explicitBound_sq`, `explicitBoundPM_sq` and
`explicitBoundImproved_sq_of_fbsDegreeBound`. The passage from the statements on the cube of
`Defs.lean` to polynomials, and from the bounds without square roots to the printed forms, is in
`PrintedAA.lean`. `PrintedAA.lean` also gives two steps used in some of the proofs below: the
real power `ε ^ ((5 : ℝ) / 2)` of `Conjecture.lean` equals `ε² √ε` (`rpow_five_halves`), and the
encoding `true ↦ 1`, `false ↦ -1` of `ExplicitBoundPM` is reached from the encoding
`true ↦ -1`, `false ↦ 1` of `Defs.lean` by negating every bit (`pmt_sq_of_mainTheorem`,
`pmt_sqrt_of_mainTheorem`). The axioms on which the theorems depend are printed at the end.
-/

namespace AaronsonAmbainis.Bridge

open Finset MvPolynomial

/-! ### The theorems with no hypothesis -/

/-- Conjecture 6 of arXiv:0911.0996 with `192 ε^5 ≤ 3125 π^8 d^12 Inf_i[p]²`, no hypothesis. -/
theorem explicitBound_sq (N d : ℕ) (p : MvPolynomial (Fin N) ℝ) (hp : p.totalDegree ≤ d)
    (hrange : ∀ X, 0 ≤ ev01 p X ∧ ev01 p X ≤ 1) (ε : ℝ) (hε : 0 < ε)
    (hvar : Ex (fun X => (ev01 p X - Ex (ev01 p)) ^ 2) ≥ ε) :
    ∃ i, 192 * ε ^ 5 ≤ 3125 * Real.pi ^ 8 * (d : ℝ) ^ 12
      * Ex (fun X => (ev01 p X - ev01 p (flipBit X i)) ^ 2) ^ 2 :=
  zo_sq_of_mainTheorem AaronsonAmbainis.mainTheorem N d p hp hrange ε hε hvar

/-- Conjecture 6 of arXiv:0911.0996 with `Inf_i[p] ≥ (8 √15 / (125 π^4)) ε^{5/2} / d^6`, no
hypothesis. -/
theorem explicitBound : ExplicitBound := by
  intro N d p hp hrange ε hε hvar
  rw [rpow_five_halves hε.le]
  exact zo_sqrt_of_mainTheorem AaronsonAmbainis.mainTheorem N d p hp hrange ε hε hvar

/-- Conjecture 6 of arXiv:0911.0996 as printed with `Inf_i[p] ≥ (ε/d)^7`, no hypothesis. -/
theorem printedConjecture : PrintedConjecture :=
  fun N d p hp hrange ε hε hvar =>
    zo_pow_of_mainTheorem AaronsonAmbainis.mainTheorem N d p hp hrange ε hε hvar

/-- Theorem 1.1 of the paper of this repository on `{-1,1}^n` (`true ↦ 1`, `false ↦ -1`), without
square roots: `3 ε^5 ≤ 50000 π^8 d^12 Inf_i(p)²`, no hypothesis. -/
theorem explicitBoundPM_sq (n d : ℕ) (p : MvPolynomial (Fin n) ℝ) (hp : p.totalDegree ≤ d)
    (hbd : ∀ X, |evPMt p X| ≤ 1) (ε : ℝ) (hε : 0 < ε)
    (hvar : Ex (fun X => (evPMt p X - Ex (evPMt p)) ^ 2) ≥ ε) :
    ∃ i, 3 * ε ^ 5 ≤ 50000 * Real.pi ^ 8 * (d : ℝ) ^ 12
      * Ex (fun X => ((evPMt p X - evPMt p (flipBit X i)) / 2) ^ 2) ^ 2 :=
  pmt_sq_of_mainTheorem AaronsonAmbainis.mainTheorem n d p hp hbd ε hε hvar

/-- Theorem 1.1 of the paper of this repository on `{-1,1}^n` (`true ↦ 1`, `false ↦ -1`):
`Inf_i(p) ≥ (√15 / (500 π^4)) ε^{5/2} / d^6`, no hypothesis. -/
theorem explicitBoundPM : ExplicitBoundPM := by
  intro n d p hp hbd ε hε hvar
  rw [rpow_five_halves hε.le]
  exact pmt_sqrt_of_mainTheorem AaronsonAmbainis.mainTheorem n d p hp hbd ε hε hvar

/-! ### The conditional theorem, both ends Mathlib-only -/

/-- Theorem 1.7 of arXiv:2410.19062 as printed ⟹ Conjecture 6 of arXiv:0911.0996 with
`3072 ε^5 ≤ 3125 π^8 d^12 Inf_i[p]²`. -/
theorem explicitBoundImproved_sq_of_fbsDegreeBound (h : FbsDegreeBound) (N d : ℕ)
    (p : MvPolynomial (Fin N) ℝ) (hp : p.totalDegree ≤ d)
    (hrange : ∀ X, 0 ≤ ev01 p X ∧ ev01 p X ≤ 1) (ε : ℝ) (hε : 0 < ε)
    (hvar : Ex (fun X => (ev01 p X - Ex (ev01 p)) ^ 2) ≥ ε) :
    ∃ i, 3072 * ε ^ 5 ≤ 3125 * Real.pi ^ 8 * (d : ℝ) ^ 12
      * Ex (fun X => (ev01 p X - ev01 p (flipBit X i)) ^ 2) ^ 2 :=
  zo_sq_of_mainTheoremImproved
    (AaronsonAmbainis.mainTheoremImproved_of_rowBound (rowBound_of_printed h))
    N d p hp hrange ε hε hvar

/-- Theorem 1.7 of arXiv:2410.19062 as printed ⟹ Conjecture 6 of arXiv:0911.0996 with
`Inf_i[p] ≥ (32 √15 / (125 π^4)) ε^{5/2} / d^6`. -/
theorem explicitBoundImproved_of_fbsDegreeBound : FbsDegreeBound → ExplicitBoundImproved := by
  intro h N d p hp hrange ε hε hvar
  rw [rpow_five_halves hε.le]
  exact zo_sqrt_of_mainTheoremImproved
    (AaronsonAmbainis.mainTheoremImproved_of_rowBound (rowBound_of_printed h))
    N d p hp hrange ε hε hvar

end AaronsonAmbainis.Bridge

/-! Types and axioms. -/

#check (AaronsonAmbainis.mainTheorem : AaronsonAmbainis.MainTheorem)
#check (AaronsonAmbainis.mainTheoremImproved_of_rowBound :
  AaronsonAmbainis.RowBound → AaronsonAmbainis.MainTheoremImproved)
#check (AaronsonAmbainis.Bridge.explicitBound : AaronsonAmbainis.ExplicitBound)
#check (AaronsonAmbainis.Bridge.explicitBoundImproved_of_fbsDegreeBound :
  AaronsonAmbainis.FbsDegreeBound → AaronsonAmbainis.ExplicitBoundImproved)
#print axioms AaronsonAmbainis.mainTheorem
#print axioms AaronsonAmbainis.mainTheoremImproved_of_rowBound
#print axioms AaronsonAmbainis.Bridge.explicitBound_sq
#print axioms AaronsonAmbainis.Bridge.explicitBound
#print axioms AaronsonAmbainis.Bridge.printedConjecture
#print axioms AaronsonAmbainis.Bridge.explicitBoundPM_sq
#print axioms AaronsonAmbainis.Bridge.explicitBoundPM
#print axioms AaronsonAmbainis.Bridge.explicitBoundImproved_sq_of_fbsDegreeBound
#print axioms AaronsonAmbainis.Bridge.explicitBoundImproved_of_fbsDegreeBound

end
/- END UPSTREAM MODULE: AaronsonAmbainis.Bridge.Capstone -/

/- BEGIN UPSTREAM MODULE: AaronsonAmbainis.Main -/
section
/-!
# The Aaronson–Ambainis conjecture: the final theorems

The statements proved here are the propositions of `AaronsonAmbainis/Conjecture.lean`. That file
imports only Mathlib and uses no definition of this project, so it is enough to read it in order
to know what has been proved.

* `aaronson_ambainis` — the conjecture of Aaronson and Ambainis (Conjecture 6 of arXiv:0911.0996v3;
  Conjecture 1.7 of the journal version) with the exponent `7` in place of `O(1)`: a polynomial
  `p` of degree at most `d` with `0 ≤ p ≤ 1` on `{0,1}^N` and variance at least `ε > 0` has a
  variable of influence at least `(ε/d)^7`.
* `aaronson_ambainis_explicit` — the same with the lower bound
  `(8 √15 / (125 π^4)) ε^{5/2} / d^6`.
* `aaronson_ambainis_pm` — Theorem 1.1 of the paper of this repository
  (`paper/aaronson_ambainis_paper.pdf`), on the cube `{-1,1}^n` (the bit `true` is `1`, the bit
  `false` is `-1`), for polynomials with values in `[-1,1]`, with the lower bound
  `(√15 / (500 π^4)) ε^{5/2} / d^6`.
* `aaronson_ambainis_of_fbsDegreeBound` — the lower bound `(32 √15 / (125 π^4)) ε^{5/2} / d^6`,
  under the hypothesis `FbsDegreeBound`, which is Theorem 1.7 of Agarwal and Ben-David
  (arXiv:2410.19062) as printed.

The first three theorems have no hypothesis. The proofs are assembled in `Chain.lean` (the chain
of the links, from the determinant inequality to the main theorem on the cube) and in
`Bridge/Capstone.lean` (the passage from the definitions of the project to the statements of
`Conjecture.lean`).
-/

namespace AaronsonAmbainis

/-- **The Aaronson–Ambainis conjecture**, as printed, with the exponent `7` for `O(1)`. -/
theorem aaronson_ambainis : PrintedConjecture :=
  Bridge.printedConjecture

/-- The Aaronson–Ambainis conjecture with the explicit lower bound
`(8 √15 / (125 π^4)) ε^{5/2} / d^6`. -/
theorem aaronson_ambainis_explicit : ExplicitBound :=
  Bridge.explicitBound

/-- Theorem 1.1 of the paper of this repository (`paper/aaronson_ambainis_paper.pdf`), on the cube
`{-1,1}^n`, with the explicit lower bound `(√15 / (500 π^4)) ε^{5/2} / d^6`. -/
theorem aaronson_ambainis_pm : ExplicitBoundPM :=
  Bridge.explicitBoundPM

/-- The explicit lower bound `(32 √15 / (125 π^4)) ε^{5/2} / d^6`, from Theorem 1.7 of
arXiv:2410.19062, which is a hypothesis here. -/
theorem aaronson_ambainis_of_fbsDegreeBound : FbsDegreeBound → ExplicitBoundImproved :=
  Bridge.explicitBoundImproved_of_fbsDegreeBound

end AaronsonAmbainis

#print axioms AaronsonAmbainis.aaronson_ambainis
#print axioms AaronsonAmbainis.aaronson_ambainis_explicit
#print axioms AaronsonAmbainis.aaronson_ambainis_pm
#print axioms AaronsonAmbainis.aaronson_ambainis_of_fbsDegreeBound

end
/- END UPSTREAM MODULE: AaronsonAmbainis.Main -/

/- Adapter to the existing Prove2Me target. -/
open AaronsonAmbainis in
theorem solution :
    ∃ C : ℕ, ∀ (N d : ℕ) (p : MvPolynomial (Fin N) ℝ) (ε : ℝ),
      p.totalDegree ≤ d →
      (∀ x : Fin N → Bool, 0 ≤ cubeEval p x ∧ cubeEval p x ≤ 1) →
      0 < ε → ε ≤ cubeVar p →
      ∃ i : Fin N, (ε / (d : ℝ)) ^ C ≤ cubeInfl p i := by
  refine ⟨7, ?_⟩
  intro N d p ε hd hb hε hv
  dsimp only [AaronsonAmbainis.cubeEval, AaronsonAmbainis.cubeVar,
    AaronsonAmbainis.cubeExp, AaronsonAmbainis.flipBit, AaronsonAmbainis.toReal] at hb hv ⊢
  have hb' : ∀ x : Fin N → Bool,
      0 ≤ MvPolynomial.eval (fun i => if x i then (1 : ℝ) else 0) p ∧
      MvPolynomial.eval (fun i => if x i then (1 : ℝ) else 0) p ≤ 1 := by
    exact hb
  have hv' :
      (∑ x : Fin N → Bool,
          (MvPolynomial.eval (fun i => if x i then (1 : ℝ) else 0) p -
            (∑ y : Fin N → Bool,
              MvPolynomial.eval (fun i => if y i then (1 : ℝ) else 0) p) / 2 ^ N) ^ 2)
        / 2 ^ N ≥ ε := by
    change ε ≤ (2 ^ N : ℝ)⁻¹ *
      ∑ x : Fin N → Bool,
        (MvPolynomial.eval (fun i => if x i then (1 : ℝ) else 0) p -
          (2 ^ N : ℝ)⁻¹ * ∑ y : Fin N → Bool,
            MvPolynomial.eval (fun i => if y i then (1 : ℝ) else 0) p) ^ 2 at hv
    simpa only [div_eq_mul_inv, mul_comm] using hv
  obtain ⟨i, hi⟩ := AaronsonAmbainis.aaronson_ambainis N d p hd hb' ε hε hv'
  refine ⟨i, ?_⟩
  change (ε / (d : ℝ)) ^ 7 ≤ (2 ^ N : ℝ)⁻¹ *
    ∑ x : Fin N → Bool,
      (MvPolynomial.eval (fun k => if x k then (1 : ℝ) else 0) p -
        MvPolynomial.eval
          (fun k => if Function.update x i (!x i) k then (1 : ℝ) else 0) p) ^ 2
  simpa only [div_eq_mul_inv, mul_comm] using hi


#print axioms solution

/-
UPSTREAM NOTICE
The Aaronson–Ambainis conjecture: paper and Lean 4 formalization

Copyright 2026 David Turturean

The Lean source code and the repository documentation are licensed under the
Apache License, Version 2.0. See LICENSE for the full text.

The included paper, "A proof of the Aaronson–Ambainis conjecture," is authored
by David Turturean and remains copyright its author.

The conjecture is due to Scott Aaronson and Andris Ambainis, "The need for
structure in quantum speedups," Theory of Computing 10 (2014), 133-166
(arXiv:0911.0996).

The proof builds on ideas from the following works, which are credited in the
paper together with the other sources:

  David Reimer, "Proof of the van den Berg-Kesten conjecture," Combinatorics,
  Probability and Computing 9 (2000), 27-32 (the Butterfly Lemma, which the
  bijection theorem of the paper refines, and the passage from antipodal pairs
  of subcubes to all pairs of points).

  Jeff Kahn, Michael Saks and Clifford Smyth, "The dual BKR inequality and
  Rudich's conjecture," Combinatorics, Probability and Computing 20 (2011),
  257-266 (the proof of the dual inequality, which uses that passage and
  certificates at a point and at its antipode).

  Raghav Kulkarni and Avishay Tal, "On fractional block sensitivity," Chicago
  Journal of Theoretical Computer Science 2016, Article 8 (the lemma on the
  fractional certificates at two points with different values).

  Shachar Lovett and Jiapeng Zhang, "Fractional certificates for bounded
  functions," ITCS 2023 (the use of fractional certificates and of level sets).

  Avantika Agarwal and Shalev Ben-David, "Oracle separations for the
  quantum-classical polynomial hierarchy," arXiv:2410.19062; ITCS 2026 (the
  bound for the fractional block sensitivity of bounded functions of low
  degree, and the method of its proof).

  Yuval Filmus, Hamed Hatami, Nathan Keller and Noam Lifshitz, "On the sum of
  the L1 influences of bounded functions," Israel Journal of Mathematics 214
  (2016), 167-192 (the bound for the sum of the absolute increments at a
  point).

The script scripts/fake_landrun.sh is adapted from scripts/fake-landrun.sh of
comparator (https://github.com/leanprover/comparator), which is licensed under
the Apache License, Version 2.0. The comments and the messages were rewritten.

The mathematical statements, the first draft of the paper and the Lean
formalization were produced by AI models, in a research harness developed by
David Turturean at PSI. David Turturean reviewed the paper and is responsible
for its correctness.

FULL APACHE-2.0 LICENSE

                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "[]"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright [yyyy] [name of copyright owner]

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

-/
