-- Prove2me | Definitions.Def_AgnosticImitate_Reduction_Setting
-- name    : AgnosticImitate_Reduction_Setting
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T21:23:16.193456+00:00
-- url     : https://prove2.me/theorems/e774e4c6-2333-4add-a36c-91a108b4104e
-- title:
--   Labeled distributions, predictors, admissible classes, multiaccuracy, conditional multiaccuracy and agnostic learning
-- statement:
--   The objects of §1 (pp. 1–2, PDF 3–4), Definition 1.5 (p. 9, PDF 11) and §2 (p. 14, PDF 16).
--
--   - **Label-mean encoding.** Labels are $y\in\{\pm1\}$. A labeled distribution $D$ on $X\times\{\pm1\}$ with feature marginal $D_X=\mu$ (a probability measure on a measurable space $X$) is given by its label mean $g(x)=\mathbb E[y\mid x]\in[-1,1]$, and
--   $$\mathbb E_D[\varphi(x,y)]=\int\Big(\tfrac{1+g(x)}2\,\varphi(x,1)+\tfrac{1-g(x)}2\,\varphi(x,-1)\Big)\,d\mu(x)\quad(\texttt{expect}).$$
--   - **Predictors** (`IsPredictor`): measurable $p:X\to\mathbb R$ with $p(x)\in[-1,1]$; the same notion is used for class members and label means.
--   - **Admissible class** (`IsAdmissibleClass`): $C$ consists of predictors, contains the constant $1$, and is closed under negation and convex combinations (the standing assumption after Definition 1.5).
--   - **Absolute loss** `l1Loss` $=\mathbb E[|y-p(x)|]$.
--   - **$(C,\varepsilon)$-multiaccuracy** (`IsMultiaccurate`): $|\mathbb E[c(x)(y-p(x))]|\le\varepsilon$ for every $c\in C$, i.e. $\max_{c\in C}|\mathbb E[c(x)(y-p(x))]|\le\varepsilon$.
--   - **$(C,\varepsilon)$-conditional multiaccuracy** with respect to a splitting function $f:X\to V$ (`IsCondMultiaccurate`), in the per-level-set reading: for every value $v$ and every $c\in C$, $|\mathbb E[\mathbf 1\{f(x)=v\}\,c(x)(y-p(x))]|\le\varepsilon$ (`levelInd` is the indicator).
--   - **$(C,\varepsilon)$-agnostic learning** (`IsAgnosticLearner`): $p$ is a measurable $[-1,1]$-valued predictor and $\mathbb E[|y-p(x)|]\le\inf_{c\in C}\mathbb E[|y-c(x)|]+\varepsilon$; the infimum is over the nonempty class $C$ of values bounded below by $0$, so it is the paper's $\min$ whenever that exists.
--   - **Oracle query** (`queryMean`): the query $(m,p')$ of Algorithm 1, line 3, asks about the labeled distribution with marginal $\mu$ and label mean $m\,g+(1-m)\,p'$.
-- source:
--   Casacuberta, Gopalan, Kanade, Reingold, Stavropoulos, Tankala (2026), Agnostic Learning by Imitating, STOC 2027 submission, SHA-256 225d86c2…0fb04, §1 (pp. 1–2, PDF 3–4), Definition 1.5 (p. 9, PDF 11), §2 (p. 14, PDF 16)

import Mathlib

noncomputable section
open MeasureTheory Classical

namespace AgnosticImitate.Reduction

/-! # Labeled distributions, predictors, multiaccuracy and agnostic learning

Casacuberta, Gopalan, Kanade, Reingold, Stavropoulos, Tankala (2026), *Agnostic Learning by
Imitating*, §1 (pp. 1–2, PDF 3–4), §1.3 (pp. 5–6, PDF 7–8), Definition 1.5 (p. 9, PDF 11),
§2 (p. 14, PDF 16).

**Label-mean encoding.** Labels are `y ∈ {±1}`. A labeled distribution `D` on `X × {±1}` with
feature marginal `μ` is determined (up to `μ`-null sets) by its label mean
`g(x) = E[y | x] ∈ [-1, 1]`, and
`E_D[φ(x, y)] = ∫ ((1 + g x)/2 · φ(x, 1) + (1 - g x)/2 · φ(x, -1)) dμ(x)`. -/

variable {X : Type*} [MeasurableSpace X]

/-- A predictor `p : X → [±1]` (also used for class members and label means): a measurable
real function with values in `[-1, 1]` (p. 1; `[±1] = [-1, 1]`, p. 14). -/
def IsPredictor (p : X → ℝ) : Prop :=
  Measurable p ∧ ∀ x, p x ∈ Set.Icc (-1 : ℝ) 1

/-- The standing assumption on the base class (p. 9, after Definition 1.5): `C` consists of
predictors `X → [±1]`, contains the constant function `1`, and is closed under negation and
under convex combinations. -/
structure IsAdmissibleClass (C : Set (X → ℝ)) : Prop where
  isPredictor : ∀ c ∈ C, IsPredictor c
  one_mem : (fun _ => (1 : ℝ)) ∈ C
  neg_mem : ∀ c ∈ C, (fun x => -c x) ∈ C
  convex : Convex ℝ C

/-- `E_{(x,y) ∼ D}[φ(x, y)]` for the labeled distribution with feature marginal `μ` and label
mean `g` (label-mean encoding; only the values `φ x 1` and `φ x (-1)` are used). -/
def expect (μ : Measure X) (g : X → ℝ) (φ : X → ℝ → ℝ) : ℝ :=
  ∫ x, ((1 + g x) / 2 * φ x 1 + (1 - g x) / 2 * φ x (-1)) ∂μ

/-- The expected absolute loss `E[|y - p(x)|]` (inequality (1), p. 1). -/
def l1Loss (μ : Measure X) (g : X → ℝ) (p : X → ℝ) : ℝ :=
  expect μ g (fun x y => |y - p x|)

/-- `(C, ε)`-multiaccuracy (inequality (2), p. 2; Definition 1.5, p. 9):
`max_{c ∈ C} |E[c(x)(y - p(x))]| ≤ ε`, written as a bound for every `c ∈ C`
(equivalent to the bound on the supremum). -/
def IsMultiaccurate (μ : Measure X) (C : Set (X → ℝ)) (g : X → ℝ) (p : X → ℝ) (ε : ℝ) : Prop :=
  ∀ c ∈ C, |expect μ g (fun x y => c x * (y - p x))| ≤ ε

/-- The indicator `1{f(x) = v}` of a level set of `f`. -/
def levelInd {V : Type*} (f : X → V) (v : V) : X → ℝ :=
  fun x => if f x = v then 1 else 0

/-- `(C, ε)`-conditional multiaccuracy with respect to a splitting function `f : X → V`
(p. 6, PDF 8; footnote 5, p. 11), in the per-level-set reading: for every value `v`,
`max_{c ∈ C} |E[1{f(x) = v} · c(x)(y - p(x))]| ≤ ε`. -/
def IsCondMultiaccurate (μ : Measure X) (C : Set (X → ℝ)) (g : X → ℝ) {V : Type*}
    (f : X → V) (p : X → ℝ) (ε : ℝ) : Prop :=
  ∀ v : V, ∀ c ∈ C, |expect μ g (fun x y => levelInd f v x * c x * (y - p x))| ≤ ε

/-- `(C, ε)`-agnostic learning (inequality (1), p. 1): a measurable `[-1,1]`-valued predictor and
`E[|y - p(x)|] ≤ min_{c ∈ C} E[|y - c(x)|] + ε`, with the minimum written as the infimum over
the (nonempty, bounded below) class `C`. -/
def IsAgnosticLearner (μ : Measure X) (C : Set (X → ℝ)) (g : X → ℝ) (p : X → ℝ) (ε : ℝ) :
    Prop :=
  IsPredictor p ∧ l1Loss μ g p ≤ (⨅ c : C, l1Loss μ g (c : X → ℝ)) + ε

/-- The label mean of an oracle query `(m, p')` (Algorithm 1, line 3, p. 5): the labeled
distribution with feature marginal `μ` and `E[z | x] = m(x) · g(x) + (1 - m(x)) · p'(x)`. -/
def queryMean (g m p' : X → ℝ) : X → ℝ :=
  fun x => m x * g x + (1 - m x) * p' x

end AgnosticImitate.Reduction


