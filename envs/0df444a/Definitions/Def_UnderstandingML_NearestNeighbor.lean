-- Prove2me | Definitions.Def_UnderstandingML_NearestNeighbor
-- name    : UnderstandingML_NearestNeighbor
-- status  : Definition
-- author  : @naimengye
-- created : 2026-09-24T04:55:22.849846+00:00
-- url     : https://prove2.me/theorems/2c4a20b9-d1fd-49e7-9866-6e8516fa4d26
-- title:
--   Chapter 19: Bernoulli labels and conditional-probability distributions, the Bayes rule, the k-NN rules (19.1), majority votes, the nearest-neighbor distance and the cube [0,1]^d
-- statement:
--   Chapter 19 of Shalev-Shwartz and Ben-David. **Labels.** `bernoulliLaw p` is the law of a Bernoulli label with $P[y = 1] = p$ (the book's $y \sim p$); `bernoulliErr p y'` $= P_{y \sim p}[y \ne y']$; `majority Z` is the majority label of a finite family, $1$ iff strictly more than half are $1$ (the book's $\mathbb{1}[p' > 1/2]$); `condLaw DX η` is the distribution over $X \times \{0,1\}$ with marginal $D_X$ and conditional probability $\eta(x) = P[y = 1 \mid x]$, i.e. $x \sim D_X$, then $y \sim \eta(x)$; `bayesRule η` is the Bayes optimal rule $h^\star(x) = \mathbb{1}[\eta(x) > 1/2]$. **Rules (§19.1).** In a metric space, `nnDist S x` is the distance $\|x - x_{\pi_1(x)}\|$ to the nearest sample point; `IsKNNRuleWith k φ h` says $h$ is a $k$-NN rule with respect to $\varphi$ (19.1): there is a reordering $\pi_1(x), \dots, \pi_m(x)$ of the sample indices by distance to $x$, determined by the instances $x_1, \dots, x_m$ and $x$ alone, with $h_S(x) = \varphi((x_{\pi_1(x)}, y_{\pi_1(x)}), \dots, (x_{\pi_k(x)}, y_{\pi_k(x)}))$ for every sample of size $m \ge k$. Ties in distance may be broken arbitrarily but not by the labels. A rule that chooses among equidistant neighbors by their labels is not the book's rule, and it defeats the chapter's bounds. For $D_X = \delta_a$, $\eta \equiv 0.1$, and a 1-NN rule predicting $1$ whenever some nearest neighbor has label $1$, $\mathbb{E}[L_D(h_S)] = 0.252 > 0.2 = 2L_D(h^\star)$ at $m = 2$; `IsKNNRule k h` is the majority $k$-NN rule and `IsNN1Rule h` the 1-NN rule $h_S(x) = y_{\pi_1(x)}$. `cube d` is $X = [0,1]^d \subseteq \mathbb{R}^d$ with the Euclidean distance.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §19.1 pp. 258-259 (the k-NN rules, Equation (19.1)), §19.2.1 p. 260 (X = [0,1]^d, D_X, η, h⋆, c-Lipschitz η), §19.6 p. 266 (y ∼ p)

import Definitions.Def_UnderstandingML_Linear
import Mathlib.MeasureTheory.Measure.GiryMonad

/-!
# Shalev-Shwartz and Ben-David, *Understanding Machine Learning*, Chapter 19: nearest neighbor

Shalev-Shwartz and Ben-David, *Understanding Machine Learning: From Theory to Algorithms*,
Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §19.1–§19.2.

**The `k`-NN rules (§19.1, p. 258–259).** The instance domain `X` carries a metric `ρ`. For a
training sample `S = (x₁, y₁), …, (x_m, y_m)` and a point `x`, let `π₁(x), …, π_m(x)` be a
reordering of `{1, …, m}` by distance to `x`, `ρ(x, x_{πᵢ(x)}) ≤ ρ(x, x_{πᵢ₊₁(x)})`. The `k`-NN
rule for binary classification returns the majority label among `{y_{πᵢ(x)} : i ≤ k}`; for
`k = 1` this is the 1-NN rule `h_S(x) = y_{π₁(x)}`; in general, for `φ : (X × Y)^k → Y`, the
`k`-NN rule with respect to `φ` is `h_S(x) = φ((x_{π₁(x)}, y_{π₁(x)}), …, (x_{π_k(x)}, y_{π_k(x)}))`
(19.1).

**The analysis (§19.2.1, p. 260).** `X = [0,1]^d` with the Euclidean distance, `Y = {0,1}`, the
0–1 loss. For a distribution `D` over `X × Y`, `D_X` is the marginal over `X` and
`η(x) = P[y = 1 | x]` the conditional probability; the Bayes optimal rule is
`h⋆(x) = 𝟙[η(x) > 1/2]`, and `η` is assumed `c`-Lipschitz.

**Conventions.** A distribution over `X × {0,1}` with marginal `D_X` and conditional probability
`η` is written `condLaw D_X η`: draw `x ∼ D_X`, then `y ∼ Bernoulli(η(x))`; every distribution
with a regression function `η` is of this form. A `k`-NN rule is any rule of the shape (19.1)
for *some* distance ordering of the sample (ties are broken arbitrarily), for `k ≤ m`; majority
votes predict `1` iff strictly more than half of the `k` labels are `1` (the book's
`𝟙[p' > 1/2]`, Lemma 19.7). Learning rules are deterministic, and the expectation statements
assume the rule is measurable in `(S, x)` (Remark 3.1). The nearest-neighbor distance
`‖x − x_{π₁(x)}‖` is the infimum of the distances to the sample points.
-/

open MeasureTheory

namespace UnderstandingML

/-! ### Labels drawn from a conditional probability -/

section Labels

/-- The Bernoulli law on `{0,1} = Bool` with `P[y = 1] = p` (`y ∼ p` in the book's shorthand,
p. 266). -/
noncomputable def bernoulliLaw (p : ℝ) : Measure Bool :=
  ENNReal.ofReal p • Measure.dirac true + ENNReal.ofReal (1 - p) • Measure.dirac false

/-- `P_{y ∼ p}[y ≠ y']`: the probability that a Bernoulli(`p`) label differs from `y'`. -/
def bernoulliErr (p : ℝ) (y' : Bool) : ℝ := if y' then 1 - p else p

/-- The majority label of a finite family of labels: `1` iff strictly more than half are `1`. -/
noncomputable def majority {ι : Type*} [Fintype ι] (Z : ι → Bool) : Bool :=
  decide ((Fintype.card ι : ℝ) / 2 < ∑ i, if Z i then (1 : ℝ) else 0)

variable {X : Type*} [MeasurableSpace X]

/-- The distribution `D` over `X × {0,1}` with marginal `D_X` and conditional probability
`η(x) = P[y = 1 | x]` (p. 260): sample `x ∼ D_X`, then `y ∼ Bernoulli(η(x))`. -/
noncomputable def condLaw (DX : Measure X) (η : X → ℝ) : Measure (X × Bool) :=
  DX.bind (fun x ↦ (bernoulliLaw (η x)).map (fun y ↦ (x, y)))

/-- The **Bayes optimal rule** `h⋆(x) = 𝟙[η(x) > 1/2]` (p. 260). -/
noncomputable def bayesRule (η : X → ℝ) : X → Bool := fun x ↦ decide (1 / 2 < η x)

end Labels

/-! ### Nearest neighbor rules -/

section Rules

variable {X : Type*} [MetricSpace X]

/-- The distance `‖x − x_{π₁(x)}‖` from `x` to its nearest neighbor in the sample `S`. -/
noncomputable def nnDist {Y : Type*} {m : ℕ} (S : Fin m → X × Y) (x : X) : ℝ :=
  ⨅ i, dist x (S i).1

/-- `h` is a **`k`-NN rule with respect to `φ`** (19.1): there is a reordering `π(x)` of the
sample indices by distance to `x` that is determined by the instances `x₁, …, x_m` and `x` alone
(the book's `π₁(x), …, π_m(x)`), such that for every sample `S` of size `m ≥ k` and every `x`,
`h_S(x) = φ((x_{π₁(x)}, y_{π₁(x)}), …, (x_{π_k(x)}, y_{π_k(x)}))`. Ties in distance may be broken
arbitrarily, but not by looking at the labels: a rule that picks among equidistant neighbors by
label defeats Lemma 19.1 and Theorems 19.3 and 19.5 when `D_X` has atoms. -/
def IsKNNRuleWith {Y : Type*} (k : ℕ) (φ : (Fin k → X × Y) → Y)
    (h : (m : ℕ) → (Fin m → X × Y) → X → Y) : Prop :=
  ∃ π : (m : ℕ) → (Fin m → X) → X → Fin m ≃ Fin m,
    (∀ (m : ℕ) (xs : Fin m → X) (x : X) (i j : Fin m), i ≤ j →
      dist x (xs (π m xs x i)) ≤ dist x (xs (π m xs x j))) ∧
    ∀ (m : ℕ) (hk : k ≤ m) (S : Fin m → X × Y) (x : X),
      h m S x = φ (fun i ↦ S (π m (fun j ↦ (S j).1) x (Fin.castLE hk i)))

/-- `h` is a **`k`-NN rule** for binary classification (p. 259): the majority label among the
`k` nearest neighbors. -/
def IsKNNRule (k : ℕ) (h : Learner (X × Bool) (X → Bool)) : Prop :=
  IsKNNRuleWith k (fun s ↦ majority (fun i ↦ (s i).2)) h

/-- `h` is a **1-NN rule** (p. 259): `h_S(x) = y_{π₁(x)}`, the label of a nearest neighbor. -/
def IsNN1Rule (h : Learner (X × Bool) (X → Bool)) : Prop :=
  IsKNNRuleWith 1 (fun s ↦ (s 0).2) h

end Rules

/-- The unit cube `X = [0,1]^d ⊆ ℝ^d` with the Euclidean distance (p. 260). -/
abbrev cube (d : ℕ) := {x : Vec d // ∀ j, x j ∈ Set.Icc (0 : ℝ) 1}

end UnderstandingML


