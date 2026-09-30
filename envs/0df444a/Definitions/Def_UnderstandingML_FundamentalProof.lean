-- Prove2me | Definitions.Def_UnderstandingML_FundamentalProof
-- name    : UnderstandingML_FundamentalProof
-- status  : Definition
-- author  : @naimengye
-- created : 2026-09-24T05:53:32.053996+00:00
-- url     : https://prove2.me/theorems/102f3d30-1ae8-4b75-8f23-017b8246be06
-- title:
--   Chapter 28: the lower-bound distributions D_b on a shattered set, the Maximum-Likelihood (majority) rule of Lemma 28.1, and ε-nets (Definition 28.2)
-- statement:
--   Chapter 28 of Shalev-Shwartz and Ben-David. `uniformOn C` is the uniform distribution on the points $c_1, \dots, c_d$; `flipEta C ρ b` is the conditional label probability $(1 + \rho)/2$ at $c_i$ when $b_i = 1$ and $(1-\rho)/2$ when $b_i = -1$; `lowerBoundLaw C ρ b` is the distribution $D_b$ of §28.2.2 ($c_i$ uniform, label $b_i$ with probability $(1+\rho)/2$), which for $d = 1$ and $\rho = \epsilon$ gives the two distributions $D_+, D_-$ of §28.2.1. `IsMajorityRule C A` says $A$ is the Maximum-Likelihood rule $A_{ML}$ of Lemma 28.1: at each $c_i$ it predicts the majority of the labels observed at $c_i$ (ties arbitrary). **Definition 28.2 (ε-net).** `IsEpsNet H D ε S` says $S$ is an $\epsilon$-net for $H \subseteq 2^X$ with respect to $D$: every $h \in H$ with $D(h) \ge \epsilon$ meets $S$ (a hypothesis $h$ being the set $\{x : h(x) = 1\}$).
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §28.2 pp. 394-396 (D₊, D₋, D_b, A_ML), §28.3 p. 398 (Definition 28.2)

import Definitions.Def_UnderstandingML_NearestNeighbor
import Definitions.Def_UnderstandingML_Rademacher

/-!
# Shalev-Shwartz and Ben-David, *Understanding Machine Learning*, Chapter 28: proof of the
# fundamental theorem of learning theory

Shalev-Shwartz and Ben-David, *Understanding Machine Learning: From Theory to Algorithms*,
Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §28.1–§28.3.

Throughout, `H` is a class of functions from `X` to `{0,1}`, the loss is the 0–1 loss and
`VCdim(H) = d < ∞`.

**The lower-bound distributions (§28.2, pp. 393–395).** For a shattered set `C = {c₁, …, c_d}`,
`ρ ∈ (0, 1)` and `b ∈ {±1}^d`, `D_b` samples `cᵢ` uniformly from `C` and labels it `bᵢ` with
probability `(1 + ρ)/2`, `−bᵢ` with probability `(1 − ρ)/2`; for `d = 1`, `C = {c}` and `ρ = ε`
these are the two distributions `D₊, D₋` of §28.2.1. The **Maximum-Likelihood rule** `A_ML`
(Lemma 28.1) predicts at each `cᵢ` the majority of the labels observed at `cᵢ`.

**ε-nets (Definition 28.2, p. 398).** `S ⊆ X` is an `ε`-net for `H ⊆ 2^X` with respect to `D`
if every `h ∈ H` with `D(h) ≥ ε` meets `S`.

**Conventions.** `D_b` is `condLaw` of Chapter 19: the uniform law on `C` composed with the
Bernoulli labels of conditional probability `(1 ± ρ)/2`; labels `±1` are `Bool`. A hypothesis
`h` is identified with the set `{x : h(x) = 1}`. Majority rules break ties arbitrarily. Risks,
samples and learners are those of Chapter 2; the growth-function and Rademacher notions are
Chapters 6 and 26.
-/

open MeasureTheory

namespace UnderstandingML

section LowerBound

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

/-- The uniform distribution on the points `c₁, …, c_d` (p. 395). -/
noncomputable def uniformOn (C : Fin d → X) : Measure X :=
  (d : ENNReal)⁻¹ • ∑ i, Measure.dirac (C i)

open Classical in
/-- The conditional probability of the label `1` under `D_b`: `(1 + ρ)/2` at `cᵢ` if `bᵢ = 1`,
`(1 − ρ)/2` at `cᵢ` if `bᵢ = 0`, and `1/2` off `C` (irrelevant, `C` carries all the mass). -/
noncomputable def flipEta (C : Fin d → X) (ρ : ℝ) (b : Fin d → Bool) : X → ℝ := fun x ↦
  if ∃ i, x = C i ∧ b i = true then (1 + ρ) / 2
  else if ∃ i, x = C i then (1 - ρ) / 2 else 1 / 2

/-- The distribution `D_b` over `X × {0,1}` of §28.2: `cᵢ` uniform on `C`, label `bᵢ` with
probability `(1 + ρ)/2` (p. 395); for `d = 1` and `ρ = ε` the distributions `D₊, D₋` of
§28.2.1 (p. 394). -/
noncomputable def lowerBoundLaw (C : Fin d → X) (ρ : ℝ) (b : Fin d → Bool) : Measure (X × Bool) :=
  condLaw (uniformOn C) (flipEta C ρ b)

open Classical in
/-- `A` is a **Maximum-Likelihood (majority-vote) rule** on `C` (Lemma 28.1): at each `cᵢ` it
predicts the majority of the labels observed at `cᵢ`, ties broken arbitrarily. -/
def IsMajorityRule (C : Fin d → X) (A : Learner (X × Bool) (X → Bool)) : Prop :=
  ∀ (m : ℕ) (S : Fin m → X × Bool) (i : Fin d),
    ((Finset.univ.filter (fun r ↦ (S r).1 = C i ∧ (S r).2 = false)).card <
        (Finset.univ.filter (fun r ↦ (S r).1 = C i ∧ (S r).2 = true)).card →
      A m S (C i) = true) ∧
    ((Finset.univ.filter (fun r ↦ (S r).1 = C i ∧ (S r).2 = true)).card <
        (Finset.univ.filter (fun r ↦ (S r).1 = C i ∧ (S r).2 = false)).card →
      A m S (C i) = false)

end LowerBound

section EpsNet

variable {X : Type*} [MeasurableSpace X]

/-- **Definition 28.2 (ε-net).** `S` is an `ε`-net for `H` with respect to `D` if every `h ∈ H`
with `D(h) ≥ ε` contains some point of `S`. -/
def IsEpsNet (H : Set (X → Bool)) (D : Measure X) (ε : ℝ) {m : ℕ} (S : Fin m → X) : Prop :=
  ∀ h ∈ H, ENNReal.ofReal ε ≤ D {x | h x = true} → ∃ i, h (S i) = true

end EpsNet

end UnderstandingML


