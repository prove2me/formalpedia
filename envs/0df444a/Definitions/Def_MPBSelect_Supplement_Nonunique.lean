-- Prove2me | Definitions.Def_MPBSelect_Supplement_Nonunique
-- name    : MPBSelect_Supplement_Nonunique
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T02:46:40.75545+00:00
-- url     : https://prove2.me/theorems/5fda3ff0-6b0c-4d56-9c3b-5f120e7e647f
-- title:
--   Non-unique MPB model and balance weights
-- statement:
--   This is the paper's finite MPB model with only the unique-MPB assumption removed. The conditional means remain pairwise distinct, so each $i^b$ is unique, while $i^*$ is the nonempty set of all maximizers of the preference probability.
--
--   For each $\ell\in i^*$, the bundle defines $d_j^\ell$, $\Xi_\ell=\{(i,\theta_b):i\ne i^b,\ i\ne\ell\}$ and the weight $W_i^\ell(\theta_b)$ in (EC.29), including $+\infty$ off $\Xi_\ell$. It also defines the nested lower bound and the set-valued estimated-MPB false-selection event used by Theorem EC.1.
-- source:
--   Kim, Kim, Song, Selection of the Most Probable Best, arXiv:2207.07533v2, Section EC.4 and (EC.29), p.ec14 (PDF p.57)

import Mathlib
import Definitions.Def_MPBSelect_Supplement_ExactRates

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

namespace MPBSelect.Supplement

/-- The finite-support MPB model with the unique-MPB assumption removed, as in §EC.4. Conditional
means remain pairwise distinct, so each conditional optimum is still unique. -/
structure NonuniqueProblem (k B : ℕ) where
  p : Fin B → ℝ
  y : Fin k → Fin B → ℝ
  lam : Fin k → Fin B → ℝ
  ib : Fin B → Fin k
  two_le_k : 2 ≤ k
  p_pos : ∀ b, 0 < p b
  p_sum : ∑ b, p b = 1
  y_injective : ∀ b, Function.Injective fun i => y i b
  ib_spec : ∀ b j, j ≠ ib b → y (ib b) b < y j b
  lam_pos : ∀ i b, 0 < lam i b

/-- Public bundle name for the non-unique-MPB model of §EC.4. -/
abbrev Nonunique := NonuniqueProblem

/-- The set `i* = argmax_j P_j` of all most probable best solutions. -/
def NonuniqueProblem.mpbSet {k B : ℕ} (P : NonuniqueProblem k B) : Finset (Fin k) :=
  Finset.univ.filter fun i => ∀ j, MPBSelect.prefProb P.p P.ib j ≤
    MPBSelect.prefProb P.p P.ib i

theorem NonuniqueProblem.mpbSet_nonempty {k B : ℕ} (P : NonuniqueProblem k B) :
    P.mpbSet.Nonempty := by
  have hk : 0 < k := lt_of_lt_of_le (by decide : 0 < 2) P.two_le_k
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ
    (fun j : Fin k => MPBSelect.prefProb P.p P.ib j)
    (by exact ⟨⟨0, hk⟩, Finset.mem_univ _⟩)
  exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun j => hi j (Finset.mem_univ _)⟩⟩

/-- The comparison gap `d_j^ell` in §EC.4. -/
def NonuniqueProblem.dEll {k B : ℕ} (P : NonuniqueProblem k B)
    (ell j : Fin k) : ℝ :=
  MPBSelect.prefProb P.p P.ib ell - MPBSelect.prefProb P.p P.ib j

/-- `Ξ_ell = {(i,θ_b) : i ≠ i^b, i ≠ ell}`. -/
def NonuniqueProblem.xiEll {k B : ℕ} (P : NonuniqueProblem k B)
    (ell : Fin k) : Finset (Fin k × Fin B) :=
  Finset.univ.filter fun x => x.1 ≠ P.ib x.2 ∧ x.1 ≠ ell

/-- `min_{j ≠ ell} d_j^ell`. The index set is nonempty because `k ≥ 2`. -/
def NonuniqueProblem.minDEll {k B : ℕ} (P : NonuniqueProblem k B)
    (ell : Fin k) : ℝ :=
  sInf {z : ℝ | ∃ j : Fin k, j ≠ ell ∧ z = P.dEll ell j}

/-- The extended balance weight `W_i^ell(θ_b)` in (EC.29), including the paper's `+∞` value
off `Ξ_ell`. -/
def NonuniqueProblem.wEll {k B : ℕ} (P : NonuniqueProblem k B)
    (ell i : Fin k) (b : Fin B) : EReal :=
  if (i, b) ∈ P.xiEll ell then
    if P.ib b = ell then
      ((max (min (P.minDEll ell) (P.dEll ell i / 2) / P.p b) 1 : ℝ) : EReal)
    else ((max (P.dEll ell i / P.p b) 1 : ℝ) : EReal)
  else ⊤

/-- The union `⋃_{ell∈i*} Ξ_ell` in Theorem EC.1. -/
def NonuniqueProblem.activePairs {k B : ℕ} (P : NonuniqueProblem k B) :
    Finset (Fin k × Fin B) :=
  Finset.univ.filter fun x => ∃ ell ∈ P.mpbSet, x ∈ P.xiEll ell

/-- The nested weight `min_{ell∈i*} W_i^ell(θ_b)`. The MPB set is nonempty. -/
def NonuniqueProblem.minWeight {k B : ℕ} (P : NonuniqueProblem k B)
    (i : Fin k) (b : Fin B) : EReal :=
  sInf {z : EReal | ∃ ell ∈ P.mpbSet, z = P.wEll ell i b}

/-- Pairwise Gaussian rate for the non-unique-MPB model. -/
def NonuniqueProblem.G {k B : ℕ} (P : NonuniqueProblem k B)
    (α : Fin k → Fin B → ℝ) (i : Fin k) (b : Fin B) : ℝ :=
  if 0 < α i b ∧ 0 < α (P.ib b) b then
    (P.y i b - P.y (P.ib b) b) ^ 2 /
      (2 * (P.lam i b ^ 2 / α i b + P.lam (P.ib b) b ^ 2 / α (P.ib b) b))
  else 0

/-- The right side of the lower bound in Theorem EC.1. The active pair set is finite and is
nonempty in the paper's `k ≥ 2`, nonempty-support setting. -/
def NonuniqueProblem.ldrLowerBound {k B : ℕ} (P : NonuniqueProblem k B)
    (α : Fin k → Fin B → ℝ) : EReal :=
  sInf {z : EReal | ∃ x ∈ P.activePairs,
    z = P.minWeight x.1 x.2 * (P.G α x.1 x.2 : EReal)}

/-- Independent Gaussian outputs for the non-unique-MPB extension. -/
def NonuniqueProblem.IsGaussianSamples {k B : ℕ} (P : NonuniqueProblem k B)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Y : Fin k → Fin B → ℕ → Ω → ℝ) : Prop :=
  (∀ i b r, Measurable (Y i b r) ∧
    Measure.map (Y i b r) μ = gaussianReal (P.y i b) ⟨P.lam i b ^ 2, sq_nonneg _⟩) ∧
  iIndepFun (fun q : (Fin k × Fin B) × ℕ => Y q.1.1 q.1.2 q.2) μ

/-- Estimated conditional-optimum mapping in the non-unique model, from the posterior means (5)
under the prior `pr` (zero precision: the noninformative prior). -/
def NonuniqueProblem.mappingHat {k B : ℕ} {Ω : Type*} (P : NonuniqueProblem k B)
    (pr : GaussianPrior k B) (N : ℕ → Fin k → Fin B → ℕ) (Y : Fin k → Fin B → ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) : Mapping k B :=
  fun b => argminFin (lt_of_lt_of_le (by decide : 0 < 2) P.two_le_k)
    (fun i => staticMean P.lam pr N Y n i b ω)

/-- Set-valued estimated MPB. -/
def NonuniqueProblem.mpbHat {k B : ℕ} {Ω : Type*} (P : NonuniqueProblem k B)
    (pr : GaussianPrior k B) (N : ℕ → Fin k → Fin B → ℕ) (Y : Fin k → Fin B → ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) : Finset (Fin k) :=
  MPBSelect.Supplement.mpbSet P.p (P.mappingHat pr N Y n ω)

/-- The set-valued false-selection event `{i*_n ≠ i*}` of Theorem EC.1. -/
def NonuniqueProblem.falseSelectionEvent {k B : ℕ} {Ω : Type*}
    (P : NonuniqueProblem k B) (pr : GaussianPrior k B) (N : ℕ → Fin k → Fin B → ℕ)
    (Y : Fin k → Fin B → ℕ → Ω → ℝ) (n : ℕ) : Set Ω :=
  {ω | P.mpbHat pr N Y n ω ≠ P.mpbSet}

end MPBSelect.Supplement


