-- Prove2me | Definitions.Def_TestDistancing_Equilibrium_Model
-- name    : TestDistancing_Equilibrium_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:33:19.469312+00:00
-- url     : https://prove2.me/theorems/e4d4d0c8-9be3-4a27-892b-7b8e5ffba7af
-- title:
--   Activity game, symmetric equilibrium and policy regions
-- statement:
--   Agents choose social activity $x_i\in[0,1]$. An undirected contact $ij$ forms independently with probability $\eta x_i x_j$; infection then follows the finite cascade. A testing policy is $(\alpha_L,\alpha_H)$, and a symmetric strategy $(\gamma_L,\gamma_H)$ independently puts probability $\gamma_T$ on activity one for each type $T$. Utility is
--
--   $$u_i(x,\alpha_L,\alpha_H)=v_i x_i-P_i^{\mathrm{inf}}(x,\alpha_L,\alpha_H)-c\alpha_i.$$
--
--   The definition checks equilibrium against every unilateral activity $x_i\in[0,1]$, defines the resulting infection probability, and reproduces the four threshold regions $A_1,\ldots,A_4$ of Section 3.1. The high type comprises the first $\lceil r_H n\rceil$ agents, a disclosed scaling convention.
-- source:
--   Acemoglu, Makhdoumi, Malekian & Ozdaglar, Testing, Voluntary Social Distancing and the Spread of an Infection, NBER Working Paper 27483 (July 2020), https://www.nber.org/papers/w27483, pp. 5–11 (PDF 7–13), §2, §3.1, Definitions 1–3 and (1)

import Mathlib
import Definitions.Def_TestDistancing_Equilibrium_Cascade
open Classical

namespace TestDistancing.Equilibrium

structure Params where
  vL : ℝ
  vH : ℝ
  η : ℝ
  β : ℝ
  p : ℝ
  c : ℝ
  rH : ℝ

/-- Section 2's standing parameter assumptions, with the positive high-type fraction. -/
def Params.Standing (P : Params) : Prop :=
  0 ≤ P.vL ∧ P.vL < P.vH ∧ P.vH ≤ 1 ∧
  0 < P.η ∧ P.η ≤ 1 ∧ 0 < P.β ∧ P.β ≤ 1 ∧
  0 ≤ P.p ∧ P.p < 1 ∧ 0 < P.c ∧ 0 < P.rH ∧ P.rH < 1

/-- The first ⌈r_H n⌉ agents have high value. -/
noncomputable def IsHigh {n : ℕ} (P : Params) (i : Fin n) : Prop := (i : ℕ) < ⌈P.rH * n⌉₊

noncomputable def val {n : ℕ} (P : Params) (i : Fin n) : ℝ :=
  if IsHigh P i then P.vH else P.vL

/-- Policy coordinates are `(α_L, α_H)`. -/
noncomputable def testProb {n : ℕ} (P : Params) (α : ℝ × ℝ) (i : Fin n) : ℝ :=
  if IsHigh P i then α.2 else α.1

/-- Definition 1: infection probability conditional on the contact graph. -/
noncomputable def PinfG {n : ℕ} (P : Params) (G : SimpleGraph (Fin n))
    (α : ℝ × ℝ) (i : Fin n) : ℝ :=
  cascadeInf G (testProb P α) P.β P.p i

/-- Independent undirected links, sampled once for each pair `i < j`. -/
noncomputable def netWeight {n : ℕ} (P : Params) (x : Fin n → ℝ)
    (G : SimpleGraph (Fin n)) : ℝ :=
  ∏ i : Fin n, ∏ j : Fin n,
    if i < j then bern (P.η * x i * x j) (decide (G.Adj i j)) else 1

/-- Definition 2: infection probability after averaging over the random contact graph. -/
noncomputable def Pinf {n : ℕ} (P : Params) (x : Fin n → ℝ)
    (α : ℝ × ℝ) (i : Fin n) : ℝ :=
  ∑ G : SimpleGraph (Fin n), netWeight P x G * PinfG P G α i

/-- Strategy coordinates are `(γ_L, γ_H)`, the probabilities of playing activity one. -/
noncomputable def stratProb {n : ℕ} (P : Params) (γ : ℝ × ℝ) (i : Fin n) : ℝ :=
  if IsHigh P i then γ.2 else γ.1

def profileOf {n : ℕ} (a : Fin n → Bool) : Fin n → ℝ :=
  fun j => if a j then 1 else 0

/-- Expected infection when `i` plays `xi` and the other agents mix independently. -/
noncomputable def PinfMix {n : ℕ} (P : Params) (γ α : ℝ × ℝ)
    (i : Fin n) (xi : ℝ) : ℝ :=
  ∑ a : Fin n → Bool,
    (∏ j : Fin n, if j = i then (if a j then (1 : ℝ) else 0)
      else bern (stratProb P γ j) (a j)) *
    Pinf P (Function.update (profileOf a) i xi) α i

/-- Expected utility (1) of playing `xi` against a symmetric mixed profile. -/
noncomputable def expUtil {n : ℕ} (P : Params) (γ α : ℝ × ℝ)
    (i : Fin n) (xi : ℝ) : ℝ :=
  val P i * xi - PinfMix P γ α i xi - P.c * testProb P α i

/-- Utility (1) at a deterministic activity profile. -/
noncomputable def pureUtil {n : ℕ} (P : Params) (x : Fin n → ℝ) (α : ℝ × ℝ)
    (i : Fin n) : ℝ :=
  val P i * x i - Pinf P x α i - P.c * testProb P α i

/-- Definition 3 restricted to type-symmetric Bernoulli mixtures on `{0,1}`. -/
def IsSymEq (P : Params) (n : ℕ) (γ α : ℝ × ℝ) : Prop :=
  γ ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 ∧
    ∀ (i : Fin n) (xi : ℝ), xi ∈ Set.Icc (0 : ℝ) 1 →
      expUtil P γ α i xi ≤
        stratProb P γ i * expUtil P γ α i 1 +
        (1 - stratProb P γ i) * expUtil P γ α i 0

/-- Infection probability when the agent herself also mixes. -/
noncomputable def eqInf {n : ℕ} (P : Params) (γ α : ℝ × ℝ) (i : Fin n) : ℝ :=
  stratProb P γ i * PinfMix P γ α i 1 +
    (1 - stratProb P γ i) * PinfMix P γ α i 0

noncomputable def prof {n : ℕ} (P : Params) (xH xL : ℝ) : Fin n → ℝ :=
  fun j => if IsHigh P j then xH else xL

def PolicySquare : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1

/-- Product order on policies, in low then high coordinates. -/
def PolicyLe (α α' : ℝ × ℝ) : Prop := α.1 ≤ α'.1 ∧ α.2 ≤ α'.2

/-- Section 3.1's first policy region. -/
def A1 (P : Params) (n : ℕ) : Set (ℝ × ℝ) :=
  {α | α ∈ PolicySquare ∧
    ∀ l h : Fin n, ¬ IsHigh P l → IsHigh P h →
      Pinf P (prof P 1 1) α l ≤ P.vL + (1 : ℝ) / n ∧
      Pinf P (prof P 1 1) α h ≤ P.vH + (1 : ℝ) / n}

/-- Section 3.1's low-type mixing region. -/
def A2 (P : Params) (n : ℕ) : Set (ℝ × ℝ) :=
  {α | α ∈ PolicySquare ∧
    ∀ l h : Fin n, ¬ IsHigh P l → IsHigh P h →
      P.vL + (1 : ℝ) / n ≤ Pinf P (prof P 1 1) α l ∧
      Pinf P (Function.update (prof P 1 0) l 1) α l ≤ P.vL + (1 : ℝ) / n ∧
      Pinf P (prof P 1 0) α h ≤ P.vH + (1 : ℝ) / n}

/-- Section 3.1's pure region with high agents active and low agents inactive. -/
def A3 (P : Params) (n : ℕ) : Set (ℝ × ℝ) :=
  {α | α ∈ PolicySquare ∧
    ∀ l h : Fin n, ¬ IsHigh P l → IsHigh P h →
      P.vL + (1 : ℝ) / n ≤ Pinf P (prof P 1 1) α l ∧
      P.vL + (1 : ℝ) / n ≤ Pinf P (Function.update (prof P 1 0) l 1) α l ∧
      Pinf P (prof P 1 0) α h ≤ P.vH + (1 : ℝ) / n}

/-- Section 3.1's high-type mixing region. -/
def A4 (P : Params) (n : ℕ) : Set (ℝ × ℝ) :=
  {α | α ∈ PolicySquare ∧
    ∀ l h : Fin n, ¬ IsHigh P l → IsHigh P h →
      P.vL + (1 : ℝ) / n ≤ Pinf P (prof P 1 1) α l ∧
      P.vH + (1 : ℝ) / n ≤ Pinf P (prof P 1 0) α h}

end TestDistancing.Equilibrium


