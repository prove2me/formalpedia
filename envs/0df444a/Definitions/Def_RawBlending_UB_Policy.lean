-- Prove2me | Definitions.Def_RawBlending_UB_Policy
-- name    : RawBlending_UB_Policy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T04:18:20.394164+00:00
-- url     : https://prove2.me/theorems/a930858b-94a8-4223-bb40-55f72c3af187
-- title:
--   Definition 1: use-down-to and balancing production policy
-- statement:
--   For demand $D$, capacity $R$, and $j\in\{1,2\}$, let $K^j=\min\{R,D/a^j\}$ and let $L^1,L^2$ be the piecewise production limits on page 12. Four curves $\gamma^1,\gamma^2,\alpha,\beta$ meet at $\bar w$. Definition 1 uses these curves and the shifted functions $\bar\gamma^j$ to form regions $\mathcal R_0,\ldots,\mathcal R_5$ and choose a remaining-inventory vector $w^*$ by the use-down-to or balancing rule.
--
--   $$
--    w^*(y)=\begin{cases}(y^1\wedge(\gamma^1(y^2)\vee\bar w^1),\ y^2\wedge(\gamma^2(y^1)\vee\bar w^2)),&y\in\mathcal R_0,\\
--    (y^1,y^2-K^2),&y\in\mathcal R_1,\\
--    \alpha(a^1y^1+a^2y^2-D),&y\in\mathcal R_2,\\
--    (y^1-L^1,y^2-L^2),&y\in\mathcal R_3,\\
--    \beta(y^1+y^2-R),&y\in\mathcal R_4,\\
--    (y^1-K^1,y^2),&y\in\mathcal R_5.
--    \end{cases}
--   $$
--   The `IsUBCurves` property also records the curve minimizers in equations (11)–(14). These definitions are the target policy whose feasibility and optimality the mission asks solvers to prove.
--
--   **Formalization Note** Region membership uses every strict and weak inequality in Definition 1. When regions overlap at low demand, `ubAction` applies the first matching rule in the displayed order. The second branch of each $\bar\gamma^j$ formula is outside its stated domain when its denominator $L^{3-j}$ vanishes.
-- source:
--   Chen, Duenyas & Jasin, Optimal use and replenishment of two substitutable raw materials, SSRN working paper 2801786 (version of 2016-06-28), §4.1, pp. 12–15 (PDF 12–15), Definition 1 and equations (8)–(9)

import Mathlib
import Definitions.Def_RawBlending_UB_Model

noncomputable section

namespace RawBlending.UB

def K1 (a1 a2 D R : ℝ) : ℝ := min R (D / a1)
def K2 (a1 a2 D R : ℝ) : ℝ := min R (D / a2)

def L1 (a1 a2 D R : ℝ) : ℝ :=
  if D ≤ a1 * R then K1 a1 a2 D R
  else if D < a2 * R then (a2 * R - D) / (a2 - a1) else 0
def L2 (a1 a2 D R : ℝ) : ℝ :=
  if D ≤ a1 * R then 0
  else if D < a2 * R then (D - a1 * R) / (a2 - a1) else K2 a1 a2 D R

structure Curves where
  γ1 : ℝ → ℝ
  γ2 : ℝ → ℝ
  α : ℝ → Vec
  β : ℝ → Vec
  wbar : Vec

def γbar1 (C : Curves) (a1 a2 D R y2 : ℝ) : ℝ :=
  if y2 ≤ C.wbar.2 then C.γ1 y2 + K1 a1 a2 D R
  else C.wbar.1 + K1 a1 a2 D R +
    (y2 - C.wbar.2) * (L1 a1 a2 D R - K1 a1 a2 D R) / L2 a1 a2 D R
def γbar2 (C : Curves) (a1 a2 D R y1 : ℝ) : ℝ :=
  if y1 ≤ C.wbar.1 then C.γ2 y1 + K2 a1 a2 D R
  else C.wbar.2 + K2 a1 a2 D R +
    (y1 - C.wbar.1) * (L2 a1 a2 D R - K2 a1 a2 D R) / L1 a1 a2 D R

def exceedsDemand (C : Curves) (a1 a2 D : ℝ) (y : Vec) : Prop :=
  a1 * C.wbar.1 + a2 * C.wbar.2 + D < a1 * y.1 + a2 * y.2
def exceedsCapacity (C : Curves) (R : ℝ) (y : Vec) : Prop :=
  C.wbar.1 + C.wbar.2 + R < y.1 + y.2

def R0 (C : Curves) (a1 a2 D R : ℝ) : Set Vec :=
  {y | y ∈ orthant ∧
    (y.1 ≤ C.wbar.1 + L1 a1 a2 D R ∨ y.2 ≤ C.wbar.2 + L2 a1 a2 D R) ∧
    (y.2 ≤ C.wbar.2 + L2 a1 a2 D R → y.1 ≤ γbar1 C a1 a2 D R y.2) ∧
    (y.1 ≤ C.wbar.1 + L1 a1 a2 D R → y.2 ≤ γbar2 C a1 a2 D R y.1)}

def R1a (C : Curves) (a1 a2 D R : ℝ) : Set Vec :=
  {y | y ∈ orthant ∧ y ∉ R0 C a1 a2 D R ∧
    y.1 ≤ (C.α (a1 * y.1 + a2 * y.2 - D)).1 ∧ exceedsDemand C a1 a2 D y}
def R1b (C : Curves) (a1 a2 D R : ℝ) : Set Vec :=
  {y | y ∈ orthant ∧ y ∉ R0 C a1 a2 D R ∧
    y.1 < C.wbar.1 ∧ ¬ exceedsDemand C a1 a2 D y ∧
    ¬ exceedsCapacity C R y ∧ γbar2 C a1 a2 D R y.1 < y.2}
def R2 (C : Curves) (a1 a2 D R : ℝ) : Set Vec :=
  {y | y ∈ orthant ∧ y ∉ R0 C a1 a2 D R ∧
    (C.α (a1 * y.1 + a2 * y.2 - D)).1 < y.1 ∧
    y.1 < (C.α (a1 * y.1 + a2 * y.2 - D)).1 + L1 a1 a2 D R ∧
    exceedsDemand C a1 a2 D y}
def R3a (C : Curves) (a1 a2 D R : ℝ) : Set Vec :=
  {y | y ∈ orthant ∧ y ∉ R0 C a1 a2 D R ∧
    exceedsDemand C a1 a2 D y ∧ ¬ exceedsCapacity C R y ∧
    (C.α (a1 * y.1 + a2 * y.2 - D)).1 + L1 a1 a2 D R ≤ y.1}
def R3b (C : Curves) (a1 a2 D R : ℝ) : Set Vec :=
  {y | y ∈ orthant ∧ y ∉ R0 C a1 a2 D R ∧
    ¬ exceedsDemand C a1 a2 D y ∧ exceedsCapacity C R y ∧
    y.1 ≤ (C.β (y.1 + y.2 - R)).1 + L1 a1 a2 D R}
def R3c (C : Curves) (a1 a2 D R : ℝ) : Set Vec :=
  {y | y ∈ orthant ∧ y ∉ R0 C a1 a2 D R ∧
    exceedsDemand C a1 a2 D y ∧ exceedsCapacity C R y ∧
    (C.α (a1 * y.1 + a2 * y.2 - D)).1 + L1 a1 a2 D R ≤ y.1 ∧
    y.1 ≤ (C.β (y.1 + y.2 - R)).1 + L1 a1 a2 D R}
def R4 (C : Curves) (a1 a2 D R : ℝ) : Set Vec :=
  {y | y ∈ orthant ∧ y ∉ R0 C a1 a2 D R ∧
    (C.β (y.1 + y.2 - R)).1 + L1 a1 a2 D R < y.1 ∧
    y.1 < (C.β (y.1 + y.2 - R)).1 + K1 a1 a2 D R ∧
    exceedsCapacity C R y}
def R5a (C : Curves) (a1 a2 D R : ℝ) : Set Vec :=
  {y | y ∈ orthant ∧ y ∉ R0 C a1 a2 D R ∧
    (C.β (y.1 + y.2 - R)).1 + K1 a1 a2 D R ≤ y.1 ∧ exceedsCapacity C R y}
def R5b (C : Curves) (a1 a2 D R : ℝ) : Set Vec :=
  {y | y ∈ orthant ∧ y ∉ R0 C a1 a2 D R ∧
    y.2 < C.wbar.2 ∧ ¬ exceedsCapacity C R y ∧
    ¬ exceedsDemand C a1 a2 D y ∧ γbar1 C a1 a2 D R y.2 < y.1}

def R1 (C : Curves) (a1 a2 D R : ℝ) : Set Vec :=
  R1a C a1 a2 D R ∪ R1b C a1 a2 D R
def R3 (C : Curves) (a1 a2 D R : ℝ) : Set Vec :=
  R3a C a1 a2 D R ∪ R3b C a1 a2 D R ∪ R3c C a1 a2 D R
def R5 (C : Curves) (a1 a2 D R : ℝ) : Set Vec :=
  R5a C a1 a2 D R ∪ R5b C a1 a2 D R

def region (C : Curves) (a1 a2 D R : ℝ) : Fin 6 → Set Vec
  | ⟨0, _⟩ => R0 C a1 a2 D R
  | ⟨1, _⟩ => R1 C a1 a2 D R
  | ⟨2, _⟩ => R2 C a1 a2 D R
  | ⟨3, _⟩ => R3 C a1 a2 D R
  | ⟨4, _⟩ => R4 C a1 a2 D R
  | ⟨5, _⟩ => R5 C a1 a2 D R

def RegionsCover (C : Curves) (a1 a2 D R : ℝ) : Prop :=
  ∀ y ∈ orthant, ∃ i : Fin 6, y ∈ region C a1 a2 D R i

def RegionsDisjoint (C : Curves) (a1 a2 D R : ℝ) : Prop :=
  ∀ i j : Fin 6, i ≠ j → Disjoint (region C a1 a2 D R i) (region C a1 a2 D R j)

def ubAction (C : Curves) (a1 a2 D R : ℝ) (y : Vec) : Vec := by
  classical
  exact
    if y ∈ R0 C a1 a2 D R then
      (min y.1 (max (C.γ1 y.2) C.wbar.1), min y.2 (max (C.γ2 y.1) C.wbar.2))
    else if y ∈ R1 C a1 a2 D R then (y.1, y.2 - K2 a1 a2 D R)
    else if y ∈ R2 C a1 a2 D R then C.α (a1 * y.1 + a2 * y.2 - D)
    else if y ∈ R3 C a1 a2 D R then (y.1 - L1 a1 a2 D R, y.2 - L2 a1 a2 D R)
    else if y ∈ R4 C a1 a2 D R then C.β (y.1 + y.2 - R)
    else (y.1 - K1 a1 a2 D R, y.2)

def ScalarMinimizes (f : ℝ → ℝ) (S : Set ℝ) (x : ℝ) : Prop :=
  x ∈ S ∧ ∀ y ∈ S, f x ≤ f y

def IsUBCurves (Jobj : Vec → ℝ) (a1 a2 : ℝ) (C : Curves) : Prop :=
  C.wbar ∈ orthant ∧
  (∀ x y : ℝ, 0 ≤ x → x ≤ y → C.γ1 y ≤ C.γ1 x ∧ C.γ2 y ≤ C.γ2 x) ∧
  (∀ s : ℝ, 0 ≤ s → 0 ≤ C.γ1 s ∧ 0 ≤ C.γ2 s ∧
    C.α s ∈ orthant ∧ C.β s ∈ orthant) ∧
  C.γ1 C.wbar.2 = C.wbar.1 ∧ C.γ2 C.wbar.1 = C.wbar.2 ∧
  C.α (a1 * C.wbar.1 + a2 * C.wbar.2) = C.wbar ∧
  C.β (C.wbar.1 + C.wbar.2) = C.wbar ∧
  Minimizes Jobj orthant C.wbar ∧
  (∀ s : ℝ, 0 ≤ s → ScalarMinimizes (fun u => Jobj (u, s)) (Set.Ici 0) (C.γ1 s)) ∧
  (∀ s : ℝ, 0 ≤ s → ScalarMinimizes (fun u => Jobj (s, u)) (Set.Ici 0) (C.γ2 s)) ∧
  (∀ x : ℝ, 0 ≤ x → Minimizes Jobj
    {w : Vec | w ∈ orthant ∧ a1 * w.1 + a2 * w.2 = x} (C.α x)) ∧
  (∀ x : ℝ, 0 ≤ x → Minimizes Jobj
    {w : Vec | w ∈ orthant ∧ w.1 + w.2 = x} (C.β x))

/-- The strictly convex perturbation of J, indexed by positive n. -/
def Jn (Jobj : Vec → ℝ) (n : ℕ) (w : Vec) : ℝ :=
  Jobj w + (1 / (n : ℝ)) * (w.1 ^ 2 + w.2 ^ 2)

end RawBlending.UB


