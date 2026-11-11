-- Prove2me | Definitions.Def_HarmonicRanking_Main_Scan
-- name    : HarmonicRanking_Main_Scan
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:32:15.27258+00:00
-- url     : https://prove2.me/theorems/aac6cef8-9489-47ff-82ca-9405692e9407
-- title:
--   Operational scan, admissible orders, matching times, and credits
-- statement:
--   A total scan order is a permutation list of all potential pairs. Given a realized edge set $E$, the generic scan visits that list and accepts a pair exactly when it belongs to $E$ and neither endpoint is already matched. It is also defined on every finite prefix and on the realization obtained by deleting one right vertex.
--
--   For ranks $\rho$, score $h$, and fixed potential weights $w$, an admissible order rule $\tau$ sorts by
--
--   $$
--   \pi_{uv}=w_{uv}\frac{h(\rho_u)h(\rho_v)}{h(\rho_u)+h(\rho_v)}.
--   $$
--
--   Its scan positions are completion-measurable in the product rank law. Lowering any one rank preserves every relative order between nonincident pairs and preserves every precedence of an incident pair over a nonincident pair. This retains all source measurable rules and also allows a.e. measurable positions, while keeping the rank-perturbation property pointwise.
--
--   The selected matching determines $\operatorname{ALG}$ and its product-measure expectation. A matched vertex's matching time is the scan index of its selected edge; an unmatched vertex has time $+\infty$. Earlier means strict comparison of these times. For a selected pair $uv$, the credit to $u$ is $g_h(\rho_u,\rho_v)w_{uv}$ and the credit to $v$ is $g_h(\rho_v,\rho_u)w_{uv}$; unmatched credits are zero. These are computed outputs of the scan, without approximation assumptions.
-- source:
--   Bo Peng, Zhihao Gavin Tang, Harmonic Ranking for Edge-Weighted Oblivious Matching, STOC 2027 submission #176 (October 2026), pp. 2, 5, 8–10, algorithm (1), §2.4, Eqs. (6)–(7)

import Definitions.Def_HarmonicRanking_Main_Instance

open MeasureTheory
set_option autoImplicit false
noncomputable section

namespace HarmonicRanking.Main

/-- A total order represented as a permutation list, independent of realization. -/
structure ScanOrder (L R : Type*) where
  edges : List (L × R)
  nodup : edges.Nodup
  complete : ∀ e, e ∈ edges

variable {L R : Type*} [Fintype L] [Fintype R]

def incident (e : L × R) (z : L ⊕ R) : Prop :=
  z = Sum.inl e.1 ∨ z = Sum.inr e.2

/-- Generic query-commit scan: failed probes and occupied pairs change no state. -/
def greedy (E : Finset (L × R)) (order : List (L × R)) : Finset (L × R) := by
  classical
  exact order.foldl (fun M e =>
    if e ∈ E ∧ (∀ f ∈ M, f.1 ≠ e.1 ∧ f.2 ≠ e.2) then insert e M else M) ∅

/-- Deleting a right vertex is implemented by skipping its incident edges. -/
def withoutRight (E : Finset (L × R)) (v : R) : Finset (L × R) := by
  classical
  exact E.filter (fun e => e.2 ≠ v)

def priority (h : ℝ → ℝ) (w : L × R → NNReal) (r : Ranks L R) (e : L × R) : ℝ :=
  (w e : ℝ) * h (r (Sum.inl e.1)) * h (r (Sum.inr e.2)) /
    (h (r (Sum.inl e.1)) + h (r (Sum.inr e.2)))

/-- A rule receives ranks only, with the potential weights fixed in admissibility. -/
abbrev TieRule (L R : Type*) := Ranks L R → ScanOrder L R

def position (o : ScanOrder L R) (e : L × R) : ℕ := by
  classical
  exact o.edges.idxOf e

/-- Section 2.4: measurable total priority order and every one-coordinate decrease. -/
def Admissible (h : ℝ → ℝ) (w : L × R → NNReal) (τ : TieRule L R) : Prop := by
  classical
  exact (∀ e, AEMeasurable (fun r => position (τ r) e) (ranksLaw L R)) ∧
  (∀ r e f, position (τ r) e < position (τ r) f →
    priority h w r f ≤ priority h w r e) ∧
  ∀ (r : Ranks L R) (z : L ⊕ R) (t : Rank), t ≤ r z →
    let r' := Function.update r z t
    (∀ e f, ¬ incident e z → ¬ incident f z →
      (position (τ r') e < position (τ r') f ↔
       position (τ r) e < position (τ r) f)) ∧
    (∀ e f, incident e z → ¬ incident f z →
      position (τ r) e < position (τ r) f →
      position (τ r') e < position (τ r') f)

def selected (G : Instance L R) (τ : TieRule L R) (r : Ranks L R) : Finset (L × R) :=
  greedy G.realized (τ r).edges

def ALG (G : Instance L R) (τ : TieRule L R) (r : Ranks L R) : ℝ :=
  matchingWeight G (selected G τ r)

def expectedALG (G : Instance L R) (τ : TieRule L R) : ℝ :=
  ∫ r, ALG G τ r ∂ranksLaw L R

/-- Unmatched vertices have time top; a matched vertex has its selecting scan index. -/
def matchTime (E : Finset (L × R)) (o : ScanOrder L R) (z : L ⊕ R) : WithTop ℕ := by
  classical
  exact (greedy E o.edges).inf (fun e =>
    if incident e z then (position o e : WithTop ℕ) else ⊤)

def earlier (G : Instance L R) (τ : TieRule L R) (r : Ranks L R)
    (z z' : L ⊕ R) : Prop :=
  matchTime G.realized (τ r) z < matchTime G.realized (τ r) z'

/-- The other endpoint's score supplies the endpoint credit in (6). -/
def credit (h : ℝ → ℝ) (G : Instance L R) (τ : TieRule L R)
    (r : Ranks L R) (z : L ⊕ R) : ℝ := by
  classical
  exact ∑ e ∈ selected G τ r,
    if z = Sum.inl e.1 then gain h (r z) (r (Sum.inr e.2)) * (G.weight e : ℝ)
    else if z = Sum.inr e.2 then gain h (r z) (r (Sum.inl e.1)) * (G.weight e : ℝ)
    else 0

end HarmonicRanking.Main


