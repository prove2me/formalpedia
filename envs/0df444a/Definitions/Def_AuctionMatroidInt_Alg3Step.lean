-- Prove2me | Definitions.Def_AuctionMatroidInt_Alg3Step
-- name    : AuctionMatroidInt_Alg3Step
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:27:29.222278+00:00
-- url     : https://prove2.me/theorems/c87d5a58-406b-4ba8-b85d-2349f81b7dd8
-- title:
--   Algorithm 3: state and one iteration of the inner for-loop (Lines 6–14)
-- statement:
--   Algorithm 3 runs in rounds. In a round, $X^*$ and $\pi^*$ are the set and prices at the beginning of the round (frozen during the round), and $q^*$ is the utility vector they induce; the round maintains a proposal $Y$, the current set $X$ and the prices $\pi$. One iteration of the inner loop scans an element $e\in E\setminus X^*$:
--
--   1. **Condition (Line 6):** $q(e)=q^*(e)>0$, where $q$ is induced by the current $(X,\pi)$, and $Y+e$ is contained in a $q^*$-maximum base of $M_1$.
--   2. **Execution (Lines 7–14), if the condition holds:** $Y\leftarrow Y+e$; $\pi(e)\leftarrow p(e)$, with $p(e)$ computed from the current $(X,\pi)$; if $X+e\in\mathcal I_2$ then $X\leftarrow X+e$, otherwise an element $f\in C_2(X\mid e)-e$ minimizing $\pi(f)$ is chosen and $X\leftarrow X+e-f$, $\pi(f)\leftarrow\bot$.
--   3. If the condition fails, nothing changes.
--
--   **Formalization Note** `Alg3State` holds $(Y,X,\pi)$; `Alg3Cond`, `Alg3Exec` and `Alg3Step` are relations, so the tie-break in Line 12 is free (any minimizer). The price of Line 8 is computed before the update. Line 14 needs no update since $\pi$ is never read off $X$.
-- source:
--   Huang, Kobayashi, Terao, Auction-Based Algorithms for Weighted Matroid Intersection with Near-Linear Query Complexity (manuscript, sha256 2e12cb4a…), Algorithm 3, Lines 6–14, p.22, and §5.1.2, p.21 (PDF pp.23–24)

import Mathlib
import Definitions.Def_AuctionMatroidInt_IsMaxBase
import Definitions.Def_AuctionMatroidInt_utility

namespace AuctionMatroidInt

/-- **The mutable state of Algorithm 3 inside a round**: the proposal `Y`, the current common
independent set `X`, and the prices `π`.
Huang, Kobayashi, Terao (manuscript, sha256 2e12cb4a…), Algorithm 3, p.22.

**Formalization Note.** `π : α → ℝ` is read only on `X`; the paper's `π(e) = ⊥` for `e ∉ X`
(and Line 14, `π(f) ← ⊥`) is modelled by never reading `π` off `X`, so a stale value `π f` after
`f` leaves `X` has no effect. -/
structure Alg3State (α : Type*) where
  /-- The proposal `Y` built during the round. -/
  Y : Finset α
  /-- The current set `X`. -/
  X : Finset α
  /-- The current prices `π` (read only on `X`). -/
  π : α → ℝ

/-- **The condition of Line 6 of Algorithm 3** for the scanned element `e`, with `(X*, π*)` the
set and prices frozen at the beginning of the round (p.21–22): "if q(e) = q*(e) > 0 and Y + e is
contained in a q*-maximum base of M₁". Here `q` is the utility induced by the current `(X, π)`
and `q*` the one induced by `(X*, π*)`. -/
def Alg3Cond {α : Type*} [Fintype α] [DecidableEq α] (ε : ℝ) (w : α → ℝ)
    (I₁ I₂ : Finset α → Prop) (Xs : Finset α) (πs : α → ℝ) (s : Alg3State α) (e : α) : Prop :=
  utility ε w I₂ s.X s.π e = utility ε w I₂ Xs πs e ∧ 0 < utility ε w I₂ Xs πs e ∧
    ∃ B : Finset α, IsMaxBase I₁ (utility ε w I₂ Xs πs) B ∧ insert e s.Y ⊆ B

open Classical in
/-- **Lines 7–14 of Algorithm 3** executed for the scanned element `e`, from state `s` to `s'`
(p.22): `Y ← Y + e`; `π(e) ← p(e)`; if `X + e ∈ I₂` then `X ← X + e`, else find
`f ∈ C₂(X | e) − e` minimizing `π(f)`, `X ← X + e − f`, `π(f) ← ⊥`.

**Formalization Note.** The price `p(e)` of Line 8 is computed from the state *before* the
update (`price ε w I₂ s.X s.π e`). The tie-break in Line 12 is free: **any** minimizer `f` is
allowed. `C₂(X | e) − e` is `fundCircuitErase I₂ s.X e` (Observation 2.1). Line 14 needs no
update since `π` is never read off `X`. -/
def Alg3Exec {α : Type*} [DecidableEq α] (ε : ℝ) (w : α → ℝ) (I₂ : Finset α → Prop)
    (e : α) (s s' : Alg3State α) : Prop :=
  s'.Y = insert e s.Y ∧
  s'.π = Function.update s.π e (price ε w I₂ s.X s.π e) ∧
  (if I₂ (insert e s.X) then s'.X = insert e s.X
   else ∃ f ∈ fundCircuitErase I₂ s.X e,
      (∀ g ∈ fundCircuitErase I₂ s.X e, s.π f ≤ s.π g) ∧ s'.X = (insert e s.X).erase f)

/-- **One iteration of the inner for-loop of Algorithm 3** (Lines 6–14, p.22) for the scanned
element `e`: if the condition of Line 6 holds, Lines 7–14 are executed; otherwise nothing
changes. `(Xs, πs)` are `(X*, π*)`, frozen at the beginning of the round. -/
def Alg3Step {α : Type*} [Fintype α] [DecidableEq α] (ε : ℝ) (w : α → ℝ)
    (I₁ I₂ : Finset α → Prop) (Xs : Finset α) (πs : α → ℝ) (e : α) (s s' : Alg3State α) :
    Prop :=
  (Alg3Cond ε w I₁ I₂ Xs πs s e ∧ Alg3Exec ε w I₂ e s s') ∨
    (¬ Alg3Cond ε w I₁ I₂ Xs πs s e ∧ s' = s)

end AuctionMatroidInt


