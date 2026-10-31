-- Prove2me | Definitions.Def_PopularMixed_LP2
-- name    : PopularMixed_LP2
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:54:24.751182+00:00
-- url     : https://prove2.me/theorems/daf14d47-0ed1-4db9-a2a5-41994a4fd6d2
-- title:
--   The linear program LP2 of the extended formulation
-- statement:
--   LP2 is the linear program in the $m+2n$ variables $x_e$ ($e\in\tilde E$) and $\alpha_u$ ($u\in A\cup B$):
--   $$\begin{aligned}\text{minimize}\ &\sum_{u\in A\cup B}\alpha_u\\ \text{s.t.}\ &\alpha_a+\alpha_b\ \ge\ \sum_{b':b'\prec_a b}x(a,b')-\sum_{b':b'\succ_a b}x(a,b')+\sum_{a':a'\prec_b a}x(a',b)-\sum_{a':a'\succ_b a}x(a',b)\quad\forall (a,b)\in E,\\ &\alpha_u\ \ge\ -\sum_{v\in\mathrm{Nbr}(u)}x(u,v)\quad\forall u\in A\cup B,\\ &\sum_{e\in\tilde E(u)}x_e=1\quad\forall u\in A\cup B,\qquad x_e\ge0\quad\forall e\in\tilde E,\end{aligned}$$
--   where the $\prec$ sums include the last-resort edge. Its set of optimal solutions is $\mathcal P'_G$.
--
--   **Formalization Note** LP2 is a `MixedLP` with variables `EdgeT G ⊕ (A ⊕ B)`, where `EdgeT G = E ⊕ (A ⊕ B)` is $\tilde E$ (`inr u` is the last-resort edge $(u,\ell(u))$). The covering rows are indexed by $\tilde E$, the equality rows by $A\cup B$; `coefVA`, `coefVB`, `coefNbr`, `coefInc` are the coefficients of $x_e$ in the displayed sums. The $x$ variables are the sign-constrained ones.
-- source:
--   Huang–Kavitha, Popularity, Mixed Matchings, and Self-duality, conference version (SODA 2017), Section 2, PDF p.5, (LP2).

import Mathlib
import Definitions.Def_PopularMixed_Model
import Definitions.Def_PopularMixed_MixedLP

namespace PopularMixed

/-!
Huang–Kavitha, *Popularity, Mixed Matchings, and Self-duality*, conference version (SODA 2017),
Section 2, PDF p.5: the linear program LP2 in the `m + 2n` variables `x_e` (`e ∈ Ẽ`) and `α_u`
(`u ∈ A ∪ B`), written as a `MixedLP`:

  minimize `Σ_u α_u`
  subject to, for every `(a,b) ∈ E`:
    `α_a + α_b − (Σ_{b′≺_a b} x(a,b′) − Σ_{b′≻_a b} x(a,b′) + Σ_{a′≺_b a} x(a′,b) − Σ_{a′≻_b a} x(a′,b)) ≥ 0`,
  for every `u ∈ A ∪ B`: `α_u + Σ_{v ∈ Nbr(u)} x(u,v) ≥ 0`,
  for every `u ∈ A ∪ B`: `Σ_{e ∈ Ẽ(u)} x_e = 1`, and `x_e ≥ 0` for every `e ∈ Ẽ` (`α` free).

**Formalization Note.** `Ẽ = E ∪ {(u, ℓ(u)) : u ∈ A ∪ B}` is the type `EdgeT G =
E ⊕ (A ⊕ B)`: `inl e` is a genuine edge and `inr u` is the last-resort edge `(u, ℓ(u))`. The
variables are `EdgeT G ⊕ (A ⊕ B)` (`inl e` = `x_e`, `inr u` = `α_u`). The covering rows are
indexed by `EdgeT G` (one per edge of `Ẽ`), the equality rows by `A ⊕ B`. In the `≺` sums the
last resort `ℓ(u)` is below every neighbour (PDF p.4), so `x(a, ℓ(a))` has coefficient `+1` in
the sum `Σ_{b′≺_a b} x(a,b′)`.
-/

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

namespace Instance

variable (G : Instance A B)

/-- `Ẽ`: the genuine edges `E` and one last-resort edge `(u, ℓ(u))` per vertex (PDF p.4). -/
abbrev EdgeT := G.E ⊕ (A ⊕ B)

/-- The coefficient of `x_e` in `vote_a(b, x) = Σ_{b′≺_a b} x(a,b′) − Σ_{b′≻_a b} x(a,b′)`
(the `≺` sum includes `ℓ(a)`). -/
def coefVA (a : A) (b : B) : G.EdgeT → ℝ
  | Sum.inl e =>
      if e.1.1 = a then
        (if G.rankA a b < G.rankA a e.1.2 then 1 else if G.rankA a e.1.2 < G.rankA a b then -1 else 0)
      else 0
  | Sum.inr (Sum.inl a') => if a' = a then 1 else 0
  | Sum.inr (Sum.inr _) => 0

/-- The coefficient of `x_e` in `vote_b(a, x) = Σ_{a′≺_b a} x(a′,b) − Σ_{a′≻_b a} x(a′,b)`
(the `≺` sum includes `ℓ(b)`). -/
def coefVB (a : A) (b : B) : G.EdgeT → ℝ
  | Sum.inl e =>
      if e.1.2 = b then
        (if G.rankB b a < G.rankB b e.1.1 then 1 else if G.rankB b e.1.1 < G.rankB b a then -1 else 0)
      else 0
  | Sum.inr (Sum.inr b') => if b' = b then 1 else 0
  | Sum.inr (Sum.inl _) => 0

/-- The coefficient of `x_e` in `Σ_{v ∈ Nbr(u)} x(u,v)` (genuine edges at `u`). -/
def coefNbr : A ⊕ B → G.EdgeT → ℝ
  | Sum.inl a, Sum.inl e => if e.1.1 = a then 1 else 0
  | Sum.inr b, Sum.inl e => if e.1.2 = b then 1 else 0
  | _, Sum.inr _ => 0

/-- The coefficient of `x_e` in `Σ_{e ∈ Ẽ(u)} x_e`: `1` if `e` is incident on `u`. -/
def coefInc : A ⊕ B → G.EdgeT → ℝ
  | Sum.inl a, Sum.inl e => if e.1.1 = a then 1 else 0
  | Sum.inr b, Sum.inl e => if e.1.2 = b then 1 else 0
  | u, Sum.inr u' => if u' = u then 1 else 0

/-- The linear program LP2 (PDF p.5). -/
def LP2 : MixedLP (G.EdgeT ⊕ (A ⊕ B)) G.EdgeT (A ⊕ B) where
  c := fun k => match k with
    | Sum.inl _ => 0
    | Sum.inr _ => 1
  P := fun i k => match i, k with
    | Sum.inl e, Sum.inr u =>
        (if u = Sum.inl e.1.1 then 1 else 0) + (if u = Sum.inr e.1.2 then 1 else 0)
    | Sum.inl e, Sum.inl f => -(G.coefVA e.1.1 e.1.2 f + G.coefVB e.1.1 e.1.2 f)
    | Sum.inr u, Sum.inr u' => if u' = u then 1 else 0
    | Sum.inr u, Sum.inl f => G.coefNbr u f
  p := fun _ => 0
  Q := fun j k => match k with
    | Sum.inl f => G.coefInc j f
    | Sum.inr _ => 0
  q := fun _ => 1
  nonneg := fun k => match k with
    | Sum.inl _ => True
    | Sum.inr _ => False

end Instance

end PopularMixed


