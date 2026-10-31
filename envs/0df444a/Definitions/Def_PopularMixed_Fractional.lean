-- Prove2me | Definitions.Def_PopularMixed_Fractional
-- name    : PopularMixed_Fractional
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:54:21.623992+00:00
-- url     : https://prove2.me/theorems/d4092a59-a9eb-4bf9-bc2b-87c3762f7669
-- title:
--   Fractional matchings $\mathcal M_G$, votes, $\Delta(\vec x,M)$, the popular fractional matching polytope $\mathcal P_G$ and the extended polytope $\mathcal P'_G$
-- statement:
--   Each vertex $u$ of $G$ gets a **last resort** $\ell(u)$ ranked below all its neighbours, and $\tilde E=E\cup\{(u,\ell(u)):u\in A\cup B\}$. The **matching polytope** is
--   $$\mathcal M_G=\Big\{\vec x\in\mathbb R^{\tilde E}_{\ge0}:\ \sum_{e\in\tilde E(u)}x_e=1\ \ \forall u\in A\cup B\Big\},$$
--   so $x(u,\ell(u))=1-\sum_{v}x(u,v)$. For $v'\in\mathrm{Nbr}(u)\cup\{\ell(u)\}$,
--   $$\mathrm{vote}_u(\vec x,v')=\sum_{v\succ_u v'}x(u,v)-\sum_{v\prec_u v'}x(u,v),$$
--   where $\ell(u)$ belongs to the second set when $v'\neq\ell(u)$, and $\mathrm{vote}_u(v',\vec x)=-\mathrm{vote}_u(\vec x,v')$. For a matching $M$, $\Delta(\vec x,M)=\sum_{u\in A\cup B}\mathrm{vote}_u(\vec x,M(u))$ with $M(u)=\ell(u)$ for an unmatched $u$.
--
--   1. (2.1) The **popular fractional matching polytope** is $\mathcal P_G=\{\vec x\in\mathcal M_G:\Delta(\vec x,M)\ge0\ \text{for all matchings }M\}$.
--   2. The edge weight is $\mathrm{wt}_x(a,b)=\mathrm{vote}_a(b,\vec x)+\mathrm{vote}_b(a,\vec x)$.
--   3. The **extended polytope** $\mathcal P'_G$ is the set of $(\vec x,\vec\alpha)$, $\vec\alpha\in\mathbb R^{A\cup B}$, with
--   $$\sum_{u}\alpha_u=0,\quad \alpha_a+\alpha_b\ge\mathrm{wt}_x(a,b)\ \forall (a,b)\in E,\quad \alpha_u\ge\mathrm{vote}_u(\ell(u),\vec x)=-\!\!\sum_{v\in\mathrm{Nbr}(u)}\!x(u,v)\ \forall u,\quad \vec x\in\mathcal M_G.$$
--   4. A **half-integral** vector has all coordinates in $\{0,\tfrac12,1\}$; $I_M$ is the incidence vector of $M$, and $x_\Lambda=\sum_M\Lambda(M)\,I_M$ is the fractional matching of a mixed matching $\Lambda$.
--
--   These are the polytopes whose integrality (Theorem 3.1) and half-integrality (Theorem 4.1) the paper proves.
--
--   **Formalization Note** A fractional matching is `x : A → B → ℝ` on genuine edges ($x\ge0$, $x=0$ off $E$, $\sum_v x(u,v)\le1$); the last-resort coordinate is the derived value `lrA x a = 1 − Σ_b x a b` (resp. `lrB`), so `InMG` is exactly $\mathcal M_G$. In `voteA x a o`, `o = none` stands for $\ell(a)$. $\Delta(\vec x,M)$ is computed with `voteAM`, which reads $M(a)$ off $M$ (and $\ell(a)$ if $a$ is unmatched). Witnesses are `α : A ⊕ B → ℝ`.
-- source:
--   Huang–Kavitha, Popularity, Mixed Matchings, and Self-duality, conference version (SODA 2017), Section 2, PDF p.4 (M_G, last resorts, vote_u, Δ(x,M), (2.1)) and PDF p.5 (wt_x, the description of P′_G after LP2); half-integral matchings: Section 1, PDF p.3.

import Mathlib
import Definitions.Def_PopularMixed_Model

namespace PopularMixed

/-!
Huang–Kavitha, *Popularity, Mixed Matchings, and Self-duality*, conference version (SODA 2017),
Section 2, PDF pp.4–5, and Section 1, PDF pp.2–3: fractional matchings with last resorts, the
votes `vote_u`, `Δ(x, M)`, the popular fractional matching polytope `P_G` of (2.1), the edge
weights `wt_x`, the extended polytope `P′_G`, half-integral matchings, and the fractional
matching of a mixed matching.

**Formalization Note.**
* A fractional matching is a vector `x : A → B → ℝ` over the genuine edges: `x ≥ 0`, `x = 0` off
  `E`, and `Σ_b x(a,b) ≤ 1`, `Σ_a x(a,b) ≤ 1`. The last-resort coordinate `x(u, ℓ(u))` of the
  paper (PDF p.4) is not a separate variable: it is `1 − Σ_v x(u,v)` (`lrA`, `lrB`), and the
  constraint `x(u, ℓ(u)) ≥ 0` is the `≤ 1` constraint. So `InMG` is exactly the paper's `M_G`.
* The last resort `ℓ(u)` is ranked below every neighbour of `u`; a vertex left unmatched by a
  matching `M` is assigned `ℓ(u)`, and as on PDF p.4 the "worse" set `{v : v ≺_u v′}` contains
  `ℓ(u)` whenever `v′ ≠ ℓ(u)`. In `voteA x a o`, the option `o = none` stands for `ℓ(a)`.
* A witness `α` is a function on `A ⊕ B` (`inl a` = applicant `a`, `inr b` = job `b`).
-/

open Finset

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- The 0-1 edge incidence vector `I_M` of `M` (PDF p.5). -/
def incid (M : Finset (A × B)) : A → B → ℝ :=
  fun a b => if (a, b) ∈ M then 1 else 0

/-- The last-resort coordinate `x(a, ℓ(a)) = 1 − Σ_b x(a,b)` of applicant `a` (PDF p.4). -/
def lrA (x : A → B → ℝ) (a : A) : ℝ := 1 - ∑ b, x a b

/-- The last-resort coordinate `x(b, ℓ(b)) = 1 − Σ_a x(a,b)` of job `b` (PDF p.4). -/
def lrB (x : A → B → ℝ) (b : B) : ℝ := 1 - ∑ a, x a b

/-- The mixed matching `Λ` viewed as a fractional matching: `x_Λ = Σ_M Λ(M) · I_M`
(PDF p.2, p.4: "in a bipartite graph, a fractional matching is equivalent to a mixed matching"). -/
noncomputable def mixedToFrac (Λ : Finset (A × B) → ℝ) : A → B → ℝ :=
  fun a b => ∑ M, Λ M * incid M a b

/-- A half-integral vector (PDF p.3): every coordinate is in `{0, 1/2, 1}`. -/
def IsHalfIntegral (x : A → B → ℝ) : Prop :=
  ∀ a b, x a b = 0 ∨ x a b = 1 / 2 ∨ x a b = 1

namespace Instance

variable (G : Instance A B)

/-- The matching polytope `M_G` of `G` with last resorts (PDF p.4), i.e. the fractional
matchings of `G` (PDF p.2): `x ≥ 0`, `x` vanishes off `E`, and every vertex has total weight at
most `1` on genuine edges (its last-resort coordinate `1 − Σ` is then `≥ 0`). -/
def InMG (x : A → B → ℝ) : Prop :=
  (∀ a b, 0 ≤ x a b) ∧ (∀ a b, (a, b) ∉ G.E → x a b = 0) ∧
    (∀ a, ∑ b, x a b ≤ 1) ∧ ∀ b, ∑ a, x a b ≤ 1

/-- `vote_a(x, v′)` for applicant `a` (PDF p.4): `Σ_{v ≻_a v′} x(a,v) − Σ_{v ≺_a v′} x(a,v)`.
For a genuine neighbour `v′ = b` (`some b`) the worse set contains the last resort `ℓ(a)`; for
`v′ = ℓ(a)` (`none`) every neighbour is better and nothing is worse. -/
def voteA (x : A → B → ℝ) (a : A) : Option B → ℝ
  | some b =>
      (∑ b' ∈ univ.filter (fun b' => (a, b') ∈ G.E ∧ G.rankA a b' < G.rankA a b), x a b') -
        (∑ b' ∈ univ.filter (fun b' => (a, b') ∈ G.E ∧ G.rankA a b < G.rankA a b'), x a b') -
          lrA x a
  | none => ∑ b' ∈ univ.filter (fun b' => (a, b') ∈ G.E), x a b'

/-- `vote_b(x, v′)` for job `b` (PDF p.4), as `voteA`; `none` stands for `ℓ(b)`. -/
def voteB (x : A → B → ℝ) (b : B) : Option A → ℝ
  | some a =>
      (∑ a' ∈ univ.filter (fun a' => (a', b) ∈ G.E ∧ G.rankB b a' < G.rankB b a), x a' b) -
        (∑ a' ∈ univ.filter (fun a' => (a', b) ∈ G.E ∧ G.rankB b a < G.rankB b a'), x a' b) -
          lrB x b
  | none => ∑ a' ∈ univ.filter (fun a' => (a', b) ∈ G.E), x a' b

/-- `vote_a(x, M(a))` (PDF p.4): `M(a)` is `a`'s partner in the matching `M`, or `ℓ(a)` if `a` is
unmatched in `M`. (For a matching the first sum has at most one term.) -/
def voteAM (x : A → B → ℝ) (a : A) (M : Finset (A × B)) : ℝ :=
  (∑ b ∈ univ.filter (fun b => (a, b) ∈ M), G.voteA x a (some b)) +
    if ∀ b, (a, b) ∉ M then G.voteA x a none else 0

/-- `vote_b(x, M(b))` (PDF p.4), as `voteAM`. -/
def voteBM (x : A → B → ℝ) (b : B) (M : Finset (A × B)) : ℝ :=
  (∑ a ∈ univ.filter (fun a => (a, b) ∈ M), G.voteB x b (some a)) +
    if ∀ a, (a, b) ∉ M then G.voteB x b none else 0

/-- `Δ(x, M) = Σ_{u ∈ A ∪ B} vote_u(x, M(u))` (PDF p.4). -/
def deltaFrac (x : A → B → ℝ) (M : Finset (A × B)) : ℝ :=
  (∑ a, G.voteAM x a M) + ∑ b, G.voteBM x b M

/-- A popular fractional matching (PDF p.4, (2.1)): `x ∈ M_G` with `Δ(x, M) ≥ 0` for every
matching `M` of `G`. -/
def InPG (x : A → B → ℝ) : Prop :=
  G.InMG x ∧ ∀ M, G.IsMatching M → 0 ≤ G.deltaFrac x M

/-- The popular fractional matching polytope `P_G` (PDF p.4, (2.1)). -/
def PG : Set (A → B → ℝ) := {x | G.InPG x}

/-- The weight `wt_x(a,b) = vote_a(b, x) + vote_b(a, x)` of an edge `(a,b) ∈ E` in `G̃_x`
(PDF p.5), where `vote_u(v, x) = −vote_u(x, v)`. It equals
`Σ_{b′ ≺_a b} x(a,b′) − Σ_{b′ ≻_a b} x(a,b′) + Σ_{a′ ≺_b a} x(a′,b) − Σ_{a′ ≻_b a} x(a′,b)`,
the `≺` sums including the last-resort coordinates. -/
def wt (x : A → B → ℝ) (a : A) (b : B) : ℝ :=
  -G.voteA x a (some b) - G.voteB x b (some a)

/-- The extended popular fractional matching polytope `P′_G` (PDF p.5, the description after
LP2): `(x, α)` with `Σ_u α_u = 0`; the covering constraint `α_a + α_b ≥ vote_a(b,x) + vote_b(a,x)`
for every `(a,b) ∈ E`; the covering constraint `α_u ≥ vote_u(ℓ(u), x) = −Σ_{v ∈ Nbr(u)} x(u,v)`
for every `u ∈ A ∪ B`; and `x ∈ M_G` (`Σ_{e ∈ Ẽ(u)} x_e = 1`, `x_e ≥ 0`). -/
def InP'G (x : A → B → ℝ) (α : A ⊕ B → ℝ) : Prop :=
  G.InMG x ∧ ∑ u, α u = 0 ∧
    (∀ a b, (a, b) ∈ G.E → G.wt x a b ≤ α (Sum.inl a) + α (Sum.inr b)) ∧
    (∀ a, -G.voteA x a none ≤ α (Sum.inl a)) ∧
    ∀ b, -G.voteB x b none ≤ α (Sum.inr b)

end Instance

end PopularMixed


