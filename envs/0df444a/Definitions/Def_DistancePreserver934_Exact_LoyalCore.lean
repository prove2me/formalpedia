-- Prove2me | Definitions.Def_DistancePreserver934_Exact_LoyalCore
-- name    : DistancePreserver934_Exact_LoyalCore
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T08:37:47.8214+00:00
-- url     : https://prove2.me/theorems/07e895d7-4491-4f77-9a80-b30907a6229f
-- title:
--   §5 — standing context, Equations (5)–(6), loyal core, local label counts, good edges
-- statement:
--   **Standing context of §5.** $\mathrm{Ctx}(G,H,R,n,d,l)$ means: $R$ is a demand set of $G$, $H$ is a minimal distance preserver of $(G,R)$, $|V_H|\le n$, $|E_H|\le nd$, and
--   $$\lambda_H(q)\ge l\qquad(q\in R)\tag{4}$$
--   Equation (5) is $6\le r\le\min\{d^2,l\}$ for a real radius $r$.
--
--   **Loyal core.** For a vertex set $V^*$, $\Lambda^*_H=\{\{u,v\}\in\Lambda_H:u,v\in V^*\}$ is the set of private edges with both endpoints in $V^*$ (the loyal edges of $H_L=(V^*,\Lambda^*_H)$), $m=|\Lambda^*_H|$, and $\deg_{H_L}(x)$ is the number of loyal edges at $x$. Equation (6) for $V^*$ means: $V^*\neq\emptyset$ and
--   $$m\ge\frac{nd}{40},\qquad \deg_{H_L}(x)\ge\frac d{40}\quad(x\in V^*).\tag{6}$$
--
--   **Local counts.** $\Lambda^*_H(x,a)$ consists of the loyal edges with at least one endpoint in $B_H(x,a)$, and $\Lambda^*_H(x,a,q)$ of those with $D(e)=\{q\}$; $\lambda^*_H(x,a,q)=|\Lambda^*_H(x,a,q)|$. Here this count is indexed by the label set $D$, so $\lambda^*_H(x,a,D(e))$ is literally the paper's quantity for a loyal edge $e$. Also $n_x=|B_H(x,r)|$.
--
--   **The sum of Lemma 17.**
--   $$Z=\sum_{x\in V^*}\ \sum_{e\in\Lambda^*_H,\ x\in e}\frac{\lambda^*_H(x,r/2,D(e))}{n_x},$$
--   counting incidences $(x,e)$.
--
--   **Good edges.** An edge $e$ satisfies Equation (11) with constant $C$ if $\lambda^*_H(x,r/2,D(e))\le C\,n_x/(d\sqrt r)$ for both endpoints $x$ of $e$.
--
--   All balls, distances and diameters are measured in $H$, never in the core.
-- source:
--   Yanyu Chen, Yu Chen, Zihan Tan, Mingyang Yang, Improved Bounds on Distance Preservers, STOC 2027 submission #934 (October 2026), SHA-256 79b3d23a6e7b7fc6148c7a627181474a0129fb2f4c1d04ccd94c1da7987ed76b, §5 opening (Equation (4)), Equation (5), Lemma 13 and the definitions after it, §5.2 (n_x, Equation (11), Equation (13)), printed p. 13–16 (PDF p. 14–17)

import Mathlib
import Definitions.Def_DistancePreserver934_Exact_Essential

namespace DistancePreserver934.Exact

open Classical

variable {V : Type} [Fintype V]

/-- The standing context of §5 (PDF pp.14–15): `R` is a demand set, `H` is a minimal distance
preserver of `(G, R)` with `|V_H| ≤ n` and `|E_H| ≤ n d`, and every demand has private length at
least `l` (Equation (4)). -/
def Sec5Context (G H : SimpleGraph V) (R : Finset (Sym2 V)) (n : ℕ) (d l : ℝ) : Prop :=
  IsDemandSet G R ∧ IsMinimalPreserver G H R ∧ Fintype.card V ≤ n ∧
    (numEdges H : ℝ) ≤ n * d ∧ ∀ q ∈ R, l ≤ (privLen H R q : ℝ)

/-- Equation (5): `6 ≤ r ≤ min{d², l}`. -/
def Eq5 (d l r : ℝ) : Prop := 6 ≤ r ∧ r ≤ min (d ^ 2) l

/-- `Λ*_H = {{u,v} ∈ Λ_H : u, v ∈ V*}`: the private edges with both endpoints in `V*`
(the loyal edges of the core `H_L = (V*, Λ*_H)`, Lemma 13). -/
noncomputable def coreEdges (H : SimpleGraph V) (R : Finset (Sym2 V)) (Vs : Finset V) :
    Finset (Sym2 V) :=
  (privEdges H R).filter (fun e => ∀ v ∈ e, v ∈ Vs)

/-- `deg_{H_L}(x)`: the number of loyal edges incident to `x`. -/
noncomputable def coreDeg (H : SimpleGraph V) (R : Finset (Sym2 V)) (Vs : Finset V) (x : V) : ℕ :=
  ((coreEdges H R Vs).filter (fun e => x ∈ e)).card

/-- Equation (6) for the core `H_L = (V*, Λ*_H)` with nonempty `V*`:
`m = |Λ*_H| ≥ nd/40` and `deg_{H_L}(x) ≥ d/40` for every `x ∈ V*`. -/
def Eq6 (H : SimpleGraph V) (R : Finset (Sym2 V)) (Vs : Finset V) (n : ℕ) (d : ℝ) : Prop :=
  Vs.Nonempty ∧ (n : ℝ) * d / 40 ≤ ((coreEdges H R Vs).card : ℝ) ∧
    ∀ x ∈ Vs, d / 40 ≤ (coreDeg H R Vs x : ℝ)

/-- The loyal edges `f ∈ Λ*_H` meeting the ball `B_H(x, a)` (at least one endpoint in the ball,
i.e. `f ∈ Λ*_H(x,a) = E_H(x,a) ∩ Λ*_H`) whose essential-demand set is exactly `D`.
For `D = {q}` this is `Λ*_H(x, a, q)`. -/
noncomputable def lamStarSet (H : SimpleGraph V) (R : Finset (Sym2 V)) (Vs : Finset V) (x : V)
    (a : ℝ) (D : Finset (Sym2 V)) : Finset (Sym2 V) :=
  (coreEdges H R Vs).filter (fun f => (∃ v ∈ f, v ∈ ball H x a) ∧ essSet H R f = D)

/-- `λ*_H(x, a, D)`: the cardinality of `lamStarSet`; with `D = D(e) = {q}` this is
`λ*_H(x, a, q)`. -/
noncomputable def lamStar (H : SimpleGraph V) (R : Finset (Sym2 V)) (Vs : Finset V) (x : V)
    (a : ℝ) (D : Finset (Sym2 V)) : ℕ :=
  (lamStarSet H R Vs x a D).card

/-- `n_x = |B_H(x, r)|`. -/
noncomputable def vol (H : SimpleGraph V) (x : V) (r : ℝ) : ℕ := (ball H x r).card

/-- The sum `Z` of Lemma 17 (Equation (13)):
`Z = ∑_{x ∈ V*} ∑_{e ∈ Λ*_H, x ∈ e} λ*_H(x, r/2, D(e)) / n_x`, counting incidences. -/
noncomputable def conflictSum (H : SimpleGraph V) (R : Finset (Sym2 V)) (Vs : Finset V)
    (r : ℝ) : ℝ :=
  ∑ x ∈ Vs, ∑ e ∈ (coreEdges H R Vs).filter (fun e => x ∈ e),
    (lamStar H R Vs x (r / 2) (essSet H R e) : ℝ) / (vol H x r : ℝ)

/-- Equation (11) with constant `C`: for every endpoint `x` of `e`,
`λ*_H(x, r/2, D(e)) ≤ C n_x / (d √r)`. -/
def IsGoodEdge (H : SimpleGraph V) (R : Finset (Sym2 V)) (Vs : Finset V) (d r C : ℝ)
    (e : Sym2 V) : Prop :=
  ∀ x ∈ e, (lamStar H R Vs x (r / 2) (essSet H R e) : ℝ) ≤ C * (vol H x r : ℝ) / (d * Real.sqrt r)

end DistancePreserver934.Exact


