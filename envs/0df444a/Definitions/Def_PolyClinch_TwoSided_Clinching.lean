-- Prove2me | Definitions.Def_PolyClinch_TwoSided_Clinching
-- name    : PolyClinch_TwoSided_Clinching
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T09:19:17.914404+00:00
-- url     : https://prove2.me/theorems/550891a1-a16f-4a5f-9088-49f362cad803
-- title:
--   pp. 9–12 — virtual buyers, extended f_j (12), P (13), P̃, remnant supply polytopes (14)–(15), (19)–(20), clinching polytope (21), Algorithms 1 and 2, Mechanism 2
-- statement:
--   **Preprocessing (p. 9).** For each seller $j$ a virtual buyer $n+j$ is added with a single edge $(n+j)j$, budget $B_{n+j}=\infty$ and bid $v'_{n+j}=\rho_j$. The function $f_j$ is extended by
--   $$
--   f_j(F)=\begin{cases} f_j(E_j) & (n+j)j\in F,\\ f_j(F) & \text{otherwise}\end{cases}\qquad (F\subseteq E_j\cup\{(n+j)j\}). \tag{12}
--   $$
--   The polymatroid of the extended market is $P=\{w\in\mathbb R^E_+\mid w|_{E_j}\in P_j\ (j\in M)\}$ (13), and the polymatroidal environment of the **reduced one-sided market** is $\tilde P=\{y\in\mathbb R^N_+\mid \exists w\in P,\ y_i=w(E_i)\ (i\in N)\}$, now with $N$ the $n+m$ buyers.
--
--   **Algorithm 1 (pp. 9–10)** runs on a one-sided market with buyers $N$, feasible set $\tilde P$, budgets $B$ and bids $v'$. It keeps transactions $y$, payments $\pi$, price clocks $c$, demands $d$ and a pointer $l$, starting from $y=\pi=c=0$, $d=\infty$, $l=1$. While $d\ne0$ it (3) lets every buyer $i$ clinch $\zeta_i$, the largest $\zeta\ge0$ with $\tilde P^i_{y,d}(\zeta)=\tilde P^i_{y,d}(0)$, where
--   $$
--   \tilde P_{y,d}=\{z\in\mathbb R^N_+\mid y+z\in\tilde P,\ z_i\le d_i\},\qquad \tilde P^i_{y,d}(\zeta)=\{\sigma\in\mathbb R^{N-i}_+\mid \exists z\in\tilde P_{y,d},\ z_i=\zeta,\ z|_{N-i}=\sigma\}; \tag{14–15}
--   $$
--   (4) sets $y_i\mathrel{+}=\zeta_i$, $\pi_i\mathrel{+}=c_i\zeta_i$; (5) increases $c_l$ by $\varepsilon$; (6) sets $d_i=(B_i-\pi_i)/c_i$ if $c_i<v'_i$ and $0$ otherwise; (7) moves $l$ cyclically. It outputs $(y,\pi)$ when every demand is $0$.
--
--   **Algorithm 2 (p. 12)** runs on the extended two-sided market with transactions $w$, payments $p$, revenues $r$, clocks, demands and pointer. Each iteration lets the buyers $1,\dots,n+m$ in turn clinch a maximal vector $\xi$ of the **clinching polytope**
--   $$
--   P^i_{w,d}=\{\xi\in\mathbb R^{E_i}_+\mid P^i_{w,d}(\xi)=P^i_{w,d}(0)\}, \tag{21}
--   $$
--   where $P_{w,d}=\{x\in\mathbb R^E_+\mid w+x\in P,\ x(E_i)\le d_i\}$ (19) and $P^i_{w,d}(\xi)=\{u\in\mathbb R^{N-i}_+\mid\exists x\in P_{w,d},\ x|_{E_i}=\xi,\ x(E_k)=u_k\ (k\in N-i)\}$ (20); after each clinch $w\mathrel{+}=\xi$, $p_i\mathrel{+}=c_i\xi(E_i)$ and $d_i$ is recomputed. Then $r_j\mathrel{+}=\sum_{ij\in E_j}c_i\xi_{ij}$ (line 10), $c_l\mathrel{+}=\varepsilon$, the demand of buyer $l$ is recomputed and $l$ moves cyclically. **Mechanism 2** outputs the terminal $(w,p,r)$ transformed back to the original market (p. 11): $w$ restricted to $E$, the payments of the real buyers, and $r_j-p_{n+j}$.
--
--   **Formalization Note** Buyers of the extended market are `Fin (n + m)`: real buyer $i$ is `Fin.castAdd m i`, virtual buyer $n+j$ is `Fin.natAdd n j`; indices are 0-based and $l$ starts at buyer $0$. Budgets and demands live in `WithTop ℝ`; the demand update is $\infty$ when the budget is $\infty$ and $c_i<v'_i$, and also when $c_i=0<v'_i$ (the value $\infty$ of line 1, kept by Table 1, p. 16; Lean's $x/0=0$ would end the auction at once). Both algorithms are relations: a run is a finite sequence of states that starts at line 1, takes one while-iteration per step while some demand is nonzero, and stops at the first state with every demand $0$; the clinch of Algorithm 2 is any maximal vector (it is not unique). Vectors $\xi\in\mathbb R^{E_i}$ are vectors on all edges vanishing off $E_i$. Line 10's revenue is accumulated during the for loop; the clocks do not change before line 10, so this is the page's sum. Line 13 recomputes the demand of the buyer whose clock was just increased at line 11: read literally after line 12, it would recompute a demand that line 8 has just set at unchanged $p$ and $c$, and Table 1 (p. 16, rows 1–2) shows the clocked buyer's demand updated.
-- source:
--   Hirai & Sato, Polyhedral Clinching Auctions for Two-sided Markets, arXiv:1708.04881v2, p. 9 (Algorithm 1, preprocessing, (12), (13), P̃), p. 10 ((14), (15)), p. 11 (transformation), p. 12 (Algorithm 2, (19)–(21)), p. 16 (Table 1)

import Mathlib
import Definitions.Def_PolyClinch_TwoSided_Market

namespace PolyClinch.TwoSided

open Finset

/-! ### Demand update (line 6 of Algorithm 1, lines 8 and 13 of Algorithm 2) -/

/-- The demand `d_i := (B_i − p_i)/c_i` if `c_i < v′_i`, and `0` otherwise (pp. 9, 12), with the
budget `B_i ∈ ℝ ∪ {∞}`. Conventions: the demand is `∞` (`⊤`) when the budget is `∞` and
`c_i < v′_i`, and also when the clock is still `c_i = 0 < v′_i` (line 1 and Table 1, p. 16). -/
noncomputable def demandUpdate (B : WithTop ℝ) (p c v : ℝ) : WithTop ℝ :=
  if c < v then (if c = 0 then ⊤ else B.map (fun b => (b - p) / c)) else 0

/-! ### Algorithm 1 (p. 9) for a one-sided market with buyers `Fin K` and feasible set `Q` -/

section OneSided

variable {K : ℕ}

/-- The variables of Algorithm 1: transactions `y`, payments `π` (`pay`), price clocks `c`,
demands `d`, and the buyer `l` whose clock is increased next. -/
structure Alg1State (K : ℕ) where
  /-- transactions `y_i` -/
  y : Fin K → ℝ
  /-- payments `π_i` -/
  pay : Fin K → ℝ
  /-- price clocks `c_i` -/
  c : Fin K → ℝ
  /-- demands `d_i ∈ ℝ ∪ {∞}` -/
  d : Fin K → WithTop ℝ
  /-- the buyer whose clock is increased in the next iteration -/
  l : Fin K

/-- The remnant supply polytope (14), p. 10:
`P̃_{y,d} = {z ∈ ℝ^N_+ | y + z ∈ Q, z_i ≤ d_i (i ∈ N)}`. -/
def remnantSupply (Q : Set (Fin K → ℝ)) (y : Fin K → ℝ) (d : Fin K → WithTop ℝ) :
    Set (Fin K → ℝ) :=
  {z | (∀ i, 0 ≤ z i) ∧ y + z ∈ Q ∧ ∀ i, ((z i : ℝ) : WithTop ℝ) ≤ d i}

/-- The remnant supply polytope of the remaining buyers (15), p. 10:
`P̃^i_{y,d}(ζ) = {σ ∈ ℝ^{N−i}_+ | ∃ z ∈ P̃_{y,d}, z_i = ζ, z|_{N−i} = σ}`. -/
def remnantSupplyOthers (Q : Set (Fin K → ℝ)) (y : Fin K → ℝ) (d : Fin K → WithTop ℝ)
    (i : Fin K) (ζ : ℝ) : Set ({k : Fin K // k ≠ i} → ℝ) :=
  {σ | (∀ k, 0 ≤ σ k) ∧ ∃ z ∈ remnantSupply Q y d, z i = ζ ∧ ∀ k : {k : Fin K // k ≠ i}, z k = σ k}

/-- Line 3 of Algorithm 1 for buyer `i` (p. 10): `ζ` is the maximum `ζ ∈ ℝ_+` with
`P̃^i_{y,d}(ζ) = P̃^i_{y,d}(0)`. -/
def IsMaxClinch1 (Q : Set (Fin K → ℝ)) (y : Fin K → ℝ) (d : Fin K → WithTop ℝ) (i : Fin K)
    (ζ : ℝ) : Prop :=
  IsGreatest {ζ' : ℝ | 0 ≤ ζ' ∧ remnantSupplyOthers Q y d i ζ' = remnantSupplyOthers Q y d i 0} ζ

/-- Line 1 of Algorithm 1: `y = 0`, `π = 0`, `c = 0`, `d = ∞`, and `l` is the first buyer. -/
def Alg1Init (s : Alg1State K) : Prop :=
  s.y = 0 ∧ s.pay = 0 ∧ s.c = 0 ∧ s.d = (fun _ => ⊤) ∧ (s.l : ℕ) = 0

/-- One iteration (lines 3–7) of Algorithm 1 with feasible set `Q`, budgets `B`, bids `v` and
clock step `ε`. All clinches `ζ_i` are computed from the same `(y, d)`; line 4 uses the clocks
before line 5; line 6 uses the payments after line 4 and the clocks after line 5; line 7 moves
`l` to the cyclic successor. -/
def Alg1Step (Q : Set (Fin K → ℝ)) (B : Fin K → WithTop ℝ) (v : Fin K → ℝ) (ε : ℝ)
    (s s' : Alg1State K) : Prop :=
  ∃ ζ : Fin K → ℝ, (∀ i, IsMaxClinch1 Q s.y s.d i (ζ i)) ∧
    s'.y = s.y + ζ ∧
    s'.pay = (fun i => s.pay i + s.c i * ζ i) ∧
    s'.c = Function.update s.c s.l (s.c s.l + ε) ∧
    s'.d = (fun i => demandUpdate (B i) (s'.pay i) (s'.c i) (v i)) ∧
    s'.l = finRotate K s.l

/-- `S` is a terminal state of a run of Algorithm 1: a finite sequence of states starting at
line 1, each obtained from the previous one by an iteration performed while some demand is
nonzero, and ending at the first state where every demand is `0`. Its output is `(S.y, S.pay)`. -/
def Alg1Outcome (Q : Set (Fin K → ℝ)) (B : Fin K → WithTop ℝ) (v : Fin K → ℝ) (ε : ℝ)
    (S : Alg1State K) : Prop :=
  ∃ (T : ℕ) (s : ℕ → Alg1State K), Alg1Init (s 0) ∧
    (∀ t < T, (∃ i, (s t).d i ≠ 0) ∧ Alg1Step Q B v ε (s t) (s (t + 1))) ∧
    (∀ i, (s T).d i = 0) ∧ S = s T

/-- Utility (2) of buyer `i` with true value `t` in the one-sided market (p. 9): `t y_i − π_i`
if `π_i ≤ B_i`, and `−∞` otherwise. -/
noncomputable def oneSidedUtility (B : Fin K → WithTop ℝ) (t : ℝ) (S : Alg1State K)
    (i : Fin K) : WithBot ℝ :=
  if ((S.pay i : ℝ) : WithTop ℝ) ≤ B i then ((t * S.y i - S.pay i : ℝ) : WithBot ℝ) else ⊥

end OneSided

/-! ### The preprocessed market with virtual buyers (p. 9) -/

section Extended

variable {n m : ℕ} (E : Finset (Fin n × Fin m))

/-- The edge set after preprocessing (p. 9): buyers are `Fin (n + m)`, real buyer `i` is
`Fin.castAdd m i`, and the virtual buyer `n + j` (`Fin.natAdd n j`) is joined to seller `j` only. -/
def extEdges : Finset (Fin (n + m) × Fin m) :=
  E.image (fun e => (Fin.castAdd m e.1, e.2)) ∪ univ.image (fun j => (Fin.natAdd n j, j))

/-- An original edge `ij ∈ E` as an edge of the preprocessed market. -/
def liftEdge (e : ↥E) : ↥(extEdges E) :=
  ⟨(Fin.castAdd m e.1.1, e.1.2), by
    simp only [extEdges, mem_union, mem_image]
    exact Or.inl ⟨e.1, e.2, rfl⟩⟩

/-- The new edge `(n + j)j` of the virtual buyer of seller `j`. -/
def virtEdge (j : Fin m) : ↥(extEdges E) :=
  ⟨(Fin.natAdd n j, j), by
    simp only [extEdges, mem_union, mem_image]
    exact Or.inr ⟨j, mem_univ _, rfl⟩⟩

/-- `E_i` in the preprocessed market. -/
def extEdgesOfBuyer (i : Fin (n + m)) : Finset ↥(extEdges E) := univ.filter (fun e => e.1.1 = i)

/-- `E_j` in the preprocessed market (`E_j ∪ {(n + j)j}`). -/
def extEdgesOfSeller (j : Fin m) : Finset ↥(extEdges E) := univ.filter (fun e => e.1.2 = j)

/-- The extended `f_j` of (12), p. 9: `f_j(E_j)` if `(n + j)j ∈ F`, and `f_j(F)` otherwise
(`F` read as a set of original edges). -/
noncomputable def extF (I : PublicInfo E) (j : Fin m) (F : Finset ↥(extEdges E)) : ℝ :=
  if virtEdge E j ∈ F then I.f j (edgesOfSeller E j)
  else I.f j (univ.filter (fun e => liftEdge E e ∈ F))

/-- Budgets after preprocessing: `B_i` for real buyers, `B_{n+j} = ∞` for virtual buyers. -/
def extBudget (I : PublicInfo E) : Fin (n + m) → WithTop ℝ :=
  Fin.append (fun i => ((I.budget i : ℝ) : WithTop ℝ)) (fun _ => ⊤)

/-- Bids after preprocessing: `v′_i` for real buyers, `v′_{n+j} = ρ_j` for virtual buyers. -/
def extBid (I : PublicInfo E) : Fin (n + m) → ℝ :=
  Fin.append I.bid I.rho

/-- The polymatroid `P = ⊕_j P_j` of (13), p. 9, for the preprocessed market. -/
def extP (I : PublicInfo E) : Set (↥(extEdges E) → ℝ) :=
  {w | (∀ e, 0 ≤ w e) ∧ ∀ j, w ∈ polymatroidOn (extEdgesOfSeller E j) (extF E I j)}

/-- The polymatroidal environment `P̃ = {y ∈ ℝ^N_+ | ∃ w ∈ P, y_i = w(E_i) (i ∈ N)}` of the
reduced one-sided market (p. 9). -/
def reducedP (I : PublicInfo E) : Set (Fin (n + m) → ℝ) :=
  {y | (∀ i, 0 ≤ y i) ∧ ∃ w ∈ extP E I, ∀ i, y i = ∑ e ∈ extEdgesOfBuyer E i, w e}

/-! ### Algorithm 2 (p. 12) -/

/-- The variables of Algorithm 2: transactions `w`, payments `p`, revenues `r`, clocks `c`,
demands `d`, and the buyer `l` whose clock is increased next. -/
structure Alg2State where
  /-- transactions `w_ij` on the preprocessed edges -/
  w : ↥(extEdges E) → ℝ
  /-- payments `p_i` -/
  p : Fin (n + m) → ℝ
  /-- revenues `r_j` -/
  r : Fin m → ℝ
  /-- price clocks `c_i` -/
  c : Fin (n + m) → ℝ
  /-- demands `d_i ∈ ℝ ∪ {∞}` -/
  d : Fin (n + m) → WithTop ℝ
  /-- the buyer whose clock is increased in the current iteration -/
  l : Fin (n + m)

/-- The variables changed inside the for loop (lines 4–9), plus the revenue increments
`Δr_j = ∑_{ij ∈ E_j} c_i ξ_ij` collected for line 10. -/
structure Alg2Inner where
  /-- transactions -/
  w : ↥(extEdges E) → ℝ
  /-- payments -/
  p : Fin (n + m) → ℝ
  /-- demands -/
  d : Fin (n + m) → WithTop ℝ
  /-- revenue increments collected for line 10 -/
  dr : Fin m → ℝ

/-- The remnant supply polytope (19), p. 12:
`P_{w,d} = {x ∈ ℝ^E_+ | w + x ∈ P, x(E_i) ≤ d_i (i ∈ N)}`. -/
def remnantSupply2 (I : PublicInfo E) (w : ↥(extEdges E) → ℝ) (d : Fin (n + m) → WithTop ℝ) :
    Set (↥(extEdges E) → ℝ) :=
  {x | (∀ e, 0 ≤ x e) ∧ w + x ∈ extP E I ∧
    ∀ i, ((∑ e ∈ extEdgesOfBuyer E i, x e : ℝ) : WithTop ℝ) ≤ d i}

/-- The remnant supply polytope of the remaining buyers (20), p. 12:
`P^i_{w,d}(ξ) = {u ∈ ℝ^{N−i}_+ | ∃ x ∈ P_{w,d}, x|_{E_i} = ξ, x(E_k) = u_k (k ∈ N − i)}`. -/
def remnantSupplyOthers2 (I : PublicInfo E) (w : ↥(extEdges E) → ℝ)
    (d : Fin (n + m) → WithTop ℝ) (i : Fin (n + m)) (ξ : ↥(extEdges E) → ℝ) :
    Set ({k : Fin (n + m) // k ≠ i} → ℝ) :=
  {u | (∀ k, 0 ≤ u k) ∧ ∃ x ∈ remnantSupply2 E I w d, (∀ e ∈ extEdgesOfBuyer E i, x e = ξ e) ∧
    ∀ k : {k : Fin (n + m) // k ≠ i}, ∑ e ∈ extEdgesOfBuyer E k, x e = u k}

/-- The clinching polytope (21), p. 12: `P^i_{w,d} = {ξ ∈ ℝ^{E_i}_+ | P^i_{w,d}(ξ) = P^i_{w,d}(0)}`,
with `ξ ∈ ℝ^{E_i}` represented as a vector on all edges that vanishes off `E_i`. -/
def clinchingPolytope (I : PublicInfo E) (w : ↥(extEdges E) → ℝ) (d : Fin (n + m) → WithTop ℝ)
    (i : Fin (n + m)) : Set (↥(extEdges E) → ℝ) :=
  {ξ | (∀ e, 0 ≤ ξ e) ∧ (∀ e ∉ extEdgesOfBuyer E i, ξ e = 0) ∧
    remnantSupplyOthers2 E I w d i ξ = remnantSupplyOthers2 E I w d i 0}

/-- Lines 5–8 of Algorithm 2 for buyer `i` at clocks `c`: `ξ` is a maximal vector of the
clinching polytope `P^i_{w,d}` (p. 12); `w := w + ξ`; `p_i := p_i + c_i ξ(E_i)`;
`d_i := (B_i − p_i)/c_i` if `c_i < v′_i`, else `0`; and `c_i ξ_ij` is added to the revenue
increment of the seller of each edge `ij ∈ E_i` (for line 10). -/
def Alg2Clinch (I : PublicInfo E) (c : Fin (n + m) → ℝ) (i : Fin (n + m))
    (u u' : Alg2Inner E) : Prop :=
  ∃ ξ : ↥(extEdges E) → ℝ, Maximal (· ∈ clinchingPolytope E I u.w u.d i) ξ ∧
    u'.w = u.w + ξ ∧
    u'.p = Function.update u.p i (u.p i + c i * ∑ e ∈ extEdgesOfBuyer E i, ξ e) ∧
    u'.d = Function.update u.d i (demandUpdate (extBudget E I i) (u'.p i) (c i) (extBid E I i)) ∧
    u'.dr = (fun j => u.dr j + ∑ e ∈ extEdgesOfSeller E j, c e.1.1 * ξ e)

/-- Line 1–2 of Algorithm 2: `p = 0`, `c = 0`, `d = ∞`, `l` the first buyer, `r = 0`, `w = 0`. -/
def Alg2Init (s : Alg2State E) : Prop :=
  s.w = 0 ∧ s.p = 0 ∧ s.r = 0 ∧ s.c = 0 ∧ s.d = (fun _ => ⊤) ∧ (s.l : ℕ) = 0

/-- One iteration of the while loop (lines 4–13) of Algorithm 2: the buyers `0, 1, …, n + m − 1`
clinch in turn (each from the `(w, d)` left by the previous ones), the collected revenues are
added (line 10), the clock of buyer `l` is increased by `ε` (line 11), the demand of that buyer is
recomputed at the new clock (line 13), and `l` moves to the cyclic successor (line 12). -/
def Alg2Step (I : PublicInfo E) (ε : ℝ) (s s' : Alg2State E) : Prop :=
  ∃ u : ℕ → Alg2Inner E, u 0 = ⟨s.w, s.p, s.d, 0⟩ ∧
    (∀ k (hk : k < n + m), Alg2Clinch E I s.c ⟨k, hk⟩ (u k) (u (k + 1))) ∧
    s'.w = (u (n + m)).w ∧ s'.p = (u (n + m)).p ∧ s'.r = s.r + (u (n + m)).dr ∧
    s'.c = Function.update s.c s.l (s.c s.l + ε) ∧
    s'.d = Function.update (u (n + m)).d s.l
      (demandUpdate (extBudget E I s.l) (s'.p s.l) (s'.c s.l) (extBid E I s.l)) ∧
    s'.l = finRotate (n + m) s.l

/-- `S` is a terminal state of a run of Algorithm 2 on the preprocessed market of `I`: a finite
sequence of states starting at lines 1–2, each obtained from the previous one by an iteration
performed while some demand is nonzero, ending at the first state where every demand is `0`. -/
def Alg2Outcome (I : PublicInfo E) (ε : ℝ) (S : Alg2State E) : Prop :=
  ∃ (T : ℕ) (s : ℕ → Alg2State E), Alg2Init E (s 0) ∧
    (∀ t < T, (∃ i, (s t).d i ≠ 0) ∧ Alg2Step E I ε (s t) (s (t + 1))) ∧
    (∀ i, (s T).d i = 0) ∧ S = s T

/-- The transformation back to the original market (p. 11): keep `w` on the original edges and
the payments of the real buyers, and replace `r_j` by `r_j − p_{n+j}`. -/
def toOriginal (S : Alg2State E) : Allocation E :=
  ⟨fun e => S.w (liftEdge E e), fun i => S.p (Fin.castAdd m i),
    fun j => S.r j - S.p (Fin.natAdd n j)⟩

/-- `A` is an output of Mechanism 2 (p. 11–12) on input `I` with clock step `ε`: the
transformation of a terminal state of Algorithm 2 on the preprocessed market. -/
def Mech2Outcome (I : PublicInfo E) (ε : ℝ) (A : Allocation E) : Prop :=
  ∃ S, Alg2Outcome E I ε S ∧ A = toOriginal E S

end Extended

end PolyClinch.TwoSided


