-- Prove2me | Definitions.Def_RobustBCPCVRP_Formulation_Polytopes
-- name    : RobustBCPCVRP_Formulation_Polytopes
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T05:41:17.749001+00:00
-- url     : https://prove2.me/theorems/22fc544d-d42e-4599-8386-235285813df8
-- title:
--   §2, pp. 4–5, §3.1, p. 6 — constraints (1)–(6), the polytopes P₁, P₂, P₃, the Dantzig–Wolfe Master (7)–(11) and edge reduced costs
-- statement:
--   Keep the setting of the CVRP definitions: graph $G=(V,E)$, $V=\{0,\dots,n\}$, clients $V_+=\{1,\dots,n\}$, demands $d$, $K$ vehicles of capacity $C$. For $S\subseteq V$ let $\delta(S)$ be the set of edges with exactly one end-vertex in $S$, $x(\delta(S))=\sum_{e\in\delta(S)}x_e$, $d(S)=\sum_{i\in S}d_i$ and $k(S)=\lceil d(S)/C\rceil$. For a vector $x\in\mathbb R^{E}$ consider the constraints
--   $$
--   \begin{aligned}
--   &x(\delta(\{i\}))=2 \quad \forall i\in V_+ &&(1)\\
--   &x(\delta(\{0\}))=2K &&(2)\\
--   &x(\delta(S))\ge 2k(S) \quad \forall S\subseteq V_+ &&(3)\\
--   &x_e\le 1 \quad \forall e\in E\setminus\delta(\{0\}) &&(4)\\
--   &\textstyle\sum_j q^e_j\lambda_j - x_e=0\quad\forall e\in E &&(5)\\
--   &\textstyle\sum_j\lambda_j=K &&(6)
--   \end{aligned}
--   $$
--   together with $x\ge 0$ and $\lambda\ge 0$, where $j$ ranges over the q-routes without 2-cycles and $q^e_j$ is the number of times q-route $j$ traverses $e$.
--
--   1. $P_1$ is the set of $x\ge 0$ satisfying (1)–(4).
--   2. $P_2$ is the set of $x\ge 0$ satisfying (1) for which some $\lambda\ge 0$ satisfies (5) and (6).
--   3. $P_3$ (the **Explicit Master**) is the set of $x\ge 0$ for which some single $\lambda\ge 0$ makes $(x,\lambda)$ satisfy all of (1)–(6).
--   4. $\lambda\ge 0$ is feasible for the **Dantzig–Wolfe Master** (DWM) if
--   $$
--   \begin{aligned}
--   &\textstyle\sum_j\sum_{e\in\delta(\{i\})}q^e_j\lambda_j=2\quad\forall i\in V_+ &&(8)\\
--   &\textstyle\sum_j\sum_{e\in\delta(\{0\})}q^e_j\lambda_j=2K &&(9)\\
--   &\textstyle\sum_j\sum_{e\in\delta(S)}q^e_j\lambda_j\ge 2k(S)\quad\forall S\subseteq V_+ &&(10)\\
--   &\textstyle\sum_j q^e_j\lambda_j\le 1\quad\forall e\in E\setminus\delta(\{0\}) &&(11)
--   \end{aligned}
--   $$
--   and its objective (7) is $\sum_j\sum_{e\in E}\ell_e q^e_j\lambda_j$.
--   5. For dual values $\mu_i$ of (8), $\nu$ of (9), $\pi_S$ of (10), $\omega_e$ of (11) and $\alpha_t$ of finitely many generic cuts $\sum_j(\sum_e a_{t,e}q^e_j)\lambda_j\ge b_t$, the **reduced cost** of an edge is
--   $$
--   \bar c_e=\begin{cases}\ell_e-\mu_i-\mu_j-\sum_{S:\,\delta(S)\ni e}\pi_S-\omega_e-\sum_t a_{t,e}\alpha_t, & e=\{i,j\}\in E\setminus\delta(\{0\}),\\[2pt] \ell_e-\nu-\mu_j-\sum_{S:\,\delta(S)\ni e}\pi_S-\sum_t a_{t,e}\alpha_t, & e=\{0,j\}\in\delta(\{0\}),\end{cases}
--   $$
--   where $S$ ranges over the subsets of $V_+$.
--
--   These sets encode the paper's new formulation: $P_3=P_1\cap P_2$ is optimized over by column generation on the DWM.
--
--   **Formalization Note** The paper's $x\in\mathbb R^{|E|}$ is a function on all unordered pairs that vanishes off $E$ (`OnE`), which is part of every polytope. $x(\delta(S))$ is the published `LysgaardCVRP.Shrink.cut`, and $k(S)$ is the published `LysgaardCVRP.Shrink.roundedCapacityBound` with real capacity $C$. In (3) and (10) the sets $S$ range over all subsets of $V_+$, including $\emptyset$. $P_3$ is written from the Explicit Master display with one $\lambda$ for (5) and (6) together, not as $P_1\cap P_2$. The constraints (8)–(10) keep the paper's double sums, with $\sum_{e\in\delta(S)}q^e_j$ written as the cut value of the column's incidence vector. The $\pi$ sum in $\bar c_e$ runs over all $S\subseteq V_+$ with $e\in\delta(S)$; $\mu$ enters only through client end-vertices. The generic cuts' duals $\alpha_t$ are folded into $\bar c_e$ as the paper prescribes ("contributes with the value $-a_e\cdot\alpha$").
-- source:
--   Fukasawa, Longo, Lysgaard, Poggi de Aragão, Reis, Uchoa & Werneck, Robust branch-and-cut-and-price for the capacitated vehicle routing problem, Math. Program. (DOI 10.1007/s10107-005-0644-x); accepted manuscript, p. 4 (§2, P₁ (1)–(4), P₂ (5)–(6)), p. 5 (§2, P₃, DWM (7)–(11)), p. 6 (§3.1, c̄ₑ)

import Mathlib
import Definitions.Def_LysgaardCVRP_Shrink_cut
import Definitions.Def_LysgaardCVRP_Shrink_roundedCapacityBound
import Definitions.Def_RobustBCPCVRP_Formulation_Setting

namespace RobustBCPCVRP.Formulation

/-! Fukasawa et al., *Robust branch-and-cut-and-price for the capacitated vehicle routing
problem*, §2, pp. 4–5: the constraint blocks (1)–(6), the polytopes `P₁`, `P₂`, `P₃`, and the
Dantzig–Wolfe Master (7)–(11); §3.1, p. 6: the edge reduced costs `c̄_e`. The cut value
`x(δ(S))` is `LysgaardCVRP.Shrink.cut x S` and `k(S) = ⌈d(S)/C⌉` is
`LysgaardCVRP.Shrink.roundedCapacityBound d C S`. -/

open LysgaardCVRP.Shrink

variable {n : ℕ}

/-- `x ∈ ℝ^{|E|}`: the vector vanishes off the edge set `E`. -/
def OnE (E : Finset (Sym2 (Fin (n + 1)))) (x : Sym2 (Fin (n + 1)) → ℝ) : Prop :=
  ∀ e, e ∉ E → x e = 0

/-- `x_e ≥ 0` for all `e`. -/
def Nonneg (x : Sym2 (Fin (n + 1)) → ℝ) : Prop :=
  ∀ e, 0 ≤ x e

/-- Constraints (1): `x(δ({i})) = 2` for every client `i ∈ V₊`. -/
def Deg1 (x : Sym2 (Fin (n + 1)) → ℝ) : Prop :=
  ∀ i : Fin (n + 1), i ≠ 0 → cut x {i} = 2

/-- Constraint (2): `x(δ({0})) = 2K`. -/
def Deg2 (K : ℕ) (x : Sym2 (Fin (n + 1)) → ℝ) : Prop :=
  cut x {0} = 2 * (K : ℝ)

/-- Constraints (3), the rounded capacity inequalities: `x(δ(S)) ≥ 2 k(S)` for every
`S ⊆ V₊`, where `k(S) = ⌈d(S)/C⌉`. -/
def Cap3 (d : Fin (n + 1) → ℕ) (C : ℕ) (x : Sym2 (Fin (n + 1)) → ℝ) : Prop :=
  ∀ S : Finset (Fin (n + 1)), (0 : Fin (n + 1)) ∉ S →
    2 * (roundedCapacityBound d (C : ℝ) S : ℝ) ≤ cut x S

/-- Constraints (4): `x_e ≤ 1` for every edge `e ∈ E` not incident to the depot. -/
def Bnd4 (E : Finset (Sym2 (Fin (n + 1)))) (x : Sym2 (Fin (n + 1)) → ℝ) : Prop :=
  ∀ e ∈ E, (0 : Fin (n + 1)) ∉ e → x e ≤ 1

/-- `x ∈ P₁` (p. 4): constraints (1)–(4) and `x ≥ 0`. -/
def InP1 (E : Finset (Sym2 (Fin (n + 1)))) (d : Fin (n + 1) → ℕ) (K C : ℕ)
    (x : Sym2 (Fin (n + 1)) → ℝ) : Prop :=
  OnE E x ∧ Deg1 x ∧ Deg2 K x ∧ Cap3 d C x ∧ Bnd4 E x ∧ Nonneg x

/-- `x ∈ P₂` (p. 4): there are column weights `λ ≥ 0` on q-routes without 2-cycles with
(5) `∑_j q^e_j λ_j = x_e` for `e ∈ E` and (6) `∑_j λ_j = K`, and `x` satisfies (1) and `x ≥ 0`. -/
def InP2 (E : Finset (Sym2 (Fin (n + 1)))) (d : Fin (n + 1) → ℕ) (K C : ℕ)
    (x : Sym2 (Fin (n + 1)) → ℝ) : Prop :=
  OnE E x ∧ Nonneg x ∧ Deg1 x ∧
    ∃ lam : List (Fin (n + 1)) →₀ ℝ, IsColumns E d C lam ∧
      (∀ e ∈ E, colSum lam e = x e) ∧ colCount lam = (K : ℝ)

/-- `x ∈ P₃` (p. 5, the Explicit Master): there are column weights `λ ≥ 0` on q-routes without
2-cycles such that `(x, λ)` satisfies (1)–(6), `x ≥ 0`. -/
def InP3 (E : Finset (Sym2 (Fin (n + 1)))) (d : Fin (n + 1) → ℕ) (K C : ℕ)
    (x : Sym2 (Fin (n + 1)) → ℝ) : Prop :=
  OnE E x ∧ Deg1 x ∧ Deg2 K x ∧ Cap3 d C x ∧ Bnd4 E x ∧ Nonneg x ∧
    ∃ lam : List (Fin (n + 1)) →₀ ℝ, IsColumns E d C lam ∧
      (∀ e ∈ E, colSum lam e = x e) ∧ colCount lam = (K : ℝ)

/-- `∑_{e ∈ δ(S)} q^e`: the coefficient of the column of `r` in a row `x(δ(S))`. -/
noncomputable def cutCoeff (r : List (Fin (n + 1))) (S : Finset (Fin (n + 1))) : ℝ :=
  cut (fun e => (inc r e : ℝ)) S

/-- `λ` is feasible for the Dantzig–Wolfe Master (p. 5): `λ ≥ 0` on q-routes without
2-cycles, and (8)–(11) hold, each written as the paper's double sum `∑_j ∑_{e ∈ ·} q^e_j λ_j`. -/
def IsDWMFeasible (E : Finset (Sym2 (Fin (n + 1)))) (d : Fin (n + 1) → ℕ) (K C : ℕ)
    (lam : List (Fin (n + 1)) →₀ ℝ) : Prop :=
  IsColumns E d C lam ∧
    (∀ i : Fin (n + 1), i ≠ 0 → ∑ r ∈ lam.support, cutCoeff r {i} * lam r = 2) ∧
    ∑ r ∈ lam.support, cutCoeff r {0} * lam r = 2 * (K : ℝ) ∧
    (∀ S : Finset (Fin (n + 1)), (0 : Fin (n + 1)) ∉ S →
      2 * (roundedCapacityBound d (C : ℝ) S : ℝ) ≤ ∑ r ∈ lam.support, cutCoeff r S * lam r) ∧
    (∀ e ∈ E, (0 : Fin (n + 1)) ∉ e → ∑ r ∈ lam.support, (inc r e : ℝ) * lam r ≤ 1)

/-- The DWM objective (7): `∑_j ∑_{e ∈ E} ℓ_e q^e_j λ_j`. -/
noncomputable def dwmObjective (E : Finset (Sym2 (Fin (n + 1)))) (ℓ : Sym2 (Fin (n + 1)) → ℝ)
    (lam : List (Fin (n + 1)) →₀ ℝ) : ℝ :=
  ∑ r ∈ lam.support, ∑ e ∈ E, ℓ e * (inc r e : ℝ) * lam r

/-- `e ∈ δ(S)`: exactly one end-vertex of `e` lies in `S`. -/
def InCut (S : Finset (Fin (n + 1))) (e : Sym2 (Fin (n + 1))) : Prop :=
  Sym2.lift ⟨fun i j => (i ∈ S ∧ j ∉ S) ∨ (j ∈ S ∧ i ∉ S), fun _ _ => propext or_comm⟩ e

/-- The client sets `S ⊆ V₊ = {1, …, n}`. -/
def clientSets (n : ℕ) : Finset (Finset (Fin (n + 1))) :=
  (Finset.univ.filter (fun i : Fin (n + 1) => i ≠ 0)).powerset

/-- `μ_i + μ_j` summed over the client end-vertices of `e = {i, j}` (the depot contributes
nothing): `μ_i + μ_j` off the depot and `μ_j` for `e = {0, j}`. -/
def clientDual (μ : Fin (n + 1) → ℝ) (e : Sym2 (Fin (n + 1))) : ℝ :=
  Sym2.lift ⟨fun i j => (if i = 0 then 0 else μ i) + (if j = 0 then 0 else μ j),
    fun _ _ => add_comm _ _⟩ e

open Classical in
/-- The reduced cost `c̄_e` of an edge (§3.1, p. 6), for duals `μ` of (8), `ν` of (9), `π` of
(10), `ω` of (11), and duals `α_t` of finitely many generic cuts `∑_j (∑_e a_{t,e} q^e_j) λ_j ≥ b_t`:
`c̄_e = ℓ_e − μ_i − μ_j − ∑_{S : δ(S) ∋ e} π_S − ω_e − ∑_t a_{t,e} α_t` for `e = {i, j}` off the
depot, and `c̄_e = ℓ_e − ν − μ_j − ∑_{S : δ(S) ∋ e} π_S − ∑_t a_{t,e} α_t` for `e = {0, j}`. -/
noncomputable def edgeReducedCost {ι : Type*} [Fintype ι] (ℓ : Sym2 (Fin (n + 1)) → ℝ)
    (μ : Fin (n + 1) → ℝ) (ν : ℝ) (π : Finset (Fin (n + 1)) → ℝ)
    (ω : Sym2 (Fin (n + 1)) → ℝ) (a : ι → Sym2 (Fin (n + 1)) → ℝ) (α : ι → ℝ)
    (e : Sym2 (Fin (n + 1))) : ℝ :=
  ℓ e - clientDual μ e - (if (0 : Fin (n + 1)) ∈ e then ν else ω e)
    - ∑ S ∈ (clientSets n).filter (fun S => InCut S e), π S
    - ∑ t, a t e * α t

end RobustBCPCVRP.Formulation


