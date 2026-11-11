-- Prove2me | Definitions.Def_PCSFBreach_Main_PrimalDual
-- name    : PCSFBreach_Main_PrimalDual
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T06:56:26.999468+00:00
-- url     : https://prove2.me/theorems/a452d73b-2726-4b39-a14f-d9a944070fc8
-- title:
--   The parametric (λ, µ) primal-dual algorithm as a relation on runs; colorings, forced pairs Q, D′ and balanced colorings
-- statement:
--   Fix parameters $\lambda>0$, $\mu\ge 0$. A **coloring** of a dual vector $(y_U)_{U\subseteq V}$ is $a_{Ui}\ge 0$ with $a_{Ui}=0$ unless $i\in\mathrm{sep}(U)$, $\sum_{i\in\mathrm{sep}(U)}a_{Ui}=y_U$ for every $U$, and $\sum_U a_{Ui}\le\lambda\pi_i$ for every pair $i$ (constraints (1)).
--
--   A **run** records event times $0=t_0<t_1<\dots<t_{\ell}$ and, for each stage $k$ (the interval $[t_k,t_{k+1})$, and $[t_\ell,\infty)$ for $k=\ell$), a forest $F_k$, a set $A_k$ of active moats and a set $N_k\subseteq A_k$ of normal-active moats. The current moats $C_k$ are the components of $(V,F_k)$; $C_t$, $A_t$ denote those of the stage containing $t$; $H$ is the set of all moats that ever appear. Normal duals grow at unit rate on stages where $U\in N_k$, extension duals on stages where $U\in A_k\setminus N_k$: $y^n_U(t)$, $y^e_U(t)$, $y_U=y^n_U+y^e_U$. The extension budget of a current moat $U$ is $\sum_{W\subseteq U}(\mu y^n_W(t)-y^e_W(t))$ (earned at rate $\mu$, spent at unit rate, added on merges). An edge is tight at $t$ if $\sum_{U:e\in\delta(U)}y_U(t)=c_e$.
--
--   The run is a run of the algorithm (**IsPDRun**) when: event times increase; each $F_k$ is a forest, $F_k\subseteq F_{k+1}$, edges of $F_0$ are tight at $0$ and edges added at $t_{k+1}$ are tight then; at every time of stage $k$ every tight edge lies inside a component of $F_k$ (merges are complete and happen before activity is determined); at every $t\ge 0$ edge feasibility (2) holds and the normal duals admit a coloring; $N_k\subseteq A_k\subseteq C_k$, and at every time $t$ of stage $k$ a current moat is in $N_k$ iff its normal dual can be increased by a positive amount keeping (1) feasible, and in $A_k$ iff it is normal-active or has positive budget; $A_k\ne\emptyset$ for $k<\ell$ and $A_\ell=\emptyset$.
--
--   A pair is **forced** at $t$ if every coloring of the normal duals at $t$ gives it total color $\lambda\pi_i$; $Q$ is the set of pairs forced at some $t\ge 0$ and $D'=D\setminus Q$. For a coloring $a$ of the final normal duals, $l_i=\sum_{U\in H}a_{Ui}$, $r_i=l_i/(\lambda\pi_i)$ ($r_i:=1$ if $\pi_i=0$), and $a$ is **balanced** if $a_{Ui}>0$ implies $r_i\le r_j$ for all $U\in H$, $j\in\mathrm{sep}(U)$. Also $y(H)$, $Y^n=y^n(H)$, $Y^e=y^e(H)$ are the sums of the final duals over $H$.
--
--   **Formalization Note** The continuous-time algorithm is a relation on finite stage records; every statement quantifies over all runs. Duals are summed over all vertex sets; sets that are never moats have zero dual and receive no color.
-- source:
--   Bosch-Calvo, Grandoni, Mátravölgyi, Breaching the 2-Approximation Barrier for Prize-Collecting Steiner Forest, STOC 2027 submission (manuscript sha256 05d9cc28…3eb3), pp. 4–6, §2 (constraints (1), (2), activity, merges) and §2.1 (forced pairs, Q, D′), p. 6, Lemma 1(iv) (balanced coloring)

import Mathlib
import Definitions.Def_PCSFBreach_Main_Instance
set_option autoImplicit false

namespace PCSFBreach.Main

open Finset

/-- A **coloring** of a dual vector `y` (constraints (1), p. 5) with capacity parameter `λ`:
`a_{Ui} ≥ 0`, `a_{Ui} = 0` unless `i ∈ sep(U)`, `Σ_{i ∈ sep(U)} a_{Ui} = y_U` for every set `U`, and
`Σ_U a_{Ui} ≤ λ π_i` for every pair `i`. (Sets with `y_U = 0`, in particular every set that is not
a moat, receive no color.) -/
def IsColoring (I : Instance) (lam : ℝ) (y : Finset (Fin I.n) → ℝ)
    (a : Finset (Fin I.n) → I.Pair → ℝ) : Prop :=
  (∀ U i, 0 ≤ a U i) ∧ (∀ U i, ¬ I.Separates U i → a U i = 0) ∧
  (∀ U, ∑ i ∈ I.sep U, a U i = y U) ∧ (∀ i, ∑ U, a U i ≤ lam * (I.pen i : ℝ))

/-- A run of the **parametric primal-dual algorithm** (§2, pp. 4–5), recorded by its event times
`0 = t₀ < t₁ < … < t_len`, and for each stage `k` (the interval `[t_k, t_{k+1})`, and for
`k = len` the final time `t_len` onwards): the grown forest `F_k`, the set `A_k` of active moats
and the set `N_k ⊆ A_k` of normal-active moats. The current moats `C_k` are the connected
components of `F_k`. Whether a record is a run of the algorithm is `IsPDRun`. -/
structure PDRun (I : Instance) where
  len : ℕ
  time : ℕ → ℝ
  forest : ℕ → Finset I.Edge
  active : ℕ → Finset (Finset (Fin I.n))
  normal : ℕ → Finset (Finset (Fin I.n))

namespace PDRun

variable {I : Instance} (R : PDRun I)

open scoped Classical in
/-- The current moats `C_k` of stage `k`: the vertex sets of the connected components of `F_k`. -/
noncomputable def moats (k : ℕ) : Finset (Finset (Fin I.n)) :=
  univ.image (fun v => univ.filter (fun w => I.Connected (R.forest k) v w))

open scoped Classical in
/-- The stage containing time `t`: the largest `k ≤ len` with `t_k ≤ t`. -/
noncomputable def stage (t : ℝ) : ℕ := ((range (R.len + 1)).filter (fun k => R.time k ≤ t)).sup id

/-- `C_t`, the current moats at time `t`. -/
noncomputable def moatsAt (t : ℝ) : Finset (Finset (Fin I.n)) := R.moats (R.stage t)

/-- `A_t`, the active moats at time `t`. -/
noncomputable def activeAt (t : ℝ) : Finset (Finset (Fin I.n)) := R.active (R.stage t)

/-- Length of `[t_k, t_{k+1}) ∩ [0, t)`. -/
noncomputable def overlap (k : ℕ) (t : ℝ) : ℝ := max 0 (min t (R.time (k + 1)) - R.time k)

open scoped Classical in
/-- Normal dual `yⁿ_U(t)`: `U` grows its normal dual at unit rate while it is normal-active. -/
noncomputable def yn (U : Finset (Fin I.n)) (t : ℝ) : ℝ :=
  ∑ k ∈ range R.len, if U ∈ R.normal k then R.overlap k t else 0

open scoped Classical in
/-- Extension dual `yᵉ_U(t)`: `U` grows its extension dual at unit rate while it is active but
not normal-active (extension-active). -/
noncomputable def ye (U : Finset (Fin I.n)) (t : ℝ) : ℝ :=
  ∑ k ∈ range R.len, if U ∈ R.active k ∧ U ∉ R.normal k then R.overlap k t else 0

/-- Total dual `y_U(t) = yⁿ_U(t) + yᵉ_U(t)`. -/
noncomputable def y (U : Finset (Fin I.n)) (t : ℝ) : ℝ := R.yn U t + R.ye U t

open scoped Classical in
/-- Load `Σ_{U : e ∈ δ(U)} y_U(t)` of edge `e` at time `t` (left side of (2)). -/
noncomputable def load (e : I.Edge) (t : ℝ) : ℝ :=
  ∑ U : Finset (Fin I.n), if I.Crosses e U then R.y U t else 0

/-- Edge `e` is tight at time `t`: equality in (2). -/
def Tight (e : I.Edge) (t : ℝ) : Prop := R.load e t = (I.c e : ℝ)

open scoped Classical in
/-- Extension budget of the current moat `U` at time `t`: budgets are earned at rate `μ` during
normal activity, spent at unit rate during extension activity, and added on merges, so the
budget of `U` is `Σ_{W ⊆ U} (μ yⁿ_W(t) − yᵉ_W(t))` over all moats `W` that merged into `U`. -/
noncomputable def budget (μ : ℝ) (U : Finset (Fin I.n)) (t : ℝ) : ℝ :=
  ∑ W ∈ univ.filter (fun W : Finset (Fin I.n) => W ⊆ U), (μ * R.yn W t - R.ye W t)

/-- The current moat `U` is **normal-active** at time `t` (p. 5): its normal dual can be increased
by a positive amount while keeping (1) feasible. -/
def NormalActive (lam : ℝ) (t : ℝ) (U : Finset (Fin I.n)) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∃ a, IsColoring I lam (Function.update (fun W => R.yn W t) U (R.yn U t + ε)) a

/-- The time `t ≥ 0` lies in stage `k`. -/
def InStage (k : ℕ) (t : ℝ) : Prop := R.time k ≤ t ∧ (k < R.len → t < R.time (k + 1))

/-- The end time `t_len` of the run. -/
noncomputable def finalTime : ℝ := R.time R.len

/-- The final grown forest `F_len`. -/
def finalForest : Finset I.Edge := R.forest R.len

open scoped Classical in
/-- `H`: every moat that ever appears. -/
noncomputable def H : Finset (Finset (Fin I.n)) := (range (R.len + 1)).biUnion R.moats

/-- Final normal dual `yⁿ_U`. -/
noncomputable def ynF (U : Finset (Fin I.n)) : ℝ := R.yn U R.finalTime
/-- Final extension dual `yᵉ_U`. -/
noncomputable def yeF (U : Finset (Fin I.n)) : ℝ := R.ye U R.finalTime
/-- Final total dual `y_U`. -/
noncomputable def yF (U : Finset (Fin I.n)) : ℝ := R.y U R.finalTime

/-- `y(H) = Σ_{U ∈ H} y_U`. -/
noncomputable def yH : ℝ := ∑ U ∈ R.H, R.yF U
/-- `Yⁿ = yⁿ(H) = Σ_{U ∈ H} yⁿ_U`. -/
noncomputable def YnH : ℝ := ∑ U ∈ R.H, R.ynF U
/-- `Yᵉ = yᵉ(H) = Σ_{U ∈ H} yᵉ_U`. -/
noncomputable def YeH : ℝ := ∑ U ∈ R.H, R.yeF U

/-- Pair `i` is **forced** at time `t` (§2.1, p. 5): every feasible coloring of the normal duals
at time `t` saturates its capacity `λ π_i`. -/
def Forced (lam : ℝ) (t : ℝ) (i : I.Pair) : Prop :=
  ∀ a, IsColoring I lam (fun U => R.yn U t) a → ∑ U, a U i = lam * (I.pen i : ℝ)

open scoped Classical in
/-- `Q`: the pairs forced at some time `t ≥ 0` (p. 6). -/
noncomputable def Q (lam : ℝ) : Finset I.Pair :=
  univ.filter (fun i => ∃ t : ℝ, 0 ≤ t ∧ R.Forced lam t i)

/-- `D′ = D \ Q`. -/
noncomputable def D' (lam : ℝ) : Finset I.Pair := univ \ R.Q lam

/-- `l_i = Σ_{U ∈ H} a_{Ui}`, the color pair `i` gives. -/
noncomputable def used (a : Finset (Fin I.n) → I.Pair → ℝ) (i : I.Pair) : ℝ :=
  ∑ U ∈ R.H, a U i

/-- The ratio `r_i = l_i / (λ π_i)` (Lemma 1(iv), p. 6). For `π_i = 0` (a pair the paper removes
without loss of generality, p. 4; its capacity `0` is saturated by every coloring) the ratio is
set to `1`. -/
noncomputable def ratio (lam : ℝ) (a : Finset (Fin I.n) → I.Pair → ℝ) (i : I.Pair) : ℝ :=
  if I.pen i = 0 then 1 else R.used a i / (lam * (I.pen i : ℝ))

/-- A **balanced coloring** (Lemma 1(iv), p. 6): a feasible coloring of the final normal duals
such that, for every `U ∈ H`, `a_{Ui} > 0` implies `r_i ≤ r_j` for every pair `j ∈ sep(U)`. -/
def IsBalanced (lam : ℝ) (a : Finset (Fin I.n) → I.Pair → ℝ) : Prop :=
  IsColoring I lam R.ynF a ∧
    ∀ U ∈ R.H, ∀ i, 0 < a U i → ∀ j ∈ I.sep U, R.ratio lam a i ≤ R.ratio lam a j

end PDRun

/-- `R` is a run of the parametric primal-dual algorithm with parameters `λ, μ` on `I`
(§2, pp. 4–5):
1. `t₀ = 0` and event times increase strictly;
2. every `F_k` is a forest, `F_k ⊆ F_{k+1}`, every edge of `F_0` is tight at time `0`, every edge
   added at the event `t_{k+1}` is tight at `t_{k+1}`;
3. merges are complete and happen exactly when edges get tight: at every time `t` of stage `k`
   every tight edge has both endpoints in one component of `F_k` (all tight-edge events at a time
   are processed before activity is determined);
4. at every time `t ≥ 0`, edge feasibility (2) holds and the normal duals admit a coloring (1);
5. `N_k ⊆ A_k ⊆ C_k`, and at every time `t` of stage `k` a current moat is in `N_k` iff it is
   normal-active at `t`, and in `A_k` iff it is normal-active or has positive extension budget;
6. the algorithm stops as soon as no moat is active: `A_k ≠ ∅` for `k < len`, `A_len = ∅`. -/
def IsPDRun (I : Instance) (lam μ : ℝ) (R : PDRun I) : Prop :=
  R.time 0 = 0 ∧ (∀ k < R.len, R.time k < R.time (k + 1)) ∧
  (∀ k ≤ R.len, I.IsForest (R.forest k)) ∧
  (∀ k < R.len, R.forest k ⊆ R.forest (k + 1)) ∧
  (∀ e ∈ R.forest 0, R.Tight e 0) ∧
  (∀ k < R.len, ∀ e ∈ R.forest (k + 1), e ∉ R.forest k → R.Tight e (R.time (k + 1))) ∧
  (∀ k ≤ R.len, ∀ t : ℝ, R.InStage k t → ∀ e, R.Tight e t →
      I.Connected (R.forest k) (I.eu e) (I.ev e)) ∧
  (∀ t : ℝ, 0 ≤ t → (∀ e, R.load e t ≤ (I.c e : ℝ)) ∧ ∃ a, IsColoring I lam (fun U => R.yn U t) a) ∧
  (∀ k ≤ R.len, R.normal k ⊆ R.active k ∧ R.active k ⊆ R.moats k) ∧
  (∀ k ≤ R.len, ∀ t : ℝ, R.InStage k t → ∀ U ∈ R.moats k,
      (U ∈ R.normal k ↔ R.NormalActive lam t U) ∧
      (U ∈ R.active k ↔ (U ∈ R.normal k ∨ 0 < R.budget μ U t))) ∧
  (∀ k < R.len, (R.active k).Nonempty) ∧ R.active R.len = ∅

end PCSFBreach.Main


