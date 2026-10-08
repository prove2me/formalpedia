-- Prove2me | Definitions.Def_ProjSchedTW_NetPresentValue_Project
-- name    : ProjSchedTW_NetPresentValue_Project
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T11:07:19.600119+00:00
-- url     : https://prove2.me/theorems/ef8fa822-9d62-4536-95f1-420217c6e94f
-- title:
--   §1.2 and §3.1 — project network with a deadline, time-feasible region and the net present value objective
-- statement:
--   A **project** consists of the activities $V=\{0,1,\dots,n+1\}$ with $n\ge 1$, where $0$ is the project beginning and $n+1$ the project completion, a **project network** $N=\langle V,E;\delta\rangle$ with arc set $E\subseteq V\times V$ (no loops) and integer arc weights $\delta_{ij}$, integer durations $p_i$ with $p_0=p_{n+1}=0$ and $p_i>0$ for $i=1,\dots,n$, and a maximum project duration $\bar d\in\mathbb N$. The deadline $S_{n+1}\le\bar d$ is an arc of the network: $E$ contains $\langle n+1,0\rangle$ with weight $\delta_{n+1,0}=-\bar d$.
--
--   A schedule is a vector $S=(S_0,\dots,S_{n+1})$ of real start times. The **time-feasible region** is
--   $$\mathcal S_T=\{S\in\mathbb R^{n+2}_{\ge 0}\mid S_0=0,\ S_j-S_i\ge\delta_{ij}\ \text{for all }\langle i,j\rangle\in E\}.$$
--
--   Given a discount rate $\beta$ and cash flows $c_i^F\in\mathbb R$ occurring at the completion times $C_i=S_i+p_i$, the **net present value objective** (to be minimized) is
--   $$f(S)=-\sum_{i\in V}c_i^F\beta^{S_i+p_i}.$$
--   A schedule $S$ is **time-optimal** if $S\in\mathcal S_T$ and $f(S)\le f(S')$ for every $S'\in\mathcal S_T$ (problem (3.9.1)). Finally, a **walk of length** $w$ from $i$ to $j$ in $N$ is a sequence of arcs of $E$ leading from $i$ to $j$ whose weights sum to $w$.
--
--   These objects are the setting of the time-constrained project scheduling problem $PS\infty|temp,\bar d|-\sum c_i^F\beta^{C_i}$ of Section 3.9.
--
--   **Formalization Note** Activities are `Fin (n + 2)` with `Fin.last (n+1)` the project completion; start times are real. $\beta^x$ is `Real.rpow`, so the statements that use it assume $\beta>0$. The discount rate and the cash flows are parameters of the objective, not fields of the project.
-- source:
--   Neumann, Schwindt & Zimmermann, Project Scheduling with Time Windows and Scarce Resources, 2nd ed., Springer 2003, pp. 7–8 (Eq. (1.2.1), Definition 1.3.1), pp. 197–198 (Eq. (3.1.1), time-optimal schedule), p. 203 (net present value objective), p. 333 (problem (3.9.1))

import Mathlib

namespace ProjSchedTW.NetPresentValue

/-- Neumann, Schwindt & Zimmermann, *Project Scheduling with Time Windows and Scarce Resources*,
2nd ed., §1.1–1.2 and §3.1 (pp. 1–8, 197–198). A project of the time-constrained problem
`PS∞|temp, d̄|f` (no resource constraints): activities `V = {0, 1, …, n+1}` (`Fin (n + 2)`,
`n ≥ 1`; `0` is the project beginning, `Fin.last (n+1)` the project completion), a project
network with arc set `E` and integer arc weights `δ i j`, integer durations `p i` (zero for the
two fictitious activities, positive for the real activities `1, …, n`), and a prescribed maximum
project duration `d̄ ∈ ℕ`. As §3.1 prescribes, the deadline `S_{n+1} ≤ d̄` (3.1.1) is part of the
network: `E` contains the backward arc `⟨n+1, 0⟩` with weight `δ_{n+1,0} = −d̄`. -/
structure Project (n : ℕ) where
  /-- The arc set `E` of the project network `N`. -/
  E : Finset (Fin (n + 2) × Fin (n + 2))
  /-- The arc weights `δ_ij` (only their values on arcs of `E` matter). -/
  δ : Fin (n + 2) → Fin (n + 2) → ℤ
  /-- The durations `p_i`. -/
  p : Fin (n + 2) → ℕ
  /-- The prescribed maximum project duration `d̄ ∈ ℕ` of (3.1.1). -/
  dbar : ℕ
  /-- There is at least one real activity (`n ≥ 1`, §1.1). -/
  one_le_n : 1 ≤ n
  /-- The network has no loops. -/
  no_loop : ∀ e ∈ E, e.1 ≠ e.2
  /-- `p_0 = 0`. -/
  p_zero : p 0 = 0
  /-- `p_{n+1} = 0`. -/
  p_last : p (Fin.last (n + 1)) = 0
  /-- `p_i > 0` for the real activities `i = 1, …, n`. -/
  p_pos : ∀ i : Fin (n + 2), i ≠ 0 → i ≠ Fin.last (n + 1) → 0 < p i
  /-- §3.1 (p. 197): the network contains the backward arc `⟨n+1, 0⟩` … -/
  back_arc : (Fin.last (n + 1), 0) ∈ E
  /-- … weighted by `δ_{n+1,0} = −d̄`, which encodes `S_{n+1} ≤ d̄`. -/
  back_weight : δ (Fin.last (n + 1)) 0 = -(dbar : ℤ)

variable {n : ℕ}

/-- Definition 1.3.1 and Eq. (1.2.1), with (3.1.1) through the backward arc (p. 198): the
time-feasible region `S_T`, i.e. the vectors `S = (S_0, …, S_{n+1})` of real start times with
`S_0 = 0`, `S_i ≥ 0` and `S_j − S_i ≥ δ_ij` for every arc `⟨i, j⟩ ∈ E`. -/
def timeFeasibleSet (P : Project n) : Set (Fin (n + 2) → ℝ) :=
  {S | S 0 = 0 ∧ (∀ i, 0 ≤ S i) ∧ ∀ e ∈ P.E, (P.δ e.1 e.2 : ℝ) ≤ S e.2 - S e.1}

/-- §3.1 (p. 203): the net present value objective `−∑ c_i^F β^{C_i}`, i.e.
`f(S) = −∑_{i ∈ V} c_i^F β^{S_i + p_i}` with discount rate `β` and cash flows `c_i^F ∈ ℝ` occurring
at the completion times `C_i = S_i + p_i`. The power `β^x` with real exponent is `Real.rpow`. -/
noncomputable def npvObjective (P : Project n) (β : ℝ) (c : Fin (n + 2) → ℝ)
    (S : Fin (n + 2) → ℝ) : ℝ :=
  -∑ i, c i * β ^ (S i + (P.p i : ℝ))

/-- §3.1 (p. 198) with problem (3.9.1) (p. 333): `S` is a time-optimal schedule for
`PS∞|temp, d̄| −∑ c_i^F β^{C_i}`, i.e. `S ∈ S_T` and `f(S) ≤ f(S')` for every `S' ∈ S_T`. -/
def IsTimeOptimal (P : Project n) (β : ℝ) (c : Fin (n + 2) → ℝ) (S : Fin (n + 2) → ℝ) :
    Prop :=
  S ∈ timeFeasibleSet P ∧ ∀ S' ∈ timeFeasibleSet P, npvObjective P β c S ≤ npvObjective P β c S'

/-- A directed walk in the project network `N` from `i` to `j` of length `w` (the sum of the arc
weights `δ` along the walk); the empty walk from `i` to `i` has length `0`. -/
inductive WalkLength (P : Project n) : Fin (n + 2) → Fin (n + 2) → ℤ → Prop
  | refl (i : Fin (n + 2)) : WalkLength P i i 0
  | step {i j l : Fin (n + 2)} {w : ℤ} :
      WalkLength P i j w → (j, l) ∈ P.E → WalkLength P i l (w + P.δ j l)

end ProjSchedTW.NetPresentValue


