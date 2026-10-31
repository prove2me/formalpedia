-- Prove2me | Definitions.Def_MultiwaySoS_Algorithm
-- name    : MultiwaySoS_Algorithm
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:18:00.861722+00:00
-- url     : https://prove2.me/theorems/7f3233f7-775f-4981-9bfb-6943a7e3c593
-- title:
--   Algorithm 2 — the Sum-of-Squares algorithm with virtual and true queues
-- statement:
--   This module defines Algorithm 2 (p.21) with the quantities of §5 (pp.19–20).
--
--   1. **State.** $Y_{im}$ counts units of type $i$ committed to configuration $m$; $\mathscr X_m$ counts virtual matches and $X_m$ true matches of $m$. Initially all are $0$.
--   2. **Queues** ((3)–(4)). The true queue is $Q_{im}=Y_{im}-X_mM_{im}$ and the virtual queue is $\mathscr Q_{im}=Y_{im}-\mathscr X_mM_{im}$.
--   3. **Potential** ((5), (7)). For a cyclic order $\sigma_m=(\sigma_m(1),\dots,\sigma_m(\ell_m))$ of $\mathcal I(m)$,
--   $$\Phi_m(\mathscr Q_m)=(\mathscr Q_{\sigma_m(1)m}-\mathscr Q_{\sigma_m(\ell_m)m})^2+\sum_{k=2}^{\ell_m}(\mathscr Q_{\sigma_m(k)m}-\mathscr Q_{\sigma_m(k-1)m})^2,\qquad\Phi(\mathscr Q)=\sum_{m\in\mathcal M_+}\Phi_m(\mathscr Q_m).$$
--   4. **Virtual feasibility** ((9)). A virtual match is executed when the committed type is online-nonqueueable, or when $m$ has no online-nonqueueable type and $\mathscr Q_m+e_i\ge M_m$ coordinatewise.
--   5. **Change of potential** ((8)). $\Delta\Phi_m(\mathscr Q_m,i)=\Phi_m(\mathscr Q^\prime_m)-\Phi_m(\mathscr Q_m)$ with $\mathscr Q^\prime_m=\mathscr Q_m+e_i-M_m$ after a virtual match and $\mathscr Q_m+e_i$ otherwise.
--   6. **True feasibility** ((10)). A true match of $m$ is infeasible if some offline $i^\prime\in\mathcal I(m)$ has $\bar\lambda_{i^\prime}T<M_{i^\prime m}+\sum_{m^\prime}X_{m^\prime}M_{i^\prime m^\prime}$, or some online $i^\prime\in\mathcal I(m)$ has $Q_{i^\prime m}+\mathbb 1\{i^\prime=i\}<M_{i^\prime m}$.
--   7. **Algorithm 2.** At each time $t$ the arriving unit of type $I^t$ is irrevocably committed to a configuration $m^t\in\mathcal M_+$ containing $I^t$ that minimizes $\Delta\Phi_m(\mathscr Q^{t-1}_m,I^t)$; $Y_{I^tm^t}$ increases by one; if the virtual match is feasible, $\mathscr X_{m^t}$ increases by one, and if moreover the true match is feasible (tested on $Q^{t-1}$ and $X^{t-1}$), $X_{m^t}$ increases by one.
--
--   The module also defines the run of the algorithm on an arrival sequence, the true reward $\sum_m r_mX^t_m$, the virtual reward $\sum_m r_m\mathscr X^t_m$ and the arrival counts $A^t_i=\sum_{s=1}^t\mathbb 1\{I^s=i\}$.
--
--   **Formalization Note** The arg min is resolved by a commit rule `pick t s i`; `IsArgminRule` says that it returns a minimizer among the configurations of $\mathcal M_+$ containing $i$ whenever there is one, and every theorem quantifies over all such rules (the paper's ties are arbitrary). The cyclic order of $m$ is a list `σ m` containing each type of $\mathcal I(m)$ once. Time is $1$-based (`run … arr 0` is the initial state); the offline inventory $\bar\lambda_iT$ is a parameter `cap i`. The second line of (10) prints $M_{im}$, read as $M_{i^\prime m}$ (both are $1$).
-- source:
--   Gupta, Greedy Algorithm for Multiway Matching with Bounded Regret, arXiv:2112.04622v3, §5, (3)–(5), (7)–(10), pp.19–20; Algorithm 2, p.21; A^t, p.15

import Mathlib
import Definitions.Def_MultiwaySoS_Model

namespace MultiwaySoS

/-! # The Sum-of-Squares algorithm (Algorithm 2)

Gupta, arXiv:2112.04622v3, §5, pp.18–21: queue lengths (3)–(4), the potential (5), (7), the
change of potential (8), `virtual_feasible` (9), `true_feasible` (10) and Algorithm 2 (p.21).

**Formalization Note.** Time is 1-based: the arrival at time `t ∈ [1, T]` is `arr t`, and
`run … arr t` is the state after the arrivals `arr 1, …, arr t` (`run … arr 0` is the initial
state). Counters `Y`, `X̂` (`Xv`), `X` are natural numbers, queue lengths are integers. The arg min
of Algorithm 2 is resolved by a *commit rule* `pick t s i` (the configuration chosen for an arrival
of type `i` at time `t` in state `s`); theorems quantify over every commit rule that returns a
minimizer (`IsArgminRule`), which is the paper's arbitrary tie-breaking. -/

variable {n d : ℕ}

/-- The state of Algorithm 2: `Y i m = Y_im` (units of type `i` committed to `m`), `Xv m = 𝒳_m`
(virtual matches of `m`) and `X m = X_m` (true matches of `m`) (§5, p.19). -/
structure State (n d : ℕ) where
  Y : Fin n → Fin d → ℕ
  Xv : Fin d → ℕ
  X : Fin d → ℕ

/-- The initial state: `X⁰ = 𝒳⁰ = 0`, `Y⁰ = 0` (Algorithm 2, "Initialize"). -/
def State.init : State n d :=
  ⟨fun _ _ => 0, fun _ => 0, fun _ => 0⟩

/-- The virtual queue length `𝒬_im = Y_im − 𝒳_m M_im` ((4), p.19). -/
def State.Qv (I : Instance n d) (s : State n d) (i : Fin n) (m : Fin d) : ℤ :=
  (s.Y i m : ℤ) - (s.Xv m : ℤ) * I.Mz i m

/-- The true queue length `Q_im = Y_im − X_m M_im` ((3), p.19). -/
def State.Qt (I : Instance n d) (s : State n d) (i : Fin n) (m : Fin d) : ℤ :=
  (s.Y i m : ℤ) - (s.X m : ℤ) * I.Mz i m

/-- `σ` is a family of cyclic orders: `σ m` lists each resource type of `I(m)` exactly once
(the permutation `σ_m` of `I(m)` in (5), p.19, "an arbitrary permutation of I(m) that is fixed
throughout the execution of the algorithm"). -/
def IsCyclicOrder (I : Instance n d) (σ : Fin d → List (Fin n)) : Prop :=
  ∀ m, (σ m).Nodup ∧ ∀ i, i ∈ σ m ↔ i ∈ I.conf m

/-- The cyclic sum-of-squares potential (5), p.19, of a queue vector `q` along the list
`l = [σ(1), …, σ(ℓ)]`:
`(q_{σ(1)} − q_{σ(ℓ)})² + ∑_{k=2}^{ℓ} (q_{σ(k)} − q_{σ(k−1)})²`.

**Formalization Note.** `l.rotate (ℓ − 1) = [σ(ℓ), σ(1), …, σ(ℓ−1)]`, so zipping `l` with it pairs
each `σ(k)` with its cyclic predecessor. For `ℓ = 1` the single term is `0`; for `ℓ = 0` the sum
is empty. -/
def phiM (l : List (Fin n)) (q : Fin n → ℤ) : ℤ :=
  ((l.zip (l.rotate (l.length - 1))).map (fun p => (q p.1 - q p.2) ^ 2)).sum

/-- The overall potential `Φ(𝒬) = ∑_{m ∈ M₊} Φ_m(𝒬_m)` ((7), p.20), for a queue array
`Q i m` and the basis `B = M₊`. -/
def Phi (B : Finset (Fin d)) (σ : Fin d → List (Fin n)) (Q : Fin n → Fin d → ℤ) : ℤ :=
  ∑ m ∈ B, phiM (σ m) (fun i => Q i m)

/-- `virtual_feasible(m, 𝒬_m, i)` ((9), p.20): true if `i ∈ I^on-nq`, or if `m` contains no
online-nonqueueable type and `𝒬_m + e_i ≥ M_m` coordinatewise; false otherwise. -/
def VirtualFeasible (I : Instance n d) (m : Fin d) (q : Fin n → ℤ) (i : Fin n) : Prop :=
  I.kind i = Kind.onNQ ∨
    ((∀ j ∈ I.conf m, I.kind j ≠ Kind.onNQ) ∧
      ∀ j, I.Mz j m ≤ q j + (if j = i then 1 else 0))

/-- The virtual queue vector `𝒬'_m` after committing a unit of type `i` to `m` ((8), p.20):
`𝒬_m + e_i − M_m` if `virtual_feasible(m, 𝒬_m, i)`, and `𝒬_m + e_i` otherwise. -/
noncomputable def nextVirtual (I : Instance n d) (m : Fin d) (q : Fin n → ℤ) (i : Fin n) :
    Fin n → ℤ := by
  classical
  exact if VirtualFeasible I m q i then fun j => q j + (if j = i then 1 else 0) - I.Mz j m
    else fun j => q j + (if j = i then 1 else 0)

/-- `ΔΦ_m(𝒬_m, i) = Φ_m(𝒬'_m) − Φ_m(𝒬_m)` ((8), p.20), with `σm` the cyclic order of `m`. -/
noncomputable def deltaPhi (I : Instance n d) (σm : List (Fin n)) (m : Fin d) (q : Fin n → ℤ)
    (i : Fin n) : ℤ :=
  phiM σm (nextVirtual I m q i) - phiM σm q

/-- `true_feasible(m, Q_m, X, i)` ((10), p.20), with `cap i' = λ̄_{i'} T` the inventory of the
offline type `i'`: false if some offline `i' ∈ I(m)` has `λ̄_{i'} T < M_{i'm} + ∑_{m'} X_{m'} M_{i'm'}`,
false if some online `i' ∈ I(m)` has `Q_{i'm} + 1{i' = i} < M_{i'm}`, true otherwise.

**Formalization Note.** The second line of (10) prints `M_im`; it is read as `M_{i'm}` (both are `1`
for `i, i' ∈ I(m)`). `I^on = I^on-q ∪ I^on-nq` is "not offline". -/
def TrueFeasible (I : Instance n d) (cap : Fin n → ℝ) (m : Fin d) (qt : Fin n → ℤ)
    (X : Fin d → ℕ) (i : Fin n) : Prop :=
  (∀ i' ∈ I.conf m, I.kind i' = Kind.off → I.M i' m + ∑ m', (X m' : ℝ) * I.M i' m' ≤ cap i') ∧
  (∀ i' ∈ I.conf m, I.kind i' ≠ Kind.off → I.Mz i' m ≤ qt i' + (if i' = i then 1 else 0))

/-- `pick` is an arg-min commit rule for Algorithm 2 with basis `B` and cyclic orders `σ`: whenever
some configuration of `B` contains the arriving type `i`, `pick t s i` is such a configuration and
minimizes `ΔΦ_m(𝒬_m, i)` over them (Algorithm 2, p.21,
`m^t = arg min_m {ΔΦ_m(𝒬^{t−1}_m, I^t) | m ∈ M₊, I^t ∈ I(m)}`). The rule may depend on the time and
the whole state; this is the paper's arbitrary tie-breaking. -/
def IsArgminRule (I : Instance n d) (B : Finset (Fin d)) (σ : Fin d → List (Fin n))
    (pick : ℕ → State n d → Fin n → Fin d) : Prop :=
  ∀ t s i, (∃ m ∈ B, i ∈ I.conf m) →
    pick t s i ∈ B ∧ i ∈ I.conf (pick t s i) ∧
    ∀ m ∈ B, i ∈ I.conf m →
      deltaPhi I (σ (pick t s i)) (pick t s i) (fun j => s.Qv I j (pick t s i)) i ≤
        deltaPhi I (σ m) m (fun j => s.Qv I j m) i

/-- One iteration of the loop of Algorithm 2 (p.21) at time `t`, in state `s` (the state at time
`t − 1`), for an arrival of type `i`:
1. `m^t := pick t s i`;
2. `Y_{i m^t} += 1`;
3. if `virtual_feasible(m^t, 𝒬^{t−1}_{m^t}, i)`: `𝒳_{m^t} += 1`, and if moreover
   `true_feasible(m^t, Q^{t−1}_{m^t}, X^{t−1}, i)`: `X_{m^t} += 1`;
4. everything else is unchanged.

Both feasibility tests read the state before this step's commitment. -/
noncomputable def step (I : Instance n d) (cap : Fin n → ℝ)
    (pick : ℕ → State n d → Fin n → Fin d) (t : ℕ) (s : State n d) (i : Fin n) : State n d := by
  classical
  exact
    let m := pick t s i
    let Y' := Function.update s.Y i (Function.update (s.Y i) m (s.Y i m + 1))
    if VirtualFeasible I m (fun j => s.Qv I j m) i then
      { Y := Y'
        Xv := Function.update s.Xv m (s.Xv m + 1)
        X := if TrueFeasible I cap m (fun j => s.Qt I j m) s.X i then
            Function.update s.X m (s.X m + 1) else s.X }
    else
      { Y := Y', Xv := s.Xv, X := s.X }

/-- The run of Algorithm 2 on the arrival sequence `arr` (`arr t = I^t` for `t ≥ 1`):
`run … arr t` is the state after time `t`. -/
noncomputable def run (I : Instance n d) (cap : Fin n → ℝ)
    (pick : ℕ → State n d → Fin n → Fin d) (arr : ℕ → Fin n) : ℕ → State n d
  | 0 => State.init
  | t + 1 => step I cap pick (t + 1) (run I cap pick arr t) (arr (t + 1))

/-- The true reward `∑_m r_m X^t_m` collected by time `t` (Theorem 2, p.18). -/
noncomputable def trueReward (I : Instance n d) (cap : Fin n → ℝ)
    (pick : ℕ → State n d → Fin n → Fin d) (arr : ℕ → Fin n) (t : ℕ) : ℝ :=
  ∑ m, I.r m * ((run I cap pick arr t).X m : ℝ)

/-- The virtual reward `∑_m r_m 𝒳^t_m` (Lemmas 6, 7, p.23). -/
noncomputable def virtualReward (I : Instance n d) (cap : Fin n → ℝ)
    (pick : ℕ → State n d → Fin n → Fin d) (arr : ℕ → Fin n) (t : ℕ) : ℝ :=
  ∑ m, I.r m * ((run I cap pick arr t).Xv m : ℝ)

/-- The cumulative arrival count `A^t_i = ∑_{s=1}^{t} 1{I^s = i}` (§4, p.15). -/
noncomputable def arrCount (arr : ℕ → Fin n) (t : ℕ) (i : Fin n) : ℝ :=
  ((Finset.Icc 1 t).filter (fun s => arr s = i)).card

end MultiwaySoS


