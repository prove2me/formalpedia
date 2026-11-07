-- Prove2me | Definitions.Def_OnlineBinCover_Epochs
-- name    : OnlineBinCover_Epochs
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:53:19.639541+00:00
-- url     : https://prove2.me/theorems/eedf3ba3-6fa1-4a95-9cb1-44fbc64f0d7f
-- title:
--   Algorithm 4: epochs when the input length is unknown
-- statement:
--   Let $\sigma$ be the arrival order.
--
--   1. **Endpoints (13).** $n_1=1$ and $n_{i+1}=n_i+\lceil n_i/\max\{1,V_i\}^{1/10}\rceil$, where $V_i=\mathrm{vol}(I_\sigma(n_i))$ is the volume of the first $n_i$ arrivals. Epoch $E_i$ consists of the arrivals at positions $n_{i-1}+1,\dots,n_i$ ($n_0=0$); its planned length is $|E_i|=n_i-n_{i-1}$.
--   2. $m$ is the number of epochs, the least $i$ with $n_i\ge n$, and $j=\min\{i\in[m]:n_i\ge n/\mathrm{vol}(I)^{1/20}\}$; $E_1,\dots,E_j$ are the initial epochs and $E_{j+1},\dots,E_m$ the later epochs.
--   3. Epoch $E_i$, $i\ge2$, runs a fresh instance of Algorithm 3 told the input length $n_i-n_{i-1}$ on its own arrivals, with new bins; $A_{ro}(E_i)$ is its number of covered blueprint bins. The first epoch is one item in its own bin.
--
--   These are the epochs of Lemmas D.3, D.5 and D.6.
--
--   **Formalization Note** The last epoch may be cut by the end of the input; for every other epoch the planned length is the actual length. If the set defining $j$ is empty, $j:=m$ (it is nonempty when $\mathrm{vol}(I)\ge1$).
-- source:
--   Ayyadevara, Khan, Kumar, Sreenivas, Optimal Online Bin Covering across Stochastic Models, STOC 2027 submission (manuscript sha256 e77e556c…), App. D.2, pp.34–35 (PDF pp.35–36), (13) and Algorithm 4

import Mathlib
import Definitions.Def_OnlineBinCover_Alg3

namespace OnlineBinCover

/-!
# Algorithm 4: epochs when the input length is unknown

Ayyadevara, Khan, Kumar, Sreenivas, *Optimal Online Bin Covering across Stochastic Models*,
STOC 2027 submission (manuscript sha256 e77e556c…), App. D.2, pp.34–35: the epoch endpoints (13),
Algorithm 4, the number of epochs `m` and the index `j` of the last initial epoch.

The arrival order is `σ` (item `σ t` arrives at time `t`); `y = s ∘ σ` is the arrival sequence of
sizes.

**Formalization Note.**
* *(13).* `epEnd y i` is the planned last position `n_i` (`1`-based) of epoch `E_i`, `i ≥ 1`:
  `n_1 = 1`, `n_{i+1} = n_i + ⌈n_i / max{1, V_i}^{1/10}⌉` with `V_i = vol(Iσ(n_i))` the volume of
  the first `n_i` arrivals (all of them if `n_i > n`); `epEnd y 0 = 0`. Epoch `E_i` consists of the
  arrivals at `0`-based positions `n_{i−1}, …, n_i − 1`; `epochLen` is its planned length
  `n_i − n_{i−1}`, which is its actual length for every epoch but the last.
* `numEpochs y = m`, the least `i` with `n_i ≥ n` (the epoch holding the last arrival).
* `jInit y = j = min {i ∈ [m] : n_i ≥ n / vol(I)^{1/20}}` (`m` if the set is empty); `vol(I)` is
  the volume of `y`, which equals that of `s`. Epochs `E_{j+1}, …, E_m` are the later epochs.
* Epoch `E_i` with `i ≥ 2` runs a fresh instance of Algorithm 3 (`alg3`) told the input length
  `n_i − n_{i−1}` on that epoch's arrival list, with its own bins; `epochRun` is its number of
  covered blueprint bins, the analysis quantity `A_ro(E_i)` of p.37. The first epoch (one item in
  its own bin) is not an Algorithm 3 instance and `epochRun` is not used for it.
-/

open Finset

/-- `vol(Iσ(t))`: the volume of the first `t` arrivals of the size sequence `y`. -/
noncomputable def arrVol {n : ℕ} (y : Fin n → ℝ) (t : ℕ) : ℝ :=
  ∑ u ∈ univ.filter (fun u : Fin n => u.val < t), y u

/-- The planned epoch endpoints `n_i` of (13), with `epEnd y 0 = 0`, `epEnd y 1 = 1`. -/
noncomputable def epEnd {n : ℕ} (y : Fin n → ℝ) : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | i + 2 => epEnd y (i + 1) +
      ⌈(epEnd y (i + 1) : ℝ) / (max 1 (arrVol y (epEnd y (i + 1)))) ^ ((1 : ℝ) / 10)⌉₊

/-- The number of epochs `m`: the least `i` with `n_i ≥ n`. -/
noncomputable def numEpochs {n : ℕ} (y : Fin n → ℝ) : ℕ :=
  by classical exact if h : ∃ i, n ≤ epEnd y i then Nat.find h else 0

/-- `j = min {i ∈ [m] : n_i ≥ n / vol(I)^{1/20}}` (p.34). -/
noncomputable def jInit {n : ℕ} (y : Fin n → ℝ) : ℕ :=
  by classical exact
    let P : ℕ → Prop := fun i => 1 ≤ i ∧ i ≤ numEpochs y ∧
      (n : ℝ) / vol y ^ ((1 : ℝ) / 20) ≤ epEnd y i
    if h : ∃ i, P i then Nat.find h else numEpochs y

/-- The planned length `|E_i| = n_i − n_{i−1}`. -/
noncomputable def epochLen {n : ℕ} (s : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) (i : ℕ) : ℕ :=
  epEnd (s ∘ σ) i - epEnd (s ∘ σ) (i - 1)

/-- The arrival list of epoch `E_i` (cut at the end of the input). -/
noncomputable def epochList {n : ℕ} (s : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) (i : ℕ) :
    List (Fin n) :=
  ((List.ofFn σ).drop (epEnd (s ∘ σ) (i - 1))).take (epochLen s σ i)

/-- The items of epoch `E_i`. -/
noncomputable def epochItems {n : ℕ} (s : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) (i : ℕ) :
    Finset (Fin n) :=
  (epochList s σ i).toFinset

/-- The sample of epoch `E_i`'s Algorithm 3 instance. -/
noncomputable def epochSample {n : ℕ} (s : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) (i : ℕ) :
    Finset (Fin n) :=
  a3Sample s (epochLen s σ i) (epochList s σ i)

/-- The accuracy `ε` of epoch `E_i`'s Algorithm 3 instance. -/
noncomputable def epochEps {n : ℕ} (s : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) (i : ℕ) : ℝ :=
  a3Eps s (epochLen s σ i) (epochList s σ i)

/-- `A_ro(E_i)`: covered blueprint bins of epoch `E_i`'s Algorithm 3 instance (`i ≥ 2`). -/
noncomputable def epochRun {n : ℕ} (s : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) (i : ℕ)
    (x : (Fin (Kof (epochEps s σ i)) → ℕ) →₀ ℝ) (prioL : LSlot (Kof (epochEps s σ i)) → ℕ)
    (prioS : Bin (Kof (epochEps s σ i)) → ℕ) : ℕ :=
  alg3 s (epochLen s σ i) (epochList s σ i) x prioL prioS

end OnlineBinCover


