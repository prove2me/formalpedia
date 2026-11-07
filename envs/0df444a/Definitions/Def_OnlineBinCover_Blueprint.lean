-- Prove2me | Definitions.Def_OnlineBinCover_Blueprint
-- name    : OnlineBinCover_Blueprint
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:50:36.285933+00:00
-- url     : https://prove2.me/theorems/1b89bc7b-dd3e-4ecb-9491-a9676f896a33
-- title:
--   The blueprint, the item classes of Definition 3.1 and the assignment phase
-- statement:
--   Let $\sigma$ be the arrival order; the **sample** of size $k$ is the set $I_p$ of items arriving at times $0,\dots,k-1$, a uniform $k$-subset when $\sigma$ is uniform.
--
--   1. **Choice of $\varepsilon$.** $\varepsilon=2^{\lfloor\log_2(p/\mathrm{vol}(I_p))^{1/24}\rfloor}$, i.e. $(p/\mathrm{vol}(I_p))^{1/24}$ rounded down to a power of two.
--   2. **Definition 3.1.** The classes $L_p,M_p,S_p$ and groups of the sample define the classes of every input item: large if it is at or above (in rank order) the boundary item defining $t_L$, medium if it is below that item and at or above the boundary item defining $t_M$, small otherwise; in the all-large case every item is large.
--   3. **Blueprint.** For an LP solution $x$ on the sample, each configuration $C$ gets $z_C=\lfloor\lfloor x_C\rfloor/p\rfloor$ bins; $\mathrm{ALG}_{BP}=\sum_Cz_C$. A bin of configuration $C$ has one L-slot of demand $r_j$ for each rounded item of group $j$ in $C$ and one S-slot of demand $d(C)$.
--   4. **Assignment phase (§4).** A large item goes to a vacant L-slot of largest demand not exceeding its size, if any. A medium or small item goes to the active S-slot: the S-slot of least positive demand whose demand is not yet met. Ties are broken by arbitrary priorities $\mathrm{prio}_L,\mathrm{prio}_S$; an item with no slot goes to an overflow bin outside the blueprint.
--   5. The value of the phase is the number of **covered blueprint bins**: bins all of whose L-slots are filled and whose S-slot load reaches $d(C)$. Each is covered, so this is a lower bound on the number of covered bins for any placement of the overflow items.
--
--   These are the procedures of the order-oblivious algorithm and of Algorithm 3.
--
--   **Formalization Note** At an empty sample the conventions $p/0=0$ and $\log_2 0=0$ give $\varepsilon=1$. Statements quantify over all priorities, so none depends on the tie-breaking.
-- source:
--   Ayyadevara, Khan, Kumar, Sreenivas, Optimal Online Bin Covering across Stochastic Models, STOC 2027 submission (manuscript sha256 e77e556c…), §3, p.8 (PDF p.9), Definition 3.1 and "Blueprint solution"; §4, p.11 (PDF p.12); Algorithm 2, p.18; Section B.4, p.26

import Mathlib
import Definitions.Def_DynamicOnlineLP_DLA_Instance
import Definitions.Def_OnlineBinCover_ConfigLP

namespace OnlineBinCover

/-!
# The blueprint, the item classes of Definition 3.1 and the assignment phase

Ayyadevara, Khan, Kumar, Sreenivas, *Optimal Online Bin Covering across Stochastic Models*,
STOC 2027 submission (manuscript sha256 e77e556c…), §3 p.8 (Definition 3.1, "Blueprint solution"),
§4 p.11 (the order-oblivious sampling and assignment phases), Algorithm 2 p.18 and Section B.4 p.26
(the choice of `ε`).

**Formalization Note.**
* *Sample.* The sample of size `k` under arrival order `σ` is the set of items arriving at times
  `0, …, k − 1`, i.e. `σ` of the published `firstTimes n k`; for a uniform `σ` it is a uniform
  `k`-subset.
* *Choice of ε.* `epsChoice p v = 2^{⌊log₂ (p/v)^{1/24}⌋}` ("rounding `(p/vol(Ip))^{1/24}` down to
  a power of two"). At `v = 0` Lean's conventions give `ε = 1`; this happens only for an empty
  sample.
* *Classes of the whole input (Definition 3.1).* An item is large if it is at or above (in rank
  order, ties by label) some large sample item, i.e. up to and including the boundary item defining
  `t_L`; medium if not large and at or above some large or medium sample item; small otherwise. In
  the all-large case every item is large.
* *Blueprint.* For each configuration `C` of the LP solution `x` there are
  `z_C = ⌊⌊x_C⌋ / p⌋` blueprint bins `(C, k)`, `k < z_C`; `ALGBP = ∑_C z_C`. Bin `(C, k)` has `C j`
  L-slots `((C, k), j, u)`, `u < C j`, of demand `r_j` (the rounded size of group `j`) and one S-slot
  of demand `d(C)`.
* *Assignment rules (§4, p.11).* A large item goes to a vacant L-slot of largest demand not
  exceeding its size, ties broken by least `prioL`; with no such slot it goes to an overflow bin
  outside the blueprint. A medium or small item goes to the active S-slot: among the S-slots of
  positive demand whose demand is not yet met, the one of least demand, ties by least `prioS`
  (processing the S-slots in increasing order of demand and advancing as soon as a demand is met);
  with no such slot it goes to an overflow bin. `prioL`, `prioS` are arbitrary and statements
  quantify over them, so no statement depends on the tie-breaking.
* *Count.* `phaseRun` returns the number of covered **blueprint** bins: bins all of whose L-slots
  are filled and whose S-slot load reaches `d(C)`. Each is a covered bin (load at least
  `vol(C) + d(C) ≥ 1`), so this is a lower bound for every placement of the overflow items.
-/

open Finset

/-- The sample of size `k`: the items arriving at times `0, …, k − 1`. -/
noncomputable def smp {n : ℕ} (σ : Equiv.Perm (Fin n)) (k : ℕ) : Finset (Fin n) :=
  (DynamicOnlineLP.DLA.firstTimes n k).image σ

/-- `ε = 2^{⌊log₂ (p/v)^{1/24}⌋}` (Section B.4, p.26). -/
noncomputable def epsChoice (p v : ℝ) : ℝ :=
  (2 : ℝ) ^ (⌊Real.logb 2 ((p / v) ^ ((1 : ℝ) / 24))⌋)

/-- The three item classes. -/
inductive ItemClass where
  | large
  | medium
  | small
  deriving DecidableEq

/-- The class of an input item from the sample `J` (Definition 3.1; all large in the all-large
case). -/
noncomputable def classOf {n : ℕ} (s : Fin n → ℝ) (J : Finset (Fin n)) (ε : ℝ) (i : Fin n) :
    ItemClass :=
  by classical exact
    if ¬ ThreeClass s J ε then ItemClass.large
    else if ∃ b ∈ largeOf s J ε, b = i ∨ before s i b then ItemClass.large
    else if ∃ b ∈ largeOf s J ε ∪ medOf s J ε, b = i ∨ before s i b then ItemClass.medium
    else ItemClass.small

/-- A blueprint bin: a configuration and a copy index. -/
abbrev Bin (K : ℕ) := (Fin K → ℕ) × ℕ

/-- An L-slot: a bin, a group and a copy index. -/
abbrev LSlot (K : ℕ) := Bin K × Fin K × ℕ

/-- `z_C = ⌊⌊x_C⌋ / p⌋`. -/
noncomputable def zC {K : ℕ} (x : (Fin K → ℕ) →₀ ℝ) (p : ℝ) (C : Fin K → ℕ) : ℕ :=
  ⌊(⌊x C⌋₊ : ℝ) / p⌋₊

/-- `ALGBP = ∑_C z_C`, the number of blueprint bins. -/
noncomputable def ALGBP {K : ℕ} (x : (Fin K → ℕ) →₀ ℝ) (p : ℝ) : ℕ :=
  ∑ C ∈ x.support, zC x p C

/-- The blueprint bins. -/
noncomputable def bpBins {K : ℕ} (x : (Fin K → ℕ) →₀ ℝ) (p : ℝ) : Finset (Bin K) :=
  x.support.biUnion (fun C => (range (zC x p C)).image (fun k => (C, k)))

/-- The L-slots of the blueprint. -/
noncomputable def bpLSlots {K : ℕ} (x : (Fin K → ℕ) →₀ ℝ) (p : ℝ) : Finset (LSlot K) :=
  (bpBins x p).biUnion
    (fun b => univ.biUnion (fun j : Fin K => (range (b.1 j)).image (fun u => (b, j, u))))

/-- The assignment state: the filled L-slots and the load of each S-slot. -/
structure AState (K : ℕ) where
  filled : Finset (LSlot K)
  sload : Bin K → ℝ

/-- An element of `F` minimizing `f`, if `F` is nonempty. -/
noncomputable def pickMin {β γ : Type*} [LinearOrder γ] (F : Finset β) (f : β → γ) :
    Option β :=
  if h : F.Nonempty then some (Classical.choose (F.exists_min_image f h)) else none

/-- The large-item rule: a vacant L-slot of largest demand not exceeding the size `w`. -/
noncomputable def largeStep {K : ℕ} (size : Fin K → ℝ) (slots : Finset (LSlot K))
    (prioL : LSlot K → ℕ) (st : AState K) (w : ℝ) : AState K :=
  by classical exact
    let cands := slots.filter (fun sl => sl ∉ st.filled ∧ size sl.2.1 ≤ w)
    if h : cands.Nonempty then
      let best := cands.filter (fun sl => size sl.2.1 = cands.sup' h (fun sl => size sl.2.1))
      match pickMin best prioL with
      | some sl => { st with filled := insert sl st.filled }
      | none => st
    else st

/-- The medium/small-item rule: the active S-slot (least demand among unmet positive demands). -/
noncomputable def smallStep {K : ℕ} (size : Fin K → ℝ) (bins : Finset (Bin K))
    (prioS : Bin K → ℕ) (st : AState K) (w : ℝ) : AState K :=
  by classical exact
    let active := bins.filter (fun b => 0 < demand size b.1 ∧ st.sload b < demand size b.1)
    match pickMin active (fun b => toLex (demand size b.1, prioS b)) with
    | some b => { st with sload := Function.update st.sload b (st.sload b + w) }
    | none => st

/-- One step of the assignment phase for item `i`. -/
noncomputable def assignStep {n : ℕ} (s : Fin n → ℝ) (J : Finset (Fin n)) (ε p : ℝ)
    (x : (Fin (Kof ε) → ℕ) →₀ ℝ) (prioL : LSlot (Kof ε) → ℕ) (prioS : Bin (Kof ε) → ℕ)
    (st : AState (Kof ε)) (i : Fin n) : AState (Kof ε) :=
  match classOf s J ε i with
  | ItemClass.large => largeStep (rsize s J ε) (bpLSlots x p) prioL st (s i)
  | _ => smallStep (rsize s J ε) (bpBins x p) prioS st (s i)

/-- The number of covered blueprint bins in an assignment state. -/
noncomputable def bpCovered {K : ℕ} (size : Fin K → ℝ) (x : (Fin K → ℕ) →₀ ℝ) (p : ℝ)
    (st : AState K) : ℕ :=
  by classical exact
    ((bpBins x p).filter (fun b => (∀ j : Fin K, ∀ u < b.1 j, (b, j, u) ∈ st.filled) ∧
      demand size b.1 ≤ st.sload b)).card

/-- The assignment phase: classes from the sample `J` and `ε`, the blueprint of `x` with fraction
`p`, and the remaining items arriving in the order `rest`; the number of covered blueprint bins. -/
noncomputable def phaseRun {n : ℕ} (s : Fin n → ℝ) (J : Finset (Fin n)) (ε p : ℝ)
    (x : (Fin (Kof ε) → ℕ) →₀ ℝ) (prioL : LSlot (Kof ε) → ℕ) (prioS : Bin (Kof ε) → ℕ)
    (rest : List (Fin n)) : ℕ :=
  bpCovered (rsize s J ε) x p
    (rest.foldl (assignStep s J ε p x prioL prioS) ⟨∅, fun _ => 0⟩)

end OnlineBinCover


