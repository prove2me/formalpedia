-- Prove2me | Definitions.Def_KServer_race_core
-- name    : KServer_race_core
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-01T15:47:23.828168+00:00
-- url     : https://prove2.me/theorems/25d4c520-0ffd-41aa-ab06-558713f45b46
-- title:
--   The BCR race: sample space, coin-tree measure, and interleaved schedule
-- statement:
--   Fix four level-$w$ chunk systems $A$, $B_L$, $B_R$, $C$ on a metric space $X$ (with common entry $s$, exit $t$, size lower bound $0$, chunk bound $c_B$, total bound $T$, price $p_e$, and chunk count $m_L$), request transformations $G_A, G_L, G_R, G_{TL}, G_{TR}$ from subsets of $X$ to subsets of a target space $Y$, a stopping point, a coin count $\kappa$, and a clamp $\varepsilon > 0$. The race runs the four systems against $\kappa$ size-weighted coins on the product sample space
--   $$\Omega_A \times \Omega_{B_L} \times \Omega_{B_R} \times \Omega_C \times \{0,1\}^\kappa .$$
--   The measure is the product of the four chunk-system measures with a path-dependent coin-tree measure whose per-step left probability is $\max(n_R,\varepsilon)/(\max(n_L,\varepsilon)+\max(n_R,\varepsilon))$, where $n_L, n_R$ are the sizes of the next unconsumed chunks of the two coin-phase systems; the two weights at each step sum to one, so the total mass is one and each atom has positive mass. The schedule plays: first the $m_L$ chunks of $A$ transformed by $G_A$; then $\kappa$ coin steps, where coin $j$ advances the chosen side's next chunk (transformed by $G_L$ or $G_R$) with the other side's current position mapped in as a park set, claiming size $\min(p_L n_L, p_R n_R)$; then the survivor side (the one with the smaller consumed coin-phase size, ties to left) plays its remaining chunks, then the tail system $C$ transformed by $G_{TL}$ or $G_{TR}$ according to the survivor, then padding chunks $\{\mathrm{stop}\}$, with the two phase-transition chunks claiming size zero. A three-tag history function pairs the histories of the constituent systems with the coin-prefix code. Auxiliary lemmas give the branch equations of the assembled chunks, sizes and histories, and show the coin-prefix code determines the coins (hence the consumption counts) below its index. This is the request-schedule skeleton for the coin-race step of the Bansal-Coester-Rabani style $(\log k)^2$ randomized lower bound.
-- source:
--   N. Bansal, M. Elias, A. Gupta, Lower bounds for the randomized k-server conjecture (following Bartal-Bollobas-Mendel style multi-scale constructions); race/coin construction as in the BCR lower bound for metrical task systems, adapted

import Mathlib
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b
import Definitions.Def_KServer_chunk_cond
import Definitions.Def_KServer_chunk_stopping
import Definitions.Def_KServer_shadow
import Definitions.Def_KServer_park_shadow
import Definitions.Def_KServer_shadow2
import Definitions.Def_KServer_race_sched
import Definitions.Def_KServer_race_coin

set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 1600000

namespace KServer

namespace Race

/-! ### The race: data and schedule

The race combines four level-`w` chunk systems on `X` — `A` (the union
phase on the two first thirds), `BL`/`BR` (the coin phase on the two
middle thirds), and `CC` (the tail on the survivor's third) — into one
random request schedule on a larger space `Y`, along `κ` size-weighted
coins.  This file defines the sample space, the measure, the schedule
bookkeeping, the assembled chunks, sizes, and filtration.  Geometry
enters only through the abstract request transformations `GA`, `GL`,
`GR`, `TA`, `TB` and the final point `stopPt`. -/

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
variable {s t : X} {cB T pe : ℝ} {mL : ℕ}

section Core

variable (A BL BR CC : ChunkSystemB X s t 0 cB T pe mL)
variable (GmA GmL GmR GmTL GmTR : Set X → Set Y) (stopPt : Y)
variable (κ : ℕ) (ε : ℝ)

/-- The race sample space. -/
abbrev RΩ := A.Ω × BL.Ω × BR.Ω × CC.Ω × (Fin κ → Bool)

/-- Next left size before coin `j`, given the coin prefix. -/
noncomputable def nextL (ω : RΩ A BL BR CC κ) (j : ℕ) : ℝ :=
  BL.sizeN (cntL ω.2.2.2.2 j) ω.2.1

/-- Next right size before coin `j`. -/
noncomputable def nextR (ω : RΩ A BL BR CC κ) (j : ℕ) : ℝ :=
  BR.sizeN (cntR ω.2.2.2.2 j) ω.2.2.1

/-- The per-step coin weight, as a function of the prefix (for the
coin-tree measure, the sizes are read off the fixed side outcomes). -/
noncomputable def coinW (ωA : A.Ω) (ωL : BL.Ω) (ωR : BR.Ω)
    (j : ℕ) (p : Fin j → Bool) (b : Bool) : ℝ :=
  let nL := BL.sizeN (cntL (fun i : Fin j => p i) j) ωL
  let nR := BR.sizeN (cntR (fun i : Fin j => p i) j) ωR
  if b then probL nL nR ε else probL nR nL ε

/-- The race measure. -/
noncomputable def RP (ω : RΩ A BL BR CC κ) : ℝ :=
  A.P ω.1 * (BL.P ω.2.1 * (BR.P ω.2.2.1 * (CC.P ω.2.2.2.1
    * coinWt (coinW A BL BR ω.1 ω.2.1 ω.2.2.1 (ε := ε)) ω.2.2.2.2)))

theorem RP_pos (hε : 0 < ε) (ω : RΩ A BL BR CC κ) :
    0 < RP A BL BR CC κ ε ω := by
  unfold RP
  have hc : 0 < coinWt (coinW A BL BR ω.1 ω.2.1 ω.2.2.1 (ε := ε))
      ω.2.2.2.2 := by
    refine coinWt_pos (fun j p b => ?_) _
    unfold coinW
    by_cases hb : b
    · rw [hb, if_pos rfl]
      exact probL_pos hε
    · rw [if_neg hb]
      exact probL_pos hε
  have h1 := A.hP ω.1
  have h2 := BL.hP ω.2.1
  have h3 := BR.hP ω.2.2.1
  have h4 := CC.hP ω.2.2.2.1
  positivity

theorem RP_sum (hε : 0 < ε) : ∑ ω : RΩ A BL BR CC κ,
    RP A BL BR CC κ ε ω = 1 := by
  unfold RP
  rw [Fintype.sum_prod_type]
  have h1 : ∀ ωA, ∑ ω2 : BL.Ω × BR.Ω × CC.Ω × (Fin κ → Bool),
      A.P ωA * (BL.P ω2.1 * (BR.P ω2.2.1 * (CC.P ω2.2.2.1
        * coinWt (coinW A BL BR ωA ω2.1 ω2.2.1 (ε := ε)) ω2.2.2.2)))
      = A.P ωA := by
    intro ωA
    have h2 : ∀ ωL, ∑ ω3 : BR.Ω × CC.Ω × (Fin κ → Bool),
        A.P ωA * (BL.P ωL * (BR.P ω3.1 * (CC.P ω3.2.1
          * coinWt (coinW A BL BR ωA ωL ω3.1 (ε := ε)) ω3.2.2)))
        = A.P ωA * BL.P ωL := by
      intro ωL
      have h3 : ∀ ωR, ∑ ω4 : CC.Ω × (Fin κ → Bool),
          A.P ωA * (BL.P ωL * (BR.P ωR * (CC.P ω4.1
            * coinWt (coinW A BL BR ωA ωL ωR (ε := ε)) ω4.2)))
          = A.P ωA * (BL.P ωL * BR.P ωR) := by
        intro ωR
        have h4 : ∀ ωC, ∑ c : Fin κ → Bool,
            A.P ωA * (BL.P ωL * (BR.P ωR * (CC.P ωC
              * coinWt (coinW A BL BR ωA ωL ωR (ε := ε)) c)))
            = A.P ωA * (BL.P ωL * (BR.P ωR * CC.P ωC)) := by
          intro ωC
          have hcsum : ∑ c : Fin κ → Bool,
              coinWt (coinW A BL BR ωA ωL ωR (ε := ε)) c = 1 := by
            refine sum_coinWt fun j p => ?_
            show probL _ _ ε + probL _ _ ε = 1
            exact probL_add_probR _ _ ε hε
          calc ∑ c : Fin κ → Bool, A.P ωA * (BL.P ωL * (BR.P ωR * (CC.P ωC
              * coinWt (coinW A BL BR ωA ωL ωR (ε := ε)) c)))
              = (A.P ωA * (BL.P ωL * (BR.P ωR * CC.P ωC)))
                * ∑ c : Fin κ → Bool,
                  coinWt (coinW A BL BR ωA ωL ωR (ε := ε)) c := by
                rw [Finset.mul_sum]
                exact Finset.sum_congr rfl fun c _ => by ring
            _ = _ := by rw [hcsum, mul_one]
        calc ∑ ω4 : CC.Ω × (Fin κ → Bool), A.P ωA * (BL.P ωL * (BR.P ωR
            * (CC.P ω4.1 * coinWt (coinW A BL BR ωA ωL ωR (ε := ε)) ω4.2)))
            = ∑ ωC, A.P ωA * (BL.P ωL * (BR.P ωR * CC.P ωC)) := by
              rw [Fintype.sum_prod_type]
              exact Finset.sum_congr rfl fun ωC _ => h4 ωC
          _ = A.P ωA * (BL.P ωL * BR.P ωR) := by
              have : ∑ ωC, A.P ωA * (BL.P ωL * (BR.P ωR * CC.P ωC))
                  = (A.P ωA * (BL.P ωL * BR.P ωR)) * ∑ ωC, CC.P ωC := by
                rw [Finset.mul_sum]
                exact Finset.sum_congr rfl fun ωC _ => by ring
              rw [this, CC.hPsum, mul_one]
      calc ∑ ω3 : BR.Ω × CC.Ω × (Fin κ → Bool), A.P ωA * (BL.P ωL
          * (BR.P ω3.1 * (CC.P ω3.2.1
            * coinWt (coinW A BL BR ωA ωL ω3.1 (ε := ε)) ω3.2.2)))
          = ∑ ωR, A.P ωA * (BL.P ωL * BR.P ωR) := by
            rw [Fintype.sum_prod_type]
            exact Finset.sum_congr rfl fun ωR _ => h3 ωR
        _ = A.P ωA * BL.P ωL := by
            have : ∑ ωR, A.P ωA * (BL.P ωL * BR.P ωR)
                = (A.P ωA * BL.P ωL) * ∑ ωR, BR.P ωR := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun ωR _ => by ring
            rw [this, BR.hPsum, mul_one]
    calc ∑ ω2 : BL.Ω × BR.Ω × CC.Ω × (Fin κ → Bool), A.P ωA * (BL.P ω2.1
        * (BR.P ω2.2.1 * (CC.P ω2.2.2.1
          * coinWt (coinW A BL BR ωA ω2.1 ω2.2.1 (ε := ε)) ω2.2.2.2)))
        = ∑ ωL, A.P ωA * BL.P ωL := by
          rw [Fintype.sum_prod_type]
          exact Finset.sum_congr rfl fun ωL _ => h2 ωL
      _ = A.P ωA := by
          have : ∑ ωL, A.P ωA * BL.P ωL = A.P ωA * ∑ ωL, BL.P ωL := by
            rw [Finset.mul_sum]
          rw [this, BL.hPsum, mul_one]
  calc ∑ ωA, ∑ ω2 : BL.Ω × BR.Ω × CC.Ω × (Fin κ → Bool),
      A.P ωA * (BL.P ω2.1 * (BR.P ω2.2.1 * (CC.P ω2.2.2.1
        * coinWt (coinW A BL BR ωA ω2.1 ω2.2.1 (ε := ε)) ω2.2.2.2)))
      = ∑ ωA, A.P ωA := Finset.sum_congr rfl fun ωA _ => h1 ωA
    _ = 1 := A.hPsum

end Core


section Sched

variable (A BL BR CC : ChunkSystemB X s t 0 cB T pe mL)
variable (GmA GmL GmR GmTL GmTR : Set X → Set Y) (stopPt : Y)
variable (κ : ℕ) (ε : ℝ)

/-- Total chunk access. -/
noncomputable def chunkN (C : ChunkSystemB X s t 0 cB T pe mL) (ωC : C.Ω)
    (idx : ℕ) : List (Set X) :=
  if h : idx < C.m then C.chunk ωC ⟨idx, h⟩ else []

/-- The last request set of a side's consumed prefix (defaulting to the
entry `{s}`). -/
noncomputable def lastXset (C : ChunkSystemB X s t 0 cB T pe mL) (ωC : C.Ω)
    (idx : ℕ) : Set X :=
  ((((List.ofFn (C.chunk ωC)).take idx).flatten).getLast?).getD {s}

/-- Consumed left size after all coins. -/
noncomputable def sumL (ω : RΩ A BL BR CC κ) : ℝ :=
  ∑ j : Fin κ, if ω.2.2.2.2 j then nextL A BL BR CC κ ω (j : ℕ) else 0

/-- Consumed right size after all coins. -/
noncomputable def sumR (ω : RΩ A BL BR CC κ) : ℝ :=
  ∑ j : Fin κ, if ω.2.2.2.2 j then 0 else nextR A BL BR CC κ ω (j : ℕ)

open Classical in
/-- The survivor: the side with the smaller consumed size (ties to left). -/
noncomputable def survL (ω : RΩ A BL BR CC κ) : Bool :=
  if sumL A BL BR CC κ ω ≤ sumR A BL BR CC κ ω then true else false

/-- The number of remaining survivor chunks after the kill. -/
noncomputable def remCnt (ω : RΩ A BL BR CC κ) : ℕ :=
  if survL A BL BR CC κ ω then BL.m - cntL ω.2.2.2.2 κ
  else BR.m - cntR ω.2.2.2.2 κ

/-- The race chunk count. -/
def mrace : ℕ := A.m + κ + max BL.m BR.m + CC.m

open Classical in
/-- The left park before coin `j`. -/
noncomputable def parkL (ω : RΩ A BL BR CC κ) (j : ℕ) : Set Y :=
  GmL (lastXset BL ω.2.1 (cntL ω.2.2.2.2 j))

open Classical in
/-- The right park before coin `j`. -/
noncomputable def parkR (ω : RΩ A BL BR CC κ) (j : ℕ) : Set Y :=
  GmR (lastXset BR ω.2.2.1 (cntR ω.2.2.2.2 j))

open Classical in
/-- The assembled race chunk. -/
noncomputable def rchunk (ω : RΩ A BL BR CC κ) (r : ℕ) : List (Set Y) :=
  if r < A.m then reqMap GmA (chunkN A ω.1 r)
  else if r < A.m + κ then
    (let j := r - A.m
     if h : j < κ then
       (if ω.2.2.2.2 ⟨j, h⟩ then
         parkMap GmL (parkR A BL BR CC GmR κ ω j)
           (chunkN BL ω.2.1 (cntL ω.2.2.2.2 j))
       else
         parkMap GmR (parkL A BL BR CC GmL κ ω j)
           (chunkN BR ω.2.2.1 (cntR ω.2.2.2.2 j)))
     else [])
  else
    (let k := r - A.m - κ
     if survL A BL BR CC κ ω then
       (if k < remCnt A BL BR CC κ ω then
         reqMap GmL (chunkN BL ω.2.1 (cntL ω.2.2.2.2 κ + k))
       else if k - remCnt A BL BR CC κ ω < CC.m then
         reqMap GmTL (chunkN CC ω.2.2.2.1 (k - remCnt A BL BR CC κ ω))
       else [{stopPt}])
     else
       (if k < remCnt A BL BR CC κ ω then
         reqMap GmR (chunkN BR ω.2.2.1 (cntR ω.2.2.2.2 κ + k))
       else if k - remCnt A BL BR CC κ ω < CC.m then
         reqMap GmTR (chunkN CC ω.2.2.2.1 (k - remCnt A BL BR CC κ ω))
       else [{stopPt}]))

open Classical in
/-- The race sizes: input sizes through the phases, the coin phase's
size-weighted minimum, zero on the two phase-transition chunks and the
padding. -/
noncomputable def rsize (ω : RΩ A BL BR CC κ) (r : ℕ) : ℝ :=
  if r < A.m then A.sizeN r ω.1
  else if r < A.m + κ then
    (let j := r - A.m
     min (probL (nextL A BL BR CC κ ω j) (nextR A BL BR CC κ ω j) ε
          * nextL A BL BR CC κ ω j)
        (probL (nextR A BL BR CC κ ω j) (nextL A BL BR CC κ ω j) ε
          * nextR A BL BR CC κ ω j))
  else
    (let k := r - A.m - κ
     if k = 0 ∨ k = remCnt A BL BR CC κ ω then 0
     else if k < remCnt A BL BR CC κ ω then
       (if survL A BL BR CC κ ω then BL.sizeN (cntL ω.2.2.2.2 κ + k) ω.2.1
        else BR.sizeN (cntR ω.2.2.2.2 κ + k) ω.2.2.1)
     else CC.sizeN (k - remCnt A BL BR CC κ ω) ω.2.2.2.1)

open Classical in
/-- Coin-prefix code (an iterated pairing, refining in `j`). -/
noncomputable def coinCode (c : Fin κ → Bool) : ℕ → ℕ
  | 0 => 0
  | (j + 1) => Nat.pair (coinCode c j)
      (if h : j < κ then (if c ⟨j, h⟩ then 1 else 0) else 0)

/-- Revealed side-counts in the tail phase. -/
noncomputable def revL (ω : RΩ A BL BR CC κ) (k : ℕ) : ℕ :=
  if survL A BL BR CC κ ω then min (cntL ω.2.2.2.2 κ + k) BL.m
  else cntL ω.2.2.2.2 κ

noncomputable def revR (ω : RΩ A BL BR CC κ) (k : ℕ) : ℕ :=
  if survL A BL BR CC κ ω then cntR ω.2.2.2.2 κ
  else min (cntR ω.2.2.2.2 κ + k) BR.m

noncomputable def revC (ω : RΩ A BL BR CC κ) (k : ℕ) : ℕ :=
  min (k - remCnt A BL BR CC κ ω) CC.m

open Classical in
/-- The race filtration. -/
noncomputable def rhist (ω : RΩ A BL BR CC κ) (r : ℕ) : ℕ :=
  if r ≤ A.m then Nat.pair 0 (A.hist r ω.1)
  else if r ≤ A.m + κ then
    Nat.pair 1 (Nat.pair (A.hist A.m ω.1)
      (Nat.pair (coinCode κ ω.2.2.2.2 (r - A.m))
        (Nat.pair (BL.hist (cntL ω.2.2.2.2 (r - A.m)) ω.2.1)
          (BR.hist (cntR ω.2.2.2.2 (r - A.m)) ω.2.2.1))))
  else
    Nat.pair 2 (Nat.pair (A.hist A.m ω.1)
      (Nat.pair (coinCode κ ω.2.2.2.2 κ)
        (Nat.pair (BL.hist (revL A BL BR CC κ ω (r - A.m - κ)) ω.2.1)
          (Nat.pair (BR.hist (revR A BL BR CC κ ω (r - A.m - κ)) ω.2.2.1)
            (CC.hist (revC A BL BR CC κ ω (r - A.m - κ)) ω.2.2.2.1)))))

end Sched


section CoinCodeLemmas

variable {κ : ℕ}

theorem coinCode_succ (c : Fin κ → Bool) (j : ℕ) :
    coinCode κ c (j + 1) = Nat.pair (coinCode κ c j)
      (if h : j < κ then (if c ⟨j, h⟩ then 1 else 0) else 0) := rfl

/-- Coin codes agree on coin strings agreeing below `j`. -/
theorem coinCode_congr {c c' : Fin κ → Bool} {j : ℕ}
    (h : ∀ i : Fin κ, (i : ℕ) < j → c i = c' i) :
    coinCode κ c j = coinCode κ c' j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [coinCode_succ, coinCode_succ, ih (fun i hi => h i (by omega))]
    congr 1
    by_cases hj : j < κ
    · rw [dif_pos hj, dif_pos hj, h ⟨j, hj⟩ (Nat.lt_succ_self j)]
    · rw [dif_neg hj, dif_neg hj]

/-- The coin code determines the coins below `j`. -/
theorem coinCode_inj {c c' : Fin κ → Bool} :
    ∀ {j : ℕ}, coinCode κ c j = coinCode κ c' j →
      ∀ i : Fin κ, (i : ℕ) < j → c i = c' i := by
  intro j
  induction j with
  | zero => intro h i hi; omega
  | succ j ih =>
    intro h i hi
    rw [coinCode_succ, coinCode_succ, Nat.pair_eq_pair] at h
    rcases Nat.lt_or_ge (i : ℕ) j with hij | hij
    · exact ih h.1 i hij
    · have hlt := i.isLt
      have hii : (i : ℕ) = j := by omega
      have hjκ : j < κ := by omega
      have h2 := h.2
      rw [dif_pos hjκ, dif_pos hjκ] at h2
      have hcc : c ⟨j, hjκ⟩ = c' ⟨j, hjκ⟩ := by
        by_cases hb : c ⟨j, hjκ⟩ = true <;>
          by_cases hb' : c' ⟨j, hjκ⟩ = true
        · rw [hb, hb']
        · rw [if_pos hb, if_neg hb'] at h2; omega
        · rw [if_neg hb, if_pos hb'] at h2; omega
        · rw [Bool.not_eq_true] at hb hb'; rw [hb, hb']
      have hieq : i = (⟨j, hjκ⟩ : Fin κ) := Fin.ext hii
      rw [hieq]; exact hcc

theorem cntL_eq_of_coinCode {c c' : Fin κ → Bool} {j : ℕ}
    (h : coinCode κ c j = coinCode κ c' j) : cntL c j = cntL c' j :=
  cntL_congr (fun i hi => coinCode_inj h i hi)

theorem cntR_eq_of_coinCode {c c' : Fin κ → Bool} {j : ℕ}
    (h : coinCode κ c j = coinCode κ c' j) : cntR c j = cntR c' j :=
  cntR_congr (fun i hi => coinCode_inj h i hi)

end CoinCodeLemmas


section BranchLemmas

variable (A BL BR CC : ChunkSystemB X s t 0 cB T pe mL)
variable (GmA GmL GmR GmTL GmTR : Set X → Set Y) (stopPt : Y)
variable (κ : ℕ) (ε : ℝ)

theorem chunkN_lt (C : ChunkSystemB X s t 0 cB T pe mL) (ωC : C.Ω)
    {idx : ℕ} (h : idx < C.m) : chunkN C ωC idx = C.chunk ωC ⟨idx, h⟩ :=
  dif_pos h

theorem chunkN_ge (C : ChunkSystemB X s t 0 cB T pe mL) (ωC : C.Ω)
    {idx : ℕ} (h : C.m ≤ idx) : chunkN C ωC idx = [] :=
  dif_neg (by omega)

theorem remCnt_le_max (ω : RΩ A BL BR CC κ) :
    remCnt A BL BR CC κ ω ≤ max BL.m BR.m := by
  unfold remCnt
  by_cases hs : survL A BL BR CC κ ω
  · rw [if_pos hs]
    exact le_trans (Nat.sub_le _ _) (le_max_left _ _)
  · rw [if_neg hs]
    exact le_trans (Nat.sub_le _ _) (le_max_right _ _)

theorem rchunk_A (ω : RΩ A BL BR CC κ) {r : ℕ} (hr : r < A.m) :
    rchunk A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω r
      = reqMap GmA (chunkN A ω.1 r) := by
  unfold rchunk
  rw [if_pos hr]

theorem rchunk_coin (ω : RΩ A BL BR CC κ) {j : ℕ} (hj : j < κ) :
    rchunk A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω (A.m + j)
      = (if ω.2.2.2.2 ⟨j, hj⟩ then
          parkMap GmL (parkR A BL BR CC GmR κ ω j)
            (chunkN BL ω.2.1 (cntL ω.2.2.2.2 j))
        else
          parkMap GmR (parkL A BL BR CC GmL κ ω j)
            (chunkN BR ω.2.2.1 (cntR ω.2.2.2.2 j))) := by
  unfold rchunk
  rw [if_neg (by omega), if_pos (by omega)]
  simp only [Nat.add_sub_cancel_left]
  rw [dif_pos hj]

theorem rchunk_tail (ω : RΩ A BL BR CC κ) (k : ℕ) :
    rchunk A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω (A.m + κ + k)
      = (if survL A BL BR CC κ ω then
          (if k < remCnt A BL BR CC κ ω then
            reqMap GmL (chunkN BL ω.2.1 (cntL ω.2.2.2.2 κ + k))
          else if k - remCnt A BL BR CC κ ω < CC.m then
            reqMap GmTL (chunkN CC ω.2.2.2.1 (k - remCnt A BL BR CC κ ω))
          else [{stopPt}])
        else
          (if k < remCnt A BL BR CC κ ω then
            reqMap GmR (chunkN BR ω.2.2.1 (cntR ω.2.2.2.2 κ + k))
          else if k - remCnt A BL BR CC κ ω < CC.m then
            reqMap GmTR (chunkN CC ω.2.2.2.1 (k - remCnt A BL BR CC κ ω))
          else [{stopPt}])) := by
  unfold rchunk
  rw [if_neg (by omega), if_neg (by omega)]
  simp only [show A.m + κ + k - A.m - κ = k from by omega]

theorem rsize_A (ω : RΩ A BL BR CC κ) {r : ℕ} (hr : r < A.m) :
    rsize A BL BR CC κ ε ω r = A.sizeN r ω.1 := by
  unfold rsize
  rw [if_pos hr]

theorem rsize_coin (ω : RΩ A BL BR CC κ) {j : ℕ} (hj : j < κ) :
    rsize A BL BR CC κ ε ω (A.m + j)
      = min (probL (nextL A BL BR CC κ ω j) (nextR A BL BR CC κ ω j) ε
             * nextL A BL BR CC κ ω j)
            (probL (nextR A BL BR CC κ ω j) (nextL A BL BR CC κ ω j) ε
             * nextR A BL BR CC κ ω j) := by
  unfold rsize
  rw [if_neg (by omega), if_pos (by omega)]
  simp only [Nat.add_sub_cancel_left]

theorem rsize_tail (ω : RΩ A BL BR CC κ) (k : ℕ) :
    rsize A BL BR CC κ ε ω (A.m + κ + k)
      = (if k = 0 ∨ k = remCnt A BL BR CC κ ω then 0
         else if k < remCnt A BL BR CC κ ω then
           (if survL A BL BR CC κ ω then
             BL.sizeN (cntL ω.2.2.2.2 κ + k) ω.2.1
            else BR.sizeN (cntR ω.2.2.2.2 κ + k) ω.2.2.1)
         else CC.sizeN (k - remCnt A BL BR CC κ ω) ω.2.2.2.1) := by
  unfold rsize
  rw [if_neg (by omega), if_neg (by omega)]
  simp only [show A.m + κ + k - A.m - κ = k from by omega]

theorem rhist_le_A (ω : RΩ A BL BR CC κ) {r : ℕ} (hr : r ≤ A.m) :
    rhist A BL BR CC κ ω r = Nat.pair 0 (A.hist r ω.1) := by
  unfold rhist
  rw [if_pos hr]

theorem rhist_coin (ω : RΩ A BL BR CC κ) {j : ℕ} (hj0 : 0 < j)
    (hjκ : j ≤ κ) :
    rhist A BL BR CC κ ω (A.m + j)
      = Nat.pair 1 (Nat.pair (A.hist A.m ω.1)
          (Nat.pair (coinCode κ ω.2.2.2.2 j)
            (Nat.pair (BL.hist (cntL ω.2.2.2.2 j) ω.2.1)
              (BR.hist (cntR ω.2.2.2.2 j) ω.2.2.1)))) := by
  unfold rhist
  rw [if_neg (by omega), if_pos (by omega)]
  simp only [Nat.add_sub_cancel_left]

theorem rhist_tail (ω : RΩ A BL BR CC κ) {r : ℕ} (hr : A.m + κ < r) :
    rhist A BL BR CC κ ω r
      = Nat.pair 2 (Nat.pair (A.hist A.m ω.1)
          (Nat.pair (coinCode κ ω.2.2.2.2 κ)
            (Nat.pair (BL.hist (revL A BL BR CC κ ω (r - A.m - κ)) ω.2.1)
              (Nat.pair
                (BR.hist (revR A BL BR CC κ ω (r - A.m - κ)) ω.2.2.1)
                (CC.hist (revC A BL BR CC κ ω (r - A.m - κ))
                  ω.2.2.2.1))))) := by
  unfold rhist
  rw [if_neg (by omega), if_neg (by omega)]

end BranchLemmas


end Race

end KServer


