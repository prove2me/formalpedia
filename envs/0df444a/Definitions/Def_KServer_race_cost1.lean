-- Prove2me | Definitions.Def_KServer_race_cost1
-- name    : KServer_race_cost1
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-01T17:09:04.585963+00:00
-- url     : https://prove2.me/theorems/93c7dbf6-2893-4cf7-981f-9b9563e2680c
-- title:
--   Race cost plumbing: restricted coin masses, prefix constancy, atom decompositions, and the measure factorization
-- statement:
--   Fix the BCR race setting: four chunk systems $A, B_L, B_R, C$ on $X$, request transformations into $Y$, $\kappa$ size-weighted coins, the interleaved schedule, and the corrected race filtration. This file provides the measure-theoretic plumbing for the race's chunk-cost bound. (1) *Restricted coin masses*: for path-dependent per-step weights summing to one, the total mass of the coin strings extending a fixed prefix of length $j$ equals the weight of the prefix itself viewed as a $j$-step string,
--   $$\sum_{c\,:\,c|_{<j} = c_1|_{<j}} \prod_{i<\kappa} W_i(c) \;=\; \prod_{i<j} W_i(c_1),$$
--   proved by peeling the last coin. (2) *Prefix constancy*: on each atom of the race filtration at time $r$, the flattened race prefix (hence the position of any evader after it) is constant — the refinement and adaptedness properties propagate chunkwise. (3) *Prefix last-request shapes*: with no empty chunks in the inputs, the last request of a coin-phase race prefix is either the image of the pinned exit $G_A\{t\}$ or a park-augmented side request $G_L S \cup G_R S'$ (or with the roles swapped) — the source of the side dichotomy for the evader's position. (4) *Atom decompositions*: the equality of race histories at a fixed time is equivalent to the conjunction of per-component atom conditions (with counts and revelation indices evaluated along the base outcome's coins). (5) *The master factorization*: for a product atom $Q_A \wedge Q_L \wedge Q_R \wedge Q_C \wedge Q_c$ and a product integrand, the race-measure sum factors as
--   $$\sum_{\omega \in \mathrm{atom}} \mathbb{P}(\omega)\, f_A f_L f_R f_C = w \cdot \Bigl(\sum_{Q_A} P_A f_A\Bigr)\Bigl(\sum_{Q_L} P_L f_L\Bigr)\Bigl(\sum_{Q_R} P_R f_R\Bigr)\Bigl(\sum_{Q_C} P_C f_C\Bigr),$$
--   whenever the restricted coin mass is a constant $w$ on the atom. These are the ingredients that reduce the race's per-atom cost bound to the constituent systems' own bounds.
-- source:
--   Measure bookkeeping for the race construction in the BCR randomized k-server lower bound, adapted

import Mathlib
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b
import Definitions.Def_KServer_chunk_cond
import Definitions.Def_KServer_chunk_stopping
import Definitions.Def_KServer_bail_append
import Definitions.Def_KServer_shadow
import Definitions.Def_KServer_park_shadow
import Definitions.Def_KServer_shadow2
import Definitions.Def_KServer_race_sched
import Definitions.Def_KServer_race_coin
import Definitions.Def_KServer_race_core
import Definitions.Def_KServer_race_hist
import Definitions.Def_KServer_absorb
import Definitions.Def_KServer_race_opt

set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 1600000

namespace KServer

namespace Race

/-! ### Restricted coin-tree masses

The mass of the set of coin strings extending a fixed prefix is the
product of the prefix weights — the weight of the prefix viewed as a
shorter coin string.  This is the conditional-probability computation
behind the coin split of the race's chunk-cost bound. -/

section CoinRestrict

/-- The mass of the coin strings extending a fixed prefix. -/
theorem sum_coinWt_restrict {κ : ℕ} :
    ∀ {W : (j : ℕ) → (Fin j → Bool) → Bool → ℝ},
    (∀ j p, W j p true + W j p false = 1) →
    ∀ {j : ℕ} (hj : j ≤ κ), ∀ c₁ : Fin κ → Bool,
    ∑ c ∈ Finset.univ.filter (fun c : Fin κ → Bool =>
        ∀ i : Fin κ, (i : ℕ) < j → c i = c₁ i), coinWt W c
      = coinWt W (restrict c₁ j hj) := by
  induction κ with
  | zero =>
    intro W hsum j hj c₁
    have hj0 : j = 0 := by omega
    subst hj0
    have hfil : (Finset.univ.filter (fun c : Fin 0 → Bool =>
        ∀ i : Fin 0, (i : ℕ) < 0 → c i = c₁ i)) = Finset.univ := by
      ext c
      simp
    rw [hfil]
    haveI : Subsingleton (Fin 0 → Bool) :=
      ⟨fun a b => funext fun i => i.elim0⟩
    rw [Fintype.sum_subsingleton _ (fun _ : Fin 0 => true)]
    unfold coinWt
    rw [Finset.univ_eq_empty, Finset.prod_empty, Finset.prod_empty]
  | succ κ ih =>
    intro W hsum j hj c₁
    have hsplit : ∀ (p : Fin κ → Bool) (b : Bool),
        coinWt W ((snocEquiv κ).symm (p, b)) = coinWt W p * W κ p b := by
      intro p b
      unfold coinWt
      rw [Fin.prod_univ_castSucc]
      congr 1
      · refine Finset.prod_congr rfl fun q _ => ?_
        show W (q : ℕ)
            (restrict ((snocEquiv κ).symm (p, b)) (q : ℕ) (by omega))
            (((snocEquiv κ).symm (p, b)) q.castSucc) = _
        rw [restrict_snoc p b (q : ℕ) (le_of_lt q.isLt) (by omega),
          snocEquiv_symm_castSucc]
      · show W κ (restrict ((snocEquiv κ).symm (p, b)) κ (by omega))
            (((snocEquiv κ).symm (p, b)) (Fin.last κ)) = _
        rw [restrict_snoc p b κ (le_refl κ) (by omega), snocEquiv_symm_last]
        congr 1
    rcases Nat.lt_or_ge j (κ + 1) with hjκ | hjκ'
    · -- j ≤ κ: the last coin is free
      have hjκ2 : j ≤ κ := by omega
      rw [Finset.sum_filter,
        ← Equiv.sum_comp (snocEquiv κ).symm
          (fun c => if (∀ i : Fin (κ + 1), (i : ℕ) < j → c i = c₁ i)
            then coinWt W c else 0),
        Fintype.sum_prod_type]
      have hcond : ∀ (p : Fin κ → Bool) (b : Bool),
          (∀ i : Fin (κ + 1), (i : ℕ) < j →
            ((snocEquiv κ).symm (p, b)) i = c₁ i)
          ↔ (∀ i' : Fin κ, (i' : ℕ) < j → p i' = c₁ i'.castSucc) := by
        intro p b
        constructor
        · intro hc i' hi'
          have := hc i'.castSucc (by
            show ((i'.castSucc : Fin (κ + 1)) : ℕ) < j
            rw [Fin.coe_castSucc]
            exact hi')
          rw [snocEquiv_symm_castSucc] at this
          exact this
        · intro hc i hi
          rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
          · rw [snocEquiv_symm_castSucc]
            exact hc i' (by
              rw [Fin.coe_castSucc] at hi
              exact hi)
          · exfalso
            have : ((Fin.last κ : Fin (κ + 1)) : ℕ) = κ := rfl
            omega
      have hstep : ∀ p : Fin κ → Bool,
          (∑ b : Bool, if (∀ i : Fin (κ + 1), (i : ℕ) < j →
              ((snocEquiv κ).symm (p, b)) i = c₁ i)
            then coinWt W ((snocEquiv κ).symm (p, b)) else 0)
          = (if (∀ i' : Fin κ, (i' : ℕ) < j → p i' = c₁ i'.castSucc)
            then coinWt W p else 0) := by
        intro p
        by_cases hc : ∀ i' : Fin κ, (i' : ℕ) < j → p i' = c₁ i'.castSucc
        · have hc2 : ∀ b : Bool, (∀ i : Fin (κ + 1), (i : ℕ) < j →
              ((snocEquiv κ).symm (p, b)) i = c₁ i) := by
            intro b
            exact (hcond p b).mpr hc
          rw [show (Finset.univ : Finset Bool) = {true, false} from rfl,
            Finset.sum_insert (by simp), Finset.sum_singleton,
            if_pos (hc2 true), if_pos (hc2 false), if_pos hc,
            hsplit p true, hsplit p false, ← mul_add, hsum κ p, mul_one]
        · have hc2 : ∀ b : Bool, ¬ (∀ i : Fin (κ + 1), (i : ℕ) < j →
              ((snocEquiv κ).symm (p, b)) i = c₁ i) := by
            intro b hcc
            exact hc ((hcond p b).mp hcc)
          rw [show (Finset.univ : Finset Bool) = {true, false} from rfl,
            Finset.sum_insert (by simp), Finset.sum_singleton,
            if_neg (hc2 true), if_neg (hc2 false), if_neg hc, add_zero]
      calc ∑ p : Fin κ → Bool, ∑ b : Bool,
          (if (∀ i : Fin (κ + 1), (i : ℕ) < j →
              ((snocEquiv κ).symm (p, b)) i = c₁ i)
            then coinWt W ((snocEquiv κ).symm (p, b)) else 0)
          = ∑ p : Fin κ → Bool,
            (if (∀ i' : Fin κ, (i' : ℕ) < j → p i' = c₁ i'.castSucc)
              then coinWt W p else 0) :=
            Finset.sum_congr rfl fun p _ => hstep p
        _ = coinWt W (restrict (fun i' : Fin κ => c₁ i'.castSucc) j hjκ2) := by
            rw [← Finset.sum_filter]
            exact ih hsum hjκ2 (fun i' => c₁ i'.castSucc)
        _ = coinWt W (restrict c₁ j hj) := by
            congr 1
    · -- j = κ + 1: the prefix is everything
      have hje : j = κ + 1 := by omega
      subst hje
      have hfil : (Finset.univ.filter (fun c : Fin (κ + 1) → Bool =>
          ∀ i : Fin (κ + 1), (i : ℕ) < κ + 1 → c i = c₁ i)) = {c₁} := by
        ext c
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_singleton]
        constructor
        · intro hc
          funext i
          exact hc i i.isLt
        · intro hc i _
          rw [hc]
      rw [hfil, Finset.sum_singleton]
      congr 1

end CoinRestrict


section Prefixes

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
variable {s t : X} {cB T pe : ℝ} {mL : ℕ}
variable (A BL BR CC : ChunkSystemB X s t 0 cB T pe mL)
variable (GmA GmL GmR GmTL GmTR : Set X → Set Y) (stopPt : Y)
variable (κ : ℕ)

/-- The race prefix before chunk `r`. -/
noncomputable def rpre (ω : RΩ A BL BR CC κ) (r : ℕ) : List (Set Y) :=
  ((List.ofFn (fun i : Fin (mrace A BL BR CC κ) =>
    rchunk A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω (i : ℕ))).take
      r).flatten

/-- The race prefix is constant on filtration atoms. -/
theorem rpre_congr (hκL : κ ≤ BL.m) (hκR : κ ≤ BR.m)
    {ω ω' : RΩ A BL BR CC κ} {r : ℕ}
    (h : rhist2 A BL BR CC κ ω r = rhist2 A BL BR CC κ ω' r) :
    rpre A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω r
      = rpre A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω' r := by
  unfold rpre
  congr 1
  apply List.ext_getElem
  · rw [List.length_take, List.length_take, List.length_ofFn,
      List.length_ofFn]
  · intro rr h1 h2
    rw [List.getElem_take, List.getElem_take, List.getElem_ofFn,
      List.getElem_ofFn]
    have hrr : rr < r := by
      rw [List.length_take, List.length_ofFn] at h1
      omega
    exact rchunk_adapt A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ hκL hκR
      ω ω' (rhist2_refine A BL BR CC κ hκL hκR
        (by omega : rr + 1 ≤ r) ω ω' h)

theorem take_succ_ofFn {α : Type*} {n : ℕ} (f : Fin n → α) {i : ℕ}
    (hi : i < n) :
    (List.ofFn f).take (i + 1) = (List.ofFn f).take i ++ [f ⟨i, hi⟩] := by
  rw [List.take_succ]
  congr 1
  rw [List.getElem?_eq_getElem (by rw [List.length_ofFn]; exact hi)]
  rw [List.getElem_ofFn]
  rfl

/-- With no empty chunks, the last chunk ends at the pinned exit. -/
theorem chunk_last_pin (C : ChunkSystemB X s t 0 cB T pe mL) (ωc : C.Ω)
    (hch : ∀ i : Fin C.m, C.chunk ωc i ≠ []) :
    (C.chunk ωc ⟨C.m - 1, by have := C.hm0; omega⟩).getLast?
      = some ({t} : Set X) := by
  have hm1 : C.m - 1 < C.m := by have := C.hm0; omega
  have hdec : (List.ofFn (C.chunk ωc)).flatten
      = (((List.ofFn (C.chunk ωc)).take (C.m - 1)).flatten)
        ++ C.chunk ωc ⟨C.m - 1, hm1⟩ := by
    have h1 : (List.ofFn (C.chunk ωc)).take ((C.m - 1) + 1)
        = List.ofFn (C.chunk ωc) := by
      apply List.take_of_length_le
      rw [List.length_ofFn]
      omega
    conv_lhs => rw [← h1]
    rw [take_succ_ofFn (C.chunk ωc) hm1, List.flatten_append,
      List.flatten_cons, List.flatten_nil, List.append_nil]
  have hlast := C.hlast ωc
  rw [hdec, List.getLast?_append_of_ne_nil _ (hch ⟨C.m - 1, hm1⟩)] at hlast
  exact hlast

/-- Shape of the last request of a coin-phase race prefix: the two
junction images, or a park-augmented side request. -/
theorem rpre_getLast_coin (hκL : κ ≤ BL.m) (hκR : κ ≤ BR.m)
    (hchA : ∀ (ωa : A.Ω) (i : Fin A.m), A.chunk ωa i ≠ [])
    (hchL : ∀ (ωl : BL.Ω) (i : Fin BL.m), BL.chunk ωl i ≠ [])
    (hchR : ∀ (ωr : BR.Ω) (i : Fin BR.m), BR.chunk ωr i ≠ [])
    (ω : RΩ A BL BR CC κ) {r : ℕ} (hr1 : A.m ≤ r) (hr2 : r ≤ A.m + κ) :
    (rpre A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω r).getLast?
        = some (GmA ({t} : Set X))
    ∨ (∃ SL SR : Set X,
        (rpre A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω r).getLast?
          = some (GmL SL ∪ GmR SR))
    ∨ (∃ SR SL : Set X,
        (rpre A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω r).getLast?
          = some (GmR SR ∪ GmL SL)) := by
  have hm0 := A.hm0
  have hr0 : 0 < r := by omega
  have hrm : r ≤ mrace A BL BR CC κ := by
    unfold mrace
    omega
  have hrm1 : r - 1 < mrace A BL BR CC κ := by omega
  have hdec : rpre A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω r
      = rpre A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω (r - 1)
        ++ rchunk A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω (r - 1) := by
    unfold rpre
    have h1 : (List.ofFn (fun i : Fin (mrace A BL BR CC κ) =>
        rchunk A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω (i : ℕ))).take r
        = (List.ofFn (fun i : Fin (mrace A BL BR CC κ) =>
          rchunk A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω (i : ℕ))).take
            ((r - 1) + 1) := by
      congr 1
      omega
    rw [h1, take_succ_ofFn _ hrm1, List.flatten_append, List.flatten_cons,
      List.flatten_nil, List.append_nil]
  by_cases hcase : r - 1 < A.m
  · -- the previous chunk is the last phase-A chunk
    left
    have hre : r - 1 = A.m - 1 := by omega
    rw [hdec, hre,
      rchunk_A A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω
        (by omega : A.m - 1 < A.m)]
    have hchunkN : chunkN A ω.1 (A.m - 1)
        = A.chunk ω.1 ⟨A.m - 1, by omega⟩ := chunkN_lt A ω.1 (by omega)
    have hne2 : reqMap GmA (chunkN A ω.1 (A.m - 1)) ≠ [] := by
      unfold reqMap
      rw [hchunkN]
      intro hcon
      rw [List.map_eq_nil_iff] at hcon
      exact hchA ω.1 _ hcon
    rw [List.getLast?_append_of_ne_nil _ hne2]
    unfold reqMap
    rw [getLast?_map', hchunkN, chunk_last_pin A ω.1 (hchA ω.1),
      Option.map_some]
  · -- the previous chunk is a coin chunk
    have hj : r - 1 - A.m < κ := by omega
    have hjr : r - 1 = A.m + (r - 1 - A.m) := by omega
    rw [hdec, hjr, rchunk_coin A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω hj]
    by_cases hb : ω.2.2.2.2 ⟨r - 1 - A.m, hj⟩
    · right; left
      rw [if_pos hb]
      have hcnt : cntL ω.2.2.2.2 (r - 1 - A.m) < BL.m := by
        have h1 := cntL_le ω.2.2.2.2 (le_of_lt hj)
        omega
      have hchunkN : chunkN BL ω.2.1 (cntL ω.2.2.2.2 (r - 1 - A.m))
          = BL.chunk ω.2.1 ⟨_, hcnt⟩ := chunkN_lt BL ω.2.1 hcnt
      have hne2 : parkMap GmL (parkR A BL BR CC GmR κ ω (r - 1 - A.m))
          (chunkN BL ω.2.1 (cntL ω.2.2.2.2 (r - 1 - A.m))) ≠ [] := by
        unfold parkMap
        rw [hchunkN]
        intro hcon
        rw [List.map_eq_nil_iff] at hcon
        exact hchL ω.2.1 _ hcon
      rw [List.getLast?_append_of_ne_nil _ hne2]
      unfold parkMap
      rw [getLast?_map']
      have hglc : (chunkN BL ω.2.1 (cntL ω.2.2.2.2 (r - 1 - A.m))).getLast?
          = some ((chunkN BL ω.2.1 (cntL ω.2.2.2.2 (r - 1 - A.m))).getLast
            (by rw [hchunkN]; exact hchL ω.2.1 _)) := by
        exact List.getLast?_eq_some_getLast _
      rw [hglc, Option.map_some]
      exact ⟨_, lastXset BR ω.2.2.1 (cntR ω.2.2.2.2 (r - 1 - A.m)), rfl⟩
    · right; right
      rw [if_neg hb]
      have hcnt : cntR ω.2.2.2.2 (r - 1 - A.m) < BR.m := by
        have h1 := cntR_le ω.2.2.2.2 (le_of_lt hj)
        omega
      have hchunkN : chunkN BR ω.2.2.1 (cntR ω.2.2.2.2 (r - 1 - A.m))
          = BR.chunk ω.2.2.1 ⟨_, hcnt⟩ := chunkN_lt BR ω.2.2.1 hcnt
      have hne2 : parkMap GmR (parkL A BL BR CC GmL κ ω (r - 1 - A.m))
          (chunkN BR ω.2.2.1 (cntR ω.2.2.2.2 (r - 1 - A.m))) ≠ [] := by
        unfold parkMap
        rw [hchunkN]
        intro hcon
        rw [List.map_eq_nil_iff] at hcon
        exact hchR ω.2.2.1 _ hcon
      rw [List.getLast?_append_of_ne_nil _ hne2]
      unfold parkMap
      rw [getLast?_map']
      have hglc : (chunkN BR ω.2.2.1 (cntR ω.2.2.2.2 (r - 1 - A.m))).getLast?
          = some ((chunkN BR ω.2.2.1 (cntR ω.2.2.2.2 (r - 1 - A.m))).getLast
            (by rw [hchunkN]; exact hchR ω.2.2.1 _)) := by
        exact List.getLast?_eq_some_getLast _
      rw [hglc, Option.map_some]
      exact ⟨_, lastXset BL ω.2.1 (cntL ω.2.2.2.2 (r - 1 - A.m)), rfl⟩

end Prefixes



section AtomIff

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
variable {s t : X} {cB T pe : ℝ} {mL : ℕ}
variable (A BL BR CC : ChunkSystemB X s t 0 cB T pe mL)
variable (κ : ℕ)

theorem rhist2_eq_iff_A {ω ω₀ : RΩ A BL BR CC κ} {r : ℕ} (hr : r ≤ A.m) :
    rhist2 A BL BR CC κ ω r = rhist2 A BL BR CC κ ω₀ r
      ↔ A.hist r ω.1 = A.hist r ω₀.1 := by
  rw [rhist2_le_A A BL BR CC κ ω hr, rhist2_le_A A BL BR CC κ ω₀ hr,
    Nat.pair_eq_pair]
  exact ⟨fun h => h.2, fun h => ⟨by trivial, h⟩⟩

theorem rhist2_eq_iff_coin {ω ω₀ : RΩ A BL BR CC κ} {r : ℕ}
    (h1 : A.m < r) (h2 : r ≤ A.m + κ) :
    rhist2 A BL BR CC κ ω r = rhist2 A BL BR CC κ ω₀ r
      ↔ (A.hist A.m ω.1 = A.hist A.m ω₀.1
        ∧ (∀ i : Fin κ, (i : ℕ) < r - A.m → ω.2.2.2.2 i = ω₀.2.2.2.2 i)
        ∧ BL.hist (cntL ω₀.2.2.2.2 (r - A.m)) ω.2.1
            = BL.hist (cntL ω₀.2.2.2.2 (r - A.m)) ω₀.2.1
        ∧ BR.hist (cntR ω₀.2.2.2.2 (r - A.m)) ω.2.2.1
            = BR.hist (cntR ω₀.2.2.2.2 (r - A.m)) ω₀.2.2.1) := by
  rw [rhist2_coin A BL BR CC κ ω h1 h2, rhist2_coin A BL BR CC κ ω₀ h1 h2]
  simp only [Nat.pair_eq_pair]
  constructor
  · rintro ⟨-, hA, hcode, hLh, hRh⟩
    have hcs : ∀ i : Fin κ, (i : ℕ) < r - A.m →
        ω.2.2.2.2 i = ω₀.2.2.2.2 i := coinCode_inj hcode
    refine ⟨hA, hcs, ?_, ?_⟩
    · rw [cntL_congr hcs] at hLh
      exact hLh
    · rw [cntR_congr hcs] at hRh
      exact hRh
  · rintro ⟨hA, hcs, hLh, hRh⟩
    refine ⟨by trivial, hA, coinCode_congr hcs, ?_, ?_⟩
    · rw [cntL_congr hcs]
      exact hLh
    · rw [cntR_congr hcs]
      exact hRh

theorem rhist2_eq_iff_tail (hκL : κ ≤ BL.m) (hκR : κ ≤ BR.m)
    {ω ω₀ : RΩ A BL BR CC κ} {r : ℕ} (h1 : A.m + κ < r) :
    rhist2 A BL BR CC κ ω r = rhist2 A BL BR CC κ ω₀ r
      ↔ (A.hist A.m ω.1 = A.hist A.m ω₀.1
        ∧ ω.2.2.2.2 = ω₀.2.2.2.2
        ∧ BL.hist (revL2 A BL BR CC κ ω₀ (r - A.m - κ)) ω.2.1
            = BL.hist (revL2 A BL BR CC κ ω₀ (r - A.m - κ)) ω₀.2.1
        ∧ BR.hist (revR2 A BL BR CC κ ω₀ (r - A.m - κ)) ω.2.2.1
            = BR.hist (revR2 A BL BR CC κ ω₀ (r - A.m - κ)) ω₀.2.2.1
        ∧ CC.hist (revC A BL BR CC κ ω₀ (r - A.m - κ)) ω.2.2.2.1
            = CC.hist (revC A BL BR CC κ ω₀ (r - A.m - κ)) ω₀.2.2.2.1) := by
  rw [rhist2_tail A BL BR CC κ ω h1, rhist2_tail A BL BR CC κ ω₀ h1]
  simp only [Nat.pair_eq_pair]
  set k := r - A.m - κ with hk
  constructor
  · rintro ⟨-, hA, hcode, hLh, hRh, hCh⟩
    have hceq : ω.2.2.2.2 = ω₀.2.2.2.2 :=
      funext fun ii => coinCode_inj hcode ii ii.isLt
    have hrevL : revL2 A BL BR CC κ ω k = revL2 A BL BR CC κ ω₀ k := by
      unfold revL2
      rw [hceq]
    have hrevR : revR2 A BL BR CC κ ω k = revR2 A BL BR CC κ ω₀ k := by
      unfold revR2
      rw [hceq]
    rw [hrevL] at hLh
    rw [hrevR] at hRh
    have hNL : cntL ω.2.2.2.2 κ ≤ revL2 A BL BR CC κ ω₀ k := by
      rw [hceq]
      unfold revL2
      exact le_min (Nat.le_add_right _ _)
        (le_trans (cntL_le _ le_rfl) hκL)
    have hNR : cntR ω.2.2.2.2 κ ≤ revR2 A BL BR CC κ ω₀ k := by
      rw [hceq]
      unfold revR2
      exact le_min (Nat.le_add_right _ _)
        (le_trans (cntR_le _ le_rfl) hκR)
    have hCk : revC A BL BR CC κ ω k = revC A BL BR CC κ ω₀ k :=
      revC_congr A BL BR CC κ hceq hNL hNR hLh hRh k
    rw [hCk] at hCh
    exact ⟨hA, hceq, hLh, hRh, hCh⟩
  · rintro ⟨hA, hceq, hLh, hRh, hCh⟩
    have hrevL : revL2 A BL BR CC κ ω k = revL2 A BL BR CC κ ω₀ k := by
      unfold revL2
      rw [hceq]
    have hrevR : revR2 A BL BR CC κ ω k = revR2 A BL BR CC κ ω₀ k := by
      unfold revR2
      rw [hceq]
    have hNL : cntL ω.2.2.2.2 κ ≤ revL2 A BL BR CC κ ω₀ k := by
      rw [hceq]
      unfold revL2
      exact le_min (Nat.le_add_right _ _)
        (le_trans (cntL_le _ le_rfl) hκL)
    have hNR : cntR ω.2.2.2.2 κ ≤ revR2 A BL BR CC κ ω₀ k := by
      rw [hceq]
      unfold revR2
      exact le_min (Nat.le_add_right _ _)
        (le_trans (cntR_le _ le_rfl) hκR)
    have hCk : revC A BL BR CC κ ω k = revC A BL BR CC κ ω₀ k :=
      revC_congr A BL BR CC κ hceq hNL hNR hLh hRh k
    refine ⟨by trivial, hA, by rw [hceq], ?_, ?_, ?_⟩
    · rw [hrevL]
      exact hLh
    · rw [hrevR]
      exact hRh
    · rw [hCk]
      exact hCh

end AtomIff

section Factor

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
variable {s t : X} {cB T pe : ℝ} {mL : ℕ}
variable (A BL BR CC : ChunkSystemB X s t 0 cB T pe mL)
variable (κ : ℕ) (ε : ℝ)

open Classical in
/-- The master factorization of a race-measure sum over a product atom:
the four components and the restricted coin mass factor out. -/
theorem sum_RP_factor
    (QA : A.Ω → Prop) (QL : BL.Ω → Prop) (QR : BR.Ω → Prop)
    (QC : CC.Ω → Prop) (Qc : (Fin κ → Bool) → Prop)
    (fA : A.Ω → ℝ) (fL : BL.Ω → ℝ) (fR : BR.Ω → ℝ) (fC : CC.Ω → ℝ)
    (wval : ℝ)
    (hW : ∀ (ωA : A.Ω) (ωL : BL.Ω) (ωR : BR.Ω), QA ωA → QL ωL → QR ωR →
      ∑ c ∈ Finset.univ.filter Qc,
        coinWt (coinW A BL BR ωA ωL ωR (ε := ε)) c = wval) :
    ∑ ω ∈ Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
        QA ω.1 ∧ QL ω.2.1 ∧ QR ω.2.2.1 ∧ QC ω.2.2.2.1 ∧ Qc ω.2.2.2.2),
      RP A BL BR CC κ ε ω * (fA ω.1 * fL ω.2.1 * fR ω.2.2.1 * fC ω.2.2.2.1)
      = wval * ((∑ ωA ∈ Finset.univ.filter QA, A.P ωA * fA ωA)
        * ((∑ ωL ∈ Finset.univ.filter QL, BL.P ωL * fL ωL)
          * ((∑ ωR ∈ Finset.univ.filter QR, BR.P ωR * fR ωR)
            * (∑ ωC ∈ Finset.univ.filter QC, CC.P ωC * fC ωC)))) := by
  set SC := ∑ ωC ∈ Finset.univ.filter QC, CC.P ωC * fC ωC with hSC
  set SR := ∑ ωR ∈ Finset.univ.filter QR, BR.P ωR * fR ωR with hSR
  set SL := ∑ ωL ∈ Finset.univ.filter QL, BL.P ωL * fL ωL with hSL
  set SA := ∑ ωA ∈ Finset.univ.filter QA, A.P ωA * fA ωA with hSA
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  have hA : ∀ ωA : A.Ω,
      (∑ ω2 : BL.Ω × BR.Ω × CC.Ω × (Fin κ → Bool),
        if QA ωA ∧ QL ω2.1 ∧ QR ω2.2.1 ∧ QC ω2.2.2.1 ∧ Qc ω2.2.2.2 then
          RP A BL BR CC κ ε (ωA, ω2)
            * (fA ωA * fL ω2.1 * fR ω2.2.1 * fC ω2.2.2.1)
        else 0)
      = (if QA ωA then A.P ωA * fA ωA else 0) * (SL * (SR * SC) * wval) := by
    intro ωA
    by_cases hQA : QA ωA
    · rw [if_pos hQA, Fintype.sum_prod_type]
      have hL : ∀ ωL : BL.Ω,
          (∑ ω3 : BR.Ω × CC.Ω × (Fin κ → Bool),
            if QA ωA ∧ QL ωL ∧ QR ω3.1 ∧ QC ω3.2.1 ∧ Qc ω3.2.2 then
              RP A BL BR CC κ ε (ωA, ωL, ω3)
                * (fA ωA * fL ωL * fR ω3.1 * fC ω3.2.1)
            else 0)
          = (if QL ωL then BL.P ωL * fL ωL else 0)
            * (A.P ωA * fA ωA * (SR * SC * wval)) := by
        intro ωL
        by_cases hQL : QL ωL
        · rw [if_pos hQL, Fintype.sum_prod_type]
          have hR : ∀ ωR : BR.Ω,
              (∑ ω4 : CC.Ω × (Fin κ → Bool),
                if QA ωA ∧ QL ωL ∧ QR ωR ∧ QC ω4.1 ∧ Qc ω4.2 then
                  RP A BL BR CC κ ε (ωA, ωL, ωR, ω4)
                    * (fA ωA * fL ωL * fR ωR * fC ω4.1)
                else 0)
              = (if QR ωR then BR.P ωR * fR ωR else 0)
                * (A.P ωA * fA ωA * (BL.P ωL * fL ωL) * (SC * wval)) := by
            intro ωR
            by_cases hQR : QR ωR
            · rw [if_pos hQR, Fintype.sum_prod_type]
              have hC : ∀ ωC : CC.Ω,
                  (∑ c : Fin κ → Bool,
                    if QA ωA ∧ QL ωL ∧ QR ωR ∧ QC ωC ∧ Qc c then
                      RP A BL BR CC κ ε (ωA, ωL, ωR, ωC, c)
                        * (fA ωA * fL ωL * fR ωR * fC ωC)
                    else 0)
                  = (if QC ωC then CC.P ωC * fC ωC else 0)
                    * (A.P ωA * fA ωA * (BL.P ωL * fL ωL)
                      * (BR.P ωR * fR ωR) * wval) := by
                intro ωC
                by_cases hQC : QC ωC
                · rw [if_pos hQC]
                  have hcs := hW ωA ωL ωR hQA hQL hQR
                  rw [Finset.sum_filter] at hcs
                  calc ∑ c : Fin κ → Bool,
                      (if QA ωA ∧ QL ωL ∧ QR ωR ∧ QC ωC ∧ Qc c then
                        RP A BL BR CC κ ε (ωA, ωL, ωR, ωC, c)
                          * (fA ωA * fL ωL * fR ωR * fC ωC)
                      else 0)
                      = ∑ c : Fin κ → Bool,
                        (A.P ωA * fA ωA * (BL.P ωL * fL ωL)
                          * (BR.P ωR * fR ωR) * (CC.P ωC * fC ωC))
                          * (if Qc c then
                            coinWt (coinW A BL BR ωA ωL ωR (ε := ε)) c
                          else 0) := by
                        refine Finset.sum_congr rfl fun c _ => ?_
                        by_cases hQc : Qc c
                        · rw [if_pos ⟨hQA, hQL, hQR, hQC, hQc⟩, if_pos hQc]
                          unfold RP
                          ring
                        · rw [if_neg (by
                            intro hcon
                            exact hQc hcon.2.2.2.2), if_neg hQc, mul_zero]
                    _ = (A.P ωA * fA ωA * (BL.P ωL * fL ωL)
                          * (BR.P ωR * fR ωR) * (CC.P ωC * fC ωC)) * wval := by
                        rw [← Finset.mul_sum, hcs]
                    _ = (CC.P ωC * fC ωC)
                          * (A.P ωA * fA ωA * (BL.P ωL * fL ωL)
                            * (BR.P ωR * fR ωR) * wval) := by
                        ring
                · rw [if_neg hQC, zero_mul]
                  refine Finset.sum_eq_zero fun c _ => ?_
                  rw [if_neg (by
                    intro hcon
                    exact hQC hcon.2.2.2.1)]
              calc ∑ ωC : CC.Ω, ∑ c : Fin κ → Bool,
                  (if QA ωA ∧ QL ωL ∧ QR ωR ∧ QC ωC ∧ Qc c then
                    RP A BL BR CC κ ε (ωA, ωL, ωR, ωC, c)
                      * (fA ωA * fL ωL * fR ωR * fC ωC)
                  else 0)
                  = ∑ ωC : CC.Ω, (if QC ωC then CC.P ωC * fC ωC else 0)
                    * (A.P ωA * fA ωA * (BL.P ωL * fL ωL)
                      * (BR.P ωR * fR ωR) * wval) :=
                    Finset.sum_congr rfl fun ωC _ => hC ωC
                _ = SC * (A.P ωA * fA ωA * (BL.P ωL * fL ωL)
                      * (BR.P ωR * fR ωR) * wval) := by
                    rw [← Finset.sum_mul, hSC, Finset.sum_filter]
                _ = (BR.P ωR * fR ωR)
                      * (A.P ωA * fA ωA * (BL.P ωL * fL ωL) * (SC * wval)) := by
                    ring
            · rw [if_neg hQR, zero_mul]
              refine Finset.sum_eq_zero fun ω4 _ => ?_
              rw [if_neg (by
                intro hcon
                exact hQR hcon.2.2.1)]
          calc ∑ ωR : BR.Ω, ∑ ω4 : CC.Ω × (Fin κ → Bool),
              (if QA ωA ∧ QL ωL ∧ QR ωR ∧ QC ω4.1 ∧ Qc ω4.2 then
                RP A BL BR CC κ ε (ωA, ωL, ωR, ω4)
                  * (fA ωA * fL ωL * fR ωR * fC ω4.1)
              else 0)
              = ∑ ωR : BR.Ω, (if QR ωR then BR.P ωR * fR ωR else 0)
                * (A.P ωA * fA ωA * (BL.P ωL * fL ωL) * (SC * wval)) :=
                Finset.sum_congr rfl fun ωR _ => hR ωR
            _ = SR * (A.P ωA * fA ωA * (BL.P ωL * fL ωL) * (SC * wval)) := by
                rw [← Finset.sum_mul, hSR, Finset.sum_filter]
            _ = (BL.P ωL * fL ωL)
                  * (A.P ωA * fA ωA * (SR * SC * wval)) := by
                ring
        · rw [if_neg hQL, zero_mul]
          refine Finset.sum_eq_zero fun ω3 _ => ?_
          rw [if_neg (by
            intro hcon
            exact hQL hcon.2.1)]
      calc ∑ ωL : BL.Ω, ∑ ω3 : BR.Ω × CC.Ω × (Fin κ → Bool),
          (if QA ωA ∧ QL ωL ∧ QR ω3.1 ∧ QC ω3.2.1 ∧ Qc ω3.2.2 then
            RP A BL BR CC κ ε (ωA, ωL, ω3)
              * (fA ωA * fL ωL * fR ω3.1 * fC ω3.2.1)
          else 0)
          = ∑ ωL : BL.Ω, (if QL ωL then BL.P ωL * fL ωL else 0)
            * (A.P ωA * fA ωA * (SR * SC * wval)) :=
            Finset.sum_congr rfl fun ωL _ => hL ωL
        _ = SL * (A.P ωA * fA ωA * (SR * SC * wval)) := by
            rw [← Finset.sum_mul, hSL, Finset.sum_filter]
        _ = (A.P ωA * fA ωA) * (SL * (SR * SC) * wval) := by
            ring
    · rw [if_neg hQA, zero_mul]
      refine Finset.sum_eq_zero fun ω2 _ => ?_
      rw [if_neg (by
        intro hcon
        exact hQA hcon.1)]
  calc ∑ ωA : A.Ω, ∑ ω2 : BL.Ω × BR.Ω × CC.Ω × (Fin κ → Bool),
      (if QA (ωA, ω2).1 ∧ QL (ωA, ω2).2.1 ∧ QR (ωA, ω2).2.2.1
          ∧ QC (ωA, ω2).2.2.2.1 ∧ Qc (ωA, ω2).2.2.2.2 then
        RP A BL BR CC κ ε (ωA, ω2)
          * (fA (ωA, ω2).1 * fL (ωA, ω2).2.1 * fR (ωA, ω2).2.2.1
            * fC (ωA, ω2).2.2.2.1)
      else 0)
      = ∑ ωA : A.Ω, (if QA ωA then A.P ωA * fA ωA else 0)
        * (SL * (SR * SC) * wval) :=
      Finset.sum_congr rfl fun ωA _ => hA ωA
    _ = SA * (SL * (SR * SC) * wval) := by
        rw [← Finset.sum_mul, hSA, Finset.sum_filter]
    _ = wval * (SA * (SL * (SR * SC))) := by ring

end Factor



end Race

end KServer


