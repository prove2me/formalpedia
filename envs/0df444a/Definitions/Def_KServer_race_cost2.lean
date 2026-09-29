-- Prove2me | Definitions.Def_KServer_race_cost2
-- name    : KServer_race_cost2
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-01T17:51:13.974662+00:00
-- url     : https://prove2.me/theorems/47b55df7-eacb-48ba-92a4-89fb59448867
-- title:
--   The race chunk-cost bound: per-atom domination in every phase
-- statement:
--   This file proves the chunk-cost bound of the BCR race against every evader on the target space and every online escape rule, phase by phase. Fix the race over four chunk systems $A, B_L, B_R, C$ with $\kappa$ size-weighted coins, the corrected filtration, escape price $p_e \ge 0$ in the constituents and $p' \ge p_e$ in the race. The master inequality, for each race time $r$ and each atom of the race filtration, is
--   $$\mathrm{size}(r)\cdot \mathbb{P}(\mathrm{atom}) \;\le\; \sum_{\omega \in \mathrm{atom}} \mathbb{P}(\omega)\, \mathrm{bailCost}\bigl(E, \mathrm{prefix}(\omega), \mathrm{chunk}_r(\omega), p'\bigr).$$
--   In phase $A$ the atom marginalizes to the $A$-component and the bound transports through an offset shadow along the retraction $\pi_A$. In the coin phase the evader's position after the (atom-constant) prefix lies in the last request — the mapped exit pin or a union of the two sides' running positions — and a geometric dichotomy hypothesis separates it from at least one side's images; that side's coin, whose conditional probability is the atom-constant weight $p_\sigma$, finances the claimed size $\min(p_L n_L, p_R n_R)$ through the park-aware offset shadow (the separation $\mathrm{sep} \ge \mathrm{diam}(X) + p_e$ pays for the boundary jump), while the other coin's contribution is nonnegative. In the tail phases the coins are fully fixed, the survivor identity and remaining count are atom-determined, and the survivor's remainder and the tail system are bounded by pure offset shadows aligned at the previous chunk's last request; the two phase-transition chunks and the padding claim size zero and cost nothing. The proofs run through restricted coin-tree masses, atom decompositions, and product factorizations of the race measure.
-- source:
--   Chunk-cost bounds for the race construction in the BCR randomized k-server lower bound, adapted

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
import Definitions.Def_KServer_race_cost1

set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 3200000

namespace KServer

namespace Race

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
variable {s t : X} {cB T pe : ℝ} {mL : ℕ}

open Classical in
/-- The boundary position of the offset shadow (restated locally): on a
history of exact length `n` whose last request already contains the
projected evader position, the shadow sits at the projected position. -/
theorem shadowFrom_pos_boundary
    (n : ℕ) (π : Y → X) (G : Set X → Set Y)
    (hG : ∀ S : Set X, ∀ y ∈ G S, π y ∈ S)
    (hGne : ∀ S : Set X, S.Nonempty → (G S).Nonempty)
    (E : EvaderAlgorithm Y) (h₀ : List (Set Y)) {h : List (Set X)}
    (hh : h.length = n)
    (hmem : ∀ S : Set X, h.getLast? = some S → π (E.pos h₀) ∈ S) :
    (shadowFrom n π G hG hGne E h₀).pos h = π (E.pos h₀) := by
  have hlen : h.length ≤ n := le_of_eq hh
  have hdrop : h.drop n = [] := by
    rw [← hh]
    exact List.drop_length
  have hmap : reqMap G ([] : List (Set X)) = [] := by
    unfold reqMap
    rw [List.map_nil]
  unfold shadowFrom
  simp only [hlen, if_true]
  cases hgl : h.getLast? with
  | none =>
    simp only [hgl]
    rw [hdrop, hmap, List.append_nil]
  | some Sl =>
    simp only [hgl]
    rw [hdrop, hmap, List.append_nil]
    rw [if_pos (hmem Sl hgl)]

section PhaseA

variable (A BL BR CC : ChunkSystemB X s t 0 cB T pe mL)
variable (GmA GmL GmR GmTL GmTR : Set X → Set Y) (stopPt : Y)
variable (κ : ℕ) (ε : ℝ)

/-- The inner race mass at a fixed `A`-outcome is one. -/
theorem sum_RP_inner (hε : 0 < ε) (ωA : A.Ω) :
    ∑ ω2 : BL.Ω × BR.Ω × CC.Ω × (Fin κ → Bool),
      BL.P ω2.1 * (BR.P ω2.2.1 * (CC.P ω2.2.2.1
        * coinWt (coinW A BL BR ωA ω2.1 ω2.2.1 (ε := ε)) ω2.2.2.2)) = 1 := by
  rw [Fintype.sum_prod_type]
  have h2 : ∀ ωL, ∑ ω3 : BR.Ω × CC.Ω × (Fin κ → Bool),
      BL.P ωL * (BR.P ω3.1 * (CC.P ω3.2.1
        * coinWt (coinW A BL BR ωA ωL ω3.1 (ε := ε)) ω3.2.2))
      = BL.P ωL := by
    intro ωL
    rw [Fintype.sum_prod_type]
    have h3 : ∀ ωR, ∑ ω4 : CC.Ω × (Fin κ → Bool),
        BL.P ωL * (BR.P ωR * (CC.P ω4.1
          * coinWt (coinW A BL BR ωA ωL ωR (ε := ε)) ω4.2))
        = BL.P ωL * BR.P ωR := by
      intro ωR
      rw [Fintype.sum_prod_type]
      have h4 : ∀ ωC, ∑ c : Fin κ → Bool,
          BL.P ωL * (BR.P ωR * (CC.P ωC
            * coinWt (coinW A BL BR ωA ωL ωR (ε := ε)) c))
          = BL.P ωL * (BR.P ωR * CC.P ωC) := by
        intro ωC
        have hcsum : ∑ c : Fin κ → Bool,
            coinWt (coinW A BL BR ωA ωL ωR (ε := ε)) c = 1 := by
          refine sum_coinWt fun j p => ?_
          show probL _ _ ε + probL _ _ ε = 1
          exact probL_add_probR _ _ ε hε
        calc ∑ c : Fin κ → Bool, BL.P ωL * (BR.P ωR * (CC.P ωC
            * coinWt (coinW A BL BR ωA ωL ωR (ε := ε)) c))
            = (BL.P ωL * (BR.P ωR * CC.P ωC))
              * ∑ c : Fin κ → Bool,
                coinWt (coinW A BL BR ωA ωL ωR (ε := ε)) c := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun c _ => by ring
          _ = _ := by rw [hcsum, mul_one]
      calc ∑ ωC, ∑ c : Fin κ → Bool, BL.P ωL * (BR.P ωR * (CC.P ωC
          * coinWt (coinW A BL BR ωA ωL ωR (ε := ε)) c))
          = ∑ ωC, BL.P ωL * (BR.P ωR * CC.P ωC) :=
            Finset.sum_congr rfl fun ωC _ => h4 ωC
        _ = BL.P ωL * BR.P ωR := by
            have h5 : ∑ ωC, BL.P ωL * (BR.P ωR * CC.P ωC)
                = (BL.P ωL * BR.P ωR) * ∑ ωC, CC.P ωC := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun ωC _ => by ring
            rw [h5, CC.hPsum, mul_one]
    calc ∑ ωR, ∑ ω4 : CC.Ω × (Fin κ → Bool), BL.P ωL * (BR.P ωR
        * (CC.P ω4.1 * coinWt (coinW A BL BR ωA ωL ωR (ε := ε)) ω4.2))
        = ∑ ωR, BL.P ωL * BR.P ωR :=
          Finset.sum_congr rfl fun ωR _ => h3 ωR
      _ = BL.P ωL := by
          have h5 : ∑ ωR, BL.P ωL * BR.P ωR
              = BL.P ωL * ∑ ωR, BR.P ωR := by
            rw [Finset.mul_sum]
          rw [h5, BR.hPsum, mul_one]
  calc ∑ ωL, ∑ ω3 : BR.Ω × CC.Ω × (Fin κ → Bool),
      BL.P ωL * (BR.P ω3.1 * (CC.P ω3.2.1
        * coinWt (coinW A BL BR ωA ωL ω3.1 (ε := ε)) ω3.2.2))
      = ∑ ωL, BL.P ωL := Finset.sum_congr rfl fun ωL _ => h2 ωL
    _ = 1 := BL.hPsum

/-- Marginalization of a race sum depending only on the `A`-component. -/
theorem sum_RP_factor_A (hε : 0 < ε) (QA : A.Ω → Prop) [DecidablePred QA]
    (fA : A.Ω → ℝ) :
    ∑ ω ∈ Finset.univ.filter (fun ω : RΩ A BL BR CC κ => QA ω.1),
      RP A BL BR CC κ ε ω * fA ω.1
      = ∑ ωA ∈ Finset.univ.filter QA, A.P ωA * fA ωA := by
  rw [Finset.sum_filter, Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun ωA _ => ?_
  by_cases hQ : QA ωA
  · rw [if_pos hQ]
    have hterm : ∀ ω2 : BL.Ω × BR.Ω × CC.Ω × (Fin κ → Bool),
        (if QA (ωA, ω2).1 then RP A BL BR CC κ ε (ωA, ω2) * fA (ωA, ω2).1
          else 0)
        = (A.P ωA * fA ωA) * (BL.P ω2.1 * (BR.P ω2.2.1 * (CC.P ω2.2.2.1
          * coinWt (coinW A BL BR ωA ω2.1 ω2.2.1 (ε := ε)) ω2.2.2.2))) := by
      intro ω2
      rw [if_pos hQ]
      unfold RP
      ring
    rw [Finset.sum_congr rfl fun ω2 _ => hterm ω2, ← Finset.mul_sum,
      sum_RP_inner A BL BR CC κ ε hε ωA, mul_one]
  · rw [if_neg hQ]
    refine Finset.sum_eq_zero fun ω2 _ => ?_
    rw [if_neg hQ]

/-- The phase-A race prefix is the mapped phase-A prefix. -/
theorem rpre_A (ω : RΩ A BL BR CC κ) {r : ℕ} (hr : r ≤ A.m) :
    rpre A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω r
      = reqMap GmA (((List.ofFn (A.chunk ω.1)).take r).flatten) := by
  unfold rpre
  rw [reqMap_flatten]
  congr 1
  apply List.ext_getElem
  · rw [List.length_take, List.length_map, List.length_take,
      List.length_ofFn, List.length_ofFn]
    unfold mrace
    omega
  · intro rr h1 h2
    rw [List.getElem_take, List.getElem_ofFn, List.getElem_map,
      List.getElem_take, List.getElem_ofFn]
    have hrr : rr < r := by
      rw [List.length_take, List.length_ofFn] at h1
      have hml : A.m ≤ mrace A BL BR CC κ := by
        unfold mrace
        omega
      omega
    rw [rchunk_A A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω
      (by omega : rr < A.m), chunkN_lt A ω.1 (by omega)]

/-- The phase-A chunk-cost bound for the race. -/
theorem race_hcost_A (hε : 0 < ε)
    (πA : Y → X)
    (hπA : ∀ y z : Y, dist (πA y) (πA z) ≤ dist y z)
    (hGA : ∀ S : Set X, ∀ y ∈ GmA S, πA y ∈ S)
    (hGAne : ∀ S : Set X, S.Nonempty → (GmA S).Nonempty)
    {p' : ℝ} (hpe : pe ≤ p')
    {r : ℕ} (hr : r < A.m)
    (ω₀ : RΩ A BL BR CC κ) (E : EvaderAlgorithm Y)
    (bail : List (Set Y) → Bool) :
    rsize A BL BR CC κ ε ω₀ r
      * (∑ ω ∈ Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
          rhist2 A BL BR CC κ ω r = rhist2 A BL BR CC κ ω₀ r),
        RP A BL BR CC κ ε ω)
    ≤ ∑ ω ∈ Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
        rhist2 A BL BR CC κ ω r = rhist2 A BL BR CC κ ω₀ r),
      RP A BL BR CC κ ε ω
        * E.bailCost bail
          (rpre A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω r)
          (rchunk A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω r) p' := by
  set hOrig := ((List.ofFn (A.chunk ω₀.1)).take r).flatten with hOdef
  set hPad := rpre A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω₀ r with hPdef
  have hPadA : hPad = reqMap GmA hOrig := by
    rw [hPdef, rpre_A A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω₀
      (le_of_lt hr)]
  set E' := shadowFrom hOrig.length πA GmA hGA hGAne E hPad with hE'def
  -- start alignment
  have hstart : E'.pos hOrig = πA (E.pos hPad) := by
    rw [hE'def]
    refine shadowFrom_pos_boundary hOrig.length πA GmA hGA hGAne E hPad
      rfl ?_
    intro Sl hgl
    have hSlne : Sl.Nonempty := by
      refine mem_take_flatten_ne A ω₀.1 r ?_
      exact List.mem_of_getLast? hgl
    have hglP : hPad.getLast? = some (GmA Sl) := by
      rw [hPadA]
      unfold reqMap
      rw [getLast?_map', hgl, Option.map_some]
    have hPne : hPad ≠ [] := by
      intro hcon
      rw [hcon] at hglP
      simp at hglP
    have h8 : hPad.getLast hPne = GmA Sl := by
      have h9 := List.getLast?_eq_some_getLast (l := hPad) hPne
      rw [h9] at hglP
      exact Option.some_injective _ hglP
    have hdecomp : hPad.dropLast ++ [GmA Sl] = hPad := by
      rw [← h8]
      exact List.dropLast_append_getLast hPne
    have hmemY : E.pos hPad ∈ GmA Sl := by
      rw [← hdecomp]
      exact E.serves _ _ (hGAne _ hSlne)
    exact hGA _ _ hmemY
  have hmain := A.hcost ⟨r, hr⟩ ω₀.1 E'
    (fun l => bail (hPad ++ reqMap GmA (l.drop hOrig.length)))
  -- rewrite the atom filter to the A-component form
  have hfil : (Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
      rhist2 A BL BR CC κ ω r = rhist2 A BL BR CC κ ω₀ r))
      = Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
        A.hist r ω.1 = A.hist r ω₀.1) := by
    refine Finset.filter_congr fun ω _ => ?_
    rw [rhist2_eq_iff_A A BL BR CC κ (le_of_lt hr)]
  -- mass identity
  have hmass : (∑ ω ∈ Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
      rhist2 A BL BR CC κ ω r = rhist2 A BL BR CC κ ω₀ r),
      RP A BL BR CC κ ε ω)
      = ∑ ωA ∈ Finset.univ.filter
          (fun ωA => A.hist r ωA = A.hist r ω₀.1), A.P ωA := by
    rw [hfil]
    have h2 := sum_RP_factor_A A BL BR CC κ ε hε
      (fun ωA => A.hist r ωA = A.hist r ω₀.1) (fun _ => 1)
    simp only [mul_one] at h2
    exact h2
  -- cost identity
  have hcost2 : (∑ ω ∈ Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
      rhist2 A BL BR CC κ ω r = rhist2 A BL BR CC κ ω₀ r),
      RP A BL BR CC κ ε ω
        * E.bailCost bail
          (rpre A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω r)
          (rchunk A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω r) p')
      = ∑ ωA ∈ Finset.univ.filter
          (fun ωA => A.hist r ωA = A.hist r ω₀.1),
        A.P ωA * E.bailCost bail hPad
          (reqMap GmA (A.chunk ωA ⟨r, hr⟩)) p' := by
    rw [hfil]
    have hterm : ∀ ω ∈ Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
        A.hist r ω.1 = A.hist r ω₀.1),
        RP A BL BR CC κ ε ω
          * E.bailCost bail
            (rpre A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω r)
            (rchunk A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω r) p'
        = RP A BL BR CC κ ε ω
          * (fun ωA => E.bailCost bail hPad
              (reqMap GmA (A.chunk ωA ⟨r, hr⟩)) p') ω.1 := by
      intro ω hω
      rw [Finset.mem_filter] at hω
      have hpre : rpre A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω r
          = hPad := by
        rw [rpre_A A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω
          (le_of_lt hr), hPadA]
        congr 2
        exact take_congr A (le_refl r) hω.2
      have hch : rchunk A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω r
          = reqMap GmA (A.chunk ω.1 ⟨r, hr⟩) := by
        rw [rchunk_A A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω hr,
          chunkN_lt A ω.1 hr]
      rw [hpre, hch]
    rw [Finset.sum_congr rfl hterm]
    exact sum_RP_factor_A A BL BR CC κ ε hε
      (fun ωA => A.hist r ωA = A.hist r ω₀.1)
      (fun ωA => E.bailCost bail hPad (reqMap GmA (A.chunk ωA ⟨r, hr⟩)) p')
  -- per-outcome shadow domination
  have hdom : ∀ ωA ∈ Finset.univ.filter
      (fun ωA => A.hist r ωA = A.hist r ω₀.1),
      A.P ωA * E'.bailCost
          (fun l => bail (hPad ++ reqMap GmA (l.drop hOrig.length)))
          (((List.ofFn (A.chunk ωA)).take r).flatten)
          (A.chunk ωA ⟨r, hr⟩) pe
      ≤ A.P ωA * E.bailCost bail hPad
          (reqMap GmA (A.chunk ωA ⟨r, hr⟩)) p' := by
    intro ωA hωA
    rw [Finset.mem_filter] at hωA
    have hpre : ((List.ofFn (A.chunk ωA)).take r).flatten = hOrig := by
      rw [hOdef]
      congr 1
      exact take_congr A (le_refl r) hωA.2
    rw [hpre]
    refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (A.hP ωA))
    exact shadowFrom_bailCost_le hOrig.length πA GmA hπA hGA hGAne E bail
      hPad hOrig (A.chunk ωA ⟨r, hr⟩) hpe rfl hstart
  -- assemble
  rw [rsize_A A BL BR CC κ ε ω₀ hr, hmass, hcost2]
  have hsize : A.sizeN r ω₀.1 = A.size ω₀.1 ⟨r, hr⟩ := by
    unfold ChunkSystemB.sizeN
    rw [dif_pos hr]
  rw [hsize]
  exact le_trans hmain (Finset.sum_le_sum hdom)

end PhaseA



section CoinInfra

variable (A BL BR CC : ChunkSystemB X s t 0 cB T pe mL)
variable (GmA GmL GmR GmTL GmTR : Set X → Set Y) (stopPt : Y)
variable (κ : ℕ) (ε : ℝ)

open Classical in
/-- The boundary position of the offset park shadow: with the evader out
of the park and the last request containing the projected position, the
shadow sits at the projected position. -/
theorem parkShadowFrom_pos_boundary
    (n : ℕ) (π : Y → X) (G : Set X → Set Y) (Pk : Set Y)
    (hG : ∀ S : Set X, ∀ y ∈ G S, π y ∈ S)
    (hGne : ∀ S : Set X, S.Nonempty → (G S).Nonempty)
    (E : EvaderAlgorithm Y) (h₀ : List (Set Y)) {h : List (Set X)}
    (hh : h.length = n)
    (hout : E.pos h₀ ∉ Pk)
    (hmem : ∀ S : Set X, h.getLast? = some S → π (E.pos h₀) ∈ S) :
    (parkShadowFrom n π G Pk hG hGne E h₀).pos h = π (E.pos h₀) := by
  have hlen : h.length ≤ n := le_of_eq hh
  have hdrop : h.drop n = [] := by
    rw [← hh]
    exact List.drop_length
  have hmap : parkMap G Pk ([] : List (Set X)) = [] := by
    unfold parkMap
    rw [List.map_nil]
  unfold parkShadowFrom
  simp only [hdrop, hmap, List.append_nil]
  rw [if_neg hout, if_pos hlen]
  cases hgl : h.getLast? with
  | none => simp only [hgl]
  | some Sl =>
    simp only [hgl]
    rw [if_pos (hmem Sl hgl)]

/-- Every request of a race prefix is nonempty. -/
theorem mem_rpre_ne
    (hGneA : ∀ S : Set X, S.Nonempty → (GmA S).Nonempty)
    (hGneL : ∀ S : Set X, S.Nonempty → (GmL S).Nonempty)
    (hGneR : ∀ S : Set X, S.Nonempty → (GmR S).Nonempty)
    (hGneTL : ∀ S : Set X, S.Nonempty → (GmTL S).Nonempty)
    (hGneTR : ∀ S : Set X, S.Nonempty → (GmTR S).Nonempty)
    (ω : RΩ A BL BR CC κ) (r : ℕ) {S : Set Y}
    (hS : S ∈ rpre A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω r) :
    S.Nonempty := by
  unfold rpre at hS
  rw [List.mem_flatten] at hS
  obtain ⟨l, hl, hSl⟩ := hS
  have hl2 : l ∈ List.ofFn (fun i : Fin (mrace A BL BR CC κ) =>
      rchunk A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω (i : ℕ)) :=
    List.mem_of_mem_take hl
  rw [List.mem_ofFn] at hl2
  obtain ⟨i, rfl⟩ := hl2
  exact race_ne A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ
    hGneA hGneL hGneR hGneTL hGneTR ω (i : ℕ) S hSl

/-- The last element of a consumed chunk is the next running last. -/
theorem chunkN_getLast?_lastXset (C : ChunkSystemB X s t 0 cB T pe mL)
    (ωc : C.Ω) {idx : ℕ} (hm : idx < C.m)
    (hne : chunkN C ωc idx ≠ []) :
    (chunkN C ωc idx).getLast? = some (lastXset C ωc (idx + 1)) := by
  have hchunkN : chunkN C ωc idx = C.chunk ωc ⟨idx, hm⟩ := chunkN_lt C ωc hm
  unfold lastXset
  rw [take_succ_ofFn (C.chunk ωc) hm, List.flatten_append,
    List.flatten_cons, List.flatten_nil, List.append_nil,
    List.getLast?_append_of_ne_nil _ (by rw [← hchunkN]; exact hne),
    ← hchunkN]
  cases hgl : (chunkN C ωc idx).getLast? with
  | none => exact absurd (List.getLast?_eq_none_iff.mp hgl) hne
  | some Z => rw [Option.getD_some]

/-- The exact shape of the last coin-phase request: at the phase start it
is the mapped exit pin; after `j ≥ 1` coins it is the union of the two
sides' running last positions (in one of the two orders). -/
theorem rpre_getLast_coin_exact (hκL : κ ≤ BL.m) (hκR : κ ≤ BR.m)
    (hchA : ∀ (ωa : A.Ω) (i : Fin A.m), A.chunk ωa i ≠ [])
    (hchL : ∀ (ωl : BL.Ω) (i : Fin BL.m), BL.chunk ωl i ≠ [])
    (hchR : ∀ (ωr : BR.Ω) (i : Fin BR.m), BR.chunk ωr i ≠ [])
    (ω : RΩ A BL BR CC κ) {j : ℕ} (hj : j ≤ κ) :
    (j = 0 ∧ (rpre A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω
        (A.m + j)).getLast? = some (GmA ({t} : Set X)))
    ∨ ((rpre A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω
        (A.m + j)).getLast?
        = some (GmL (lastXset BL ω.2.1 (cntL ω.2.2.2.2 j))
          ∪ GmR (lastXset BR ω.2.2.1 (cntR ω.2.2.2.2 j))))
    ∨ ((rpre A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω
        (A.m + j)).getLast?
        = some (GmR (lastXset BR ω.2.2.1 (cntR ω.2.2.2.2 j))
          ∪ GmL (lastXset BL ω.2.1 (cntL ω.2.2.2.2 j)))) := by
  have hm0 := A.hm0
  have hrm1 : A.m + j - 1 < mrace A BL BR CC κ := by
    unfold mrace
    omega
  have hdec : rpre A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω (A.m + j)
      = rpre A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω (A.m + j - 1)
        ++ rchunk A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω
          (A.m + j - 1) := by
    unfold rpre
    have h1 : (List.ofFn (fun i : Fin (mrace A BL BR CC κ) =>
        rchunk A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω (i : ℕ))).take
          (A.m + j)
        = (List.ofFn (fun i : Fin (mrace A BL BR CC κ) =>
          rchunk A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω (i : ℕ))).take
            ((A.m + j - 1) + 1) := by
      congr 1
      omega
    rw [h1, take_succ_ofFn _ hrm1, List.flatten_append, List.flatten_cons,
      List.flatten_nil, List.append_nil]
  rcases Nat.eq_zero_or_pos j with hj0 | hj0
  · left
    refine ⟨hj0, ?_⟩
    subst hj0
    rw [hdec]
    have hre : A.m + 0 - 1 = A.m - 1 := by omega
    rw [hre, rchunk_A A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω
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
  · have hjj : j - 1 < κ := by omega
    have hje : A.m + j - 1 = A.m + (j - 1) := by omega
    rw [hdec, hje, rchunk_coin A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ
      ω hjj]
    by_cases hb : ω.2.2.2.2 ⟨j - 1, hjj⟩
    · right; left
      rw [if_pos hb]
      have hcnt : cntL ω.2.2.2.2 (j - 1) < BL.m := by
        have h1 := cntL_le ω.2.2.2.2 (le_of_lt hjj)
        omega
      have hne3 : chunkN BL ω.2.1 (cntL ω.2.2.2.2 (j - 1)) ≠ [] := by
        rw [chunkN_lt BL ω.2.1 hcnt]
        exact hchL ω.2.1 _
      have hne2 : parkMap GmL (parkR A BL BR CC GmR κ ω (j - 1))
          (chunkN BL ω.2.1 (cntL ω.2.2.2.2 (j - 1))) ≠ [] := by
        unfold parkMap
        intro hcon
        rw [List.map_eq_nil_iff] at hcon
        exact hne3 hcon
      rw [List.getLast?_append_of_ne_nil _ hne2]
      unfold parkMap
      rw [getLast?_map',
        List.getLast?_eq_some_getLast
          (l := chunkN BL ω.2.1 (cntL ω.2.2.2.2 (j - 1))) hne3,
        Option.map_some]
      have hstep : cntL ω.2.2.2.2 j = cntL ω.2.2.2.2 (j - 1) + 1 := by
        have h1 := cntL_succ ω.2.2.2.2 hjj
        rw [if_pos hb] at h1
        rw [show j = (j - 1) + 1 from by omega]
        exact h1
      have hstepR : cntR ω.2.2.2.2 j = cntR ω.2.2.2.2 (j - 1) := by
        have h1 := cntR_succ ω.2.2.2.2 hjj
        rw [if_neg (by simp [hb]), Nat.add_zero] at h1
        rw [show j = (j - 1) + 1 from by omega]
        exact h1
      have hlx? := chunkN_getLast?_lastXset BL ω.2.1 hcnt hne3
      have hlgl : (chunkN BL ω.2.1 (cntL ω.2.2.2.2 (j - 1))).getLast hne3
          = lastXset BL ω.2.1 (cntL ω.2.2.2.2 (j - 1) + 1) := by
        rw [List.getLast?_eq_some_getLast
          (l := chunkN BL ω.2.1 (cntL ω.2.2.2.2 (j - 1))) hne3] at hlx?
        exact Option.some_injective _ hlx?
      show some (GmL ((chunkN BL ω.2.1
          (cntL ω.2.2.2.2 (j - 1))).getLast hne3)
          ∪ parkR A BL BR CC GmR κ ω (j - 1)) = _
      rw [hlgl, ← hstep]
      unfold parkR
      rw [← hstepR]
    · right; right
      rw [if_neg hb]
      have hcnt : cntR ω.2.2.2.2 (j - 1) < BR.m := by
        have h1 := cntR_le ω.2.2.2.2 (le_of_lt hjj)
        omega
      have hne3 : chunkN BR ω.2.2.1 (cntR ω.2.2.2.2 (j - 1)) ≠ [] := by
        rw [chunkN_lt BR ω.2.2.1 hcnt]
        exact hchR ω.2.2.1 _
      have hne2 : parkMap GmR (parkL A BL BR CC GmL κ ω (j - 1))
          (chunkN BR ω.2.2.1 (cntR ω.2.2.2.2 (j - 1))) ≠ [] := by
        unfold parkMap
        intro hcon
        rw [List.map_eq_nil_iff] at hcon
        exact hne3 hcon
      rw [List.getLast?_append_of_ne_nil _ hne2]
      unfold parkMap
      rw [getLast?_map',
        List.getLast?_eq_some_getLast
          (l := chunkN BR ω.2.2.1 (cntR ω.2.2.2.2 (j - 1))) hne3,
        Option.map_some]
      have hstep : cntR ω.2.2.2.2 j = cntR ω.2.2.2.2 (j - 1) + 1 := by
        have h1 := cntR_succ ω.2.2.2.2 hjj
        rw [if_pos (by simp [hb])] at h1
        rw [show j = (j - 1) + 1 from by omega]
        exact h1
      have hstepL : cntL ω.2.2.2.2 j = cntL ω.2.2.2.2 (j - 1) := by
        have h1 := cntL_succ ω.2.2.2.2 hjj
        rw [if_neg hb, Nat.add_zero] at h1
        rw [show j = (j - 1) + 1 from by omega]
        exact h1
      have hlx? := chunkN_getLast?_lastXset BR ω.2.2.1 hcnt hne3
      have hlgl : (chunkN BR ω.2.2.1 (cntR ω.2.2.2.2 (j - 1))).getLast hne3
          = lastXset BR ω.2.2.1 (cntR ω.2.2.2.2 (j - 1) + 1) := by
        rw [List.getLast?_eq_some_getLast
          (l := chunkN BR ω.2.2.1 (cntR ω.2.2.2.2 (j - 1))) hne3] at hlx?
        exact Option.some_injective _ hlx?
      show some (GmR ((chunkN BR ω.2.2.1
          (cntR ω.2.2.2.2 (j - 1))).getLast hne3)
          ∪ parkL A BL BR CC GmL κ ω (j - 1)) = _
      rw [hlgl, ← hstep]
      unfold parkL
      rw [← hstepL]

end CoinInfra



section CoinWeights

variable (A BL BR CC : ChunkSystemB X s t 0 cB T pe mL)
variable (κ : ℕ) (ε : ℝ)

/-- Counts of a restricted coin string agree with the original. -/
theorem cntL_restrict {κ : ℕ} (c : Fin κ → Bool) {j : ℕ} (hj : j ≤ κ)
    {i : ℕ} (hi : i ≤ j) :
    cntL (restrict c j hj) i = cntL c i := by
  unfold cntL restrict
  congr 1
  refine Finset.filter_congr fun q hq => ?_
  rw [Finset.mem_range] at hq
  constructor
  · intro hall hqκ
    exact hall (by omega)
  · intro hall hqj
    exact hall (by omega)

theorem cntR_restrict {κ : ℕ} (c : Fin κ → Bool) {j : ℕ} (hj : j ≤ κ)
    {i : ℕ} (hi : i ≤ j) :
    cntR (restrict c j hj) i = cntR c i := by
  unfold cntR restrict
  congr 1
  refine Finset.filter_congr fun q hq => ?_
  rw [Finset.mem_range] at hq
  constructor
  · intro hall hqκ
    exact hall (by omega)
  · intro hall hqj
    exact hall (by omega)

theorem coinW_eval (ωA : A.Ω) (ωL : BL.Ω) (ωR : BR.Ω) (j' : ℕ)
    (p : Fin j' → Bool) (b : Bool) :
    coinW A BL BR ωA ωL ωR (ε := ε) j' p b
      = if b then
          probL (BL.sizeN (cntL p j') ωL) (BR.sizeN (cntR p j') ωR) ε
        else
          probL (BR.sizeN (cntR p j') ωR) (BL.sizeN (cntL p j') ωL) ε := rfl

/-- The restriction of a restriction. -/
theorem restrict_restrict {κ : ℕ} (c : Fin κ → Bool) {j q : ℕ}
    (hj : j ≤ κ) (hq : q ≤ j) (hq2 : q ≤ κ) :
    restrict (restrict c j hj) q hq = restrict c q hq2 := by
  funext i
  rfl

/-- The weight of a coin prefix is determined by the side histories at
the prefix counts. -/
theorem coinWt_restrict_congr {j : ℕ} (hj : j ≤ κ) (c₀ : Fin κ → Bool)
    (ωA ω₀A : A.Ω) (ωL ω₀L : BL.Ω) (ωR ω₀R : BR.Ω)
    (hLh : BL.hist (cntL c₀ j) ωL = BL.hist (cntL c₀ j) ω₀L)
    (hRh : BR.hist (cntR c₀ j) ωR = BR.hist (cntR c₀ j) ω₀R) :
    coinWt (coinW A BL BR ωA ωL ωR (ε := ε)) (restrict c₀ j hj)
      = coinWt (coinW A BL BR ω₀A ω₀L ω₀R (ε := ε)) (restrict c₀ j hj) := by
  unfold coinWt
  refine Finset.prod_congr rfl fun q _ => ?_
  rw [coinW_eval, coinW_eval,
    restrict_restrict c₀ hj (le_of_lt q.isLt) (by omega),
    cntL_restrict c₀ (by omega) (le_refl _),
    cntR_restrict c₀ (by omega) (le_refl _)]
  have hszL : BL.sizeN (cntL c₀ (q : ℕ)) ωL
      = BL.sizeN (cntL c₀ (q : ℕ)) ω₀L :=
    sizeN_congr_le BL (cntL_mono c₀ (le_of_lt q.isLt)) hLh
  have hszR : BR.sizeN (cntR c₀ (q : ℕ)) ωR
      = BR.sizeN (cntR c₀ (q : ℕ)) ω₀R :=
    sizeN_congr_le BR (cntR_mono c₀ (le_of_lt q.isLt)) hRh
  rw [hszL, hszR]

end CoinWeights



section CoinFactor

variable (A BL BR CC : ChunkSystemB X s t 0 cB T pe mL)
variable (κ : ℕ) (ε : ℝ)

/-- Splitting the last step off a coin-string weight. -/
theorem coinWt_split_last {n : ℕ} (W : (j : ℕ) → (Fin j → Bool) → Bool → ℝ)
    (c : Fin (n + 1) → Bool) :
    coinWt W c
      = coinWt W (fun i : Fin n => c i.castSucc)
        * W n (fun i : Fin n => c i.castSucc) (c (Fin.last n)) := by
  unfold coinWt
  rw [Fin.prod_univ_castSucc]
  exact congrArg₂ (· * ·) (Finset.prod_congr rfl fun q _ => rfl) rfl

/-- Marginalization of a race sum over a coin-phase atom with side
factors: the tail system integrates out, and the restricted coin mass is
a constant on the atom. -/
theorem sum_RP_factor_coin (hε : 0 < ε)
    (QA : A.Ω → Prop) (QL : BL.Ω → Prop) (QR : BR.Ω → Prop)
    (Qc : (Fin κ → Bool) → Prop)
    [DecidablePred QA] [DecidablePred QL] [DecidablePred QR]
    [DecidablePred Qc]
    (fL : BL.Ω → ℝ) (fR : BR.Ω → ℝ) (wval : ℝ)
    (hW : ∀ (ωA : A.Ω) (ωL : BL.Ω) (ωR : BR.Ω), QL ωL → QR ωR →
      ∑ c ∈ Finset.univ.filter Qc,
        coinWt (coinW A BL BR ωA ωL ωR (ε := ε)) c = wval) :
    ∑ ω ∈ Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
        QA ω.1 ∧ QL ω.2.1 ∧ QR ω.2.2.1 ∧ Qc ω.2.2.2.2),
      RP A BL BR CC κ ε ω * (fL ω.2.1 * fR ω.2.2.1)
      = wval * ((∑ ωA ∈ Finset.univ.filter QA, A.P ωA)
        * ((∑ ωL ∈ Finset.univ.filter QL, BL.P ωL * fL ωL)
          * (∑ ωR ∈ Finset.univ.filter QR, BR.P ωR * fR ωR))) := by
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  have hA : ∀ ωA : A.Ω,
      (∑ ω2 : BL.Ω × BR.Ω × CC.Ω × (Fin κ → Bool),
        if QA ωA ∧ QL ω2.1 ∧ QR ω2.2.1 ∧ Qc ω2.2.2.2 then
          RP A BL BR CC κ ε (ωA, ω2) * (fL ω2.1 * fR ω2.2.1)
        else 0)
      = (if QA ωA then A.P ωA else 0)
        * ((∑ ωL ∈ Finset.univ.filter QL, BL.P ωL * fL ωL)
          * (∑ ωR ∈ Finset.univ.filter QR, BR.P ωR * fR ωR) * wval) := by
    intro ωA
    by_cases hQA : QA ωA
    · rw [if_pos hQA, Fintype.sum_prod_type]
      have hL : ∀ ωL : BL.Ω,
          (∑ ω3 : BR.Ω × CC.Ω × (Fin κ → Bool),
            if QA ωA ∧ QL ωL ∧ QR ω3.1 ∧ Qc ω3.2.2 then
              RP A BL BR CC κ ε (ωA, ωL, ω3) * (fL ωL * fR ω3.1)
            else 0)
          = (if QL ωL then BL.P ωL * fL ωL else 0)
            * (A.P ωA * ((∑ ωR ∈ Finset.univ.filter QR,
              BR.P ωR * fR ωR) * wval)) := by
        intro ωL
        by_cases hQL : QL ωL
        · rw [if_pos hQL, Fintype.sum_prod_type]
          have hR : ∀ ωR : BR.Ω,
              (∑ ω4 : CC.Ω × (Fin κ → Bool),
                if QA ωA ∧ QL ωL ∧ QR ωR ∧ Qc ω4.2 then
                  RP A BL BR CC κ ε (ωA, ωL, ωR, ω4) * (fL ωL * fR ωR)
                else 0)
              = (if QR ωR then BR.P ωR * fR ωR else 0)
                * (A.P ωA * (BL.P ωL * fL ωL) * wval) := by
            intro ωR
            by_cases hQR : QR ωR
            · rw [if_pos hQR, Fintype.sum_prod_type]
              have hC : ∀ ωC : CC.Ω,
                  (∑ c : Fin κ → Bool,
                    if QA ωA ∧ QL ωL ∧ QR ωR ∧ Qc c then
                      RP A BL BR CC κ ε (ωA, ωL, ωR, ωC, c)
                        * (fL ωL * fR ωR)
                    else 0)
                  = CC.P ωC * (A.P ωA * (BL.P ωL * fL ωL)
                    * (BR.P ωR * fR ωR) * wval) := by
                intro ωC
                have hcs := hW ωA ωL ωR hQL hQR
                rw [Finset.sum_filter] at hcs
                calc ∑ c : Fin κ → Bool,
                    (if QA ωA ∧ QL ωL ∧ QR ωR ∧ Qc c then
                      RP A BL BR CC κ ε (ωA, ωL, ωR, ωC, c)
                        * (fL ωL * fR ωR)
                    else 0)
                    = ∑ c : Fin κ → Bool,
                      (A.P ωA * (BL.P ωL * fL ωL) * (BR.P ωR * fR ωR)
                        * CC.P ωC)
                        * (if Qc c then
                          coinWt (coinW A BL BR ωA ωL ωR (ε := ε)) c
                        else 0) := by
                      refine Finset.sum_congr rfl fun c _ => ?_
                      by_cases hQc : Qc c
                      · rw [if_pos ⟨hQA, hQL, hQR, hQc⟩, if_pos hQc]
                        unfold RP
                        ring
                      · rw [if_neg (by
                          intro hcon
                          exact hQc hcon.2.2.2), if_neg hQc, mul_zero]
                  _ = (A.P ωA * (BL.P ωL * fL ωL) * (BR.P ωR * fR ωR)
                        * CC.P ωC) * wval := by
                      rw [← Finset.mul_sum, hcs]
                  _ = CC.P ωC * (A.P ωA * (BL.P ωL * fL ωL)
                        * (BR.P ωR * fR ωR) * wval) := by
                      ring
              calc ∑ ωC : CC.Ω, ∑ c : Fin κ → Bool,
                  (if QA ωA ∧ QL ωL ∧ QR ωR ∧ Qc c then
                    RP A BL BR CC κ ε (ωA, ωL, ωR, ωC, c)
                      * (fL ωL * fR ωR)
                  else 0)
                  = ∑ ωC : CC.Ω, CC.P ωC * (A.P ωA * (BL.P ωL * fL ωL)
                    * (BR.P ωR * fR ωR) * wval) :=
                    Finset.sum_congr rfl fun ωC _ => hC ωC
                _ = (BR.P ωR * fR ωR)
                      * (A.P ωA * (BL.P ωL * fL ωL) * wval) := by
                    rw [← Finset.sum_mul, CC.hPsum, one_mul]
                    ring
            · rw [if_neg hQR, zero_mul]
              refine Finset.sum_eq_zero fun ω4 _ => ?_
              rw [if_neg (by
                intro hcon
                exact hQR hcon.2.2.1)]
          calc ∑ ωR : BR.Ω, ∑ ω4 : CC.Ω × (Fin κ → Bool),
              (if QA ωA ∧ QL ωL ∧ QR ωR ∧ Qc ω4.2 then
                RP A BL BR CC κ ε (ωA, ωL, ωR, ω4) * (fL ωL * fR ωR)
              else 0)
              = ∑ ωR : BR.Ω, (if QR ωR then BR.P ωR * fR ωR else 0)
                * (A.P ωA * (BL.P ωL * fL ωL) * wval) :=
                Finset.sum_congr rfl fun ωR _ => hR ωR
            _ = (∑ ωR ∈ Finset.univ.filter QR, BR.P ωR * fR ωR)
                  * (A.P ωA * (BL.P ωL * fL ωL) * wval) := by
                rw [← Finset.sum_mul]
                repeat rw [Finset.sum_filter]
            _ = (BL.P ωL * fL ωL)
                  * (A.P ωA * ((∑ ωR ∈ Finset.univ.filter QR,
                    BR.P ωR * fR ωR) * wval)) := by
                ring
        · rw [if_neg hQL, zero_mul]
          refine Finset.sum_eq_zero fun ω3 _ => ?_
          rw [if_neg (by
            intro hcon
            exact hQL hcon.2.1)]
      calc ∑ ωL : BL.Ω, ∑ ω3 : BR.Ω × CC.Ω × (Fin κ → Bool),
          (if QA ωA ∧ QL ωL ∧ QR ω3.1 ∧ Qc ω3.2.2 then
            RP A BL BR CC κ ε (ωA, ωL, ω3) * (fL ωL * fR ω3.1)
          else 0)
          = ∑ ωL : BL.Ω, (if QL ωL then BL.P ωL * fL ωL else 0)
            * (A.P ωA * ((∑ ωR ∈ Finset.univ.filter QR,
              BR.P ωR * fR ωR) * wval)) :=
            Finset.sum_congr rfl fun ωL _ => hL ωL
        _ = (∑ ωL ∈ Finset.univ.filter QL, BL.P ωL * fL ωL)
              * (A.P ωA * ((∑ ωR ∈ Finset.univ.filter QR,
                BR.P ωR * fR ωR) * wval)) := by
            rw [← Finset.sum_mul]
            repeat rw [Finset.sum_filter]
        _ = A.P ωA * ((∑ ωL ∈ Finset.univ.filter QL, BL.P ωL * fL ωL)
              * (∑ ωR ∈ Finset.univ.filter QR, BR.P ωR * fR ωR) * wval) := by
            ring
    · rw [if_neg hQA, zero_mul]
      refine Finset.sum_eq_zero fun ω2 _ => ?_
      rw [if_neg (by
        intro hcon
        exact hQA hcon.1)]
  calc ∑ ωA : A.Ω, ∑ ω2 : BL.Ω × BR.Ω × CC.Ω × (Fin κ → Bool),
      (if QA (ωA, ω2).1 ∧ QL (ωA, ω2).2.1 ∧ QR (ωA, ω2).2.2.1
          ∧ Qc (ωA, ω2).2.2.2.2 then
        RP A BL BR CC κ ε (ωA, ω2)
          * (fL (ωA, ω2).2.1 * fR (ωA, ω2).2.2.1)
      else 0)
      = ∑ ωA : A.Ω, (if QA ωA then A.P ωA else 0)
        * ((∑ ωL ∈ Finset.univ.filter QL, BL.P ωL * fL ωL)
          * (∑ ωR ∈ Finset.univ.filter QR, BR.P ωR * fR ωR) * wval) :=
      Finset.sum_congr rfl fun ωA _ => hA ωA
    _ = (∑ ωA ∈ Finset.univ.filter QA, A.P ωA)
        * ((∑ ωL ∈ Finset.univ.filter QL, BL.P ωL * fL ωL)
          * (∑ ωR ∈ Finset.univ.filter QR, BR.P ωR * fR ωR) * wval) := by
        rw [← Finset.sum_mul]
        repeat rw [Finset.sum_filter]
    _ = _ := by ring

end CoinFactor



section CoinMain

variable (A BL BR CC : ChunkSystemB X s t 0 cB T pe mL)
variable (GmA GmL GmR GmTL GmTR : Set X → Set Y) (stopPt : Y)
variable (κ : ℕ) (ε : ℝ)

open Classical in
/-- The coin-phase cost bound, left branch: the evader is separated from
the right side, so the left coin finances the claimed size. -/
theorem race_hcost_coin_L (hε : 0 < ε) (hκL : κ ≤ BL.m) (hκR : κ ≤ BR.m)
    (πL : Y → X)
    (hπL : ∀ y z : Y, dist (πL y) (πL z) ≤ dist y z)
    (hGL : ∀ S : Set X, ∀ y ∈ GmL S, πL y ∈ S)
    (hGneL : ∀ S : Set X, S.Nonempty → (GmL S).Nonempty)
    {sep J p' : ℝ}
    (hpe0 : 0 ≤ pe) (hpe : pe ≤ p') (hsep0 : 0 < sep)
    (hdiam : ∀ x₁ x₂ : X, dist x₁ x₂ ≤ J) (harith : J + pe ≤ sep)
    (hsepL : ∀ SL SR : Set X, ∀ y ∈ GmL SL,
      ∀ z ∈ GmR SR, sep ≤ dist y z)
    (h0L : ∀ a b : BL.Ω, BL.hist 0 a = BL.hist 0 b)
    (h0R : ∀ a b : BR.Ω, BR.hist 0 a = BR.hist 0 b)
    {j : ℕ} (hj : j < κ)
    (ω₀ : RΩ A BL BR CC κ) (E : EvaderAlgorithm Y)
    (bail : List (Set Y) → Bool)
    (hfarR : ∀ S' : Set X, ∀ p ∈ GmR S',
      sep ≤ dist (E.pos (rpre A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ
        ω₀ (A.m + j))) p)
    (hstart2 : ∀ S : Set X,
      (((List.ofFn (BL.chunk ω₀.2.1)).take
        (cntL ω₀.2.2.2.2 j)).flatten).getLast? = some S →
      πL (E.pos (rpre A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ
        ω₀ (A.m + j))) ∈ S) :
    rsize A BL BR CC κ ε ω₀ (A.m + j)
      * (∑ ω ∈ Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
          rhist2 A BL BR CC κ ω (A.m + j)
            = rhist2 A BL BR CC κ ω₀ (A.m + j)),
        RP A BL BR CC κ ε ω)
    ≤ ∑ ω ∈ Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
        rhist2 A BL BR CC κ ω (A.m + j)
          = rhist2 A BL BR CC κ ω₀ (A.m + j)),
      RP A BL BR CC κ ε ω
        * E.bailCost bail
          (rpre A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω (A.m + j))
          (rchunk A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω (A.m + j))
          p' := by
  have hp'0 : 0 ≤ p' := le_trans hpe0 hpe
  have hm0 := A.hm0
  set r := A.m + j with hrdef
  set c₀ := ω₀.2.2.2.2 with hc₀
  set hPad := rpre A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω₀ r
    with hPdef
  set nL0 := BL.sizeN (cntL c₀ j) ω₀.2.1 with hnL0
  set nR0 := BR.sizeN (cntR c₀ j) ω₀.2.2.1 with hnR0
  set pL0 := probL nL0 nR0 ε with hpL0
  set Pk₀ := GmR (lastXset BR ω₀.2.2.1 (cntR c₀ j)) with hPk₀
  set hOrig := ((List.ofFn (BL.chunk ω₀.2.1)).take (cntL c₀ j)).flatten
    with hOdef
  have hcnt : cntL c₀ j < BL.m := by
    have h1 := cntL_le c₀ (le_of_lt hj)
    omega
  -- atom conditions
  set QA : A.Ω → Prop := fun ωA => A.hist A.m ωA = A.hist A.m ω₀.1
    with hQA
  set QL : BL.Ω → Prop :=
    fun ωL => BL.hist (cntL c₀ j) ωL = BL.hist (cntL c₀ j) ω₀.2.1
    with hQL
  set QR : BR.Ω → Prop :=
    fun ωR => BR.hist (cntR c₀ j) ωR = BR.hist (cntR c₀ j) ω₀.2.2.1
    with hQR
  set Qcs : (Fin κ → Bool) → Prop :=
    fun c => ∀ i : Fin κ, (i : ℕ) < j → c i = c₀ i with hQcs
  set Qc1 : (Fin κ → Bool) → Prop :=
    fun c => (∀ i : Fin κ, (i : ℕ) < j → c i = c₀ i) ∧ c ⟨j, hj⟩ = true
    with hQc1
  have hje : r - A.m = j := by omega
  have hiff : ∀ ω : RΩ A BL BR CC κ,
      (rhist2 A BL BR CC κ ω r = rhist2 A BL BR CC κ ω₀ r)
      ↔ (QA ω.1 ∧ QL ω.2.1 ∧ QR ω.2.2.1 ∧ Qcs ω.2.2.2.2) := by
    intro ω
    rcases Nat.eq_zero_or_pos j with hj0 | hj0
    · have hrA : r = A.m := by omega
      have hcl0 : cntL c₀ j = 0 := by
        rw [hj0]
        exact cntL_zero c₀
      have hcr0 : cntR c₀ j = 0 := by
        rw [hj0]
        exact cntR_zero c₀
      rw [hrA, rhist2_eq_iff_A A BL BR CC κ (le_refl _)]
      constructor
      · intro h
        refine ⟨h, ?_, ?_, ?_⟩
        · rw [hQL]
          rw [hcl0]
          exact h0L _ _
        · rw [hQR]
          rw [hcr0]
          exact h0R _ _
        · intro i hi
          omega
      · rintro ⟨h1, -, -, -⟩
        exact h1
    · rw [rhist2_eq_iff_coin A BL BR CC κ (by omega) (by omega), hje]
      constructor
      · rintro ⟨h1, h2, h3, h4⟩
        exact ⟨h1, h3, h4, h2⟩
      · rintro ⟨h1, h2, h3, h4⟩
        exact ⟨h1, h4, h2, h3⟩
  have hfil : (Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
      rhist2 A BL BR CC κ ω r = rhist2 A BL BR CC κ ω₀ r))
      = Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
        QA ω.1 ∧ QL ω.2.1 ∧ QR ω.2.2.1 ∧ Qcs ω.2.2.2.2) := by
    refine Finset.filter_congr fun ω _ => ?_
    exact hiff ω
  -- the constant coin-prefix weight
  set wJ := coinWt (coinW A BL BR ω₀.1 ω₀.2.1 ω₀.2.2.1 (ε := ε))
    (restrict c₀ j (le_of_lt hj)) with hwJ
  have hwJpos : 0 < wJ := by
    rw [hwJ]
    refine coinWt_pos (fun q p b => ?_) _
    rw [coinW_eval]
    by_cases hb : b
    · rw [if_pos hb]
      exact probL_pos hε
    · rw [if_neg hb]
      exact probL_pos hε
  have hWJ : ∀ (ωA : A.Ω) (ωL : BL.Ω) (ωR : BR.Ω), QL ωL → QR ωR →
      ∑ c ∈ Finset.univ.filter Qcs,
        coinWt (coinW A BL BR ωA ωL ωR (ε := ε)) c = wJ := by
    intro ωA ωL ωR hqL hqR
    rw [sum_coinWt_restrict (fun q p => by
        rw [coinW_eval, coinW_eval, if_pos rfl, if_neg (by simp)]
        exact probL_add_probR _ _ ε hε) (le_of_lt hj) c₀]
    rw [hwJ]
    refine coinWt_restrict_congr A BL BR κ ε (le_of_lt hj) c₀ ωA ω₀.1
      ωL ω₀.2.1 ωR ω₀.2.2.1 ?_ ?_
    · exact hqL
    · exact hqR
  -- the coin-true weight
  set c₁ : Fin κ → Bool := fun i => if (i : ℕ) = j then true else c₀ i
    with hc₁
  have hW1 : ∀ (ωA : A.Ω) (ωL : BL.Ω) (ωR : BR.Ω), QL ωL → QR ωR →
      ∑ c ∈ Finset.univ.filter Qc1,
        coinWt (coinW A BL BR ωA ωL ωR (ε := ε)) c = wJ * pL0 := by
    intro ωA ωL ωR hqL hqR
    have hc₁j : c₁ ⟨j, hj⟩ = true := by
      simp [hc₁]
    have hc₁lt : ∀ i : Fin κ, (i : ℕ) < j → c₁ i = c₀ i := by
      intro i hi
      simp only [hc₁]
      rw [if_neg (by omega)]
    have hfil2 : Finset.univ.filter Qc1
        = Finset.univ.filter (fun c : Fin κ → Bool =>
          ∀ i : Fin κ, (i : ℕ) < j + 1 → c i = c₁ i) := by
      refine Finset.filter_congr fun c _ => ?_
      constructor
      · rintro ⟨h1, h2⟩ i hi
        by_cases hij : (i : ℕ) = j
        · have hie : i = ⟨j, hj⟩ := Fin.ext hij
          rw [hie, h2, hc₁j]
        · rw [hc₁lt i (by omega)]
          exact h1 i (by omega)
      · intro h1
        constructor
        · intro i hi
          have h2 := h1 i (by omega)
          rw [hc₁lt i (by omega)] at h2
          exact h2
        · have h2 := h1 ⟨j, hj⟩ (by
            show j < j + 1
            omega)
          rw [hc₁j] at h2
          exact h2
    rw [hfil2, sum_coinWt_restrict (fun q p => by
        rw [coinW_eval, coinW_eval, if_pos rfl, if_neg (by simp)]
        exact probL_add_probR _ _ ε hε) (by omega : j + 1 ≤ κ) c₁]
    have hsplit := coinWt_split_last
      (coinW A BL BR ωA ωL ωR (ε := ε))
      (restrict c₁ (j + 1) (by omega))
    rw [hsplit]
    have hinit : (fun i : Fin j =>
        restrict c₁ (j + 1) (by omega) i.castSucc)
        = restrict c₀ j (le_of_lt hj) := by
      funext i
      show c₁ ⟨(i : ℕ), by omega⟩ = c₀ ⟨(i : ℕ), by omega⟩
      rw [show (⟨(i : ℕ), by omega⟩ : Fin κ)
        = (⟨(i : ℕ), by omega⟩ : Fin κ) from rfl]
      exact hc₁lt ⟨(i : ℕ), by omega⟩ (by
        have := i.isLt
        omega)
    have hlastc : restrict c₁ (j + 1) (by omega) (Fin.last j) = true := by
      show c₁ ⟨j, by omega⟩ = true
      rw [show (⟨j, by omega⟩ : Fin κ) = (⟨j, hj⟩ : Fin κ) from rfl]
      exact hc₁j
    rw [hinit, hlastc, coinW_eval]
    rw [if_pos rfl]
    have hcnl : cntL (restrict c₀ j (le_of_lt hj)) j = cntL c₀ j :=
      cntL_restrict c₀ (le_of_lt hj) (le_refl j)
    have hcnr : cntR (restrict c₀ j (le_of_lt hj)) j = cntR c₀ j :=
      cntR_restrict c₀ (le_of_lt hj) (le_refl j)
    rw [hcnl, hcnr]
    have hszL : BL.sizeN (cntL c₀ j) ωL = nL0 := by
      rw [hnL0]
      exact BL.sizeN_congr hqL
    have hszR : BR.sizeN (cntR c₀ j) ωR = nR0 := by
      rw [hnR0]
      exact BR.sizeN_congr hqR
    rw [hszL, hszR, ← hpL0]
    congr 1
    rw [hwJ]
    exact coinWt_restrict_congr A BL BR κ ε (le_of_lt hj) c₀ ωA ω₀.1
      ωL ω₀.2.1 ωR ω₀.2.2.1 hqL hqR
  -- masses
  set mA := ∑ ωA ∈ Finset.univ.filter QA, A.P ωA with hmA
  set mLmass := ∑ ωL ∈ Finset.univ.filter QL, BL.P ωL with hmL
  set mRmass := ∑ ωR ∈ Finset.univ.filter QR, BR.P ωR with hmR
  have hmA0 : 0 ≤ mA :=
    Finset.sum_nonneg fun ωA _ => le_of_lt (A.hP ωA)
  have hmL0 : 0 ≤ mLmass :=
    Finset.sum_nonneg fun ωL _ => le_of_lt (BL.hP ωL)
  have hmR0 : 0 ≤ mRmass :=
    Finset.sum_nonneg fun ωR _ => le_of_lt (BR.hP ωR)
  have hmass : (∑ ω ∈ Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
      rhist2 A BL BR CC κ ω r = rhist2 A BL BR CC κ ω₀ r),
      RP A BL BR CC κ ε ω) = wJ * (mA * (mLmass * mRmass)) := by
    rw [hfil]
    have h1 := sum_RP_factor_coin A BL BR CC κ ε hε QA QL QR Qcs
      (fun _ => 1) (fun _ => 1) wJ hWJ
    have h2 : ∀ ω ∈ Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
        QA ω.1 ∧ QL ω.2.1 ∧ QR ω.2.2.1 ∧ Qcs ω.2.2.2.2),
        RP A BL BR CC κ ε ω = RP A BL BR CC κ ε ω * ((1:ℝ) * 1) := by
      intro ω _
      ring
    rw [Finset.sum_congr rfl h2, h1]
    have h3 : ∑ ωL ∈ Finset.univ.filter QL, BL.P ωL * (1:ℝ) = mLmass := by
      rw [hmL]
      exact Finset.sum_congr rfl fun ωL _ => mul_one _
    have h4 : ∑ ωR ∈ Finset.univ.filter QR, BR.P ωR * (1:ℝ) = mRmass := by
      rw [hmR]
      exact Finset.sum_congr rfl fun ωR _ => mul_one _
    rw [h3, h4]
  -- the side-shadow evader
  set SH := parkShadowFrom hOrig.length πL GmL Pk₀ hGL hGneL E hPad
    with hSHdef
  set bailL : List (Set X) → Bool := fun l =>
    bail (hPad ++ parkMap GmL Pk₀ (l.drop hOrig.length))
      || decide (E.pos (hPad ++ parkMap GmL Pk₀ (l.drop hOrig.length))
        ∈ Pk₀) with hbailL
  have hout : E.pos hPad ∉ Pk₀ := by
    intro hmem
    have h1 := hfarR _ _ hmem
    rw [dist_self] at h1
    linarith
  have hstart : SH.pos hOrig = πL (E.pos hPad) := by
    rw [hSHdef]
    exact parkShadowFrom_pos_boundary hOrig.length πL GmL Pk₀
      hGL hGneL E hPad rfl hout hstart2
  -- the side cost bound with the transported evader
  have hside := BL.hcost ⟨cntL c₀ j, hcnt⟩ ω₀.2.1 SH bailL
  have hsize0 : BL.size ω₀.2.1 ⟨cntL c₀ j, hcnt⟩ = nL0 := by
    rw [hnL0]
    unfold ChunkSystemB.sizeN
    rw [dif_pos hcnt]
  -- per-outcome park-shadow domination
  have hdom : ∀ ωL ∈ Finset.univ.filter QL,
      BL.P ωL * SH.bailCost bailL
          (((List.ofFn (BL.chunk ωL)).take (cntL c₀ j)).flatten)
          (BL.chunk ωL ⟨cntL c₀ j, hcnt⟩) pe
      ≤ BL.P ωL * E.bailCost bail hPad
          (parkMap GmL Pk₀ (BL.chunk ωL ⟨cntL c₀ j, hcnt⟩)) p' := by
    intro ωL hωL
    rw [Finset.mem_filter] at hωL
    have hpre : ((List.ofFn (BL.chunk ωL)).take (cntL c₀ j)).flatten
        = hOrig := by
      rw [hOdef]
      congr 1
      exact take_congr BL (le_refl _) hωL.2
    rw [hpre]
    refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (BL.hP ωL))
    rw [hSHdef, hbailL]
    exact parkShadowFrom_bailCost_le hOrig.length πL GmL Pk₀ hπL hGL
      hGneL E bail hPad hOrig (BL.chunk ωL ⟨cntL c₀ j, hcnt⟩)
      hpe0 hpe hsep0
      (fun S y z hy hz => hsepL S _ y hy z hz)
      (fun z hz => hfarR _ _ hz) hdiam harith
      (fun q hq => BL.hne ωL _ _ (List.getElem_mem _))
      rfl hstart
  -- the coin-true part of the goal sum
  have hsub : ∑ ω ∈ Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
      QA ω.1 ∧ QL ω.2.1 ∧ QR ω.2.2.1 ∧ Qc1 ω.2.2.2.2),
      RP A BL BR CC κ ε ω
        * E.bailCost bail
          (rpre A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω r)
          (rchunk A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω r) p'
      ≤ ∑ ω ∈ Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
        rhist2 A BL BR CC κ ω r = rhist2 A BL BR CC κ ω₀ r),
        RP A BL BR CC κ ε ω
          * E.bailCost bail
            (rpre A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω r)
            (rchunk A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω r) p' := by
    rw [hfil]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro ω hω
      rw [Finset.mem_filter] at hω ⊢
      obtain ⟨hu, h1, h2, h3, h4⟩ := hω
      exact ⟨hu, h1, h2, h3, h4.1⟩
    · intro ω _ _
      refine mul_nonneg (le_of_lt (RP_pos A BL BR CC κ ε hε ω)) ?_
      exact E.bailCost_nonneg _ _ _ hp'0
  -- identify the integrand on the coin-true part
  have hident : ∀ ω ∈ Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
      QA ω.1 ∧ QL ω.2.1 ∧ QR ω.2.2.1 ∧ Qc1 ω.2.2.2.2),
      RP A BL BR CC κ ε ω
        * E.bailCost bail
          (rpre A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω r)
          (rchunk A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω r) p'
      = RP A BL BR CC κ ε ω
        * ((fun ωL => E.bailCost bail hPad
            (parkMap GmL Pk₀ (BL.chunk ωL ⟨cntL c₀ j, hcnt⟩)) p') ω.2.1
          * (fun _ : BR.Ω => (1:ℝ)) ω.2.2.1) := by
    intro ω hω
    rw [Finset.mem_filter] at hω
    obtain ⟨-, hqA, hqL, hqR, hqcs, hqj⟩ :=
      And.intro hω.1 hω.2
    -- the atom equality
    have hatom : rhist2 A BL BR CC κ ω r = rhist2 A BL BR CC κ ω₀ r :=
      (hiff ω).mpr ⟨hqA, hqL, hqR, hqcs⟩
    have hpre : rpre A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω r
        = hPad := by
      rw [hPdef]
      exact rpre_congr A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ hκL hκR
        hatom
    have hcntω : cntL ω.2.2.2.2 j = cntL c₀ j := cntL_congr hqcs
    have hcntωR : cntR ω.2.2.2.2 j = cntR c₀ j := cntR_congr hqcs
    have hch : rchunk A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω r
        = parkMap GmL Pk₀ (BL.chunk ω.2.1 ⟨cntL c₀ j, hcnt⟩) := by
      rw [rchunk_coin A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω hj,
        if_pos hqj]
      congr 1
      · rw [hPk₀]
        unfold parkR
        rw [hcntωR]
        congr 1
        exact lastXset_congr BR (le_refl _) hqR
      · rw [hcntω, chunkN_lt BL ω.2.1 hcnt]
    rw [hpre, hch]
    ring
  -- the factored coin-true sum
  have hmR1 : (∑ ωR ∈ Finset.univ.filter QR, BR.P ωR * (1:ℝ)) = mRmass := by
    rw [hmR]
    exact Finset.sum_congr rfl fun _ _ => mul_one _
  have hpart : ∑ ω ∈ Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
      QA ω.1 ∧ QL ω.2.1 ∧ QR ω.2.2.1 ∧ Qc1 ω.2.2.2.2),
      RP A BL BR CC κ ε ω
        * E.bailCost bail
          (rpre A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω r)
          (rchunk A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω r) p'
      = (wJ * pL0) * (mA * ((∑ ωL ∈ Finset.univ.filter QL,
          BL.P ωL * E.bailCost bail hPad
            (parkMap GmL Pk₀ (BL.chunk ωL ⟨cntL c₀ j, hcnt⟩)) p')
        * mRmass)) := by
    rw [Finset.sum_congr rfl hident]
    rw [sum_RP_factor_coin A BL BR CC κ ε hε QA QL QR Qc1
      (fun ωL => E.bailCost bail hPad
        (parkMap GmL Pk₀ (BL.chunk ωL ⟨cntL c₀ j, hcnt⟩)) p')
      (fun _ => 1) (wJ * pL0) hW1, hmR1]
  -- the side premise transported
  have hpL0pos : 0 < pL0 := by
    rw [hpL0]
    exact probL_pos hε
  have hbailsum : nL0 * mLmass ≤ ∑ ωL ∈ Finset.univ.filter QL,
      BL.P ωL * E.bailCost bail hPad
        (parkMap GmL Pk₀ (BL.chunk ωL ⟨cntL c₀ j, hcnt⟩)) p' := by
    have h1 : nL0 * mLmass ≤ ∑ ωL ∈ Finset.univ.filter QL,
        BL.P ωL * SH.bailCost bailL
          (((List.ofFn (BL.chunk ωL)).take (cntL c₀ j)).flatten)
          (BL.chunk ωL ⟨cntL c₀ j, hcnt⟩) pe := by
      rw [← hsize0]
      exact hside
    exact le_trans h1 (Finset.sum_le_sum hdom)
  -- assemble
  have hrsize : rsize A BL BR CC κ ε ω₀ r
      = min (pL0 * nL0) (probL nR0 nL0 ε * nR0) := by
    rw [hrdef, rsize_coin A BL BR CC κ ε ω₀ hj]
    rfl
  calc rsize A BL BR CC κ ε ω₀ r
      * (∑ ω ∈ Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
          rhist2 A BL BR CC κ ω r = rhist2 A BL BR CC κ ω₀ r),
        RP A BL BR CC κ ε ω)
      = min (pL0 * nL0) (probL nR0 nL0 ε * nR0)
        * (wJ * (mA * (mLmass * mRmass))) := by
        rw [hrsize, hmass]
    _ ≤ (pL0 * nL0) * (wJ * (mA * (mLmass * mRmass))) := by
        refine mul_le_mul_of_nonneg_right (min_le_left _ _) ?_
        exact mul_nonneg (le_of_lt hwJpos)
          (mul_nonneg hmA0 (mul_nonneg hmL0 hmR0))
    _ = (wJ * pL0) * (mA * ((nL0 * mLmass) * mRmass)) := by
        ring
    _ ≤ (wJ * pL0) * (mA * ((∑ ωL ∈ Finset.univ.filter QL,
          BL.P ωL * E.bailCost bail hPad
            (parkMap GmL Pk₀ (BL.chunk ωL ⟨cntL c₀ j, hcnt⟩)) p')
        * mRmass)) := by
        refine mul_le_mul_of_nonneg_left ?_
          (mul_nonneg (le_of_lt hwJpos) (le_of_lt hpL0pos))
        refine mul_le_mul_of_nonneg_left ?_ hmA0
        exact mul_le_mul_of_nonneg_right hbailsum hmR0
    _ = ∑ ω ∈ Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
          QA ω.1 ∧ QL ω.2.1 ∧ QR ω.2.2.1 ∧ Qc1 ω.2.2.2.2),
        RP A BL BR CC κ ε ω
          * E.bailCost bail
            (rpre A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω r)
            (rchunk A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω r) p' :=
        hpart.symm
    _ ≤ _ := hsub


open Classical in
/-- The coin-phase cost bound, right branch: the evader is separated from
the left side, so the right coin finances the claimed size. -/
theorem race_hcost_coin_R (hε : 0 < ε) (hκL : κ ≤ BL.m) (hκR : κ ≤ BR.m)
    (πR : Y → X)
    (hπR : ∀ y z : Y, dist (πR y) (πR z) ≤ dist y z)
    (hGR : ∀ S : Set X, ∀ y ∈ GmR S, πR y ∈ S)
    (hGneR : ∀ S : Set X, S.Nonempty → (GmR S).Nonempty)
    {sep J p' : ℝ}
    (hpe0 : 0 ≤ pe) (hpe : pe ≤ p') (hsep0 : 0 < sep)
    (hdiam : ∀ x₁ x₂ : X, dist x₁ x₂ ≤ J) (harith : J + pe ≤ sep)
    (hsepL : ∀ SL SR : Set X, ∀ y ∈ GmL SL,
      ∀ z ∈ GmR SR, sep ≤ dist y z)
    (h0L : ∀ a b : BL.Ω, BL.hist 0 a = BL.hist 0 b)
    (h0R : ∀ a b : BR.Ω, BR.hist 0 a = BR.hist 0 b)
    {j : ℕ} (hj : j < κ)
    (ω₀ : RΩ A BL BR CC κ) (E : EvaderAlgorithm Y)
    (bail : List (Set Y) → Bool)
    (hfarL : ∀ S' : Set X, ∀ p ∈ GmL S',
      sep ≤ dist (E.pos (rpre A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ
        ω₀ (A.m + j))) p)
    (hstart2 : ∀ S : Set X,
      (((List.ofFn (BR.chunk ω₀.2.2.1)).take
        (cntR ω₀.2.2.2.2 j)).flatten).getLast? = some S →
      πR (E.pos (rpre A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ
        ω₀ (A.m + j))) ∈ S) :
    rsize A BL BR CC κ ε ω₀ (A.m + j)
      * (∑ ω ∈ Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
          rhist2 A BL BR CC κ ω (A.m + j)
            = rhist2 A BL BR CC κ ω₀ (A.m + j)),
        RP A BL BR CC κ ε ω)
    ≤ ∑ ω ∈ Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
        rhist2 A BL BR CC κ ω (A.m + j)
          = rhist2 A BL BR CC κ ω₀ (A.m + j)),
      RP A BL BR CC κ ε ω
        * E.bailCost bail
          (rpre A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω (A.m + j))
          (rchunk A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω (A.m + j))
          p' := by
  have hp'0 : 0 ≤ p' := le_trans hpe0 hpe
  have hm0 := A.hm0
  set r := A.m + j with hrdef
  set c₀ := ω₀.2.2.2.2 with hc₀
  set hPad := rpre A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω₀ r
    with hPdef
  set nL0 := BL.sizeN (cntL c₀ j) ω₀.2.1 with hnL0
  set nR0 := BR.sizeN (cntR c₀ j) ω₀.2.2.1 with hnR0
  set pR0 := probL nR0 nL0 ε with hpR0
  set Pk₀ := GmL (lastXset BL ω₀.2.1 (cntL c₀ j)) with hPk₀
  set hOrig := ((List.ofFn (BR.chunk ω₀.2.2.1)).take (cntR c₀ j)).flatten
    with hOdef
  have hcnt : cntR c₀ j < BR.m := by
    have h1 := cntR_le c₀ (le_of_lt hj)
    omega
  -- atom conditions
  set QA : A.Ω → Prop := fun ωA => A.hist A.m ωA = A.hist A.m ω₀.1
    with hQA
  set QL : BL.Ω → Prop :=
    fun ωL => BL.hist (cntL c₀ j) ωL = BL.hist (cntL c₀ j) ω₀.2.1
    with hQL
  set QR : BR.Ω → Prop :=
    fun ωR => BR.hist (cntR c₀ j) ωR = BR.hist (cntR c₀ j) ω₀.2.2.1
    with hQR
  set Qcs : (Fin κ → Bool) → Prop :=
    fun c => ∀ i : Fin κ, (i : ℕ) < j → c i = c₀ i with hQcs
  set Qc1 : (Fin κ → Bool) → Prop :=
    fun c => (∀ i : Fin κ, (i : ℕ) < j → c i = c₀ i) ∧ c ⟨j, hj⟩ = false
    with hQc1
  have hje : r - A.m = j := by omega
  have hiff : ∀ ω : RΩ A BL BR CC κ,
      (rhist2 A BL BR CC κ ω r = rhist2 A BL BR CC κ ω₀ r)
      ↔ (QA ω.1 ∧ QL ω.2.1 ∧ QR ω.2.2.1 ∧ Qcs ω.2.2.2.2) := by
    intro ω
    rcases Nat.eq_zero_or_pos j with hj0 | hj0
    · have hrA : r = A.m := by omega
      have hcl0 : cntL c₀ j = 0 := by
        rw [hj0]
        exact cntL_zero c₀
      have hcr0 : cntR c₀ j = 0 := by
        rw [hj0]
        exact cntR_zero c₀
      rw [hrA, rhist2_eq_iff_A A BL BR CC κ (le_refl _)]
      constructor
      · intro h
        refine ⟨h, ?_, ?_, ?_⟩
        · rw [hQL]
          rw [hcl0]
          exact h0L _ _
        · rw [hQR]
          rw [hcr0]
          exact h0R _ _
        · intro i hi
          omega
      · rintro ⟨h1, -, -, -⟩
        exact h1
    · rw [rhist2_eq_iff_coin A BL BR CC κ (by omega) (by omega), hje]
      constructor
      · rintro ⟨h1, h2, h3, h4⟩
        exact ⟨h1, h3, h4, h2⟩
      · rintro ⟨h1, h2, h3, h4⟩
        exact ⟨h1, h4, h2, h3⟩
  have hfil : (Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
      rhist2 A BL BR CC κ ω r = rhist2 A BL BR CC κ ω₀ r))
      = Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
        QA ω.1 ∧ QL ω.2.1 ∧ QR ω.2.2.1 ∧ Qcs ω.2.2.2.2) := by
    refine Finset.filter_congr fun ω _ => ?_
    exact hiff ω
  -- the constant coin-prefix weight
  set wJ := coinWt (coinW A BL BR ω₀.1 ω₀.2.1 ω₀.2.2.1 (ε := ε))
    (restrict c₀ j (le_of_lt hj)) with hwJ
  have hwJpos : 0 < wJ := by
    rw [hwJ]
    refine coinWt_pos (fun q p b => ?_) _
    rw [coinW_eval]
    by_cases hb : b
    · rw [if_pos hb]
      exact probL_pos hε
    · rw [if_neg hb]
      exact probL_pos hε
  have hWJ : ∀ (ωA : A.Ω) (ωL : BL.Ω) (ωR : BR.Ω), QL ωL → QR ωR →
      ∑ c ∈ Finset.univ.filter Qcs,
        coinWt (coinW A BL BR ωA ωL ωR (ε := ε)) c = wJ := by
    intro ωA ωL ωR hqL hqR
    rw [sum_coinWt_restrict (fun q p => by
        rw [coinW_eval, coinW_eval, if_pos rfl, if_neg (by simp)]
        exact probL_add_probR _ _ ε hε) (le_of_lt hj) c₀]
    rw [hwJ]
    refine coinWt_restrict_congr A BL BR κ ε (le_of_lt hj) c₀ ωA ω₀.1
      ωL ω₀.2.1 ωR ω₀.2.2.1 ?_ ?_
    · exact hqL
    · exact hqR
  -- the coin-true weight
  set c₁ : Fin κ → Bool := fun i => if (i : ℕ) = j then false else c₀ i
    with hc₁
  have hW1 : ∀ (ωA : A.Ω) (ωL : BL.Ω) (ωR : BR.Ω), QL ωL → QR ωR →
      ∑ c ∈ Finset.univ.filter Qc1,
        coinWt (coinW A BL BR ωA ωL ωR (ε := ε)) c = wJ * pR0 := by
    intro ωA ωL ωR hqL hqR
    have hc₁j : c₁ ⟨j, hj⟩ = false := by
      simp [hc₁]
    have hc₁lt : ∀ i : Fin κ, (i : ℕ) < j → c₁ i = c₀ i := by
      intro i hi
      simp only [hc₁]
      rw [if_neg (by omega)]
    have hfil2 : Finset.univ.filter Qc1
        = Finset.univ.filter (fun c : Fin κ → Bool =>
          ∀ i : Fin κ, (i : ℕ) < j + 1 → c i = c₁ i) := by
      refine Finset.filter_congr fun c _ => ?_
      constructor
      · rintro ⟨h1, h2⟩ i hi
        by_cases hij : (i : ℕ) = j
        · have hie : i = ⟨j, hj⟩ := Fin.ext hij
          rw [hie, h2, hc₁j]
        · rw [hc₁lt i (by omega)]
          exact h1 i (by omega)
      · intro h1
        constructor
        · intro i hi
          have h2 := h1 i (by omega)
          rw [hc₁lt i (by omega)] at h2
          exact h2
        · have h2 := h1 ⟨j, hj⟩ (by
            show j < j + 1
            omega)
          rw [hc₁j] at h2
          exact h2
    rw [hfil2, sum_coinWt_restrict (fun q p => by
        rw [coinW_eval, coinW_eval, if_pos rfl, if_neg (by simp)]
        exact probL_add_probR _ _ ε hε) (by omega : j + 1 ≤ κ) c₁]
    have hsplit := coinWt_split_last
      (coinW A BL BR ωA ωL ωR (ε := ε))
      (restrict c₁ (j + 1) (by omega))
    rw [hsplit]
    have hinit : (fun i : Fin j =>
        restrict c₁ (j + 1) (by omega) i.castSucc)
        = restrict c₀ j (le_of_lt hj) := by
      funext i
      show c₁ ⟨(i : ℕ), by omega⟩ = c₀ ⟨(i : ℕ), by omega⟩
      rw [show (⟨(i : ℕ), by omega⟩ : Fin κ)
        = (⟨(i : ℕ), by omega⟩ : Fin κ) from rfl]
      exact hc₁lt ⟨(i : ℕ), by omega⟩ (by
        have := i.isLt
        omega)
    have hlastc : restrict c₁ (j + 1) (by omega) (Fin.last j) = false := by
      show c₁ ⟨j, by omega⟩ = false
      rw [show (⟨j, by omega⟩ : Fin κ) = (⟨j, hj⟩ : Fin κ) from rfl]
      exact hc₁j
    rw [hinit, hlastc, coinW_eval]
    rw [if_neg (by simp)]
    have hcnl : cntL (restrict c₀ j (le_of_lt hj)) j = cntL c₀ j :=
      cntL_restrict c₀ (le_of_lt hj) (le_refl j)
    have hcnr : cntR (restrict c₀ j (le_of_lt hj)) j = cntR c₀ j :=
      cntR_restrict c₀ (le_of_lt hj) (le_refl j)
    rw [hcnl, hcnr]
    have hszL : BL.sizeN (cntL c₀ j) ωL = nL0 := by
      rw [hnL0]
      exact BL.sizeN_congr hqL
    have hszR : BR.sizeN (cntR c₀ j) ωR = nR0 := by
      rw [hnR0]
      exact BR.sizeN_congr hqR
    rw [hszL, hszR, ← hpR0]
    congr 1
    rw [hwJ]
    exact coinWt_restrict_congr A BL BR κ ε (le_of_lt hj) c₀ ωA ω₀.1
      ωL ω₀.2.1 ωR ω₀.2.2.1 hqL hqR
  -- masses
  set mA := ∑ ωA ∈ Finset.univ.filter QA, A.P ωA with hmA
  set mLmass := ∑ ωL ∈ Finset.univ.filter QL, BL.P ωL with hmL
  set mRmass := ∑ ωR ∈ Finset.univ.filter QR, BR.P ωR with hmR
  have hmA0 : 0 ≤ mA :=
    Finset.sum_nonneg fun ωA _ => le_of_lt (A.hP ωA)
  have hmL0 : 0 ≤ mLmass :=
    Finset.sum_nonneg fun ωL _ => le_of_lt (BL.hP ωL)
  have hmR0 : 0 ≤ mRmass :=
    Finset.sum_nonneg fun ωR _ => le_of_lt (BR.hP ωR)
  have hmass : (∑ ω ∈ Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
      rhist2 A BL BR CC κ ω r = rhist2 A BL BR CC κ ω₀ r),
      RP A BL BR CC κ ε ω) = wJ * (mA * (mLmass * mRmass)) := by
    rw [hfil]
    have h1 := sum_RP_factor_coin A BL BR CC κ ε hε QA QL QR Qcs
      (fun _ => 1) (fun _ => 1) wJ hWJ
    have h2 : ∀ ω ∈ Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
        QA ω.1 ∧ QL ω.2.1 ∧ QR ω.2.2.1 ∧ Qcs ω.2.2.2.2),
        RP A BL BR CC κ ε ω = RP A BL BR CC κ ε ω * ((1:ℝ) * 1) := by
      intro ω _
      ring
    rw [Finset.sum_congr rfl h2, h1]
    have h3 : ∑ ωL ∈ Finset.univ.filter QL, BL.P ωL * (1:ℝ) = mLmass := by
      rw [hmL]
      exact Finset.sum_congr rfl fun ωL _ => mul_one _
    have h4 : ∑ ωR ∈ Finset.univ.filter QR, BR.P ωR * (1:ℝ) = mRmass := by
      rw [hmR]
      exact Finset.sum_congr rfl fun ωR _ => mul_one _
    rw [h3, h4]
  -- the side-shadow evader
  set SH := parkShadowFrom hOrig.length πR GmR Pk₀ hGR hGneR E hPad
    with hSHdef
  set bailL : List (Set X) → Bool := fun l =>
    bail (hPad ++ parkMap GmR Pk₀ (l.drop hOrig.length))
      || decide (E.pos (hPad ++ parkMap GmR Pk₀ (l.drop hOrig.length))
        ∈ Pk₀) with hbailL
  have hout : E.pos hPad ∉ Pk₀ := by
    intro hmem
    have h1 := hfarL _ _ hmem
    rw [dist_self] at h1
    linarith
  have hstart : SH.pos hOrig = πR (E.pos hPad) := by
    rw [hSHdef]
    exact parkShadowFrom_pos_boundary hOrig.length πR GmR Pk₀
      hGR hGneR E hPad rfl hout hstart2
  -- the side cost bound with the transported evader
  have hside := BR.hcost ⟨cntR c₀ j, hcnt⟩ ω₀.2.2.1 SH bailL
  have hsize0 : BR.size ω₀.2.2.1 ⟨cntR c₀ j, hcnt⟩ = nR0 := by
    rw [hnR0]
    unfold ChunkSystemB.sizeN
    rw [dif_pos hcnt]
  -- per-outcome park-shadow domination
  have hdom : ∀ ωR ∈ Finset.univ.filter QR,
      BR.P ωR * SH.bailCost bailL
          (((List.ofFn (BR.chunk ωR)).take (cntR c₀ j)).flatten)
          (BR.chunk ωR ⟨cntR c₀ j, hcnt⟩) pe
      ≤ BR.P ωR * E.bailCost bail hPad
          (parkMap GmR Pk₀ (BR.chunk ωR ⟨cntR c₀ j, hcnt⟩)) p' := by
    intro ωR hωR
    rw [Finset.mem_filter] at hωR
    have hpre : ((List.ofFn (BR.chunk ωR)).take (cntR c₀ j)).flatten
        = hOrig := by
      rw [hOdef]
      congr 1
      exact take_congr BR (le_refl _) hωR.2
    rw [hpre]
    refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (BR.hP ωR))
    rw [hSHdef, hbailL]
    exact parkShadowFrom_bailCost_le hOrig.length πR GmR Pk₀ hπR hGR
      hGneR E bail hPad hOrig (BR.chunk ωR ⟨cntR c₀ j, hcnt⟩)
      hpe0 hpe hsep0
      (fun S y z hy hz => by
        rw [dist_comm]
        exact hsepL _ S z hz y hy)
      (fun z hz => hfarL _ _ hz) hdiam harith
      (fun q hq => BR.hne ωR _ _ (List.getElem_mem _))
      rfl hstart
  -- the coin-true part of the goal sum
  have hsub : ∑ ω ∈ Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
      QA ω.1 ∧ QL ω.2.1 ∧ QR ω.2.2.1 ∧ Qc1 ω.2.2.2.2),
      RP A BL BR CC κ ε ω
        * E.bailCost bail
          (rpre A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω r)
          (rchunk A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω r) p'
      ≤ ∑ ω ∈ Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
        rhist2 A BL BR CC κ ω r = rhist2 A BL BR CC κ ω₀ r),
        RP A BL BR CC κ ε ω
          * E.bailCost bail
            (rpre A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω r)
            (rchunk A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω r) p' := by
    rw [hfil]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro ω hω
      rw [Finset.mem_filter] at hω ⊢
      obtain ⟨hu, h1, h2, h3, h4⟩ := hω
      exact ⟨hu, h1, h2, h3, h4.1⟩
    · intro ω _ _
      refine mul_nonneg (le_of_lt (RP_pos A BL BR CC κ ε hε ω)) ?_
      exact E.bailCost_nonneg _ _ _ hp'0
  -- identify the integrand on the coin-true part
  have hident : ∀ ω ∈ Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
      QA ω.1 ∧ QL ω.2.1 ∧ QR ω.2.2.1 ∧ Qc1 ω.2.2.2.2),
      RP A BL BR CC κ ε ω
        * E.bailCost bail
          (rpre A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω r)
          (rchunk A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω r) p'
      = RP A BL BR CC κ ε ω
        * ((fun _ : BL.Ω => (1:ℝ)) ω.2.1
          * (fun ωR => E.bailCost bail hPad
            (parkMap GmR Pk₀ (BR.chunk ωR ⟨cntR c₀ j, hcnt⟩)) p') ω.2.2.1)
        := by
    intro ω hω
    rw [Finset.mem_filter] at hω
    obtain ⟨-, hqA, hqL, hqR, hqcs, hqj⟩ :=
      And.intro hω.1 hω.2
    -- the atom equality
    have hatom : rhist2 A BL BR CC κ ω r = rhist2 A BL BR CC κ ω₀ r :=
      (hiff ω).mpr ⟨hqA, hqL, hqR, hqcs⟩
    have hpre : rpre A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω r
        = hPad := by
      rw [hPdef]
      exact rpre_congr A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ hκL hκR
        hatom
    have hcntω : cntL ω.2.2.2.2 j = cntL c₀ j := cntL_congr hqcs
    have hcntωR : cntR ω.2.2.2.2 j = cntR c₀ j := cntR_congr hqcs
    have hch : rchunk A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω r
        = parkMap GmR Pk₀ (BR.chunk ω.2.2.1 ⟨cntR c₀ j, hcnt⟩) := by
      rw [rchunk_coin A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω hj,
        if_neg (by rw [hqj]; simp)]
      congr 1
      · rw [hPk₀]
        unfold parkL
        rw [hcntω]
        congr 1
        exact lastXset_congr BL (le_refl _) hqL
      · rw [hcntωR, chunkN_lt BR ω.2.2.1 hcnt]
    rw [hpre, hch]
    ring
  -- the factored coin-true sum
  have hmL1 : (∑ ωL ∈ Finset.univ.filter QL, BL.P ωL * (1:ℝ)) = mLmass := by
    rw [hmL]
    exact Finset.sum_congr rfl fun _ _ => mul_one _
  have hpart : ∑ ω ∈ Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
      QA ω.1 ∧ QL ω.2.1 ∧ QR ω.2.2.1 ∧ Qc1 ω.2.2.2.2),
      RP A BL BR CC κ ε ω
        * E.bailCost bail
          (rpre A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω r)
          (rchunk A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω r) p'
      = (wJ * pR0) * (mA * (mLmass
        * (∑ ωR ∈ Finset.univ.filter QR,
          BR.P ωR * E.bailCost bail hPad
            (parkMap GmR Pk₀ (BR.chunk ωR ⟨cntR c₀ j, hcnt⟩)) p'))) := by
    rw [Finset.sum_congr rfl hident]
    rw [sum_RP_factor_coin A BL BR CC κ ε hε QA QL QR Qc1
      (fun _ => 1)
      (fun ωR => E.bailCost bail hPad
        (parkMap GmR Pk₀ (BR.chunk ωR ⟨cntR c₀ j, hcnt⟩)) p')
      (wJ * pR0) hW1, hmL1]
  -- the side premise transported
  have hpR0pos : 0 < pR0 := by
    rw [hpR0]
    exact probL_pos hε
  have hbailsum : nR0 * mRmass ≤ ∑ ωR ∈ Finset.univ.filter QR,
      BR.P ωR * E.bailCost bail hPad
        (parkMap GmR Pk₀ (BR.chunk ωR ⟨cntR c₀ j, hcnt⟩)) p' := by
    have h1 : nR0 * mRmass ≤ ∑ ωR ∈ Finset.univ.filter QR,
        BR.P ωR * SH.bailCost bailL
          (((List.ofFn (BR.chunk ωR)).take (cntR c₀ j)).flatten)
          (BR.chunk ωR ⟨cntR c₀ j, hcnt⟩) pe := by
      rw [← hsize0]
      exact hside
    exact le_trans h1 (Finset.sum_le_sum hdom)
  -- assemble
  have hrsize : rsize A BL BR CC κ ε ω₀ r
      = min (probL nL0 nR0 ε * nL0) (pR0 * nR0) := by
    rw [hrdef, rsize_coin A BL BR CC κ ε ω₀ hj]
    rfl
  calc rsize A BL BR CC κ ε ω₀ r
      * (∑ ω ∈ Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
          rhist2 A BL BR CC κ ω r = rhist2 A BL BR CC κ ω₀ r),
        RP A BL BR CC κ ε ω)
      = min (probL nL0 nR0 ε * nL0) (pR0 * nR0)
        * (wJ * (mA * (mLmass * mRmass))) := by
        rw [hrsize, hmass]
    _ ≤ (pR0 * nR0) * (wJ * (mA * (mLmass * mRmass))) := by
        refine mul_le_mul_of_nonneg_right (min_le_right _ _) ?_
        exact mul_nonneg (le_of_lt hwJpos)
          (mul_nonneg hmA0 (mul_nonneg hmL0 hmR0))
    _ = (wJ * pR0) * (mA * (mLmass * (nR0 * mRmass))) := by
        ring
    _ ≤ (wJ * pR0) * (mA * (mLmass
        * (∑ ωR ∈ Finset.univ.filter QR,
          BR.P ωR * E.bailCost bail hPad
            (parkMap GmR Pk₀ (BR.chunk ωR ⟨cntR c₀ j, hcnt⟩)) p'))) := by
        refine mul_le_mul_of_nonneg_left ?_
          (mul_nonneg (le_of_lt hwJpos) (le_of_lt hpR0pos))
        refine mul_le_mul_of_nonneg_left ?_ hmA0
        exact mul_le_mul_of_nonneg_left hbailsum hmL0
    _ = ∑ ω ∈ Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
          QA ω.1 ∧ QL ω.2.1 ∧ QR ω.2.2.1 ∧ Qc1 ω.2.2.2.2),
        RP A BL BR CC κ ε ω
          * E.bailCost bail
            (rpre A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω r)
            (rchunk A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω r) p' :=
        hpart.symm
    _ ≤ _ := hsub




open Classical in
/-- The coin-phase cost bound: the evader's position after the prefix
lies in the last request, whose shape puts it on one side; the dichotomy
hypothesis separates it from the other side's images, and that side's
coin finances the claimed size. -/
theorem race_hcost_coin (hε : 0 < ε) (hκL : κ ≤ BL.m) (hκR : κ ≤ BR.m)
    (πL πR : Y → X)
    (hπL : ∀ y z : Y, dist (πL y) (πL z) ≤ dist y z)
    (hπR : ∀ y z : Y, dist (πR y) (πR z) ≤ dist y z)
    (hGL : ∀ S : Set X, ∀ y ∈ GmL S, πL y ∈ S)
    (hGR : ∀ S : Set X, ∀ y ∈ GmR S, πR y ∈ S)
    (hGneA : ∀ S : Set X, S.Nonempty → (GmA S).Nonempty)
    (hGneL : ∀ S : Set X, S.Nonempty → (GmL S).Nonempty)
    (hGneR : ∀ S : Set X, S.Nonempty → (GmR S).Nonempty)
    (hGneTL : ∀ S : Set X, S.Nonempty → (GmTL S).Nonempty)
    (hGneTR : ∀ S : Set X, S.Nonempty → (GmTR S).Nonempty)
    (hchA : ∀ (ωa : A.Ω) (i : Fin A.m), A.chunk ωa i ≠ [])
    (hchL : ∀ (ωl : BL.Ω) (i : Fin BL.m), BL.chunk ωl i ≠ [])
    (hchR : ∀ (ωr : BR.Ω) (i : Fin BR.m), BR.chunk ωr i ≠ [])
    {sep J p' : ℝ}
    (hpe0 : 0 ≤ pe) (hpe : pe ≤ p') (hsep0 : 0 < sep)
    (hdiam : ∀ x₁ x₂ : X, dist x₁ x₂ ≤ J) (harith : J + pe ≤ sep)
    (hsepLR : ∀ SL SR : Set X, ∀ y ∈ GmL SL,
      ∀ z ∈ GmR SR, sep ≤ dist y z)
    (hdicho : ∀ z : Y,
      (z ∈ GmA ({t} : Set X) ∨ (∃ S, z ∈ GmL S) ∨ (∃ S, z ∈ GmR S)) →
      (∀ S' : Set X, ∀ p ∈ GmR S', sep ≤ dist z p)
      ∨ (∀ S' : Set X, ∀ p ∈ GmL S', sep ≤ dist z p))
    (h0L : ∀ a b : BL.Ω, BL.hist 0 a = BL.hist 0 b)
    (h0R : ∀ a b : BR.Ω, BR.hist 0 a = BR.hist 0 b)
    {j : ℕ} (hj : j < κ)
    (ω₀ : RΩ A BL BR CC κ) (E : EvaderAlgorithm Y)
    (bail : List (Set Y) → Bool) :
    rsize A BL BR CC κ ε ω₀ (A.m + j)
      * (∑ ω ∈ Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
          rhist2 A BL BR CC κ ω (A.m + j)
            = rhist2 A BL BR CC κ ω₀ (A.m + j)),
        RP A BL BR CC κ ε ω)
    ≤ ∑ ω ∈ Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
        rhist2 A BL BR CC κ ω (A.m + j)
          = rhist2 A BL BR CC κ ω₀ (A.m + j)),
      RP A BL BR CC κ ε ω
        * E.bailCost bail
          (rpre A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω (A.m + j))
          (rchunk A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω (A.m + j))
          p' := by
  set hPad := rpre A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω₀ (A.m + j)
    with hPdef
  set z := E.pos hPad with hzdef
  have hzin : ∀ L₀ : Set Y, hPad.getLast? = some L₀ → z ∈ L₀ := by
    intro L₀ hgl
    have hL₀ne : L₀.Nonempty := by
      refine mem_rpre_ne A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ
        hGneA hGneL hGneR hGneTL hGneTR ω₀ (A.m + j) ?_
      exact List.mem_of_getLast? hgl
    have hPne : hPad ≠ [] := by
      intro hcon
      rw [hcon] at hgl
      simp at hgl
    have h8 : hPad.getLast hPne = L₀ := by
      have h9 := List.getLast?_eq_some_getLast (l := hPad) hPne
      rw [h9] at hgl
      exact Option.some_injective _ hgl
    have hdecomp : hPad.dropLast ++ [L₀] = hPad := by
      rw [← h8]
      exact List.dropLast_append_getLast hPne
    rw [hzdef, ← hdecomp]
    exact E.serves _ _ hL₀ne
  -- identify a running last from a getLast? equation
  have hlxL : ∀ S : Set X,
      (((List.ofFn (BL.chunk ω₀.2.1)).take
        (cntL ω₀.2.2.2.2 j)).flatten).getLast? = some S →
      lastXset BL ω₀.2.1 (cntL ω₀.2.2.2.2 j) = S := by
    intro S hS
    unfold lastXset
    rw [hS, Option.getD_some]
  have hlxR : ∀ S : Set X,
      (((List.ofFn (BR.chunk ω₀.2.2.1)).take
        (cntR ω₀.2.2.2.2 j)).flatten).getLast? = some S →
      lastXset BR ω₀.2.2.1 (cntR ω₀.2.2.2.2 j) = S := by
    intro S hS
    unfold lastXset
    rw [hS, Option.getD_some]
  rcases rpre_getLast_coin_exact A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ
      hκL hκR hchA hchL hchR ω₀ (le_of_lt hj) with ⟨hj0, hgl⟩ | hgl | hgl
  · -- the pin shape: `j = 0`, both consumed prefixes are empty
    have hzA : z ∈ GmA ({t} : Set X) := hzin _ hgl
    have hstart2L : ∀ S : Set X,
        (((List.ofFn (BL.chunk ω₀.2.1)).take
          (cntL ω₀.2.2.2.2 j)).flatten).getLast? = some S →
        πL z ∈ S := by
      intro S hS
      rw [hj0, cntL_zero] at hS
      simp at hS
    have hstart2R : ∀ S : Set X,
        (((List.ofFn (BR.chunk ω₀.2.2.1)).take
          (cntR ω₀.2.2.2.2 j)).flatten).getLast? = some S →
        πR z ∈ S := by
      intro S hS
      rw [hj0, cntR_zero] at hS
      simp at hS
    rcases hdicho z (Or.inl hzA) with hfar | hfar
    · exact race_hcost_coin_L A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ε
        hε hκL hκR πL hπL hGL hGneL hpe0 hpe hsep0 hdiam harith hsepLR
        h0L h0R hj ω₀ E bail hfar hstart2L
    · exact race_hcost_coin_R A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ε
        hε hκL hκR πR hπR hGR hGneR hpe0 hpe hsep0 hdiam harith hsepLR
        h0L h0R hj ω₀ E bail hfar hstart2R
  · -- union, left component first
    have hzu : z ∈ GmL (lastXset BL ω₀.2.1 (cntL ω₀.2.2.2.2 j))
        ∪ GmR (lastXset BR ω₀.2.2.1 (cntR ω₀.2.2.2.2 j)) := hzin _ hgl
    rcases hzu with hzL | hzR
    · rcases hdicho z (Or.inr (Or.inl ⟨_, hzL⟩)) with hfar | hfar
      · refine race_hcost_coin_L A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ε
          hε hκL hκR πL hπL hGL hGneL hpe0 hpe hsep0 hdiam harith hsepLR
          h0L h0R hj ω₀ E bail hfar ?_
        intro S hS
        rw [← hlxL S hS]
        exact hGL _ _ hzL
      · exact absurd (hfar _ _ hzL) (by
          rw [dist_self]
          linarith)
    · rcases hdicho z (Or.inr (Or.inr ⟨_, hzR⟩)) with hfar | hfar
      · exact absurd (hfar _ _ hzR) (by
          rw [dist_self]
          linarith)
      · refine race_hcost_coin_R A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ε
          hε hκL hκR πR hπR hGR hGneR hpe0 hpe hsep0 hdiam harith hsepLR
          h0L h0R hj ω₀ E bail hfar ?_
        intro S hS
        rw [← hlxR S hS]
        exact hGR _ _ hzR
  · -- union, right component first
    have hzu : z ∈ GmR (lastXset BR ω₀.2.2.1 (cntR ω₀.2.2.2.2 j))
        ∪ GmL (lastXset BL ω₀.2.1 (cntL ω₀.2.2.2.2 j)) := hzin _ hgl
    rcases hzu with hzR | hzL
    · rcases hdicho z (Or.inr (Or.inr ⟨_, hzR⟩)) with hfar | hfar
      · exact absurd (hfar _ _ hzR) (by
          rw [dist_self]
          linarith)
      · refine race_hcost_coin_R A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ε
          hε hκL hκR πR hπR hGR hGneR hpe0 hpe hsep0 hdiam harith hsepLR
          h0L h0R hj ω₀ E bail hfar ?_
        intro S hS
        rw [← hlxR S hS]
        exact hGR _ _ hzR
    · rcases hdicho z (Or.inr (Or.inl ⟨_, hzL⟩)) with hfar | hfar
      · refine race_hcost_coin_L A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ε
          hε hκL hκR πL hπL hGL hGneL hpe0 hpe hsep0 hdiam harith hsepLR
          h0L h0R hj ω₀ E bail hfar ?_
        intro S hS
        rw [← hlxL S hS]
        exact hGL _ _ hzL
      · exact absurd (hfar _ _ hzL) (by
          rw [dist_self]
          linarith)

end CoinMain



section TailFactor

variable (A BL BR CC : ChunkSystemB X s t 0 cB T pe mL)
variable (κ : ℕ) (ε : ℝ)

/-- Marginalization of a race sum over a tail atom: the coins are fully
fixed and each component carries its own factor. -/
theorem sum_RP_factor_tail (hε : 0 < ε)
    (QA : A.Ω → Prop) (QL : BL.Ω → Prop) (QR : BR.Ω → Prop)
    (QC : CC.Ω → Prop) (c₀ : Fin κ → Bool)
    [DecidablePred QA] [DecidablePred QL] [DecidablePred QR]
    [DecidablePred QC]
    (fL : BL.Ω → ℝ) (fR : BR.Ω → ℝ) (fC : CC.Ω → ℝ) (wval : ℝ)
    (hW : ∀ (ωA : A.Ω) (ωL : BL.Ω) (ωR : BR.Ω), QL ωL → QR ωR →
      coinWt (coinW A BL BR ωA ωL ωR (ε := ε)) c₀ = wval) :
    ∑ ω ∈ Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
        QA ω.1 ∧ QL ω.2.1 ∧ QR ω.2.2.1 ∧ QC ω.2.2.2.1
          ∧ ω.2.2.2.2 = c₀),
      RP A BL BR CC κ ε ω * (fL ω.2.1 * fR ω.2.2.1 * fC ω.2.2.2.1)
      = wval * ((∑ ωA ∈ Finset.univ.filter QA, A.P ωA)
        * ((∑ ωL ∈ Finset.univ.filter QL, BL.P ωL * fL ωL)
          * ((∑ ωR ∈ Finset.univ.filter QR, BR.P ωR * fR ωR)
            * (∑ ωC ∈ Finset.univ.filter QC, CC.P ωC * fC ωC)))) := by
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  have hA : ∀ ωA : A.Ω,
      (∑ ω2 : BL.Ω × BR.Ω × CC.Ω × (Fin κ → Bool),
        if QA ωA ∧ QL ω2.1 ∧ QR ω2.2.1 ∧ QC ω2.2.2.1 ∧ ω2.2.2.2 = c₀ then
          RP A BL BR CC κ ε (ωA, ω2) * (fL ω2.1 * fR ω2.2.1 * fC ω2.2.2.1)
        else 0)
      = (if QA ωA then A.P ωA else 0)
        * ((∑ ωL ∈ Finset.univ.filter QL, BL.P ωL * fL ωL)
          * ((∑ ωR ∈ Finset.univ.filter QR, BR.P ωR * fR ωR)
            * (∑ ωC ∈ Finset.univ.filter QC, CC.P ωC * fC ωC)) * wval) := by
    intro ωA
    by_cases hQA : QA ωA
    · rw [if_pos hQA, Fintype.sum_prod_type]
      have hL : ∀ ωL : BL.Ω,
          (∑ ω3 : BR.Ω × CC.Ω × (Fin κ → Bool),
            if QA ωA ∧ QL ωL ∧ QR ω3.1 ∧ QC ω3.2.1 ∧ ω3.2.2 = c₀ then
              RP A BL BR CC κ ε (ωA, ωL, ω3)
                * (fL ωL * fR ω3.1 * fC ω3.2.1)
            else 0)
          = (if QL ωL then BL.P ωL * fL ωL else 0)
            * (A.P ωA * ((∑ ωR ∈ Finset.univ.filter QR, BR.P ωR * fR ωR)
              * (∑ ωC ∈ Finset.univ.filter QC, CC.P ωC * fC ωC) * wval))
          := by
        intro ωL
        by_cases hQL : QL ωL
        · rw [if_pos hQL, Fintype.sum_prod_type]
          have hR : ∀ ωR : BR.Ω,
              (∑ ω4 : CC.Ω × (Fin κ → Bool),
                if QA ωA ∧ QL ωL ∧ QR ωR ∧ QC ω4.1 ∧ ω4.2 = c₀ then
                  RP A BL BR CC κ ε (ωA, ωL, ωR, ω4)
                    * (fL ωL * fR ωR * fC ω4.1)
                else 0)
              = (if QR ωR then BR.P ωR * fR ωR else 0)
                * (A.P ωA * (BL.P ωL * fL ωL)
                  * ((∑ ωC ∈ Finset.univ.filter QC, CC.P ωC * fC ωC)
                    * wval)) := by
            intro ωR
            by_cases hQR : QR ωR
            · rw [if_pos hQR, Fintype.sum_prod_type]
              have hC : ∀ ωC : CC.Ω,
                  (∑ c : Fin κ → Bool,
                    if QA ωA ∧ QL ωL ∧ QR ωR ∧ QC ωC ∧ c = c₀ then
                      RP A BL BR CC κ ε (ωA, ωL, ωR, ωC, c)
                        * (fL ωL * fR ωR * fC ωC)
                    else 0)
                  = (if QC ωC then CC.P ωC * fC ωC else 0)
                    * (A.P ωA * (BL.P ωL * fL ωL) * (BR.P ωR * fR ωR)
                      * wval) := by
                intro ωC
                by_cases hQC : QC ωC
                · rw [if_pos hQC]
                  have hfil3 : ∀ c : Fin κ → Bool,
                      (if QA ωA ∧ QL ωL ∧ QR ωR ∧ QC ωC ∧ c = c₀ then
                        RP A BL BR CC κ ε (ωA, ωL, ωR, ωC, c)
                          * (fL ωL * fR ωR * fC ωC)
                      else 0)
                      = (if c = c₀ then
                        RP A BL BR CC κ ε (ωA, ωL, ωR, ωC, c)
                          * (fL ωL * fR ωR * fC ωC)
                      else 0) := by
                    intro c
                    by_cases hc : c = c₀
                    · rw [if_pos ⟨hQA, hQL, hQR, hQC, hc⟩, if_pos hc]
                    · rw [if_neg (by
                        intro hcon
                        exact hc hcon.2.2.2.2), if_neg hc]
                  rw [Finset.sum_congr rfl fun c _ => hfil3 c,
                    Finset.sum_ite_eq' Finset.univ c₀
                      (fun c => RP A BL BR CC κ ε (ωA, ωL, ωR, ωC, c)
                        * (fL ωL * fR ωR * fC ωC))]
                  rw [if_pos (Finset.mem_univ _)]
                  unfold RP
                  rw [hW ωA ωL ωR hQL hQR]
                  ring
                · rw [if_neg hQC, zero_mul]
                  refine Finset.sum_eq_zero fun c _ => ?_
                  rw [if_neg (by
                    intro hcon
                    exact hQC hcon.2.2.2.1)]
              calc ∑ ωC : CC.Ω, ∑ c : Fin κ → Bool,
                  (if QA ωA ∧ QL ωL ∧ QR ωR ∧ QC ωC ∧ c = c₀ then
                    RP A BL BR CC κ ε (ωA, ωL, ωR, ωC, c)
                      * (fL ωL * fR ωR * fC ωC)
                  else 0)
                  = ∑ ωC : CC.Ω, (if QC ωC then CC.P ωC * fC ωC else 0)
                    * (A.P ωA * (BL.P ωL * fL ωL) * (BR.P ωR * fR ωR)
                      * wval) :=
                    Finset.sum_congr rfl fun ωC _ => hC ωC
                _ = (∑ ωC ∈ Finset.univ.filter QC, CC.P ωC * fC ωC)
                      * (A.P ωA * (BL.P ωL * fL ωL) * (BR.P ωR * fR ωR)
                        * wval) := by
                    rw [← Finset.sum_mul]
                    repeat rw [Finset.sum_filter]
                _ = (BR.P ωR * fR ωR)
                      * (A.P ωA * (BL.P ωL * fL ωL)
                        * ((∑ ωC ∈ Finset.univ.filter QC, CC.P ωC * fC ωC)
                          * wval)) := by
                    ring
            · rw [if_neg hQR, zero_mul]
              refine Finset.sum_eq_zero fun ω4 _ => ?_
              rw [if_neg (by
                intro hcon
                exact hQR hcon.2.2.1)]
          calc ∑ ωR : BR.Ω, ∑ ω4 : CC.Ω × (Fin κ → Bool),
              (if QA ωA ∧ QL ωL ∧ QR ωR ∧ QC ω4.1 ∧ ω4.2 = c₀ then
                RP A BL BR CC κ ε (ωA, ωL, ωR, ω4)
                  * (fL ωL * fR ωR * fC ω4.1)
              else 0)
              = ∑ ωR : BR.Ω, (if QR ωR then BR.P ωR * fR ωR else 0)
                * (A.P ωA * (BL.P ωL * fL ωL)
                  * ((∑ ωC ∈ Finset.univ.filter QC, CC.P ωC * fC ωC)
                    * wval)) :=
                Finset.sum_congr rfl fun ωR _ => hR ωR
            _ = (∑ ωR ∈ Finset.univ.filter QR, BR.P ωR * fR ωR)
                  * (A.P ωA * (BL.P ωL * fL ωL)
                    * ((∑ ωC ∈ Finset.univ.filter QC, CC.P ωC * fC ωC)
                      * wval)) := by
                rw [← Finset.sum_mul]
                repeat rw [Finset.sum_filter]
            _ = (BL.P ωL * fL ωL)
                  * (A.P ωA * ((∑ ωR ∈ Finset.univ.filter QR,
                      BR.P ωR * fR ωR)
                    * (∑ ωC ∈ Finset.univ.filter QC, CC.P ωC * fC ωC)
                    * wval)) := by
                ring
        · rw [if_neg hQL, zero_mul]
          refine Finset.sum_eq_zero fun ω3 _ => ?_
          rw [if_neg (by
            intro hcon
            exact hQL hcon.2.1)]
      calc ∑ ωL : BL.Ω, ∑ ω3 : BR.Ω × CC.Ω × (Fin κ → Bool),
          (if QA ωA ∧ QL ωL ∧ QR ω3.1 ∧ QC ω3.2.1 ∧ ω3.2.2 = c₀ then
            RP A BL BR CC κ ε (ωA, ωL, ω3)
              * (fL ωL * fR ω3.1 * fC ω3.2.1)
          else 0)
          = ∑ ωL : BL.Ω, (if QL ωL then BL.P ωL * fL ωL else 0)
            * (A.P ωA * ((∑ ωR ∈ Finset.univ.filter QR, BR.P ωR * fR ωR)
              * (∑ ωC ∈ Finset.univ.filter QC, CC.P ωC * fC ωC) * wval))
          := Finset.sum_congr rfl fun ωL _ => hL ωL
        _ = (∑ ωL ∈ Finset.univ.filter QL, BL.P ωL * fL ωL)
              * (A.P ωA * ((∑ ωR ∈ Finset.univ.filter QR, BR.P ωR * fR ωR)
                * (∑ ωC ∈ Finset.univ.filter QC, CC.P ωC * fC ωC) * wval))
            := by
            rw [← Finset.sum_mul]
            repeat rw [Finset.sum_filter]
        _ = A.P ωA * ((∑ ωL ∈ Finset.univ.filter QL, BL.P ωL * fL ωL)
              * ((∑ ωR ∈ Finset.univ.filter QR, BR.P ωR * fR ωR)
                * (∑ ωC ∈ Finset.univ.filter QC, CC.P ωC * fC ωC))
              * wval) := by
            ring
    · rw [if_neg hQA, zero_mul]
      refine Finset.sum_eq_zero fun ω2 _ => ?_
      rw [if_neg (by
        intro hcon
        exact hQA hcon.1)]
  calc ∑ ωA : A.Ω, ∑ ω2 : BL.Ω × BR.Ω × CC.Ω × (Fin κ → Bool),
      (if QA (ωA, ω2).1 ∧ QL (ωA, ω2).2.1 ∧ QR (ωA, ω2).2.2.1
          ∧ QC (ωA, ω2).2.2.2.1 ∧ (ωA, ω2).2.2.2.2 = c₀ then
        RP A BL BR CC κ ε (ωA, ω2)
          * (fL (ωA, ω2).2.1 * fR (ωA, ω2).2.2.1 * fC (ωA, ω2).2.2.2.1)
      else 0)
      = ∑ ωA : A.Ω, (if QA ωA then A.P ωA else 0)
        * ((∑ ωL ∈ Finset.univ.filter QL, BL.P ωL * fL ωL)
          * ((∑ ωR ∈ Finset.univ.filter QR, BR.P ωR * fR ωR)
            * (∑ ωC ∈ Finset.univ.filter QC, CC.P ωC * fC ωC)) * wval) :=
      Finset.sum_congr rfl fun ωA _ => hA ωA
    _ = (∑ ωA ∈ Finset.univ.filter QA, A.P ωA)
        * ((∑ ωL ∈ Finset.univ.filter QL, BL.P ωL * fL ωL)
          * ((∑ ωR ∈ Finset.univ.filter QR, BR.P ωR * fR ωR)
            * (∑ ωC ∈ Finset.univ.filter QC, CC.P ωC * fC ωC)) * wval) := by
        rw [← Finset.sum_mul]
        repeat rw [Finset.sum_filter]
    _ = _ := by ring

end TailFactor




/-- The running last request is nonempty. -/
theorem lastXset_ne (C : ChunkSystemB X s t 0 cB T pe mL) (ωc : C.Ω)
    (idx : ℕ) : (lastXset C ωc idx).Nonempty := by
  unfold lastXset
  cases hgl : (((List.ofFn (C.chunk ωc)).take idx).flatten).getLast? with
  | none =>
    rw [Option.getD_none]
    exact ⟨s, rfl⟩
  | some S =>
    rw [Option.getD_some]
    refine mem_take_flatten_ne C ωc idx ?_
    exact List.mem_of_getLast? hgl

/-- A serving evader's position lies in the last request. -/
theorem pos_in_getLast {Y' : Type*} [MetricSpace Y'] (E : EvaderAlgorithm Y')
    {l : List (Set Y')} {L₀ : Set Y'}
    (hgl : l.getLast? = some L₀) (hne : L₀.Nonempty) : E.pos l ∈ L₀ := by
  have hPne : l ≠ [] := by
    intro hcon
    rw [hcon] at hgl
    simp at hgl
  have h8 : l.getLast hPne = L₀ := by
    have h9 := List.getLast?_eq_some_getLast (l := l) hPne
    rw [h9] at hgl
    exact Option.some_injective _ hgl
  have hdecomp : l.dropLast ++ [L₀] = l := by
    rw [← h8]
    exact List.dropLast_append_getLast hPne
  rw [← hdecomp]
  exact E.serves _ _ hne

section TailShapes

variable (A BL BR CC : ChunkSystemB X s t 0 cB T pe mL)
variable (GmA GmL GmR GmTL GmTR : Set X → Set Y) (stopPt : Y)
variable (κ : ℕ) (ε : ℝ)

/-- Generic tail-prefix decomposition. -/
theorem rpre_tail_dec (ω : RΩ A BL BR CC κ) {k : ℕ} (hk1 : 1 ≤ k)
    (hkm : A.m + κ + k ≤ mrace A BL BR CC κ) :
    rpre A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω (A.m + κ + k)
      = rpre A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω (A.m + κ + (k - 1))
        ++ rchunk A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω
          (A.m + κ + (k - 1)) := by
  unfold rpre
  have hrm1 : A.m + κ + (k - 1) < mrace A BL BR CC κ := by omega
  have h1 : (List.ofFn (fun i : Fin (mrace A BL BR CC κ) =>
      rchunk A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω (i : ℕ))).take
        (A.m + κ + k)
      = (List.ofFn (fun i : Fin (mrace A BL BR CC κ) =>
        rchunk A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω (i : ℕ))).take
          ((A.m + κ + (k - 1)) + 1) := by
    congr 1
    omega
  rw [h1, take_succ_ofFn _ hrm1, List.flatten_append, List.flatten_cons,
    List.flatten_nil, List.append_nil]

/-- The last request in the survivor-remainder region (left survivor). -/
theorem rpre_getLast_tail_L (hκL : κ ≤ BL.m)
    (hchL : ∀ (ωl : BL.Ω) (i : Fin BL.m), BL.chunk ωl i ≠ [])
    (ω : RΩ A BL BR CC κ) (hs : survL A BL BR CC κ ω = true)
    {k : ℕ} (hk1 : 1 ≤ k) (hkr : k ≤ remCnt A BL BR CC κ ω) :
    (rpre A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω
      (A.m + κ + k)).getLast?
      = some (GmL (lastXset BL ω.2.1 (cntL ω.2.2.2.2 κ + k))) := by
  have hremv : remCnt A BL BR CC κ ω = BL.m - cntL ω.2.2.2.2 κ := by
    unfold remCnt
    rw [if_pos hs]
  have hcm : cntL ω.2.2.2.2 κ ≤ BL.m := le_trans (cntL_le _ le_rfl) hκL
  have hidx : cntL ω.2.2.2.2 κ + (k - 1) < BL.m := by omega
  have hkm : A.m + κ + k ≤ mrace A BL BR CC κ := by
    unfold mrace
    omega
  rw [rpre_tail_dec A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω hk1 hkm,
    rchunk_tail A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω (k - 1),
    if_pos hs, if_pos (by omega : k - 1 < remCnt A BL BR CC κ ω)]
  have hne3 : chunkN BL ω.2.1 (cntL ω.2.2.2.2 κ + (k - 1)) ≠ [] := by
    rw [chunkN_lt BL ω.2.1 hidx]
    exact hchL ω.2.1 _
  have hne2 : reqMap GmL (chunkN BL ω.2.1 (cntL ω.2.2.2.2 κ + (k - 1)))
      ≠ [] := by
    unfold reqMap
    intro hcon
    rw [List.map_eq_nil_iff] at hcon
    exact hne3 hcon
  rw [List.getLast?_append_of_ne_nil _ hne2]
  unfold reqMap
  rw [getLast?_map',
    chunkN_getLast?_lastXset BL ω.2.1 hidx hne3, Option.map_some]
  rw [show cntL ω.2.2.2.2 κ + (k - 1) + 1 = cntL ω.2.2.2.2 κ + k from by
    omega]

/-- The last request in the tail-system region (left survivor). -/
theorem rpre_getLast_tail_CC_L (hκL : κ ≤ BL.m) (hκR : κ ≤ BR.m)
    (hchC : ∀ (ωc : CC.Ω) (i : Fin CC.m), CC.chunk ωc i ≠ [])
    (ω : RΩ A BL BR CC κ) (hs : survL A BL BR CC κ ω = true)
    {k : ℕ} (hk1 : remCnt A BL BR CC κ ω < k)
    (hkc : k ≤ remCnt A BL BR CC κ ω + CC.m) :
    (rpre A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω
      (A.m + κ + k)).getLast?
      = some (GmTL (lastXset CC ω.2.2.2.1 (k - remCnt A BL BR CC κ ω)))
      := by
  have hidx : k - 1 - remCnt A BL BR CC κ ω < CC.m := by omega
  have hkm : A.m + κ + k ≤ mrace A BL BR CC κ := by
    have h1 := remCnt_le_max A BL BR CC κ ω
    unfold mrace
    omega
  rw [rpre_tail_dec A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω
    (by omega) hkm,
    rchunk_tail A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω (k - 1),
    if_pos hs, if_neg (by omega : ¬ (k - 1 < remCnt A BL BR CC κ ω)),
    if_pos hidx]
  have hne3 : chunkN CC ω.2.2.2.1 (k - 1 - remCnt A BL BR CC κ ω)
      ≠ [] := by
    rw [chunkN_lt CC ω.2.2.2.1 hidx]
    exact hchC ω.2.2.2.1 _
  have hne2 : reqMap GmTL (chunkN CC ω.2.2.2.1
      (k - 1 - remCnt A BL BR CC κ ω)) ≠ [] := by
    unfold reqMap
    intro hcon
    rw [List.map_eq_nil_iff] at hcon
    exact hne3 hcon
  rw [List.getLast?_append_of_ne_nil _ hne2]
  unfold reqMap
  rw [getLast?_map',
    chunkN_getLast?_lastXset CC ω.2.2.2.1 hidx hne3, Option.map_some]
  rw [show k - 1 - remCnt A BL BR CC κ ω + 1
    = k - remCnt A BL BR CC κ ω from by omega]

end TailShapes



section TailShapesR

variable (A BL BR CC : ChunkSystemB X s t 0 cB T pe mL)
variable (GmA GmL GmR GmTL GmTR : Set X → Set Y) (stopPt : Y)
variable (κ : ℕ)

/-- The last request in the survivor-remainder region (right survivor). -/
theorem rpre_getLast_tail_R (hκR : κ ≤ BR.m)
    (hchR : ∀ (ωr : BR.Ω) (i : Fin BR.m), BR.chunk ωr i ≠ [])
    (ω : RΩ A BL BR CC κ) (hs : survL A BL BR CC κ ω = false)
    {k : ℕ} (hk1 : 1 ≤ k) (hkr : k ≤ remCnt A BL BR CC κ ω) :
    (rpre A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω
      (A.m + κ + k)).getLast?
      = some (GmR (lastXset BR ω.2.2.1 (cntR ω.2.2.2.2 κ + k))) := by
  have hsn : ¬ (survL A BL BR CC κ ω = true) := by
    rw [hs]
    simp
  have hremv : remCnt A BL BR CC κ ω = BR.m - cntR ω.2.2.2.2 κ := by
    unfold remCnt
    rw [if_neg hsn]
  have hcm : cntR ω.2.2.2.2 κ ≤ BR.m := le_trans (cntR_le _ le_rfl) hκR
  have hidx : cntR ω.2.2.2.2 κ + (k - 1) < BR.m := by omega
  have hkm : A.m + κ + k ≤ mrace A BL BR CC κ := by
    unfold mrace
    omega
  rw [rpre_tail_dec A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω hk1 hkm,
    rchunk_tail A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω (k - 1),
    if_neg hsn, if_pos (by omega : k - 1 < remCnt A BL BR CC κ ω)]
  have hne3 : chunkN BR ω.2.2.1 (cntR ω.2.2.2.2 κ + (k - 1)) ≠ [] := by
    rw [chunkN_lt BR ω.2.2.1 hidx]
    exact hchR ω.2.2.1 _
  have hne2 : reqMap GmR (chunkN BR ω.2.2.1 (cntR ω.2.2.2.2 κ + (k - 1)))
      ≠ [] := by
    unfold reqMap
    intro hcon
    rw [List.map_eq_nil_iff] at hcon
    exact hne3 hcon
  rw [List.getLast?_append_of_ne_nil _ hne2]
  unfold reqMap
  rw [getLast?_map',
    chunkN_getLast?_lastXset BR ω.2.2.1 hidx hne3, Option.map_some]
  rw [show cntR ω.2.2.2.2 κ + (k - 1) + 1 = cntR ω.2.2.2.2 κ + k from by
    omega]

/-- The last request in the tail-system region (right survivor). -/
theorem rpre_getLast_tail_CC_R
    (hchC : ∀ (ωc : CC.Ω) (i : Fin CC.m), CC.chunk ωc i ≠ [])
    (ω : RΩ A BL BR CC κ) (hs : survL A BL BR CC κ ω = false)
    {k : ℕ} (hk1 : remCnt A BL BR CC κ ω < k)
    (hkc : k ≤ remCnt A BL BR CC κ ω + CC.m) :
    (rpre A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω
      (A.m + κ + k)).getLast?
      = some (GmTR (lastXset CC ω.2.2.2.1 (k - remCnt A BL BR CC κ ω)))
      := by
  have hsn : ¬ (survL A BL BR CC κ ω = true) := by
    rw [hs]
    simp
  have hidx : k - 1 - remCnt A BL BR CC κ ω < CC.m := by omega
  have hkm : A.m + κ + k ≤ mrace A BL BR CC κ := by
    have h1 := remCnt_le_max A BL BR CC κ ω
    unfold mrace
    omega
  rw [rpre_tail_dec A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω
    (by omega) hkm,
    rchunk_tail A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω (k - 1),
    if_neg hsn, if_neg (by omega : ¬ (k - 1 < remCnt A BL BR CC κ ω)),
    if_pos hidx]
  have hne3 : chunkN CC ω.2.2.2.1 (k - 1 - remCnt A BL BR CC κ ω)
      ≠ [] := by
    rw [chunkN_lt CC ω.2.2.2.1 hidx]
    exact hchC ω.2.2.2.1 _
  have hne2 : reqMap GmTR (chunkN CC ω.2.2.2.1
      (k - 1 - remCnt A BL BR CC κ ω)) ≠ [] := by
    unfold reqMap
    intro hcon
    rw [List.map_eq_nil_iff] at hcon
    exact hne3 hcon
  rw [List.getLast?_append_of_ne_nil _ hne2]
  unfold reqMap
  rw [getLast?_map',
    chunkN_getLast?_lastXset CC ω.2.2.2.1 hidx hne3, Option.map_some]
  rw [show k - 1 - remCnt A BL BR CC κ ω + 1
    = k - remCnt A BL BR CC κ ω from by omega]

end TailShapesR

section TailMain

variable (A BL BR CC : ChunkSystemB X s t 0 cB T pe mL)
variable (GmA GmL GmR GmTL GmTR : Set X → Set Y) (stopPt : Y)
variable (κ : ℕ) (ε : ℝ)

open Classical in
/-- The survivor-remainder cost bound (left survivor). -/
theorem race_hcost_tail_L (hε : 0 < ε) (hκL : κ ≤ BL.m) (hκR : κ ≤ BR.m)
    (πL : Y → X)
    (hπL : ∀ y z : Y, dist (πL y) (πL z) ≤ dist y z)
    (hGL : ∀ S : Set X, ∀ y ∈ GmL S, πL y ∈ S)
    (hGneL : ∀ S : Set X, S.Nonempty → (GmL S).Nonempty)
    (hchL : ∀ (ωl : BL.Ω) (i : Fin BL.m), BL.chunk ωl i ≠ [])
    {p' : ℝ} (hpe : pe ≤ p')
    (ω₀ : RΩ A BL BR CC κ) (E : EvaderAlgorithm Y)
    (bail : List (Set Y) → Bool)
    {k : ℕ} (hs : survL A BL BR CC κ ω₀ = true)
    (hk1 : 1 ≤ k) (hkr : k < remCnt A BL BR CC κ ω₀) :
    rsize A BL BR CC κ ε ω₀ (A.m + κ + k)
      * (∑ ω ∈ Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
          rhist2 A BL BR CC κ ω (A.m + κ + k)
            = rhist2 A BL BR CC κ ω₀ (A.m + κ + k)),
        RP A BL BR CC κ ε ω)
    ≤ ∑ ω ∈ Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
        rhist2 A BL BR CC κ ω (A.m + κ + k)
          = rhist2 A BL BR CC κ ω₀ (A.m + κ + k)),
      RP A BL BR CC κ ε ω
        * E.bailCost bail
          (rpre A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω (A.m + κ + k))
          (rchunk A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω
            (A.m + κ + k)) p' := by
  set r := A.m + κ + k with hrdef
  set c₀ := ω₀.2.2.2.2 with hc₀
  have hremv : remCnt A BL BR CC κ ω₀ = BL.m - cntL c₀ κ := by
    unfold remCnt
    rw [if_pos hs]
  have hcm : cntL c₀ κ ≤ BL.m := le_trans (cntL_le _ le_rfl) hκL
  have hcmR : cntR c₀ κ ≤ BR.m := le_trans (cntR_le _ le_rfl) hκR
  set n := cntL c₀ κ + k with hndef
  have hn : n < BL.m := by omega
  have hkm : r - A.m - κ = k := by omega
  -- the revealed counts at the base outcome
  have hrevLv : revL2 A BL BR CC κ ω₀ k = n := by
    unfold revL2
    rw [← hc₀, ← hndef]
    omega
  have hrevRv : revR2 A BL BR CC κ ω₀ k = min (cntR c₀ κ + k) BR.m := by
    unfold revR2
    rw [← hc₀]
  set nR2 := min (cntR c₀ κ + k) BR.m with hnR2
  set nC2 := revC A BL BR CC κ ω₀ k with hnC2
  set hPad := rpre A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω₀ r
    with hPdef
  set hOrig := ((List.ofFn (BL.chunk ω₀.2.1)).take n).flatten with hOdef
  -- atom conditions
  set QA : A.Ω → Prop := fun ωA => A.hist A.m ωA = A.hist A.m ω₀.1
    with hQA
  set QL : BL.Ω → Prop :=
    fun ωL => BL.hist n ωL = BL.hist n ω₀.2.1 with hQL
  set QR : BR.Ω → Prop :=
    fun ωR => BR.hist nR2 ωR = BR.hist nR2 ω₀.2.2.1 with hQR
  set QC : CC.Ω → Prop :=
    fun ωC => CC.hist nC2 ωC = CC.hist nC2 ω₀.2.2.2.1 with hQC
  have hiff : ∀ ω : RΩ A BL BR CC κ,
      (rhist2 A BL BR CC κ ω r = rhist2 A BL BR CC κ ω₀ r)
      ↔ (QA ω.1 ∧ QL ω.2.1 ∧ QR ω.2.2.1 ∧ QC ω.2.2.2.1
        ∧ ω.2.2.2.2 = c₀) := by
    intro ω
    rw [rhist2_eq_iff_tail A BL BR CC κ hκL hκR (by omega), hkm,
      hrevLv, hrevRv]
    constructor
    · rintro ⟨h1, h2, h3, h4, h5⟩
      rw [← hnC2] at h5
      exact ⟨h1, h3, h4, h5, h2⟩
    · rintro ⟨h1, h2, h3, h4, h5⟩
      rw [← hnC2]
      exact ⟨h1, h5, h2, h3, h4⟩
  have hfil : (Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
      rhist2 A BL BR CC κ ω r = rhist2 A BL BR CC κ ω₀ r))
      = Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
        QA ω.1 ∧ QL ω.2.1 ∧ QR ω.2.2.1 ∧ QC ω.2.2.2.1
          ∧ ω.2.2.2.2 = c₀) := by
    refine Finset.filter_congr fun ω _ => ?_
    exact hiff ω
  -- the fixed coin weight
  set wF := coinWt (coinW A BL BR ω₀.1 ω₀.2.1 ω₀.2.2.1 (ε := ε)) c₀
    with hwF
  have hwFpos : 0 < wF := by
    rw [hwF]
    refine coinWt_pos (fun q p b => ?_) _
    rw [coinW_eval]
    by_cases hb : b
    · rw [if_pos hb]
      exact probL_pos hε
    · rw [if_neg hb]
      exact probL_pos hε
  have hres : restrict c₀ κ (le_refl κ) = c₀ := by
    funext i
    exact congrArg c₀ (Fin.ext rfl)
  have hW : ∀ (ωA : A.Ω) (ωL : BL.Ω) (ωR : BR.Ω), QL ωL → QR ωR →
      coinWt (coinW A BL BR ωA ωL ωR (ε := ε)) c₀ = wF := by
    intro ωA ωL ωR hqL hqR
    rw [hwF, ← hres]
    refine coinWt_restrict_congr A BL BR κ ε (le_refl κ) c₀ ωA ω₀.1
      ωL ω₀.2.1 ωR ω₀.2.2.1 ?_ ?_
    · exact BL.href _ n (by omega) _ _ hqL
    · refine BR.href _ nR2 ?_ _ _ hqR
      rw [hnR2]
      omega
  -- masses
  set mA := ∑ ωA ∈ Finset.univ.filter QA, A.P ωA with hmA
  set mLmass := ∑ ωL ∈ Finset.univ.filter QL, BL.P ωL with hmL
  set mRmass := ∑ ωR ∈ Finset.univ.filter QR, BR.P ωR with hmR
  set mCmass := ∑ ωC ∈ Finset.univ.filter QC, CC.P ωC with hmC
  have hmA0 : 0 ≤ mA :=
    Finset.sum_nonneg fun ωA _ => le_of_lt (A.hP ωA)
  have hmL0 : 0 ≤ mLmass :=
    Finset.sum_nonneg fun ωL _ => le_of_lt (BL.hP ωL)
  have hmR0 : 0 ≤ mRmass :=
    Finset.sum_nonneg fun ωR _ => le_of_lt (BR.hP ωR)
  have hmC0 : 0 ≤ mCmass :=
    Finset.sum_nonneg fun ωC _ => le_of_lt (CC.hP ωC)
  have hmR1 : (∑ ωR ∈ Finset.univ.filter QR, BR.P ωR * (1:ℝ)) = mRmass := by
    rw [hmR]
    exact Finset.sum_congr rfl fun _ _ => mul_one _
  have hmC1 : (∑ ωC ∈ Finset.univ.filter QC, CC.P ωC * (1:ℝ)) = mCmass := by
    rw [hmC]
    exact Finset.sum_congr rfl fun _ _ => mul_one _
  have hmass : (∑ ω ∈ Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
      rhist2 A BL BR CC κ ω r = rhist2 A BL BR CC κ ω₀ r),
      RP A BL BR CC κ ε ω)
      = wF * (mA * (mLmass * (mRmass * mCmass))) := by
    rw [hfil]
    have h1 := sum_RP_factor_tail A BL BR CC κ ε hε QA QL QR QC c₀
      (fun _ => 1) (fun _ => 1) (fun _ => 1) wF hW
    have h2 : ∀ ω ∈ Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
        QA ω.1 ∧ QL ω.2.1 ∧ QR ω.2.2.1 ∧ QC ω.2.2.2.1
          ∧ ω.2.2.2.2 = c₀),
        RP A BL BR CC κ ε ω
        = RP A BL BR CC κ ε ω * ((1:ℝ) * 1 * 1) := by
      intro ω _
      ring
    rw [Finset.sum_congr rfl h2, h1]
    have h3 : ∑ ωL ∈ Finset.univ.filter QL, BL.P ωL * (1:ℝ) = mLmass := by
      rw [hmL]
      exact Finset.sum_congr rfl fun _ _ => mul_one _
    rw [h3, hmR1, hmC1]
  -- start alignment
  set SH := shadowFrom hOrig.length πL GmL hGL hGneL E hPad with hSHdef
  have hstart : SH.pos hOrig = πL (E.pos hPad) := by
    rw [hSHdef]
    refine shadowFrom_pos_boundary hOrig.length πL GmL hGL hGneL E hPad
      rfl ?_
    intro Sl hgl
    have hlxv : lastXset BL ω₀.2.1 n = Sl := by
      unfold lastXset
      rw [hgl, Option.getD_some]
    have hshape := rpre_getLast_tail_L A BL BR CC GmA GmL GmR GmTL GmTR
      stopPt κ hκL hchL ω₀ hs hk1 (le_of_lt hkr)
    have hidx2 : cntL ω₀.2.2.2.2 κ + k = n := by
      rw [hndef, hc₀]
    rw [hidx2] at hshape
    have hz := pos_in_getLast E hshape
      (hGneL _ (lastXset_ne BL ω₀.2.1 n))
    have hz2 := hGL _ _ hz
    rw [hlxv] at hz2
    exact hz2
  -- the side cost bound
  have hside := BL.hcost ⟨n, hn⟩ ω₀.2.1 SH
    (fun l => bail (hPad ++ reqMap GmL (l.drop hOrig.length)))
  have hsize0 : BL.size ω₀.2.1 ⟨n, hn⟩ = BL.sizeN n ω₀.2.1 := by
    unfold ChunkSystemB.sizeN
    rw [dif_pos hn]
  -- per-outcome domination
  have hdom : ∀ ωL ∈ Finset.univ.filter QL,
      BL.P ωL * SH.bailCost
          (fun l => bail (hPad ++ reqMap GmL (l.drop hOrig.length)))
          (((List.ofFn (BL.chunk ωL)).take n).flatten)
          (BL.chunk ωL ⟨n, hn⟩) pe
      ≤ BL.P ωL * E.bailCost bail hPad
          (reqMap GmL (BL.chunk ωL ⟨n, hn⟩)) p' := by
    intro ωL hωL
    rw [Finset.mem_filter] at hωL
    have hpre : ((List.ofFn (BL.chunk ωL)).take n).flatten = hOrig := by
      rw [hOdef]
      congr 1
      exact take_congr BL (le_refl _) hωL.2
    rw [hpre]
    refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (BL.hP ωL))
    rw [hSHdef]
    exact shadowFrom_bailCost_le hOrig.length πL GmL hπL hGL hGneL E bail
      hPad hOrig (BL.chunk ωL ⟨n, hn⟩) hpe rfl hstart
  -- identify the goal integrand
  have hident : ∀ ω ∈ Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
      QA ω.1 ∧ QL ω.2.1 ∧ QR ω.2.2.1 ∧ QC ω.2.2.2.1 ∧ ω.2.2.2.2 = c₀),
      RP A BL BR CC κ ε ω
        * E.bailCost bail
          (rpre A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω r)
          (rchunk A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω r) p'
      = RP A BL BR CC κ ε ω
        * ((fun ωL => E.bailCost bail hPad
            (reqMap GmL (BL.chunk ωL ⟨n, hn⟩)) p') ω.2.1
          * (fun _ : BR.Ω => (1:ℝ)) ω.2.2.1
          * (fun _ : CC.Ω => (1:ℝ)) ω.2.2.2.1) := by
    intro ω hω
    rw [Finset.mem_filter] at hω
    obtain ⟨-, hqA, hqL, hqR, hqC, hqc⟩ := hω
    have hatom : rhist2 A BL BR CC κ ω r = rhist2 A BL BR CC κ ω₀ r :=
      (hiff ω).mpr ⟨hqA, hqL, hqR, hqC, hqc⟩
    have hpre : rpre A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω r
        = hPad := by
      rw [hPdef]
      exact rpre_congr A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ hκL hκR
        hatom
    have hsurv : survL A BL BR CC κ ω = survL A BL BR CC κ ω₀ := by
      refine survL_congr A BL BR CC κ (by rw [hqc])
        (NL := n) (NR := nR2) ?_ ?_ ?_ ?_
      · rw [hqc]
        omega
      · rw [hqc, hnR2]
        omega
      · exact hqL
      · exact hqR
    have hrem : remCnt A BL BR CC κ ω = remCnt A BL BR CC κ ω₀ := by
      refine remCnt_congr A BL BR CC κ (by rw [hqc])
        (NL := n) (NR := nR2) ?_ ?_ ?_ ?_
      · rw [hqc]
        omega
      · rw [hqc, hnR2]
        omega
      · exact hqL
      · exact hqR
    have hch : rchunk A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω r
        = reqMap GmL (BL.chunk ω.2.1 ⟨n, hn⟩) := by
      rw [hrdef, rchunk_tail A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω k,
        if_pos (by rw [hsurv]; exact hs), if_pos (by rw [hrem]; exact hkr)]
      rw [hqc]
      rw [show cntL c₀ κ + k = n from by rw [hndef]]
      rw [chunkN_lt BL ω.2.1 hn]
    rw [hpre, hch]
    ring
  -- the factored cost sum
  have hpart : (∑ ω ∈ Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
      rhist2 A BL BR CC κ ω r = rhist2 A BL BR CC κ ω₀ r),
      RP A BL BR CC κ ε ω
        * E.bailCost bail
          (rpre A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω r)
          (rchunk A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω r) p')
      = wF * (mA * ((∑ ωL ∈ Finset.univ.filter QL,
          BL.P ωL * E.bailCost bail hPad
            (reqMap GmL (BL.chunk ωL ⟨n, hn⟩)) p')
        * (mRmass * mCmass))) := by
    rw [hfil, Finset.sum_congr rfl hident,
      sum_RP_factor_tail A BL BR CC κ ε hε QA QL QR QC c₀
        (fun ωL => E.bailCost bail hPad
          (reqMap GmL (BL.chunk ωL ⟨n, hn⟩)) p')
        (fun _ => 1) (fun _ => 1) wF hW, hmR1, hmC1]
  -- the side premise
  have hbailsum : BL.sizeN n ω₀.2.1 * mLmass
      ≤ ∑ ωL ∈ Finset.univ.filter QL,
        BL.P ωL * E.bailCost bail hPad
          (reqMap GmL (BL.chunk ωL ⟨n, hn⟩)) p' := by
    have h1 : BL.sizeN n ω₀.2.1 * mLmass
        ≤ ∑ ωL ∈ Finset.univ.filter QL,
          BL.P ωL * SH.bailCost
            (fun l => bail (hPad ++ reqMap GmL (l.drop hOrig.length)))
            (((List.ofFn (BL.chunk ωL)).take n).flatten)
            (BL.chunk ωL ⟨n, hn⟩) pe := by
      rw [← hsize0]
      exact hside
    exact le_trans h1 (Finset.sum_le_sum hdom)
  -- rsize identification
  have hrsize : rsize A BL BR CC κ ε ω₀ r = BL.sizeN n ω₀.2.1 := by
    rw [hrdef, rsize_tail A BL BR CC κ ε ω₀ k,
      if_neg (by omega),
      if_pos hkr, if_pos hs]
  -- assemble
  rw [hrsize, hmass, hpart]
  calc BL.sizeN n ω₀.2.1 * (wF * (mA * (mLmass * (mRmass * mCmass))))
      = wF * (mA * ((BL.sizeN n ω₀.2.1 * mLmass) * (mRmass * mCmass)))
        := by ring
    _ ≤ wF * (mA * ((∑ ωL ∈ Finset.univ.filter QL,
          BL.P ωL * E.bailCost bail hPad
            (reqMap GmL (BL.chunk ωL ⟨n, hn⟩)) p')
        * (mRmass * mCmass))) := by
        refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hwFpos)
        refine mul_le_mul_of_nonneg_left ?_ hmA0
        exact mul_le_mul_of_nonneg_right hbailsum
          (mul_nonneg hmR0 hmC0)


open Classical in
/-- The survivor-remainder cost bound (right survivor). -/
theorem race_hcost_tail_R (hε : 0 < ε) (hκL : κ ≤ BL.m) (hκR : κ ≤ BR.m)
    (πR : Y → X)
    (hπR : ∀ y z : Y, dist (πR y) (πR z) ≤ dist y z)
    (hGR : ∀ S : Set X, ∀ y ∈ GmR S, πR y ∈ S)
    (hGneR : ∀ S : Set X, S.Nonempty → (GmR S).Nonempty)
    (hchR : ∀ (ωr : BR.Ω) (i : Fin BR.m), BR.chunk ωr i ≠ [])
    {p' : ℝ} (hpe : pe ≤ p')
    (ω₀ : RΩ A BL BR CC κ) (E : EvaderAlgorithm Y)
    (bail : List (Set Y) → Bool)
    {k : ℕ} (hs : survL A BL BR CC κ ω₀ = false)
    (hk1 : 1 ≤ k) (hkr : k < remCnt A BL BR CC κ ω₀) :
    rsize A BL BR CC κ ε ω₀ (A.m + κ + k)
      * (∑ ω ∈ Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
          rhist2 A BL BR CC κ ω (A.m + κ + k)
            = rhist2 A BL BR CC κ ω₀ (A.m + κ + k)),
        RP A BL BR CC κ ε ω)
    ≤ ∑ ω ∈ Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
        rhist2 A BL BR CC κ ω (A.m + κ + k)
          = rhist2 A BL BR CC κ ω₀ (A.m + κ + k)),
      RP A BL BR CC κ ε ω
        * E.bailCost bail
          (rpre A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω (A.m + κ + k))
          (rchunk A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω
            (A.m + κ + k)) p' := by
  set r := A.m + κ + k with hrdef
  set c₀ := ω₀.2.2.2.2 with hc₀
  have hsn : ¬ (survL A BL BR CC κ ω₀ = true) := by
    rw [hs]
    simp
  have hremv : remCnt A BL BR CC κ ω₀ = BR.m - cntR c₀ κ := by
    unfold remCnt
    rw [if_neg hsn]
  have hcm : cntR c₀ κ ≤ BR.m := le_trans (cntR_le _ le_rfl) hκR
  have hcmL : cntL c₀ κ ≤ BL.m := le_trans (cntL_le _ le_rfl) hκL
  set n := cntR c₀ κ + k with hndef
  have hn : n < BR.m := by omega
  have hkm : r - A.m - κ = k := by omega
  -- the revealed counts at the base outcome
  have hrevRv : revR2 A BL BR CC κ ω₀ k = n := by
    unfold revR2
    rw [← hc₀, ← hndef]
    omega
  have hrevLv : revL2 A BL BR CC κ ω₀ k = min (cntL c₀ κ + k) BL.m := by
    unfold revL2
    rw [← hc₀]
  set nL2 := min (cntL c₀ κ + k) BL.m with hnL2
  set nC2 := revC A BL BR CC κ ω₀ k with hnC2
  set hPad := rpre A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω₀ r
    with hPdef
  set hOrig := ((List.ofFn (BR.chunk ω₀.2.2.1)).take n).flatten with hOdef
  -- atom conditions
  set QA : A.Ω → Prop := fun ωA => A.hist A.m ωA = A.hist A.m ω₀.1
    with hQA
  set QL : BL.Ω → Prop :=
    fun ωL => BL.hist nL2 ωL = BL.hist nL2 ω₀.2.1 with hQL
  set QR : BR.Ω → Prop :=
    fun ωR => BR.hist n ωR = BR.hist n ω₀.2.2.1 with hQR
  set QC : CC.Ω → Prop :=
    fun ωC => CC.hist nC2 ωC = CC.hist nC2 ω₀.2.2.2.1 with hQC
  have hiff : ∀ ω : RΩ A BL BR CC κ,
      (rhist2 A BL BR CC κ ω r = rhist2 A BL BR CC κ ω₀ r)
      ↔ (QA ω.1 ∧ QL ω.2.1 ∧ QR ω.2.2.1 ∧ QC ω.2.2.2.1
        ∧ ω.2.2.2.2 = c₀) := by
    intro ω
    rw [rhist2_eq_iff_tail A BL BR CC κ hκL hκR (by omega), hkm,
      hrevLv, hrevRv]
    constructor
    · rintro ⟨h1, h2, h3, h4, h5⟩
      rw [← hnC2] at h5
      exact ⟨h1, h3, h4, h5, h2⟩
    · rintro ⟨h1, h2, h3, h4, h5⟩
      rw [← hnC2]
      exact ⟨h1, h5, h2, h3, h4⟩
  have hfil : (Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
      rhist2 A BL BR CC κ ω r = rhist2 A BL BR CC κ ω₀ r))
      = Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
        QA ω.1 ∧ QL ω.2.1 ∧ QR ω.2.2.1 ∧ QC ω.2.2.2.1
          ∧ ω.2.2.2.2 = c₀) := by
    refine Finset.filter_congr fun ω _ => ?_
    exact hiff ω
  -- the fixed coin weight
  set wF := coinWt (coinW A BL BR ω₀.1 ω₀.2.1 ω₀.2.2.1 (ε := ε)) c₀
    with hwF
  have hwFpos : 0 < wF := by
    rw [hwF]
    refine coinWt_pos (fun q p b => ?_) _
    rw [coinW_eval]
    by_cases hb : b
    · rw [if_pos hb]
      exact probL_pos hε
    · rw [if_neg hb]
      exact probL_pos hε
  have hres : restrict c₀ κ (le_refl κ) = c₀ := by
    funext i
    exact congrArg c₀ (Fin.ext rfl)
  have hW : ∀ (ωA : A.Ω) (ωL : BL.Ω) (ωR : BR.Ω), QL ωL → QR ωR →
      coinWt (coinW A BL BR ωA ωL ωR (ε := ε)) c₀ = wF := by
    intro ωA ωL ωR hqL hqR
    rw [hwF, ← hres]
    refine coinWt_restrict_congr A BL BR κ ε (le_refl κ) c₀ ωA ω₀.1
      ωL ω₀.2.1 ωR ω₀.2.2.1 ?_ ?_
    · refine BL.href _ nL2 ?_ _ _ hqL
      rw [hnL2]
      omega
    · exact BR.href _ n (by omega) _ _ hqR
  -- masses
  set mA := ∑ ωA ∈ Finset.univ.filter QA, A.P ωA with hmA
  set mLmass := ∑ ωL ∈ Finset.univ.filter QL, BL.P ωL with hmL
  set mRmass := ∑ ωR ∈ Finset.univ.filter QR, BR.P ωR with hmR
  set mCmass := ∑ ωC ∈ Finset.univ.filter QC, CC.P ωC with hmC
  have hmA0 : 0 ≤ mA :=
    Finset.sum_nonneg fun ωA _ => le_of_lt (A.hP ωA)
  have hmL0 : 0 ≤ mLmass :=
    Finset.sum_nonneg fun ωL _ => le_of_lt (BL.hP ωL)
  have hmR0 : 0 ≤ mRmass :=
    Finset.sum_nonneg fun ωR _ => le_of_lt (BR.hP ωR)
  have hmC0 : 0 ≤ mCmass :=
    Finset.sum_nonneg fun ωC _ => le_of_lt (CC.hP ωC)
  have hmL1 : (∑ ωL ∈ Finset.univ.filter QL, BL.P ωL * (1:ℝ)) = mLmass := by
    rw [hmL]
    exact Finset.sum_congr rfl fun _ _ => mul_one _
  have hmC1 : (∑ ωC ∈ Finset.univ.filter QC, CC.P ωC * (1:ℝ)) = mCmass := by
    rw [hmC]
    exact Finset.sum_congr rfl fun _ _ => mul_one _
  have hmass : (∑ ω ∈ Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
      rhist2 A BL BR CC κ ω r = rhist2 A BL BR CC κ ω₀ r),
      RP A BL BR CC κ ε ω)
      = wF * (mA * (mLmass * (mRmass * mCmass))) := by
    rw [hfil]
    have h1 := sum_RP_factor_tail A BL BR CC κ ε hε QA QL QR QC c₀
      (fun _ => 1) (fun _ => 1) (fun _ => 1) wF hW
    have h2 : ∀ ω ∈ Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
        QA ω.1 ∧ QL ω.2.1 ∧ QR ω.2.2.1 ∧ QC ω.2.2.2.1
          ∧ ω.2.2.2.2 = c₀),
        RP A BL BR CC κ ε ω
        = RP A BL BR CC κ ε ω * ((1:ℝ) * 1 * 1) := by
      intro ω _
      ring
    rw [Finset.sum_congr rfl h2, h1]
    have h3 : ∑ ωR ∈ Finset.univ.filter QR, BR.P ωR * (1:ℝ) = mRmass := by
      rw [hmR]
      exact Finset.sum_congr rfl fun _ _ => mul_one _
    rw [hmL1, h3, hmC1]
  -- start alignment
  set SH := shadowFrom hOrig.length πR GmR hGR hGneR E hPad with hSHdef
  have hstart : SH.pos hOrig = πR (E.pos hPad) := by
    rw [hSHdef]
    refine shadowFrom_pos_boundary hOrig.length πR GmR hGR hGneR E hPad
      rfl ?_
    intro Sl hgl
    have hlxv : lastXset BR ω₀.2.2.1 n = Sl := by
      unfold lastXset
      rw [hgl, Option.getD_some]
    have hshape := rpre_getLast_tail_R A BL BR CC GmA GmL GmR GmTL GmTR
      stopPt κ hκR hchR ω₀ hs hk1 (le_of_lt hkr)
    have hidx2 : cntR ω₀.2.2.2.2 κ + k = n := by
      rw [hndef, hc₀]
    rw [hidx2] at hshape
    have hz := pos_in_getLast E hshape
      (hGneR _ (lastXset_ne BR ω₀.2.2.1 n))
    have hz2 := hGR _ _ hz
    rw [hlxv] at hz2
    exact hz2
  -- the side cost bound
  have hside := BR.hcost ⟨n, hn⟩ ω₀.2.2.1 SH
    (fun l => bail (hPad ++ reqMap GmR (l.drop hOrig.length)))
  have hsize0 : BR.size ω₀.2.2.1 ⟨n, hn⟩ = BR.sizeN n ω₀.2.2.1 := by
    unfold ChunkSystemB.sizeN
    rw [dif_pos hn]
  -- per-outcome domination
  have hdom : ∀ ωR ∈ Finset.univ.filter QR,
      BR.P ωR * SH.bailCost
          (fun l => bail (hPad ++ reqMap GmR (l.drop hOrig.length)))
          (((List.ofFn (BR.chunk ωR)).take n).flatten)
          (BR.chunk ωR ⟨n, hn⟩) pe
      ≤ BR.P ωR * E.bailCost bail hPad
          (reqMap GmR (BR.chunk ωR ⟨n, hn⟩)) p' := by
    intro ωR hωR
    rw [Finset.mem_filter] at hωR
    have hpre : ((List.ofFn (BR.chunk ωR)).take n).flatten = hOrig := by
      rw [hOdef]
      congr 1
      exact take_congr BR (le_refl _) hωR.2
    rw [hpre]
    refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (BR.hP ωR))
    rw [hSHdef]
    exact shadowFrom_bailCost_le hOrig.length πR GmR hπR hGR hGneR E bail
      hPad hOrig (BR.chunk ωR ⟨n, hn⟩) hpe rfl hstart
  -- identify the goal integrand
  have hident : ∀ ω ∈ Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
      QA ω.1 ∧ QL ω.2.1 ∧ QR ω.2.2.1 ∧ QC ω.2.2.2.1 ∧ ω.2.2.2.2 = c₀),
      RP A BL BR CC κ ε ω
        * E.bailCost bail
          (rpre A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω r)
          (rchunk A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω r) p'
      = RP A BL BR CC κ ε ω
        * ((fun _ : BL.Ω => (1:ℝ)) ω.2.1
          * (fun ωR => E.bailCost bail hPad
            (reqMap GmR (BR.chunk ωR ⟨n, hn⟩)) p') ω.2.2.1
          * (fun _ : CC.Ω => (1:ℝ)) ω.2.2.2.1) := by
    intro ω hω
    rw [Finset.mem_filter] at hω
    obtain ⟨-, hqA, hqL, hqR, hqC, hqc⟩ := hω
    have hatom : rhist2 A BL BR CC κ ω r = rhist2 A BL BR CC κ ω₀ r :=
      (hiff ω).mpr ⟨hqA, hqL, hqR, hqC, hqc⟩
    have hpre : rpre A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω r
        = hPad := by
      rw [hPdef]
      exact rpre_congr A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ hκL hκR
        hatom
    have hsurv : survL A BL BR CC κ ω = survL A BL BR CC κ ω₀ := by
      refine survL_congr A BL BR CC κ (by rw [hqc])
        (NL := nL2) (NR := n) ?_ ?_ ?_ ?_
      · rw [hqc, hnL2]
        omega
      · rw [hqc]
        omega
      · exact hqL
      · exact hqR
    have hrem : remCnt A BL BR CC κ ω = remCnt A BL BR CC κ ω₀ := by
      refine remCnt_congr A BL BR CC κ (by rw [hqc])
        (NL := nL2) (NR := n) ?_ ?_ ?_ ?_
      · rw [hqc, hnL2]
        omega
      · rw [hqc]
        omega
      · exact hqL
      · exact hqR
    have hch : rchunk A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω r
        = reqMap GmR (BR.chunk ω.2.2.1 ⟨n, hn⟩) := by
      rw [hrdef, rchunk_tail A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω k,
        if_neg (by rw [hsurv, hs]; simp),
        if_pos (by rw [hrem]; exact hkr)]
      rw [hqc]
      rw [show cntR c₀ κ + k = n from by rw [hndef]]
      rw [chunkN_lt BR ω.2.2.1 hn]
    rw [hpre, hch]
    ring
  -- the factored cost sum
  have hpart : (∑ ω ∈ Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
      rhist2 A BL BR CC κ ω r = rhist2 A BL BR CC κ ω₀ r),
      RP A BL BR CC κ ε ω
        * E.bailCost bail
          (rpre A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω r)
          (rchunk A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω r) p')
      = wF * (mA * (mLmass * ((∑ ωR ∈ Finset.univ.filter QR,
          BR.P ωR * E.bailCost bail hPad
            (reqMap GmR (BR.chunk ωR ⟨n, hn⟩)) p')
        * mCmass))) := by
    rw [hfil, Finset.sum_congr rfl hident,
      sum_RP_factor_tail A BL BR CC κ ε hε QA QL QR QC c₀
        (fun _ => 1)
        (fun ωR => E.bailCost bail hPad
          (reqMap GmR (BR.chunk ωR ⟨n, hn⟩)) p')
        (fun _ => 1) wF hW, hmL1, hmC1]
  -- the side premise
  have hbailsum : BR.sizeN n ω₀.2.2.1 * mRmass
      ≤ ∑ ωR ∈ Finset.univ.filter QR,
        BR.P ωR * E.bailCost bail hPad
          (reqMap GmR (BR.chunk ωR ⟨n, hn⟩)) p' := by
    have h1 : BR.sizeN n ω₀.2.2.1 * mRmass
        ≤ ∑ ωR ∈ Finset.univ.filter QR,
          BR.P ωR * SH.bailCost
            (fun l => bail (hPad ++ reqMap GmR (l.drop hOrig.length)))
            (((List.ofFn (BR.chunk ωR)).take n).flatten)
            (BR.chunk ωR ⟨n, hn⟩) pe := by
      rw [← hsize0]
      exact hside
    exact le_trans h1 (Finset.sum_le_sum hdom)
  -- rsize identification
  have hrsize : rsize A BL BR CC κ ε ω₀ r = BR.sizeN n ω₀.2.2.1 := by
    rw [hrdef, rsize_tail A BL BR CC κ ε ω₀ k,
      if_neg (by omega),
      if_pos hkr, if_neg hsn]
  -- assemble
  rw [hrsize, hmass, hpart]
  calc BR.sizeN n ω₀.2.2.1 * (wF * (mA * (mLmass * (mRmass * mCmass))))
      = wF * (mA * (mLmass * ((BR.sizeN n ω₀.2.2.1 * mRmass) * mCmass)))
        := by ring
    _ ≤ wF * (mA * (mLmass * ((∑ ωR ∈ Finset.univ.filter QR,
          BR.P ωR * E.bailCost bail hPad
            (reqMap GmR (BR.chunk ωR ⟨n, hn⟩)) p')
        * mCmass))) := by
        refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hwFpos)
        refine mul_le_mul_of_nonneg_left ?_ hmA0
        refine mul_le_mul_of_nonneg_left ?_ hmL0
        exact mul_le_mul_of_nonneg_right hbailsum hmC0




open Classical in
/-- The tail-system cost bound (left survivor). -/
theorem race_hcost_CC_L (hε : 0 < ε) (hκL : κ ≤ BL.m) (hκR : κ ≤ BR.m)
    (πT : Y → X)
    (hπT : ∀ y z : Y, dist (πT y) (πT z) ≤ dist y z)
    (hGT : ∀ S : Set X, ∀ y ∈ GmTL S, πT y ∈ S)
    (hGneT : ∀ S : Set X, S.Nonempty → (GmTL S).Nonempty)
    (hchC : ∀ (ωc : CC.Ω) (i : Fin CC.m), CC.chunk ωc i ≠ [])
    {p' : ℝ} (hpe : pe ≤ p')
    (ω₀ : RΩ A BL BR CC κ) (E : EvaderAlgorithm Y)
    (bail : List (Set Y) → Bool)
    {k : ℕ} (hs : survL A BL BR CC κ ω₀ = true)
    (hk1 : remCnt A BL BR CC κ ω₀ < k)
    (hkc : k - remCnt A BL BR CC κ ω₀ < CC.m) :
    rsize A BL BR CC κ ε ω₀ (A.m + κ + k)
      * (∑ ω ∈ Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
          rhist2 A BL BR CC κ ω (A.m + κ + k)
            = rhist2 A BL BR CC κ ω₀ (A.m + κ + k)),
        RP A BL BR CC κ ε ω)
    ≤ ∑ ω ∈ Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
        rhist2 A BL BR CC κ ω (A.m + κ + k)
          = rhist2 A BL BR CC κ ω₀ (A.m + κ + k)),
      RP A BL BR CC κ ε ω
        * E.bailCost bail
          (rpre A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω (A.m + κ + k))
          (rchunk A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω
            (A.m + κ + k)) p' := by
  set r := A.m + κ + k with hrdef
  set c₀ := ω₀.2.2.2.2 with hc₀
  have hcm : cntL c₀ κ ≤ BL.m := le_trans (cntL_le _ le_rfl) hκL
  have hcmR : cntR c₀ κ ≤ BR.m := le_trans (cntR_le _ le_rfl) hκR
  set n := k - remCnt A BL BR CC κ ω₀ with hndef
  have hn : n < CC.m := by omega
  have hkm : r - A.m - κ = k := by omega
  have hk1' : 1 ≤ k := by omega
  -- the revealed counts at the base outcome
  have hrevLv : revL2 A BL BR CC κ ω₀ k = min (cntL c₀ κ + k) BL.m := by
    unfold revL2
    rw [← hc₀]
  have hrevRv : revR2 A BL BR CC κ ω₀ k = min (cntR c₀ κ + k) BR.m := by
    unfold revR2
    rw [← hc₀]
  set nL2 := min (cntL c₀ κ + k) BL.m with hnL2
  set nR2 := min (cntR c₀ κ + k) BR.m with hnR2
  have hrevCv : revC A BL BR CC κ ω₀ k = n := by
    unfold revC
    rw [← hndef]
    omega
  set hPad := rpre A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω₀ r
    with hPdef
  set hOrig := ((List.ofFn (CC.chunk ω₀.2.2.2.1)).take n).flatten
    with hOdef
  -- atom conditions
  set QA : A.Ω → Prop := fun ωA => A.hist A.m ωA = A.hist A.m ω₀.1
    with hQA
  set QL : BL.Ω → Prop :=
    fun ωL => BL.hist nL2 ωL = BL.hist nL2 ω₀.2.1 with hQL
  set QR : BR.Ω → Prop :=
    fun ωR => BR.hist nR2 ωR = BR.hist nR2 ω₀.2.2.1 with hQR
  set QC : CC.Ω → Prop :=
    fun ωC => CC.hist n ωC = CC.hist n ω₀.2.2.2.1 with hQC
  have hiff : ∀ ω : RΩ A BL BR CC κ,
      (rhist2 A BL BR CC κ ω r = rhist2 A BL BR CC κ ω₀ r)
      ↔ (QA ω.1 ∧ QL ω.2.1 ∧ QR ω.2.2.1 ∧ QC ω.2.2.2.1
        ∧ ω.2.2.2.2 = c₀) := by
    intro ω
    rw [rhist2_eq_iff_tail A BL BR CC κ hκL hκR (by omega), hkm,
      hrevLv, hrevRv, hrevCv]
    constructor
    · rintro ⟨h1, h2, h3, h4, h5⟩
      exact ⟨h1, h3, h4, h5, h2⟩
    · rintro ⟨h1, h2, h3, h4, h5⟩
      exact ⟨h1, h5, h2, h3, h4⟩
  have hfil : (Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
      rhist2 A BL BR CC κ ω r = rhist2 A BL BR CC κ ω₀ r))
      = Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
        QA ω.1 ∧ QL ω.2.1 ∧ QR ω.2.2.1 ∧ QC ω.2.2.2.1
          ∧ ω.2.2.2.2 = c₀) := by
    refine Finset.filter_congr fun ω _ => ?_
    exact hiff ω
  -- the fixed coin weight
  set wF := coinWt (coinW A BL BR ω₀.1 ω₀.2.1 ω₀.2.2.1 (ε := ε)) c₀
    with hwF
  have hwFpos : 0 < wF := by
    rw [hwF]
    refine coinWt_pos (fun q p b => ?_) _
    rw [coinW_eval]
    by_cases hb : b
    · rw [if_pos hb]
      exact probL_pos hε
    · rw [if_neg hb]
      exact probL_pos hε
  have hres : restrict c₀ κ (le_refl κ) = c₀ := by
    funext i
    exact congrArg c₀ (Fin.ext rfl)
  have hW : ∀ (ωA : A.Ω) (ωL : BL.Ω) (ωR : BR.Ω), QL ωL → QR ωR →
      coinWt (coinW A BL BR ωA ωL ωR (ε := ε)) c₀ = wF := by
    intro ωA ωL ωR hqL hqR
    rw [hwF, ← hres]
    refine coinWt_restrict_congr A BL BR κ ε (le_refl κ) c₀ ωA ω₀.1
      ωL ω₀.2.1 ωR ω₀.2.2.1 ?_ ?_
    · refine BL.href _ nL2 ?_ _ _ hqL
      rw [hnL2]
      omega
    · refine BR.href _ nR2 ?_ _ _ hqR
      rw [hnR2]
      omega
  -- masses
  set mA := ∑ ωA ∈ Finset.univ.filter QA, A.P ωA with hmA
  set mLmass := ∑ ωL ∈ Finset.univ.filter QL, BL.P ωL with hmL
  set mRmass := ∑ ωR ∈ Finset.univ.filter QR, BR.P ωR with hmR
  set mCmass := ∑ ωC ∈ Finset.univ.filter QC, CC.P ωC with hmC
  have hmA0 : 0 ≤ mA :=
    Finset.sum_nonneg fun ωA _ => le_of_lt (A.hP ωA)
  have hmL0 : 0 ≤ mLmass :=
    Finset.sum_nonneg fun ωL _ => le_of_lt (BL.hP ωL)
  have hmR0 : 0 ≤ mRmass :=
    Finset.sum_nonneg fun ωR _ => le_of_lt (BR.hP ωR)
  have hmC0 : 0 ≤ mCmass :=
    Finset.sum_nonneg fun ωC _ => le_of_lt (CC.hP ωC)
  have hmL1 : (∑ ωL ∈ Finset.univ.filter QL, BL.P ωL * (1:ℝ)) = mLmass := by
    rw [hmL]
    exact Finset.sum_congr rfl fun _ _ => mul_one _
  have hmR1 : (∑ ωR ∈ Finset.univ.filter QR, BR.P ωR * (1:ℝ)) = mRmass := by
    rw [hmR]
    exact Finset.sum_congr rfl fun _ _ => mul_one _
  have hmass : (∑ ω ∈ Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
      rhist2 A BL BR CC κ ω r = rhist2 A BL BR CC κ ω₀ r),
      RP A BL BR CC κ ε ω)
      = wF * (mA * (mLmass * (mRmass * mCmass))) := by
    rw [hfil]
    have h1 := sum_RP_factor_tail A BL BR CC κ ε hε QA QL QR QC c₀
      (fun _ => 1) (fun _ => 1) (fun _ => 1) wF hW
    have h2 : ∀ ω ∈ Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
        QA ω.1 ∧ QL ω.2.1 ∧ QR ω.2.2.1 ∧ QC ω.2.2.2.1
          ∧ ω.2.2.2.2 = c₀),
        RP A BL BR CC κ ε ω
        = RP A BL BR CC κ ε ω * ((1:ℝ) * 1 * 1) := by
      intro ω _
      ring
    rw [Finset.sum_congr rfl h2, h1]
    have h3 : ∑ ωC ∈ Finset.univ.filter QC, CC.P ωC * (1:ℝ) = mCmass := by
      rw [hmC]
      exact Finset.sum_congr rfl fun _ _ => mul_one _
    rw [hmL1, hmR1, h3]
  -- start alignment
  set SH := shadowFrom hOrig.length πT GmTL hGT hGneT E hPad with hSHdef
  have hstart : SH.pos hOrig = πT (E.pos hPad) := by
    rw [hSHdef]
    refine shadowFrom_pos_boundary hOrig.length πT GmTL hGT hGneT E hPad
      rfl ?_
    intro Sl hgl
    have hlxv : lastXset CC ω₀.2.2.2.1 n = Sl := by
      unfold lastXset
      rw [hgl, Option.getD_some]
    have hshape := rpre_getLast_tail_CC_L A BL BR CC GmA GmL GmR GmTL GmTR
      stopPt κ hκL hκR hchC ω₀ hs hk1 (by omega)
    have hidx2 : k - remCnt A BL BR CC κ ω₀ = n := by
      rw [hndef]
    rw [hidx2] at hshape
    have hz := pos_in_getLast E hshape
      (hGneT _ (lastXset_ne CC ω₀.2.2.2.1 n))
    have hz2 := hGT _ _ hz
    rw [hlxv] at hz2
    exact hz2
  -- the side cost bound
  have hside := CC.hcost ⟨n, hn⟩ ω₀.2.2.2.1 SH
    (fun l => bail (hPad ++ reqMap GmTL (l.drop hOrig.length)))
  have hsize0 : CC.size ω₀.2.2.2.1 ⟨n, hn⟩ = CC.sizeN n ω₀.2.2.2.1 := by
    unfold ChunkSystemB.sizeN
    rw [dif_pos hn]
  -- per-outcome domination
  have hdom : ∀ ωC ∈ Finset.univ.filter QC,
      CC.P ωC * SH.bailCost
          (fun l => bail (hPad ++ reqMap GmTL (l.drop hOrig.length)))
          (((List.ofFn (CC.chunk ωC)).take n).flatten)
          (CC.chunk ωC ⟨n, hn⟩) pe
      ≤ CC.P ωC * E.bailCost bail hPad
          (reqMap GmTL (CC.chunk ωC ⟨n, hn⟩)) p' := by
    intro ωC hωC
    rw [Finset.mem_filter] at hωC
    have hpre : ((List.ofFn (CC.chunk ωC)).take n).flatten = hOrig := by
      rw [hOdef]
      congr 1
      exact take_congr CC (le_refl _) hωC.2
    rw [hpre]
    refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (CC.hP ωC))
    rw [hSHdef]
    exact shadowFrom_bailCost_le hOrig.length πT GmTL hπT hGT hGneT E bail
      hPad hOrig (CC.chunk ωC ⟨n, hn⟩) hpe rfl hstart
  -- identify the goal integrand
  have hident : ∀ ω ∈ Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
      QA ω.1 ∧ QL ω.2.1 ∧ QR ω.2.2.1 ∧ QC ω.2.2.2.1 ∧ ω.2.2.2.2 = c₀),
      RP A BL BR CC κ ε ω
        * E.bailCost bail
          (rpre A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω r)
          (rchunk A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω r) p'
      = RP A BL BR CC κ ε ω
        * ((fun _ : BL.Ω => (1:ℝ)) ω.2.1
          * (fun _ : BR.Ω => (1:ℝ)) ω.2.2.1
          * (fun ωC => E.bailCost bail hPad
            (reqMap GmTL (CC.chunk ωC ⟨n, hn⟩)) p') ω.2.2.2.1) := by
    intro ω hω
    rw [Finset.mem_filter] at hω
    obtain ⟨-, hqA, hqL, hqR, hqC, hqc⟩ := hω
    have hatom : rhist2 A BL BR CC κ ω r = rhist2 A BL BR CC κ ω₀ r :=
      (hiff ω).mpr ⟨hqA, hqL, hqR, hqC, hqc⟩
    have hpre : rpre A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω r
        = hPad := by
      rw [hPdef]
      exact rpre_congr A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ hκL hκR
        hatom
    have hsurv : survL A BL BR CC κ ω = survL A BL BR CC κ ω₀ := by
      refine survL_congr A BL BR CC κ (by rw [hqc])
        (NL := nL2) (NR := nR2) ?_ ?_ ?_ ?_
      · rw [hqc, hnL2]
        omega
      · rw [hqc, hnR2]
        omega
      · exact hqL
      · exact hqR
    have hrem : remCnt A BL BR CC κ ω = remCnt A BL BR CC κ ω₀ := by
      refine remCnt_congr A BL BR CC κ (by rw [hqc])
        (NL := nL2) (NR := nR2) ?_ ?_ ?_ ?_
      · rw [hqc, hnL2]
        omega
      · rw [hqc, hnR2]
        omega
      · exact hqL
      · exact hqR
    have hch : rchunk A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω r
        = reqMap GmTL (CC.chunk ω.2.2.2.1 ⟨n, hn⟩) := by
      rw [hrdef, rchunk_tail A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω k,
        if_pos (by rw [hsurv]; exact hs),
        if_neg (by rw [hrem]; omega), if_pos (by rw [hrem]; omega)]
      rw [hrem]
      rw [show k - remCnt A BL BR CC κ ω₀ = n from by rw [hndef]]
      rw [chunkN_lt CC ω.2.2.2.1 hn]
    rw [hpre, hch]
    ring
  -- the factored cost sum
  have hpart : (∑ ω ∈ Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
      rhist2 A BL BR CC κ ω r = rhist2 A BL BR CC κ ω₀ r),
      RP A BL BR CC κ ε ω
        * E.bailCost bail
          (rpre A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω r)
          (rchunk A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω r) p')
      = wF * (mA * (mLmass * (mRmass
        * (∑ ωC ∈ Finset.univ.filter QC,
          CC.P ωC * E.bailCost bail hPad
            (reqMap GmTL (CC.chunk ωC ⟨n, hn⟩)) p')))) := by
    rw [hfil, Finset.sum_congr rfl hident,
      sum_RP_factor_tail A BL BR CC κ ε hε QA QL QR QC c₀
        (fun _ => 1) (fun _ => 1)
        (fun ωC => E.bailCost bail hPad
          (reqMap GmTL (CC.chunk ωC ⟨n, hn⟩)) p')
        wF hW, hmL1, hmR1]
  -- the side premise
  have hbailsum : CC.sizeN n ω₀.2.2.2.1 * mCmass
      ≤ ∑ ωC ∈ Finset.univ.filter QC,
        CC.P ωC * E.bailCost bail hPad
          (reqMap GmTL (CC.chunk ωC ⟨n, hn⟩)) p' := by
    have h1 : CC.sizeN n ω₀.2.2.2.1 * mCmass
        ≤ ∑ ωC ∈ Finset.univ.filter QC,
          CC.P ωC * SH.bailCost
            (fun l => bail (hPad ++ reqMap GmTL (l.drop hOrig.length)))
            (((List.ofFn (CC.chunk ωC)).take n).flatten)
            (CC.chunk ωC ⟨n, hn⟩) pe := by
      rw [← hsize0]
      exact hside
    exact le_trans h1 (Finset.sum_le_sum hdom)
  -- rsize identification
  have hrsize : rsize A BL BR CC κ ε ω₀ r = CC.sizeN n ω₀.2.2.2.1 := by
    rw [hrdef, rsize_tail A BL BR CC κ ε ω₀ k,
      if_neg (by omega),
      if_neg (by omega)]
  -- assemble
  rw [hrsize, hmass, hpart]
  calc CC.sizeN n ω₀.2.2.2.1 * (wF * (mA * (mLmass * (mRmass * mCmass))))
      = wF * (mA * (mLmass * (mRmass
        * (CC.sizeN n ω₀.2.2.2.1 * mCmass)))) := by ring
    _ ≤ wF * (mA * (mLmass * (mRmass
        * (∑ ωC ∈ Finset.univ.filter QC,
          CC.P ωC * E.bailCost bail hPad
            (reqMap GmTL (CC.chunk ωC ⟨n, hn⟩)) p')))) := by
        refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hwFpos)
        refine mul_le_mul_of_nonneg_left ?_ hmA0
        refine mul_le_mul_of_nonneg_left ?_ hmL0
        exact mul_le_mul_of_nonneg_left hbailsum hmR0





open Classical in
/-- The tail-system cost bound (right survivor). -/
theorem race_hcost_CC_R (hε : 0 < ε) (hκL : κ ≤ BL.m) (hκR : κ ≤ BR.m)
    (πT : Y → X)
    (hπT : ∀ y z : Y, dist (πT y) (πT z) ≤ dist y z)
    (hGT : ∀ S : Set X, ∀ y ∈ GmTR S, πT y ∈ S)
    (hGneT : ∀ S : Set X, S.Nonempty → (GmTR S).Nonempty)
    (hchC : ∀ (ωc : CC.Ω) (i : Fin CC.m), CC.chunk ωc i ≠ [])
    {p' : ℝ} (hpe : pe ≤ p')
    (ω₀ : RΩ A BL BR CC κ) (E : EvaderAlgorithm Y)
    (bail : List (Set Y) → Bool)
    {k : ℕ} (hs : survL A BL BR CC κ ω₀ = false)
    (hk1 : remCnt A BL BR CC κ ω₀ < k)
    (hkc : k - remCnt A BL BR CC κ ω₀ < CC.m) :
    rsize A BL BR CC κ ε ω₀ (A.m + κ + k)
      * (∑ ω ∈ Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
          rhist2 A BL BR CC κ ω (A.m + κ + k)
            = rhist2 A BL BR CC κ ω₀ (A.m + κ + k)),
        RP A BL BR CC κ ε ω)
    ≤ ∑ ω ∈ Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
        rhist2 A BL BR CC κ ω (A.m + κ + k)
          = rhist2 A BL BR CC κ ω₀ (A.m + κ + k)),
      RP A BL BR CC κ ε ω
        * E.bailCost bail
          (rpre A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω (A.m + κ + k))
          (rchunk A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω
            (A.m + κ + k)) p' := by
  set r := A.m + κ + k with hrdef
  set c₀ := ω₀.2.2.2.2 with hc₀
  have hsn : ¬ (survL A BL BR CC κ ω₀ = true) := by
    rw [hs]
    simp
  have hcm : cntL c₀ κ ≤ BL.m := le_trans (cntL_le _ le_rfl) hκL
  have hcmR : cntR c₀ κ ≤ BR.m := le_trans (cntR_le _ le_rfl) hκR
  set n := k - remCnt A BL BR CC κ ω₀ with hndef
  have hn : n < CC.m := by omega
  have hkm : r - A.m - κ = k := by omega
  have hk1' : 1 ≤ k := by omega
  -- the revealed counts at the base outcome
  have hrevLv : revL2 A BL BR CC κ ω₀ k = min (cntL c₀ κ + k) BL.m := by
    unfold revL2
    rw [← hc₀]
  have hrevRv : revR2 A BL BR CC κ ω₀ k = min (cntR c₀ κ + k) BR.m := by
    unfold revR2
    rw [← hc₀]
  set nL2 := min (cntL c₀ κ + k) BL.m with hnL2
  set nR2 := min (cntR c₀ κ + k) BR.m with hnR2
  have hrevCv : revC A BL BR CC κ ω₀ k = n := by
    unfold revC
    rw [← hndef]
    omega
  set hPad := rpre A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω₀ r
    with hPdef
  set hOrig := ((List.ofFn (CC.chunk ω₀.2.2.2.1)).take n).flatten
    with hOdef
  -- atom conditions
  set QA : A.Ω → Prop := fun ωA => A.hist A.m ωA = A.hist A.m ω₀.1
    with hQA
  set QL : BL.Ω → Prop :=
    fun ωL => BL.hist nL2 ωL = BL.hist nL2 ω₀.2.1 with hQL
  set QR : BR.Ω → Prop :=
    fun ωR => BR.hist nR2 ωR = BR.hist nR2 ω₀.2.2.1 with hQR
  set QC : CC.Ω → Prop :=
    fun ωC => CC.hist n ωC = CC.hist n ω₀.2.2.2.1 with hQC
  have hiff : ∀ ω : RΩ A BL BR CC κ,
      (rhist2 A BL BR CC κ ω r = rhist2 A BL BR CC κ ω₀ r)
      ↔ (QA ω.1 ∧ QL ω.2.1 ∧ QR ω.2.2.1 ∧ QC ω.2.2.2.1
        ∧ ω.2.2.2.2 = c₀) := by
    intro ω
    rw [rhist2_eq_iff_tail A BL BR CC κ hκL hκR (by omega), hkm,
      hrevLv, hrevRv, hrevCv]
    constructor
    · rintro ⟨h1, h2, h3, h4, h5⟩
      exact ⟨h1, h3, h4, h5, h2⟩
    · rintro ⟨h1, h2, h3, h4, h5⟩
      exact ⟨h1, h5, h2, h3, h4⟩
  have hfil : (Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
      rhist2 A BL BR CC κ ω r = rhist2 A BL BR CC κ ω₀ r))
      = Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
        QA ω.1 ∧ QL ω.2.1 ∧ QR ω.2.2.1 ∧ QC ω.2.2.2.1
          ∧ ω.2.2.2.2 = c₀) := by
    refine Finset.filter_congr fun ω _ => ?_
    exact hiff ω
  -- the fixed coin weight
  set wF := coinWt (coinW A BL BR ω₀.1 ω₀.2.1 ω₀.2.2.1 (ε := ε)) c₀
    with hwF
  have hwFpos : 0 < wF := by
    rw [hwF]
    refine coinWt_pos (fun q p b => ?_) _
    rw [coinW_eval]
    by_cases hb : b
    · rw [if_pos hb]
      exact probL_pos hε
    · rw [if_neg hb]
      exact probL_pos hε
  have hres : restrict c₀ κ (le_refl κ) = c₀ := by
    funext i
    exact congrArg c₀ (Fin.ext rfl)
  have hW : ∀ (ωA : A.Ω) (ωL : BL.Ω) (ωR : BR.Ω), QL ωL → QR ωR →
      coinWt (coinW A BL BR ωA ωL ωR (ε := ε)) c₀ = wF := by
    intro ωA ωL ωR hqL hqR
    rw [hwF, ← hres]
    refine coinWt_restrict_congr A BL BR κ ε (le_refl κ) c₀ ωA ω₀.1
      ωL ω₀.2.1 ωR ω₀.2.2.1 ?_ ?_
    · refine BL.href _ nL2 ?_ _ _ hqL
      rw [hnL2]
      omega
    · refine BR.href _ nR2 ?_ _ _ hqR
      rw [hnR2]
      omega
  -- masses
  set mA := ∑ ωA ∈ Finset.univ.filter QA, A.P ωA with hmA
  set mLmass := ∑ ωL ∈ Finset.univ.filter QL, BL.P ωL with hmL
  set mRmass := ∑ ωR ∈ Finset.univ.filter QR, BR.P ωR with hmR
  set mCmass := ∑ ωC ∈ Finset.univ.filter QC, CC.P ωC with hmC
  have hmA0 : 0 ≤ mA :=
    Finset.sum_nonneg fun ωA _ => le_of_lt (A.hP ωA)
  have hmL0 : 0 ≤ mLmass :=
    Finset.sum_nonneg fun ωL _ => le_of_lt (BL.hP ωL)
  have hmR0 : 0 ≤ mRmass :=
    Finset.sum_nonneg fun ωR _ => le_of_lt (BR.hP ωR)
  have hmC0 : 0 ≤ mCmass :=
    Finset.sum_nonneg fun ωC _ => le_of_lt (CC.hP ωC)
  have hmL1 : (∑ ωL ∈ Finset.univ.filter QL, BL.P ωL * (1:ℝ)) = mLmass := by
    rw [hmL]
    exact Finset.sum_congr rfl fun _ _ => mul_one _
  have hmR1 : (∑ ωR ∈ Finset.univ.filter QR, BR.P ωR * (1:ℝ)) = mRmass := by
    rw [hmR]
    exact Finset.sum_congr rfl fun _ _ => mul_one _
  have hmass : (∑ ω ∈ Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
      rhist2 A BL BR CC κ ω r = rhist2 A BL BR CC κ ω₀ r),
      RP A BL BR CC κ ε ω)
      = wF * (mA * (mLmass * (mRmass * mCmass))) := by
    rw [hfil]
    have h1 := sum_RP_factor_tail A BL BR CC κ ε hε QA QL QR QC c₀
      (fun _ => 1) (fun _ => 1) (fun _ => 1) wF hW
    have h2 : ∀ ω ∈ Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
        QA ω.1 ∧ QL ω.2.1 ∧ QR ω.2.2.1 ∧ QC ω.2.2.2.1
          ∧ ω.2.2.2.2 = c₀),
        RP A BL BR CC κ ε ω
        = RP A BL BR CC κ ε ω * ((1:ℝ) * 1 * 1) := by
      intro ω _
      ring
    rw [Finset.sum_congr rfl h2, h1]
    have h3 : ∑ ωC ∈ Finset.univ.filter QC, CC.P ωC * (1:ℝ) = mCmass := by
      rw [hmC]
      exact Finset.sum_congr rfl fun _ _ => mul_one _
    rw [hmL1, hmR1, h3]
  -- start alignment
  set SH := shadowFrom hOrig.length πT GmTR hGT hGneT E hPad with hSHdef
  have hstart : SH.pos hOrig = πT (E.pos hPad) := by
    rw [hSHdef]
    refine shadowFrom_pos_boundary hOrig.length πT GmTR hGT hGneT E hPad
      rfl ?_
    intro Sl hgl
    have hlxv : lastXset CC ω₀.2.2.2.1 n = Sl := by
      unfold lastXset
      rw [hgl, Option.getD_some]
    have hshape := rpre_getLast_tail_CC_R A BL BR CC GmA GmL GmR GmTL GmTR
      stopPt κ hchC ω₀ hs hk1 (by omega)
    have hidx2 : k - remCnt A BL BR CC κ ω₀ = n := by
      rw [hndef]
    rw [hidx2] at hshape
    have hz := pos_in_getLast E hshape
      (hGneT _ (lastXset_ne CC ω₀.2.2.2.1 n))
    have hz2 := hGT _ _ hz
    rw [hlxv] at hz2
    exact hz2
  -- the side cost bound
  have hside := CC.hcost ⟨n, hn⟩ ω₀.2.2.2.1 SH
    (fun l => bail (hPad ++ reqMap GmTR (l.drop hOrig.length)))
  have hsize0 : CC.size ω₀.2.2.2.1 ⟨n, hn⟩ = CC.sizeN n ω₀.2.2.2.1 := by
    unfold ChunkSystemB.sizeN
    rw [dif_pos hn]
  -- per-outcome domination
  have hdom : ∀ ωC ∈ Finset.univ.filter QC,
      CC.P ωC * SH.bailCost
          (fun l => bail (hPad ++ reqMap GmTR (l.drop hOrig.length)))
          (((List.ofFn (CC.chunk ωC)).take n).flatten)
          (CC.chunk ωC ⟨n, hn⟩) pe
      ≤ CC.P ωC * E.bailCost bail hPad
          (reqMap GmTR (CC.chunk ωC ⟨n, hn⟩)) p' := by
    intro ωC hωC
    rw [Finset.mem_filter] at hωC
    have hpre : ((List.ofFn (CC.chunk ωC)).take n).flatten = hOrig := by
      rw [hOdef]
      congr 1
      exact take_congr CC (le_refl _) hωC.2
    rw [hpre]
    refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (CC.hP ωC))
    rw [hSHdef]
    exact shadowFrom_bailCost_le hOrig.length πT GmTR hπT hGT hGneT E bail
      hPad hOrig (CC.chunk ωC ⟨n, hn⟩) hpe rfl hstart
  -- identify the goal integrand
  have hident : ∀ ω ∈ Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
      QA ω.1 ∧ QL ω.2.1 ∧ QR ω.2.2.1 ∧ QC ω.2.2.2.1 ∧ ω.2.2.2.2 = c₀),
      RP A BL BR CC κ ε ω
        * E.bailCost bail
          (rpre A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω r)
          (rchunk A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω r) p'
      = RP A BL BR CC κ ε ω
        * ((fun _ : BL.Ω => (1:ℝ)) ω.2.1
          * (fun _ : BR.Ω => (1:ℝ)) ω.2.2.1
          * (fun ωC => E.bailCost bail hPad
            (reqMap GmTR (CC.chunk ωC ⟨n, hn⟩)) p') ω.2.2.2.1) := by
    intro ω hω
    rw [Finset.mem_filter] at hω
    obtain ⟨-, hqA, hqL, hqR, hqC, hqc⟩ := hω
    have hatom : rhist2 A BL BR CC κ ω r = rhist2 A BL BR CC κ ω₀ r :=
      (hiff ω).mpr ⟨hqA, hqL, hqR, hqC, hqc⟩
    have hpre : rpre A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω r
        = hPad := by
      rw [hPdef]
      exact rpre_congr A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ hκL hκR
        hatom
    have hsurv : survL A BL BR CC κ ω = survL A BL BR CC κ ω₀ := by
      refine survL_congr A BL BR CC κ (by rw [hqc])
        (NL := nL2) (NR := nR2) ?_ ?_ ?_ ?_
      · rw [hqc, hnL2]
        omega
      · rw [hqc, hnR2]
        omega
      · exact hqL
      · exact hqR
    have hrem : remCnt A BL BR CC κ ω = remCnt A BL BR CC κ ω₀ := by
      refine remCnt_congr A BL BR CC κ (by rw [hqc])
        (NL := nL2) (NR := nR2) ?_ ?_ ?_ ?_
      · rw [hqc, hnL2]
        omega
      · rw [hqc, hnR2]
        omega
      · exact hqL
      · exact hqR
    have hch : rchunk A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω r
        = reqMap GmTR (CC.chunk ω.2.2.2.1 ⟨n, hn⟩) := by
      rw [hrdef, rchunk_tail A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω k,
        if_neg (by rw [hsurv, hs]; simp),
        if_neg (by rw [hrem]; omega), if_pos (by rw [hrem]; omega)]
      rw [hrem]
      rw [show k - remCnt A BL BR CC κ ω₀ = n from by rw [hndef]]
      rw [chunkN_lt CC ω.2.2.2.1 hn]
    rw [hpre, hch]
    ring
  -- the factored cost sum
  have hpart : (∑ ω ∈ Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
      rhist2 A BL BR CC κ ω r = rhist2 A BL BR CC κ ω₀ r),
      RP A BL BR CC κ ε ω
        * E.bailCost bail
          (rpre A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω r)
          (rchunk A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω r) p')
      = wF * (mA * (mLmass * (mRmass
        * (∑ ωC ∈ Finset.univ.filter QC,
          CC.P ωC * E.bailCost bail hPad
            (reqMap GmTR (CC.chunk ωC ⟨n, hn⟩)) p')))) := by
    rw [hfil, Finset.sum_congr rfl hident,
      sum_RP_factor_tail A BL BR CC κ ε hε QA QL QR QC c₀
        (fun _ => 1) (fun _ => 1)
        (fun ωC => E.bailCost bail hPad
          (reqMap GmTR (CC.chunk ωC ⟨n, hn⟩)) p')
        wF hW, hmL1, hmR1]
  -- the side premise
  have hbailsum : CC.sizeN n ω₀.2.2.2.1 * mCmass
      ≤ ∑ ωC ∈ Finset.univ.filter QC,
        CC.P ωC * E.bailCost bail hPad
          (reqMap GmTR (CC.chunk ωC ⟨n, hn⟩)) p' := by
    have h1 : CC.sizeN n ω₀.2.2.2.1 * mCmass
        ≤ ∑ ωC ∈ Finset.univ.filter QC,
          CC.P ωC * SH.bailCost
            (fun l => bail (hPad ++ reqMap GmTR (l.drop hOrig.length)))
            (((List.ofFn (CC.chunk ωC)).take n).flatten)
            (CC.chunk ωC ⟨n, hn⟩) pe := by
      rw [← hsize0]
      exact hside
    exact le_trans h1 (Finset.sum_le_sum hdom)
  -- rsize identification
  have hrsize : rsize A BL BR CC κ ε ω₀ r = CC.sizeN n ω₀.2.2.2.1 := by
    rw [hrdef, rsize_tail A BL BR CC κ ε ω₀ k,
      if_neg (by omega),
      if_neg (by omega)]
  -- assemble
  rw [hrsize, hmass, hpart]
  calc CC.sizeN n ω₀.2.2.2.1 * (wF * (mA * (mLmass * (mRmass * mCmass))))
      = wF * (mA * (mLmass * (mRmass
        * (CC.sizeN n ω₀.2.2.2.1 * mCmass)))) := by ring
    _ ≤ wF * (mA * (mLmass * (mRmass
        * (∑ ωC ∈ Finset.univ.filter QC,
          CC.P ωC * E.bailCost bail hPad
            (reqMap GmTR (CC.chunk ωC ⟨n, hn⟩)) p')))) := by
        refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hwFpos)
        refine mul_le_mul_of_nonneg_left ?_ hmA0
        refine mul_le_mul_of_nonneg_left ?_ hmL0
        exact mul_le_mul_of_nonneg_left hbailsum hmR0




end TailMain





section HcostFinal

variable (A BL BR CC : ChunkSystemB X s t 0 cB T pe mL)
variable (GmA GmL GmR GmTL GmTR : Set X → Set Y) (stopPt : Y)
variable (κ : ℕ) (ε : ℝ)

/-- Chunks with zero claimed size cost nothing. -/
theorem race_hcost_trivial (hε : 0 < ε) {p' : ℝ} (hp'0 : 0 ≤ p')
    {r : ℕ} (ω₀ : RΩ A BL BR CC κ) (E : EvaderAlgorithm Y)
    (bail : List (Set Y) → Bool)
    (hz : rsize A BL BR CC κ ε ω₀ r = 0) :
    rsize A BL BR CC κ ε ω₀ r
      * (∑ ω ∈ Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
          rhist2 A BL BR CC κ ω r = rhist2 A BL BR CC κ ω₀ r),
        RP A BL BR CC κ ε ω)
    ≤ ∑ ω ∈ Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
        rhist2 A BL BR CC κ ω r = rhist2 A BL BR CC κ ω₀ r),
      RP A BL BR CC κ ε ω
        * E.bailCost bail
          (rpre A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω r)
          (rchunk A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω r) p' := by
  rw [hz, zero_mul]
  refine Finset.sum_nonneg fun ω _ => ?_
  exact mul_nonneg (le_of_lt (RP_pos A BL BR CC κ ε hε ω))
    (E.bailCost_nonneg _ _ _ hp'0)

open Classical in
/-- **The race chunk-cost bound**, all phases. -/
theorem race_hcost (hε : 0 < ε) (hκL : κ ≤ BL.m) (hκR : κ ≤ BR.m)
    (πA πL πR πTL πTR : Y → X)
    (hπA : ∀ y z : Y, dist (πA y) (πA z) ≤ dist y z)
    (hπL : ∀ y z : Y, dist (πL y) (πL z) ≤ dist y z)
    (hπR : ∀ y z : Y, dist (πR y) (πR z) ≤ dist y z)
    (hπTL : ∀ y z : Y, dist (πTL y) (πTL z) ≤ dist y z)
    (hπTR : ∀ y z : Y, dist (πTR y) (πTR z) ≤ dist y z)
    (hGA : ∀ S : Set X, ∀ y ∈ GmA S, πA y ∈ S)
    (hGL : ∀ S : Set X, ∀ y ∈ GmL S, πL y ∈ S)
    (hGR : ∀ S : Set X, ∀ y ∈ GmR S, πR y ∈ S)
    (hGTL : ∀ S : Set X, ∀ y ∈ GmTL S, πTL y ∈ S)
    (hGTR : ∀ S : Set X, ∀ y ∈ GmTR S, πTR y ∈ S)
    (hGneA : ∀ S : Set X, S.Nonempty → (GmA S).Nonempty)
    (hGneL : ∀ S : Set X, S.Nonempty → (GmL S).Nonempty)
    (hGneR : ∀ S : Set X, S.Nonempty → (GmR S).Nonempty)
    (hGneTL : ∀ S : Set X, S.Nonempty → (GmTL S).Nonempty)
    (hGneTR : ∀ S : Set X, S.Nonempty → (GmTR S).Nonempty)
    (hchA : ∀ (ωa : A.Ω) (i : Fin A.m), A.chunk ωa i ≠ [])
    (hchL : ∀ (ωl : BL.Ω) (i : Fin BL.m), BL.chunk ωl i ≠ [])
    (hchR : ∀ (ωr : BR.Ω) (i : Fin BR.m), BR.chunk ωr i ≠ [])
    (hchC : ∀ (ωc : CC.Ω) (i : Fin CC.m), CC.chunk ωc i ≠ [])
    {sep J p' : ℝ}
    (hpe0 : 0 ≤ pe) (hpe : pe ≤ p') (hsep0 : 0 < sep)
    (hdiam : ∀ x₁ x₂ : X, dist x₁ x₂ ≤ J) (harith : J + pe ≤ sep)
    (hsepLR : ∀ SL SR : Set X, ∀ y ∈ GmL SL,
      ∀ z ∈ GmR SR, sep ≤ dist y z)
    (hdicho : ∀ z : Y,
      (z ∈ GmA ({t} : Set X) ∨ (∃ S, z ∈ GmL S) ∨ (∃ S, z ∈ GmR S)) →
      (∀ S' : Set X, ∀ p ∈ GmR S', sep ≤ dist z p)
      ∨ (∀ S' : Set X, ∀ p ∈ GmL S', sep ≤ dist z p))
    (h0L : ∀ a b : BL.Ω, BL.hist 0 a = BL.hist 0 b)
    (h0R : ∀ a b : BR.Ω, BR.hist 0 a = BR.hist 0 b)
    {r : ℕ}
    (ω₀ : RΩ A BL BR CC κ) (E : EvaderAlgorithm Y)
    (bail : List (Set Y) → Bool) :
    rsize A BL BR CC κ ε ω₀ r
      * (∑ ω ∈ Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
          rhist2 A BL BR CC κ ω r = rhist2 A BL BR CC κ ω₀ r),
        RP A BL BR CC κ ε ω)
    ≤ ∑ ω ∈ Finset.univ.filter (fun ω : RΩ A BL BR CC κ =>
        rhist2 A BL BR CC κ ω r = rhist2 A BL BR CC κ ω₀ r),
      RP A BL BR CC κ ε ω
        * E.bailCost bail
          (rpre A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω r)
          (rchunk A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ω r) p' := by
  have hp'0 : 0 ≤ p' := le_trans hpe0 hpe
  by_cases hr1 : r < A.m
  · exact race_hcost_A A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ε hε
      πA hπA hGA hGneA hpe hr1 ω₀ E bail
  · rw [not_lt] at hr1
    by_cases hr2 : r < A.m + κ
    · obtain ⟨j, rfl⟩ : ∃ j, r = A.m + j := ⟨r - A.m, by omega⟩
      exact race_hcost_coin A BL BR CC GmA GmL GmR GmTL GmTR stopPt κ ε
        hε hκL hκR πL πR hπL hπR hGL hGR hGneA hGneL hGneR hGneTL hGneTR
        hchA hchL hchR hpe0 hpe hsep0 hdiam harith hsepLR hdicho h0L h0R
        (by omega) ω₀ E bail
    · rw [not_lt] at hr2
      obtain ⟨k, rfl⟩ : ∃ k, r = A.m + κ + k := ⟨r - A.m - κ, by omega⟩
      by_cases hz1 : k = 0 ∨ k = remCnt A BL BR CC κ ω₀
      · refine race_hcost_trivial A BL BR CC GmA GmL GmR GmTL GmTR stopPt
          κ ε hε hp'0 ω₀ E bail ?_
        rw [rsize_tail A BL BR CC κ ε ω₀ k, if_pos hz1]
      · by_cases hk : k < remCnt A BL BR CC κ ω₀
        · by_cases hs : survL A BL BR CC κ ω₀
          · exact race_hcost_tail_L A BL BR CC GmA GmL GmR GmTL GmTR
              stopPt κ ε hε hκL hκR πL hπL hGL hGneL hchL hpe ω₀ E bail
              hs (by omega) hk
          · exact race_hcost_tail_R A BL BR CC GmA GmL GmR GmTL GmTR
              stopPt κ ε hε hκL hκR πR hπR hGR hGneR hchR hpe ω₀ E bail
              (by
                cases hsv : survL A BL BR CC κ ω₀
                · rfl
                · exact absurd hsv hs) (by omega) hk
        · by_cases hk2 : k - remCnt A BL BR CC κ ω₀ < CC.m
          · by_cases hs : survL A BL BR CC κ ω₀
            · exact race_hcost_CC_L A BL BR CC GmA GmL GmR GmTL GmTR
                stopPt κ ε hε hκL hκR πTL hπTL hGTL hGneTL hchC hpe ω₀ E
                bail hs (by omega) hk2
            · exact race_hcost_CC_R A BL BR CC GmA GmL GmR GmTL GmTR
                stopPt κ ε hε hκL hκR πTR hπTR hGTR hGneTR hchC hpe ω₀ E
                bail (by
                  cases hsv : survL A BL BR CC κ ω₀
                  · rfl
                  · exact absurd hsv hs) (by omega) hk2
          · refine race_hcost_trivial A BL BR CC GmA GmL GmR GmTL GmTR
              stopPt κ ε hε hp'0 ω₀ E bail ?_
            rw [rsize_tail A BL BR CC κ ε ω₀ k, if_neg hz1,
              if_neg hk]
            unfold ChunkSystemB.sizeN
            rw [dif_neg (by omega)]

end HcostFinal


end Race

end KServer


