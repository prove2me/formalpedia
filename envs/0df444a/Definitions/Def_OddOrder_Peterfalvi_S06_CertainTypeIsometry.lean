-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S06_CertainTypeIsometry
-- name    : OddOrder_Peterfalvi_S06_CertainTypeIsometry
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T06:14:49.993995+00:00
-- url     : https://prove2.me/theorems/7503cd1e-7dec-46c4-9f60-26991fbb6336
-- title:
--   Peterfalvi (4.8): equal-degree certain-type differences are $\sigma$-isometric
-- statement:
--   Peterfalvi, *Character Theory for the Odd Order Theorem*, §4, pp. 23-24, statement (4.8). Under Hypothesis (4.6), fix a row $i$ and two nontrivial columns $j,k$. If $\mu_{ij}(1)=\mu_{ik}(1)$, then $\mathrm{Supp}(\mu_{ij}-\mu_{ik})\subseteq A_0$ and the difference behaves isometrically under $\sigma$.
--
--   Main definitions: `ticVdiff` (the (3.1)-for-$G$ TI-cyclic hypothesis on the smaller TI set $V=W-(W_1\cup W_2)$), `ticVdiffFullDadeApplication`, `ticWEquivSdiffW` (the bridge isomorphism between the two descriptions of $W$), `omegaProdCharTic` and `certainTypeOmegaSigma` (the $G$-side $\sigma$-image of the column character $\omega_{ij}$).
--
--   The bundle also proves 16 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S06_CertainTypeIsometry.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S06_CertainTypeIsometry.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S06_CertainTypeSupport
import Definitions.Def_OddOrder_Peterfalvi_S06_CertainTypeStructure
import Definitions.Def_OddOrder_Peterfalvi_S05_GridTrichotomy

namespace OddOrder.Peterfalvi.S06

open OddOrder.RepresentationTheory

open scoped IsMulCommutative

variable {G : Type*} [Group G] [Fintype G]

variable {A : Set G} {L : Subgroup G} [Fintype ↥L]

variable [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥L : ℂ)]

/-- The (3.1)-for-`G` TI-cyclic hypothesis on the **smaller** TI set `V = W − (W₁ ∪ W₂)`, the one
the §5 `σ`-machinery ((3.2)-(3.9)) runs on (the `ω_{ij}`-basis lives in `CF(W, V)`, vanishing on
`W₁` and `W₂`).  The ambient `h.tic` carries `V = W − W₂` for the Dade isometry `τ`; this shrinks
the TI set, which stays TI since `W − (W₁ ∪ W₂) ⊆ W − W₂` and `IsTISubset` is antitone in the set
(`tic.V_ti.subset`).  This is the `G`-side analogue of the `(L, W)`-side `toTICyclicHypothesis`, and
is what makes `σ_G` (its `sigma`) well-typed: `ticVdiff.V = ticVdiff.Vdiff` by `rfl`. -/
noncomputable def ticVdiff (h : Hypothesis46 A L) :
    OddOrder.Peterfalvi.S05.TICyclicHypothesis G where
  W := h.tic.W
  W1 := h.tic.W1
  W2 := h.tic.W2
  W1_le_W := h.tic.W1_le_W
  W2_le_W := h.tic.W2_le_W
  W1_nontrivial := h.tic.W1_nontrivial
  W2_nontrivial := h.tic.W2_nontrivial
  W_sup := h.tic.W_sup
  W_disjoint := h.tic.W_disjoint
  W_card_coprime := h.tic.W_card_coprime
  W_card_odd := h.tic.W_card_odd
  W_cyclic := h.tic.W_cyclic
  V := (↑h.tic.W : Set G) \ ((↑h.tic.W1 : Set G) ∪ (↑h.tic.W2 : Set G))
  V_subset_sharp := fun v hv => by
    rw [OddOrder.Peterfalvi.S04.mem_sharp]
    exact ⟨Set.mem_univ v, fun heq => hv.2 (Or.inl (by rw [heq]; exact Subgroup.one_mem h.tic.W1))⟩
  V_subset_W := fun _ hv => hv.1
  W_normalizes_V := by
    intro w v hv
    have := h.tic.isMulCommutative_W
    have h1 : (⟨v, hv.1⟩ : ↥h.tic.W) * w = w * ⟨v, hv.1⟩ := mul_comm _ _
    have h2 : (w : G) * v = v * (w : G) := (Subtype.ext_iff.mp h1).symm
    have h3 : (w : G) * v * (w : G)⁻¹ = v := by rw [h2]; exact mul_inv_cancel_right v w
    rw [h3]; exact hv
  V_ti := h.tic.V_ti.subset (by rw [h.tic_V])

/-- The canonical Dade application driving `σ_G`: the §4 Dade package on `ticVdiff`'s TI set
`V = W − (W₁ ∪ W₂)`, whose local subgroups are all trivial (`H(a) = ⊥`), so `HConjInvariant` holds
for free.  Mirror of the `(L, W)`-side `toTICyclicFullDadeApplication`. -/
noncomputable def ticVdiffFullDadeApplication (h : Hypothesis46 A L)
    [Fintype (ticVdiff h).W] [Invertible (Nat.card (ticVdiff h).W : ℂ)] :
    OddOrder.Peterfalvi.S05.TICyclicHypothesis.FullDadeApplication (ticVdiff h) :=
  ⟨(ticVdiff h).toDadeHypothesis.fullDadeIsometryData⟩

/-- `tic.W = (W₁ ⊔ W₂).map (L ↪ G)`: the ambient (3.1)-for-`G` group is the `G`-image of the
certain-type `W = W₁ ⊔ W₂ ≤ L`.  (Named so the bridge `ticWEquivSdiffW` and its coherence share one
proof term.) -/
theorem tic_W_eq_map (h : Hypothesis46 A L) :
    h.tic.W = (h.W1 ⊔ h.W2).map L.subtype := by
  rw [← h.tic.W_sup, h.tic_W1, h.tic_W2, ← Subgroup.map_sup]

/-- The bridge isomorphism `tic.W ≃* sdiff.W` — both are `W₁ ⊔ W₂`, one as a subgroup of `G`, the
other of `L`, identified by the corestriction of `L ↪ G`.  Transports the `sdiff`-side `(L, W)`
characters (`omegaProdChar`, `chiColumn`) to the `tic`-side `(G, W)` for the `G`-side `σ`. -/
noncomputable def ticWEquivSdiffW (h : Hypothesis46 A L) :
    h.tic.W ≃* h.sdiffTICyclicHypothesis.W :=
  (MulEquiv.subgroupCongr (tic_W_eq_map h)).trans
    (Subgroup.equivMapOfInjective (h.W1 ⊔ h.W2) L.subtype L.subtype_injective).symm

set_option backward.isDefEq.respectTransparency false in
/-- Carrier coherence for the bridge: the underlying `G`-element of `g : tic.W` equals the image of
its `sdiff.W` partner under `L ↪ G`. -/
theorem coe_ticWEquivSdiffW (h : Hypothesis46 A L) (g : h.tic.W) :
    ((ticWEquivSdiffW h g : ↥L) : G) = (g : G) := by
  -- `equivMapOfInjective` undoes the `.symm` in the bridge, landing back on the `subgroupCongr`
  -- cast
  have key : (Subgroup.equivMapOfInjective (h.W1 ⊔ h.W2) L.subtype L.subtype_injective)
      (ticWEquivSdiffW h g) = MulEquiv.subgroupCongr (tic_W_eq_map h) g :=
    (Subgroup.equivMapOfInjective (h.W1 ⊔ h.W2) L.subtype L.subtype_injective).apply_symm_apply _
  simpa [Subgroup.coe_equivMapOfInjective_apply, MulEquiv.subgroupCongr_apply] using
    congrArg (fun x : ((h.W1 ⊔ h.W2).map L.subtype) => (x : G)) key

/-- The `tic`-side (`G`) linear character `ω_{ij}` of `W = W₁ ⊔ W₂`, transported from the
`sdiff`-side `omegaProdChar (w1CharEquiv i) χ₂` along the bridge `ticWEquivSdiffW`.  Its `σ_G`-image
`h.tic.sigma rfl (ticFullDadeApplication h) (h.tic.omega …)` is the `ω_{ij}^σ ∈ CF(G)` of (4.8)
conclusion (3). -/
noncomputable def omegaProdCharTic (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1)) :
    h.tic.W →* ℂˣ :=
  (h.sdiffTICyclicHypothesis.omegaProdChar (h.w1CharEquiv i) χ₂).comp (ticWEquivSdiffW h)

/-- The transported `tic`-side character evaluates as the `sdiff`-side `chiColumn` at the bridge
partner: `ω_{ij}^{tic}(g) = ω_{ij}(e g) = chiColumn χ₂ i (e g)` (`e = ticWEquivSdiffW`). -/
theorem omegaProdCharTic_apply (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1)) (g : h.tic.W) :
    ((omegaProdCharTic h χ₂ i g : ℂˣ) : ℂ)
      = (h.chiColumn χ₂ i : ClassFunction h.sdiffTICyclicHypothesis.W ℂ) (ticWEquivSdiffW h g) := by
  rw [omegaProdCharTic, MonoidHom.comp_apply, Hypothesis.chiColumn,
    h.sdiffTICyclicHypothesis.omega_apply]
  rfl

/-- The `G`-side `σ`-image `ω_{ij}^σ ∈ CF(G)` of the certain-type column character `ω_{ij}`, built
from the `ticVdiff` σ-machinery applied to the transported `tic`-side character `omegaProdCharTic`.
This is the right-hand side ingredient of (4.8) conclusion (3). -/
noncomputable def certainTypeOmegaSigma (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    [Fintype (ticVdiff h).W] [Invertible (Nat.card (ticVdiff h).W : ℂ)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1)) : ClassFunction G ℂ :=
  (ticVdiff h).sigma rfl (ticVdiffFullDadeApplication h)
    ((ticVdiff h).omega (omegaProdCharTic h χ₂ i))

set_option backward.isDefEq.respectTransparency false in
/-- The `σ_G`-image on `V = W − (W₁ ∪ W₂)`: `ω_{ij}^σ(v) = ω_{ij}(v) = chiColumn χ₂ i (e v)`
(`sigma_apply_of_mem_V` (3.2.c) + `omega_apply` + `omegaProdCharTic_apply`). -/
theorem certainTypeOmegaSigma_apply_of_mem_V (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    [Fintype (ticVdiff h).W] [Invertible (Nat.card (ticVdiff h).W : ℂ)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1))
    {v : G} (hv : v ∈ (ticVdiff h).V) :
    certainTypeOmegaSigma h χ₂ i v
      = (h.chiColumn χ₂ i : ClassFunction h.sdiffTICyclicHypothesis.W ℂ)
          (ticWEquivSdiffW h ⟨v, (ticVdiff h).V_subset_W hv⟩) := by
  rw [certainTypeOmegaSigma, (ticVdiff h).sigma_apply_of_mem_V rfl _ _ hv,
    (ticVdiff h).omega_apply]
  exact omegaProdCharTic_apply h χ₂ i _

/-- The `σ_G`-image `ω_{ij}^σ` is the `χ`-family member at the index `omegaProdEquiv.symm` of the
transported character: `ω_{ij}^σ = χ_{P_{ij}}` (`sigma_omega`).  This identifies the two `δ`-term
positions `P_{ij}, P_{ik}` in the `σ`-coefficient grid of (4.8). -/
theorem certainTypeOmegaSigma_eq_chiFam (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    [Fintype (ticVdiff h).W] [Invertible (Nat.card (ticVdiff h).W : ℂ)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1)) :
    certainTypeOmegaSigma h χ₂ i = (ticVdiff h).chiFam rfl (ticVdiffFullDadeApplication h)
      ((ticVdiff h).omegaProdEquiv.symm (omegaProdCharTic h χ₂ i)) :=
  (ticVdiff h).sigma_omega rfl (ticVdiffFullDadeApplication h) (omegaProdCharTic h χ₂ i)

omit [Invertible (Nat.card G : ℂ)] in
/-- **Peterfalvi (4.8), step (1)** (the sign equality `δ_j = δ_k`).  Fix a row `i` and two
columns `χ₂, χ₂'`.  If the certain-type characters `μ_{ij}` and `μ_{ik}` have equal degree at
`1`, then the two column signs coincide.

By the degree congruence (4.3.d), `μ_{ij}(1) ≡ δ_j` and `μ_{ik}(1) ≡ δ_k` modulo `w₁`, so the
equal-degree hypothesis forces `w₁ ∣ (δ_j − δ_k)`.  Since `δ_j, δ_k ∈ {±1}` and `w₁ ≥ 3`
(`W₁ ≠ 1` of odd order), the only multiple of `w₁` in `[-2, 2]` is `0`. -/
theorem certainType_sign_eq_of_degree_eq (h : Hypothesis46Core A L)
    [NeZero (Nat.card h.W1)] [Finite ↥(h.W1 ⊔ h.W2)]
    [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    (χ₂ χ₂' : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1))
    (hdeg : ((h.columnFamily χ₂).mu i : ClassFunction ↥L ℂ) 1
          = ((h.columnFamily χ₂').mu i : ClassFunction ↥L ℂ) 1) :
    (h.columnFamily χ₂).sign = (h.columnFamily χ₂').sign := by
  have : Fintype ↥(h.W1 ⊔ h.W2) := Fintype.ofFinite _
  obtain ⟨a, ha⟩ := h.certainType_degree_modEq χ₂ i
  obtain ⟨b, hb⟩ := h.certainType_degree_modEq χ₂' i
  have hw3 : 3 ≤ Nat.card h.W1 := h.sdiffTICyclicHypothesis.three_le_card_W1
  -- `δ_j + w₁·a = δ_k + w₁·b` in `ℤ`, transported from the `ℂ`-valued degree identity.
  have hZ : (h.columnFamily χ₂).sign + (Nat.card h.W1 : ℤ) * a
          = (h.columnFamily χ₂').sign + (Nat.card h.W1 : ℤ) * b := by
    have hC : ((h.columnFamily χ₂).sign : ℂ) + (Nat.card h.W1 : ℂ) * (a : ℂ)
            = ((h.columnFamily χ₂').sign : ℂ) + (Nat.card h.W1 : ℂ) * (b : ℂ) := by
      rw [← ha, ← hb]; exact hdeg
    exact_mod_cast hC
  -- Case split on the two signs.  Diagonal cases are reflexive; off-diagonal cases give
  -- `w₁ ∣ 2`, contradicting `w₁ ≥ 3`.
  rcases (h.columnFamily χ₂).sign_eq with hd | hd <;>
    rcases (h.columnFamily χ₂').sign_eq with hd' | hd' <;>
    rw [hd, hd'] at hZ ⊢ <;>
    first
    | rfl
    | (exfalso
       have hdvd : (Nat.card h.W1 : ℤ) ∣ 2 := ⟨b - a, by linear_combination hZ⟩
       have hle := Int.le_of_dvd (by norm_num) hdvd
       omega)
    | (exfalso
       have hdvd : (Nat.card h.W1 : ℤ) ∣ 2 := ⟨a - b, by linear_combination -hZ⟩
       have hle := Int.le_of_dvd (by norm_num) hdvd
       omega)

omit [Invertible (Nat.card G : ℂ)] in
omit [Invertible (Nat.card ↥L : ℂ)] in
/-- On `W₁`, the column character `ω_{ij} = chiColumn χ₂ i` is independent of the column `χ₂`:
the `W₂`-projection `wSnd` is trivial on `W₁` (`wSnd_eq_one_of_mem_W1`), so
`ω_{ij}(w) = (w1CharEquiv i)(wFst w)` for every column `χ₂`.  (Generalizes `chiColumn_one_apply`
— the `χ₂ = 1` column for all `w` — to every column, with the point restricted to `W₁`.) -/
theorem chiColumn_apply_of_mem_W1 (h : Hypothesis46Core A L) [NeZero (Nat.card h.W1)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1))
    {w : ↥h.sdiffTICyclicHypothesis.W}
    (hw : w ∈ h.sdiffTICyclicHypothesis.W1.subgroupOf h.sdiffTICyclicHypothesis.W) :
    (h.chiColumn χ₂ i : ClassFunction h.sdiffTICyclicHypothesis.W ℂ) w
      = ((h.w1CharEquiv i) (h.sdiffTICyclicHypothesis.wFst w) : ℂ) := by
  have hχ : χ₂ (h.sdiffTICyclicHypothesis.wSnd w) = 1 := by
    rw [h.sdiffTICyclicHypothesis.wSnd_eq_one_of_mem_W1 hw]; exact map_one χ₂
  have h1 : h.sdiffTICyclicHypothesis.omegaProdChar (h.w1CharEquiv i) χ₂ w
      = (h.w1CharEquiv i) (h.sdiffTICyclicHypothesis.wFst w)
        * χ₂ (h.sdiffTICyclicHypothesis.wSnd w) := rfl
  rw [Hypothesis.chiColumn, h.sdiffTICyclicHypothesis.omega_apply, h1, hχ, mul_one]

omit [Invertible (Nat.card G : ℂ)] in
/-- **Peterfalvi (4.8), step (2)** (agreement on `W₁`).  Two equal-degree certain-type characters
`μ_{ij}, μ_{ik}` (same row `i`, columns `χ₂, χ₂'`) agree on all of `W₁`, so `μ_{ij} − μ_{ik}`
vanishes there.

On `W₁^# ⊆ W − W₂` the (4.3.c) value identity gives `μ_{ij}(w) = δ_j·ω_{ij}(w)` and
`μ_{ik}(w) = δ_k·ω_{ik}(w)`; `δ_j = δ_k` (step (1), `certainType_sign_eq_of_degree_eq`) and the
column-independence of `ω` on `W₁` (`chiColumn_apply_of_mem_W1`) make these equal.  At `1` it is
the equal-degree hypothesis. -/
theorem certainType_apply_eq_of_mem_W1 (h : Hypothesis46Core A L)
    [NeZero (Nat.card h.W1)] [Finite ↥(h.W1 ⊔ h.W2)]
    [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    (χ₂ χ₂' : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1))
    (hdeg : ((h.columnFamily χ₂).mu i : ClassFunction ↥L ℂ) 1
          = ((h.columnFamily χ₂').mu i : ClassFunction ↥L ℂ) 1)
    {w : ↥L} (hw : w ∈ h.W1) :
    ((h.columnFamily χ₂).mu i : ClassFunction ↥L ℂ) w
      = ((h.columnFamily χ₂').mu i : ClassFunction ↥L ℂ) w := by
  have : Fintype ↥(h.W1 ⊔ h.W2) := Fintype.ofFinite _
  by_cases hw1 : w = 1
  · rw [hw1]; exact hdeg
  · -- `w ∈ W₁^# ⊆ sdiff.V = W − W₂`
    have hwV : w ∈ h.sdiffTICyclicHypothesis.V := by
      have hVdef : h.sdiffTICyclicHypothesis.V
          = ((h.W1 ⊔ h.W2 : Subgroup ↥L) : Set ↥L) \ (h.W2 : Set ↥L) := rfl
      rw [hVdef]
      refine ⟨(le_sup_left : h.W1 ≤ h.W1 ⊔ h.W2) hw, fun hw2 => hw1 ?_⟩
      exact Subgroup.mem_bot.mp (h.W_disjoint.le_bot (Subgroup.mem_inf.mpr ⟨hw, hw2⟩))
    -- the point `⟨w, _⟩` lies in `W₁` inside `sdiff.W`
    have hwsub : (⟨w, h.sdiffTICyclicHypothesis.V_subset_W hwV⟩ : ↥h.sdiffTICyclicHypothesis.W)
        ∈ h.sdiffTICyclicHypothesis.W1.subgroupOf h.sdiffTICyclicHypothesis.W :=
      Subgroup.mem_subgroupOf.mpr hw
    rw [h.certainType_apply_eq_of_mem_V χ₂ i hwV, h.certainType_apply_eq_of_mem_V χ₂' i hwV,
      certainType_sign_eq_of_degree_eq h χ₂ χ₂' i hdeg,
      chiColumn_apply_of_mem_W1 h χ₂ i hwsub, chiColumn_apply_of_mem_W1 h χ₂' i hwsub]

omit [Invertible (Nat.card G : ℂ)] in
/-- **Peterfalvi (4.8), conclusion (1)** (`Supp(μ_{ij} − μ_{ik}) ⊆ A₀`).  For nontrivial columns
`χ₂, χ₂' ≠ 1` and equal degree `μ_{ij}(1) = μ_{ik}(1)`, every point where `μ_{ij} − μ_{ik}` is
nonzero maps (via `L ↪ G`) into `A₀ = A ∪ V^L`.

Proof by cases on `z`:
* `z = 1`: the value is `μ_{ij}(1) − μ_{ik}(1) = 0` (equal degree), so this case is vacuous.
* `z ∈ K` (`z ≠ 1`): `μ_{ij}` and `μ_{ik}` restrict to `K` as `χ_j, χ_k` (`restrict_certainType_eq`,
  `coe_chiRestrict`), and (4.7) (`chiRestrict_apply_eq_zero_of_not_mem_union`) makes both vanish
  unless `L.subtype z ∈ A ∪ {1}`; with `z ≠ 1` this puts `L.subtype z ∈ A`.
* `z ∈ L − K`: by (2.1) (`mem_compl_conj_into_W`) `z` is `L`-conjugate to `x·y` with `x ∈ W₁^#`,
  `y ∈ W₂`; then `x·y ∈ W − W₂`, so its image lies in `tic.V = ↑W \ ↑W₂` (`tic_V`), and
  `L.subtype z` is an `L`-conjugate of it, i.e. lies in `V^L`. -/
theorem certainType_diff_supp_subset_A0 (h : Hypothesis46Core A L)
    [NeZero (Nat.card h.W1)] [Invertible (Nat.card ↥h.K : ℂ)]
    [Finite ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    {χ₂ χ₂' : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ} (hχ₂ : χ₂ ≠ 1) (hχ₂' : χ₂' ≠ 1)
    (i : Fin (Nat.card h.W1))
    (hdeg : ((h.columnFamily χ₂).mu i : ClassFunction ↥L ℂ) 1
          = ((h.columnFamily χ₂').mu i : ClassFunction ↥L ℂ) 1)
    {z : ↥L}
    (hz : (((h.columnFamily χ₂).mu i : ClassFunction ↥L ℂ)
          - ((h.columnFamily χ₂').mu i : ClassFunction ↥L ℂ)) z ≠ 0) :
    L.subtype z ∈ (A ∪ OddOrder.GroupTheory.conjClassSetIn L h.tic.V : Set G) := by
  have : Fintype ↥(h.W1 ⊔ h.W2) := Fintype.ofFinite _
  rw [ClassFunction.sub_apply, sub_ne_zero] at hz
  by_cases hz1 : z = 1
  · exact absurd (by rw [hz1]; exact hdeg) hz
  · by_cases hzK : z ∈ h.K
    · -- `z ∈ K`, `z ≠ 1`: land in `A`.
      left
      by_contra hzA
      have hsub1 : L.subtype z ≠ 1 := fun he => hz1 (L.subtype_injective (by simpa using he))
      have hnm : L.subtype z ∉ A ∪ ({1} : Set G) := by
        rintro (h' | h'); exacts [hzA h', hsub1 h']
      have hcoe : ∀ (ξ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ),
          ξ ≠ 1 → ((h.columnFamily ξ).mu i : ClassFunction ↥L ℂ) z = 0 := by
        intro ξ hξ
        have key := chiRestrict_apply_eq_zero_of_not_mem_union h hξ (g := ⟨z, hzK⟩) hnm
        rwa [h.coe_chiRestrict, ← h.restrict_certainType_eq ξ i,
          ClassFunction.restrict_apply] at key
      exact hz ((hcoe χ₂ hχ₂).trans (hcoe χ₂' hχ₂').symm)
    · -- `z ∈ L − K`: `z ~_L x·y` with `x ∈ W₁^#`, `y ∈ W₂`; moreover `y ≠ 1` (else `z ~ x ∈ W₁`,
      -- where the difference vanishes by step (2)), so `x·y ∈ V = W − (W₁ ∪ W₂)` and `z ∈ V^L`.
      right
      obtain ⟨c, x, hxW1, hx1, y, hyW2, hcxy⟩ :=
        (h.toHypothesis).mem_compl_conj_into_W hzK
      have hz_eq : z = c * (x * y) * c⁻¹ := by rw [← hcxy]; group
      -- `y ≠ 1`: otherwise `μ_{ij} − μ_{ik}` vanishes at `z` (the `W₁`-agreement, step (2)).
      have hy1 : y ≠ 1 := by
        intro hy1
        apply hz
        have hzx : z = c * x * c⁻¹ := by rw [hz_eq, hy1, mul_one]
        have hval : ∀ ξ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ,
            ((h.columnFamily ξ).mu i : ClassFunction ↥L ℂ) z
              = ((h.columnFamily ξ).mu i : ClassFunction ↥L ℂ) x := fun ξ => by
          rw [hzx]; exact ClassFunction.conj_eq _ x c
        rw [hval χ₂, hval χ₂']
        exact certainType_apply_eq_of_mem_W1 h χ₂ χ₂' i hdeg hxW1
      -- `tic.W = (W₁ ⊔ W₂).map L.subtype`.
      have htW : h.tic.W = (h.W1 ⊔ h.W2).map L.subtype := by
        rw [← h.tic.W_sup, h.tic_W1, h.tic_W2, ← Subgroup.map_sup]
      have hxyW : x * y ∈ (h.W1 ⊔ h.W2 : Subgroup ↥L) :=
        Subgroup.mul_mem _ (Subgroup.mem_sup_left hxW1) (Subgroup.mem_sup_right hyW2)
      have hvV : L.subtype (x * y) ∈ h.tic.V := by
        rw [h.tic_V]
        refine ⟨?_, ?_⟩
        · change L.subtype (x * y) ∈ h.tic.W
          rw [htW]; exact Subgroup.mem_map.mpr ⟨x * y, hxyW, rfl⟩
        · rintro (hmem | hmem)
          · -- `x·y ∈ W₁` would force `y = 1`.
            rw [h.tic_W1] at hmem
            obtain ⟨w, hwW1, hweq⟩ := Subgroup.mem_map.mp hmem
            have hwxy : w = x * y := L.subtype_injective hweq
            have hxyW1 : x * y ∈ h.W1 := hwxy ▸ hwW1
            have hyW1 : y ∈ h.W1 := by
              have hy_eq : y = x⁻¹ * (x * y) := by group
              rw [hy_eq]; exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hxW1) hxyW1
            have hybot : y ∈ h.W1 ⊓ h.W2 := ⟨hyW1, hyW2⟩
            rw [disjoint_iff.mp h.W_disjoint, Subgroup.mem_bot] at hybot
            exact hy1 hybot
          · -- `x·y ∈ W₂` would force `x = 1`.
            rw [h.tic_W2] at hmem
            obtain ⟨w, hwW2, hweq⟩ := Subgroup.mem_map.mp hmem
            have hwxy : w = x * y := L.subtype_injective hweq
            have hxyW2 : x * y ∈ h.W2 := hwxy ▸ hwW2
            have hxW2 : x ∈ h.W2 := by
              have hx_eq : x = (x * y) * y⁻¹ := by group
              rw [hx_eq]; exact Subgroup.mul_mem _ hxyW2 (Subgroup.inv_mem _ hyW2)
            have hxbot : x ∈ h.W1 ⊓ h.W2 := ⟨hxW1, hxW2⟩
            rw [disjoint_iff.mp h.W_disjoint, Subgroup.mem_bot] at hxbot
            exact hx1 hxbot
      exact ⟨L.subtype (x * y), hvV, L.subtype c, c.2, by rw [hz_eq]; simp [map_mul, map_inv]⟩

/-- `μ_{ij} − μ_{ik}` as an element of Peterfalvi's `CF(L, A₀)` (`SupportedClassFunctions` on
`A₀ = A ∪ V^L`), the domain element fed to the certain-type Dade isometry `τ`.  The support
condition is exactly conclusion (1) `certainType_diff_supp_subset_A0`. -/
noncomputable def certainTypeDiffSupported (h : Hypothesis46Core A L)
    [NeZero (Nat.card h.W1)] [Invertible (Nat.card ↥h.K : ℂ)]
    [Fintype ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    {χ₂ χ₂' : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ} (hχ₂ : χ₂ ≠ 1) (hχ₂' : χ₂' ≠ 1)
    (i : Fin (Nat.card h.W1))
    (hdeg : ((h.columnFamily χ₂).mu i : ClassFunction ↥L ℂ) 1
          = ((h.columnFamily χ₂').mu i : ClassFunction ↥L ℂ) 1) :
    OddOrder.Peterfalvi.S04.SupportedClassFunctions ℂ
      (A ∪ OddOrder.GroupTheory.conjClassSetIn L h.tic.V) L :=
  ⟨((h.columnFamily χ₂).mu i : ClassFunction ↥L ℂ)
      - ((h.columnFamily χ₂').mu i : ClassFunction ↥L ℂ), by
    rw [ClassFunction.mem_supportedSubmodule]
    intro z hz
    rw [ClassFunction.mem_support] at hz
    rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]
    exact certainType_diff_supp_subset_A0 h hχ₂ hχ₂' i hdeg hz⟩

/-- The certain-type Dade isometry `τ` (= `h.tau`) preserves values on its support `A₀`:
`τ(α)(a) = α(a)` for every `a ∈ A₀`.  Since `a = a · 1` and `1 ∈ H(a)`, the point `a` lies in its
own `H`-coset, so the general `map_eq_of_mem_hCoset` applies even though the certain-type `dade0`
need not have trivial local subgroups. -/
theorem tau_toDadeMap_apply_of_mem (h : Hypothesis46 A L)
    (α : OddOrder.Peterfalvi.S04.SupportedClassFunctions ℂ
      (A ∪ OddOrder.GroupTheory.conjClassSetIn L h.tic.V) L)
    {a : G} (ha : a ∈ (A ∪ OddOrder.GroupTheory.conjClassSetIn L h.tic.V : Set G)) :
    h.tau.toDadeMap α a = (α : ClassFunction ↥L ℂ) ⟨a, h.dade0.mem_L ha⟩ :=
  h.tau.toDadeIsometryData.isDadeMap.map_eq_of_mem_hCoset α ⟨a, ha⟩
    ⟨1, one_mem _, (mul_one _).symm⟩

/-- **Peterfalvi (4.8), step (4)** (the two sides agree on `V`).  For `v ∈ V = W − (W₁ ∪ W₂)`,
`(μ_{ij} − μ_{ik})^τ(v) = δ_j·(ω_{ij}^σ(v) − ω_{ik}^σ(v))`.

On `V` both maps are value-preserving: `τ` preserves values on `A₀ ⊇ V^L`
(`tau_toDadeMap_apply_of_mem`) and `σ_G` on `V` (`certainTypeOmegaSigma_apply_of_mem_V`).  Writing
`w = e v` for the `sdiff.W` partner of `v` (`ticWEquivSdiffW`), the (4.3.c) value identity gives
`μ_{ij}(w) = δ_j·ω_{ij}(w)`, `μ_{ik}(w) = δ_k·ω_{ik}(w)`, and `δ_j = δ_k` (step (1)) makes the two
sides coincide. -/
theorem certainType_diff_dade_apply_eq_of_mem_V (h : Hypothesis46 A L)
    [NeZero (Nat.card h.W1)] [Invertible (Nat.card ↥h.K : ℂ)]
    [Fintype ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    [Fintype (ticVdiff h).W] [Invertible (Nat.card (ticVdiff h).W : ℂ)]
    {χ₂ χ₂' : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ} (hχ₂ : χ₂ ≠ 1) (hχ₂' : χ₂' ≠ 1)
    (i : Fin (Nat.card h.W1))
    (hdeg : ((h.columnFamily χ₂).mu i : ClassFunction ↥L ℂ) 1
          = ((h.columnFamily χ₂').mu i : ClassFunction ↥L ℂ) 1)
    {v : G} (hv : v ∈ (ticVdiff h).V) :
    h.tau.toDadeMap (certainTypeDiffSupported h.toCore hχ₂ hχ₂' i hdeg) v
      = ((h.columnFamily χ₂).sign : ℂ)
        * (certainTypeOmegaSigma h χ₂ i v - certainTypeOmegaSigma h χ₂' i v) := by
  -- `v ∈ tic.V` (the same TI set), hence `v ∈ A₀`
  have hv_ticV : v ∈ h.tic.V := by rw [h.tic_V]; exact hv
  have hvA0 : v ∈ (A ∪ OddOrder.GroupTheory.conjClassSetIn L h.tic.V : Set G) :=
    Or.inr (OddOrder.GroupTheory.subset_conjClassSetIn hv_ticV)
  -- the `sdiff.W` partner `w = e v`, with `(w : L) = ⟨v, _⟩` and `(w : L) ∈ sdiff.V`
  set w : h.sdiffTICyclicHypothesis.W := ticWEquivSdiffW h ⟨v, (ticVdiff h).V_subset_W hv⟩ with hw
  have hwG : ((w : ↥L) : G) = v := coe_ticWEquivSdiffW h ⟨v, (ticVdiff h).V_subset_W hv⟩
  have hwL : (w : ↥L) = ⟨v, h.dade0.mem_L hvA0⟩ := Subtype.ext hwG
  have hwsdiffV : (w : ↥L) ∈ h.sdiffTICyclicHypothesis.V := by
    refine ⟨w.2, fun hW2 => ?_⟩
    have hvW2 : v ∈ h.tic.W2 := by
      rw [h.tic_W2]; exact ⟨(w : ↥L), hW2, hwG⟩
    exact hv.2 (Or.inr hvW2)
  -- the point `⟨(w:L), _⟩ : sdiff.W` is `w` itself
  have hwpt : (⟨(w : ↥L), h.sdiffTICyclicHypothesis.V_subset_W hwsdiffV⟩ :
      h.sdiffTICyclicHypothesis.W) = w := Subtype.ext rfl
  rw [tau_toDadeMap_apply_of_mem h _ hvA0]
  change (((h.columnFamily χ₂).mu i : ClassFunction ↥L ℂ)
      - ((h.columnFamily χ₂').mu i : ClassFunction ↥L ℂ)) ⟨v, h.dade0.mem_L hvA0⟩ = _
  rw [ClassFunction.sub_apply, ← hwL,
    h.certainType_apply_eq_of_mem_V χ₂ i hwsdiffV,
    h.certainType_apply_eq_of_mem_V χ₂' i hwsdiffV, hwpt,
    certainTypeOmegaSigma_apply_of_mem_V h χ₂ i hv,
    certainTypeOmegaSigma_apply_of_mem_V h χ₂' i hv,
    certainType_sign_eq_of_degree_eq h.toCore χ₂ χ₂' i hdeg]
  ring

/-- **Peterfalvi (4.8), step (5) input** (`‖φ‖² = 2`).  For distinct columns `χ₂ ≠ χ₂'`, the Dade
image `φ = (μ_{ij} − μ_{ik})^τ` is a virtual character of squared norm `2`: `τ` is an isometry
(`h.tau.inner_eq`), `μ_{ij}, μ_{ik}` are distinct irreducibles (`columnFamily_mu_ne`, (4.1)), so
`⟨φ, φ⟩ = ⟨μ_{ij} − μ_{ik}, μ_{ij} − μ_{ik}⟩ = 1 + 1 = 2`. -/
theorem certainType_diff_dade_inner_self (h : Hypothesis46 A L)
    [NeZero (Nat.card h.W1)] [Invertible (Nat.card ↥h.K : ℂ)]
    [Fintype ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    {χ₂ χ₂' : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ} (hχ : χ₂ ≠ χ₂')
    (hχ₂ : χ₂ ≠ 1) (hχ₂' : χ₂' ≠ 1) (i : Fin (Nat.card h.W1))
    (hdeg : ((h.columnFamily χ₂).mu i : ClassFunction ↥L ℂ) 1
          = ((h.columnFamily χ₂').mu i : ClassFunction ↥L ℂ) 1) :
    ClassFunction.inner (h.tau.toDadeMap (certainTypeDiffSupported h.toCore hχ₂ hχ₂' i hdeg))
        (h.tau.toDadeMap (certainTypeDiffSupported h.toCore hχ₂ hχ₂' i hdeg)) = 2 := by
  rw [h.tau.inner_eq]
  change ClassFunction.inner
      (((h.columnFamily χ₂).mu i : ClassFunction ↥L ℂ)
        - ((h.columnFamily χ₂').mu i : ClassFunction ↥L ℂ))
      (((h.columnFamily χ₂).mu i : ClassFunction ↥L ℂ)
        - ((h.columnFamily χ₂').mu i : ClassFunction ↥L ℂ)) = 2
  rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right, ClassFunction.inner_sub_right,
    irreducibleCharacter_inner_eq_ite, irreducibleCharacter_inner_eq_ite,
    irreducibleCharacter_inner_eq_ite, irreducibleCharacter_inner_eq_ite, if_pos rfl, if_pos rfl,
    if_neg (h.columnFamily_mu_ne hχ i i), if_neg (h.columnFamily_mu_ne hχ i i).symm]
  ring

set_option backward.isDefEq.respectTransparency false in
/-- **Peterfalvi (4.8), step (6) input** (`NC(φ) ≤ 2`).  The Dade image `φ = (μ_{ij} − μ_{ik})^τ`,
of squared norm `2`, has at most two nonzero `σ`-image coefficients. By
`mem_ZIrr_inner_self_eq_sum_sq`
+ `exists_pair_of_sum_sq_eq_two` it is `ε_α·α + ε_β·β` for two distinct irreducibles `α, β`; each of
`α, β` has `≤ 1` nonzero inner product against the orthonormal `χ`-family
(`ncard_inner_chiFam_ne_zero_le_one`), and `Supp(φ-coeffs) ⊆ S_α ∪ S_β`. -/
theorem sigmaNC_dade_le_two (h : Hypothesis46 A L)
    [NeZero (Nat.card h.W1)] [Invertible (Nat.card ↥h.K : ℂ)]
    [Fintype ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    [Fintype (ticVdiff h).W] [Invertible (Nat.card (ticVdiff h).W : ℂ)]
    {χ₂ χ₂' : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ} (hχ : χ₂ ≠ χ₂')
    (hχ₂ : χ₂ ≠ 1) (hχ₂' : χ₂' ≠ 1) (i : Fin (Nat.card h.W1))
    (hdeg : ((h.columnFamily χ₂).mu i : ClassFunction ↥L ℂ) 1
          = ((h.columnFamily χ₂').mu i : ClassFunction ↥L ℂ) 1) :
    (ticVdiff h).sigmaNC rfl (ticVdiffFullDadeApplication h)
        (h.tau.toDadeMap (certainTypeDiffSupported h.toCore hχ₂ hχ₂' i hdeg)) ≤ 2 := by
  set φ := h.tau.toDadeMap (certainTypeDiffSupported h.toCore hχ₂ hχ₂' i hdeg) with hφdef
  have hφZ : φ ∈ ZIrr G := h.tau.maps_virtualCharacter _
    ((ZIrr (↥L)).sub_mem ((h.columnFamily χ₂).mu i).mem_ZIrr
      ((h.columnFamily χ₂').mu i).mem_ZIrr)
  have hφ2 : ClassFunction.inner φ φ = 2 := certainType_diff_dade_inner_self h hχ hχ₂ hχ₂' i hdeg
  rw [OddOrder.Peterfalvi.S05.TICyclicHypothesis.sigmaNC]
  exact (ticVdiff h).ncard_sigmaCoeff_ne_zero_le_two rfl (ticVdiffFullDadeApplication h) hφZ hφ2

/-- **Peterfalvi (4.8), step (7) input** (the `σ`-coefficients of `φ` lie in `{0, ±1}`).  Writing
`φ = ε_α·α + ε_β·β` (norm-2 ⟹ two constituents) and `χ_{pq} = ε·ν` (norm-1 classifier), the
coefficient `⟨φ, χ_{pq}⟩` is `ε_α·ε` if `ν = α`, `ε_β·ε` if `ν = β`, and `0` otherwise (`α ≠ β`).
This `|·| ≤ 1` bound (beyond `NC ≤ 2`) is what excludes the `w₂ = 3` row case in the trichotomy
endgame, where a coefficient would otherwise be `±2`. -/
theorem sigmaCoeff_dade_eq_zero_or_one (h : Hypothesis46 A L)
    [NeZero (Nat.card h.W1)] [Invertible (Nat.card ↥h.K : ℂ)]
    [Fintype ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    [Fintype (ticVdiff h).W] [Invertible (Nat.card (ticVdiff h).W : ℂ)]
    {χ₂ χ₂' : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ} (hχ : χ₂ ≠ χ₂')
    (hχ₂ : χ₂ ≠ 1) (hχ₂' : χ₂' ≠ 1) (i : Fin (Nat.card h.W1))
    (hdeg : ((h.columnFamily χ₂).mu i : ClassFunction ↥L ℂ) 1
          = ((h.columnFamily χ₂').mu i : ClassFunction ↥L ℂ) 1)
    (pq : ((ticVdiff h).W1.subgroupOf (ticVdiff h).W →* ℂˣ) ×
        ((ticVdiff h).W2.subgroupOf (ticVdiff h).W →* ℂˣ)) :
    (ticVdiff h).sigmaCoeff rfl (ticVdiffFullDadeApplication h)
        (h.tau.toDadeMap (certainTypeDiffSupported h.toCore hχ₂ hχ₂' i hdeg)) pq = 0 ∨
      (ticVdiff h).sigmaCoeff rfl (ticVdiffFullDadeApplication h)
        (h.tau.toDadeMap (certainTypeDiffSupported h.toCore hχ₂ hχ₂' i hdeg)) pq = 1 ∨
      (ticVdiff h).sigmaCoeff rfl (ticVdiffFullDadeApplication h)
        (h.tau.toDadeMap (certainTypeDiffSupported h.toCore hχ₂ hχ₂' i hdeg)) pq = -1 := by
  set φ := h.tau.toDadeMap (certainTypeDiffSupported h.toCore hχ₂ hχ₂' i hdeg) with hφdef
  have hφZ : φ ∈ ZIrr G := h.tau.maps_virtualCharacter _
    ((ZIrr (↥L)).sub_mem ((h.columnFamily χ₂).mu i).mem_ZIrr
      ((h.columnFamily χ₂').mu i).mem_ZIrr)
  have hφ2 : ClassFunction.inner φ φ = 2 := certainType_diff_dade_inner_self h hχ hχ₂ hχ₂' i hdeg
  exact (ticVdiff h).sigmaCoeff_eq_zero_or_one_of_inner_self_two rfl
    (ticVdiffFullDadeApplication h) hφZ hφ2 pq

open scoped Classical in
/-- The `σ`-coefficient grid of `ψ = φ − δ_j·(ω_{ij}^σ − ω_{ik}^σ)`.  As `ω_{ij}^σ = χ_{P_{ij}}`
(`certainTypeOmegaSigma_eq_chiFam`) and the `χ`-family is orthonormal, the `δ`-part contributes
`∓δ_j` exactly at the two grid positions `P_{ij}, P_{ik}`:
`a(pq) = ⟨φ, χ_{pq}⟩ − δ_j·([P_{ij} = pq] − [P_{ik} = pq])`. -/
theorem sigmaCoeff_psi_eq (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    [Finite ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    [Fintype (ticVdiff h).W] [Invertible (Nat.card (ticVdiff h).W : ℂ)]
    (χ₂ χ₂' : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1))
    (φ : ClassFunction G ℂ)
    (pq : ((ticVdiff h).W1.subgroupOf (ticVdiff h).W →* ℂˣ) ×
        ((ticVdiff h).W2.subgroupOf (ticVdiff h).W →* ℂˣ)) :
    (ticVdiff h).sigmaCoeff rfl (ticVdiffFullDadeApplication h)
        (φ - (h.columnFamily χ₂).sign •
          (certainTypeOmegaSigma h χ₂ i - certainTypeOmegaSigma h χ₂' i)) pq
      = (ticVdiff h).sigmaCoeff rfl (ticVdiffFullDadeApplication h) φ pq
        - ((h.columnFamily χ₂).sign : ℂ)
          * ((if (ticVdiff h).omegaProdEquiv.symm (omegaProdCharTic h χ₂ i) = pq then (1 : ℂ) else
              0)
            - (if (ticVdiff h).omegaProdEquiv.symm (omegaProdCharTic h χ₂' i) = pq
                then (1 : ℂ) else 0)) := by
  have : Fintype ↥(h.W1 ⊔ h.W2) := Fintype.ofFinite _
  simp only [OddOrder.Peterfalvi.S05.TICyclicHypothesis.sigmaCoeff]
  rw [certainTypeOmegaSigma_eq_chiFam, certainTypeOmegaSigma_eq_chiFam,
    ClassFunction.inner_sub_left, ← Int.cast_smul_eq_zsmul ℂ (h.columnFamily χ₂).sign,
    ClassFunction.inner_smul_left, ClassFunction.inner_sub_left,
    ((ticVdiff h).chiFam_spec rfl (ticVdiffFullDadeApplication h)).2.2.1,
    ((ticVdiff h).chiFam_spec rfl (ticVdiffFullDadeApplication h)).2.2.1]

/-- For distinct columns `χ₂ ≠ χ₂'`, the transported `tic`-side characters are distinct:
`omegaProdCharTic` is injective in the column.  (Precompose-cancel the bridge iso `e`, then
`omegaProdChar_inj`.) -/
theorem omegaProdCharTic_ne (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    {χ₂ χ₂' : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ} (hχ : χ₂ ≠ χ₂') (i : Fin (Nat.card h.W1)) :
    omegaProdCharTic h χ₂ i ≠ omegaProdCharTic h χ₂' i := by
  intro heq
  refine hχ (h.sdiffTICyclicHypothesis.omegaProdChar_inj (χ₁ := h.w1CharEquiv i)
    (χ₁' := h.w1CharEquiv i) (MonoidHom.ext fun w => ?_)).2
  obtain ⟨w', rfl⟩ := (ticWEquivSdiffW h).surjective w
  exact DFunLike.congr_fun heq w'

/-- The two `σ`-image grid indices are distinct: `P_{ij} ≠ P_{ik}` for `χ₂ ≠ χ₂'`
(`omegaProdEquiv.symm` is injective and `omegaProdCharTic` is column-injective). -/
theorem omegaProdEquiv_symm_omegaProdCharTic_ne (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    {χ₂ χ₂' : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ} (hχ : χ₂ ≠ χ₂') (i : Fin (Nat.card h.W1)) :
    (ticVdiff h).omegaProdEquiv.symm (omegaProdCharTic h χ₂ i)
      ≠ (ticVdiff h).omegaProdEquiv.symm (omegaProdCharTic h χ₂' i) :=
  fun heq => omegaProdCharTic_ne h hχ i ((ticVdiff h).omegaProdEquiv.symm.injective heq)

/-- **Peterfalvi (4.8), conclusion (3) from case (a).**  If every `σ`-coefficient of
`ψ = (μ_{ij} − μ_{ik})^τ − δ_j(ω_{ij}^σ − ω_{ik}^σ)` vanishes, then `ψ = 0`, i.e.
`(μ_{ij} − μ_{ik})^τ = δ_j(ω_{ij}^σ − ω_{ik}^σ)`.

`⟨ψ, ω_{ij}^σ⟩ = ⟨ψ, χ_{P_{ij}}⟩ = 0` (hypothesis) and the (4.8.1)-expansion `sigmaCoeff_psi_eq`
pin `⟨φ, ω_{ij}^σ⟩ = δ_j`, `⟨φ, ω_{ik}^σ⟩ = −δ_j` (with `P_{ij} ≠ P_{ik}`); then
`‖ψ‖² = ⟨ψ, φ⟩ = ‖φ‖² − δ_j·2δ_j = 2 − 2 = 0` (`‖φ‖² = 2`, `χ`-orthonormality), so `ψ = 0`. -/
theorem certainType_diff_dade_eq_of_all_sigmaCoeff_zero (h : Hypothesis46 A L)
    [NeZero (Nat.card h.W1)] [Invertible (Nat.card ↥h.K : ℂ)]
    [Fintype ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    [Fintype (ticVdiff h).W] [Invertible (Nat.card (ticVdiff h).W : ℂ)]
    {χ₂ χ₂' : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ} (hχ : χ₂ ≠ χ₂')
    (hχ₂ : χ₂ ≠ 1) (hχ₂' : χ₂' ≠ 1) (i : Fin (Nat.card h.W1))
    (hdeg : ((h.columnFamily χ₂).mu i : ClassFunction ↥L ℂ) 1
          = ((h.columnFamily χ₂').mu i : ClassFunction ↥L ℂ) 1)
    (hall : ∀ pq, (ticVdiff h).sigmaCoeff rfl (ticVdiffFullDadeApplication h)
        (h.tau.toDadeMap (certainTypeDiffSupported h.toCore hχ₂ hχ₂' i hdeg)
          - (h.columnFamily χ₂).sign •
            (certainTypeOmegaSigma h χ₂ i - certainTypeOmegaSigma h χ₂' i)) pq = 0) :
    h.tau.toDadeMap (certainTypeDiffSupported h.toCore hχ₂ hχ₂' i hdeg)
      = (h.columnFamily χ₂).sign
        • (certainTypeOmegaSigma h χ₂ i - certainTypeOmegaSigma h χ₂' i) := by
  classical
  set φ := h.tau.toDadeMap (certainTypeDiffSupported h.toCore hχ₂ hχ₂' i hdeg) with hφ
  set ωij := certainTypeOmegaSigma h χ₂ i with hωij
  set ωik := certainTypeOmegaSigma h χ₂' i with hωik
  set s : ℤ := (h.columnFamily χ₂).sign with hsdef
  set ψ := φ - s • (ωij - ωik) with hψ
  set Pij := (ticVdiff h).omegaProdEquiv.symm (omegaProdCharTic h χ₂ i) with hPij
  set Pik := (ticVdiff h).omegaProdEquiv.symm (omegaProdCharTic h χ₂' i) with hPik
  have hPne : Pij ≠ Pik := omegaProdEquiv_symm_omegaProdCharTic_ne h hχ i
  have hωijeq : ωij = (ticVdiff h).chiFam rfl (ticVdiffFullDadeApplication h) Pij :=
    certainTypeOmegaSigma_eq_chiFam h χ₂ i
  have hωikeq : ωik = (ticVdiff h).chiFam rfl (ticVdiffFullDadeApplication h) Pik :=
    certainTypeOmegaSigma_eq_chiFam h χ₂' i
  -- `⟨φ, ω_ij^σ⟩ = s`, `⟨φ, ω_ik^σ⟩ = −s` from `hall` + the expansion
  have hcij : ClassFunction.inner φ ωij = (s : ℂ) := by
    have he := hall Pij
    rw [sigmaCoeff_psi_eq, if_pos rfl, if_neg (Ne.symm hPne)] at he
    rw [hωijeq]; change (ticVdiff h).sigmaCoeff rfl (ticVdiffFullDadeApplication h) φ Pij = _
    linear_combination he
  have hcik : ClassFunction.inner φ ωik = -(s : ℂ) := by
    have he := hall Pik
    rw [sigmaCoeff_psi_eq, if_neg hPne, if_pos rfl] at he
    rw [hωikeq]; change (ticVdiff h).sigmaCoeff rfl (ticVdiffFullDadeApplication h) φ Pik = _
    linear_combination he
  -- orthonormality of `ω_ij^σ, ω_ik^σ` and `‖φ‖² = 2`
  have hnorm : ClassFunction.inner φ φ = 2 := certainType_diff_dade_inner_self h hχ hχ₂ hχ₂' i hdeg
  have hii : ClassFunction.inner ωij ωij = 1 := by
    rw [hωijeq, ((ticVdiff h).chiFam_spec rfl (ticVdiffFullDadeApplication h)).2.2.1, if_pos rfl]
  have hkk : ClassFunction.inner ωik ωik = 1 := by
    rw [hωikeq, ((ticVdiff h).chiFam_spec rfl (ticVdiffFullDadeApplication h)).2.2.1, if_pos rfl]
  have hik : ClassFunction.inner ωij ωik = 0 := by
    rw [hωijeq, hωikeq, ((ticVdiff h).chiFam_spec rfl (ticVdiffFullDadeApplication h)).2.2.1,
      if_neg hPne]
  have hki : ClassFunction.inner ωik ωij = 0 := by
    rw [hωikeq, hωijeq, ((ticVdiff h).chiFam_spec rfl (ticVdiffFullDadeApplication h)).2.2.1,
      if_neg (Ne.symm hPne)]
  -- conjugate-symmetric partners `⟨ω_ij^σ, φ⟩ = s`, `⟨ω_ik^σ, φ⟩ = −s`
  have hcji : ClassFunction.inner ωij φ = (s : ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hcij, star_intCast]
  have hcki : ClassFunction.inner ωik φ = -(s : ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hcik, star_neg, star_intCast]
  -- `s² = 1`
  have hsq : (s : ℂ) * (s : ℂ) = 1 := by
    rcases (h.columnFamily χ₂).sign_eq with hsv | hsv <;> rw [hsdef, hsv] <;> norm_num
  -- `⟨ψ, ψ⟩ = 0`
  have hself : ClassFunction.inner ψ ψ = 0 := by
    rw [hψ]
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ← Int.cast_smul_eq_zsmul ℂ s, ClassFunction.inner_smul_left,
      OddOrder.RepresentationTheory.inner_smul_right, hnorm, hcij, hcik, hcji, hcki, hii, hkk,
      hik, hki, star_intCast]
    linear_combination (-2 : ℂ) * hsq
  have := eq_zero_of_inner_self_re_eq_zero (G := G) (φ := ψ) (by rw [hself]; simp)
  rw [hψ, sub_eq_zero] at this
  exact this

/-- **Peterfalvi (4.8), conclusion (3)** (the FT-critical isometry identity).  For nontrivial
distinct columns `χ₂ ≠ χ₂'` and equal degree `μ_{ij}(1) = μ_{ik}(1)`, the Dade image is
`(μ_{ij} − μ_{ik})^τ = δ_j·(ω_{ij}^σ − ω_{ik}^σ)`.

`ψ := (μ_{ij} − μ_{ik})^τ − δ_j(ω_{ij}^σ − ω_{ik}^σ)` vanishes on `V` (step (4)), so its
`σ`-coefficient
grid is additively separable (3.7) with `NC(ψ) ≤ 4 < 2·min(w₁, w₂)`.  As `w₁, w₂` are coprime odd
(`≥ 3`), one of `w₁ + 2 ≤ w₂`, `w₂ + 2 ≤ w₁` holds; the (3.8) trichotomy `grid_trichotomy` (in that
orientation) leaves all-zero, a constant column, or a constant row.  The latter two are impossible
(`grid_no_constant_column` on the grid resp. its transpose), so all `σ`-coefficients vanish and
`certainType_diff_dade_eq_of_all_sigmaCoeff_zero` gives `ψ = 0`. -/
theorem certainType_diff_dade_eq (h : Hypothesis46 A L)
    [NeZero (Nat.card h.W1)] [Invertible (Nat.card ↥h.K : ℂ)]
    [Fintype ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    [Fintype (ticVdiff h).W] [Invertible (Nat.card (ticVdiff h).W : ℂ)]
    {χ₂ χ₂' : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ} (hχ : χ₂ ≠ χ₂')
    (hχ₂ : χ₂ ≠ 1) (hχ₂' : χ₂' ≠ 1) (i : Fin (Nat.card h.W1))
    (hdeg : ((h.columnFamily χ₂).mu i : ClassFunction ↥L ℂ) 1
          = ((h.columnFamily χ₂').mu i : ClassFunction ↥L ℂ) 1) :
    h.tau.toDadeMap (certainTypeDiffSupported h.toCore hχ₂ hχ₂' i hdeg)
      = (h.columnFamily χ₂).sign
        • (certainTypeOmegaSigma h χ₂ i - certainTypeOmegaSigma h χ₂' i) := by
  classical
  have : Finite G := Finite.of_fintype G
  have : Fintype ((ticVdiff h).W1.subgroupOf (ticVdiff h).W →* ℂˣ) := Fintype.ofFinite _
  have : Fintype ((ticVdiff h).W2.subgroupOf (ticVdiff h).W →* ℂˣ) := Fintype.ofFinite _
  have : Finite (((ticVdiff h).W1.subgroupOf (ticVdiff h).W →* ℂˣ) ×
    ((ticVdiff h).W2.subgroupOf (ticVdiff h).W →* ℂˣ)) := Finite.of_fintype _
  apply certainType_diff_dade_eq_of_all_sigmaCoeff_zero h hχ hχ₂ hχ₂' i hdeg
  set φ := h.tau.toDadeMap (certainTypeDiffSupported h.toCore hχ₂ hχ₂' i hdeg) with hφ
  set ψ := φ - (h.columnFamily χ₂).sign •
    (certainTypeOmegaSigma h χ₂ i - certainTypeOmegaSigma h χ₂' i) with hψ
  set a : ((ticVdiff h).W1.subgroupOf (ticVdiff h).W →* ℂˣ) ×
      ((ticVdiff h).W2.subgroupOf (ticVdiff h).W →* ℂˣ) → ℂ :=
    fun pq => (ticVdiff h).sigmaCoeff rfl (ticVdiffFullDadeApplication h) ψ pq with ha
  set G : ((ticVdiff h).W1.subgroupOf (ticVdiff h).W →* ℂˣ) ×
      ((ticVdiff h).W2.subgroupOf (ticVdiff h).W →* ℂˣ) → ℂ :=
    fun pq => (ticVdiff h).sigmaCoeff rfl (ticVdiffFullDadeApplication h) φ pq with hG
  set Pij := (ticVdiff h).omegaProdEquiv.symm (omegaProdCharTic h χ₂ i) with hPij
  set Pik := (ticVdiff h).omegaProdEquiv.symm (omegaProdCharTic h χ₂' i) with hPik
  have hPne : Pij ≠ Pik := omegaProdEquiv_symm_omegaProdCharTic_ne h hχ i
  have hae : ∀ pq, a pq = G pq - ((h.columnFamily χ₂).sign : ℂ)
      * ((if Pij = pq then (1 : ℂ) else 0) - (if Pik = pq then (1 : ℂ) else 0)) :=
    fun pq => sigmaCoeff_psi_eq h χ₂ χ₂' i φ pq
  have hG2 : {x | G x ≠ 0}.ncard ≤ 2 := sigmaNC_dade_le_two h hχ hχ₂ hχ₂' i hdeg
  have hG01 : ∀ x, G x = 0 ∨ G x = 1 ∨ G x = -1 :=
    fun x => sigmaCoeff_dade_eq_zero_or_one h hχ hχ₂ hχ₂' i hdeg x
  have hs : ((h.columnFamily χ₂).sign : ℂ) = 1 ∨ ((h.columnFamily χ₂).sign : ℂ) = -1 := by
    rcases (h.columnFamily χ₂).sign_eq with h1 | h1 <;> rw [h1] <;> norm_num
  -- ψ vanishes on V (step 4)
  have hψV : ∀ v ∈ (ticVdiff h).V, ψ v = 0 := by
    intro v hv
    rw [hψ, ClassFunction.sub_apply, ClassFunction.zsmul_apply, ClassFunction.sub_apply,
      certainType_diff_dade_apply_eq_of_mem_V h hχ₂ hχ₂' i hdeg hv, zsmul_eq_mul]
    ring
  -- additive separability of `a` (3.7)
  have hadd : ∀ p p' q q', a (p, q) + a (p', q') = a (p, q') + a (p', q) :=
    fun p p' q q' =>
      (ticVdiff h).sigmaCoeff_add_eq rfl (ticVdiffFullDadeApplication h) hψV p p' q q'
  -- `NC(ψ) ≤ 4`
  have hNC4 : {x | a x ≠ 0}.ncard ≤ 4 := by
    have hsub : {x | a x ≠ 0} ⊆ {x | G x ≠ 0} ∪ {Pij, Pik} := by
      intro x hx
      by_contra hcon
      simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff,
        not_or, not_not] at hcon
      exact hx (by rw [hae x, hcon.1, if_neg (Ne.symm hcon.2.1), if_neg (Ne.symm hcon.2.2)]; ring)
    have hbpair : ({Pij, Pik} : Set _).ncard ≤ 2 :=
      (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])
    calc {x | a x ≠ 0}.ncard ≤ ({x | G x ≠ 0} ∪ {Pij, Pik}).ncard :=
          Set.ncard_le_ncard hsub (Set.finite_univ.subset (Set.subset_univ _))
      _ ≤ {x | G x ≠ 0}.ncard + ({Pij, Pik} : Set _).ncard := Set.ncard_union_le _ _
      _ ≤ 2 + 2 := add_le_add hG2 hbpair
      _ = 4 := rfl
  -- card facts: `card Ŵ₁ = w₁`, `card Ŵ₂ = w₂`, both `≥ 3`, coprime, odd ⟹ a gap holds
  have hcard1 : Nat.card ((ticVdiff h).W1.subgroupOf (ticVdiff h).W →* ℂˣ) = Nat.card h.tic.W1 :=
    (ticVdiff h).card_charGroup_subgroupOf (ticVdiff h).W1_le_W
  have hcard2 : Nat.card ((ticVdiff h).W2.subgroupOf (ticVdiff h).W →* ℂˣ) = Nat.card h.tic.W2 :=
    (ticVdiff h).card_charGroup_subgroupOf (ticVdiff h).W2_le_W
  have h3w1 : 3 ≤ Nat.card h.tic.W1 := h.tic.three_le_card_W1
  have h3w2 : 3 ≤ Nat.card h.tic.W2 := h.tic.three_le_card_W2
  have hodd1 : Odd (Nat.card h.tic.W1) :=
    h.tic.W_card_odd.of_dvd_nat (Subgroup.card_dvd_of_le h.tic.W1_le_W)
  have hodd2 : Odd (Nat.card h.tic.W2) :=
    h.tic.W_card_odd.of_dvd_nat (Subgroup.card_dvd_of_le h.tic.W2_le_W)
  have hcop : Nat.Coprime (Nat.card h.tic.W1) (Nat.card h.tic.W2) := h.tic.W_card_coprime
  have hwne : Nat.card h.tic.W1 ≠ Nat.card h.tic.W2 := by
    intro he; rw [he, Nat.Coprime, Nat.gcd_self] at hcop; omega
  -- orientation: put the smaller character group as the trichotomy's rows
  rcases lt_or_gt_of_ne hwne with hlt | hgt
  · -- `w₁ < w₂`: gap `card Ŵ₁ + 2 ≤ card Ŵ₂`, run `grid_trichotomy` on `a`
    have hgap : Nat.card ((ticVdiff h).W1.subgroupOf (ticVdiff h).W →* ℂˣ) + 2
        ≤ Nat.card ((ticVdiff h).W2.subgroupOf (ticVdiff h).W →* ℂˣ) := by
      rw [hcard1, hcard2]; obtain ⟨k1, hk1⟩ := hodd1; obtain ⟨k2, hk2⟩ := hodd2; omega
    have hNClt : {x | a x ≠ 0}.ncard
        < 2 * Nat.card ((ticVdiff h).W1.subgroupOf (ticVdiff h).W →* ℂˣ) := by
      rw [hcard1]; omega
    rcases OddOrder.Peterfalvi.S05.grid_trichotomy a hadd hgap hNClt with
      hz | ⟨j₀, c, hc, h1, h2⟩ | ⟨i₀, c, hc, h1, h2⟩
    · exact hz
    · exact (OddOrder.Peterfalvi.S05.grid_no_constant_column
        (by rw [← Nat.card_eq_fintype_card, hcard1]; exact h3w1) G hG2 hG01 Pij Pik hPne hs a hae
        hc h1 h2).elim
    · exact (OddOrder.Peterfalvi.S05.grid_no_constant_row
        (by rw [← Nat.card_eq_fintype_card, hcard2]; exact h3w2) G hG2 hG01 Pij Pik hPne hs a hae
        hc h1 h2).elim
  · -- `w₂ < w₁`: transpose the grid so `Ŵ₂` is the rows
    set aT : ((ticVdiff h).W2.subgroupOf (ticVdiff h).W →* ℂˣ) ×
        ((ticVdiff h).W1.subgroupOf (ticVdiff h).W →* ℂˣ) → ℂ := fun x => a (x.2, x.1) with haT
    have hgap : Nat.card ((ticVdiff h).W2.subgroupOf (ticVdiff h).W →* ℂˣ) + 2
        ≤ Nat.card ((ticVdiff h).W1.subgroupOf (ticVdiff h).W →* ℂˣ) := by
      rw [hcard1, hcard2]; obtain ⟨k1, hk1⟩ := hodd1; obtain ⟨k2, hk2⟩ := hodd2; omega
    have haddT : ∀ q q' p p', aT (q, p) + aT (q', p') = aT (q, p') + aT (q', p) :=
      fun q q' p p' => by simp only [haT]; linear_combination hadd p p' q q'
    have hNCltT : {x | aT x ≠ 0}.ncard
        < 2 * Nat.card ((ticVdiff h).W2.subgroupOf (ticVdiff h).W →* ℂˣ) := by
      have h4 : {x | aT x ≠ 0}.ncard ≤ 4 :=
        le_trans (Set.ncard_le_ncard_of_injOn Prod.swap (fun x hx => hx)
          (Prod.swap_injective.injOn) (Set.toFinite _)) hNC4
      rw [hcard2]; omega
    rcases OddOrder.Peterfalvi.S05.grid_trichotomy aT haddT hgap hNCltT with
      hz | ⟨p₀, c, hc, h1, h2⟩ | ⟨q₀, c, hc, h1, h2⟩
    · intro pq; exact hz (pq.2, pq.1)
    · exact (OddOrder.Peterfalvi.S05.grid_no_constant_row
        (by rw [← Nat.card_eq_fintype_card, hcard2]; exact h3w2) G hG2 hG01 Pij Pik hPne hs a hae
        hc (fun q => h1 q) (fun i j hi => h2 j i hi)).elim
    · exact (OddOrder.Peterfalvi.S05.grid_no_constant_column
        (by rw [← Nat.card_eq_fintype_card, hcard1]; exact h3w1) G hG2 hG01 Pij Pik hPne hs a hae
        hc (fun p => h1 p) (fun i j hj => h2 j i hj)).elim

/-- The certain-type Dade isometry `τ` (= `h.tau`) is additive over finite sums of supported class
functions.  The abstract `h.tau.toDadeMap` agrees with the *constructed* Dade map
`h.dade0.dadeMap` by the Peterfalvi (2.5) uniqueness `IsDadeMap.unique`, and the latter is the
genuine `ℂ`-linear `dadeLinearMap`, hence commutes with `∑`. -/
theorem tau_toDadeMap_sum (h : Hypothesis46 A L) {ι : Type*} (s : Finset ι)
    (α : ι → OddOrder.Peterfalvi.S04.SupportedClassFunctions ℂ
      (A ∪ OddOrder.GroupTheory.conjClassSetIn L h.tic.V) L) :
    h.tau.toDadeMap (∑ i ∈ s, α i) = ∑ i ∈ s, h.tau.toDadeMap (α i) := by
  have hkey : h.tau.toDadeMap = h.dade0.dadeMap (k := ℂ) :=
    OddOrder.Peterfalvi.S04.IsDadeMap.unique
      h.tau.toDadeIsometryData.isDadeMap h.dade0.isDadeMap_dadeMap
  rw [hkey]
  simpa only [OddOrder.Peterfalvi.S04.Hypothesis.dadeLinearMap_apply]
    using map_sum (h.dade0.dadeLinearMap (k := ℂ)) α s

/-- **Peterfalvi (4.9)(b), the summed isometry identity.**  Summing the per-row isometry (4.8)
conclusion 3 (`certainType_diff_dade_eq`) over `0 ≤ i < w₁`:
`(μ_j − μ_k)^τ = δ_j ∑_i (ω_{ij}^σ − ω_{ik}^σ)`, where `μ_j − μ_k = ∑_i (μ_{ij} − μ_{ik})` is
`∑ i, certainTypeDiffSupported`.  Together with `δ_j = δ_k` (conclusion 2) this is the (4.9)(b)
agreement of the column map with `τ` on `Z[T, A]`.  Stated with the per-row degree equalities
`μ_{ij}(1) = μ_{ik}(1)` (which, since every `μ_{ij}` in column `j` has degree `μ_{0j}(1)`, follow
from the column-degree equality `μ_j(1) = μ_k(1)`). -/
theorem certainType_diff_dade_sum_eq (h : Hypothesis46 A L)
    [NeZero (Nat.card h.W1)] [Invertible (Nat.card ↥h.K : ℂ)]
    [Fintype ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    [Fintype (ticVdiff h).W] [Invertible (Nat.card (ticVdiff h).W : ℂ)]
    {χ₂ χ₂' : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ} (hχ : χ₂ ≠ χ₂')
    (hχ₂ : χ₂ ≠ 1) (hχ₂' : χ₂' ≠ 1)
    (hdeg : ∀ i, ((h.columnFamily χ₂).mu i : ClassFunction ↥L ℂ) 1
                = ((h.columnFamily χ₂').mu i : ClassFunction ↥L ℂ) 1) :
    h.tau.toDadeMap (∑ i, certainTypeDiffSupported h.toCore hχ₂ hχ₂' i (hdeg i))
      = (h.columnFamily χ₂).sign •
          ∑ i, (certainTypeOmegaSigma h χ₂ i - certainTypeOmegaSigma h χ₂' i) := by
  rw [tau_toDadeMap_sum, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => certainType_diff_dade_eq h hχ hχ₂ hχ₂' i (hdeg i)

/-- **Column-degree constancy.**  Every `μ_{ij}` in column `j` has degree `μ_{0j}(1)`
(`columnFamily_difference_apply_one`: `(μ_{ij} − μ_{0j})(1) = 0`). -/
theorem columnFamily_mu_apply_one_eq (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    [Finite ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1)) :
    ((h.columnFamily χ₂).mu i : ClassFunction ↥L ℂ) 1
      = ((h.columnFamily χ₂).mu 0 : ClassFunction ↥L ℂ) 1 := by
  have : Fintype ↥(h.W1 ⊔ h.W2) := Fintype.ofFinite _
  have h0 := h.columnFamily_difference_apply_one χ₂ i
  simp only [SignedIrreducibleDifferenceFamily.difference_apply_one,
    SignedIrreducibleDifferenceFamily.classFunction_apply] at h0
  exact sub_eq_zero.mp h0

/-- **The (4.9) degree bridge.**  The column-sum degree equality `∑_i μ_{ij}(1) = ∑_i μ_{ik}(1)`
(= `μ_j(1) = μ_k(1)` since `μ_j = ∑_i μ_{ij}`) gives the per-row equalities `μ_{ij}(1) = μ_{ik}(1)`:
each column is degree-constant (`columnFamily_mu_apply_one_eq`), so both sums are `w₁` times the
anchor degree, and `w₁ ≠ 0` cancels. -/
theorem forall_columnFamily_mu_apply_one_eq_of_sum_eq (h : Hypothesis46 A L)
    [NeZero (Nat.card h.W1)] [Finite ↥(h.W1 ⊔ h.W2)]
    [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    (χ₂ χ₂' : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ)
    (hdeg : ∑ i, ((h.columnFamily χ₂).mu i : ClassFunction ↥L ℂ) 1
          = ∑ i, ((h.columnFamily χ₂').mu i : ClassFunction ↥L ℂ) 1) :
    ∀ i, ((h.columnFamily χ₂).mu i : ClassFunction ↥L ℂ) 1
        = ((h.columnFamily χ₂').mu i : ClassFunction ↥L ℂ) 1 := by
  have : Fintype ↥(h.W1 ⊔ h.W2) := Fintype.ofFinite _
  have ej : ∑ i, ((h.columnFamily χ₂).mu i : ClassFunction ↥L ℂ) 1
      = (Nat.card h.W1 : ℂ) * ((h.columnFamily χ₂).mu 0 : ClassFunction ↥L ℂ) 1 := by
    rw [Finset.sum_congr rfl (fun i _ => columnFamily_mu_apply_one_eq h χ₂ i),
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have ek : ∑ i, ((h.columnFamily χ₂').mu i : ClassFunction ↥L ℂ) 1
      = (Nat.card h.W1 : ℂ) * ((h.columnFamily χ₂').mu 0 : ClassFunction ↥L ℂ) 1 := by
    rw [Finset.sum_congr rfl (fun i _ => columnFamily_mu_apply_one_eq h χ₂' i),
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [ej, ek] at hdeg
  have hw1 : (Nat.card h.W1 : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne (Nat.card h.W1))
  have hcol0 := mul_left_cancel₀ hw1 hdeg
  intro i
  rw [columnFamily_mu_apply_one_eq h χ₂ i, columnFamily_mu_apply_one_eq h χ₂' i, hcol0]

/-- **Grid-index distinctness.**  The transported `tic`-side characters `ω_{ij}^{tic}` are distinct
across the certain-type grid: `omegaProdCharTic h χ₂ i = omegaProdCharTic h χ₂' i'` iff
`χ₂ = χ₂'` and `i = i'`.  (`omegaProdChar` is injective in both arguments — `omegaProdChar_inj` —
and `w1CharEquiv` is an equivalence; the precomposition by the iso `ticWEquivSdiffW` is stripped
via its surjectivity.)  This generalises `omegaProdCharTic_ne` to differing row indices. -/
theorem omegaProdCharTic_eq_iff (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    (χ₂ χ₂' : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i i' : Fin (Nat.card h.W1)) :
    omegaProdCharTic h χ₂ i = omegaProdCharTic h χ₂' i' ↔ χ₂ = χ₂' ∧ i = i' := by
  constructor
  · intro heq
    have hstrip : h.sdiffTICyclicHypothesis.omegaProdChar (h.w1CharEquiv i) χ₂
        = h.sdiffTICyclicHypothesis.omegaProdChar (h.w1CharEquiv i') χ₂' := by
      refine MonoidHom.ext fun w => ?_
      obtain ⟨w', rfl⟩ := (ticWEquivSdiffW h).surjective w
      exact DFunLike.congr_fun heq w'
    obtain ⟨h1, h2⟩ := h.sdiffTICyclicHypothesis.omegaProdChar_inj hstrip
    exact ⟨h2, h.w1CharEquiv_injective h1⟩
  · rintro ⟨rfl, rfl⟩; rfl

open scoped Classical in
set_option backward.isDefEq.respectTransparency false in
/-- **`σ`-image orthonormality (per element).**  `⟨ω_{ij}^σ, ω_{i'j'}^σ⟩ = δ_{(i,j),(i',j')}`.
The `σ`-images are `σ(ω(P_{ij}))` with `P_{ij} = omegaProdCharTic h χ₂ i`; `σ` is an isometry
(`sigma_inner`) and the `ω`-family is orthonormal (`omega_inner_self`/`omega_inner_ne`), so the
inner product is `1` iff `P_{ij} = P_{i'j'}`, i.e. iff `χ₂ = χ₂'` and `i = i'`
(`omegaProdCharTic_eq_iff`). -/
theorem certainTypeOmegaSigma_inner (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    [Fintype (ticVdiff h).W] [Invertible (Nat.card (ticVdiff h).W : ℂ)]
    (χ₂ χ₂' : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i i' : Fin (Nat.card h.W1)) :
    ClassFunction.inner (certainTypeOmegaSigma h χ₂ i) (certainTypeOmegaSigma h χ₂' i')
      = if χ₂ = χ₂' ∧ i = i' then 1 else 0 := by
  simp only [certainTypeOmegaSigma]
  rw [(ticVdiff h).sigma_inner rfl (ticVdiffFullDadeApplication h)]
  by_cases hP : omegaProdCharTic h χ₂ i = omegaProdCharTic h χ₂' i'
  · rw [hP, (ticVdiff h).omega_inner_self,
      if_pos ((omegaProdCharTic_eq_iff h χ₂ χ₂' i i').mp hP)]
  · rw [(ticVdiff h).omega_inner_ne hP,
      if_neg (fun hcon => hP ((omegaProdCharTic_eq_iff h χ₂ χ₂' i i').mpr hcon))]

open scoped Classical in
/-- **`L`-irreducible column-sum orthonormality.**  `⟨∑_i μ_{ij}, ∑_i μ_{ij'}⟩ = w₁·δ_{jj'}`:
the certain-type characters `μ_{ij}` are distinct irreducibles of `L` (`columnFamily.injective`
within a column, `columnFamily_mu_ne` across columns), so the column sums `μ_j = ∑_i μ_{ij}` are
orthogonal for distinct columns and have norm² `w₁` on the diagonal. -/
theorem columnFamily_mu_sum_inner (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    [Finite ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    (χ₂ χ₂' : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) :
    ClassFunction.inner (∑ i, ((h.columnFamily χ₂).mu i : ClassFunction ↥L ℂ))
        (∑ i, ((h.columnFamily χ₂').mu i : ClassFunction ↥L ℂ))
      = if χ₂ = χ₂' then (Nat.card h.W1 : ℂ) else 0 := by
  have : Fintype ↥(h.W1 ⊔ h.W2) := Fintype.ofFinite _
  rw [inner_sum_left]
  simp_rw [inner_sum_right, irreducibleCharacter_inner_eq_ite]
  by_cases hc : χ₂ = χ₂'
  · subst hc
    rw [if_pos rfl]
    have hrow : ∀ i : Fin (Nat.card h.W1),
        (∑ i' : Fin (Nat.card h.W1),
          if (h.columnFamily χ₂).mu i = (h.columnFamily χ₂).mu i' then (1 : ℂ) else 0) = 1 := by
      intro i
      rw [Finset.sum_congr rfl (fun i' _ =>
          if_congr (h.columnFamily χ₂).injective.eq_iff rfl rfl),
        Finset.sum_ite_eq Finset.univ i (fun _ => (1 : ℂ)), if_pos (Finset.mem_univ i)]
    rw [Finset.sum_congr rfl (fun i _ => hrow i), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
  · rw [if_neg hc]
    exact Finset.sum_eq_zero (fun i _ =>
      Finset.sum_eq_zero (fun i' _ => if_neg (h.columnFamily_mu_ne hc i i')))

end OddOrder.Peterfalvi.S06


