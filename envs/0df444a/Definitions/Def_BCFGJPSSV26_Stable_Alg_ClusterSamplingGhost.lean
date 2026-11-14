-- Prove2me | Definitions.Def_BCFGJPSSV26_Stable_Alg_ClusterSamplingGhost
-- name    : BCFGJPSSV26_Stable_Alg_ClusterSamplingGhost
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T17:08:30.5572+00:00
-- url     : https://prove2.me/theorems/ea141e74-4c4a-4ae1-92fd-2e19033dad8e
-- title:
--   BCFGJPSSV26.Stable.Alg.ClusterSamplingGhost — The analysis of the cluster sampling: the ghost matching and the invariant
-- statement:
--   This is module `BCFGJPSSV26.Stable.Alg.ClusterSamplingGhost` of the Lean 4 formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)), from the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (formalized with Claude Code, Apache-2.0).
--
--   The data of the analysis (`BCFGJPSSV26.Stable.KSData`): a context with the standing hypotheses,
--   the local-search list `LS` of `S`, and an outcome `Λ₁` of the client sampling with its witness.
--
--   **Ghost matching** (`BCFGJPSSV26.Stable.KSData.ghost`): the dummies, in order, are matched
--   greedily to the clusters of `𝒪 = O₂ \ O_X`: each takes the least unmatched cluster of which its
--   leader is a loose satellite, if any. The matched clusters (`BCFGJPSSV26.Stable.KSData.matched`)
--   and their dummies (`BCFGJPSSV26.Stable.KSData.dumOf`) are functions of the list of dummies, so the
--   unmatched clusters `O_B` (`BCFGJPSSV26.Stable.KSData.OB`) and the cost conditions are functions of
--   the state.
--
--   **Contents.** The module is published as a whole: 58 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with library lemmas renamed back to their names in this Mathlib and a few proof steps adjusted; no statement is changed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BCFGJPSSV26_Stable_Alg_ClusterSamplingGhost`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Stable/Alg/ClusterSamplingGhost.lean

module

public import Definitions.Def_BCFGJPSSV26_Stable_Alg_ClusterSampling
public import Definitions.Def_BCFGJPSSV26_Stable_Structure_ClusterWitness

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `BCFGJPSSV26.Stable.Alg.ClusterSamplingGhost` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# The analysis of the cluster sampling: the ghost matching and the invariant

The data of the analysis (`BCFGJPSSV26.Stable.KSData`): a context with the standing hypotheses,
the local-search list `LS` of `S`, and an outcome `Λ₁` of the client sampling with its witness.

**Ghost matching** (`BCFGJPSSV26.Stable.KSData.ghost`): the dummies, in order, are matched
greedily to the clusters of `𝒪 = O₂ \ O_X`: each takes the least unmatched cluster of which its
leader is a loose satellite, if any. The matched clusters (`BCFGJPSSV26.Stable.KSData.matched`)
and their dummies (`BCFGJPSSV26.Stable.KSData.dumOf`) are functions of the list of dummies, so the
unmatched clusters `O_B` (`BCFGJPSSV26.Stable.KSData.OB`) and the cost conditions are functions of
the state.
-/

@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset

/-- **The data of the analysis of the cluster sampling.** -/
structure KSData where
  /-- The context. -/
  X : Ctx
  H : Hyp X
  /-- The local-search list. -/
  LS : List ℕ
  hLS : X.I.centers LS = X.S
  hnd : LS.Nodup
  hm : ∀ i ∈ LS, i < X.I.m
  /-- The outcome of the client sampling. -/
  Λ₁ : List DumQ
  hΛ₁ : (toRaw X.I).ValidDums Λ₁
  /-- Its witness. -/
  w₁ : ClientWitness X (toDums X.I Λ₁)

namespace KSData

variable (K : KSData)

theorem m_pos : 0 < K.X.I.m := K.H.valid.one_le_m

/-- The facility of a number (reduced mod `m`). -/
def fac (l : ℕ) : Fin K.X.I.m := ⟨l % K.X.I.m, Nat.mod_lt _ K.m_pos⟩

theorem fac_val {l : ℕ} (h : l < K.X.I.m) : (K.fac l).1 = l := Nat.mod_eq_of_lt h

theorem fac_eq {l : ℕ} (h : l < K.X.I.m) : K.fac l = ⟨l, h⟩ := Fin.ext (K.fac_val h)

@[simp] theorem fac_fin (i : Fin K.X.I.m) : K.fac i.1 = i := K.fac_eq i.2

/-- One step of the cluster sampling. -/
def step (st : KSState) (u : ℕ) : KSState :=
  ksStep K.X.P.N (toRaw K.X.I) K.LS K.Λ₁ K.X.s K.X.b st u

/-! ### The kept centers -/

/-- The candidates `LS \ R⁻`. -/
def cand (del : List ℕ) : List ℕ := K.LS.filter fun c ↦ decide (c ∉ del)

/-- The kept centers `LS' = S \ R⁻`. -/
noncomputable def LSp (del : List ℕ) : Finset (Fin K.X.I.m) := K.X.I.centers (K.cand del)

theorem mem_S {c : Fin K.X.I.m} : c ∈ K.X.S ↔ c.1 ∈ K.LS := by
  rw [← K.hLS, Instance.mem_centers]

theorem mem_LSp {del : List ℕ} {c : Fin K.X.I.m} : c ∈ K.LSp del ↔ c ∈ K.X.S ∧ c.1 ∉ del := by
  rw [LSp, Instance.mem_centers, K.mem_S, cand, List.mem_filter, decide_eq_true_iff]

theorem LSp_subset (del : List ℕ) : K.LSp del ⊆ K.X.S := fun _ h ↦ (K.mem_LSp.1 h).1

theorem cand_nodup (del : List ℕ) : (K.cand del).Nodup := K.hnd.filter _

theorem cand_lt {del : List ℕ} {i : ℕ} (h : i ∈ K.cand del) : i < K.X.I.m :=
  K.hm i (List.mem_of_mem_filter h)

theorem ksLS'_eq (st : KSState) : ksLS' K.LS st = K.cand st.del := rfl

/-! ### Dummies -/

/-- The dummy of an exact dummy. -/
noncomputable def toDum (d : DumQ) : Dummy K.X.I :=
  if h : d.1 < K.X.I.n + K.X.I.m then ⟨finSumFinEquiv.symm ⟨d.1, h⟩, d.2⟩
  else ⟨.inr (K.fac 0), d.2⟩

theorem toDum_radius (d : DumQ) : (K.toDum d).radius = d.2 := by
  unfold toDum
  split_ifs <;> rfl

theorem toDum_fac {i r : ℕ × ℚ} (h : i.1 < K.X.I.m) (hd : r.1 = K.X.I.n + i.1) :
    K.toDum r = ⟨.inr ⟨i.1, h⟩, r.2⟩ := by
  have hlt : r.1 < K.X.I.n + K.X.I.m := by omega
  unfold toDum
  rw [dif_pos hlt]
  congr 1
  have : (⟨r.1, hlt⟩ : Fin (K.X.I.n + K.X.I.m)) = Fin.natAdd K.X.I.n ⟨i.1, h⟩ := Fin.ext hd
  rw [this, finSumFinEquiv_symm_apply_natAdd]

theorem toDum_leader {d : DumQ} {i : ℕ} (h : i < K.X.I.m) (hd : d.1 = K.X.I.n + i) :
    (K.toDum d).leader = .inr ⟨i, h⟩ := by
  rw [K.toDum_fac (i := (i, 0)) h hd]

theorem toDum_inj {d d' : DumQ} (h : d.1 < K.X.I.n + K.X.I.m) (h' : d'.1 < K.X.I.n + K.X.I.m)
    (he : K.toDum d = K.toDum d') : d = d' := by
  unfold toDum at he
  rw [dif_pos h, dif_pos h'] at he
  simp only [Dummy.mk.injEq, EmbeddingLike.apply_eq_iff_eq, Fin.mk.injEq, Rat.cast_inj] at he
  exact Prod.ext he.1 he.2

theorem toDums_eq_map {D : List DumQ} (hD : (toRaw K.X.I).ValidDums D) :
    toDums K.X.I D = D.map K.toDum := by
  induction D with
  | nil => rfl
  | cons d D ih =>
    have hd : d.1 < K.X.I.n + K.X.I.m := hD d List.mem_cons_self
    rw [toDums, List.filterMap_cons, dif_pos hd, List.map_cons, ← toDums,
      ih fun l hl ↦ hD l (List.mem_cons_of_mem _ hl)]
    unfold toDum
    rw [dif_pos hd]

/-! ### The ghost matching -/

/-- `𝒪 = O₂ \ O_X`. -/
noncomputable def OO : Finset (Fin K.X.I.m) := K.X.O2 K.w₁.OL \ K.X.OX K.w₁.OL

/-- The point numbered `a` is a loose satellite of `c`. -/
def Cand (c : Fin K.X.I.m) (a : ℕ) : Prop := ∃ i ∈ K.X.GamE c, a = K.X.I.n + i.1

theorem cand_iff {c i : Fin K.X.I.m} : K.Cand c (K.X.I.n + i.1) ↔ i ∈ K.X.GamE c := by
  constructor
  · rintro ⟨i', hi', he⟩
    rwa [Fin.ext (Nat.add_left_cancel he)]
  · exact fun h ↦ ⟨i, h, rfl⟩

open Classical in
/-- The least unmatched cluster of `𝒪` of which `a` is a loose satellite. -/
noncomputable def pick (M : Finset (Fin K.X.I.m)) (a : ℕ) : Option (Fin K.X.I.m) :=
  if h : ((K.OO \ M).filter fun c ↦ K.Cand c a).Nonempty then
    some (((K.OO \ M).filter fun c ↦ K.Cand c a).min' h)
  else none

theorem pick_some {M : Finset (Fin K.X.I.m)} {a : ℕ} {c : Fin K.X.I.m}
    (h : K.pick M a = some c) : c ∈ K.OO ∧ c ∉ M ∧ K.Cand c a := by
  classical
  unfold pick at h
  split_ifs at h with hn
  obtain rfl := Option.some.inj h
  have := min'_mem _ hn
  simp only [mem_filter, mem_sdiff] at this
  exact ⟨this.1.1, this.1.2, this.2⟩

theorem pick_isSome {M : Finset (Fin K.X.I.m)} {a : ℕ} {c : Fin K.X.I.m} (hc : c ∈ K.OO)
    (hM : c ∉ M) (ha : K.Cand c a) : ∃ c', K.pick M a = some c' := by
  classical
  unfold pick
  rw [dif_pos ⟨c, mem_filter.2 ⟨mem_sdiff.2 ⟨hc, hM⟩, ha⟩⟩]
  exact ⟨_, rfl⟩

/-- One step of the greedy matching. -/
noncomputable def gstep (p : Finset (Fin K.X.I.m) × (Fin K.X.I.m → DumQ)) (d : DumQ) :
    Finset (Fin K.X.I.m) × (Fin K.X.I.m → DumQ) :=
  match K.pick p.1 d.1 with
  | some c => (insert c p.1, Function.update p.2 c d)
  | none => p

/-- **The ghost matching** of a list of dummies. -/
noncomputable def ghost (D : List DumQ) : Finset (Fin K.X.I.m) × (Fin K.X.I.m → DumQ) :=
  D.foldl K.gstep (∅, fun _ ↦ (0, 0))

/-- The matched clusters. -/
noncomputable def matched (D : List DumQ) : Finset (Fin K.X.I.m) := (K.ghost D).1

/-- The dummy of a matched cluster. -/
noncomputable def dumOf (D : List DumQ) : Fin K.X.I.m → DumQ := (K.ghost D).2

/-- The unmatched clusters `O_B`. -/
noncomputable def OB (D : List DumQ) : Finset (Fin K.X.I.m) := K.X.OB K.w₁.OL (K.matched D)

theorem ghost_append (D : List DumQ) (d : DumQ) : K.ghost (D ++ [d]) = K.gstep (K.ghost D) d := by
  unfold ghost
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem matched_nil : K.matched [] = ∅ := rfl

theorem ghost_append_some {D : List DumQ} {d : DumQ} {c : Fin K.X.I.m}
    (h : K.pick (K.matched D) d.1 = some c) :
    K.matched (D ++ [d]) = insert c (K.matched D) ∧
      K.dumOf (D ++ [d]) = Function.update (K.dumOf D) c d := by
  unfold matched dumOf at *
  rw [K.ghost_append, gstep, h]
  exact ⟨rfl, rfl⟩

theorem ghost_append_none {D : List DumQ} {d : DumQ} (h : K.pick (K.matched D) d.1 = none) :
    K.ghost (D ++ [d]) = K.ghost D := by
  unfold matched at h
  rw [K.ghost_append, gstep, h]

/-- The facts of the ghost matching. -/
theorem ghost_spec (D : List DumQ) :
    K.matched D ⊆ K.OO ∧ (K.matched D).card ≤ D.length ∧
      ∀ c ∈ K.matched D, K.dumOf D c ∈ D ∧ K.Cand c (K.dumOf D c).1 := by
  induction D using List.reverseRecOn with
  | nil => simp [matched_nil]
  | append_singleton D d ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    rcases hp : K.pick (K.matched D) d.1 with _ | c
    · have he := K.ghost_append_none hp
      unfold matched dumOf at *
      rw [he]
      refine ⟨h1, by simp; omega, fun c hc ↦ ⟨List.mem_append_left _ (h3 c hc).1, (h3 c hc).2⟩⟩
    · obtain ⟨hc, hcM, hca⟩ := K.pick_some hp
      obtain ⟨e1, e2⟩ := K.ghost_append_some hp
      rw [e1, e2]
      refine ⟨insert_subset hc h1, ?_, fun c' hc' ↦ ?_⟩
      · rw [card_insert_of_notMem hcM, List.length_append, List.length_singleton]
        omega
      · rcases mem_insert.1 hc' with rfl | hc'
        · rw [Function.update_self]
          exact ⟨List.mem_append_right _ List.mem_cons_self, hca⟩
        · have hne : c' ≠ c := fun h ↦ hcM (h ▸ hc')
          rw [Function.update_of_ne hne]
          exact ⟨List.mem_append_left _ (h3 c' hc').1, (h3 c' hc').2⟩

theorem matched_subset (D : List DumQ) : K.matched D ⊆ K.OO := (K.ghost_spec D).1

theorem dumOf_mem {D : List DumQ} {c : Fin K.X.I.m} (hc : c ∈ K.matched D) :
    K.dumOf D c ∈ D := ((K.ghost_spec D).2.2 c hc).1

theorem dumOf_cand {D : List DumQ} {c : Fin K.X.I.m} (hc : c ∈ K.matched D) :
    K.Cand c (K.dumOf D c).1 := ((K.ghost_spec D).2.2 c hc).2

theorem matched_append_subset (D : List DumQ) (d : DumQ) :
    K.matched D ⊆ K.matched (D ++ [d]) := by
  rcases hp : K.pick (K.matched D) d.1 with _ | c
  · have he := K.ghost_append_none hp
    unfold matched at *
    rw [he]
  · rw [(K.ghost_append_some hp).1]
    exact subset_insert _ _

theorem OB_append_subset (D : List DumQ) (d : DumQ) : K.OB (D ++ [d]) ⊆ K.OB D :=
  sdiff_subset_sdiff subset_rfl (K.matched_append_subset D d)

theorem mem_OB {D : List DumQ} {c : Fin K.X.I.m} : c ∈ K.OB D ↔ c ∈ K.OO ∧ c ∉ K.matched D := by
  unfold OB Ctx.OB OO
  rw [mem_sdiff]

theorem dumOf_injOn {D : List DumQ} (hD : D.Nodup) : Set.InjOn (K.dumOf D) (K.matched D) := by
  induction D using List.reverseRecOn with
  | nil => simp [matched_nil]
  | append_singleton D d ih =>
    have hnd : D.Nodup := hD.sublist (List.sublist_append_left D [d])
    have hdD : d ∉ D := by
      intro h
      rw [List.nodup_append] at hD
      exact hD.2.2 d h d List.mem_cons_self rfl
    rcases hp : K.pick (K.matched D) d.1 with _ | c
    · have he := K.ghost_append_none hp
      unfold matched dumOf at *
      rw [he]
      exact ih hnd
    · obtain ⟨-, hcM, -⟩ := K.pick_some hp
      obtain ⟨e1, e2⟩ := K.ghost_append_some hp
      rw [e1, e2]
      intro c₁ h₁ c₂ h₂ he
      rw [coe_insert, Set.mem_insert_iff] at h₁ h₂
      by_cases hc₁ : c₁ = c <;> by_cases hc₂ : c₂ = c
      · rw [hc₁, hc₂]
      · rw [hc₁, Function.update_self, Function.update_of_ne hc₂] at he
        exact absurd (he ▸ K.dumOf_mem (h₂.resolve_left hc₂)) hdD
      · rw [hc₂, Function.update_self, Function.update_of_ne hc₁] at he
        exact absurd (he ▸ K.dumOf_mem (h₁.resolve_left hc₁)) hdD
      · rw [Function.update_of_ne hc₁, Function.update_of_ne hc₂] at he
        exact ih hnd (h₁.resolve_left hc₁) (h₂.resolve_left hc₂) he

/-! ### Cost conditions -/

/-- The mixed list of dummies `Λ₁ ++ Λ₂`. -/
noncomputable def mixL (D : List DumQ) : List (Dummy K.X.I) := toDums K.X.I K.Λ₁ ++ toDums K.X.I D

/-- The sampling weight of a center: its local-search cluster cost (phase `0`), or the cost of its
cluster in the mixed set `(LS', Λ₁ ++ Λ₂)` (phase `1`). -/
noncomputable def wt (ph : ℕ) (del : List ℕ) (D : List DumQ) (c : Fin K.X.I.m) : ℝ :=
  if ph = 0 then K.X.costS (K.X.CS c)
  else costMixOn K.X.I (K.LSp del) (K.mixL D) (clusterMix K.X.I (K.LSp del) (K.mixL D) c)

/-- The good centers to sample: the satellites of `O_B` (phase `0`), and also the kept centers
outside `LS_X` (phase `1`). -/
noncomputable def GoodL (ph : ℕ) (del : List ℕ) (D : List DumQ) : Finset (Fin K.X.I.m) :=
  if ph = 0 then K.X.GamOf (K.OB D) else K.X.GamOf (K.OB D) ∪ (K.LSp del \ K.X.LSX K.w₁.OL)

/-- **The cost condition** of a phase: the good centers weigh less than `ε³ opt`. -/
def cc (ph : ℕ) (del : List ℕ) (D : List DumQ) : Prop :=
  ∑ c ∈ K.GoodL ph del D, K.wt ph del D c < K.X.ε ^ 3 * K.X.opt

/-- The satellites of `O_B` are kept. -/
def GamSub (del : List ℕ) (D : List DumQ) : Prop := ∀ c ∈ K.X.GamOf (K.OB D), c.1 ∉ del

/-! ### The invariant -/

/-- The clauses on the deleted centers and the dummies. -/
structure Base (del : List ℕ) (D : List DumQ) : Prop where
  dums_nodup : D.Nodup
  card : (K.matched D).card = D.length
  rad : ∀ c ∈ K.matched D,
    K.X.I.dd (.inr c) (K.toDum (K.dumOf D c)).leader ≤ (K.toDum (K.dumOf D c)).radius ∧
      (K.toDum (K.dumOf D c)).radius ≤ (1 + K.X.kap c + 6 * K.X.ε) * K.X.per c
  del_nodup : del.Nodup
  del_sub : ∀ i ∈ del, i < K.X.I.m ∧ K.fac i ∈ K.X.S \ K.X.LSX K.w₁.OL

/-- The clauses of the modes `DG`, `RG`, `RGB` about the leader `ℓ`: a kept center outside `LS_X`,
loose satellite of every cluster of `O_B` that lost a satellite. -/
structure Mid (del : List ℕ) (D : List DumQ) (l : ℕ) : Prop where
  lt : l < K.X.I.m
  mem : K.fac l ∈ K.X.S \ K.X.LSX K.w₁.OL
  nmem : l ∉ del
  lose : ∀ c ∈ K.OB D, (∃ i ∈ K.X.Gam c, i.1 ∈ del) → K.fac l ∈ K.X.GamE c

/-- The clause of the mode `DG`: `ℓ` is a satellite of a cluster `c₀` of `O_B`, with a kept
satellite `w` at distance in `[ε per₀/2, 5 per₀)`. -/
def DGc (del : List ℕ) (D : List DumQ) (l : ℕ) : Prop :=
  ∃ c₀ ∈ K.OB D, K.fac l ∈ K.X.Gam c₀ ∧ ∃ w ∈ K.X.Gam c₀, w.1 ∉ del ∧
    K.X.ε * K.X.per c₀ / 2 ≤ K.X.dF (K.fac l) w ∧ K.X.dF (K.fac l) w < 5 * K.X.per c₀

/-- The clause of the mode `RG`: `ℓ` is a loose satellite of a cluster of `O_B`. -/
def RGc (D : List DumQ) (l : ℕ) : Prop := ∃ c ∈ K.OB D, K.fac l ∈ K.X.GamE c

/-- The clause of the modes `RG`, `RGB`: the radius base is comparable with the percentiles of
the clusters of `O_B` that `ℓ` can lead. -/
def Rad0 (D : List DumQ) (l : ℕ) (r₀ : ℚ) : Prop :=
  0 < (r₀ : ℝ) ∧ ∀ c ∈ K.OB D, K.fac l ∈ K.X.GamE c →
    K.X.ε ^ 2 * K.X.per c / 3 ≤ r₀ ∧ (r₀ : ℝ) ≤ 15 * K.X.per c

/-- **The invariant of the cluster sampling**: the clauses on the deleted centers and the
dummies, the counters, the leaders of the dummies, and the clauses of the phases and modes. -/
structure Inv (st : KSState) : Prop where
  base : K.Base st.del st.dums
  phase_le : st.phase ≤ 2
  j_le : st.j ≤ K.X.s
  j_lt : st.tag ≠ 0 → st.j < K.X.s
  tag_le : st.tag ≤ 5
  leaders : ∀ d ∈ st.dums, (∃ i ∈ st.del, d.1 = K.X.I.n + i) ∨
    (4 ≤ st.tag ∧ d.1 = K.X.I.n + st.ldr ∧
      ∃ x < Par.Gr K.X.P.N, ∃ t < st.dums.length, d.2 = ksRad K.X.P.N K.X.s st.r₀ x t)
  gam : st.tag ≤ 2 → K.GamSub st.del st.dums
  ph1 : 1 ≤ st.phase → K.cc 0 st.del st.dums
  ph2 : st.phase = 2 → K.cc 1 st.del st.dums ∧ st.tag = 0
  start : st.phase < 2 → st.tag = 0 → K.cc st.phase st.del st.dums ∨ st.j ≤ st.del.length
  prog : st.phase < 2 → st.tag ≠ 0 → st.j ≤ st.del.length
  sample : st.phase < 2 → st.tag = 1 → ¬ K.cc st.phase st.del st.dums
  radd : st.phase < 2 → st.tag = 2 →
    st.ldr ∈ K.LS ∧ st.ldr ∉ st.del ∧ K.fac st.ldr ∈ K.GoodL st.phase st.del st.dums
  mid : st.phase < 2 → 3 ≤ st.tag → K.Mid st.del st.dums st.ldr
  dg : st.phase < 2 → st.tag = 3 → K.DGc st.del st.dums st.ldr
  rg : st.phase < 2 → st.tag = 4 → K.RGc st.dums st.ldr
  rad0 : st.phase < 2 → 4 ≤ st.tag → K.Rad0 st.dums st.ldr st.r₀

/-! ### The good chunks -/

/-- The nearest other kept center to `ℓ`. -/
def nearOther (del : List ℕ) (l : ℕ) : ℕ :=
  (toRaw K.X.I).nearQ (K.X.I.n + l) (K.LS.filter fun c ↦ decide (c ∉ del ∧ c ≠ l))

/-- The sampled center. -/
def sampled (st : KSState) (u : ℕ) : ℕ :=
  (K.cand st.del).getD
    (wsample K.X.b (ksWeights (toRaw K.X.I) K.LS K.Λ₁ st.phase st.del st.dums (K.cand st.del))
      u) 0

/-- **The good chunks** of a state. -/
def Good (st : KSState) (u : ℕ) : Prop :=
  if st.phase = 2 then True
  else if st.tag = 0 then st.j = K.X.s ∨ (cbit K.X.b u = true ↔ K.cc st.phase st.del st.dums)
  else if st.tag = 1 then K.fac (K.sampled st u) ∈ K.GoodL st.phase st.del st.dums
  else if st.tag = 2 then (cbit K.X.b u = true ↔ K.fac st.ldr ∉ K.X.GamOf (K.OB st.dums))
  else if st.tag = 3 then
    (cbit K.X.b u = true ↔ ∃ c ∈ K.OB st.dums, K.fac st.ldr ∈ K.X.GamE c ∧
      K.X.ε ^ 2 * K.X.per c ≤ ((toRaw K.X.I).fdist (K.X.I.n + st.ldr)
        (K.nearOther st.del st.ldr) : ℝ))
  else if st.tag = 4 then
    ∀ c, K.pick (K.matched st.dums) (K.X.I.n + st.ldr) = some c →
      K.X.dF c (K.fac st.ldr) ≤ (grid K.X.P.N st.r₀ (cunif (Par.Gr K.X.P.N) u) : ℝ) ∧
        (grid K.X.P.N st.r₀ (cunif (Par.Gr K.X.P.N) u) : ℝ) ≤
          (1 + K.X.ε) * K.X.dF c (K.fac st.ldr)
  else (cbit K.X.b u = true ↔ ¬ ∃ c ∈ K.OB st.dums, K.fac st.ldr ∈ K.X.GamE c)

end KSData

end BCFGJPSSV26.Stable


