-- Prove2me | Definitions.Def_BCFGJPSSV26_Greedy_Valid
-- name    : BCFGJPSSV26_Greedy_Valid
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:23:31.128202+00:00
-- url     : https://prove2.me/theorems/51b8a27c-45d8-470b-819c-50637a712525
-- title:
--   BCFGJPSSV26.Greedy.Valid — Valid sequences and solutions
-- statement:
--   This is module `BCFGJPSSV26.Greedy.Valid` of the Lean 4 formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)), from the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (formalized with Claude Code, Apache-2.0).
--
--   [BCFGJPSSV26a, Definitions D.3 and D.6], with sequences counted from `0`: sequence `p` is of
--   type 1 if `p` is even, has time `θ (p / 2)`, and the time is raised after each sequence of type 2.
--
--   * **Validity of an atom** (`BCFGJPSSV26.Greedy.ValidAt`): a free atom is always valid; a regular
--     atom must be openable with respect to a superset of the pairs of the atoms before it. The
--     superset is a set of pairs `(facility, offset)` with nonnegative offsets: a free copy at offset
--     `0` and the regular facility are the same pair, so validity is kept when the merge replaces one
--     by the other.
--   * **Maximality** (`BCFGJPSSV26.Greedy.Maximal`): no facility is `(ν, 0)`-openable after the
--     sequence.
--   * **Solutions** (`BCFGJPSSV26.Greedy.Sol`): exactly `2R` valid sequences of well-formed atoms,
--     after which every client is inactive at time `θ R`.
--
--   The invariants: no overbidding at the start of every sequence and for every superset
--   (`BCFGJPSSV26.Greedy.noOver_partial`, [BCFGJPSSV26a, Lemma E.6]); all clients become
--   inactive in a maximal sequence of type 1 once `θ ≥ f + γ M` (`BCFGJPSSV26.Greedy.all_inactive`);
--   and the validity calculus the merge uses, including [BCFGJPSSV26a, Claim D.12]
--   (`BCFGJPSSV26.Greedy.ValidSeq.param_f`, `BCFGJPSSV26.Greedy.ValidSeq.param_u`).
--
--   **Contents.** The module is published as a whole: 25 declarations (definitions, structures, instances and their supporting lemmas, with proofs). Published as separate theorems, and therefore not in this file: `BCFGJPSSV26.Greedy.ValidSeq.append_free`, `BCFGJPSSV26.Greedy.ValidSeq.of_profile_le`, `BCFGJPSSV26.Greedy.ValidSeq.param_f`, `BCFGJPSSV26.Greedy.ValidSeq.param_u`, `BCFGJPSSV26.Greedy.noOver_partial` (together with the auxiliary lemmas that depend on them).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BCFGJPSSV26_Greedy_Valid`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Greedy/Valid.lean

module

public import Definitions.Def_BCFGJPSSV26_Greedy_Openable

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `BCFGJPSSV26.Greedy.Valid` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Valid sequences and solutions

[BCFGJPSSV26a, Definitions D.3 and D.6], with sequences counted from `0`: sequence `p` is of
type 1 if `p` is even, has time `θ (p / 2)`, and the time is raised after each sequence of type 2.

* **Validity of an atom** (`BCFGJPSSV26.Greedy.ValidAt`): a free atom is always valid; a regular
  atom must be openable with respect to a superset of the pairs of the atoms before it. The
  superset is a set of pairs `(facility, offset)` with nonnegative offsets: a free copy at offset
  `0` and the regular facility are the same pair, so validity is kept when the merge replaces one
  by the other.
* **Maximality** (`BCFGJPSSV26.Greedy.Maximal`): no facility is `(ν, 0)`-openable after the
  sequence.
* **Solutions** (`BCFGJPSSV26.Greedy.Sol`): exactly `2R` valid sequences of well-formed atoms,
  after which every client is inactive at time `θ R`.

The invariants: no overbidding at the start of every sequence and for every superset
(`BCFGJPSSV26.Greedy.noOver_partial`, [BCFGJPSSV26a, Lemma E.6]); all clients become
inactive in a maximal sequence of type 1 once `θ ≥ f + γ M` (`BCFGJPSSV26.Greedy.all_inactive`);
and the validity calculus the merge uses, including [BCFGJPSSV26a, Claim D.12]
(`BCFGJPSSV26.Greedy.ValidSeq.param_f`, `BCFGJPSSV26.Greedy.ValidSeq.param_u`).
-/

@[expose] public section

namespace BCFGJPSSV26.Greedy

open Finset

variable {n m : ℕ} (P : Par) (d : Fin n → Fin m → ℚ)

/-! ### Definitions -/

/-- **Validity** of atom `h` of sequence `p` after the atoms `pre`, for the opening cost `f` and
the slack `η`. -/
def ValidAt (f η : ℚ) (p : ℕ) (pre : List (Atom m)) (h : Atom m) : Prop :=
  h.free = true ∨ ∃ S : Finset (Fin m × ℚ), pairs pre ⊆ S ∧ (∀ q ∈ S, 0 ≤ q.2) ∧
    OpenT P d (typ1 p) f η (P.θseq p) (profF P.K d S) h.fac

/-- **Maximality** after the atoms `S`, in sequence `p`. -/
def Maximal (f : ℚ) (p : ℕ) (S : List (Atom m)) : Prop :=
  ∀ i, ¬ OpenT P d (typ1 p) f 0 (P.θseq p) (profL P.K d S) i

/-- A **valid sequence** `H` of type `p` after the atoms `pre`. -/
def ValidSeq (f η : ℚ) (p : ℕ) (pre H : List (Atom m)) : Prop :=
  (∀ t (ht : t < H.length), ValidAt P d f η p (pre ++ H.take t) H[t]) ∧
    Maximal P d f p (pre ++ H)

/-- A sequence of **`η`-valid sequences**. -/
def EtaValid (f η : ℚ) (H : List (List (Atom m))) : Prop :=
  ∀ p (hp : p < H.length), ValidSeq P d f η p (H.take p).flatten H[p]

/-- An **`η`-valid solution**: `2R` valid sequences of well-formed atoms, after which every
client is inactive at time `θ R`. -/
def Sol (f η : ℚ) (H : List (List (Atom m))) : Prop :=
  H.length = 2 * P.R ∧ EtaValid P d f η H ∧ (∀ a ∈ H.flatten, a.WF P.K) ∧
    ∀ j, (1 - P.δ) * profL P.K d H.flatten j ≤ P.θ P.R

/-- The number of regular atoms. -/
def nReg (H : List (List (Atom m))) : ℕ := (H.flatten.filter fun a ↦ !a.free).length

/-- The number of free atoms. -/
def nFree (H : List (List (Atom m))) : ℕ := (H.flatten.filter fun a ↦ a.free).length

/-- The number of free atoms of a sequence. -/
def nFreeSeq (S : List (Atom m)) : ℕ := (S.filter fun a ↦ a.free).length

/-- The connection cost of a solution: the sum of the final profile. -/
def connCost (H : List (List (Atom m))) : ℚ := ∑ j, profL P.K d H.flatten j

/-- The cost of a set `O` of facilities (`0` if empty). -/
def costF (O : Finset (Fin m)) : ℚ := ∑ j, if h : O.Nonempty then O.inf' h (d j) else 0

variable {P d}

/-- The pairs of a list contained in another are among its pairs. -/
private theorem pairs_mono {S T : List (Atom m)} (h : S ⊆ T) : pairs S ⊆ pairs T := by
  intro q hq
  simp only [pairs, List.mem_toFinset, List.mem_map] at hq ⊢
  obtain ⟨a, ha, rfl⟩ := hq
  exact ⟨a, h ha, rfl⟩

/-- All times are positive. -/
private theorem θseq_pos (P : Par) (p : ℕ) : 0 < P.θseq p :=
  zero_lt_one.trans_le (P.one_le_θ (p / 2))

/-! ### No overbidding -/

/-- No overbidding at time `1`, when all distances are at least `1`. -/
theorem noOver_start (hd1 : ∀ j i, 1 ≤ d j i) {f : ℚ} (hf : 0 ≤ f) (D : Fin n → ℚ) :
    NoOver P d f 1 D := by
  intro i₀
  have h0 : over P d 1 D i₀ = 0 := sum_eq_zero fun j _ ↦
    bid_eq_zero_of_le ((min_le_left _ _).trans (hd1 j i₀)) (by linarith [hd1 j i₀])
  rw [h0]
  exact hf

/-- **Termination**: after a maximal sequence of type 1 at a time `θ ≥ f + γ M`, every client is
inactive. (An active client would pay `θ - γ M ≥ f` to any facility.) -/
theorem all_inactive (hP : P.Good n) {M : ℚ} (hd0 : ∀ j i, 0 ≤ d j i) (hdM : ∀ j i, d j i ≤ M)
    {f θ : ℚ} {D : Fin n → ℚ} (hθ : f + γ * M ≤ θ) (i₀ : Fin m)
    (hmax : ∀ i, ¬ Open1 P d f 0 θ D i) (j : Fin n) : (1 - P.δ) * D j ≤ θ := by
  by_contra hj
  push Not at hj
  refine hmax i₀ ?_
  have hδ := hP.one_sub_δ_pos
  have hγ := one_le_γ
  have hterm : f ≤ bid (mval P θ D j) ((1 - P.δ) * d j i₀) := by
    rw [mval, min_eq_left hj.le]
    refine le_trans ?_ (le_max_left _ _)
    have h1 : (1 - P.δ) * d j i₀ ≤ d j i₀ := by nlinarith [hd0 j i₀, hP.δ_pos]
    nlinarith [hdM j i₀, hd0 j i₀]
  unfold Open1 lhs1
  rw [mul_zero, sub_zero]
  exact hterm.trans (single_le_sum (fun j _ ↦ bid_nonneg _ _) (mem_univ j))

/-- An `η`-valid sequence of length `2R` is a solution if the last time `θ (R - 1)` is at least
`f + γ M` (`BCFGJPSSV26.Greedy.all_inactive` in its last sequence of type 1). -/
theorem sol_of_etaValid (hP : P.Good n) {M : ℚ} (hd0 : ∀ j i, 0 ≤ d j i)
    (hdM : ∀ j i, d j i ≤ M) {f η : ℚ} (hR : 1 ≤ P.R) (hθ : f + γ * M ≤ P.θ (P.R - 1))
    (i₀ : Fin m) {H : List (List (Atom m))} (hlen : H.length = 2 * P.R)
    (hv : EtaValid P d f η H) (hwf : ∀ a ∈ H.flatten, a.WF P.K) : Sol P d f η H := by
  refine ⟨hlen, hv, hwf, fun j ↦ ?_⟩
  have hpl : 2 * (P.R - 1) < H.length := by omega
  have ht : typ1 (2 * (P.R - 1)) = true := by simp [typ1]
  have hθp : P.θseq (2 * (P.R - 1)) = P.θ (P.R - 1) := by
    unfold Par.θseq
    congr 1
    omega
  have hmax : ∀ i, ¬ Open1 P d f 0 (P.θ (P.R - 1))
      (profL P.K d ((H.take (2 * (P.R - 1))).flatten ++ H[2 * (P.R - 1)])) i := by
    intro i hi
    refine (hv _ hpl).2 i ?_
    rw [ht, hθp]
    exact hi
  have h1 := all_inactive hP hd0 hdM hθ i₀ hmax j
  have h2 : profL P.K d H.flatten j ≤
      profL P.K d ((H.take (2 * (P.R - 1))).flatten ++ H[2 * (P.R - 1)]) j := by
    refine profL_anti _ _ (pairs_mono fun a ha ↦ ?_) j
    simp only [List.mem_append, List.mem_flatten] at ha ⊢
    rcases ha with ⟨l, hl, ha⟩ | ha
    · exact ⟨l, List.mem_of_mem_take hl, ha⟩
    · exact ⟨_, List.getElem_mem hpl, ha⟩
  have h3 := P.θ_mono (show P.R - 1 ≤ P.R by omega)
  have h4 := mul_le_mul_of_nonneg_left h2 hP.one_sub_δ_pos.le
  linarith

/-- After a solution, the profile is below the cap. -/
theorem Sol.profL_lt_K (hP : P.Good n) {f η : ℚ} {H : List (List (Atom m))}
    (hH : Sol P d f η H) (j : Fin n) : profL P.K d H.flatten j < P.K := by
  by_contra h
  push Not at h
  have h1 := hH.2.2.2 j
  have hθ := P.one_le_θ P.R
  have hK := hP.K_ge
  have hδ := hP.δ_le
  have hδ' := hP.δ_pos
  nlinarith

/-! ### Regular atoms are distinct -/

/-- A valid regular atom is not already open (as the pair `(fac, 0)`), when `f > n η`. -/
theorem ValidAt.not_mem (hP : P.Good n) (hd0 : ∀ j i, 0 ≤ d j i) {f η : ℚ} (hf : n * η < f)
    {p : ℕ} {pre : List (Atom m)} {h : Atom m} (hv : ValidAt P d f η p pre h)
    (hreg : h.free = false) : (h.fac, (0 : ℚ)) ∉ pairs pre := by
  intro hmem
  rcases hv with hv | ⟨S, hS, -, hS'⟩
  · rw [hreg] at hv
    exact Bool.false_ne_true hv
  · have hle : ∀ j, profF P.K d S j ≤ d j h.fac := fun j ↦ by
      simpa using profF_le P.K d (hS hmem) j
    cases hb : typ1 p <;> simp only [OpenT, hb, cond] at hS'
    · obtain ⟨T, -, -, h3, -⟩ := hS'
      rw [lhs3_eq_zero hP (fun j ↦ hd0 j h.fac) hle] at h3
      linarith
    · unfold Open1 at hS'
      rw [lhs1_eq_zero hP (fun j ↦ hd0 j h.fac) hle] at hS'
      linarith

/-- Regular atoms that are not already open (as pairs at offset `0`) when they are added are
distinct facilities. -/
private theorem nodup_reg_aux : ∀ (L A : List (Atom m)),
    (∀ a ∈ A ++ L, a.free = false → a.off = 0) →
    ((A.filter fun a ↦ !a.free).map Atom.fac).Nodup →
    (∀ t (ht : t < L.length), L[t].free = false → (L[t].fac, (0 : ℚ)) ∉ pairs (A ++ L.take t)) →
    (((A ++ L).filter fun a ↦ !a.free).map Atom.fac).Nodup
  | [], A, _, hA, _ => by simpa using hA
  | a :: L, A, hw, hA, hL => by
    have h0 : a.free = false → (a.fac, (0 : ℚ)) ∉ pairs A := fun ha ↦ by
      have := hL 0 (Nat.succ_pos _) ha
      simpa only [List.getElem_cons_zero, List.take_zero, List.append_nil] using this
    have := nodup_reg_aux L (A ++ [a]) ?_ ?_ ?_
    · simpa using this
    · intro b hb
      exact hw b (by simpa using hb)
    · cases ha : a.free
      · rw [List.filter_append, List.map_append, List.nodup_append]
        refine ⟨hA, by simp [ha], ?_⟩
        intro x hx y hy
        simp only [List.mem_map, List.mem_filter] at hx
        have hy' : y = a.fac := by simpa [ha] using hy
        obtain ⟨b, ⟨hbA, hbreg⟩, rfl⟩ := hx
        subst hy'
        intro heq
        apply h0 ha
        have hb0 : b.off = 0 := hw b (by simp [hbA]) (by simpa using hbreg)
        simp only [pairs, List.mem_toFinset, List.mem_map]
        exact ⟨b, hbA, by simp [Atom.pair, heq, hb0]⟩
      · simpa [List.filter_append, ha] using hA
    · intro t ht hreg
      have := hL (t + 1) (by simp; omega) (by simpa using hreg)
      simpa [List.take_succ_cons, List.append_assoc] using this

/-- In a valid sequence of well-formed atoms after well-formed atoms `pre` whose regular atoms
are distinct facilities, the regular atoms are distinct facilities. -/
theorem ValidSeq.nodup_reg (hP : P.Good n) (hd0 : ∀ j i, 0 ≤ d j i) {f η : ℚ}
    (hf : n * η < f) {p : ℕ} {pre H : List (Atom m)} (hv : ValidSeq P d f η p pre H)
    (hwf : ∀ a ∈ pre ++ H, a.WF P.K)
    (hpre : ((pre.filter fun a ↦ !a.free).map Atom.fac).Nodup) :
    (((pre ++ H).filter fun a ↦ !a.free).map Atom.fac).Nodup :=
  nodup_reg_aux H pre (fun a ha ↦ (hwf a ha).1) hpre fun t ht hreg ↦
    (hv.1 t ht).not_mem hP hd0 hf hreg

/-- A valid sequence of well-formed atoms has at most `m` regular atoms. -/
theorem ValidSeq.nReg_le (hP : P.Good n) (hd0 : ∀ j i, 0 ≤ d j i) {f η : ℚ}
    (hf : n * η < f) {p : ℕ} {pre H : List (Atom m)} (hv : ValidSeq P d f η p pre H)
    (hwf : ∀ a ∈ H, a.WF P.K) : (H.filter fun a ↦ !a.free).length ≤ m := by
  have h := nodup_reg_aux H [] (fun a ha ↦ (hwf a (by simpa using ha)).1) (by simp)
    fun t ht hreg hmem ↦ (hv.1 t ht).not_mem hP hd0 hf hreg
      (pairs_mono (List.subset_append_right _ _) (by simpa using hmem))
  have := h.length_le_card
  rw [List.length_map, Fintype.card_fin] at this
  simpa using this

/-! ### The validity calculus -/

theorem ValidAt.mono_prefix {f η : ℚ} {p : ℕ} {pre pre' : List (Atom m)} {h : Atom m}
    (hv : ValidAt P d f η p pre h) (hsub : pairs pre' ⊆ pairs pre) : ValidAt P d f η p pre' h := by
  rcases hv with hv | ⟨S, hS, hS0, hS'⟩
  · exact .inl hv
  · exact .inr ⟨S, hsub.trans hS, hS0, hS'⟩

theorem ValidAt.mono_η {f η η' : ℚ} (hη : η ≤ η') {p : ℕ}
    {pre : List (Atom m)} {h : Atom m} (hv : ValidAt P d f η p pre h) :
    ValidAt P d f η' p pre h := by
  rcases hv with hv | ⟨S, hS, hS0, hS'⟩
  · exact .inl hv
  · refine .inr ⟨S, hS, hS0, ?_⟩
    have hle : f - n * η' ≤ f - n * η := by nlinarith
    cases hb : typ1 p <;> simp only [OpenT, hb, cond] at hS' ⊢
    · obtain ⟨T, h1, h2, h3, h4⟩ := hS'
      exact ⟨T, h1, h2, hle.trans h3, h4⟩
    · exact hle.trans hS'

/-- An atom that is openable with respect to its prefix (`η = 0`) is valid. -/
theorem ValidAt.of_open {f η : ℚ} {p : ℕ} {pre : List (Atom m)} {h : Atom m}
    (hpre : ∀ a ∈ pre, 0 ≤ a.off) (hη : 0 ≤ η)
    (ho : OpenT P d (typ1 p) f 0 (P.θseq p) (profL P.K d pre) h.fac) :
    ValidAt P d f η p pre h := by
  refine ValidAt.mono_η hη (.inr ⟨pairs pre, subset_rfl, fun q hq ↦ ?_, ?_⟩)
  · simp only [pairs, List.mem_toFinset, List.mem_map] at hq
    obtain ⟨a, ha, rfl⟩ := hq
    exact hpre a ha
  · simpa [profL] using ho

/-- A free copy at offset `0` and the regular facility have the same pair. -/
theorem pairs_toRegular (X Y : List (Atom m)) (z : Fin m) :
    pairs (X ++ ⟨z, 0, true⟩ :: Y) = pairs (X ++ ⟨z, 0, false⟩ :: Y) := by
  simp [pairs, Atom.pair]

/-- The pairs of a list with one atom singled out. -/
private theorem pairs_cons_mid (A B : List (Atom m)) (a : Atom m) :
    pairs (A ++ a :: B) = insert a.pair (pairs (A ++ B)) := by
  ext q
  simp only [pairs, List.mem_toFinset, List.map_append, List.map_cons, List.mem_append,
    List.mem_cons, mem_insert]
  tauto

end BCFGJPSSV26.Greedy


