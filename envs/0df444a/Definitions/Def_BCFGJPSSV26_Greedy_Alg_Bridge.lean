-- Prove2me | Definitions.Def_BCFGJPSSV26_Greedy_Alg_Bridge
-- name    : BCFGJPSSV26_Greedy_Alg_Bridge
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:56:02.255222+00:00
-- url     : https://prove2.me/theorems/8527e182-6324-4145-a130-7ae0423cca8e
-- title:
--   BCFGJPSSV26.Greedy.Alg.Bridge — From the algorithm to the analysis
-- statement:
--   This is module `BCFGJPSSV26.Greedy.Alg.Bridge` of the Lean 4 formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)), from the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (formalized with Claude Code, Apache-2.0).
--
--   The algorithm of `Greedy/Alg/Defs.lean` works on lists and natural numbers; the analysis on a
--   space `X : Space n m` and atoms `Atom m`. Here:
--
--   * **Hypotheses** (`BCFGJPSSV26.Greedy.Ctx.Hyp`): the context reads the space `X` (its table holds
--     the distances `X.d j i ∈ [1, M]`), `2 ≤ n`, `1 ≤ k < min (n, m)`, and the parameters satisfy the
--     relations of `BCFGJPSSV26.Greedy.ipar` that the proofs use. They hold for the context of a good
--     input (`BCFGJPSSV26.Greedy.hyp_ctx`).
--   * **Decoding** (`BCFGJPSSV26.Greedy.Ctx.decA`): `(i, 0)` is the regular atom `⟨i, 0, false⟩`,
--     `(i, g + 1)` the free atom `⟨i, u g, true⟩`; atoms are in range (`BCFGJPSSV26.Greedy.Ctx.AtomOK`)
--     when `i < m` and `g ≤ 2^Pu`.
--   * **Equalities**: the profile, the left sides and the tests of the algorithm are those of the
--     analysis on the decoded atoms (`BCFGJPSSV26.Greedy.Ctx.prof_getD`,
--     `BCFGJPSSV26.Greedy.Ctx.testT_eq`, …), and so are the counts of regular atoms
--     (`BCFGJPSSV26.Greedy.Ctx.nRegA_eq`).
--
--   **Contents.** The module is published as a whole: 48 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BCFGJPSSV26_Greedy_Alg_Bridge`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Greedy/Alg/Bridge.lean

module

public import Definitions.Def_BCFGJPSSV26_Greedy_Alg_Defs
public import Definitions.Def_BCFGJPSSV26_Greedy_Valid

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `BCFGJPSSV26.Greedy.Alg.Bridge` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# From the algorithm to the analysis

The algorithm of `Greedy/Alg/Defs.lean` works on lists and natural numbers; the analysis on a
space `X : Space n m` and atoms `Atom m`. Here:

* **Hypotheses** (`BCFGJPSSV26.Greedy.Ctx.Hyp`): the context reads the space `X` (its table holds
  the distances `X.d j i ∈ [1, M]`), `2 ≤ n`, `1 ≤ k < min (n, m)`, and the parameters satisfy the
  relations of `BCFGJPSSV26.Greedy.ipar` that the proofs use. They hold for the context of a good
  input (`BCFGJPSSV26.Greedy.hyp_ctx`).
* **Decoding** (`BCFGJPSSV26.Greedy.Ctx.decA`): `(i, 0)` is the regular atom `⟨i, 0, false⟩`,
  `(i, g + 1)` the free atom `⟨i, u g, true⟩`; atoms are in range (`BCFGJPSSV26.Greedy.Ctx.AtomOK`)
  when `i < m` and `g ≤ 2^Pu`.
* **Equalities**: the profile, the left sides and the tests of the algorithm are those of the
  analysis on the decoded atoms (`BCFGJPSSV26.Greedy.Ctx.prof_getD`,
  `BCFGJPSSV26.Greedy.Ctx.testT_eq`, …), and so are the counts of regular atoms
  (`BCFGJPSSV26.Greedy.Ctx.nRegA_eq`).
-/

@[expose] public section

namespace BCFGJPSSV26.Greedy

namespace Ctx

variable (C : Ctx)

/-- The parameters of the analysis. -/
def par : Par := ⟨C.ip.δ, C.ip.ε, C.ip.η, C.ip.K, C.ip.R⟩

/-- **The hypotheses on a context** reading the space `X`. -/
structure Hyp (X : Space C.ip.n C.ip.m) : Prop where
  dist_eq : ∀ (j : Fin C.ip.n) (i : Fin C.ip.m), C.dist j i = X.d j i
  dist_nonneg : ∀ j i, 0 ≤ C.dist j i
  d1 : ∀ j i, 1 ≤ X.d j i
  dM : ∀ j i, X.d j i ≤ C.ip.M
  two_le_n : 2 ≤ C.ip.n
  one_le_k : 1 ≤ C.ip.k
  k_lt_n : C.ip.k < C.ip.n
  k_lt_m : C.ip.k < C.ip.m
  good : C.par.Good C.ip.n
  one_le_M : 1 ≤ C.ip.M
  η_eq : C.ip.η = C.ip.δ ^ 2 / (100 * (C.ip.n : ℚ) ^ 2)
  fmin_eq : C.ip.fmin = C.ip.δ
  fmax_eq : C.ip.fmax = 4 * C.ip.n * C.ip.M
  one_le_R : 1 ≤ C.ip.R
  θ_last : C.ip.fmax + γ * C.ip.M ≤ C.θ (C.ip.R - 1)
  K_eq : C.ip.K = 2 * C.θ C.ip.R
  fstep : (C.ip.fmax - C.ip.fmin) / 2 ^ C.ip.Pf ≤ C.ip.η
  ustep : C.ip.K / 2 ^ C.ip.Pu ≤ C.ip.η
  L_ge : C.ip.m + 4 ≤ C.ip.L

/-- An atom is **in range**: a facility `i < m`, and an offset index at most `2^Pu`. -/
def AtomOK (a : AAtom) : Prop := a.1 < C.ip.m ∧ a.2 ≤ 2 ^ C.ip.Pu + 1

/-- All atoms of a solution are in range. -/
def SolOK (H : List (List AAtom)) : Prop := ∀ a ∈ H.flatten, C.AtomOK a

variable {C}
variable {X : Space C.ip.n C.ip.m} (hX : C.Hyp X)
include hX

theorem Hyp.one_le_m : 1 ≤ C.ip.m := by have := hX.k_lt_m; have := hX.one_le_k; omega

theorem Hyp.m_pos : 0 < C.ip.m := hX.one_le_m

/-- Decode an atom. -/
def decA (a : AAtom) : Atom C.ip.m :=
  ⟨⟨a.1 % C.ip.m, Nat.mod_lt _ hX.m_pos⟩, C.aoff a, a.2 != 0⟩

/-- Decode a sequence. -/
def decS (S : List AAtom) : List (Atom C.ip.m) := S.map (decA hX)

/-- Decode a solution. -/
def decH (H : List (List AAtom)) : List (List (Atom C.ip.m)) := H.map (decS hX)

theorem decS_append (S T : List AAtom) : decS hX (S ++ T) = decS hX S ++ decS hX T :=
  List.map_append ..

theorem decH_flatten (H : List (List AAtom)) : (decH hX H).flatten = decS hX H.flatten := by
  simp only [decH, decS, List.map_flatten]
  rfl

theorem Hyp.K_pos : 0 < C.ip.K := by
  have h1 : 2 * C.par.θ C.par.R ≤ C.ip.K := hX.good.K_ge
  have h2 := C.par.one_le_θ C.par.R
  linarith

omit hX in
theorem off_nonneg (hK : 0 ≤ C.ip.K) (g : ℕ) : 0 ≤ C.off g := by
  unfold off
  positivity

omit hX in
theorem off_le (hK : 0 ≤ C.ip.K) {g : ℕ} (hg : g ≤ 2 ^ C.ip.Pu) : C.off g ≤ C.ip.K := by
  unfold off
  have h2 : (0 : ℚ) < 2 ^ C.ip.Pu := by positivity
  have hg' : (g : ℚ) ≤ 2 ^ C.ip.Pu := by exact_mod_cast hg
  rw [div_le_iff₀ h2]
  exact mul_le_mul_of_nonneg_left hg' hK

omit hX in
theorem aoff_nonneg (hK : 0 ≤ C.ip.K) (a : AAtom) : 0 ≤ C.aoff a := by
  unfold aoff
  split_ifs
  · exact le_rfl
  · exact off_nonneg hK _

theorem decA_fac {a : AAtom} (ha : a.1 < C.ip.m) : (decA hX a).fac = ⟨a.1, ha⟩ := by
  simp [decA, Nat.mod_eq_of_lt ha]

theorem decA_pair {a : AAtom} (ha : a.1 < C.ip.m) : (decA hX a).pair = (⟨a.1, ha⟩, C.aoff a) := by
  simp [Atom.pair, decA, Nat.mod_eq_of_lt ha]

/-- Decoded atoms in range are well formed. -/
theorem decA_wf {a : AAtom} (ha : C.AtomOK a) : (decA hX a).WF C.ip.K := by
  obtain ⟨i, g⟩ := a
  have hK := hX.K_pos
  refine ⟨fun h ↦ ?_, aoff_nonneg hK.le _, ?_⟩
  · have hg : g = 0 := by simpa [decA] using h
    simp [decA, aoff, hg]
  · rcases g with _ | g
    · simp [decA, aoff, hK.le]
    · have hg : g ≤ 2 ^ C.ip.Pu := by have := ha.2; simp only at this; omega
      simp only [decA, aoff, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel]
      exact off_le hK.le hg

/-! ### The equalities -/

omit hX in
theorem prof_getD_eq (S : List AAtom) {j : ℕ} (hj : j < C.ip.n) :
    (C.prof S).getD j 0 = S.foldr (fun a acc ↦ min (C.adist j a) acc) C.ip.K := by
  simp [prof, List.getD_eq_getElem?_getD, hj]

/-- **The profile of the algorithm is that of the analysis.** -/
theorem prof_getD {S : List AAtom} (hS : ∀ a ∈ S, C.AtomOK a) (j : Fin C.ip.n) :
    (C.prof S).getD j 0 = profL C.par.K X.d (decS hX S) j := by
  rw [prof_getD_eq S j.isLt]
  induction S with
  | nil => rfl
  | cons a S ih =>
    have ha := hS a List.mem_cons_self
    rw [List.foldr_cons, ih fun b hb ↦ hS b (List.mem_cons_of_mem _ hb)]
    simp only [profL, pairs, decS, List.map_cons, List.toFinset_cons]
    rw [profF_insert, decA_pair hX ha.1]
    have hd : C.dist j a.1 = X.d j ⟨a.1, ha.1⟩ := hX.dist_eq j ⟨a.1, ha.1⟩
    simp only [adist, hd]

omit hX in
theorem prof_length (S : List AAtom) : (C.prof S).length = C.ip.n := by
  simp [prof]

omit hX in
theorem foldr_min_init (g : AAtom → ℚ) (S : List AAtom) (x y : ℚ) :
    S.foldr (fun a acc ↦ min (g a) acc) (min x y) =
      min (S.foldr (fun a acc ↦ min (g a) acc) x) y := by
  induction S with
  | nil => rfl
  | cons a S ih => simp only [List.foldr_cons, ih, min_assoc]

omit hX in
theorem foldr_min_le_init (g : AAtom → ℚ) (S : List AAtom) (x : ℚ) :
    S.foldr (fun a acc ↦ min (g a) acc) x ≤ x := by
  induction S with
  | nil => exact le_rfl
  | cons a S ih => exact (min_le_right _ _).trans ih

omit hX in
/-- The profile of a concatenation is the pointwise minimum. -/
theorem prof_append (S T : List AAtom) :
    C.prof (S ++ T) = List.zipWith min (C.prof S) (C.prof T) := by
  unfold prof
  rw [List.zipWith_map, List.zipWith_self]
  refine List.map_congr_left fun j _ ↦ ?_
  rw [List.foldr_append]
  have h := foldr_min_init (C.adist j) S C.ip.K (T.foldr (fun a acc ↦ min (C.adist j a) acc) C.ip.K)
  rwa [min_eq_right (foldr_min_le_init _ T C.ip.K)] at h

omit hX in
theorem list_sum_map_range (g : ℕ → ℚ) (n : ℕ) :
    ((List.range n).map g).sum = ∑ i ∈ Finset.range n, g i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.sum_range_succ, Finset.sum_range_succ, ih]

omit hX in
theorem list_sum_filter_range (p : ℕ → Bool) (g : ℕ → ℚ) (n : ℕ) :
    (((List.range n).filter p).map g).sum = ∑ i ∈ Finset.range n, if p i then g i else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.filter_append, List.map_append, List.sum_append, ih,
      Finset.sum_range_succ]
    by_cases h : p n <;> simp [h]

omit hX in
theorem list_sum_filter_eq {n : ℕ} (p : ℕ → Bool) (p' : Fin n → Prop) [DecidablePred p']
    (hp : ∀ j : Fin n, p j = true ↔ p' j) (g : ℕ → ℚ) (g' : Fin n → ℚ)
    (hg : ∀ j : Fin n, g j = g' j) :
    (((List.range n).filter p).map g).sum = ∑ j ∈ Finset.univ.filter p', g' j := by
  rw [list_sum_filter_range, Finset.sum_range, Finset.sum_filter]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  by_cases h : p' j
  · simp [(hp j).2 h, h, hg j]
  · have h' : p j = false := by
      cases hpj : p j
      · rfl
      · exact absurd ((hp j).1 hpj) h
    simp [h', h]

omit hX in
theorem sumC_eq (g : ℕ → ℚ) (g' : Fin C.ip.n → ℚ) (h : ∀ j : Fin C.ip.n, g j = g' j) :
    C.sumC g = ∑ j, g' j := by
  unfold sumC
  rw [list_sum_map_range, Finset.sum_range]
  exact Finset.sum_congr rfl fun j _ ↦ h j

omit hX in
theorem foldl_max_le_iff {l : List ℚ} {b c : ℚ} :
    l.foldl max b ≤ c ↔ b ≤ c ∧ ∀ x ∈ l, x ≤ c := by
  induction l generalizing b with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldl_cons, ih, max_le_iff, List.mem_cons, forall_eq_or_imp, and_assoc]

omit hX in
theorem foldl_max_eq_fold {n : ℕ} (l : List ℕ) (s : Finset (Fin n))
    (hl : ∀ j : ℕ, j ∈ l ↔ ∃ h : j < n, (⟨j, h⟩ : Fin n) ∈ s) (g : ℕ → ℚ) (g' : Fin n → ℚ)
    (hg : ∀ j : Fin n, g j = g' j) (b : ℚ) : (l.map g).foldl max b = s.fold max b g' := by
  have key := (foldl_max_le_iff (l := l.map g) (b := b) (c := (l.map g).foldl max b)).1 le_rfl
  refine le_antisymm (foldl_max_le_iff.2 ⟨(Finset.le_fold_max _).2 (.inl le_rfl), ?_⟩)
    ((Finset.fold_max_le _).2 ⟨key.1, fun x hx ↦ ?_⟩)
  · intro x hx
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
    obtain ⟨hjn, hjs⟩ := (hl j).1 hj
    rw [hg ⟨j, hjn⟩]
    exact (Finset.le_fold_max _).2 (.inr ⟨_, hjs, le_rfl⟩)
  · rw [← hg x]
    exact key.2 _ (List.mem_map.2 ⟨x, (hl x).2 ⟨x.isLt, hx⟩, rfl⟩)

theorem Hyp.dist_eq' {j : ℕ} (hj : j < C.ip.n) (i : Fin C.ip.m) :
    C.dist j i = X.d ⟨j, hj⟩ i :=
  hX.dist_eq ⟨j, hj⟩ i

section Tests

variable {θ : ℚ} {D : List ℚ} {D' : Fin C.ip.n → ℚ} (hD : ∀ j : Fin C.ip.n, D.getD j 0 = D' j)
include hD

omit hX in
theorem mval_eq (j : Fin C.ip.n) : C.mval θ D j = Greedy.mval C.par θ D' j := by
  simp only [mval, Greedy.mval, hD j]
  rfl

theorem mT_eq (T : ℚ) (i : Fin C.ip.m) (j : Fin C.ip.n) :
    C.mT θ D i T j = Greedy.mT C.par X.d θ D' i T j := by
  simp only [mT, Greedy.mT, gT, Greedy.gT, hD j, hX.dist_eq j i]
  rfl

theorem cnear_eq (i : Fin C.ip.m) (j : Fin C.ip.n) :
    C.cnear θ D i j = Greedy.cnear C.par X.d θ D' i j := by
  simp only [cnear, Greedy.cnear, hD j, hX.dist_eq j i]
  rfl

theorem mem_nearL (i : Fin C.ip.m) (j : ℕ) :
    j ∈ C.nearL θ D i ↔ ∃ h : j < C.ip.n, (⟨j, h⟩ : Fin C.ip.n) ∈ nearAct C.par X.d θ D' i := by
  simp only [nearL, List.mem_filter, List.mem_range, Bool.and_eq_true, decide_eq_true_eq,
    nearAct, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hj, h1, h2⟩
    have h3 : D.getD j 0 = D' ⟨j, hj⟩ := hD ⟨j, hj⟩
    refine ⟨hj, ?_, ?_⟩
    · rw [hX.dist_eq' hj] at h1
      exact h1
    · rw [h3] at h2
      exact h2
  · rintro ⟨hj, h1, h2⟩
    have h3 : D.getD j 0 = D' ⟨j, hj⟩ := hD ⟨j, hj⟩
    refine ⟨hj, ?_, ?_⟩
    · rw [hX.dist_eq' hj]
      exact h1
    · rw [h3]
      exact h2

theorem sum_nearL_filter (i : Fin C.ip.m) (q : ℕ → Bool) (q' : Fin C.ip.n → Prop)
    [DecidablePred q'] (hq : ∀ j : Fin C.ip.n, q j = true ↔ q' j) (g : ℕ → ℚ)
    (g' : Fin C.ip.n → ℚ) (hg : ∀ j : Fin C.ip.n, g j = g' j) :
    (((C.nearL θ D i).filter q).map g).sum =
      ∑ j ∈ (nearAct C.par X.d θ D' i).filter q', g' j := by
  unfold nearL nearAct
  rw [List.filter_filter, Finset.filter_filter]
  refine list_sum_filter_eq _ _ (fun j ↦ ?_) g g' hg
  rw [← hq j]
  simp only [Bool.and_eq_true, decide_eq_true_eq, hD j, hX.dist_eq j i]
  exact and_comm.trans (and_congr_left' Iff.rfl)

end Tests

/-- The left side of type 1 of the algorithm is that of the analysis. -/
theorem lhs1_eq (θ : ℚ) {D : List ℚ} {D' : Fin C.ip.n → ℚ}
    (hD : ∀ j : Fin C.ip.n, D.getD j 0 = D' j) (i : Fin C.ip.m) :
    C.lhs1 θ D i = Greedy.lhs1 C.par X.d θ D' i := by
  unfold lhs1 Greedy.lhs1
  refine sumC_eq _ _ fun j ↦ ?_
  rw [mval_eq hD j, hX.dist_eq j i]
  rfl

/-- The left side of (iii) of the algorithm is that of the analysis. -/
theorem lhs3_eq (θ T : ℚ) {D : List ℚ} {D' : Fin C.ip.n → ℚ}
    (hD : ∀ j : Fin C.ip.n, D.getD j 0 = D' j) (i : Fin C.ip.m) :
    C.lhs3 θ D i T = Greedy.lhs3 C.par X.d θ D' i T := by
  unfold lhs3 Greedy.lhs3
  refine sumC_eq _ _ fun j ↦ ?_
  rw [mT_eq hX hD T i j, hX.dist_eq j i]
  rfl

/-- The left side of (iv) of the algorithm is that of the analysis. -/
theorem lhs4_eq (θ T : ℚ) {D : List ℚ} {D' : Fin C.ip.n → ℚ}
    (hD : ∀ j : Fin C.ip.n, D.getD j 0 = D' j) (i i₀ : Fin C.ip.m) :
    C.lhs4 θ D i T i₀ = Greedy.lhs4 C.par X.d θ D' i T i₀ := by
  unfold lhs4 Greedy.lhs4
  refine sumC_eq _ _ fun j ↦ ?_
  rw [mT_eq hX hD T i j, hX.dist_eq j i₀]

theorem need_eq (f θ : ℚ) {D : List ℚ} {D' : Fin C.ip.n → ℚ}
    (hD : ∀ j : Fin C.ip.n, D.getD j 0 = D' j) (i : Fin C.ip.m) :
    C.need f θ D i = Greedy.need C.par X.d f θ D' i := by
  unfold need Greedy.need
  have h1 := list_sum_filter_eq (n := C.ip.n) (fun j ↦ !(C.nearL θ D i).contains j)
    (· ∉ nearAct C.par X.d θ D' i) (fun j ↦ ?_)
    (fun j ↦ bid (C.mval θ D j) ((1 - C.ip.δ / 2) * C.dist j i))
    (fun j ↦ bid (Greedy.mval C.par θ D' j) ((1 - C.par.δ / 2) * X.d j i)) (fun j ↦ ?_)
  · have h2 := sum_nearL_filter hX hD (θ := θ) i (fun _ ↦ true) (fun _ ↦ True) (fun _ ↦ by simp)
      (fun j ↦ γ * ((1 - C.ip.δ / 2) * C.dist j i))
      (fun j ↦ γ * ((1 - C.par.δ / 2) * X.d j i)) (fun j ↦ by rw [hX.dist_eq j i]; rfl)
    rw [List.filter_true, Finset.filter_true] at h2
    rw [h1, h2, Finset.sdiff_eq_filter]
  · have hm : (C.nearL θ D i).contains j = true ↔ j ∈ nearAct C.par X.d θ D' i :=
      List.elem_iff.trans ((mem_nearL hX hD i j).trans ⟨fun ⟨_, h⟩ ↦ h, fun h ↦ ⟨j.isLt, h⟩⟩)
    simpa using hm.not
  · rw [mval_eq hD j, hX.dist_eq j i]
    rfl

theorem candT_eq (f θ : ℚ) {D : List ℚ} {D' : Fin C.ip.n → ℚ}
    (hD : ∀ j : Fin C.ip.n, D.getD j 0 = D' j) (i : Fin C.ip.m) (j₀ : Fin C.ip.n) :
    C.candT f θ D i j₀ = Greedy.candT C.par X.d f θ D' i j₀ := by
  unfold candT Greedy.candT
  have h1 := sum_nearL_filter hX hD (θ := θ) i
    (fun j ↦ decide (C.cnear θ D i j < C.cnear θ D i j₀))
    (fun j ↦ Greedy.cnear C.par X.d θ D' i j < Greedy.cnear C.par X.d θ D' i j₀)
    (fun j ↦ by simp [cnear_eq hX hD]) (C.cnear θ D i) (Greedy.cnear C.par X.d θ D' i)
    (cnear_eq hX hD i)
  have h2 := sum_nearL_filter hX hD (θ := θ) i
    (fun j ↦ decide (C.cnear θ D i j₀ ≤ C.cnear θ D i j))
    (fun j ↦ Greedy.cnear C.par X.d θ D' i j₀ ≤ Greedy.cnear C.par X.d θ D' i j)
    (fun j ↦ by simp [cnear_eq hX hD]) (fun _ ↦ 1) (fun _ ↦ 1) (fun _ ↦ rfl)
  simp only [List.map_const', List.sum_replicate, Finset.sum_const, mul_one, nsmul_eq_mul]
    at h2
  rw [need_eq hX f θ hD i, h1, h2]

theorem tstar_eq (f θ : ℚ) {D : List ℚ} {D' : Fin C.ip.n → ℚ}
    (hD : ∀ j : Fin C.ip.n, D.getD j 0 = D' j) (i : Fin C.ip.m) :
    C.tstar f θ D i = Greedy.tstar C.par X.d f θ D' i :=
  foldl_max_eq_fold _ _ (mem_nearL hX hD i) _ _ (candT_eq hX f θ hD i) θ

/-- The tests of the algorithm are those of the analysis. -/
theorem testT_eq (b : Bool) (f θ : ℚ) {D : List ℚ} {D' : Fin C.ip.n → ℚ}
    (hD : ∀ j : Fin C.ip.n, D.getD j 0 = D' j) (_hlen : D.length = C.ip.n) (i : Fin C.ip.m) :
    C.testT b f θ D i = Greedy.testT C.par X.d b f θ D' i := by
  cases b
  · simp only [testT, Greedy.testT, Bool.cond_false, test2, Greedy.test2]
    rw [Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
    rw [tstar_eq hX f θ hD i, lhs3_eq hX θ _ hD i]
    rw [and_assoc]
    refine and_congr Iff.rfl (and_congr Iff.rfl ⟨fun h i₀ ↦ ?_, fun h i₀ hi₀ ↦ ?_⟩)
    · rw [← lhs4_eq hX θ _ hD i i₀]
      exact h i₀ i₀.isLt
    · have := h ⟨i₀, hi₀⟩
      rw [← lhs4_eq hX θ _ hD i ⟨i₀, hi₀⟩] at this
      exact this
  · simp only [testT, Greedy.testT, Bool.cond_true, test1, Greedy.test1, lhs1_eq hX θ hD i]

omit hX in
/-- The time of the algorithm is that of the analysis. -/
theorem θseq_eq (p : ℕ) : C.θseq p = C.par.θseq p := rfl

/-- The counts of regular atoms agree. -/
theorem nRegA_eq (H : List (List AAtom)) : nRegA H = nReg (decH hX H) := by
  unfold nRegA nReg
  rw [decH_flatten, decS, List.filter_map, List.length_map]
  congr 2
  funext a
  simp [decA, bne]

theorem nFreeSeqA_eq (S : List AAtom) : nFreeSeqA S = nFreeSeq (decS hX S) := by
  unfold nFreeSeqA nFreeSeq
  rw [decS, List.filter_map, List.length_map]
  congr 2

omit hX in
/-- The offsets of the grid. -/
theorem aoff_free (z g : ℕ) : C.aoff (z, g + 1) = C.off g := by simp [aoff]

omit hX in
theorem off_zero : C.off 0 = 0 := by simp [off]

end Ctx

end BCFGJPSSV26.Greedy


