-- Prove2me | Definitions.Def_BCFGJPSSV26_Combine_Algorithm
-- name    : BCFGJPSSV26_Combine_Algorithm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:54:09.235074+00:00
-- url     : https://prove2.me/theorems/fc202c27-4999-42e3-8a59-2f83244130d9
-- title:
--   BCFGJPSSV26.Combine.Algorithm — The algorithm of Theorem 1.1
-- statement:
--   This is module `BCFGJPSSV26.Combine.Algorithm` of the Lean 4 formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)), from the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (formalized with Claude Code, Apache-2.0).
--
--   The algorithm of [BCFGJPSSV26a, Section 1.1, step (ii)] that combines Theorems 1.2 and 1.3, for
--   given algorithms `A₂` (Theorem 1.2, for a fixed `ε`) and `A₃` (Theorem 1.3, given a fixed
--   accuracy `ε`, with exponent `e`). On an instance `I` with `k₀ = min(k, m)` and
--   `c = K ⌈log₂(n + 1)⌉ + 1`, where `c - 1 ≥ C log n / ε²` (`BCFGJPSSV26.Combine.Prm.cnt`):
--
--   * if `k₀ > c`, it runs `A₂` with `k₀ - c` centers, which opens at most `k₀` facilities;
--   * for each `j < min(c, k₀)`, it runs `A₃` with `k₀ - j` centers and `L = M c`, on its own block of
--     coins;
--   * it outputs the cheapest of the outputs that are lists of at most `k` distinct facilities, or
--     `[0]` if there is none (`BCFGJPSSV26.Combine.best`).
--
--   Costs are computed exactly, from the table of distances (`BCFGJPSSV26.Combine.costQ`), and agree
--   with `BCFGJPSSV26.Instance.cost` on lists of facilities (`BCFGJPSSV26.Combine.costQ_eq`). The
--   output is a cheapest valid candidate (`BCFGJPSSV26.Combine.Prm.cost_alg_le`) and always a list of
--   at most `k` distinct facilities (`BCFGJPSSV26.Combine.Prm.isCenterList_alg`). Costs and centers do
--   not depend on `k`, so they are the same in the instances with fewer centers given to `A₂` and
--   `A₃` (`BCFGJPSSV26.Combine.setK`).
--
--   The coins: the runs of `A₃` read consecutive blocks of `blockLen I` coins, of which run `j` reads
--   the first `stableTime e (I_j, L)`, its number of coins. The algorithm keeps the first
--   `coinLen I = c · blockLen I` coins (`BCFGJPSSV26.Combine.Prm.alg`).
--
--   **Contents.** The module is published as a whole: 38 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BCFGJPSSV26_Combine_Algorithm`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Combine/Algorithm.lean

module

public import Definitions.Def_BCFGJPSSV26_Model
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Length
public import Mathlib.Data.Nat.Size

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `BCFGJPSSV26.Combine.Algorithm` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# The algorithm of Theorem 1.1

The algorithm of [BCFGJPSSV26a, Section 1.1, step (ii)] that combines Theorems 1.2 and 1.3, for
given algorithms `A₂` (Theorem 1.2, for a fixed `ε`) and `A₃` (Theorem 1.3, given a fixed
accuracy `ε`, with exponent `e`). On an instance `I` with `k₀ = min(k, m)` and
`c = K ⌈log₂(n + 1)⌉ + 1`, where `c - 1 ≥ C log n / ε²` (`BCFGJPSSV26.Combine.Prm.cnt`):

* if `k₀ > c`, it runs `A₂` with `k₀ - c` centers, which opens at most `k₀` facilities;
* for each `j < min(c, k₀)`, it runs `A₃` with `k₀ - j` centers and `L = M c`, on its own block of
  coins;
* it outputs the cheapest of the outputs that are lists of at most `k` distinct facilities, or
  `[0]` if there is none (`BCFGJPSSV26.Combine.best`).

Costs are computed exactly, from the table of distances (`BCFGJPSSV26.Combine.costQ`), and agree
with `BCFGJPSSV26.Instance.cost` on lists of facilities (`BCFGJPSSV26.Combine.costQ_eq`). The
output is a cheapest valid candidate (`BCFGJPSSV26.Combine.Prm.cost_alg_le`) and always a list of
at most `k` distinct facilities (`BCFGJPSSV26.Combine.Prm.isCenterList_alg`). Costs and centers do
not depend on `k`, so they are the same in the instances with fewer centers given to `A₂` and
`A₃` (`BCFGJPSSV26.Combine.setK`).

The coins: the runs of `A₃` read consecutive blocks of `blockLen I` coins, of which run `j` reads
the first `stableTime e (I_j, L)`, its number of coins. The algorithm keeps the first
`coinLen I = c · blockLen I` coins (`BCFGJPSSV26.Combine.Prm.alg`).
-/

@[expose] public section

namespace BCFGJPSSV26.Combine

open Encoding

/-! ### Instances with another number of centers -/

/-- The instance with `k` centers. -/
def setK (I : Instance) (k : ℕ) : Instance := { I with k := k }

@[simp] theorem setK_n (I : Instance) (k : ℕ) : (setK I k).n = I.n := rfl
@[simp] theorem setK_m (I : Instance) (k : ℕ) : (setK I k).m = I.m := rfl
@[simp] theorem setK_k (I : Instance) (k : ℕ) : (setK I k).k = k := rfl

theorem setK_valid {I : Instance} (hI : I.Valid) {k : ℕ} (hk : 1 ≤ k) : (setK I k).Valid :=
  ⟨hk, hI.one_le_m, hI.nonneg, hI.self, hI.comm, hI.triangle⟩

/-- The encoding of an instance with `k` centers. -/
theorem encInstance_setK (I : Instance) (k : ℕ) :
    encInstance (setK I k) =
      encPair encNat (encPair encNat (encPair encNat (encList (encList encRat))))
        (I.n, I.m, k, distTable I) := rfl

theorem length_encInstance (I : Instance) :
    (encInstance I).length = 2 * I.n.size + 1 + (2 * I.m.size + 1 + (2 * I.k.size + 1 +
      (encList (encList encRat) (distTable I)).length)) := by
  change (frame (Nat.bits I.n) ++ (frame (Nat.bits I.m) ++ (frame (Nat.bits I.k) ++
    encList (encList encRat) (distTable I)))).length = _
  simp only [List.length_append, frame, List.length_flatMap, List.length_cons, List.length_nil,
    List.map_const', List.sum_replicate, smul_eq_mul, Nat.size_eq_bits_len]
  ring

/-- Fewer centers make a shorter encoding. -/
theorem length_encInstance_setK_le {I : Instance} {k : ℕ} (hk : k ≤ I.k) :
    (encInstance (setK I k)).length ≤ (encInstance I).length := by
  rw [length_encInstance, length_encInstance]
  have := Nat.size_le_size hk
  simp only [setK_n, setK_m, setK_k]
  change _ + (_ + (_ + (encList (encList encRat) (distTable I)).length)) ≤ _
  omega

/-- The number of clients is at most the length of the encoding: the table has a row for each. -/
theorem n_le_length (I : Instance) : I.n ≤ (encInstance I).length := by
  have h : (distTable I).length ≤ (encList (encList encRat) (distTable I)).length :=
    Turing.MultiTapeTM.length_le_length_encList _ _
  have hlen : (distTable I).length = I.n + I.m := by simp [distTable]
  rw [length_encInstance]
  omega

/-! ### Exact costs -/

/-- The least element of a list of rationals: the first element below all others, or `0`. -/
def minQ (l : List ℚ) : ℚ := (l.find? fun q ↦ l.all fun q' ↦ decide (q ≤ q')).getD 0

/-- **The first minimizer.** In a nonempty list, some element is at most all others, so the first
such element exists. -/
theorem find?_min {α : Type*} (f : α → ℚ) {l : List α} (hl : l ≠ []) :
    ∃ a, l.find? (fun a ↦ l.all fun b ↦ decide (f a ≤ f b)) = some a ∧ a ∈ l ∧
      ∀ b ∈ l, f a ≤ f b := by
  classical
  obtain ⟨a₀, ha₀, hmin⟩ := Finset.exists_min_image l.toFinset f
    (List.toFinset_nonempty_iff l |>.2 hl)
  have hsome : (l.find? fun a ↦ l.all fun b ↦ decide (f a ≤ f b)).isSome := by
    rw [List.find?_isSome]
    refine ⟨a₀, List.mem_toFinset.1 ha₀, ?_⟩
    rw [List.all_eq_true]
    exact fun b hb ↦ decide_eq_true (hmin b (List.mem_toFinset.2 hb))
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1 hsome
  have hp := List.find?_some ha
  rw [List.all_eq_true] at hp
  exact ⟨a, ha, List.mem_of_find?_eq_some ha, fun b hb ↦ of_decide_eq_true (hp b hb)⟩

theorem minQ_spec {l : List ℚ} (hl : l ≠ []) : minQ l ∈ l ∧ ∀ q ∈ l, minQ l ≤ q := by
  obtain ⟨a, ha, hmem, hmin⟩ := find?_min (fun q : ℚ ↦ q) hl
  unfold minQ
  rw [ha]
  exact ⟨hmem, hmin⟩

/-- The cost of a list `S` of facilities, computed from `n` and the table `T` of distances: the
sum over the rows `j < n` of the least entry `T[j][n + i]` for `i ∈ S`. -/
def costQ (n : ℕ) (T : List (List ℚ)) (S : List ℕ) : ℚ :=
  ((List.range (min T.length n)).map fun j ↦ minQ (S.map fun i ↦ (T.getD j []).getD (n + i) 0)).sum

theorem distTable_entry (I : Instance) {j i : ℕ} (hj : j < I.n) (hi : i < I.m) :
    ((distTable I).getD j []).getD (I.n + i) 0 = I.d (.inl ⟨j, hj⟩) (.inr ⟨i, hi⟩) := by
  have hj' : j < (distTable I).length := by simp [distTable]; omega
  rw [List.getD_eq_getElem?_getD (l := distTable I), List.getElem?_eq_getElem hj',
    Option.getD_some]
  have hi' : I.n + i < ((distTable I)[j]).length := by simp [distTable]; omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some]
  simp only [distTable, List.getElem_ofFn]
  congr
  · exact finSumFinEquiv_symm_apply_castAdd (n := I.m) ⟨j, hj⟩
  · exact finSumFinEquiv_symm_apply_natAdd (m := I.n) ⟨i, hi⟩

/-- **The exact cost of a list of facilities** is its cost. -/
theorem costQ_eq (I : Instance) {S : List ℕ} (hS : S ≠ []) (hm : ∀ i ∈ S, i < I.m) :
    (costQ I.n (distTable I) S : ℝ) = I.cost (I.centers S) := by
  have hlen : min (distTable I).length I.n = I.n := by simp [distTable]
  unfold costQ Instance.cost
  rw [hlen]
  have hrange : ∀ g : ℕ → ℚ, (List.range I.n).map g = List.ofFn fun j : Fin I.n ↦ g j := by
    intro g
    rw [List.ofFn_eq_map, ← List.map_coe_finRange_eq_range, List.map_map]
    rfl
  rw [hrange, List.sum_ofFn, Rat.cast_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  set l := S.map fun i ↦ ((distTable I).getD j []).getD (I.n + i) 0 with hl
  have hl0 : l ≠ [] := by simpa [hl] using hS
  obtain ⟨hmem, hle⟩ := minQ_spec hl0
  obtain ⟨i₀, hi₀, hq⟩ := List.mem_map.1 hmem
  have hi₀m := hm i₀ hi₀
  have hc₀ : (⟨i₀, hi₀m⟩ : Fin I.m) ∈ I.centers S := by simp [Instance.centers, hi₀]
  have : Nonempty (I.centers S) := ⟨⟨_, hc₀⟩⟩
  have hbdd : BddBelow (Set.range fun i : I.centers S ↦ I.dist j i) :=
    (Set.finite_range _).bddBelow
  refine le_antisymm ?_ ?_
  · refine le_ciInf fun ⟨i, hi⟩ ↦ ?_
    have hiS : i.1 ∈ S := by simpa [Instance.centers] using hi
    have := hle _ (List.mem_map.2 ⟨i.1, hiS, rfl⟩)
    rw [distTable_entry I j.2 i.2] at this
    simp only [Fin.eta] at this
    unfold Instance.dist
    exact_mod_cast this
  · refine (ciInf_le hbdd ⟨_, hc₀⟩).trans (le_of_eq ?_)
    rw [← hq, distTable_entry I j.2 hi₀m]
    rfl

/-! ### Choosing the cheapest valid candidate -/

/-- Whether `S` is a list of at most `k` distinct facilities among `m`. -/
def valid (m k : ℕ) (S : List ℕ) : Bool :=
  !S.isEmpty && decide S.Nodup && S.all (fun i ↦ decide (i < m)) && decide (S.length ≤ k)

theorem valid_iff {m k : ℕ} {S : List ℕ} :
    valid m k S = true ↔ S ≠ [] ∧ S.Nodup ∧ (∀ i ∈ S, i < m) ∧ S.length ≤ k := by
  simp [valid, List.all_eq_true, and_assoc]

/-- The cheapest of the lists `vs`, the first one if several are, or `[0]` if there is none. -/
def bestOf (n : ℕ) (T : List (List ℚ)) (vs : List (List ℕ)) : List ℕ :=
  (vs.find? fun S ↦ vs.all fun S' ↦ decide (costQ n T S ≤ costQ n T S')).getD [0]

/-- The cheapest of the candidates `cs` that are lists of at most `k` distinct facilities, or `[0]`
if there is none. -/
def best (n m k : ℕ) (T : List (List ℚ)) (cs : List (List ℕ)) : List ℕ :=
  bestOf n T (cs.filter (valid m k))

theorem best_mem_or (n m k : ℕ) (T : List (List ℚ)) (cs : List (List ℕ)) :
    best n m k T cs ∈ cs.filter (valid m k) ∨ best n m k T cs = [0] := by
  unfold best bestOf
  cases h : (cs.filter (valid m k)).find? _ with
  | none => exact .inr rfl
  | some S => exact .inl (List.mem_of_find?_eq_some h)

/-- The output is always a list of at most `k` distinct facilities. -/
theorem valid_best {n m k : ℕ} (hm : 1 ≤ m) (hk : 1 ≤ k) (T : List (List ℚ))
    (cs : List (List ℕ)) : valid m k (best n m k T cs) = true := by
  rcases best_mem_or n m k T cs with h | h
  · exact (List.mem_filter.1 h).2
  · rw [h, valid_iff]
    refine ⟨by simp, by simp, fun i hi ↦ ?_, by simpa using hk⟩
    rw [List.mem_singleton] at hi
    omega

/-- **The output is a cheapest valid candidate.** -/
theorem costQ_best_le {n m k : ℕ} (T : List (List ℚ)) {cs : List (List ℕ)} {S : List ℕ}
    (hS : S ∈ cs) (hv : valid m k S = true) :
    valid m k (best n m k T cs) = true ∧ costQ n T (best n m k T cs) ≤ costQ n T S := by
  have hS' : S ∈ cs.filter (valid m k) := List.mem_filter.2 ⟨hS, hv⟩
  obtain ⟨a, ha, hmem, hmin⟩ := find?_min (costQ n T) (List.ne_nil_of_mem hS')
  have hb : best n m k T cs = a := by
    unfold best bestOf
    rw [ha]
    rfl
  rw [hb]
  exact ⟨(List.mem_filter.1 hmem).2, hmin S hS'⟩

/-! ### The algorithm -/

/-- The parameters of the algorithm: the algorithms `A₂` and `A₃`, the exponent `e` of `A₃`, the
constant `K` with `C log n / ε² ≤ K ⌈log₂(n + 1)⌉`, and the factor `M` of `L = M c`. -/
structure Prm where
  /-- The algorithm of Theorem 1.2. -/
  A₂ : Instance → List ℕ
  /-- The algorithm of Theorem 1.3, given a fixed accuracy. -/
  A₃ : (Instance × ℕ) × List Bool → List ℕ
  /-- The exponent of the running time of `A₃`. -/
  e : ℕ
  /-- The constant of the number of extra centers. -/
  K : ℕ
  /-- The factor of `L`. -/
  M : ℕ

/-- The number of centers, capped at the number of facilities. -/
def k₀ (I : Instance) : ℕ := min I.k I.m

/-- The instance of run `j` of `A₃`: `k₀ - j` centers. -/
def atK (I : Instance) (j : ℕ) : Instance := setK I (k₀ I - j)

namespace Prm

variable (P : Prm)

/-- The number `c ≥ C log n / ε² + 1` of runs of `A₃`, at most. -/
def cnt (I : Instance) : ℕ := P.K * I.n.size + 1

/-- The number `L = M c ≥ 1/β` given to `A₃`. -/
def Lp (I : Instance) : ℕ := P.M * P.cnt I

/-- The number of runs of `A₃`. -/
def runs (I : Instance) : ℕ := min (P.cnt I) (k₀ I)

/-- The coins of a run of `A₃`, enough for every run. -/
def blockLen (I : Instance) : ℕ := 2 ^ (P.e * P.Lp I) * ((encInstance I).length + 2) ^ P.e

/-- The number of coins the algorithm reads. -/
def coinLen (I : Instance) : ℕ := P.cnt I * P.blockLen I

/-- The coins of run `j` of `A₃`: `stableTime e (I_j, L)` coins after `j` blocks. -/
def coins (I : Instance) (r : List Bool) (j : ℕ) : List Bool :=
  (r.drop (j * P.blockLen I)).take (stableTime P.e (atK I j, P.Lp I))

/-- Run `j` of `A₃`. -/
def run₃ (x : Instance × List Bool) (j : ℕ) : List ℕ :=
  P.A₃ ((atK x.1 j, P.Lp x.1), P.coins x.1 x.2 j)

/-- The run of `A₂`, with `k₀ - c` centers, if `k₀ > c`. -/
def run₂ (I : Instance) : List (List ℕ) :=
  if P.cnt I < k₀ I then [P.A₂ (setK I (k₀ I - P.cnt I))] else []

/-- The candidates. -/
def cands (x : Instance × List Bool) : List (List ℕ) :=
  P.run₂ x.1 ++ (List.range (P.runs x.1)).map (P.run₃ x)

/-- **The algorithm, on its coins.** The cheapest valid candidate. -/
def alg' (x : Instance × List Bool) : List ℕ :=
  best x.1.n x.1.m x.1.k (distTable x.1) (P.cands x)

/-- **The algorithm**: the algorithm on the first `coinLen I` coins. -/
def alg (x : Instance × List Bool) : List ℕ := P.alg' (x.1, x.2.take (P.coinLen x.1))

/-- The output is always a list of at most `k` distinct facilities. -/
theorem isCenterList_alg {I : Instance} (hI : I.Valid) (r : List Bool) :
    I.IsCenterList (P.alg (I, r)) ∧ (P.alg (I, r)).length ≤ I.k := by
  have h := (valid_iff.1 (valid_best (n := I.n) hI.one_le_m hI.one_le_k (distTable I)
    (P.cands (I, r.take (P.coinLen I)))))
  exact ⟨⟨h.1, h.2.1, h.2.2.1⟩, h.2.2.2⟩

/-- **The output is at most as expensive as any valid candidate.** -/
theorem cost_alg_le {I : Instance} (r : List Bool) {S : List ℕ}
    (hS : S ∈ P.cands (I, r.take (P.coinLen I))) (hv : I.IsCenterList S) (hk : S.length ≤ I.k) :
    I.cost (I.centers (P.alg (I, r))) ≤ I.cost (I.centers S) := by
  have hvS : valid I.m I.k S = true := valid_iff.2 ⟨hv.1, hv.2.1, hv.2.2, hk⟩
  obtain ⟨hb, hle⟩ := costQ_best_le (n := I.n) (distTable I) hS hvS
  have hb' := valid_iff.1 hb
  change I.cost (I.centers (best I.n I.m I.k (distTable I) _)) ≤ _
  rw [← costQ_eq I hb'.1 hb'.2.2.1, ← costQ_eq I hv.1 hv.2.2]
  exact_mod_cast hle

end Prm

end BCFGJPSSV26.Combine


