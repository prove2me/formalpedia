-- Prove2me | Definitions.Def_QuantumLTF_Membership_Supplement_lcgSym54Comb
-- name    : QuantumLTF_Membership_Supplement_lcgSym54Comb
-- status  : Definition
-- author  : @Robin Kothari
-- created : 2026-11-25T02:42:29.160126+00:00
-- url     : https://prove2.me/theorems/797fd9f9-06e9-5cde-ab1c-209980d3cfcb
-- title:
--   Combinatorial structures for Alonso–Schott LES bijection and Harmonic-Bucket NSIL symmetrization ($\mathrm{LcgSym54Comb}$)
-- statement:
--   Defines the pure combinatorial structures and bundled interface `LcgSym54Comb` supporting Stage B second-to-first-quantization symmetrization (`nsil_symmetrize_54`).
--
--   1. **Alonso–Schott LES $\leftrightarrow S_N$ Bijection:** A $0$-based lower exceeding sequence (`IsLES`) $s : \mathrm{Fin}\, N \to \mathbb{N}$ satisfies $s_j \le j$ for all $j < N$. Via reverse greedy row placement `greedyState`, sorted partial sub-diagrams `greedyDiag s lo hi`, unary merge keys `mergePhi k (idx, r, c)`, and fixed-point padding `padLES54` and `padPerm54`, `LcgSym54Comb` exposes the canonical bijection `lesEquivPerm` between LESs and $S_N$ together with invariant guarantees across recursive $2^\ell$-block bitonic merges.
--
--   2. **NSIL Run Decomposition, Harmonic-Bucket Schedule, and Stabilizer Algebra:** On any non-decreasing list (NSIL) $l : \mathrm{Fin}\, N \to \alpha$, defines run start `runStart`, $1$-based intra-run offset $m_i = \mathrm{runOffset}\, l\, i$, occurrence rank $\mathrm{occ}_i = \mathrm{runOcc}\, l\, i$, canonical bucket schedule `bucketPairs N` of length $\sum_{m=2}^{N} \lfloor N/m \rfloor \le N \lceil \log_2(N+2) \rceil$, and fixed-slot $2$-sort routing records `HBRec` with keys `hbKey1`, `hbKey2` and neighbor-matching pass `hbSeqPass`.
--
--   3. **Stabilizer Factorization for Equations (655)\u2013(701):** Defines the stabilizer subgroup $\mathrm{stabGroup}\, N\, l = H_l \le S_N$, the restricted LES predicate `IsLESOf N l s`, orbit decidability, and the sum factorization
--
--   $$
--   \sum_{\sigma \in S_N} f(\sigma \cdot l,\; \sigma \cdot \tau(\sigma \cdot l)^{-1}) = \sum_{y \in S_N \cdot l} \sum_{h \in H_l} f(y, h),
--   $$
--
--   connecting stabilizer coset cardinalities to the multinomial amplitudes of `multinomKet54`.
--
--   **Formalization Note** All pure definitions live in `QuantumLTF.Membership.Supplement.LcgSym54`, while the bundled structure `LcgSym54Comb` lives in `QuantumLTF.Membership.Supplement` and is proved inhabited by `lcg_sym_comb_54`.
-- source:
--   Liu, Childs, Gottesman [LCG26], First and second quantization: reversible and quantum circuits (arXiv:2411.04019, Section IV.A–C, Equations 655–701); Alonso and Schott (1995), Random Generation of Trees; Krivcenko, Nguyen, de Wolf [KNW26] (arXiv:2609.40331, Theorem 5.4).

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_QuantumLTF_Membership_Supplement_symBand54
import Definitions.Def_QuantumLTF_Membership_Supplement_bitonicTrace54

set_option autoImplicit false

/-!
# Combinatorial Definitions & Bundled Interface for `[LCG26]` Symmetrization (`theorem_5_4`)

Defines the pure combinatorial objects and bundled theorem structure `LcgSym54Comb` covering:
1. MSB bit-packing and `particleSym54` monotonicity lemmas.
2. `[LCG26, Section IV.A]` Alonso–Schott LES ↔ `S_N` bijection (`greedyState`, `greedyDiag`,
   `mergePhi`, `lesToPermFun`, `permToLES`, `padLES54`, `padPerm54`).
3. `[LCG26, Section IV.B–C]` NSIL run decomposition, Harmonic-Bucket schedule & 2-Sort
   routing records (`runStart`, `runOffset`, `runOcc`, `bucketPairs`, `HBRec`, `hbInit`,
   `hbSeqPass`), stabilizer subgroup `stabGroup`, `IsLESOf`, and Eqs. (655)–(701) sum factorization.
-/

namespace QuantumLTF.Membership.Supplement.LcgSym54

open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement

/-! ### Part 1: Alonso–Schott LES ↔ S_N Definitions -/

/-- 0-based Lower Exceeding Sequence predicate: `∀ j, s j ≤ j.1`. -/
def IsLES (N : ℕ) (s : Fin N → ℕ) : Prop :=
  ∀ j : Fin N, s j ≤ j.1

instance instDecidableIsLES (N : ℕ) : DecidablePred (IsLES N) :=
  fun _ => inferInstanceAs (Decidable (∀ _ : Fin N, _))

/-- Equivalence between `{s : Fin N → ℕ // IsLES N s}` and `(j : Fin N) → Fin (j.1 + 1)`. -/
def lesEquivPi (N : ℕ) : { s : Fin N → ℕ // IsLES N s } ≃ ((j : Fin N) → Fin (j.1 + 1)) where
  toFun s j := ⟨s.1 j, Nat.lt_succ_of_le (s.2 j)⟩
  invFun f := ⟨fun j => (f j).1, fun j => Nat.lt_succ_iff.mp (f j).isLt⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := funext fun _ => Fin.ext rfl

noncomputable instance instFintypeLES (N : ℕ) : Fintype { s : Fin N → ℕ // IsLES N s } :=
  Fintype.ofEquiv ((j : Fin N) → Fin (j.1 + 1)) (lesEquivPi N).symm

/-- Direct map `Equiv.Perm (Fin N) → LES`: `s^σ_j = |{c < j | σ c < σ j}|`. -/
def permToLES (N : ℕ) (σ : Equiv.Perm (Fin N)) : Fin N → ℕ :=
  fun j => (Finset.univ.filter fun c : Fin N => c < j ∧ σ c < σ j).card

/-- Reverse greedy row-placement state over columns `lo + len - 1` down to `lo` out of row pool `U`. -/
def greedyState (s : ℕ → ℕ) (lo : ℕ) : ℕ → List ℕ → List (ℕ × ℕ) × List ℕ
  | 0, U => ([], U)
  | len + 1, U =>
    let c := lo + len
    let r := U.getD (s c) 0
    let res := greedyState s lo len (U.eraseIdx (s c))
    ((r, c) :: res.1, res.2)

/-- Sorted sub-diagram on column interval `[lo, hi)` (in 0-based rows `[0, hi)`). -/
def greedyDiag (s : ℕ → ℕ) (lo hi : ℕ) : List (ℕ × ℕ) :=
  ((greedyState s lo (hi - lo) (List.range hi)).1).mergeSort (fun p q => decide (p.1 ≤ q.1))

/-- Unary merge key `mergePhi k (idx, r, c)` matching `[LCG26]` `Γ_1`. -/
def mergePhi (k : ℕ) (t : ℕ × ℕ × ℕ) : ℕ ×ₗ ℕ ×ₗ ℕ :=
  if t.1 < k then toLex (t.2.1, toLex (1, t.1))
  else toLex (t.2.1 - (t.1 - k), toLex (0, t.1))

/-- Zero-extended `ℕ → ℕ` copy of `s : Fin N → ℕ`. -/
def sExt {N : ℕ} (s : Fin N → ℕ) (c : ℕ) : ℕ :=
  if h : c < N then s ⟨c, h⟩ else 0

/-- Padded extension `padLES54 N s c`: equals `s c` for `c < N` and `c` for `c ≥ N`. -/
def padLES54 (N : ℕ) (s : Fin N → ℕ) (c : ℕ) : ℕ :=
  if h : c < N then s ⟨c, h⟩ else c

/-- Embedding `Equiv.Perm (Fin N) → Equiv.Perm (Fin M)` fixing indices `≥ N`. -/
def padPerm54 (N M : ℕ) (hNM : N ≤ M) (σ : Equiv.Perm (Fin N)) : Equiv.Perm (Fin M) where
  toFun j := if h : j.1 < N then ⟨(σ ⟨j.1, h⟩).1, lt_of_lt_of_le (σ ⟨j.1, h⟩).isLt hNM⟩ else j
  invFun j := if h : j.1 < N then ⟨(σ⁻¹ ⟨j.1, h⟩).1, lt_of_lt_of_le (σ⁻¹ ⟨j.1, h⟩).isLt hNM⟩ else j
  left_inv j := by
    by_cases h : j.1 < N
    · simp [h, (σ ⟨j.1, h⟩).isLt]
    · simp [h]
  right_inv j := by
    by_cases h : j.1 < N
    · simp [h]
    · simp [h]

/-! ### Part 2: NSIL Run Structure, Harmonic-Bucket Routing & Stabilizer Definitions -/

/-- An NSIL of length `N` is a non-decreasing sequence `l : Fin N → α`. -/
def IsNSIL {α : Type*} [LinearOrder α] (N : ℕ) (l : Fin N → α) : Prop :=
  Monotone l

/-- 0-based start index of the constant run containing `i`: `#{j | l j < l i}`. -/
def runStart {α : Type*} [LinearOrder α] {N : ℕ} (l : Fin N → α) (i : Fin N) : ℕ :=
  (Finset.univ.filter fun j : Fin N => l j < l i).card

/-- Exclusive 0-based end index of the constant run containing `i`: `#{j | l j ≤ l i}`. -/
def runEndSucc {α : Type*} [LinearOrder α] {N : ℕ} (l : Fin N → α) (i : Fin N) : ℕ :=
  (Finset.univ.filter fun j : Fin N => l j ≤ l i).card

/-- Number of occurrences of `l i` in `l`. -/
def runCount {α : Type*} [LinearOrder α] {N : ℕ} (l : Fin N → α) (i : Fin N) : ℕ :=
  (Finset.univ.filter fun j : Fin N => l j = l i).card

/-- 1-based position within the constant run (`m_i = i - runStart l i + 1`). -/
def runOffset {α : Type*} [LinearOrder α] {N : ℕ} (l : Fin N → α) (i : Fin N) : ℕ :=
  i.1 - runStart l i + 1

/-- Number of indices `j < i` sharing `runOffset l j = runOffset l i`. -/
def runOcc {α : Type*} [LinearOrder α] {N : ℕ} (l : Fin N → α) (i : Fin N) : ℕ :=
  (Finset.univ.filter fun j : Fin N => j < i ∧ runOffset l j = runOffset l i).card

/-- Canonical bucket schedule `[(m, occ)]` for `2 ≤ m ≤ N`, `0 ≤ occ < N / m`. -/
def bucketPairs (N : ℕ) : List (ℕ × ℕ) :=
  ((List.range (N - 1)).map (· + 2)).flatMap fun m =>
    (List.range (N / m)).map fun occ => (m, occ)

/-- Key for sorting active `m_i ≥ 2` records before computing sequential `occ`. -/
def occSortKey {N : ℕ} (r : Bool × ℕ × Fin N) : ℕ ×ₗ ℕ ×ₗ ℕ :=
  toLex (if r.1 then 0 else 1, toLex (r.2.1, r.2.2.1))

/-- Sorted `(active, m, i)` list for sequential `occ` computation. -/
def occSortedList {α : Type*} [LinearOrder α] (N : ℕ) (l : Fin N → α) :
    List (Bool × ℕ × Fin N) :=
  ((List.finRange N).map fun i => (decide (2 ≤ runOffset l i), runOffset l i, i)).mergeSort
    (fun x y => decide (occSortKey x ≤ occSortKey y))

/-- 1-pass sequential recurrence for `occ` over `occSortedList`. -/
def seqScanOcc {N : ℕ} (L : List (Bool × ℕ × Fin N)) : ℕ → ℕ
  | 0 => 0
  | p + 1 =>
    match L[p + 1]?, L[p]? with
    | some cur, some prev =>
      if cur.1 && prev.1 && (cur.2.1 == prev.2.1) then seqScanOcc L p + 1 else 0
    | _, _ => 0

/-- Record for fixed-slot 2-Sort Harmonic-Bucket Routing:
`kind`: `0 = ITEM`, `1 = MARKER_FREE`, `2 = MARKER_USED`, `3 = INACT`. -/
@[ext]
structure HBRec where
  kind : ℕ
  m : ℕ
  occ : ℕ
  dest : ℕ
  orig : ℕ
  deriving DecidableEq, Inhabited

def hbInactive (r : HBRec) : ℕ := if r.kind = 3 then 1 else 0

def hbKindRank1 (r : HBRec) : ℕ := if r.kind = 0 then 0 else if r.kind = 1 then 1 else 2

def hbKey1 (r : HBRec) : ℕ ×ₗ ℕ ×ₗ ℕ ×ₗ ℕ ×ₗ ℕ :=
  toLex (hbInactive r, toLex (r.m, toLex (r.occ, toLex (hbKindRank1 r, r.orig))))

def hbGroup (r : HBRec) : ℕ := if r.kind = 0 ∨ r.kind = 1 then 0 else 1

def hbKey2 (r : HBRec) : ℕ ×ₗ ℕ ×ₗ ℕ :=
  toLex (hbGroup r, toLex (r.dest, r.orig))

/-- Initial `2 * B2` records (`B2` source slots followed by `B2` fixed marker slots). -/
def hbInit {α : Type*} [LinearOrder α] (N B2 : ℕ) (l : Fin N → α) : List HBRec :=
  ((List.finRange B2).map fun i =>
    if h : i.1 < N then
      if 2 ≤ runOffset l ⟨i.1, h⟩ then
        { kind := 0, m := runOffset l ⟨i.1, h⟩, occ := runOcc l ⟨i.1, h⟩, dest := 0, orig := i.1 }
      else
        { kind := 3, m := 0, occ := 0, dest := 0, orig := i.1 }
    else
      { kind := 3, m := 0, occ := 0, dest := 0, orig := i.1 }) ++
  ((List.finRange B2).map fun b =>
    if _hb : b.1 < (bucketPairs N).length then
      { kind := 1, m := (bucketPairs N)[b.1].1, occ := (bucketPairs N)[b.1].2,
        dest := b.1, orig := B2 + b.1 }
    else
      { kind := 1, m := N + 1 + b.1, occ := 0, dest := b.1, orig := B2 + b.1 })

/-- Adjacent neighbor-matching pass updating `(ITEM, MARKER_FREE)` pairs cleanly. -/
def hbNeighborStep (L : List HBRec) (p : ℕ) : List HBRec :=
  if hp : p + 1 < L.length then
    let r0 := L[p]'(by omega)
    let r1 := L[p + 1]'hp
    if r0.kind = 0 ∧ r1.kind = 1 ∧ r0.m = r1.m ∧ r0.occ = r1.occ then
      (L.set p { r0 with dest := r1.dest }).set (p + 1) { r1 with kind := 2 }
    else L
  else L

def hbSeqPass (L : List HBRec) : List HBRec :=
  (List.range L.length).foldl hbNeighborStep L

/-- Right-action list permutation `(permList σ x) i = x (σ i)`. -/
def permList {α : Type*} {N : ℕ} (σ : Equiv.Perm (Fin N)) (x : Fin N → α) : Fin N → α :=
  fun i => x (σ i)

@[simp] lemma permList_one {α : Type*} {N : ℕ} (x : Fin N → α) : permList 1 x = x := rfl

lemma permList_mul {α : Type*} {N : ℕ} (σ₁ σ₂ : Equiv.Perm (Fin N)) (x : Fin N → α) :
    permList σ₁ (permList σ₂ x) = permList (σ₂ * σ₁) x := rfl

/-- Stabilizer subgroup `H_l = { h ∈ S_N | ∀ i, l (h i) = l i }`. -/
def stabGroup {α : Type*} (N : ℕ) (l : Fin N → α) : Subgroup (Equiv.Perm (Fin N)) where
  carrier := { h | ∀ i : Fin N, l (h i) = l i }
  mul_mem' {a b} ha hb i := by simp [Equiv.Perm.mul_apply, ha (b i), hb i]
  one_mem' _ := rfl
  inv_mem' {a} ha i := by simpa using (ha (a⁻¹ i)).symm

lemma mem_stabGroup_iff {α : Type*} {N : ℕ} {l : Fin N → α} {h : Equiv.Perm (Fin N)} :
    h ∈ stabGroup N l ↔ ∀ i : Fin N, l (h i) = l i := Iff.rfl

instance instDecidableMemStabGroup {α : Type*} [DecidableEq α] (N : ℕ) (l : Fin N → α) :
    DecidablePred (· ∈ stabGroup N l) :=
  fun h => inferInstanceAs (Decidable (∀ i : Fin N, l (h i) = l i))

instance instDecidableMemOrbit {β : Type*} [DecidableEq β] (N : ℕ) (l : Fin N → β) :
    DecidablePred (fun z : Fin N → β => ∃ σ : Equiv.Perm (Fin N), permList σ l = z) :=
  fun _ => Fintype.decidableExistsFintype

/-- `LES_l` predicate: `∀ i, runStart l i ≤ s i ≤ i`. -/
def IsLESOf {α : Type*} [LinearOrder α] (N : ℕ) (l : Fin N → α) (s : Fin N → ℕ) : Prop :=
  ∀ i : Fin N, runStart l i ≤ s i ∧ s i ≤ i.1

/-- Equivalence between `LES_l` and `∏_i Fin (runOffset l i)` via `s i = i - d i` (using `runStart_le`). -/
def isLESOfEquivPiFinOf {α : Type*} [LinearOrder α] (N : ℕ) (l : Fin N → α)
    (hrs_le : ∀ i : Fin N, runStart l i ≤ i.1) :
    { s : Fin N → ℕ // IsLESOf N l s } ≃ ((i : Fin N) → Fin (runOffset l i)) where
  toFun s i := ⟨i.1 - s.1 i, by have hs := s.2 i; dsimp [runOffset]; omega⟩
  invFun d := ⟨fun i => i.1 - (d i).1, fun i => by
    have hd := (d i).isLt; have hrs := hrs_le i; dsimp [runOffset] at hd ⊢; omega⟩
  left_inv s := Subtype.ext <| funext fun i => by have hs := s.2 i; dsimp only; omega
  right_inv d := funext fun i => Fin.ext <| by
    have hd := (d i).isLt; have hrs := hrs_le i; dsimp [runOffset] at hd ⊢; omega

/-- Padding an NSIL `l : Fin N → ℕ` to length `M ≥ N` with unique trailing sentinels `(1, j)`. -/
def padNSIL (N M : ℕ) (l : Fin N → ℕ) (j : Fin M) : ℕ ×ₗ ℕ :=
  if h : j.1 < N then toLex (0, l ⟨j.1, h⟩) else toLex (1, j.1)

@[simp] lemma padPerm54_one (N M : ℕ) (hNM : N ≤ M) :
    padPerm54 N M hNM 1 = 1 := by
  ext j; simp [padPerm54]

lemma padPerm54_mul (N M : ℕ) (hNM : N ≤ M) (σ₁ σ₂ : Equiv.Perm (Fin N)) :
    padPerm54 N M hNM (σ₁ * σ₂) = padPerm54 N M hNM σ₁ * padPerm54 N M hNM σ₂ := by
  ext j
  by_cases hj : j.1 < N
  · simp [padPerm54, hj, (σ₂ ⟨j.1, hj⟩).isLt]
  · simp [padPerm54, hj]

lemma padPerm54_inv (N M : ℕ) (hNM : N ≤ M) (σ : Equiv.Perm (Fin N)) :
    (padPerm54 N M hNM σ)⁻¹ = padPerm54 N M hNM σ⁻¹ := rfl

lemma padPerm54_lt (N M : ℕ) (hNM : N ≤ M) (σ : Equiv.Perm (Fin N))
    {j : Fin M} (hj : j.1 < N) :
    (padPerm54 N M hNM σ j).1 = (σ ⟨j.1, hj⟩).1 := by
  simp [padPerm54, hj]

lemma padPerm54_ge (N M : ℕ) (hNM : N ≤ M) (σ : Equiv.Perm (Fin N))
    {j : Fin M} (hj : N ≤ j.1) :
    padPerm54 N M hNM σ j = j := by
  simp [padPerm54, Nat.not_lt.mpr hj]

end QuantumLTF.Membership.Supplement.LcgSym54

namespace QuantumLTF.Membership.Supplement

open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement.LcgSym54

/-- Bundled combinatorial engine for `[LCG26]` Stage B symmetrization (`nsil_symmetrize_54`). -/
structure LcgSym54Comb where
  bitsToNat_natToBits : ∀ {w x : ℕ}, x < 2 ^ w → bitsToNat (natToBits w x) = x
  bitsToNat_append : ∀ {w_a w_b : ℕ} (a : Qubits w_a) (b : Qubits w_b),
    bitsToNat (Fin.append a b) = 2 ^ w_b * bitsToNat a + bitsToNat b
  bitsToNat_inj : ∀ {w : ℕ}, Function.Injective (@bitsToNat w)
  bitsToNat_lt_two_pow : ∀ {w : ℕ} (b : Qubits w), bitsToNat b < 2 ^ w
  natToBits_comp_revPerm : ∀ (w x : ℕ) (i : Fin w),
    natToBits w x i.rev = Nat.testBit x i.1
  bitsToNat_particleSym54_eq : ∀ (n : ℕ) (j : Fin (n + 1)),
    bitsToNat (particleSym54 n (Nat.clog 2 n + 1) j) = if j.1 < n then j.1 else 2 ^ (Nat.clog 2 n)
  bitsToNat_particleSym54_strictMono : ∀ (n : ℕ),
    StrictMono (fun j : Fin (n + 1) => bitsToNat (particleSym54 n (Nat.clog 2 n + 1) j))
  card_les : ∀ (N : ℕ), Fintype.card { s : Fin N → ℕ // IsLES N s } = Nat.factorial N
  permToLES_isLES : ∀ (N : ℕ) (σ : Equiv.Perm (Fin N)), IsLES N (permToLES N σ)
  lesEquivPerm : ∀ (N : ℕ), { s : Fin N → ℕ // IsLES N s } ≃ Equiv.Perm (Fin N)
  lesToPerm : (N : ℕ) → (s : Fin N → ℕ) → IsLES N s → Equiv.Perm (Fin N)
  lesToPerm_eq : ∀ (N : ℕ) (s : Fin N → ℕ) (hs : IsLES N s),
    lesToPerm N s hs = lesEquivPerm N ⟨s, hs⟩
  permToLES_lesToPerm : ∀ (N : ℕ) (s : Fin N → ℕ) (hs : IsLES N s),
    permToLES N (lesToPerm N s hs) = s
  lesEquivPerm_symm_apply : ∀ (N : ℕ) (σ : Equiv.Perm (Fin N)),
    ((lesEquivPerm N).symm σ).1 = permToLES N σ
  perm_eq_of_sorted_of_inj : ∀ {α κ : Type} [LinearOrder κ] (key : α → κ) (L₁ L₂ : List α),
    List.Perm L₁ L₂ →
    L₁.Pairwise (fun x y => key x ≤ key y) →
    L₂.Pairwise (fun x y => key x ≤ key y) →
    (∀ x ∈ L₂, ∀ y ∈ L₂, key x = key y → x = y) →
    L₁ = L₂
  padLES54_le : ∀ (N : ℕ) (s : Fin N → ℕ), IsLES N s → ∀ c : ℕ, padLES54 N s c ≤ c
  mergePhi_fst_inj : ∀ (k : ℕ) (t₁ t₂ : ℕ × ℕ × ℕ),
    mergePhi k t₁ = mergePhi k t₂ → t₁.1 = t₂.1
  hbKey1_orig_inj : ∀ r₁ r₂ : HBRec, hbKey1 r₁ = hbKey1 r₂ → r₁.orig = r₂.orig
  hbKey2_orig_inj : ∀ r₁ r₂ : HBRec, hbKey2 r₁ = hbKey2 r₂ → r₁.orig = r₂.orig
  occSortKey_idx_inj : ∀ {N : ℕ} (r₁ r₂ : Bool × ℕ × Fin N),
    occSortKey r₁ = occSortKey r₂ → r₁.2.2 = r₂.2.2
  greedyDiag_length : ∀ (s : ℕ → ℕ) (lo hi : ℕ),
    lo ≤ hi → (∀ c, lo ≤ c → c < hi → s c ≤ c) → (greedyDiag s lo hi).length = hi - lo
  greedyDiag_col_mem : ∀ (s : ℕ → ℕ) (lo hi : ℕ),
    lo ≤ hi → (∀ c, lo ≤ c → c < hi → s c ≤ c) →
    ∀ p ∈ greedyDiag s lo hi, lo ≤ p.2 ∧ p.2 < hi
  greedyDiag_fst_lt : ∀ (s : ℕ → ℕ) (lo hi : ℕ),
    lo ≤ hi → (∀ c, lo ≤ c → c < hi → s c ≤ c) →
    (greedyDiag s lo hi).Pairwise (fun p q => p.1 < q.1)
  greedyDiag_fst_ge_idx : ∀ (s : ℕ → ℕ) (lo hi : ℕ),
    lo ≤ hi → (∀ c, lo ≤ c → c < hi → s c ≤ c) →
    ∀ (idx : ℕ) (hidx : idx < (greedyDiag s lo hi).length),
      idx ≤ ((greedyDiag s lo hi)[idx]'hidx).1
  greedyDiag_row_lt : ∀ (s : ℕ → ℕ) (lo hi : ℕ),
    lo ≤ hi → (∀ c, lo ≤ c → c < hi → s c ≤ c) →
    ∀ p ∈ greedyDiag s lo hi, p.1 < hi
  greedyDiag_leaf : ∀ (s : ℕ → ℕ) (lo : ℕ),
    s lo ≤ lo → greedyDiag s lo (lo + 1) = [(s lo, lo)]
  alonsoSchott_merge_spec : ∀ (s : ℕ → ℕ) (lo mid hi : ℕ),
    lo ≤ mid → mid ≤ hi → (∀ c, c < hi → s c ≤ c) →
    let L := greedyDiag s lo mid
    let R := greedyDiag s mid hi
    let k := mid - lo
    let Ttilde0 := ((L ++ R).zipIdx).map (fun ((r, c), idx) => (idx, r, c))
    let Ttilde1 := Ttilde0.mergeSort (fun a b => decide (mergePhi k a ≤ mergePhi k b))
    let U_mid := (greedyState s mid (hi - mid) (List.range hi)).2
    Ttilde1.length = hi - lo ∧
    (∀ (pos : ℕ) (hpos : pos < Ttilde1.length),
      let t := Ttilde1[pos]
      let dR := ((Ttilde1.take pos).filter (fun u => decide (k ≤ u.1))).length
      (t.1 < k → ∃ hr : t.2.1 < U_mid.length, t.1 = pos - dR ∧ U_mid[t.2.1]'hr = t.2.1 + dR) ∧
      (k ≤ t.1 → t.1 = k + dR)) ∧
    ((List.finRange Ttilde1.length).map (fun pos =>
      let t := Ttilde1[pos.1]
      let dR := ((Ttilde1.take pos.1).filter (fun u => decide (k ≤ u.1))).length
      (if t.1 < k then t.2.1 + dR else t.2.1, t.2.2))) = greedyDiag s lo hi
  Ttilde1_col_lt_iff : ∀ (s : ℕ → ℕ) (lo mid hi : ℕ),
    lo ≤ mid → mid ≤ hi → (∀ c, c < hi → s c ≤ c) →
    let L := greedyDiag s lo mid
    let R := greedyDiag s mid hi
    let k := mid - lo
    let Ttilde0 := ((L ++ R).zipIdx).map (fun ((r, c), idx) => (idx, r, c))
    ∀ t ∈ Ttilde0,
      lo ≤ t.2.2 ∧ t.2.2 < hi ∧ t.2.1 < hi ∧ t.1 < hi - lo ∧
      (t.1 < k ↔ t.2.2 < mid) ∧ (k ≤ t.1 → t.1 - k ≤ t.2.1)
  greedyDiag_pad_root : ∀ (N M : ℕ) (hNM : N ≤ M) (s : Fin N → ℕ) (hs : IsLES N s)
      (pos : ℕ) (hpos : pos < M),
    (greedyDiag (padLES54 N s) 0 M).length = M ∧
    (greedyDiag (padLES54 N s) 0 M)[pos]! =
      (pos, (padPerm54 N M hNM (lesToPerm N s hs)⁻¹ ⟨pos, hpos⟩).1)
  runStart_le : ∀ {α : Type} [LinearOrder α] {N : ℕ} {l : Fin N → α},
    Monotone l → ∀ i : Fin N, runStart l i ≤ i.1
  runOffset_pos : ∀ {α : Type} [LinearOrder α] {N : ℕ} (l : Fin N → α) (i : Fin N),
    1 ≤ runOffset l i
  runOffset_le_N : ∀ {α : Type} [LinearOrder α] {N : ℕ} (l : Fin N → α) (i : Fin N),
    runOffset l i ≤ N
  runOffset_zero : ∀ {α : Type} [LinearOrder α] {N : ℕ} (l : Fin (N + 1) → α),
    Monotone l → runOffset l ⟨0, Nat.succ_pos N⟩ = 1
  runOffset_succ : ∀ {α : Type} [LinearOrder α] {N : ℕ} (l : Fin N → α),
    Monotone l → ∀ (i : ℕ) (h : i + 1 < N),
      runOffset l ⟨i + 1, h⟩ =
        if l ⟨i, by omega⟩ = l ⟨i + 1, h⟩ then runOffset l ⟨i, by omega⟩ + 1 else 1
  runOffset_card_le : ∀ {α : Type} [LinearOrder α] {N : ℕ} {l : Fin N → α},
    Monotone l → ∀ {m : ℕ}, 1 ≤ m →
      (Finset.univ.filter fun i : Fin N => runOffset l i = m).card ≤ N / m
  harmonicBucketSum_le : ∀ N : ℕ,
    ∑ m ∈ Finset.Icc 2 N, (N / m) ≤ N * Nat.clog 2 (N + 2)
  mem_bucketPairs_iff : ∀ (N m occ : ℕ),
    (m, occ) ∈ bucketPairs N ↔ 2 ≤ m ∧ m ≤ N ∧ occ < N / m
  bucketPairs_length : ∀ N : ℕ,
    (bucketPairs N).length = ∑ m ∈ Finset.Icc 2 N, (N / m)
  bucketPairs_nodup : ∀ N : ℕ, (bucketPairs N).Nodup
  runOcc_lt_div : ∀ {α : Type} [LinearOrder α] {N : ℕ} {l : Fin N → α},
    Monotone l → ∀ i : Fin N, runOcc l i < N / runOffset l i
  runOffset_comp_strictMono : ∀ {α β : Type} [LinearOrder α] [LinearOrder β] {N : ℕ}
      (f : α → β) (_hf : StrictMono f) (l : Fin N → α) (i : Fin N),
    runOffset (f ∘ l) i = runOffset l i
  runOcc_comp_strictMono : ∀ {α β : Type} [LinearOrder α] [LinearOrder β] {N : ℕ}
      (f : α → β) (_hf : StrictMono f) (l : Fin N → α) (i : Fin N),
    runOcc (f ∘ l) i = runOcc l i
  prod_runOffset_eq_prod_modeCount : ∀ {β : Type} [LinearOrder β] [Fintype β]
      (N : ℕ) (l : Fin N → β) (_hl : Monotone l),
    ∏ i : Fin N, runOffset l i =
      ∏ b : β, (Finset.univ.filter fun i : Fin N => l i = b).card.factorial
  seqScanOcc_eq_runOcc : ∀ {α : Type} [LinearOrder α] (N : ℕ) (l : Fin N → α)
      (p : ℕ) (hp : p < (occSortedList N l).length),
    (occSortedList N l)[p].1 = true →
      seqScanOcc (occSortedList N l) p = runOcc l (occSortedList N l)[p].2.2
  harmBucket_routing_spec : ∀ {α : Type} [LinearOrder α] (N B2 : ℕ),
    N ≤ B2 → (bucketPairs N).length ≤ B2 →
    ∀ (l : Fin N → α), Monotone l →
    let init := hbInit N B2 l
    let s1 := init.mergeSort (fun x y => decide (hbKey1 x ≤ hbKey1 y))
    let matched := hbSeqPass s1
    let s2 := matched.mergeSort (fun x y => decide (hbKey2 x ≤ hbKey2 y))
    s2.length = 2 * B2 ∧
    (∀ b : Fin B2,
      s2[b.1]!.dest = b.1 ∧
      hbGroup s2[b.1]! = 0 ∧
      (∀ hb : b.1 < (bucketPairs N).length,
        let r := s2[b.1]!
        (r.kind = 0 ↔ ∃ i : Fin N, 2 ≤ runOffset l i ∧
          (runOffset l i, runOcc l i) = (bucketPairs N)[b.1]'hb) ∧
        (r.kind = 0 → r.m = ((bucketPairs N)[b.1]'hb).1 ∧ r.occ = ((bucketPairs N)[b.1]'hb).2 ∧
          r.orig < N ∧ ∃ h : r.orig < N, 2 ≤ runOffset l ⟨r.orig, h⟩) ∧
        (r.kind ≠ 0 → r.kind = 1)))
  mem_stabGroup_iff_isLESOf : ∀ {α : Type} [LinearOrder α] (N : ℕ) (l : Fin N → α),
    Monotone l → ∀ (s : Fin N → ℕ) (hs : IsLES N s),
      lesToPerm N s hs ∈ stabGroup N l ↔ IsLESOf N l s
  card_stabGroup_eq_prod_modeCount : ∀ {β : Type} [Fintype β] [DecidableEq β]
      (N : ℕ) (l : Fin N → β),
    Fintype.card (stabGroup N l) =
      ∏ b : β, (Finset.univ.filter fun i : Fin N => l i = b).card.factorial
  card_isLESOf_eq_prod_runOffset : ∀ {α : Type} [LinearOrder α] (N : ℕ) (l : Fin N → α)
      (hl : Monotone l),
    letI : Fintype { s : Fin N → ℕ // IsLESOf N l s } :=
      Fintype.ofEquiv _ (isLESOfEquivPiFinOf N l (runStart_le hl)).symm
    Fintype.card { s : Fin N → ℕ // IsLESOf N l s } = ∏ i : Fin N, runOffset l i
  mem_permList_range_iff_fiber_card : ∀ {β : Type} [DecidableEq β]
      {N : ℕ} (l y : Fin N → β),
    (∃ σ : Equiv.Perm (Fin N), permList σ l = y) ↔
      ∀ b : β, (Finset.univ.filter fun i : Fin N => y i = b).card =
        (Finset.univ.filter fun i : Fin N => l i = b).card
  eq_655_701_sum_factorization : ∀ {β V : Type} [Fintype β] [DecidableEq β]
      [AddCommMonoid V] [Module ℂ V]
      (N : ℕ) (l : Fin N → β)
      (τ : (Fin N → β) → Equiv.Perm (Fin N))
      (_hτ : ∀ y : { z : Fin N → β // ∃ σ : Equiv.Perm (Fin N), permList σ l = z },
        permList (τ y.1)⁻¹ y.1 = l)
      (f : (Fin N → β) → Equiv.Perm (Fin N) → V),
    ∑ σ : Equiv.Perm (Fin N), f (permList σ l) (σ * (τ (permList σ l))⁻¹) =
      ∑ y : { z : Fin N → β // ∃ σ : Equiv.Perm (Fin N), permList σ l = z },
        ∑ h : stabGroup N l, f y.1 h.1
  card_stabGroup_fin_succ : ∀ (n K : ℕ) (α : Fin n → ℕ)
      (l : Fin (2 * K) → Fin (n + 1))
      (_hα : ∀ i : Fin n, (Finset.univ.filter fun p => l p = ⟨i.1, by omega⟩).card = α i)
      (_hblank : (Finset.univ.filter fun p => l p = ⟨n, Nat.lt_succ_self n⟩).card = 2 * K - ∑ i, α i),
    Fintype.card (stabGroup (2 * K) l) =
      (∏ i : Fin n, (α i).factorial) * (2 * K - ∑ i : Fin n, α i).factorial
  orbit_particleSym54_iff_multinom : ∀ (n K : ℕ) (α : Fin n → ℕ)
      (l : Fin (2 * K) → Fin (n + 1))
      (_hα : ∀ i : Fin n, (Finset.univ.filter fun p => l p = ⟨i.1, by omega⟩).card = α i)
      (_hblank : (Finset.univ.filter fun p => l p = ⟨n, Nat.lt_succ_self n⟩).card = 2 * K - ∑ i, α i)
      (y : Fin (2 * K) → Fin (n + 1)),
    (∃ σ : Equiv.Perm (Fin (2 * K)), permList σ l = y) ↔
      let s := Nat.clog 2 n + 1
      let z := flatReg (2 * K) s fun p => particleSym54 n s (y p)
      (∀ i : Fin n,
          (Finset.univ.filter fun r : Fin (2 * K) =>
            splitReg (2 * K) s z r = natToBits s i.val).card = α i) ∧
        (Finset.univ.filter fun r : Fin (2 * K) =>
          splitReg (2 * K) s z r = blankSym54 s).card = 2 * K - ∑ i : Fin n, α i

end QuantumLTF.Membership.Supplement


