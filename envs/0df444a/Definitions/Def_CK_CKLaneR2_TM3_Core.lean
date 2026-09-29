-- Prove2me | Definitions.Def_CK_CKLaneR2_TM3_Core
-- name    : CK_CKLaneR2_TM3_Core
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T03:52:49.436767+00:00
-- url     : https://prove2.me/theorems/55dd671d-79de-4eb3-b1b4-b7b6cf044abe
-- title:
--   Courtade–Kumar proof module `CKLaneR2.TM3.Core` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneR2.TM3.Core` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneR2.TM3.Core` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneR2.TM3.Core (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneR2/TM3/Core.lean)

import Definitions.Def_CK_GeneralCK_RadialDerivatives
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

-- ===== source module CKLaneR2.TM3.Core =====
section

/-!
# Lane C: TM3 core (exact fixed-point Taylor models in 3 variables, graded dense form) and soundness

Bit-exact Python mirror: `~/ck_lanes_20260923/C/tools/tm3c.py` ("tm3 v2").

**Representation.**
* `Poly = List Comp` is graded: entry `k` holds the homogeneous degree-`k` part.
* `Comp = List Row`: row `i` is the coefficient of `x^i`.
* `Row = List Int`: entry `j` is the coefficient of `y^j z^(k-i-j)`.
* Coefficients are integers in units of `2^-P`, and `one = 2^P`.

**Semantics.**
* `evalR m q y z = Σ_j q_j y^j z^(m-j)`.
* `evalC k P x y z = Σ_i x^i evalR (k-i) P_i y z`.
* `evalP k A = Σ_c evalC (k+c) A_c`.
* `Contains one T f`: if `T.ok`, then for all `x y z ∈ [-1,1]`,
  `|f x y z - evalP 0 T.p x y z / one| ≤ T.r / one`.
* Only multiplication needs the shape invariant (`wfP`). It is checked at run time inside `mul`,
  and a failed check sets `ok := false`.
-/

namespace CKLaneR2.TM3

abbrev Row := List Int
abbrev Comp := List Row
abbrev Poly := List Comp

structure TM where
  p : Poly
  r : Nat
  ok : Bool

/-! ## Kernel-friendly list primitives (raw recursors; their equations hold by `rfl`) -/

section Prim
variable {α β : Type}

noncomputable def zipAdd (f : α → α → α) (p : List α) : List α → List α :=
  @List.rec α (fun _ => List α → List α) (fun q => q)
    (fun a p' ih => fun q =>
      @List.rec α (fun _ => List α) (a :: p') (fun b q' _ => f a b :: ih q') q) p

theorem zipAdd_nil (f : α → α → α) (q : List α) : zipAdd f [] q = q := rfl
theorem zipAdd_cons_nil (f : α → α → α) (a : α) (p : List α) :
    zipAdd f (a :: p) [] = a :: p := rfl
theorem zipAdd_cons_cons (f : α → α → α) (a b : α) (p q : List α) :
    zipAdd f (a :: p) (b :: q) = f a b :: zipAdd f p q := rfl

noncomputable def lmap (f : α → β) (p : List α) : List β :=
  @List.rec α (fun _ => List β) [] (fun a _ ih => f a :: ih) p

theorem lmap_nil (f : α → β) : lmap f [] = [] := rfl
theorem lmap_cons (f : α → β) (a : α) (p : List α) : lmap f (a :: p) = f a :: lmap f p := rfl

noncomputable def lsum (f : α → ℕ) (p : List α) : ℕ :=
  @List.rec α (fun _ => ℕ) 0 (fun a _ ih => f a + ih) p

theorem lsum_nil (f : α → ℕ) : lsum f [] = 0 := rfl
theorem lsum_cons (f : α → ℕ) (a : α) (p : List α) : lsum f (a :: p) = f a + lsum f p := rfl

noncomputable def ltake (p : List α) : ℕ → List α :=
  @List.rec α (fun _ => ℕ → List α) (fun _ => [])
    (fun a _ ih => fun n => @Nat.rec (fun _ => List α) [] (fun n' _ => a :: ih n') n) p

theorem ltake_nil (n : ℕ) : ltake ([] : List α) n = [] := rfl
theorem ltake_zero (a : α) (p : List α) : ltake (a :: p) 0 = [] := rfl
theorem ltake_succ (a : α) (p : List α) (n : ℕ) : ltake (a :: p) (n + 1) = a :: ltake p n := rfl

noncomputable def ldrop (p : List α) : ℕ → List α :=
  @List.rec α (fun _ => ℕ → List α) (fun _ => [])
    (fun a p' ih => fun n => @Nat.rec (fun _ => List α) (a :: p') (fun n' _ => ih n') n) p

theorem ldrop_nil (n : ℕ) : ldrop ([] : List α) n = [] := rfl
theorem ldrop_zero' (p : List α) : ldrop p 0 = p := by cases p <;> rfl
theorem ldrop_succ (a : α) (p : List α) (n : ℕ) : ldrop (a :: p) (n + 1) = ldrop p n := rfl

theorem lmap_ldrop (f : α → β) (p : List α) (n : ℕ) : lmap f (ldrop p n) = ldrop (lmap f p) n := by
  induction p generalizing n with
  | nil => rfl
  | cons a p ih => cases n with
    | zero => rfl
    | succ n => simp only [ldrop_succ, lmap_cons]; exact ih n

theorem lsum_lmap (f : α → β) (g : β → ℕ) (p : List α) : lsum g (lmap f p) = lsum (g ∘ f) p := by
  induction p with
  | nil => rfl
  | cons a p ih => simp only [lmap_cons, lsum_cons, ih, Function.comp]

end Prim

/-! ## Row / Comp / Poly operations -/

noncomputable def addR : Row → Row → Row := zipAdd (fun a b : Int => a + b)
noncomputable def smulR (c : Int) : Row → Row := lmap (fun a : Int => c * a)
noncomputable def convR (p q : Row) : Row :=
  @List.rec Int (fun _ => Row) [] (fun a _ ih => addR (smulR a q) (0 :: ih)) p
noncomputable def absR : Row → ℕ := lsum Int.natAbs
noncomputable def fracR (one : ℕ) : Row → ℕ := lsum (fun a : Int => (a % (one : Int)).toNat)
noncomputable def roundR (one : ℕ) : Row → Row := lmap (fun a : Int => a / (one : Int))
noncomputable def modR (one : ℕ) : Row → Row := lmap (fun a : Int => a % (one : Int))

theorem addR_nil (q : Row) : addR [] q = q := rfl
theorem addR_cons_nil (a : Int) (p : Row) : addR (a :: p) [] = a :: p := rfl
theorem addR_cons_cons (a b : Int) (p q : Row) : addR (a :: p) (b :: q) = (a + b) :: addR p q := rfl
theorem convR_nil (q : Row) : convR [] q = [] := rfl
theorem convR_cons (a : Int) (p q : Row) : convR (a :: p) q = addR (smulR a q) (0 :: convR p q) := rfl

noncomputable def addC : Comp → Comp → Comp := zipAdd addR
noncomputable def smulC (c : Int) : Comp → Comp := lmap (smulR c)
noncomputable def convC (P Q : Comp) : Comp :=
  @List.rec Row (fun _ => Comp) [] (fun a _ ih => addC (lmap (convR a) Q) ([] :: ih)) P
noncomputable def absC : Comp → ℕ := lsum absR
noncomputable def fracC (one : ℕ) : Comp → ℕ := lsum (fracR one)
noncomputable def roundC (one : ℕ) : Comp → Comp := lmap (roundR one)
noncomputable def modC (one : ℕ) : Comp → Comp := lmap (modR one)

theorem addC_nil (Q : Comp) : addC [] Q = Q := rfl
theorem addC_cons_nil (a : Row) (P : Comp) : addC (a :: P) [] = a :: P := rfl
theorem addC_cons_cons (a b : Row) (P Q : Comp) : addC (a :: P) (b :: Q) = addR a b :: addC P Q := rfl
theorem convC_nil (Q : Comp) : convC [] Q = [] := rfl
theorem convC_cons (a : Row) (P Q : Comp) :
    convC (a :: P) Q = addC (lmap (convR a) Q) ([] :: convC P Q) := rfl

noncomputable def addP : Poly → Poly → Poly := zipAdd addC
noncomputable def smulP (c : Int) : Poly → Poly := lmap (smulC c)
noncomputable def absP : Poly → ℕ := lsum absC
noncomputable def gAbs : Poly → List ℕ := lmap absC
noncomputable def fracP (one : ℕ) : Poly → ℕ := lsum (fracC one)
noncomputable def roundP (one : ℕ) : Poly → Poly := lmap (roundC one)
noncomputable def modP (one : ℕ) : Poly → Poly := lmap (modC one)
noncomputable def sumN : List ℕ → ℕ := lsum id

theorem addP_nil (Q : Poly) : addP [] Q = Q := rfl
theorem addP_cons_nil (a : Comp) (P : Poly) : addP (a :: P) [] = a :: P := rfl
theorem addP_cons_cons (a b : Comp) (P Q : Poly) : addP (a :: P) (b :: Q) = addC a b :: addP P Q := rfl

/-- Truncated graded product: keeps the pairs of graded components whose degrees add up to at most `n`. -/
noncomputable def gmul (A B : Poly) : ℕ → Poly :=
  @List.rec Comp (fun _ => ℕ → Poly) (fun _ => [])
    (fun a _ ih => fun n =>
      addP (lmap (convC a) (ltake B (n + 1)))
        (@Nat.rec (fun _ => Poly) [] (fun n' _ => [] :: ih n') n)) A

theorem gmul_nil (B : Poly) (n : ℕ) : gmul [] B n = [] := rfl
theorem gmul_cons_zero (a : Comp) (A B : Poly) :
    gmul (a :: A) B 0 = addP (lmap (convC a) (ltake B 1)) [] := rfl
theorem gmul_cons_succ (a : Comp) (A B : Poly) (n : ℕ) :
    gmul (a :: A) B (n + 1) = addP (lmap (convC a) (ltake B (n + 2))) ([] :: gmul A B n) := rfl

/-- Dropped mass `Σ_{k+l>n} gA_k gB_l`. It is the same number as tm3's `D`. -/
noncomputable def dropM (gA gB : List ℕ) : ℕ → ℕ :=
  @List.rec ℕ (fun _ => ℕ → ℕ) (fun _ => 0)
    (fun a gA' ih => fun n =>
      a * sumN (ldrop gB (n + 1)) + @Nat.rec (fun _ => ℕ) (sumN gA' * sumN gB) (fun n' _ => ih n') n) gA

theorem dropM_nil (gB : List ℕ) (n : ℕ) : dropM [] gB n = 0 := rfl
theorem dropM_cons_zero (a : ℕ) (gA gB : List ℕ) :
    dropM (a :: gA) gB 0 = a * sumN (ldrop gB 1) + sumN gA * sumN gB := rfl
theorem dropM_cons_succ (a : ℕ) (gA gB : List ℕ) (n : ℕ) :
    dropM (a :: gA) gB (n + 1) = a * sumN (ldrop gB (n + 2)) + dropM gA gB n := rfl

/-- Constant coefficient. -/
def c0P (A : Poly) : Int := ((A.headD []).headD []).headD 0

/-! ## Shape invariant (checked at run time by `mul`) -/

def wfC : ℕ → Comp → Bool
  | _, [] => true
  | k, row :: rows => decide (row.length ≤ k + 1) && decide (rows.length ≤ k) && wfC (k - 1) rows

def wfP : ℕ → Poly → Bool
  | _, [] => true
  | k, C :: Cs => wfC k C && wfP (k + 1) Cs

/-! ## TM operations (mirror of tm3c.py) -/

/-- `cdiv x one = ⌈x / one⌉`. -/
def cdiv (x one : ℕ) : ℕ := (x + one - 1) / one

/-- `(c0 + cx x + cy y + cz z) / one`, exactly. -/
def TM.lin (c0 cx cy cz : Int) : TM := ⟨[[[c0]], [[cz, cy], [cx]]], 0, true⟩

def TM.const (c : Int) (r : ℕ) : TM := ⟨[[[c]]], r, true⟩

noncomputable def TM.add (A B : TM) : TM := ⟨addP A.p B.p, A.r + B.r, A.ok && B.ok⟩

noncomputable def TM.neg (A : TM) : TM := ⟨smulP (-1) A.p, A.r, A.ok⟩

noncomputable def TM.sub (A B : TM) : TM := TM.add A (TM.neg B)

noncomputable def TM.addc (A : TM) (c : Int) : TM := ⟨addP A.p [[[c]]], A.r, A.ok⟩

noncomputable def TM.scaleInt (A : TM) (k : Int) : TM := ⟨smulP k A.p, k.natAbs * A.r, A.ok⟩

noncomputable def TM.mulc (one : ℕ) (A : TM) (c : Int) : TM :=
  ⟨roundP one (smulP c A.p), cdiv (A.r * c.natAbs + fracP one (smulP c A.p)) one, A.ok⟩

noncomputable def mulRem (one N : ℕ) (A B : TM) : ℕ :=
  cdiv (dropM (gAbs A.p) (gAbs B.p) N + (A.r * absP B.p + B.r * absP A.p + A.r * B.r)
    + fracP one (gmul A.p B.p N)) one

noncomputable def TM.mul (one N : ℕ) (A B : TM) : TM :=
  ⟨roundP one (gmul A.p B.p N), mulRem one N A B, A.ok && B.ok && wfP 0 A.p && wfP 0 B.p⟩

noncomputable def TM.bound (A : TM) : ℕ := absP A.p + A.r

noncomputable def TM.lower (A : TM) : Int := c0P A.p - ((absP A.p : Int) - |c0P A.p|) - A.r

noncomputable def TM.upper (A : TM) : Int := c0P A.p + ((absP A.p : Int) - |c0P A.p|) + A.r

/-! ## Semantics -/

noncomputable def evalR : ℕ → Row → ℝ → ℝ → ℝ
  | _, [], _, _ => 0
  | m, c :: q, y, z => (c : ℝ) * z ^ m + y * evalR (m - 1) q y z

noncomputable def evalC : ℕ → Comp → ℝ → ℝ → ℝ → ℝ
  | _, [], _, _, _ => 0
  | k, row :: rows, x, y, z => evalR k row y z + x * evalC (k - 1) rows x y z

noncomputable def evalP : ℕ → Poly → ℝ → ℝ → ℝ → ℝ
  | _, [], _, _, _ => 0
  | k, C :: Cs, x, y, z => evalC k C x y z + evalP (k + 1) Cs x y z

def Contains (one : ℕ) (T : TM) (f : ℝ → ℝ → ℝ → ℝ) : Prop :=
  T.ok = true → ∀ x y z : ℝ, |x| ≤ 1 → |y| ≤ 1 → |z| ≤ 1 →
    |f x y z - evalP 0 T.p x y z / one| ≤ (T.r : ℝ) / one

/-! ## Row lemmas -/

section RowLemmas
variable (y z : ℝ)

theorem evalR_addR (p q : Row) (m : ℕ) :
    evalR m (addR p q) y z = evalR m p y z + evalR m q y z := by
  induction p generalizing m q with
  | nil => simp [addR_nil, evalR]
  | cons a p ih =>
    cases q with
    | nil => simp [addR_cons_nil, evalR]
    | cons b q =>
      rw [addR_cons_cons]; simp only [evalR]; rw [ih]; push_cast; ring

theorem evalR_lmap_mul (c : Int) (p : Row) (m : ℕ) :
    evalR m (lmap (fun a : Int => c * a) p) y z = c * evalR m p y z := by
  induction p generalizing m with
  | nil => simp [lmap_nil, evalR]
  | cons a p ih => rw [lmap_cons]; simp only [evalR]; rw [ih]; push_cast; ring

theorem evalR_smulR (c : Int) (p : Row) (m : ℕ) :
    evalR m (smulR c p) y z = c * evalR m p y z := evalR_lmap_mul y z c p m

theorem evalR_shift (p : Row) (m m' : ℕ) (hp : p.length ≤ m' + 1) :
    evalR (m + m') p y z = z ^ m * evalR m' p y z := by
  induction p generalizing m' with
  | nil => simp [evalR]
  | cons c q ih =>
    simp only [evalR]
    rcases Nat.eq_zero_or_pos m' with h0 | hpos
    · subst h0
      have hq : q = [] := by
        apply List.eq_nil_of_length_eq_zero
        simp only [List.length_cons] at hp; omega
      subst hq; simp only [evalR]; ring
    · obtain ⟨m₁, rfl⟩ : ∃ m₁, m' = m₁ + 1 := ⟨m' - 1, by omega⟩
      have hq : q.length ≤ m₁ + 1 := by simp only [List.length_cons] at hp; omega
      have e1 : m + (m₁ + 1) - 1 = m + m₁ := by omega
      have e2 : m₁ + 1 - 1 = m₁ := by omega
      rw [e1, e2, ih m₁ hq]; ring

theorem evalR_convR (p q : Row) (m m' : ℕ) (hp : p.length ≤ m + 1) (hq : q.length ≤ m' + 1) :
    evalR (m + m') (convR p q) y z = evalR m p y z * evalR m' q y z := by
  induction p generalizing m with
  | nil => simp [convR_nil, evalR]
  | cons a p ih =>
    rw [convR_cons, evalR_addR, evalR_smulR, evalR_shift y z q m m' hq]
    simp only [evalR]
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · subst h0
      have hp' : p = [] := by
        apply List.eq_nil_of_length_eq_zero
        simp only [List.length_cons] at hp; omega
      subst hp'; simp only [convR_nil, evalR]; ring
    · obtain ⟨m₁, rfl⟩ : ∃ m₁, m = m₁ + 1 := ⟨m - 1, by omega⟩
      have hp' : p.length ≤ m₁ + 1 := by simp only [List.length_cons] at hp; omega
      have e1 : m₁ + 1 + m' - 1 = m₁ + m' := by omega
      have e2 : m₁ + 1 - 1 = m₁ := by omega
      rw [e1, e2, ih m₁ hp']; ring

theorem abs_evalR_le (p : Row) (m : ℕ) (hy : |y| ≤ 1) (hz : |z| ≤ 1) :
    |evalR m p y z| ≤ absR p := by
  induction p generalizing m with
  | nil => simp [evalR, absR, lsum_nil]
  | cons c q ih =>
    simp only [evalR, absR, lsum_cons] at ih ⊢
    have h1 : |(c : ℝ) * z ^ m| ≤ (c.natAbs : ℝ) := by
      rw [abs_mul, abs_pow, Nat.cast_natAbs, Int.cast_abs]
      exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (abs_nonneg _) hz)
    have h2 : |y * evalR (m - 1) q y z| ≤ (lsum Int.natAbs q : ℝ) := by
      rw [abs_mul]
      calc |y| * |evalR (m - 1) q y z| ≤ 1 * (lsum Int.natAbs q : ℝ) :=
            mul_le_mul hy (ih (m - 1)) (abs_nonneg _) zero_le_one
        _ = _ := one_mul _
    calc |(c : ℝ) * z ^ m + y * evalR (m - 1) q y z|
        ≤ |(c : ℝ) * z ^ m| + |y * evalR (m - 1) q y z| := abs_add_le _ _
      _ ≤ (c.natAbs : ℝ) + (lsum Int.natAbs q : ℝ) := add_le_add h1 h2
      _ = ((c.natAbs + lsum Int.natAbs q : ℕ) : ℝ) := by push_cast; ring

theorem int_decomp (c : ℤ) (o : ℕ) : c = (o : ℤ) * (c / (o : ℤ)) + c % (o : ℤ) := by
  rcases Nat.eq_zero_or_pos o with h | h
  · subst h; simp
  · have hb : (0 : ℤ) < (o : ℤ) := by exact_mod_cast h
    have := (Int.ediv_emod_unique (a := c) (r := c % (o : ℤ)) (q := c / (o : ℤ)) hb).mp ⟨rfl, rfl⟩
    linarith [this.1]

theorem emod_bounds (c : ℤ) {o : ℕ} (h : 0 < o) : 0 ≤ c % (o : ℤ) ∧ c % (o : ℤ) < (o : ℤ) := by
  have hb : (0 : ℤ) < (o : ℤ) := by exact_mod_cast h
  have := (Int.ediv_emod_unique (a := c) (r := c % (o : ℤ)) (q := c / (o : ℤ)) hb).mp ⟨rfl, rfl⟩
  exact this.2

theorem evalR_round (one : ℕ) (p : Row) (m : ℕ) :
    evalR m p y z = one * evalR m (roundR one p) y z + evalR m (modR one p) y z := by
  induction p generalizing m with
  | nil => simp [roundR, modR, lmap_nil, evalR]
  | cons c q ih =>
    simp only [roundR, modR, lmap_cons, evalR] at ih ⊢
    rw [ih (m - 1)]
    have hc : ((c : ℤ) : ℝ) = (one : ℝ) * ((c / (one : ℤ) : ℤ) : ℝ) + ((c % (one : ℤ) : ℤ) : ℝ) := by
      have := int_decomp c one
      exact_mod_cast this
    rw [hc]; ring

theorem absR_modR (one : ℕ) (hone : 0 < one) (p : Row) : absR (modR one p) = fracR one p := by
  induction p with
  | nil => rfl
  | cons c q ih =>
    simp only [absR, fracR, modR, lmap_cons, lsum_cons] at ih ⊢
    rw [ih]
    have := (emod_bounds c hone).1
    congr 1
    omega

theorem abs_evalR_mod_le (one : ℕ) (hone : 0 < one) (p : Row) (m : ℕ) (hy : |y| ≤ 1) (hz : |z| ≤ 1) :
    |evalR m (modR one p) y z| ≤ fracR one p := by
  rw [← absR_modR one hone p]; exact abs_evalR_le y z _ m hy hz

end RowLemmas

/-! ## Comp lemmas -/

theorem wfC_cons {k : ℕ} {row : Row} {rows : Comp} (h : wfC k (row :: rows) = true) :
    row.length ≤ k + 1 ∧ rows.length ≤ k ∧ wfC (k - 1) rows = true := by
  simp only [wfC, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem wfP_cons {k : ℕ} {C : Comp} {Cs : Poly} (h : wfP k (C :: Cs) = true) :
    wfC k C = true ∧ wfP (k + 1) Cs = true := by
  simp only [wfP, Bool.and_eq_true] at h
  exact h

section CompLemmas
variable (x y z : ℝ)

theorem evalC_addC (P Q : Comp) (k : ℕ) :
    evalC k (addC P Q) x y z = evalC k P x y z + evalC k Q x y z := by
  induction P generalizing k Q with
  | nil => simp [addC_nil, evalC]
  | cons a P ih =>
    cases Q with
    | nil => simp [addC_cons_nil, evalC]
    | cons b Q => rw [addC_cons_cons]; simp only [evalC]; rw [evalR_addR, ih]; ring

theorem evalC_smulC (c : Int) (P : Comp) (k : ℕ) :
    evalC k (smulC c P) x y z = c * evalC k P x y z := by
  induction P generalizing k with
  | nil => simp [smulC, lmap_nil, evalC]
  | cons a P ih =>
    simp only [smulC, lmap_cons, evalC] at ih ⊢
    rw [evalR_smulR, ih]; ring

theorem evalC_lmap_convR (row : Row) (Q : Comp) (k l : ℕ) (hrow : row.length ≤ k + 1)
    (hQ : wfC l Q = true) :
    evalC (k + l) (lmap (convR row) Q) x y z = evalR k row y z * evalC l Q x y z := by
  induction Q generalizing l with
  | nil => simp [lmap_nil, evalC]
  | cons q Q ih =>
    obtain ⟨hq, hQl, hQ'⟩ := wfC_cons hQ
    rw [lmap_cons]; simp only [evalC]
    rw [evalR_convR y z row q k l hrow hq]
    rcases Nat.eq_zero_or_pos l with h0 | hpos
    · subst h0
      have : Q = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst this; simp only [lmap_nil, evalC]; ring
    · obtain ⟨l₁, rfl⟩ : ∃ l₁, l = l₁ + 1 := ⟨l - 1, by omega⟩
      have e1 : k + (l₁ + 1) - 1 = k + l₁ := by omega
      have e2 : l₁ + 1 - 1 = l₁ := by omega
      rw [e2] at hQ'
      rw [e1, e2, ih l₁ hQ']; ring

theorem evalC_convC (P Q : Comp) (k l : ℕ) (hP : wfC k P = true) (hQ : wfC l Q = true) :
    evalC (k + l) (convC P Q) x y z = evalC k P x y z * evalC l Q x y z := by
  induction P generalizing k with
  | nil => simp [convC_nil, evalC]
  | cons row P ih =>
    obtain ⟨hrow, hPl, hP'⟩ := wfC_cons hP
    rw [convC_cons, evalC_addC, evalC_lmap_convR x y z row Q k l hrow hQ]
    simp only [evalC, evalR]
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · subst h0
      have : P = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst this; simp only [convC_nil, evalC]; ring
    · obtain ⟨k₁, rfl⟩ : ∃ k₁, k = k₁ + 1 := ⟨k - 1, by omega⟩
      have e1 : k₁ + 1 + l - 1 = k₁ + l := by omega
      have e2 : k₁ + 1 - 1 = k₁ := by omega
      rw [e2] at hP'
      rw [e1, e2, ih k₁ hP']; ring

theorem abs_evalC_le (P : Comp) (k : ℕ) (hx : |x| ≤ 1) (hy : |y| ≤ 1) (hz : |z| ≤ 1) :
    |evalC k P x y z| ≤ absC P := by
  induction P generalizing k with
  | nil => simp [evalC, absC, lsum_nil]
  | cons row P ih =>
    simp only [evalC, absC, lsum_cons] at ih ⊢
    have h1 := abs_evalR_le y z row k hy hz
    have h2 : |x * evalC (k - 1) P x y z| ≤ (lsum absR P : ℝ) := by
      rw [abs_mul]
      calc |x| * |evalC (k - 1) P x y z| ≤ 1 * (lsum absR P : ℝ) :=
            mul_le_mul hx (ih (k - 1)) (abs_nonneg _) zero_le_one
        _ = _ := one_mul _
    calc _ ≤ |evalR k row y z| + |x * evalC (k - 1) P x y z| := abs_add_le _ _
      _ ≤ (absR row : ℝ) + (lsum absR P : ℝ) := add_le_add h1 h2
      _ = _ := by push_cast; ring

theorem evalC_round (one : ℕ) (P : Comp) (k : ℕ) :
    evalC k P x y z = one * evalC k (roundC one P) x y z + evalC k (modC one P) x y z := by
  induction P generalizing k with
  | nil => simp [roundC, modC, lmap_nil, evalC]
  | cons row P ih =>
    simp only [roundC, modC, lmap_cons, evalC] at ih ⊢
    rw [ih (k - 1), evalR_round y z one row k]; ring

theorem absC_modC (one : ℕ) (hone : 0 < one) (P : Comp) : absC (modC one P) = fracC one P := by
  induction P with
  | nil => rfl
  | cons row P ih =>
    simp only [absC, fracC, modC, lmap_cons, lsum_cons] at ih ⊢
    rw [ih, absR_modR one hone row]

end CompLemmas

/-! ## Poly lemmas -/

section PolyLemmas
variable (x y z : ℝ)

theorem evalP_addP (A B : Poly) (k : ℕ) :
    evalP k (addP A B) x y z = evalP k A x y z + evalP k B x y z := by
  induction A generalizing k B with
  | nil => simp [addP_nil, evalP]
  | cons a A ih =>
    cases B with
    | nil => simp [addP_cons_nil, evalP]
    | cons b B => rw [addP_cons_cons]; simp only [evalP]; rw [evalC_addC, ih]; ring

theorem evalP_smulP (c : Int) (A : Poly) (k : ℕ) :
    evalP k (smulP c A) x y z = c * evalP k A x y z := by
  induction A generalizing k with
  | nil => simp [smulP, lmap_nil, evalP]
  | cons a A ih =>
    simp only [smulP, lmap_cons, evalP] at ih ⊢
    rw [evalC_smulC, ih]; ring

theorem abs_evalP_le (A : Poly) (k : ℕ) (hx : |x| ≤ 1) (hy : |y| ≤ 1) (hz : |z| ≤ 1) :
    |evalP k A x y z| ≤ absP A := by
  induction A generalizing k with
  | nil => simp [evalP, absP, lsum_nil]
  | cons a A ih =>
    simp only [evalP, absP, lsum_cons] at ih ⊢
    have h1 := abs_evalC_le x y z a k hx hy hz
    calc _ ≤ |evalC k a x y z| + |evalP (k + 1) A x y z| := abs_add_le _ _
      _ ≤ (absC a : ℝ) + (lsum absC A : ℝ) := add_le_add h1 (ih (k + 1))
      _ = _ := by push_cast; ring

theorem evalP_round (one : ℕ) (A : Poly) (k : ℕ) :
    evalP k A x y z = one * evalP k (roundP one A) x y z + evalP k (modP one A) x y z := by
  induction A generalizing k with
  | nil => simp [roundP, modP, lmap_nil, evalP]
  | cons a A ih =>
    simp only [roundP, modP, lmap_cons, evalP] at ih ⊢
    rw [ih (k + 1), evalC_round x y z one a k]; ring

theorem absP_modP (one : ℕ) (hone : 0 < one) (A : Poly) : absP (modP one A) = fracP one A := by
  induction A with
  | nil => rfl
  | cons a A ih =>
    simp only [absP, fracP, modP, lmap_cons, lsum_cons] at ih ⊢
    rw [ih, absC_modC one hone a]

theorem abs_evalP_mod_le (one : ℕ) (hone : 0 < one) (A : Poly) (k : ℕ)
    (hx : |x| ≤ 1) (hy : |y| ≤ 1) (hz : |z| ≤ 1) :
    |evalP k (modP one A) x y z| ≤ fracP one A := by
  rw [← absP_modP one hone A]; exact abs_evalP_le x y z _ k hx hy hz

theorem evalP_lmap_convC (a : Comp) (B : Poly) (s t : ℕ) (ha : wfC s a = true) (hB : wfP t B = true) :
    evalP (s + t) (lmap (convC a) B) x y z = evalC s a x y z * evalP t B x y z := by
  induction B generalizing t with
  | nil => simp [lmap_nil, evalP]
  | cons b B ih =>
    obtain ⟨hb, hB'⟩ := wfP_cons hB
    rw [lmap_cons]; simp only [evalP]
    rw [evalC_convC x y z a b s t ha hb]
    have e : s + t + 1 = s + (t + 1) := by omega
    rw [e, ih (t + 1) hB']; ring

theorem wfP_ltake (B : Poly) (t n : ℕ) (hB : wfP t B = true) : wfP t (ltake B n) = true := by
  induction B generalizing t n with
  | nil => rfl
  | cons b B ih =>
    cases n with
    | zero => rfl
    | succ n =>
      obtain ⟨hb, hB'⟩ := wfP_cons hB
      rw [ltake_succ]; simp only [wfP, Bool.and_eq_true]
      exact ⟨hb, ih (t + 1) n hB'⟩

theorem evalP_take_drop (B : Poly) (t n : ℕ) :
    evalP t B x y z = evalP t (ltake B n) x y z + evalP (t + n) (ldrop B n) x y z := by
  induction B generalizing t n with
  | nil => simp [ltake_nil, ldrop_nil, evalP]
  | cons b B ih =>
    cases n with
    | zero => simp [ltake_zero, ldrop_zero', evalP]
    | succ n =>
      rw [ltake_succ, ldrop_succ]; simp only [evalP]
      rw [ih (t + 1) n]
      have e : t + 1 + n = t + (n + 1) := by omega
      rw [e]; ring

theorem absP_eq_sumN (A : Poly) : absP A = sumN (gAbs A) := by
  simp only [absP, sumN, gAbs, lsum_lmap]; rfl

theorem sumN_ldrop_gAbs (B : Poly) (n : ℕ) : sumN (ldrop (gAbs B) n) = absP (ldrop B n) := by
  rw [absP_eq_sumN]
  show sumN (ldrop (lmap absC B) n) = sumN (lmap absC (ldrop B n))
  rw [lmap_ldrop]

theorem gAbs_cons (a : Comp) (A : Poly) : gAbs (a :: A) = absC a :: gAbs A := rfl

theorem gmul_spec (A B : Poly) (s t n : ℕ) (hA : wfP s A = true) (hB : wfP t B = true)
    (hx : |x| ≤ 1) (hy : |y| ≤ 1) (hz : |z| ≤ 1) :
    |evalP s A x y z * evalP t B x y z - evalP (s + t) (gmul A B n) x y z|
      ≤ (dropM (gAbs A) (gAbs B) n : ℝ) := by
  induction A generalizing s n with
  | nil => simp [evalP, gmul_nil, dropM_nil]
  | cons a A ih =>
    obtain ⟨ha, hA'⟩ := wfP_cons hA
    have hsplit := evalP_take_drop x y z B t (n + 1)
    have hkeep := evalP_lmap_convC x y z a (ltake B (n + 1)) s t ha (wfP_ltake B t (n + 1) hB)
    have hdrop : |evalP (t + (n + 1)) (ldrop B (n + 1)) x y z| ≤ (sumN (ldrop (gAbs B) (n + 1)) : ℝ) := by
      rw [sumN_ldrop_gAbs]; exact abs_evalP_le x y z _ _ hx hy hz
    have hca : |evalC s a x y z| ≤ (absC a : ℝ) := abs_evalC_le x y z a s hx hy hz
    have hterm : |evalC s a x y z * evalP (t + (n + 1)) (ldrop B (n + 1)) x y z|
        ≤ (absC a : ℝ) * (sumN (ldrop (gAbs B) (n + 1)) : ℝ) := by
      rw [abs_mul]; exact mul_le_mul hca hdrop (abs_nonneg _) (Nat.cast_nonneg _)
    cases n with
    | zero =>
      rw [gmul_cons_zero, evalP_addP, gAbs_cons, dropM_cons_zero]
      simp only [evalP]
      rw [hkeep]
      have hAB : |evalP (s + 1) A x y z * evalP t B x y z| ≤ (sumN (gAbs A) : ℝ) * (sumN (gAbs B) : ℝ) := by
        rw [abs_mul, ← absP_eq_sumN, ← absP_eq_sumN]
        exact mul_le_mul (abs_evalP_le x y z _ _ hx hy hz) (abs_evalP_le x y z _ _ hx hy hz)
          (abs_nonneg _) (Nat.cast_nonneg _)
      have eq : (evalC s a x y z + evalP (s + 1) A x y z) * evalP t B x y z
          - (evalC s a x y z * evalP t (ltake B (0 + 1)) x y z + 0)
          = evalC s a x y z * evalP (t + (0 + 1)) (ldrop B (0 + 1)) x y z
            + evalP (s + 1) A x y z * evalP t B x y z := by
        rw [hsplit]; ring
      rw [eq]
      push_cast
      calc _ ≤ |evalC s a x y z * evalP (t + (0 + 1)) (ldrop B (0 + 1)) x y z|
            + |evalP (s + 1) A x y z * evalP t B x y z| := abs_add_le _ _
        _ ≤ _ := add_le_add hterm hAB
    | succ n =>
      rw [gmul_cons_succ, evalP_addP, gAbs_cons, dropM_cons_succ]
      simp only [evalP, evalC]
      rw [hkeep]
      have ih' := ih (s + 1) n hA'
      have e : s + t + 1 = s + 1 + t := by omega
      rw [e]
      have eq : (evalC s a x y z + evalP (s + 1) A x y z) * evalP t B x y z
          - (evalC s a x y z * evalP t (ltake B (n + 1 + 1)) x y z + (0 + evalP (s + 1 + t) (gmul A B n) x y z))
          = evalC s a x y z * evalP (t + (n + 1 + 1)) (ldrop B (n + 1 + 1)) x y z
            + (evalP (s + 1) A x y z * evalP t B x y z - evalP (s + 1 + t) (gmul A B n) x y z) := by
        rw [hsplit]; ring
      rw [eq]
      push_cast
      calc _ ≤ |evalC s a x y z * evalP (t + (n + 1 + 1)) (ldrop B (n + 1 + 1)) x y z|
            + |evalP (s + 1) A x y z * evalP t B x y z - evalP (s + 1 + t) (gmul A B n) x y z| :=
            abs_add_le _ _
        _ ≤ _ := add_le_add hterm ih'

end PolyLemmas

/-! ## Soundness of the TM operations -/

section TMLemmas
variable {one : ℕ}

theorem le_cdiv (x one : ℕ) (hone : 0 < one) : (x : ℝ) / one ≤ (cdiv x one : ℝ) := by
  have h := Nat.div_add_mod (x + one - 1) one
  have hlt := Nat.mod_lt (x + one - 1) hone
  have hq : x ≤ one * cdiv x one := by unfold cdiv; omega
  have hone' : (0 : ℝ) < one := by exact_mod_cast hone
  rw [div_le_iff₀ hone']
  have : (x : ℝ) ≤ (one : ℝ) * (cdiv x one : ℝ) := by exact_mod_cast hq
  linarith

theorem Contains.of_eval {T : TM} {f : ℝ → ℝ → ℝ → ℝ}
    (h : T.ok = true → ∀ x y z : ℝ, |x| ≤ 1 → |y| ≤ 1 → |z| ≤ 1 →
      |f x y z - evalP 0 T.p x y z / one| ≤ (T.r : ℝ) / one) : Contains one T f := h

theorem Contains.weaken {T : TM} {f : ℝ → ℝ → ℝ → ℝ} (h : Contains one T f) {r' : ℕ} (hr : T.r ≤ r')
    (hone : 0 < one) : Contains one ⟨T.p, r', T.ok⟩ f := by
  intro hok x y z hx hy hz
  have h1 := h hok x y z hx hy hz
  have : (T.r : ℝ) / one ≤ (r' : ℝ) / one :=
    div_le_div_of_nonneg_right (by exact_mod_cast hr) (by positivity)
  exact h1.trans this

theorem Contains.congr {T : TM} {f g : ℝ → ℝ → ℝ → ℝ} (h : Contains one T f)
    (hfg : ∀ x y z : ℝ, |x| ≤ 1 → |y| ≤ 1 → |z| ≤ 1 → f x y z = g x y z) : Contains one T g := by
  intro hok x y z hx hy hz
  rw [← hfg x y z hx hy hz]; exact h hok x y z hx hy hz

theorem evalP_lin (c0 cx cy cz : Int) (x y z : ℝ) :
    evalP 0 (TM.lin c0 cx cy cz).p x y z = c0 + cx * x + cy * y + cz * z := by
  simp [TM.lin, evalP, evalC, evalR]; ring

theorem Contains.lin (c0 cx cy cz : Int) :
    Contains one (TM.lin c0 cx cy cz) (fun x y z => ((c0 : ℝ) + cx * x + cy * y + cz * z) / one) := by
  intro _ x y z _ _ _
  rw [evalP_lin]; simp [TM.lin]

theorem Contains.const (c : Int) (r : ℕ) (v : ℝ) (hv : |v - c / one| ≤ (r : ℝ) / one) :
    Contains one (TM.const c r) (fun _ _ _ => v) := by
  intro _ x y z _ _ _
  have : evalP 0 (TM.const c r).p x y z = c := by simp [TM.const, evalP, evalC, evalR]
  rw [this]; exact hv

theorem Contains.add {A B : TM} {f g : ℝ → ℝ → ℝ → ℝ} (hA : Contains one A f) (hB : Contains one B g) :
    Contains one (TM.add A B) (fun x y z => f x y z + g x y z) := by
  intro hok x y z hx hy hz
  simp only [TM.add, Bool.and_eq_true] at hok
  have h1 := hA hok.1 x y z hx hy hz
  have h2 := hB hok.2 x y z hx hy hz
  simp only [TM.add]
  rw [evalP_addP]
  have e : f x y z + g x y z - (evalP 0 A.p x y z + evalP 0 B.p x y z) / one
      = (f x y z - evalP 0 A.p x y z / one) + (g x y z - evalP 0 B.p x y z / one) := by ring
  rw [e]
  calc _ ≤ |f x y z - evalP 0 A.p x y z / one| + |g x y z - evalP 0 B.p x y z / one| := abs_add_le _ _
    _ ≤ (A.r : ℝ) / one + (B.r : ℝ) / one := add_le_add h1 h2
    _ = _ := by push_cast; ring

theorem Contains.neg {A : TM} {f : ℝ → ℝ → ℝ → ℝ} (hA : Contains one A f) :
    Contains one (TM.neg A) (fun x y z => -f x y z) := by
  intro hok x y z hx hy hz
  have h1 := hA hok x y z hx hy hz
  simp only [TM.neg] at hok ⊢
  rw [evalP_smulP]
  have e : -f x y z - ((-1 : ℤ) : ℝ) * evalP 0 A.p x y z / one = -(f x y z - evalP 0 A.p x y z / one) := by
    push_cast; ring
  rw [e, abs_neg]; exact h1

theorem Contains.sub {A B : TM} {f g : ℝ → ℝ → ℝ → ℝ} (hA : Contains one A f) (hB : Contains one B g) :
    Contains one (TM.sub A B) (fun x y z => f x y z - g x y z) := by
  have := Contains.add hA (Contains.neg hB)
  simpa [TM.sub, sub_eq_add_neg] using this

theorem Contains.addc {A : TM} {f : ℝ → ℝ → ℝ → ℝ} (hA : Contains one A f) (c : Int) :
    Contains one (TM.addc A c) (fun x y z => f x y z + c / one) := by
  intro hok x y z hx hy hz
  have h1 := hA hok x y z hx hy hz
  simp only [TM.addc] at hok ⊢
  rw [evalP_addP]
  have : evalP 0 [[[c]]] x y z = c := by simp [evalP, evalC, evalR]
  rw [this]
  have e : f x y z + c / one - (evalP 0 A.p x y z + c) / one = f x y z - evalP 0 A.p x y z / one := by ring
  rw [e]; exact h1

theorem Contains.scaleInt {A : TM} {f : ℝ → ℝ → ℝ → ℝ} (hA : Contains one A f) (k : Int) :
    Contains one (TM.scaleInt A k) (fun x y z => k * f x y z) := by
  intro hok x y z hx hy hz
  have h1 := hA hok x y z hx hy hz
  simp only [TM.scaleInt] at hok ⊢
  rw [evalP_smulP]
  have e : (k : ℝ) * f x y z - (k : ℝ) * evalP 0 A.p x y z / one = k * (f x y z - evalP 0 A.p x y z / one) := by
    ring
  rw [e, abs_mul]
  have hk : |(k : ℝ)| = (k.natAbs : ℝ) := by rw [Nat.cast_natAbs, Int.cast_abs]
  rw [hk]
  calc (k.natAbs : ℝ) * |f x y z - evalP 0 A.p x y z / one| ≤ (k.natAbs : ℝ) * ((A.r : ℝ) / one) :=
        mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
    _ = _ := by push_cast; ring

/-- Pure real-arithmetic product error. -/
theorem mul_err {f g a b ea eb : ℝ} (h1 : |f - a| ≤ ea) (h2 : |g - b| ≤ eb) :
    |f * g - a * b| ≤ ea * |b| + |a| * eb + ea * eb := by
  have e : f * g - a * b = (f - a) * b + a * (g - b) + (f - a) * (g - b) := by ring
  rw [e]
  have hea : 0 ≤ ea := (abs_nonneg _).trans h1
  calc _ ≤ |(f - a) * b| + |a * (g - b)| + |(f - a) * (g - b)| := abs_add_three _ _ _
    _ = |f - a| * |b| + |a| * |g - b| + |f - a| * |g - b| := by rw [abs_mul, abs_mul, abs_mul]
    _ ≤ ea * |b| + |a| * eb + ea * eb := by
      gcongr

theorem Contains.mulc (hone : 0 < one) {A : TM} {f : ℝ → ℝ → ℝ → ℝ} (hA : Contains one A f) (c : Int) :
    Contains one (TM.mulc one A c) (fun x y z => (c : ℝ) / one * f x y z) := by
  intro hok x y z hx hy hz
  have h1 := hA hok x y z hx hy hz
  simp only [TM.mulc] at hok ⊢
  have hone' : (0 : ℝ) < one := by exact_mod_cast hone
  set K := smulP c A.p
  have hK : evalP 0 K x y z = c * evalP 0 A.p x y z := evalP_smulP x y z c A.p 0
  have hR := evalP_round x y z one K 0
  have hM := abs_evalP_mod_le x y z one hone K 0 hx hy hz
  -- (c/one) f - R/one = (c/one)(f - a/one) + M/one^2
  have e : (c : ℝ) / one * f x y z - evalP 0 (roundP one K) x y z / one
      = (c : ℝ) / one * (f x y z - evalP 0 A.p x y z / one) + evalP 0 (modP one K) x y z / (one * one) := by
    have : evalP 0 (roundP one K) x y z = (evalP 0 K x y z - evalP 0 (modP one K) x y z) / one := by
      field_simp; linarith
    rw [this, hK]; field_simp; ring
  rw [e]
  have hc : |(c : ℝ)| = (c.natAbs : ℝ) := by rw [Nat.cast_natAbs, Int.cast_abs]
  have b1 : |(c : ℝ) / one * (f x y z - evalP 0 A.p x y z / one)| ≤ (A.r * c.natAbs : ℕ) / ((one : ℝ) * one) := by
    rw [abs_mul, abs_div, hc, abs_of_pos hone']
    calc (c.natAbs : ℝ) / one * |f x y z - evalP 0 A.p x y z / one| ≤ (c.natAbs : ℝ) / one * ((A.r : ℝ) / one) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = _ := by push_cast; field_simp
  have b2 : |evalP 0 (modP one K) x y z / (one * one)| ≤ (fracP one K : ℝ) / ((one : ℝ) * one) := by
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < one * one)]
    exact div_le_div_of_nonneg_right hM (by positivity)
  have hcd := le_cdiv (A.r * c.natAbs + fracP one K) one hone
  calc _ ≤ |(c : ℝ) / one * (f x y z - evalP 0 A.p x y z / one)| + |evalP 0 (modP one K) x y z / (one * one)| :=
        abs_add_le _ _
    _ ≤ (A.r * c.natAbs : ℕ) / ((one : ℝ) * one) + (fracP one K : ℝ) / ((one : ℝ) * one) := add_le_add b1 b2
    _ = ((A.r * c.natAbs + fracP one K : ℕ) : ℝ) / one / one := by push_cast; field_simp
    _ ≤ (cdiv (A.r * c.natAbs + fracP one K) one : ℝ) / one :=
        div_le_div_of_nonneg_right hcd (by positivity)

theorem Contains.mul (hone : 0 < one) (N : ℕ) {A B : TM} {f g : ℝ → ℝ → ℝ → ℝ}
    (hA : Contains one A f) (hB : Contains one B g) :
    Contains one (TM.mul one N A B) (fun x y z => f x y z * g x y z) := by
  intro hok x y z hx hy hz
  simp only [TM.mul, Bool.and_eq_true] at hok
  obtain ⟨⟨⟨hokA, hokB⟩, hwA⟩, hwB⟩ := hok
  have h1 := hA hokA x y z hx hy hz
  have h2 := hB hokB x y z hx hy hz
  have hone' : (0 : ℝ) < one := by exact_mod_cast hone
  simp only [TM.mul]
  set a := evalP 0 A.p x y z
  set b := evalP 0 B.p x y z
  set K := gmul A.p B.p N
  have hG := gmul_spec x y z A.p B.p 0 0 N hwA hwB hx hy hz
  simp only [Nat.add_zero] at hG
  have hR := evalP_round x y z one K 0
  have hM := abs_evalP_mod_le x y z one hone K 0 hx hy hz
  have hAa : |a| ≤ absP A.p := abs_evalP_le x y z A.p 0 hx hy hz
  have hBb : |b| ≤ absP B.p := abs_evalP_le x y z B.p 0 hx hy hz
  -- product error against a*b/one^2
  have hE := mul_err h1 h2
  have hE' : |f x y z * g x y z - a / one * (b / one)|
      ≤ ((A.r * absP B.p + B.r * absP A.p + A.r * B.r : ℕ) : ℝ) / ((one : ℝ) * one) := by
    refine hE.trans ?_
    rw [abs_div, abs_div, abs_of_pos hone']
    have : (A.r : ℝ) / one * (|b| / one) + |a| / one * ((B.r : ℝ) / one) + (A.r : ℝ) / one * ((B.r : ℝ) / one)
        = ((A.r : ℝ) * |b| + |a| * B.r + (A.r : ℝ) * B.r) / (one * one) := by field_simp
    rw [this]
    apply div_le_div_of_nonneg_right _ (by positivity)
    push_cast
    have hAr : (0 : ℝ) ≤ A.r := Nat.cast_nonneg _
    have hBr : (0 : ℝ) ≤ B.r := Nat.cast_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left hBb hAr, mul_le_mul_of_nonneg_right hAa hBr]
  -- assemble
  have e : f x y z * g x y z - evalP 0 (roundP one K) x y z / one
      = (f x y z * g x y z - a / one * (b / one)) + (a * b - evalP 0 K x y z) / (one * one)
        + evalP 0 (modP one K) x y z / (one * one) := by
    have : evalP 0 (roundP one K) x y z = (evalP 0 K x y z - evalP 0 (modP one K) x y z) / one := by
      field_simp; linarith
    rw [this]; field_simp; ring
  rw [e]
  have b2 : |(a * b - evalP 0 K x y z) / (one * one)| ≤ (dropM (gAbs A.p) (gAbs B.p) N : ℝ) / ((one : ℝ) * one) := by
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < one * one)]
    exact div_le_div_of_nonneg_right hG (by positivity)
  have b3 : |evalP 0 (modP one K) x y z / (one * one)| ≤ (fracP one K : ℝ) / ((one : ℝ) * one) := by
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < one * one)]
    exact div_le_div_of_nonneg_right hM (by positivity)
  have hcd := le_cdiv (dropM (gAbs A.p) (gAbs B.p) N + (A.r * absP B.p + B.r * absP A.p + A.r * B.r)
    + fracP one K) one hone
  unfold mulRem
  calc _ ≤ |f x y z * g x y z - a / one * (b / one)| + |(a * b - evalP 0 K x y z) / (one * one)|
          + |evalP 0 (modP one K) x y z / (one * one)| := abs_add_three _ _ _
    _ ≤ ((A.r * absP B.p + B.r * absP A.p + A.r * B.r : ℕ) : ℝ) / ((one : ℝ) * one)
          + (dropM (gAbs A.p) (gAbs B.p) N : ℝ) / ((one : ℝ) * one) + (fracP one K : ℝ) / ((one : ℝ) * one) := by
        gcongr
    _ = ((dropM (gAbs A.p) (gAbs B.p) N + (A.r * absP B.p + B.r * absP A.p + A.r * B.r) + fracP one K : ℕ) : ℝ)
          / one / one := by push_cast; field_simp; ring
    _ ≤ _ := div_le_div_of_nonneg_right hcd (by positivity)

/-- `c0` / rest decomposition: `|evalP 0 A - c0P A| ≤ absP A - |c0P A|`. -/
theorem abs_evalP_sub_c0 (A : Poly) (x y z : ℝ) (hx : |x| ≤ 1) (hy : |y| ≤ 1) (hz : |z| ≤ 1) :
    |evalP 0 A x y z - c0P A| ≤ (absP A : ℝ) - |(c0P A : ℝ)| := by
  rcases A with _ | ⟨C, Cs⟩
  · simp [evalP, c0P, absP, lsum_nil]
  · rcases C with _ | ⟨row, rows⟩
    · simp only [evalP, evalC, c0P, List.headD, absP, lsum_cons, absC, lsum_nil, zero_add, Int.cast_zero,
        abs_zero, sub_zero, Nat.cast_add, Nat.cast_zero]
      exact abs_evalP_le x y z Cs 1 hx hy hz
    · rcases row with _ | ⟨c, q⟩
      · simp only [evalP, evalC, evalR, c0P, List.headD, absP, lsum_cons, absC, absR, lsum_nil, zero_add,
          Int.cast_zero, abs_zero, sub_zero, Nat.cast_add, Nat.cast_zero]
        have h1 := abs_evalC_le x y z rows (0 - 1) hx hy hz
        have h2 := abs_evalP_le x y z Cs (0 + 1) hx hy hz
        calc _ ≤ |x * evalC (0 - 1) rows x y z| + |evalP (0 + 1) Cs x y z| := abs_add_le _ _
          _ ≤ 1 * (absC rows : ℝ) + (absP Cs : ℝ) := by
              gcongr
              rw [abs_mul]; exact mul_le_mul hx h1 (abs_nonneg _) zero_le_one
          _ = _ := by simp [absC, absP, absR]
      · simp only [evalP, evalC, evalR, c0P, List.headD, absP, lsum_cons, absC, absR]
        have h1 := abs_evalR_le y z q (0 - 1) hy hz
        have h2 := abs_evalC_le x y z rows (0 - 1) hx hy hz
        have h3 := abs_evalP_le x y z Cs (0 + 1) hx hy hz
        have hc : |(c : ℝ)| = (c.natAbs : ℝ) := by rw [Nat.cast_natAbs, Int.cast_abs]
        have e : (c : ℝ) * z ^ 0 + y * evalR (0 - 1) q y z + x * evalC (0 - 1) rows x y z
            + evalP (0 + 1) Cs x y z - c
            = y * evalR (0 - 1) q y z + x * evalC (0 - 1) rows x y z + evalP (0 + 1) Cs x y z := by ring
        rw [e, hc]
        calc _ ≤ |y * evalR (0 - 1) q y z| + |x * evalC (0 - 1) rows x y z| + |evalP (0 + 1) Cs x y z| :=
              abs_add_three _ _ _
          _ ≤ 1 * (absR q : ℝ) + 1 * (absC rows : ℝ) + (absP Cs : ℝ) := by
              gcongr
              · rw [abs_mul]; exact mul_le_mul hy h1 (abs_nonneg _) zero_le_one
              · rw [abs_mul]; exact mul_le_mul hx h2 (abs_nonneg _) zero_le_one
          _ = _ := by simp only [absR, absC, absP, lsum_cons]; push_cast; ring

theorem Contains.lower_le (hone : 0 < one) {T : TM} {f : ℝ → ℝ → ℝ → ℝ} (h : Contains one T f)
    (hok : T.ok = true) (x y z : ℝ) (hx : |x| ≤ 1) (hy : |y| ≤ 1) (hz : |z| ≤ 1) :
    (T.lower : ℝ) / one ≤ f x y z := by
  have h1 := h hok x y z hx hy hz
  have h2 := abs_evalP_sub_c0 T.p x y z hx hy hz
  have hone' : (0 : ℝ) < one := by exact_mod_cast hone
  have hlow : (T.lower : ℝ) ≤ evalP 0 T.p x y z - T.r := by
    simp only [TM.lower]; push_cast
    have := neg_abs_le (evalP 0 T.p x y z - c0P T.p)
    linarith
  have h3 := (abs_le.mp h1).1
  have : (T.lower : ℝ) / one ≤ evalP 0 T.p x y z / one - (T.r : ℝ) / one := by
    rw [← sub_div]; exact div_le_div_of_nonneg_right hlow hone'.le
  linarith

theorem Contains.le_upper (hone : 0 < one) {T : TM} {f : ℝ → ℝ → ℝ → ℝ} (h : Contains one T f)
    (hok : T.ok = true) (x y z : ℝ) (hx : |x| ≤ 1) (hy : |y| ≤ 1) (hz : |z| ≤ 1) :
    f x y z ≤ (T.upper : ℝ) / one := by
  have h1 := h hok x y z hx hy hz
  have h2 := abs_evalP_sub_c0 T.p x y z hx hy hz
  have hone' : (0 : ℝ) < one := by exact_mod_cast hone
  have hup : evalP 0 T.p x y z + T.r ≤ (T.upper : ℝ) := by
    simp only [TM.upper]; push_cast
    have := le_abs_self (evalP 0 T.p x y z - c0P T.p)
    linarith
  have h3 := (abs_le.mp h1).2
  have : evalP 0 T.p x y z / one + (T.r : ℝ) / one ≤ (T.upper : ℝ) / one := by
    rw [← add_div]; exact div_le_div_of_nonneg_right hup hone'.le
  linarith

theorem Contains.abs_le_bound (hone : 0 < one) {T : TM} {f : ℝ → ℝ → ℝ → ℝ} (h : Contains one T f)
    (hok : T.ok = true) (x y z : ℝ) (hx : |x| ≤ 1) (hy : |y| ≤ 1) (hz : |z| ≤ 1) :
    |f x y z| ≤ (T.bound : ℝ) / one := by
  have h1 := h hok x y z hx hy hz
  have h2 := abs_evalP_le x y z T.p 0 hx hy hz
  have hone' : (0 : ℝ) < one := by exact_mod_cast hone
  have : |evalP 0 T.p x y z / one| ≤ (absP T.p : ℝ) / one := by
    rw [abs_div, abs_of_pos hone']; exact div_le_div_of_nonneg_right h2 hone'.le
  calc |f x y z| = |(f x y z - evalP 0 T.p x y z / one) + evalP 0 T.p x y z / one| := by ring_nf
    _ ≤ |f x y z - evalP 0 T.p x y z / one| + |evalP 0 T.p x y z / one| := abs_add_le _ _
    _ ≤ (T.r : ℝ) / one + (absP T.p : ℝ) / one := add_le_add h1 this
    _ = _ := by simp only [TM.bound]; push_cast; ring

end TMLemmas

end CKLaneR2.TM3

end


