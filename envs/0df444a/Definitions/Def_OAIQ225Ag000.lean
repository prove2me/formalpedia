-- Prove2me | Definitions.Def_OAIQ225Ag000
-- name    : OAIQ225Ag000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T17:16:19.870986+00:00
-- url     : https://prove2.me/theorems/4c558f6e-3590-4116-b40c-4bc044726bc8
-- title:
--   Definitions bundle OAIQ225Ag000 of the split of OpenAI, Harmonic heights and the Artin K(pi,1) conjecture
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.HarmonicArtin.salvetti_cover_contractible`, carved from OpenAI's openai/math development (OpenAI, *Harmonic heights and the Artin K(pi,1) conjecture*, OpenAI Math Release, September 23, 2026, result family 254, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 406 declarations of OpenAI's Lean: 106 definitions, 8 inductive types or structures, 12 instances and 280 theorems. The definitions and types are `Convexity.StdSimplex.equivIcc`, `Convexity.StdSimplex.homeomorphI`, `Convexity.StdSimplex.subBarycenter`, `Convexity.StdSimplex.topologicalSpaceInduced`, `OAI.HarmonicArtin.BinaryProductBoundary`, `OAI.HarmonicArtin.BinaryProductBox`, `OAI.HarmonicArtin.ConeAttachment`, `OAI.HarmonicArtin.ConeAttachmentRel`, `OAI.HarmonicArtin.CoxeterExchange.IsParabolicMinimum`, `OAI.HarmonicArtin.CoxeterExchange.SignedGroup`, `OAI.HarmonicArtin.CoxeterExchange.Signs`, `OAI.HarmonicArtin.CoxeterExchange.WeakPrefix`, `OAI.HarmonicArtin.CoxeterExchange.altList`, `OAI.HarmonicArtin.CoxeterExchange.altNext`, `OAI.HarmonicArtin.CoxeterExchange.coeff`, `OAI.HarmonicArtin.CoxeterExchange.delta`, `OAI.HarmonicArtin.CoxeterExchange.parabolic`, `OAI.HarmonicArtin.CoxeterExchange.restrictedMatrix`, `OAI.HarmonicArtin.CoxeterExchange.restrictionHom`, `OAI.HarmonicArtin.CoxeterExchange.signAction`, `OAI.HarmonicArtin.CoxeterExchange.signedGenerator`, `OAI.HarmonicArtin.CoxeterExchange.signedLift`, `OAI.HarmonicArtin.Deligne`, `OAI.HarmonicArtin.DeligneRealization`, `OAI.HarmonicArtin.EarlyDelay`, `OAI.HarmonicArtin.FiniteFusionEdge`, `OAI.HarmonicArtin.FiveBlock.Index`, `OAI.HarmonicArtin.FiveBlock.differential`, `OAI.HarmonicArtin.FiveBlock.homotopy`, `OAI.HarmonicArtin.FiveBlock.identity`, `OAI.HarmonicArtin.FiveBlock.injection`, `OAI.HarmonicArtin.FiveBlock.projection`, `OAI.HarmonicArtin.FiveBlock.reverseDifferential`, `OAI.HarmonicArtin.FiveBlock.reverseHomotopy`, `OAI.HarmonicArtin.FiveBlock.reverseInjection`, `OAI.HarmonicArtin.FiveBlock.reverseProjection`, `OAI.HarmonicArtin.FrontLinked`, `OAI.HarmonicArtin.FusionEdge`, `OAI.HarmonicArtin.FusionEdge.dimension`, `OAI.HarmonicArtin.FusionEdge.multiplicity` and 74 more.
--
--   **Sources.** They come from these modules of lean/OAI/Topology, in whole or in part: `ArtinGroups_Coxeter_AltList`, `ArtinGroups_Coxeter_AltListMap`, `ArtinGroups_Coxeter_AltListPairDescent`, `ArtinGroups_Coxeter_AltListReduced`, `ArtinGroups_Coxeter_AltNext`, `ArtinGroups_Coxeter_AlternatingNextRoot`, `ArtinGroups_Coxeter_CommonWeakPrefixMaximal`, `ArtinGroups_Coxeter_InverseParabolicMinimum`, `ArtinGroups_Coxeter_Parabolic`, `ArtinGroups_Coxeter_PositiveBraidRelations`, `ArtinGroups_Coxeter_ReducedWordProperty`, `ArtinGroups_Coxeter_RestrictedMatrix`, `ArtinGroups_Coxeter_RightParabolicDecomposition`, `ArtinGroups_Coxeter_Signs`, `ArtinGroups_Coxeter_WeakPrefix`, `ArtinGroups_Coxeter_WordProdEquiv`, `ArtinGroups_DeligneDefinitions`, `ArtinGroups_Diagrams_Index`, `ArtinGroups_Diagrams_ReverseDifferential`, `ArtinGroups_Functors_Placement`, `ArtinGroups_Geometry_Cartan`, `ArtinGroups_Geometry_CartanRestricted`, `ArtinGroups_Geometry_CoordinateExtension`, `ArtinGroups_Geometry_DihedralScalar`, `ArtinGroups_Geometry_Reflect`, `ArtinGroups_Geometry_RestrictionLength`, `ArtinGroups_Geometry_RootCoeffAltExtension`, `ArtinGroups_Geometry_RootNonnegAscent`, `ArtinGroups_Geometry_TrigPhasePower`, `ArtinGroups_Geometry_TrigPhaseSqPrimitive`, `ArtinGroups_Harmonic_BinaryProductBoundary`, `ArtinGroups_Harmonic_ConeAttachmentRel`, `ArtinGroups_Harmonic_DimensionPosMultiplicityPos`, `ArtinGroups_Harmonic_EarlyDelay`, `ArtinGroups_Harmonic_FiniteFusionEdge`, `ArtinGroups_Harmonic_FusionFactorStep`, `ArtinGroups_Harmonic_FusionLabel`, `ArtinGroups_Harmonic_FusionRest`, `ArtinGroups_Harmonic_FusionVertex`, `ArtinGroups_Harmonic_GeneratorPlacement`, `ArtinGroups_Harmonic_Level`, `ArtinGroups_Harmonic_PositiveDegreeHom`, `ArtinGroups_Harmonic_PositivePrefix`, `ArtinGroups_Harmonic_QuantumNumber`, `ArtinGroups_Harmonic_ReducedExpression`, `ArtinGroups_Harmonic_SimpleFrontLink`, `ArtinGroups_Harmonic_StringAdjacent`, `ArtinGroups_Quivers_Iso`, `ArtinGroups_Quivers_Path`, `ArtinGroups_Quivers_Reduction`, `ArtinGroups_Quivers_ReversibleQuiver`, `ArtinGroups_Quivers_VertexHom`.
--
--   **Imports.** It imports the published bundle `Def_HarmonicArtin`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ225Ag002`, `OAIQ225Ag003` and `OAIQ225Ag004`.
-- source:
--   OpenAI, Harmonic heights and the Artin K(pi,1) conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 254; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Harmonic-heights-and-the-Artin-K-pi-1-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Topology at commit adc7f12

import Mathlib
import Definitions.Def_HarmonicArtin

section
-- module Solutions.OAIQ225_AG.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Quivers_ReversibleQuiver
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin

structure ReversibleQuiver (V A : Type*) where
  source : A → V
  target : A → V
  reverse : A ≃ A
  reverse_reverse : ∀ a, reverse (reverse a) = a
  source_reverse : ∀ a, source (reverse a) = target a
  target_reverse : ∀ a, target (reverse a) = source a

namespace ReversibleQuiver

variable {V A K : Type*} (Q : ReversibleQuiver V A)

@[simp] theorem reverse_reverse_apply (a : A) : Q.reverse (Q.reverse a) = a :=
  Q.reverse_reverse a

def Zigzag (_Q : ReversibleQuiver V A) (K : Type*) := (V → K) × (A → K) × (V → K)

namespace Zigzag

variable {Q}

instance instAddCommGroup [AddCommGroup K] : AddCommGroup (Q.Zigzag K) :=
  inferInstanceAs (AddCommGroup ((V → K) × (A → K) × (V → K)))

instance instModule [CommRing K] : Module K (Q.Zigzag K) :=
  inferInstanceAs (Module K ((V → K) × (A → K) × (V → K)))

def vertex (x : Q.Zigzag K) : V → K := x.1
def arrow (x : Q.Zigzag K) : A → K := x.2.1
def token (x : Q.Zigzag K) : V → K := x.2.2

@[ext] theorem ext {x y : Q.Zigzag K} (h₀ : x.vertex = y.vertex)
    (h₁ : x.arrow = y.arrow) (h₂ : x.token = y.token) : x = y :=
  Prod.ext h₀ (Prod.ext h₁ h₂)

@[simp] theorem vertex_add [AddCommGroup K] (x y : Q.Zigzag K) :
    (x + y).vertex = x.vertex + y.vertex := rfl
@[simp] theorem arrow_add [AddCommGroup K] (x y : Q.Zigzag K) :
    (x + y).arrow = x.arrow + y.arrow := rfl
@[simp] theorem token_add [AddCommGroup K] (x y : Q.Zigzag K) :
    (x + y).token = x.token + y.token := rfl
@[simp] theorem vertex_smul [CommRing K] (c : K) (x : Q.Zigzag K) :
    (c • x).vertex = c • x.vertex := rfl
@[simp] theorem arrow_smul [CommRing K] (c : K) (x : Q.Zigzag K) :
    (c • x).arrow = c • x.arrow := rfl
@[simp] theorem token_smul [CommRing K] (c : K) (x : Q.Zigzag K) :
    (c • x).token = c • x.token := rfl
@[simp] theorem vertex_zero [AddCommGroup K] : (0 : Q.Zigzag K).vertex = 0 := rfl
@[simp] theorem arrow_zero [AddCommGroup K] : (0 : Q.Zigzag K).arrow = 0 := rfl
@[simp] theorem token_zero [AddCommGroup K] : (0 : Q.Zigzag K).token = 0 := rfl

end Zigzag

section Multiplication

variable [CommRing K] [Fintype A] [DecidableEq V]

def leftScale (v : V → K) (a : A → K) : A → K := fun e => v (Q.source e) * a e

def rightScale (a : A → K) (v : V → K) : A → K := fun e => a e * v (Q.target e)

def backtrack (a b : A → K) : V → K :=
  fun i => ∑ e, if Q.source e = i then a e * b (Q.reverse e) else 0

@[simp] theorem backtrack_add_left (a b c : A → K) :
    Q.backtrack (a + b) c = Q.backtrack a c + Q.backtrack b c := by
  ext i
  simp only [backtrack, Pi.add_apply, add_mul]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun e _ => by split_ifs <;> simp

@[simp] theorem backtrack_add_right (a b c : A → K) :
    Q.backtrack a (b + c) = Q.backtrack a b + Q.backtrack a c := by
  ext i
  simp only [backtrack, Pi.add_apply, mul_add]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun e _ => by split_ifs <;> simp

@[simp] theorem backtrack_zero_left (a : A → K) : Q.backtrack 0 a = 0 := by
  ext i
  simp [backtrack]

@[simp] theorem backtrack_zero_right (a : A → K) : Q.backtrack a 0 = 0 := by
  ext i
  simp [backtrack]

theorem backtrack_leftScale (v : V → K) (a b : A → K) :
    Q.backtrack (Q.leftScale v a) b = v * Q.backtrack a b := by
  ext i
  simp only [backtrack, leftScale, Pi.mul_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  split_ifs with he
  · simp [he, mul_assoc]
  · simp

theorem backtrack_rightScale (v : V → K) (a b : A → K) :
    Q.backtrack a (Q.rightScale b v) = Q.backtrack a b * v := by
  ext i
  simp only [backtrack, rightScale, Pi.mul_apply, Finset.sum_mul, Q.target_reverse]
  apply Finset.sum_congr rfl
  intro e _
  split_ifs with he
  · simp [he, mul_assoc]
  · simp

theorem backtrack_balance (v : V → K) (a b : A → K) :
    Q.backtrack (Q.rightScale a v) b = Q.backtrack a (Q.leftScale v b) := by
  ext i
  simp only [backtrack, rightScale, leftScale, Q.source_reverse, mul_assoc]

namespace Zigzag

instance instMul : Mul (Q.Zigzag K) where
  mul x y := (x.vertex * y.vertex,
    Q.leftScale x.vertex y.arrow + Q.rightScale x.arrow y.vertex,
    x.vertex * y.token + x.token * y.vertex + Q.backtrack x.arrow y.arrow)

instance instOne : One (Q.Zigzag K) := ⟨(1, 0, 0)⟩

@[simp] theorem vertex_mul (x y : Q.Zigzag K) :
    (x * y).vertex = x.vertex * y.vertex := rfl
@[simp] theorem arrow_mul (x y : Q.Zigzag K) :
    (x * y).arrow = Q.leftScale x.vertex y.arrow + Q.rightScale x.arrow y.vertex := rfl
@[simp] theorem token_mul (x y : Q.Zigzag K) :
    (x * y).token = x.vertex * y.token + x.token * y.vertex + Q.backtrack x.arrow y.arrow := rfl
omit [Fintype A] [DecidableEq V] in
@[simp] theorem vertex_one : (1 : Q.Zigzag K).vertex = 1 := rfl
omit [Fintype A] [DecidableEq V] in
@[simp] theorem arrow_one : (1 : Q.Zigzag K).arrow = 0 := rfl
omit [Fintype A] [DecidableEq V] in
@[simp] theorem token_one : (1 : Q.Zigzag K).token = 0 := rfl

theorem mul_assoc (x y z : Q.Zigzag K) : (x * y) * z = x * (y * z) := by
  apply ext
  · simp only [vertex_mul, _root_.mul_assoc]
  · ext e
    simp only [arrow_mul, vertex_mul, leftScale, rightScale, Pi.add_apply, Pi.mul_apply]
    ring
  · simp only [token_mul, vertex_mul, arrow_mul, Q.backtrack_add_left,
      Q.backtrack_add_right, Q.backtrack_leftScale, Q.backtrack_rightScale,
      Q.backtrack_balance]
    ring

theorem one_mul (x : Q.Zigzag K) : 1 * x = x := by
  apply ext
  · simp
  · ext e
    simp [leftScale, rightScale]
  · simp

theorem mul_one (x : Q.Zigzag K) : x * 1 = x := by
  apply ext
  · simp
  · ext e
    simp [leftScale, rightScale]
  · simp

theorem mul_add (x y z : Q.Zigzag K) : x * (y + z) = x * y + x * z := by
  apply ext
  · simp [_root_.mul_add]
  · ext e
    simp only [arrow_mul, vertex_add, arrow_add, leftScale, rightScale, Pi.add_apply]
    ring
  · simp only [token_mul, vertex_add, arrow_add, token_add, Q.backtrack_add_right]
    ring

theorem add_mul (x y z : Q.Zigzag K) : (x + y) * z = x * z + y * z := by
  apply ext
  · simp [_root_.add_mul]
  · ext e
    simp only [arrow_mul, vertex_add, arrow_add, leftScale, rightScale, Pi.add_apply]
    ring
  · simp only [token_mul, vertex_add, arrow_add, token_add, Q.backtrack_add_left]
    ring

theorem zero_mul (x : Q.Zigzag K) : 0 * x = 0 := by
  apply ext
  · simp
  · ext e
    simp [leftScale, rightScale]
  · simp

theorem mul_zero (x : Q.Zigzag K) : x * 0 = 0 := by
  apply ext
  · simp
  · ext e
    simp [leftScale, rightScale]
  · simp

instance instRing : Ring (Q.Zigzag K) where
  mul_assoc := mul_assoc Q
  one_mul := one_mul Q
  mul_one := mul_one Q
  left_distrib := mul_add Q
  right_distrib := add_mul Q
  zero_mul := zero_mul Q
  mul_zero := mul_zero Q

section Trace

variable [Fintype V]

def trace (x : Q.Zigzag K) : K := ∑ i, x.token i

@[simp] theorem trace_add (x y : Q.Zigzag K) :
    trace Q (x + y) = trace Q x + trace Q y := by
  simp only [trace, token_add, Pi.add_apply, Finset.sum_add_distrib]

@[simp] theorem trace_zero : trace Q (0 : Q.Zigzag K) = 0 := by
  simp only [trace, token_zero, Pi.zero_apply, Finset.sum_const_zero]

theorem sum_backtrack (a b : A → K) :
    ∑ i, Q.backtrack a b i = ∑ e, a e * b (Q.reverse e) := by
  simp only [backtrack]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  simp

theorem trace_mul_expression (x y : Q.Zigzag K) :
    trace Q (x * y) = (∑ i, (x.vertex i * y.token i + x.token i * y.vertex i)) +
      ∑ e, x.arrow e * y.arrow (Q.reverse e) := by
  simp only [trace, token_mul, Pi.add_apply, Pi.mul_apply, Finset.sum_add_distrib,
    sum_backtrack]

theorem trace_mul_comm (x y : Q.Zigzag K) : trace Q (x * y) = trace Q (y * x) := by
  rw [trace_mul_expression, trace_mul_expression]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    ring
  · apply Fintype.sum_equiv Q.reverse
    intro e
    simp [_root_.mul_comm]

def vertexBasis (i : V) : Q.Zigzag K := (Pi.single i 1, 0, 0)

def tokenBasis (i : V) : Q.Zigzag K := (0, 0, Pi.single i 1)

def arrowBasis [DecidableEq A] (e : A) : Q.Zigzag K := (0, Pi.single e 1, 0)

@[simp] theorem trace_mul_tokenBasis (x : Q.Zigzag K) (i : V) :
    trace Q (x * tokenBasis Q i) = x.vertex i := by
  rw [trace_mul_expression]
  simp [tokenBasis, vertex, token, arrow, Pi.single_apply]

@[simp] theorem trace_mul_vertexBasis (x : Q.Zigzag K) (i : V) :
    trace Q (x * vertexBasis Q i) = x.token i := by
  rw [trace_mul_expression]
  simp [vertexBasis, vertex, token, arrow, Pi.single_apply]

@[simp] theorem trace_mul_arrowBasis [DecidableEq A] (x : Q.Zigzag K) (e : A) :
    trace Q (x * arrowBasis Q (Q.reverse e)) = x.arrow e := by
  rw [trace_mul_expression]
  simp [arrowBasis, vertex, token, arrow, Pi.single_apply]

theorem trace_smul_mul (c : K) (x y : Q.Zigzag K) :
    trace Q ((c • x) * y) = c * trace Q (x * y) := by
  rw [trace_mul_expression, trace_mul_expression]
  simp only [vertex_smul, arrow_smul, token_smul, Pi.smul_apply, smul_eq_mul,
    _root_.mul_assoc, ← _root_.mul_add, ← Finset.mul_sum]

theorem trace_mul_smul (c : K) (x y : Q.Zigzag K) :
    trace Q (x * (c • y)) = c * trace Q (x * y) := by
  rw [trace_mul_comm, trace_smul_mul, trace_mul_comm Q y x]

def tracePairing : LinearMap.BilinForm K (Q.Zigzag K) where
  toFun x :=
    { toFun y := trace Q (x * y)
      map_add' := fun y z => by rw [mul_add, trace_add]
      map_smul' := fun c y => by simpa using trace_mul_smul Q c x y }
  map_add' x y := by
    ext z
    exact (congrArg (trace Q) (add_mul Q x y z)).trans (trace_add Q _ _)
  map_smul' c x := by
    ext y
    simpa using trace_smul_mul Q c x y

@[simp] theorem tracePairing_apply (x y : Q.Zigzag K) :
    tracePairing Q x y = trace Q (x * y) := rfl

end Trace

end Zigzag
end Multiplication
end ReversibleQuiver
end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Coxeter_AltList
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.CoxeterExchange
variable {B W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

def altList (i j : B) : ℕ → List B
  | 0 => []
  | n+1 => i :: altList j i n

@[simp] lemma altList_zero (i j : B) : altList i j 0 = [] := rfl
@[simp] lemma altList_succ (i j : B) (n : ℕ) : altList i j (n+1) = i::altList j i n := rfl
@[simp] lemma length_altList (i j : B) (n : ℕ) : (altList i j n).length = n := by
  induction n generalizing i j with
  | zero => rfl
  | succ n ih => simp [ih]

lemma altList_reverse (i j : B) (n : ℕ) :
    altList i j n = (CoxeterSystem.alternatingWord j i n).reverse := by
  induction n generalizing i j with
  | zero => rfl
  | succ n ih => rw [altList_succ, CoxeterSystem.alternatingWord_succ, List.concat_eq_append, List.reverse_append, List.reverse_singleton, ih, List.singleton_append]

lemma take_altList (i j : B) (n k : ℕ) (hk : k ≤ n) :
    (altList i j n).take k = altList i j k := by
  induction k generalizing i j n with
  | zero => simp
  | succ k ih =>
    cases n with
    | zero => omega
    | succ n => simp only [altList_succ, List.take_succ_cons, ih j i n (by omega)]

lemma reduced_not_double (i : B) (u : List B) : ¬ cs.IsReduced (i::i::u) := by
  intro h
  have hb := cs.length_wordProd_le u
  have he := h.eq
  simp only [cs.wordProd_cons, ← mul_assoc, cs.simple_mul_simple_self, one_mul,
    List.length_cons] at he
  omega

lemma reduced_pair_cons_eq_alt (i j : B) (u : List B) (hu : cs.IsReduced (i::u))
    (hJ : ∀ k ∈ u, k ∈ ({i,j} : Set B)) : i::u = altList i j (u.length+1) := by
  induction u generalizing i j with
  | nil => rfl
  | cons k u ih =>
    have hk := hJ k (by simp)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hk
    rcases hk with hk | hk
    · subst k
      exact (reduced_not_double cs i u hu).elim
    · subst k
      rw [List.length_cons, altList_succ]
      congr 1
      apply ih j i
      · simpa only [List.drop_succ_cons, List.drop_zero] using hu.drop 1
      · intro k hk
        simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, or_comm] using
          hJ k (List.mem_cons_of_mem j hk)

lemma wordProd_altList_even (i j : B) (n : ℕ) :
    cs.wordProd (altList i j (2*n)) = (cs.simple i*cs.simple j)^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2*(n+1)=2*n+1+1 by omega, altList_succ, altList_succ,
      cs.wordProd_cons, cs.wordProd_cons, ih, pow_succ']
    simp only [mul_assoc]

lemma wordProd_altList_odd (i j : B) (n : ℕ) :
    cs.wordProd (altList i j (2*n+1)) = (cs.simple i*cs.simple j)^n * cs.simple i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2*(n+1)+1=(2*n+1)+1+1 by omega, altList_succ, altList_succ,
      cs.wordProd_cons, cs.wordProd_cons, ih, pow_succ']
    simp only [mul_assoc]

lemma wordProd_altList_difference (i j : B) (n : ℕ) :
    cs.wordProd (altList i j n) * (cs.wordProd (altList j i n))⁻¹ =
      (cs.simple i*cs.simple j)^n := by
  rcases Nat.even_or_odd' n with ⟨k,rfl | rfl⟩
  · rw [wordProd_altList_even, wordProd_altList_even, ← inv_pow]
    simp only [mul_inv_rev, cs.inv_simple]
    rw [← pow_add]
    congr 1
    omega
  · rw [wordProd_altList_odd, wordProd_altList_odd, mul_inv_rev, cs.inv_simple,
      ← inv_pow]
    simp only [mul_inv_rev, cs.inv_simple]
    calc
      _ = (cs.simple i*cs.simple j)^k * (cs.simple i*cs.simple j) *
          (cs.simple i*cs.simple j)^k := by group
      _ = _ := by rw [← pow_succ, ← pow_add]; congr 1; omega

lemma altList_braid (i j : B) :
    cs.wordProd (altList i j (M i j)) = cs.wordProd (altList j i (M i j)) := by
  rw [altList_reverse, altList_reverse, cs.wordProd_reverse, cs.wordProd_reverse]
  apply congrArg Inv.inv
  simpa only [CoxeterSystem.braidWord, ← M.symmetric i j] using cs.wordProd_braidWord_eq j i

lemma reduced_altList_le (i j : B) (n : ℕ) (hm : 2 ≤ M i j)
    (hn : cs.IsReduced (altList i j n)) : n ≤ M i j := by
  by_contra! hlt
  have hr := hn.take (M i j+1)
  rw [take_altList i j n (M i j+1) (by omega)] at hr
  have he : cs.wordProd (altList i j (M i j+1)) =
      cs.wordProd (altList j i (M i j-1)) := by
    rw [altList_reverse, altList_reverse, cs.wordProd_reverse, cs.wordProd_reverse]
    apply congrArg Inv.inv
    have ht := cs.prod_alternatingWord_eq_prod_alternatingWord_sub j i (M i j+1)
      (by rw [← M.symmetric i j]; omega)
    rw [← M.symmetric i j, show M i j*2-(M i j+1)=M i j-1 by omega] at ht
    exact ht
  have hb := cs.length_wordProd_le (altList j i (M i j-1))
  rw [← he, hr.eq, length_altList, length_altList] at hb
  omega

end HarmonicArtin.CoxeterExchange

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Coxeter_AltListMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.CoxeterExchange
lemma altList_map {B C : Type*} (f : B → C) (i j : B) (n : ℕ) :
    (altList i j n).map f=altList (f i) (f j) n := by
  induction n generalizing i j with
  | zero => rfl
  | succ n ih => simp only [altList_succ,List.map_cons,ih]
end HarmonicArtin.CoxeterExchange

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Coxeter_Signs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.CoxeterExchange

open scoped Classical

variable {W : Type*} [Group W]

abbrev Signs (W : Type*) := Multiplicative (W → ZMod 2)

noncomputable def signAction : W →* MulAut (Signs W) where
  toFun g :=
    { toFun f := Multiplicative.ofAdd (fun t => Multiplicative.toAdd f (g⁻¹ * t * g))
      invFun f := Multiplicative.ofAdd (fun t => Multiplicative.toAdd f (g * t * g⁻¹))
      left_inv f := by
        apply Multiplicative.toAdd.injective
        funext t
        change Multiplicative.toAdd f (g⁻¹ * (g * t * g⁻¹) * g) = Multiplicative.toAdd f t
        group
      right_inv f := by
        apply Multiplicative.toAdd.injective
        funext t
        change Multiplicative.toAdd f (g * (g⁻¹ * t * g) * g⁻¹) = Multiplicative.toAdd f t
        group
      map_mul' f h := rfl }
  map_one' := by
    apply MulEquiv.ext
    intro f
    apply Multiplicative.toAdd.injective
    funext t
    simp
  map_mul' g h := by
    apply MulEquiv.ext
    intro f
    apply Multiplicative.toAdd.injective
    funext t
    change Multiplicative.toAdd f ((g*h)⁻¹*t*(g*h)) =
      Multiplicative.toAdd f (h⁻¹*(g⁻¹*t*g)*h)
    group

abbrev SignedGroup (W : Type*) [Group W] := Signs W ⋊[signAction] W

def coeff (x : SignedGroup W) : W → ZMod 2 := Multiplicative.toAdd x.left

@[simp] lemma coeff_one : coeff (1 : SignedGroup W) = 0 := rfl

@[simp] lemma coeff_mul (x y : SignedGroup W) (t : W) :
    coeff (x*y) t = coeff x t + coeff y (x.right⁻¹ * t * x.right) := rfl

noncomputable def delta (s : W) : W → ZMod 2 := fun t => if t=s then 1 else 0

lemma delta_conj (g s t : W) : delta s (g⁻¹*t*g) = delta (g*s*g⁻¹) t := by
  unfold delta
  congr 1
  apply propext
  constructor
  · intro h
    calc t = g*(g⁻¹*t*g)*g⁻¹ := by group
         _ = g*s*g⁻¹ := by rw [h]
  · intro h
    rw [h]
    group

noncomputable def signedGenerator (s : W) : SignedGroup W :=
  ⟨Multiplicative.ofAdd (delta s),s⟩

@[simp] lemma signedGenerator_right (s : W) : (signedGenerator s).right = s := rfl
@[simp] lemma coeff_signedGenerator (s : W) : coeff (signedGenerator s) = delta s := rfl

lemma coeff_pair (s t r : W) (hs : s*s=1) :
    coeff (signedGenerator s * signedGenerator t) r =
      delta s r + delta (s*t*s) r := by
  rw [coeff_mul,coeff_signedGenerator,coeff_signedGenerator,signedGenerator_right,delta_conj]
  rw [inv_eq_of_mul_eq_one_left hs]

lemma braid_power_transport (s t : W) (n : ℕ) :
    s*(t*s)^n = (s*t)^n*s := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ,pow_succ,← mul_assoc,ih]
    group

lemma pair_pow_conj_first (s t : W) (hs : s*s=1) (ht : t*t=1) (n : ℕ) :
    (s*t)^n*s*((s*t)^n)⁻¹ = (s*t)^(2*n)*s := by
  have hsi : s⁻¹=s := inv_eq_of_mul_eq_one_left hs
  have hti : t⁻¹=t := inv_eq_of_mul_eq_one_left ht
  rw [← inv_pow,mul_inv_rev,hsi,hti,mul_assoc,braid_power_transport s t,
    ← mul_assoc,← pow_add]
  congr 2
  omega

lemma pair_pow_conj_second (s t : W) (hs : s*s=1) (ht : t*t=1) (n : ℕ) :
    (s*t)^n*(s*t*s)*((s*t)^n)⁻¹ = (s*t)^(2*n+1)*s := by
  have h := pair_pow_conj_first s t hs ht n
  calc
    _ = ((s*t)^n*(s*t))*s*((s*t)^n)⁻¹ := by group
    _ = ((s*t)*(s*t)^n)*s*((s*t)^n)⁻¹ := by rw [← pow_succ,pow_succ']
    _ = (s*t)*((s*t)^n*s*((s*t)^n)⁻¹) := by group
    _ = (s*t)*((s*t)^(2*n)*s) := by rw [h]
    _ = _ := by rw [← mul_assoc,← pow_succ']

lemma signed_pair_power_right (s t : W) (n : ℕ) :
    ((signedGenerator s * signedGenerator t)^n).right = (s*t)^n := by
  exact map_pow (SemidirectProduct.rightHom) _ n

lemma coeff_signed_pair_power (s t : W) (hs : s*s=1) (ht : t*t=1) (n : ℕ) (r : W) :
    coeff ((signedGenerator s * signedGenerator t)^n) r =
      ∑ j ∈ Finset.range (2*n), delta ((s*t)^j*s) r := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ,coeff_mul,ih,signed_pair_power_right,coeff_pair s t _ hs]
    rw [delta_conj,delta_conj,pair_pow_conj_first s t hs ht,pair_pow_conj_second s t hs ht]
    have hn : 2*(n+1)=(2*n+1)+1 := by omega
    rw [hn,Finset.sum_range_succ,Finset.sum_range_succ]
    simp only [add_assoc]

lemma signed_pair_power_eq_one (s t : W) (hs : s*s=1) (ht : t*t=1) (n : ℕ)
    (hn : (s*t)^n=1) : (signedGenerator s * signedGenerator t)^n=1 := by
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    funext r
    change coeff ((signedGenerator s * signedGenerator t)^n) r = 0
    rw [coeff_signed_pair_power s t hs ht]
    have he : 2*n=n+n := by omega
    rw [he,Finset.sum_range_add]
    have hh : (∑ j ∈ Finset.range n,delta ((s*t)^(n+j)*s) r) =
        ∑ j ∈ Finset.range n,delta ((s*t)^j*s) r := by
      apply Finset.sum_congr rfl
      intro j _
      rw [pow_add,hn,one_mul]
    rw [hh]
    exact CharTwo.add_self_eq_zero _
  · simpa only [signed_pair_power_right,SemidirectProduct.one_right] using hn

variable {B : Type*} {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

noncomputable def signedLift : W →* SignedGroup W :=
  cs.lift ⟨fun i => signedGenerator (cs.simple i), fun i j =>
    signed_pair_power_eq_one _ _ (cs.simple_mul_simple_self i)
      (cs.simple_mul_simple_self j) (M i j) (cs.simple_mul_simple_pow i j)⟩

@[simp] lemma signedLift_simple (i : B) :
    signedLift cs (cs.simple i) = signedGenerator (cs.simple i) := by
  exact cs.lift_apply_simple _ i

@[simp] lemma signedLift_right (w : W) : (signedLift cs w).right = w := by
  have h : SemidirectProduct.rightHom.comp (signedLift cs) = MonoidHom.id W := by
    apply cs.ext_simple
    intro i
    simp
  exact DFunLike.congr_fun h w

lemma coeff_wordProd (w : List B) (t : W) :
    coeff (signedLift cs (cs.wordProd w)) t =
      ((cs.leftInvSeq w).map (fun r => delta r t)).sum := by
  induction w generalizing t with
  | nil => simp
  | cons i w ih =>
    rw [cs.wordProd_cons,map_mul,coeff_mul,signedLift_simple,
      coeff_signedGenerator,signedGenerator_right,ih]
    simp only [CoxeterSystem.leftInvSeq,List.map_cons,List.map_map,List.sum_cons]
    congr 1
    apply congrArg List.sum
    apply List.map_congr_left
    intro r _
    exact delta_conj (cs.simple i) r t

omit [Group W] in
lemma sum_delta_nodup (l : List W) (h : l.Nodup) (t : W) :
    (l.map (fun r => delta r t)).sum = if t ∈ l then 1 else 0 := by
  classical
  induction l with
  | nil => simp
  | cons r l ih =>
    obtain ⟨hr,hl⟩ := List.nodup_cons.mp h
    rw [List.map_cons,List.sum_cons,ih hl]
    by_cases ht : t=r
    · subst t
      simp [delta,hr]
    · simp [delta,ht]

lemma coeff_reduced (w : List B) (hw : cs.IsReduced w) (t : W) :
    coeff (signedLift cs (cs.wordProd w)) t = if t ∈ cs.leftInvSeq w then 1 else 0 := by
  rw [coeff_wordProd, sum_delta_nodup _ (hw.nodup_leftInvSeq)]

lemma reduced_invSeq_membership {u v : List B}
    (hu : cs.IsReduced u) (hv : cs.IsReduced v) (h : cs.wordProd u = cs.wordProd v)
    (t : W) : t ∈ cs.leftInvSeq u ↔ t ∈ cs.leftInvSeq v := by
  have hh := congrArg (fun g => coeff (signedLift cs g) t) h
  rw [coeff_reduced cs u hu,coeff_reduced cs v hv] at hh
  by_cases h₁ : t ∈ cs.leftInvSeq u <;> by_cases h₂ : t ∈ cs.leftInvSeq v <;>
    simp_all

lemma simple_mem_leftInvSeq_of_shorter {w : List B} (hw : cs.IsReduced w) (i : B)
    (hi : cs.length (cs.simple i * cs.wordProd w) < cs.length (cs.wordProd w)) :
    cs.simple i ∈ cs.leftInvSeq w := by
  obtain ⟨u,hu,he⟩ := cs.exists_isReduced (cs.simple i * cs.wordProd w)
  have hw' : cs.wordProd (i :: u) = cs.wordProd w := by
    rw [cs.wordProd_cons, ← he,cs.simple_mul_simple_cancel_left]
  have hr : cs.IsReduced (i :: u) := by
    change cs.length (cs.wordProd (i :: u)) = (i :: u).length
    rw [hw',List.length_cons, ← hu.eq, ← he]
    rcases cs.length_simple_mul (cs.wordProd w) i with h | h
    · omega
    · omega
  exact (reduced_invSeq_membership cs hr hw hw' (cs.simple i)).mp (by
    simp [CoxeterSystem.leftInvSeq])

lemma simple_exchange {w : List B} (hw : cs.IsReduced w) (i : B)
    (hi : cs.length (cs.simple i * cs.wordProd w) < cs.length (cs.wordProd w)) :
    ∃ j, j < w.length ∧ cs.simple i * cs.wordProd w = cs.wordProd (w.eraseIdx j) := by
  obtain ⟨j,hj,hv⟩ := List.mem_iff_getElem.mp (simple_mem_leftInvSeq_of_shorter cs hw i hi)
  refine ⟨j,by simpa using hj,?_⟩
  rw [← hv, ← List.getD_eq_getElem _ 1 hj]
  exact cs.getD_leftInvSeq_mul_wordProd w j

end HarmonicArtin.CoxeterExchange

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Coxeter_Parabolic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.CoxeterExchange
variable {B W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

lemma exists_reduced_subword (u : List B) :
    ∃ v, v.Sublist u ∧ cs.IsReduced v ∧ cs.wordProd v = cs.wordProd u := by
  induction u with
  | nil => exact ⟨[], .refl _, by simp [CoxeterSystem.IsReduced], rfl⟩
  | cons i u ih =>
    obtain ⟨v,hv,hr,he⟩ := ih
    rcases cs.length_simple_mul (cs.wordProd v) i with ha | hd
    · refine ⟨i::v, List.cons_sublist_cons.mpr hv, ?_, ?_⟩
      · simpa only [CoxeterSystem.IsReduced, cs.wordProd_cons, List.length_cons, hr.eq] using ha
      · simp only [cs.wordProd_cons, he]
    · obtain ⟨j,hj,hjprod⟩ := simple_exchange cs hr i (by omega)
      refine ⟨v.eraseIdx j, List.Sublist.cons i ((v.eraseIdx_sublist j).trans hv), ?_, ?_⟩
      · change cs.length (cs.wordProd (v.eraseIdx j)) = (v.eraseIdx j).length
        rw [← hjprod, List.length_eraseIdx, ite_eq_left hj]
        have := hr.eq
        omega
      · rw [← hjprod, he, cs.wordProd_cons]

def parabolic (J : Set B) : Subgroup W := Subgroup.closure (cs.simple '' J)

lemma simple_mem_parabolic (J : Set B) {i : B} (hi : i ∈ J) :
    cs.simple i ∈ parabolic cs J := Subgroup.subset_closure ⟨i,hi,rfl⟩

lemma wordProd_mem_parabolic (J : Set B) (u : List B) (hu : ∀ i ∈ u, i ∈ J) :
    cs.wordProd u ∈ parabolic cs J := by
  induction u with
  | nil => simpa only [cs.wordProd_nil] using (parabolic cs J).one_mem
  | cons i u ih =>
    rw [cs.wordProd_cons]
    exact (parabolic cs J).mul_mem (simple_mem_parabolic cs J (hu i (by simp)))
      (ih (fun j hj => hu j (List.mem_cons_of_mem i hj)))

lemma mem_parabolic_iff_word (J : Set B) (w : W) :
    w ∈ parabolic cs J ↔ ∃ u : List B, (∀ i ∈ u, i ∈ J) ∧ cs.wordProd u = w := by
  constructor
  · intro hw
    induction hw using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨i,hi,rfl⟩ := hx
      exact ⟨[i], by simpa, by simp⟩
    | one => exact ⟨[], by simp, by simp⟩
    | mul x y hx hy ihx ihy =>
      obtain ⟨u,hu,rfl⟩ := ihx
      obtain ⟨v,hv,rfl⟩ := ihy
      exact ⟨u++v, fun i hi => (List.mem_append.mp hi).elim (hu i) (hv i), cs.wordProd_append u v⟩
    | inv x hx ih =>
      obtain ⟨u,hu,rfl⟩ := ih
      exact ⟨u.reverse, by simpa only [List.mem_reverse] using hu, cs.wordProd_reverse u⟩
  · rintro ⟨u,hu,rfl⟩
    exact wordProd_mem_parabolic cs J u hu

lemma mem_parabolic_iff_reduced_word (J : Set B) (w : W) :
    w ∈ parabolic cs J ↔
      ∃ u : List B, (∀ i ∈ u, i ∈ J) ∧ cs.IsReduced u ∧ cs.wordProd u = w := by
  constructor
  · intro hw
    obtain ⟨u,hu,rfl⟩ := (mem_parabolic_iff_word cs J w).mp hw
    obtain ⟨v,hv,hr,he⟩ := exists_reduced_subword cs u
    exact ⟨v, fun i hi => hu i (hv.subset hi), hr, he⟩
  · rintro ⟨u,hu,hr,rfl⟩
    exact wordProd_mem_parabolic cs J u hu

def IsParabolicMinimum (J : Set B) (w : W) : Prop :=
  ∀ a ∈ parabolic cs J, cs.length w ≤ cs.length (a*w)

lemma length_word_mul_of_minimum (J : Set B) (w : W) (hw : IsParabolicMinimum cs J w)
    (u : List B) (hu : cs.IsReduced u) (hJ : ∀ i ∈ u, i ∈ J) :
    cs.length (cs.wordProd u * w) = u.length + cs.length w := by
  induction u with
  | nil => simp
  | cons i u ih =>
    have hured : cs.IsReduced u := by simpa using hu.drop 1
    have huJ : ∀ j ∈ u, j ∈ J := fun j hj => hJ j (List.mem_cons_of_mem i hj)
    have hi := ih hured huJ
    obtain ⟨v,hv,hvprod⟩ := cs.exists_isReduced w
    have huv : cs.IsReduced (u++v) := by
      change cs.length (cs.wordProd (u++v)) = (u++v).length
      rw [cs.wordProd_append, ← hvprod, hi, List.length_append, ← hv.eq, ← hvprod]
    rcases cs.length_simple_mul (cs.wordProd u * w) i with ha | hd
    · simpa only [cs.wordProd_cons, mul_assoc, List.length_cons, hi, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using ha
    · exfalso
      have hd' : cs.length (cs.simple i * cs.wordProd (u++v)) < cs.length (cs.wordProd (u++v)) := by
        rw [cs.wordProd_append, ← hvprod]
        omega
      obtain ⟨j,hj,he⟩ := simple_exchange cs huv i hd'
      by_cases hju : j < u.length
      · rw [List.eraseIdx_append_of_lt_length hju, cs.wordProd_append,
          cs.wordProd_append, ← mul_assoc] at he
        have he' := mul_right_cancel he
        have hb := cs.length_wordProd_le (u.eraseIdx j)
        rw [List.length_eraseIdx, ite_eq_left hju, ← he', ← cs.wordProd_cons, hu.eq] at hb
        simp only [List.length_cons] at hb
        omega
      · have hjv : j-u.length < v.length := by simp only [List.length_append] at hj; omega
        rw [List.eraseIdx_append_of_length_le (by omega), cs.wordProd_append,
          cs.wordProd_append, ← hvprod] at he
        let a := (cs.wordProd u)⁻¹ * cs.simple i * cs.wordProd u
        have haJ : a ∈ parabolic cs J :=
          (parabolic cs J).mul_mem ((parabolic cs J).mul_mem
            ((parabolic cs J).inv_mem (wordProd_mem_parabolic cs J u huJ))
            (simple_mem_parabolic cs J (hJ i (by simp))))
            (wordProd_mem_parabolic cs J u huJ)
        have he' : a*w = cs.wordProd (v.eraseIdx (j-u.length)) := by
          dsimp [a]
          calc
            _ = (cs.wordProd u)⁻¹ * (cs.simple i * (cs.wordProd u*w)) := by group
            _ = _ := by rw [he]; group
        have hmin := hw a haJ
        rw [he'] at hmin
        have hb := cs.length_wordProd_le (v.eraseIdx (j-u.length))
        rw [List.length_eraseIdx, ite_eq_left hjv, ← hv.eq, ← hvprod] at hb
        have hvpos : 0 < cs.length w := by rw [hvprod, hv.eq]; omega
        omega

lemma length_mul_of_minimum (J : Set B) (w : W) (hw : IsParabolicMinimum cs J w)
    (a : W) (ha : a ∈ parabolic cs J) :
    cs.length (a*w) = cs.length a + cs.length w := by
  obtain ⟨u,hu,hr,rfl⟩ := (mem_parabolic_iff_reduced_word cs J a).mp ha
  rw [length_word_mul_of_minimum cs J w hw u hr hu, hr.eq]

lemma exists_parabolic_decomposition (J : Set B) (w : W) :
    ∃ a v : W, a ∈ parabolic cs J ∧ IsParabolicMinimum cs J v ∧
      w = a*v ∧ cs.length w = cs.length a + cs.length v := by
  classical
  have hex : ∃ n : ℕ, ∃ b : W, b ∈ parabolic cs J ∧ cs.length (b*w) = n :=
    ⟨cs.length w, 1, (parabolic cs J).one_mem, by simp⟩
  obtain ⟨b,hb,hlen⟩ := Nat.find_spec hex
  have hmin : IsParabolicMinimum cs J (b*w) := by
    intro c hc
    rw [hlen]
    apply Nat.find_min' hex
    exact ⟨c*b, (parabolic cs J).mul_mem hc hb, by rw [mul_assoc]⟩
  refine ⟨b⁻¹, b*w, (parabolic cs J).inv_mem hb, hmin, by group, ?_⟩
  simpa only [inv_mul_cancel_left] using
    length_mul_of_minimum cs J (b*w) hmin b⁻¹ ((parabolic cs J).inv_mem hb)

lemma descent_parabolic_factor (J : Set B) {a v : W}
    (ha : a ∈ parabolic cs J) (hv : IsParabolicMinimum cs J v)
    {i : B} (hi : i ∈ J) :
    cs.length (cs.simple i * (a*v)) < cs.length (a*v) ↔
      cs.length (cs.simple i*a) < cs.length a := by
  rw [← mul_assoc, length_mul_of_minimum cs J v hv a ha,
    length_mul_of_minimum cs J v hv (cs.simple i*a)
      ((parabolic cs J).mul_mem (simple_mem_parabolic cs J hi) ha)]
  omega

end HarmonicArtin.CoxeterExchange

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Geometry_Reflect
attribute [-instance] _root_.OAI.HarmonicArtin.instPreorderLiftedCell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.Geometric

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

noncomputable def reflect (e : E) (f : E →ₗ[ℝ] ℝ) : Module.End ℝ E :=
  LinearMap.id - f.smulRight e

@[simp] lemma reflect_apply (e : E) (f : E →ₗ[ℝ] ℝ) (x : E) :
    reflect e f x = x - f x • e := rfl

lemma reflect_involutive (e : E) (f : E →ₗ[ℝ] ℝ) (hf : f e = 2) :
    Function.Involutive (reflect e f) := by
  intro x
  simp only [reflect_apply, map_sub, map_smul, hf]
  module

noncomputable def reflection (e : E) (f : E →ₗ[ℝ] ℝ) (hf : f e = 2) :
    E ≃ₗ[ℝ] E where
  toLinearMap := reflect e f
  invFun := reflect e f
  left_inv := reflect_involutive e f hf
  right_inv := reflect_involutive e f hf

lemma pair_left (e d : E) (f g : E →ₗ[ℝ] ℝ) (a : ℝ)
    (hf : f e = 2) (hfd : f d = -a) (x : E) :
    f ((reflect e f * reflect d g) x) = - f x - a * g x := by
  simp only [Module.End.mul_apply, reflect_apply, map_sub, map_smul, hf, hfd]
  ring

lemma pair_right (e d : E) (f g : E →ₗ[ℝ] ℝ) (a : ℝ)
    (hg : g d = 2) (hfd : f d = -a) (hge : g e = -a) (x : E) :
    g ((reflect e f * reflect d g) x) = a * f x + (a^2-1) * g x := by
  simp only [Module.End.mul_apply, reflect_apply, map_sub, map_smul, hg, hfd, hge]
  ring

lemma pair_difference (e d : E) (f g : E →ₗ[ℝ] ℝ) (x : E) :
    ∃ p q : ℝ, (reflect e f * reflect d g) x = x + p • e + q • d := by
  refine ⟨-f (x-g x • d), -g x, ?_⟩
  simp only [Module.End.mul_apply, reflect_apply]
  module

lemma pair_power_difference (e d : E) (f g : E →ₗ[ℝ] ℝ) (x : E) (n : ℕ) :
    ∃ p q : ℝ, ((reflect e f * reflect d g)^n) x = x + p • e + q • d := by
  induction n with
  | zero => exact ⟨0, 0, by simp⟩
  | succ n ih =>
    obtain ⟨p,q,h⟩ := ih
    obtain ⟨u,v,hu⟩ := pair_difference e d f g (((reflect e f * reflect d g)^n) x)
    refine ⟨p+u, q+v, ?_⟩
    rw [pow_succ', Module.End.mul_apply, hu,h]
    module

noncomputable def phase (c s : ℝ) : ℂ := (c : ℂ) + (s : ℂ) * Complex.I

lemma phase_quad (c s : ℝ) (h : c^2+s^2=1) :
    phase c s ^ 2 = 2*(c : ℂ)*phase c s-1 := by
  apply Complex.ext <;> simp [phase,Complex.mul_re,Complex.mul_im,pow_two] <;> nlinarith

lemma phase_im (c s : ℝ) : (phase c s).im = s := by simp [phase]

lemma pair_phase (e d : E) (f g : E →ₗ[ℝ] ℝ) (c s : ℝ)
    (hf : f e=2) (hg : g d=2) (hfd : f d = -(2*c)) (hge : g e = -(2*c))
    (hcs : c^2+s^2=1) (x : E) :
    (f ((reflect e f * reflect d g) x) : ℂ) + phase c s * g ((reflect e f * reflect d g) x) =
      (phase c s)^2 * ((f x : ℂ) + phase c s * g x) := by
  rw [pair_left e d f g (2*c) hf hfd, pair_right e d f g (2*c) hg hfd hge]
  push_cast
  have hh := phase_quad c s hcs
  calc
    _ = (2*(c:ℂ)*phase c s-1) * ((f x:ℂ)+phase c s*g x) := by
      linear_combination -(g x : ℂ) * (2*(c:ℂ)) * hh
    _ = _ := by rw [hh]

lemma pair_phase_power (e d : E) (f g : E →ₗ[ℝ] ℝ) (c s : ℝ)
    (hf : f e=2) (hg : g d=2) (hfd : f d = -(2*c)) (hge : g e = -(2*c))
    (hcs : c^2+s^2=1) (x : E) (n : ℕ) :
    (f (((reflect e f * reflect d g)^n) x) : ℂ) + phase c s * g (((reflect e f * reflect d g)^n) x) =
      (phase c s)^(2*n) * ((f x : ℂ) + phase c s * g x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, pair_phase e d f g c s hf hg hfd hge hcs, ih]
    rw [← mul_assoc, ← pow_add]
    congr 2
    omega

lemma phase_coordinates_injective (c s : ℝ) (hs : s ≠ 0) {a b a' b' : ℝ}
    (h : (a:ℂ)+phase c s*b = (a':ℂ)+phase c s*b') : a=a' ∧ b=b' := by
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  simp only [Complex.add_im,Complex.ofReal_im,zero_add,Complex.mul_im,
    Complex.ofReal_re,mul_zero,phase_im] at him
  have hb : b=b' := mul_left_cancel₀ hs him
  subst b'
  have ha : (a:ℂ)=(a':ℂ) := add_right_cancel h
  exact ⟨Complex.ofReal_injective ha,rfl⟩

lemma pair_power_eq_id (e d : E) (f g : E →ₗ[ℝ] ℝ) (c s : ℝ)
    (hf : f e=2) (hg : g d=2) (hfd : f d = -(2*c)) (hge : g e = -(2*c))
    (hcs : c^2+s^2=1) (hs : s ≠ 0) (n : ℕ) (hn : phase c s ^ (2*n) = 1) :
    (reflect e f * reflect d g)^n = 1 := by
  ext x
  obtain ⟨p,q,hpq⟩ := pair_power_difference e d f g x n
  have hh := pair_phase_power e d f g c s hf hg hfd hge hcs x n
  rw [hn,one_mul] at hh
  obtain ⟨hff,hgg⟩ := phase_coordinates_injective c s hs hh
  rw [hpq] at hff hgg
  simp only [map_add,map_smul,hf,hg,hfd,hge,smul_eq_mul] at hff hgg
  have hc : c^2 < 1 := by nlinarith [sq_pos_of_ne_zero hs]
  have hqp : q = c*p := by linarith
  have hmul : (1-c^2)*p=0 := by rw [hqp] at hff; nlinarith [hff]
  have hp : p=0 := (mul_eq_zero.mp hmul).resolve_left (ne_of_gt (sub_pos.mpr hc))
  have hq : q=0 := by rw [hqp,hp,mul_zero]
  simpa [hp,hq] using hpq

end HarmonicArtin.Geometric

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Geometry_TrigPhasePower
attribute [-instance] _root_.OAI.HarmonicArtin.instPreorderLiftedCell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.Geometric

lemma trig_phase_power (m : ℕ) (hm : 2 ≤ m) :
    phase (Real.cos (Real.pi / m)) (Real.sin (Real.pi / m)) ^ (2*m) = 1 := by
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  rw [phase, Complex.ofReal_cos, Complex.ofReal_sin,
    Complex.cos_add_sin_mul_I_pow]
  have ha : (↑(2*m) : ℂ) * (↑(Real.pi / m) : ℂ) = ↑(2*Real.pi) := by
    push_cast
    field_simp [hm0]
  rw [ha,← Complex.ofReal_cos,← Complex.ofReal_sin,Real.cos_two_pi,Real.sin_two_pi]
  simp

lemma trig_phase_nonzero (m : ℕ) (hm : 2 ≤ m) :
    Real.sin (Real.pi / m) ≠ 0 := by
  have hm1 : (1:ℝ) < m := by exact_mod_cast (by omega : 1 < m)
  apply ne_of_gt
  apply Real.sin_pos_of_pos_of_lt_pi
  · positivity
  · exact div_lt_self Real.pi_pos hm1

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

lemma reflection_pair_order (e d : E) (f g : E →ₗ[ℝ] ℝ)
    (hf : f e=2) (hg : g d=2) (m : ℕ) (hm : 2 ≤ m)
    (hfd : f d = -(2*Real.cos (Real.pi/m)))
    (hge : g e = -(2*Real.cos (Real.pi/m))) :
    (reflection e f hf * reflection d g hg)^m = 1 := by
  apply LinearEquiv.toLinearMap_injective
  have h := pair_power_eq_id e d f g (Real.cos (Real.pi/m)) (Real.sin (Real.pi/m))
    hf hg hfd hge (by nlinarith [Real.sin_sq_add_cos_sq (Real.pi/m)])
    (trig_phase_nonzero m hm) m (trig_phase_power m hm)
  change (LinearEquiv.automorphismGroup.toLinearMapMonoidHom
    ((reflection e f hf * reflection d g hg)^m)) = 1
  rw [map_pow, map_mul]
  exact h

end HarmonicArtin.Geometric

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Geometry_Cartan
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.Geometric

open scoped Classical

variable {S W : Type*} [DecidableEq S] [Group W]

noncomputable def cartan (M : CoxeterMatrix S) : Matrix S S ℝ := fun i j =>
  if i=j then 2 else if M i j=0 then -2 else -2*Real.cos (Real.pi/(M i j:ℝ))

@[simp] lemma cartan_diag (M : CoxeterMatrix S) (i : S) : cartan M i i=2 := by
  simp [cartan]

variable [Fintype S]

noncomputable def rootRow (M : CoxeterMatrix S) (i : S) : (S → ℝ) →ₗ[ℝ] ℝ :=
  (LinearMap.proj i).comp (Matrix.mulVecLin (cartan M))

@[simp] lemma rootRow_apply (M : CoxeterMatrix S) (i : S) (x : S → ℝ) :
    rootRow M i x = (Matrix.mulVec (cartan M) x) i := rfl

@[simp] lemma rootRow_single (M : CoxeterMatrix S) (i j : S) :
    rootRow M i (Pi.single j 1) = cartan M i j := by
  simp [Matrix.mulVec_single]

noncomputable def simpleReflection (M : CoxeterMatrix S) (i : S) :
    (S → ℝ) ≃ₗ[ℝ] (S → ℝ) :=
  reflection (Pi.single i 1) (rootRow M i) (by simp)

@[simp] lemma simpleReflection_apply (M : CoxeterMatrix S) (i : S) (x : S → ℝ) :
    simpleReflection M i x = x - (Matrix.mulVec (cartan M) x) i • Pi.single i 1 := rfl

lemma simpleReflection_squared (M : CoxeterMatrix S) (i : S) :
    simpleReflection M i * simpleReflection M i = 1 := by
  apply LinearEquiv.ext
  intro x
  exact reflect_involutive (Pi.single i 1) (rootRow M i) (by simp) x

lemma simpleReflection_isLiftable (M : CoxeterMatrix S) :
    CoxeterMatrix.IsLiftable M (simpleReflection M) := by
  intro i j
  by_cases hij : i=j
  · subst j
    rw [M.diagonal, pow_one, simpleReflection_squared]
  by_cases hm0 : M i j=0
  · rw [hm0,pow_zero]
  have hm : 2 ≤ M i j := by have := M.off_diagonal i j hij; omega
  exact reflection_pair_order (Pi.single i 1) (Pi.single j 1) (rootRow M i) (rootRow M j)
    (by simp) (by simp) (M i j) hm
    (by simp [cartan,hij,hm0])
    (by simp [cartan,Ne.symm hij,← M.symmetric i j,hm0])

noncomputable def representation {M : CoxeterMatrix S} (cs : CoxeterSystem M W) :
    W →* ((S → ℝ) ≃ₗ[ℝ] (S → ℝ)) :=
  cs.lift ⟨simpleReflection M, simpleReflection_isLiftable M⟩

@[simp] lemma representation_simple {M : CoxeterMatrix S} (cs : CoxeterSystem M W) (i : S) :
    representation cs (cs.simple i)=simpleReflection M i := cs.lift_apply_simple _ i

end HarmonicArtin.Geometric

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Geometry_TrigPhaseSqPrimitive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.Geometric

lemma trig_phase_sq_primitive (m : ℕ) (hm : m ≠ 0) :
    IsPrimitiveRoot (phase (Real.cos (Real.pi/m)) (Real.sin (Real.pi/m)) ^ 2) m := by
  have he : phase (Real.cos (Real.pi/m)) (Real.sin (Real.pi/m)) =
      Complex.exp ((Real.pi/(m:ℝ):ℝ)*Complex.I) := by
    rw [Complex.exp_mul_I]
    simp only [phase, Complex.ofReal_cos, Complex.ofReal_sin]
  rw [he, ← Complex.exp_nat_mul]
  convert Complex.isPrimitiveRoot_exp m hm using 2
  all_goals try with_reducible_and_instances rfl
  push_cast
  ring

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

lemma infinite_pair_power (e d : E) (f g : E →ₗ[ℝ] ℝ)
    (hf : f e=2) (hg : g d=2) (hfd : f d = -2) (hge : g e = -2) (n : ℕ) :
    ((reflect e f * reflect d g)^n) e = (2*(n:ℝ)+1) • e + (2*(n:ℝ)) • d := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih]
    simp only [Module.End.mul_apply, reflect_apply, map_add, map_sub, map_smul,
      hf,hg,hfd,hge, Nat.cast_add, Nat.cast_one]
    module

variable {S W : Type*} [Fintype S] [DecidableEq S] [Group W]
variable {M : CoxeterMatrix S} (cs : CoxeterSystem M W)

lemma simple_pair_pow_eq_one_iff (i j : S) (hij : i ≠ j) (n : ℕ) :
    (cs.simple i*cs.simple j)^n=1 ↔ M i j ∣ n := by
  constructor
  · intro h
    have hrep := congrArg (representation cs) h
    simp only [map_pow, map_mul, representation_simple, map_one] at hrep
    have hlin := congrArg LinearEquiv.automorphismGroup.toLinearMapMonoidHom hrep
    simp only [map_pow, map_mul, map_one] at hlin
    change (reflect (Pi.single i 1) (rootRow M i) *
      reflect (Pi.single j 1) (rootRow M j))^n = 1 at hlin
    by_cases hm : M i j = 0
    · have hh := infinite_pair_power (Pi.single i 1) (Pi.single j 1)
        (rootRow M i) (rootRow M j) (by simp) (by simp)
        (by simp [cartan,hij,hm])
        (by simp [cartan,Ne.symm hij,← M.symmetric i j,hm]) n
      rw [hlin] at hh
      have hc := congrFun hh i
      simp only [Module.End.one_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Pi.single_eq_same, Pi.single_eq_of_ne hij, mul_one, mul_zero, add_zero] at hc
      have hn : n=0 := by exact_mod_cast (by linarith : (n:ℝ)=0)
      simp [hn]
    · have hm2 : 2 ≤ M i j := by have := M.off_diagonal i j hij; omega
      let c := Real.cos (Real.pi / (M i j:ℝ))
      let s := Real.sin (Real.pi / (M i j:ℝ))
      have hfd : rootRow M i (Pi.single j 1) = -(2*c) := by
        simp [cartan,hij,hm,c]
      have hge : rootRow M j (Pi.single i 1) = -(2*c) := by
        simp [cartan,Ne.symm hij,← M.symmetric i j,hm,c]
      have hcs : c^2+s^2=1 := by dsimp [c,s] <;> nlinarith [Real.sin_sq_add_cos_sq (Real.pi/(M i j:ℝ))]
      have hh := pair_phase_power (Pi.single i 1) (Pi.single j 1)
        (rootRow M i) (rootRow M j) c s (by simp) (by simp) hfd hge hcs (Pi.single i 1) n
      rw [hlin, Module.End.one_apply] at hh
      have hnonzero : ((rootRow M i (Pi.single i 1):ℝ):ℂ) +
          phase c s * rootRow M j (Pi.single i 1) ≠ 0 := by
        intro hz
        have hz' := phase_coordinates_injective c s (trig_phase_nonzero (M i j) hm2)
          (a:=rootRow M i (Pi.single i 1)) (b:=rootRow M j (Pi.single i 1))
          (a':=0) (b':=0) (by simpa using hz)
        norm_num at hz'
      have hp : phase c s ^ (2*n)=1 := by
        apply mul_right_cancel₀ hnonzero
        simpa only [one_mul] using hh.symm
      exact ((trig_phase_sq_primitive (M i j) hm).pow_eq_one_iff_dvd n).mp
        (by simpa only [pow_mul] using hp)
  · rintro ⟨k,rfl⟩
    rw [pow_mul, cs.simple_mul_simple_pow, one_pow]

end HarmonicArtin.Geometric

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Coxeter_AltListPairDescent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.CoxeterExchange
variable {B W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

lemma altList_of_pair_descent (i j : B) (a : W)
    (ha : a ∈ parabolic cs ({i,j} : Set B))
    (hi : cs.length (cs.simple i*a) < cs.length a) :
    cs.IsReduced (altList i j (cs.length a)) ∧
      cs.wordProd (altList i j (cs.length a)) = a := by
  have hia : cs.simple i*a ∈ parabolic cs ({i,j} : Set B) :=
    (parabolic cs _).mul_mem (simple_mem_parabolic cs _ (by simp)) ha
  obtain ⟨u,hu,hr,he⟩ := (mem_parabolic_iff_reduced_word cs _ _).mp hia
  have hd := cs.length_simple_mul a i
  have hlen : u.length+1=cs.length a := by rw [← hr.eq,he]; omega
  have hprod : cs.wordProd (i::u)=a := by
    rw [cs.wordProd_cons,he,cs.simple_mul_simple_cancel_left]
  have hred : cs.IsReduced (i::u) := by
    change cs.length (cs.wordProd (i::u)) = (i::u).length
    rw [hprod,List.length_cons,hlen]
  have hshape := reduced_pair_cons_eq_alt cs i j u hred hu
  rw [hlen] at hshape
  rw [← hshape]
  exact ⟨hred,hprod⟩

variable [Fintype B] [DecidableEq B]

lemma pair_double_descent (i j : B) (hij : i ≠ j) (a : W)
    (ha : a ∈ parabolic cs ({i,j} : Set B))
    (hi : cs.length (cs.simple i*a) < cs.length a)
    (hj : cs.length (cs.simple j*a) < cs.length a) :
    0 < M i j ∧ cs.length a=M i j ∧
      cs.wordProd (altList i j (M i j))=a ∧
      cs.wordProd (altList j i (M i j))=a := by
  obtain ⟨hired,hiprod⟩ := altList_of_pair_descent cs i j a ha hi
  obtain ⟨hjred,hjprod⟩ := altList_of_pair_descent cs j i a
    (by simpa only [Set.pair_comm] using ha) hj
  have hpow : (cs.simple i*cs.simple j)^(cs.length a)=1 := by
    rw [← wordProd_altList_difference, hiprod,hjprod,mul_inv_cancel]
  have hdvd := (Geometric.simple_pair_pow_eq_one_iff cs i j hij (cs.length a)).mp hpow
  have hn : 0 < cs.length a := by omega
  have hm : M i j ≠ 0 := by
    intro hzero
    rw [hzero, zero_dvd_iff] at hdvd
    omega
  have hm2 : 2 ≤ M i j := by have := M.off_diagonal i j hij; omega
  have hle := reduced_altList_le cs i j (cs.length a) hm2 hired
  have hmle := Nat.le_of_dvd hn hdvd
  have heq : cs.length a=M i j := by omega
  exact ⟨by omega, heq, by simpa only [heq] using hiprod,
    by simpa only [heq] using hjprod⟩

lemma double_descent_prefix (i j : B) (hij : i ≠ j) (w : W)
    (hi : cs.length (cs.simple i*w) < cs.length w)
    (hj : cs.length (cs.simple j*w) < cs.length w) :
    ∃ v : W, 0 < M i j ∧ cs.length w=M i j+cs.length v ∧
      w = cs.wordProd (altList i j (M i j))*v ∧
      w = cs.wordProd (altList j i (M i j))*v := by
  obtain ⟨a,v,ha,hv,he,hlen⟩ := exists_parabolic_decomposition cs ({i,j} : Set B) w
  have hai : cs.length (cs.simple i*a) < cs.length a := by
    apply (descent_parabolic_factor cs _ ha hv (by simp : i ∈ ({i,j}:Set B))).mp
    simpa only [← he] using hi
  have haj : cs.length (cs.simple j*a) < cs.length a := by
    apply (descent_parabolic_factor cs _ ha hv (by simp : j ∈ ({i,j}:Set B))).mp
    simpa only [← he] using hj
  obtain ⟨hm,hlenA,hip,hjp⟩ := pair_double_descent cs i j hij a ha hai haj
  exact ⟨v,hm, by simpa only [hlenA] using hlen, by simpa only [hip] using he,
    by simpa only [hjp] using he⟩

end HarmonicArtin.CoxeterExchange

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Coxeter_InverseParabolicMinimum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.CoxeterExchange
variable {B W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

lemma inverse_is_parabolic_minimum (J : Set B) (w : W)
    (hw : ∀ a ∈ parabolic cs J, cs.length w ≤ cs.length (w*a)) :
    IsParabolicMinimum cs J w⁻¹ := by
  intro a ha
  calc
    cs.length w⁻¹ = cs.length w := cs.length_inv w
    _ ≤ cs.length (w*a⁻¹) := hw a⁻¹ ((parabolic cs J).inv_mem ha)
    _ = cs.length (a*w⁻¹) := by
      rw [← cs.length_inv (w*a⁻¹),mul_inv_rev,inv_inv]

lemma length_mul_of_right_minimum (J : Set B) (w : W)
    (hw : ∀ a ∈ parabolic cs J, cs.length w ≤ cs.length (w*a))
    (a : W) (ha : a ∈ parabolic cs J) :
    cs.length (w*a) = cs.length w+cs.length a := by
  have hm := inverse_is_parabolic_minimum cs J w hw
  calc
    cs.length (w*a) = cs.length (a⁻¹*w⁻¹) := by rw [← mul_inv_rev,cs.length_inv]
    _ = cs.length a⁻¹+cs.length w⁻¹ :=
      length_mul_of_minimum cs J w⁻¹ hm a⁻¹ ((parabolic cs J).inv_mem ha)
    _ = _ := by rw [cs.length_inv,cs.length_inv,Nat.add_comm]

end HarmonicArtin.CoxeterExchange

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Coxeter_RightParabolicDecomposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.CoxeterExchange
variable {S W : Type*} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W)

lemma exists_right_parabolic_decomposition (J : Set S) (w : W) :
    ∃ v a : W, a ∈ parabolic cs J ∧
      (∀ b ∈ parabolic cs J, cs.length v ≤ cs.length (v*b)) ∧
      w = v*a ∧ cs.length w = cs.length v + cs.length a := by
  obtain ⟨a,v,ha,hv,he,hl⟩ := exists_parabolic_decomposition cs J w⁻¹
  refine ⟨v⁻¹,a⁻¹,(parabolic cs J).inv_mem ha,?_,?_,?_⟩
  · intro b hb
    have h := hv b⁻¹ ((parabolic cs J).inv_mem hb)
    rw [← cs.length_inv (v⁻¹*b),mul_inv_rev,inv_inv,cs.length_inv]
    simpa only [cs.length_inv] using h
  · simpa only [mul_inv_rev,inv_inv] using congrArg Inv.inv he
  · simpa only [cs.length_inv,Nat.add_comm] using hl

lemma exists_right_descent {w : W} (hw : w ≠ 1) :
    ∃ i : S, cs.length (w*cs.simple i)+1=cs.length w := by
  obtain ⟨u,hu,he⟩ := cs.exists_isReduced w⁻¹
  cases u with
  | nil => simp only [cs.wordProd_nil] at he; exact (hw (inv_eq_one.mp he)).elim
  | cons i u =>
    refine ⟨i, ?_⟩
    have hured : cs.IsReduced u := by simpa using hu.drop 1
    have he' : cs.simple i * w⁻¹ = cs.wordProd u := by
      rw [he,cs.wordProd_cons,cs.simple_mul_simple_cancel_left]
    have hlen := hu.eq
    rw [← he,List.length_cons] at hlen
    rw [← cs.length_inv (w*cs.simple i),mul_inv_rev,cs.inv_simple,he',hured.eq]
    simpa only [cs.length_inv] using hlen.symm

end HarmonicArtin.CoxeterExchange

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Coxeter_AltNext
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.CoxeterExchange
attribute [local instance] Classical.propDecidable
variable {S : Type*}

def altNext (i j : S) (n : ℕ) : S := if n % 2 = 0 then i else j

@[simp] lemma altNext_zero (i j : S) : altNext i j 0 = i := rfl

lemma altNext_succ (i j : S) (n : ℕ) : altNext i j (n+1) = altNext j i n := by
  unfold altNext
  split_ifs <;> first | rfl | omega

lemma altList_succ_append (i j : S) (n : ℕ) :
    altList i j (n+1) = altList i j n ++ [altNext i j n] := by
  induction n generalizing i j with
  | zero => rfl
  | succ n ih =>
    rw [altList_succ, ih j i, altList_succ, List.cons_append, altNext_succ]

end HarmonicArtin.CoxeterExchange

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Geometry_DihedralScalar
attribute [-instance] _root_.OAI.HarmonicArtin.instPreorderLiftedCell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.Geometric
open scoped BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def dihedralScalar (m n : ℕ) : ℝ :=
  if m = 0 then (n : ℝ) else Real.sin ((n : ℝ) * (Real.pi / m)) / Real.sin (Real.pi / m)

noncomputable def dihedralWeight (m : ℕ) : ℝ :=
  if m = 0 then 2 else 2 * Real.cos (Real.pi / m)

@[simp] lemma dihedralScalar_zero (m : ℕ) : dihedralScalar m 0 = 0 := by
  simp [dihedralScalar]

@[simp] lemma dihedralScalar_one (m : ℕ) (hm : m = 0 ∨ 2 ≤ m) : dihedralScalar m 1 = 1 := by
  rcases hm with rfl | hm
  · simp [dihedralScalar]
  · have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    have hang : 0 < Real.pi / (m : ℝ) := div_pos Real.pi_pos hmpos
    have hlt : Real.pi / (m : ℝ) < Real.pi := by
      apply (div_lt_iff₀ hmpos).mpr
      have hmone : (1 : ℝ) < m := by exact_mod_cast (by omega : 1 < m)
      nlinarith [Real.pi_pos]
    have hs := ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hang hlt)
    simp only [dihedralScalar, ite_eq_right (by omega : m ≠ 0), Nat.cast_one, one_mul, div_self hs]

lemma dihedralScalar_recurrence (m n : ℕ) :
    dihedralScalar m (n+2) = dihedralWeight m * dihedralScalar m (n+1) - dihedralScalar m n := by
  by_cases hm : m = 0
  · simp [dihedralScalar, dihedralWeight, hm]
    ring
  · have hsin : Real.sin (((n : ℝ)+2)*(Real.pi/m)) =
        2*Real.cos (Real.pi/m)*Real.sin (((n : ℝ)+1)*(Real.pi/m)) -
          Real.sin ((n : ℝ)*(Real.pi/m)) := by
      have h := Real.sin_add ( ((n : ℝ)+1)*(Real.pi/m)) (Real.pi/m)
      have h' := Real.sin_sub ( ((n : ℝ)+1)*(Real.pi/m)) (Real.pi/m)
      rw [show ((n : ℝ)+1)*(Real.pi/m)+(Real.pi/m)=((n : ℝ)+2)*(Real.pi/m) by ring] at h
      rw [show ((n : ℝ)+1)*(Real.pi/m)-(Real.pi/m)=(n : ℝ)*(Real.pi/m) by ring] at h'
      nlinarith
    simp only [dihedralScalar, dihedralWeight, ite_eq_right hm, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
    rw [hsin]
    ring

lemma dihedralScalar_nonneg (m n : ℕ) (hn : m = 0 ∨ n ≤ m) : 0 ≤ dihedralScalar m n := by
  by_cases hm : m = 0
  · simp [dihedralScalar, hm]
  · have hn : n ≤ m := hn.resolve_left hm
    have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    have hpos : 0 ≤ Real.pi / (m : ℝ) := (div_pos Real.pi_pos hmpos).le
    have hle : Real.pi / (m : ℝ) ≤ Real.pi := by
      apply (div_le_iff₀ hmpos).mpr
      have hmone : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
      nlinarith [Real.pi_pos]
    have hxpos : 0 ≤ (n : ℝ)*(Real.pi/m) := mul_nonneg (Nat.cast_nonneg _) hpos
    have hxle : (n : ℝ)*(Real.pi/m) ≤ Real.pi := by
      have hn' : (n : ℝ) ≤ m := by exact_mod_cast hn
      calc
        _ ≤ (m : ℝ)*(Real.pi/m) := mul_le_mul_of_nonneg_right hn' hpos
        _ = Real.pi := mul_div_cancel₀ _ (ne_of_gt hmpos)
    simpa only [dihedralScalar, ite_eq_right hm] using
      div_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hxpos hxle)
        (Real.sin_nonneg_of_nonneg_of_le_pi hpos hle)

variable {S W : Type*} [Fintype S] [DecidableEq S] [Group W]
  {M : CoxeterMatrix S} (cs : CoxeterSystem M W)

omit [Fintype S] in
lemma cartan_off_weight (i j : S) (hij : i ≠ j) :
    cartan M i j = -dihedralWeight (M i j) := by
  simp only [cartan, ite_eq_right hij, dihedralWeight]
  split_ifs <;> ring

lemma simpleReflection_basis_self (i : S) :
    simpleReflection M i (Pi.single i 1) = -(Pi.single i 1) := by
  rw [simpleReflection_apply, ← rootRow_apply, rootRow_single, cartan_diag]
  module

lemma simpleReflection_basis_other (i j : S) (hij : i ≠ j) :
    simpleReflection M i (Pi.single j 1) =
      Pi.single j 1 + dihedralWeight (M i j) • Pi.single i 1 := by
  rw [simpleReflection_apply, ← rootRow_apply, rootRow_single, cartan_off_weight i j hij]
  module

end HarmonicArtin.Geometric

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Coxeter_AlternatingNextRoot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.Geometric
open HarmonicArtin.CoxeterExchange

variable {S W : Type*} [Fintype S] [DecidableEq S] [Group W]
  {M : CoxeterMatrix S} (cs : CoxeterSystem M W)

lemma alternating_next_root (i j : S) (hij : i ≠ j) (n : ℕ) :
    representation cs (cs.wordProd (altList i j n)) (Pi.single (altNext i j n) 1) =
      dihedralScalar (M i j) (n+1) • Pi.single i 1 +
        dihedralScalar (M i j) n • Pi.single j 1 := by
  induction n generalizing i j with
  | zero =>
    simp only [altList_zero, cs.wordProd_nil, map_one, altNext_zero,
      dihedralScalar_zero, zero_smul, add_zero]
    rw [dihedralScalar_one _ (by have := M.off_diagonal i j hij; omega), one_smul]
    rfl
  | succ n ih =>
    rw [altList_succ, cs.wordProd_cons, map_mul, LinearEquiv.mul_apply,
      altNext_succ, ih j i (Ne.symm hij)]
    simp only [representation_simple, map_add, map_smul,
      simpleReflection_basis_other i j hij, simpleReflection_basis_self,
      ← M.symmetric i j]
    rw [show n+1+1=n+2 by omega, dihedralScalar_recurrence]
    module

end HarmonicArtin.Geometric

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Geometry_RootCoeffAltExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.Geometric
open HarmonicArtin.CoxeterExchange

attribute [local instance] Classical.propDecidable Classical.decEq
variable {S W : Type*} [Fintype S] [DecidableEq S] [Group W]
  {M : CoxeterMatrix S} (cs : CoxeterSystem M W)

lemma root_coeff_of_alt_extension (i j : S) (hij : i ≠ j) (u : List S) (s : S)
    (he : u++[s] = altList i j (u.length+1)) (hr : cs.IsReduced (u++[s])) :
    ∃ x y : ℝ, 0 ≤ x ∧ 0 ≤ y ∧
      representation cs (cs.wordProd u) (Pi.single s 1) =
        x • Pi.single i 1 + y • Pi.single j 1 := by
  have hre : cs.IsReduced (altList i j (u.length+1)) := he ▸ hr
  rw [altList_succ_append] at he
  obtain ⟨hu,hs⟩ := List.append_inj he (by simp)
  have hs' : s = altNext i j u.length := by simpa using hs
  have hb : M i j = 0 ∨ u.length+1 ≤ M i j := by
    by_cases hm : M i j=0
    · exact Or.inl hm
    · have hm2 : 2 ≤ M i j := by have := M.off_diagonal i j hij; omega
      exact Or.inr (reduced_altList_le cs i j _ hm2 hre)
  refine ⟨dihedralScalar (M i j) (u.length+1),dihedralScalar (M i j) u.length,
    dihedralScalar_nonneg _ _ hb,dihedralScalar_nonneg _ _ (by omega),?_⟩
  rw [hu,hs']
  simpa only [length_altList] using alternating_next_root cs i j hij u.length

lemma pair_ascent_root_coeff (i j : S) (hij : i ≠ j) (a : W)
    (ha : a ∈ parabolic cs ({i,j} : Set S))
    (has : cs.length (a*cs.simple i)=cs.length a+1) :
    ∃ x y : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ representation cs a (Pi.single i 1) =
      x • Pi.single i 1 + y • Pi.single j 1 := by
  obtain ⟨u,hu,hr,rfl⟩ := (mem_parabolic_iff_reduced_word cs _ a).mp ha
  have hext : cs.IsReduced (u++[i]) := by
    simpa only [CoxeterSystem.IsReduced,cs.wordProd_append,cs.wordProd_singleton,
      List.length_append,List.length_singleton,hr.eq] using has
  cases u with
  | nil => exact ⟨1,0,by norm_num,by norm_num,by simp⟩
  | cons k u =>
    have hk := hu k (by simp)
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hk
    rcases hk with hki | hkj
    · subst k
      apply root_coeff_of_alt_extension cs i j hij (i::u) i _ hext
      simpa only [List.cons_append,List.length_append,List.length_singleton,List.length_cons,List.length_nil,Nat.zero_add] using
        reduced_pair_cons_eq_alt cs i j (u++[i]) hext (by
          intro k hk
          rcases List.mem_append.mp hk with hk | hk
          · exact hu k (List.mem_cons_of_mem i hk)
          · simp only [List.mem_singleton] at hk
            subst k
            simp)
    · subst k
      obtain ⟨x,y,hx,hy,he⟩ := root_coeff_of_alt_extension cs j i (Ne.symm hij) (j::u) i
        (by
          simpa only [List.cons_append,List.length_append,List.length_singleton,List.length_cons,List.length_nil,Nat.zero_add] using
            reduced_pair_cons_eq_alt cs j i (u++[i]) hext (by
              intro k hk
              rcases List.mem_append.mp hk with hk | hk
              · simpa only [Set.mem_insert_iff,Set.mem_singleton_iff,or_comm] using
                  hu k (List.mem_cons_of_mem j hk)
              · simp only [List.mem_singleton] at hk
                subst k
                simp)) hext
      exact ⟨y,x,hy,hx,he.trans (add_comm _ _)⟩

end HarmonicArtin.Geometric

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Geometry_RootNonnegAscent
attribute [-instance] _root_.OAI.HarmonicArtin.instPreorderLiftedCell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.Geometric
open HarmonicArtin.CoxeterExchange

attribute [local instance] Classical.propDecidable Classical.decEq
variable {S W : Type*} [Fintype S] [DecidableEq S] [Group W]
  {M : CoxeterMatrix S} (cs : CoxeterSystem M W)

theorem root_nonneg_of_ascent (w : W) (s : S)
    (hs : cs.length (w*cs.simple s)=cs.length w+1) :
    ∀ k, 0 ≤ representation cs w (Pi.single s 1) k := by
  suffices H : ∀ n : ℕ, ∀ w : W, cs.length w=n → ∀ s : S,
      cs.length (w*cs.simple s)=cs.length w+1 →
      ∀ k, 0 ≤ representation cs w (Pi.single s 1) k from H _ w rfl s hs
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro w hn s hs
    by_cases hw : w=1
    · subst w
      intro k
      simp only [map_one]
      change 0 ≤ (Pi.single s (1 : ℝ) : S → ℝ) k
      by_cases hks : k=s <;> simp [hks]
    · obtain ⟨j,hj⟩ := exists_right_descent cs hw
      have hsj : s≠j := by intro he; subst j; omega
      let J : Set S := {s,j}
      obtain ⟨v,a,ha,hv,he,hl⟩ := exists_right_parabolic_decomposition cs J w
      have hsJ : s ∈ J := by simp [J]
      have hjJ : j ∈ J := by simp [J]
      have haone : a≠1 := by
        intro h
        have hmin := hv (cs.simple j) (simple_mem_parabolic cs J hjJ)
        rw [h,mul_one] at he
        rw [← he] at hmin
        omega
      have halen : 0 < cs.length a := by
        exact Nat.pos_of_ne_zero (fun h => haone (cs.length_eq_zero_iff.mp h))
      have hvlt : cs.length v < n := by omega
      have hvas : cs.length (v*cs.simple s)=cs.length v+1 := by
        have hmin := hv (cs.simple s) (simple_mem_parabolic cs J hsJ)
        rcases cs.length_mul_simple v s with h | h <;> omega
      have hvaj : cs.length (v*cs.simple j)=cs.length v+1 := by
        have hmin := hv (cs.simple j) (simple_mem_parabolic cs J hjJ)
        rcases cs.length_mul_simple v j with h | h <;> omega
      have hposS := ih (cs.length v) hvlt v rfl s hvas
      have hposJ := ih (cs.length v) hvlt v rfl j hvaj
      have has : cs.length (a*cs.simple s)=cs.length a+1 := by
        have hmul := length_mul_of_right_minimum cs J v hv (a*cs.simple s)
          ((parabolic cs J).mul_mem ha (simple_mem_parabolic cs J hsJ))
        have hwprod : w*cs.simple s=v*(a*cs.simple s) := by rw [he,mul_assoc]
        rw [← hwprod] at hmul
        omega
      obtain ⟨x,y,hx,hy,hroot⟩ := pair_ascent_root_coeff cs s j hsj a ha has
      intro k
      rw [he,map_mul,LinearEquiv.mul_apply,hroot,map_add,map_smul,map_smul]
      exact add_nonneg (mul_nonneg hx (hposS k)) (mul_nonneg hy (hposJ k))

lemma geometric_root_ne_zero (w : W) (s : S) :
    representation cs w (Pi.single s 1) ≠ 0 := by
  intro h
  have hb : (Pi.single s (1 : ℝ) : S → ℝ) = 0 :=
    (representation cs w).map_eq_zero_iff.mp h
  have := congrFun hb s
  simp at this

theorem root_nonpos_of_descent (w : W) (s : S)
    (hs : cs.length (w*cs.simple s)+1=cs.length w) :
    ∀ k, representation cs w (Pi.single s 1) k ≤ 0 := by
  have has : cs.length ((w*cs.simple s)*cs.simple s)=cs.length (w*cs.simple s)+1 := by
    rw [cs.simple_mul_simple_cancel_right]
    omega
  have hpos := root_nonneg_of_ascent cs (w*cs.simple s) s has
  rw [map_mul] at hpos
  simp only [LinearEquiv.mul_apply,representation_simple,simpleReflection_basis_self,map_neg,
    Pi.neg_apply,neg_nonneg] at hpos
  exact hpos

theorem root_nonneg_iff_ascent (w : W) (s : S) :
    (∀ k, 0 ≤ representation cs w (Pi.single s 1) k) ↔
      cs.length (w*cs.simple s)=cs.length w+1 := by
  constructor
  · intro h
    rcases cs.length_mul_simple w s with hlen | hlen
    · exact hlen
    · have hn := root_nonpos_of_descent cs w s hlen
      have hz : representation cs w (Pi.single s 1)=0 :=
        funext (fun k => le_antisymm (hn k) (h k))
      exact (geometric_root_ne_zero cs w s hz).elim
  · exact root_nonneg_of_ascent cs w s

end HarmonicArtin.Geometric

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Coxeter_AltListReduced
attribute [-instance] _root_.OAI.HarmonicArtin.instPreorderLiftedCell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.CoxeterExchange
open Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S W : Type*} [Fintype S] [DecidableEq S] [Group W]
  {M : CoxeterMatrix S} (cs : CoxeterSystem M W)

theorem altList_reduced (i j : S) (hij : i≠j) (n : ℕ) (hn : M i j=0 ∨ n≤M i j) :
    cs.IsReduced (altList i j n) := by
  induction n with
  | zero => simp [CoxeterSystem.IsReduced]
  | succ n ih =>
    have hn' : M i j=0 ∨ n≤M i j := by omega
    have hred := ih hn'
    have hroot : ∀ k,0 ≤ representation cs (cs.wordProd (altList i j n))
        (Pi.single (altNext i j n) 1) k := by
      rw [alternating_next_root cs i j hij n]
      intro k
      exact add_nonneg
        (mul_nonneg (dihedralScalar_nonneg _ _ hn) (by simp [Pi.single_apply]; split_ifs <;> norm_num))
        (mul_nonneg (dihedralScalar_nonneg _ _ hn') (by simp [Pi.single_apply]; split_ifs <;> norm_num))
    have ha := (root_nonneg_iff_ascent cs (cs.wordProd (altList i j n)) (altNext i j n)).mp hroot
    change cs.length (cs.wordProd (altList i j (n+1)))=(altList i j (n+1)).length
    rw [altList_succ_append,cs.wordProd_append,cs.wordProd_singleton,ha,hred.eq]
    simp

omit [Fintype S] [DecidableEq S] in
lemma pair_length_bound (i j : S) (hm : 2≤M i j) (w : W)
    (hw : w∈parabolic cs ({i,j} : Set S)) : cs.length w≤M i j := by
  obtain ⟨u,hu,hr,he⟩ := (mem_parabolic_iff_reduced_word cs _ _).mp hw
  cases u with
  | nil => simp only [cs.wordProd_nil] at he; simp [← he]
  | cons k u =>
    have hk := hu k (by simp)
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hk
    rcases hk with hk|hk
    · subst k
      have hs := reduced_pair_cons_eq_alt cs i j u hr (fun k hk => hu k (List.mem_cons_of_mem _ hk))
      have hb := reduced_altList_le cs i j (u.length+1) hm (hs ▸ hr)
      rw [← he,hr.eq,List.length_cons]
      exact hb
    · subst k
      have hs := reduced_pair_cons_eq_alt cs j i u hr
        (fun k hk => by simpa only [Set.pair_comm] using hu k (List.mem_cons_of_mem _ hk))
      have hb := reduced_altList_le cs j i (u.length+1) (by simpa only [M.symmetric j i] using hm) (hs ▸ hr)
      rw [← he,hr.eq,List.length_cons]
      simpa only [M.symmetric j i] using hb

omit [DecidableEq S] in
lemma finite_parabolic_pair (i j : S) (hm : 2≤M i j) : Finite (parabolic cs ({i,j} : Set S)) := by
  have ht : Set.Finite {w : W | cs.length w≤M i j} := by
    apply ((List.finite_length_le S (M i j)).image cs.wordProd).subset
    intro w hw
    obtain ⟨u,hu,he⟩ := cs.exists_isReduced w
    refine ⟨u,?_,he.symm⟩
    change u.length≤M i j
    rw [← hu.eq,← he]
    exact hw
  let : Finite {w : W // cs.length w≤M i j} := ht
  apply Finite.of_injective
    (fun w : parabolic cs ({i,j} : Set S) => (⟨w,pair_length_bound cs i j hm w w.property⟩ :
      {w : W // cs.length w≤M i j}))
  intro a b h
  exact Subtype.ext (congrArg (fun w : {w : W // cs.length w≤M i j} => (w:W)) h)

end HarmonicArtin.CoxeterExchange

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Coxeter_WeakPrefix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.CoxeterExchange
attribute [local instance] Classical.decEq Classical.propDecidable
variable {B W:Type*} [Group W] {M:CoxeterMatrix B} (cs:CoxeterSystem M W)

def WeakPrefix (a b:W) : Prop := cs.length b=cs.length a+cs.length (a⁻¹*b)

lemma weakPrefix_one (a:W) : WeakPrefix cs 1 a := by simp [WeakPrefix]
lemma weakPrefix_length {a b:W} (h:WeakPrefix cs a b) : cs.length a ≤ cs.length b := by
  unfold WeakPrefix at h;omega

lemma weakPrefix_trans {a b c:W} (hab:WeakPrefix cs a b) (hbc:WeakPrefix cs b c) : WeakPrefix cs a c := by
  have hl:=cs.length_mul_le (a⁻¹*b) (b⁻¹*c)
  have he:(a⁻¹*b)*(b⁻¹*c)=a⁻¹*c:=by group
  rw [he] at hl
  have hr:=cs.length_mul_le a (a⁻¹*c)
  rw [mul_inv_cancel_left] at hr
  unfold WeakPrefix at *
  omega

lemma weakPrefix_simple_iff (s:B) (a:W) : WeakPrefix cs (cs.simple s) a ↔ cs.length (cs.simple s*a)+1=cs.length a := by
  simp only [WeakPrefix,cs.length_simple,cs.inv_simple]
  omega

lemma weakPrefix_left_remove {a b:W} (s:B) (ha:WeakPrefix cs (cs.simple s) a)
    (hb:WeakPrefix cs (cs.simple s) b) :
    WeakPrefix cs (cs.simple s*a) (cs.simple s*b) ↔ WeakPrefix cs a b := by
  have hla:=(weakPrefix_simple_iff cs s a).mp ha
  have hlb:=(weakPrefix_simple_iff cs s b).mp hb
  have he:(cs.simple s*a)⁻¹*(cs.simple s*b)=a⁻¹*b:=by group
  unfold WeakPrefix
  rw [he]
  omega

lemma weakPrefix_left_add {g a:W} (s:B) (ha:WeakPrefix cs (cs.simple s) a)
    (hg:WeakPrefix cs g (cs.simple s*a)) :
    WeakPrefix cs (cs.simple s*g) a ∧ cs.length (cs.simple s*g)=cs.length g+1 := by
  have hla:=(weakPrefix_simple_iff cs s a).mp ha
  have hmul:=cs.length_mul_le (cs.simple s*g) (g⁻¹*(cs.simple s*a))
  have he:(cs.simple s*g)*(g⁻¹*(cs.simple s*a))=a:=by
    rw [mul_assoc,mul_inv_cancel_left,cs.simple_mul_simple_cancel_left]
  rw [he] at hmul
  have hstep:=cs.length_simple_mul g s
  have hlen:cs.length (cs.simple s*g)=cs.length g+1:=by unfold WeakPrefix at hg;omega
  refine ⟨?_,hlen⟩
  have hsuf:(cs.simple s*g)⁻¹*a=g⁻¹*(cs.simple s*a):=by rw [mul_inv_rev,cs.inv_simple,mul_assoc]
  unfold WeakPrefix at *
  rw [hsuf,hlen]
  omega

lemma exists_simple_prefix {a:W} (ha:a≠1) : ∃s:B,WeakPrefix cs (cs.simple s) a := by
  obtain ⟨w,hw,he⟩:=cs.exists_isReduced a
  cases w with
  | nil=>simp only [cs.wordProd_nil] at he;exact (ha he).elim
  | cons s w=>
    refine ⟨s,(weakPrefix_simple_iff cs s a).mpr ?_⟩
    have hl:=hw.drop 1
    simp only [List.drop_succ_cons,List.drop_zero] at hl
    rw [he,hw.eq,cs.wordProd_cons,cs.simple_mul_simple_cancel_left,hl.eq]
    rfl

lemma weakPrefix_first_of_reduced (s:B) (w:List B) (h:cs.IsReduced (s::w)) :
    WeakPrefix cs (cs.simple s) (cs.wordProd (s::w)) := by
  apply (weakPrefix_simple_iff cs s _).mpr
  have hr:=h.drop 1
  simp only [List.drop_succ_cons,List.drop_zero] at hr
  rw [h.eq,cs.wordProd_cons,cs.simple_mul_simple_cancel_left,hr.eq]
  rfl

variable [Fintype B]

lemma simple_pair_prefix (s t:B) (hne:s≠t) {a:W}
    (hs:WeakPrefix cs (cs.simple s) a) (ht:WeakPrefix cs (cs.simple t) a) :
    WeakPrefix cs (cs.wordProd (altList s t (M s t))) a ∧
      WeakPrefix cs (cs.simple s) (cs.wordProd (altList s t (M s t))) ∧
      WeakPrefix cs (cs.simple t) (cs.wordProd (altList s t (M s t))) := by
  have hsl:=(weakPrefix_simple_iff cs s a).mp hs
  have htl:=(weakPrefix_simple_iff cs t a).mp ht
  obtain ⟨v,hm,hl,he,he'⟩:=double_descent_prefix cs s t hne a (by omega) (by omega)
  let d:=cs.wordProd (altList s t (M s t))
  have hred:cs.IsReduced (altList s t (M s t)):=by
    have hd:=cs.length_wordProd_le (altList s t (M s t))
    have hh:=cs.length_mul_le d v
    change cs.length (cs.wordProd (altList s t (M s t))*v) ≤ cs.length (cs.wordProd (altList s t (M s t)))+cs.length v at hh
    rw [←he] at hh
    simp only [length_altList] at hd
    change cs.length d=(altList s t (M s t)).length
    rw [length_altList]
    dsimp [d]
    omega
  have hda:WeakPrefix cs d a:=by
    unfold WeakPrefix
    rw [he,inv_mul_cancel_left,hred.eq,length_altList]
    simpa only [he] using hl
  have hsD:WeakPrefix cs (cs.simple s) d:=by
    obtain ⟨n,hn⟩:=Nat.exists_eq_succ_of_ne_zero (by omega : M s t≠0)
    change WeakPrefix cs (cs.simple s) (cs.wordProd (altList s t (M s t)))
    rw [hn,altList_succ] at hred ⊢
    exact weakPrefix_first_of_reduced cs s _ hred
  have htD:WeakPrefix cs (cs.simple t) d:=by
    have hdEq:cs.wordProd (altList s t (M s t))=cs.wordProd (altList t s (M s t)):=altList_braid cs s t
    have htred:cs.IsReduced (altList t s (M s t)):=by
      change cs.length (cs.wordProd (altList t s (M s t)))=(altList t s (M s t)).length
      rw [←hdEq,hred.eq,length_altList,length_altList]
    change WeakPrefix cs (cs.simple t) (cs.wordProd (altList s t (M s t)))
    rw [hdEq]
    obtain ⟨n,hn⟩:=Nat.exists_eq_succ_of_ne_zero (by omega : M s t≠0)
    rw [hn,altList_succ] at htred ⊢
    exact weakPrefix_first_of_reduced cs t _ htred
  exact ⟨hda,hsD,htD⟩

end HarmonicArtin.CoxeterExchange

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Coxeter_CommonWeakPrefixMaximal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.CoxeterExchange
attribute [local instance] Classical.decEq Classical.propDecidable
variable {B W:Type*} [Group W] [Fintype B] {M:CoxeterMatrix B} (cs:CoxeterSystem M W)

omit [Fintype B] in
lemma common_weakPrefix_maximal_remove (a b g:W)
    (hmax:∀x:W,WeakPrefix cs x a→WeakPrefix cs x b→cs.length x ≤ cs.length g)
    (s:B) (hsa:WeakPrefix cs (cs.simple s) a) (hsb:WeakPrefix cs (cs.simple s) b)
    (hsg:WeakPrefix cs (cs.simple s) g) :
    ∀x:W,WeakPrefix cs x (cs.simple s*a)→WeakPrefix cs x (cs.simple s*b)→
      cs.length x ≤ cs.length (cs.simple s*g) := by
  intro x hxa hxb
  obtain ⟨hxa',hl⟩:=weakPrefix_left_add cs s hsa hxa
  have hxb':=(weakPrefix_left_add cs s hsb hxb).1
  have hh:=hmax _ hxa' hxb'
  have hg:=(weakPrefix_simple_iff cs s g).mp hsg
  omega

theorem maximal_common_weakPrefix_greatest (a b g:W)
    (hga:WeakPrefix cs g a) (hgb:WeakPrefix cs g b)
    (hmax:∀x:W,WeakPrefix cs x a→WeakPrefix cs x b→cs.length x ≤ cs.length g) :
    ∀e:W,WeakPrefix cs e a→WeakPrefix cs e b→WeakPrefix cs e g := by
  induction a using (measure cs.length).wf.induction generalizing b g with
  | h a ih=>
    intro e hea heb
    by_cases he:e=1
    · rw [he];exact weakPrefix_one cs g
    obtain ⟨s,hse⟩:=exists_simple_prefix cs he
    have hsa:=weakPrefix_trans cs hse hea
    have hsb:=weakPrefix_trans cs hse heb
    have hsg:WeakPrefix cs (cs.simple s) g:=by
      have hg:g≠1:=by
        intro hg
        have hh:=hmax _ hsa hsb
        rw [hg,cs.length_simple,cs.length_one] at hh
        omega
      obtain ⟨t,htg⟩:=exists_simple_prefix cs hg
      by_cases hts:t=s
      · simpa only [hts] using htg
      have hta:=weakPrefix_trans cs htg hga
      have htb:=weakPrefix_trans cs htg hgb
      let d:=cs.wordProd (altList t s (M t s))
      obtain ⟨hda,htd,hsd⟩:=simple_pair_prefix cs t s hts hta hsa
      have hdb:WeakPrefix cs d b:=(simple_pair_prefix cs t s hts htb hsb).1
      have hga':WeakPrefix cs (cs.simple t*g) (cs.simple t*a):=
        (weakPrefix_left_remove cs t htg hta).mpr hga
      have hgb':WeakPrefix cs (cs.simple t*g) (cs.simple t*b):=
        (weakPrefix_left_remove cs t htg htb).mpr hgb
      have hmax':=common_weakPrefix_maximal_remove cs a b g hmax t hta htb htg
      have hlt:cs.length (cs.simple t*a) < cs.length a:=by
        have hh:=(weakPrefix_simple_iff cs t a).mp hta;omega
      have hda':WeakPrefix cs (cs.simple t*d) (cs.simple t*a):=
        (weakPrefix_left_remove cs t htd hta).mpr hda
      have hdb':WeakPrefix cs (cs.simple t*d) (cs.simple t*b):=
        (weakPrefix_left_remove cs t htd htb).mpr hdb
      have hdg':=ih (cs.simple t*a) hlt (cs.simple t*b) (cs.simple t*g) hga' hgb' hmax' (cs.simple t*d) hda' hdb'
      have hdg:WeakPrefix cs d g:=(weakPrefix_left_remove cs t htd htg).mp hdg'
      exact weakPrefix_trans cs hsd hdg
    have hea':WeakPrefix cs (cs.simple s*e) (cs.simple s*a):=
      (weakPrefix_left_remove cs s hse hsa).mpr hea
    have heb':WeakPrefix cs (cs.simple s*e) (cs.simple s*b):=
      (weakPrefix_left_remove cs s hse hsb).mpr heb
    have hga':WeakPrefix cs (cs.simple s*g) (cs.simple s*a):=
      (weakPrefix_left_remove cs s hsg hsa).mpr hga
    have hgb':WeakPrefix cs (cs.simple s*g) (cs.simple s*b):=
      (weakPrefix_left_remove cs s hsg hsb).mpr hgb
    have hmax':=common_weakPrefix_maximal_remove cs a b g hmax s hsa hsb hsg
    have hlt:cs.length (cs.simple s*a) < cs.length a:=by
      have hh:=(weakPrefix_simple_iff cs s a).mp hsa;omega
    have heg':=ih (cs.simple s*a) hlt (cs.simple s*b) (cs.simple s*g) hga' hgb' hmax' (cs.simple s*e) hea' heb'
    exact (weakPrefix_left_remove cs s hse hsg).mp heg'

theorem exists_greatest_common_weakPrefix (a b:W) :
    ∃g:W,WeakPrefix cs g a ∧ WeakPrefix cs g b ∧
      ∀e:W,WeakPrefix cs e a→WeakPrefix cs e b→WeakPrefix cs e g := by
  let P:ℕ→Prop:=fun n=>∃g:W,WeakPrefix cs g a ∧ WeakPrefix cs g b ∧ cs.length g=n
  have hP:P 0:=⟨1,weakPrefix_one cs a,weakPrefix_one cs b,cs.length_one⟩
  obtain ⟨g,hga,hgb,hlen⟩:=Nat.findGreatest_spec (Nat.zero_le (cs.length a)) hP
  refine ⟨g,hga,hgb,maximal_common_weakPrefix_greatest cs a b g hga hgb ?_⟩
  intro x hxa hxb
  rw [hlen]
  exact Nat.le_findGreatest (weakPrefix_length cs hxa) ⟨x,hxa,hxb,rfl⟩

end HarmonicArtin.CoxeterExchange

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Coxeter_ReducedWordProperty
attribute [-instance] _root_.OAI.HarmonicArtin.instPreorderLiftedCell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.CoxeterExchange
variable {B W : Type*} [Group W] [Fintype B] [DecidableEq B]
variable {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

theorem reduced_word_property {N : Type*} [Monoid N] (f : B → N)
    (hbraid : ∀ i j, ((altList i j (M i j)).map f).prod =
      ((altList j i (M i j)).map f).prod)
    (u v : List B) (hu : cs.IsReduced u) (hv : cs.IsReduced v)
    (he : cs.wordProd u = cs.wordProd v) : (u.map f).prod = (v.map f).prod := by
  suffices hall : ∀ n (u v : List B), u.length=n → cs.IsReduced u → cs.IsReduced v →
      cs.wordProd u=cs.wordProd v → (u.map f).prod=(v.map f).prod by
    exact hall u.length u v rfl hu hv he
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro u v hlen hu hv he
    cases u with
    | nil =>
      have hv0 : v.length=0 := by rw [← hv.eq,← he]; simp
      have hvnil := List.eq_nil_of_length_eq_zero hv0
      simp [hvnil]
    | cons i u =>
      cases v with
      | nil =>
        have hu0 : (i::u).length=0 := by rw [← hu.eq,he]; simp
        simp at hu0
      | cons j v =>
        have hur : cs.IsReduced u := by simpa only [List.drop_succ_cons,List.drop_zero] using hu.drop 1
        have hvr : cs.IsReduced v := by simpa only [List.drop_succ_cons,List.drop_zero] using hv.drop 1
        have hsmall : u.length<n := by simp only [List.length_cons] at hlen; omega
        have hvlen : v.length=u.length := by
          have hl := congrArg cs.length he
          rw [hu.eq,hv.eq] at hl
          simp only [List.length_cons] at hl
          omega
        by_cases hij : i=j
        · subst j
          have htail : cs.wordProd u=cs.wordProd v := by
            simpa only [cs.wordProd_cons,mul_left_cancel_iff] using he
          simp only [List.map_cons,List.prod_cons]
          rw [ih u.length hsmall u v rfl hur hvr htail]
        · let w := cs.wordProd (i::u)
          have hdi : cs.length (cs.simple i*w) < cs.length w := by
            change cs.length (cs.simple i*cs.wordProd (i::u)) < cs.length (cs.wordProd (i::u))
            rw [hu.eq,cs.wordProd_cons,cs.simple_mul_simple_cancel_left,hur.eq,List.length_cons]
            omega
          have hdj : cs.length (cs.simple j*w) < cs.length w := by
            change cs.length (cs.simple j*cs.wordProd (i::u)) < cs.length (cs.wordProd (i::u))
            rw [he,hv.eq,cs.wordProd_cons,cs.simple_mul_simple_cancel_left,hvr.eq,List.length_cons]
            omega
          obtain ⟨r,hm,hl,hip,hjp⟩ := double_descent_prefix cs i j hij w hdi hdj
          obtain ⟨c,hcr,hcp⟩ := cs.exists_isReduced r
          have hpi : cs.wordProd (altList i j (M i j)++c)=w := by
            rw [cs.wordProd_append,← hcp]
            exact hip.symm
          have hpj : cs.wordProd (altList j i (M i j)++c)=w := by
            rw [cs.wordProd_append,← hcp]
            exact hjp.symm
          have hri : cs.IsReduced (altList i j (M i j)++c) := by
            change cs.length (cs.wordProd _)=_
            rw [hpi,hl,List.length_append,length_altList,← hcr.eq,← hcp]
          have hrj : cs.IsReduced (altList j i (M i j)++c) := by
            change cs.length (cs.wordProd _)=_
            rw [hpj,hl,List.length_append,length_altList,← hcr.eq,← hcp]
          obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hm)
          have hti : cs.IsReduced (altList j i k++c) := by
            rw [hk,altList_succ,List.cons_append] at hri
            simpa only [List.drop_succ_cons,List.drop_zero] using hri.drop 1
          have htj : cs.IsReduced (altList i j k++c) := by
            rw [hk,altList_succ,List.cons_append] at hrj
            simpa only [List.drop_succ_cons,List.drop_zero] using hrj.drop 1
          have hei : cs.wordProd u=cs.wordProd (altList j i k++c) := by
            apply mul_left_cancel (a:=cs.simple i)
            simpa only [w,hk,altList_succ,List.cons_append,cs.wordProd_cons] using hpi.symm
          have hej : cs.wordProd v=cs.wordProd (altList i j k++c) := by
            apply mul_left_cancel (a:=cs.simple j)
            have hh := he.symm.trans hpj.symm
            simpa only [hk,altList_succ,List.cons_append,cs.wordProd_cons] using hh
          have hevi := ih u.length hsmall u (altList j i k++c) rfl hur hti hei
          have hevj := ih v.length (by omega) v (altList i j k++c) rfl hvr htj hej
          calc
            ((i::u).map f).prod = ((altList i j (M i j)++c).map f).prod := by
              simp only [hk,altList_succ,List.cons_append,List.map_cons,List.prod_cons,hevi]
            _ = ((altList j i (M i j)++c).map f).prod := by
              simp only [List.map_append,List.prod_append]
              rw [hbraid i j]
            _ = ((j::v).map f).prod := by
              simp only [hk,altList_succ,List.cons_append,List.map_cons,List.prod_cons,hevj]

end HarmonicArtin.CoxeterExchange

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_DeligneDefinitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
universe u
variable {S : Type u}
def artinParabolic (M : CoxeterMatrix S) (T : Set S) : Subgroup (Artin M) :=
  Subgroup.closure (generator M '' T)

def rightCoset (M : CoxeterMatrix S) (T : Set S) (x : Artin M) : Set (Artin M) :=
  {g | g * x⁻¹ ∈ artinParabolic M T}

abbrev Deligne (M : CoxeterMatrix S) :=
  {c : Set S × Set (Artin M) //
    IsSpherical M c.1 ∧ ∃ x : Artin M, c.2 = rightCoset M c.1 x}

noncomputable def DeligneRealization (M : CoxeterMatrix S) : TopCat :=
  SSet.toTop.obj (CategoryTheory.nerve (Deligne M))

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_ReducedExpression
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
universe v
variable {S : Type v}
open CoxeterExchange

lemma wordArtin_altList (M : CoxeterMatrix S) (i j : S) (n : ℕ) :
    wordArtin M (altList i j n) = PresentedGroup.mk (braidRelators M) (alternating i j n) := by
  induction n generalizing i j with
  | zero => simp [wordArtin,alternating]
  | succ n ih =>
    simp only [altList_succ,wordArtin,List.map_cons,List.prod_cons,alternating,map_mul]
    rw [← ih]
    rfl

lemma wordArtin_braid (M : CoxeterMatrix S) (i j : S) :
    wordArtin M (altList i j (M i j)) = wordArtin M (altList j i (M i j)) := by
  rw [wordArtin_altList,wordArtin_altList]
  exact PresentedGroup.mk_eq_mk_of_mul_inv_mem ⟨(i,j),rfl⟩

theorem wordArtin_eq_of_reduced [Finite S] (M : CoxeterMatrix S)
    (u v : List S)
    (hu : M.toCoxeterSystem.IsReduced u) (hv : M.toCoxeterSystem.IsReduced v)
    (he : wordCoxeter M u=wordCoxeter M v) : wordArtin M u=wordArtin M v := by
  classical
  let := Fintype.ofFinite S
  exact reduced_word_property M.toCoxeterSystem (generator M) (wordArtin_braid M)
    u v hu hv he

noncomputable def reducedExpression (M : CoxeterMatrix S) (w : M.Group) : List S :=
  Classical.choose (M.toCoxeterSystem.exists_isReduced w)

lemma reducedExpression_reduced (M : CoxeterMatrix S) (w : M.Group) :
    M.toCoxeterSystem.IsReduced (reducedExpression M w) :=
  (Classical.choose_spec (M.toCoxeterSystem.exists_isReduced w)).1

lemma wordCoxeter_reducedExpression (M : CoxeterMatrix S) (w : M.Group) :
    wordCoxeter M (reducedExpression M w)=w :=
  (Classical.choose_spec (M.toCoxeterSystem.exists_isReduced w)).2.symm

noncomputable def positiveLift (M : CoxeterMatrix S) (w : M.Group) : Artin M :=
  wordArtin M (reducedExpression M w)

lemma positiveLift_word [Finite S] (M : CoxeterMatrix S) (u : List S)
    (hu : M.toCoxeterSystem.IsReduced u) :
    positiveLift M (wordCoxeter M u)=wordArtin M u :=
  wordArtin_eq_of_reduced M _ u (reducedExpression_reduced M _) hu
    (wordCoxeter_reducedExpression M _)

@[simp] lemma positiveLift_one [Finite S] (M : CoxeterMatrix S) : positiveLift M 1=1 := by
  have hr : M.toCoxeterSystem.IsReduced ([] : List S) := by simp [CoxeterSystem.IsReduced]
  simpa only [wordCoxeter,List.map_nil,List.prod_nil,wordArtin] using positiveLift_word M [] hr

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Coxeter_PositiveBraidRelations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CoxeterExchange

universe u
variable {S:Type u} (M:CoxeterMatrix S)

def positiveBraidRelations (u v:FreeMonoid S) : Prop :=
  ∃s t:S,u=FreeMonoid.ofList (altList s t (M s t)) ∧ v=FreeMonoid.ofList (altList t s (M s t))

abbrev PositiveArtin := PresentedMonoid (positiveBraidRelations M)

def positiveGenerator (s:S) : PositiveArtin M := PresentedMonoid.of (positiveBraidRelations M) s

def wordPositive (w:List S) : PositiveArtin M := (w.map (positiveGenerator M)).prod

lemma wordPositive_mk (w:List S) : wordPositive M w=PresentedMonoid.mk (positiveBraidRelations M) (FreeMonoid.ofList w) := by
  induction w with
  | nil=>rfl
  | cons s w ih=>
    change positiveGenerator M s*wordPositive M w=PresentedMonoid.mk (positiveBraidRelations M) (FreeMonoid.of s*FreeMonoid.ofList w)
    rw [map_mul,←ih];rfl

lemma wordPositive_braid (s t:S) : wordPositive M (altList s t (M s t))=wordPositive M (altList t s (M s t)) := by
  rw [wordPositive_mk,wordPositive_mk]
  exact PresentedMonoid.mk_eq_mk_of_rel ⟨s,t,rfl,rfl⟩

lemma wordPositive_eq_of_reduced [Finite S] (u v:List S)
    (hu:M.toCoxeterSystem.IsReduced u) (hv:M.toCoxeterSystem.IsReduced v)
    (he:wordCoxeter M u=wordCoxeter M v) : wordPositive M u=wordPositive M v := by
  classical
  let := Fintype.ofFinite S
  exact reduced_word_property M.toCoxeterSystem (positiveGenerator M) (wordPositive_braid M) u v hu hv he

lemma positiveToArtin_relations : ∀u v:FreeMonoid S,positiveBraidRelations M u v →
    FreeMonoid.lift (generator M) u=FreeMonoid.lift (generator M) v := by
  rintro u v ⟨s,t,rfl,rfl⟩
  simpa only [FreeMonoid.lift_ofList,wordArtin] using wordArtin_braid M s t

def positiveToArtin : PositiveArtin M →* Artin M :=
  PresentedMonoid.lift (generator M) (positiveToArtin_relations M)

@[simp] lemma positiveToArtin_generator (s:S) : positiveToArtin M (positiveGenerator M s)=generator M s :=rfl

@[simp] lemma positiveToArtin_word (w:List S) : positiveToArtin M (wordPositive M w)=wordArtin M w := by
  induction w with
  | nil=>exact map_one _
  | cons s w ih=>
    change positiveToArtin M (positiveGenerator M s*wordPositive M w)=generator M s*wordArtin M w
    rw [map_mul,positiveToArtin_generator,ih]

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Coxeter_RestrictedMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.CoxeterExchange
variable {S : Type*}

def restrictedMatrix (M : CoxeterMatrix S) (J : Set S) : CoxeterMatrix J where
  M i j := M i j
  isSymm := M.isSymm.submatrix Subtype.val
  diagonal i := M.diagonal i
  off_diagonal i j h := M.off_diagonal i j (fun he => h (Subtype.ext he))

@[simp] lemma restrictedMatrix_apply (M : CoxeterMatrix S) (J : Set S) (i j : J) :
    restrictedMatrix M J i j=M i j := rfl

noncomputable def restrictionHom (M : CoxeterMatrix S) (J : Set S) :
    (restrictedMatrix M J).Group →* M.Group :=
  (restrictedMatrix M J).toCoxeterSystem.lift
    ⟨fun i => M.simple i, fun i j => M.toCoxeterSystem.simple_mul_simple_pow i j⟩

@[simp] lemma restrictionHom_simple (M : CoxeterMatrix S) (J : Set S) (i : J) :
    restrictionHom M J ((restrictedMatrix M J).toCoxeterSystem.simple i)=M.toCoxeterSystem.simple i :=
  (restrictedMatrix M J).toCoxeterSystem.lift_apply_simple _ i

end HarmonicArtin.CoxeterExchange

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Geometry_CoordinateExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.Geometric
open _root_.Matrix
open scoped _root_.Matrix BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type*} [Fintype S] [DecidableEq S]

noncomputable def coordinateExtension (J:Set S) (v:J → ℝ) : S → ℝ :=
  ∑ j:J,v j • Pi.single (j:S) 1

lemma coordinateExtension_apply (J:Set S) (v:J → ℝ) (j:J) :
    coordinateExtension J v j=v j := by
  simp only [coordinateExtension,Finset.sum_apply,Pi.smul_apply,Pi.single_apply,smul_eq_mul]
  have he : ∀ x:J,(j:S)=x ↔ j=x := fun x=>Subtype.val_injective.eq_iff
  simp_rw [he]
  simp

lemma coordinateExtension_outside (J:Set S) (v:J → ℝ) (i:S) (hi:i∉J) :
    coordinateExtension J v i=0 := by
  unfold coordinateExtension
  rw [Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro j _
  have h:i≠(j:S):=fun h=>hi (h.symm ▸ j.property)
  simp [h]

end HarmonicArtin.Geometric

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Quivers_VertexHom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver
namespace Zigzag

variable {V A K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V]

def vertexId (v : V) : Q.Zigzag K := (Pi.single v 1, 0, 0)

omit [Fintype A] in
@[simp] theorem vertex_vertexId (v : V) :
    (vertexId Q v).vertex = Pi.single v (1 : K) := rfl
omit [Fintype A] in
@[simp] theorem arrow_vertexId (v : V) :
    (vertexId Q (K := K) v).arrow = 0 := rfl
omit [Fintype A] in
@[simp] theorem token_vertexId (v : V) :
    (vertexId Q (K := K) v).token = 0 := rfl

@[simp] theorem vertexId_mul_self (v : V) :
    vertexId Q (K := K) v * vertexId Q v = vertexId Q v := by
  apply Zigzag.ext
  · ext w
    by_cases h : w = v <;> simp [h]
  · ext a
    simp [arrow_mul, leftScale, rightScale]
  · ext w
    simp [token_mul]

end Zigzag
end HarmonicArtin.ReversibleQuiver

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_GeneratorPlacement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin

structure GeneratorPlacement (V : Type*) where
  color : V
  cochain : ℤ
  internal : ℤ
  deriving DecidableEq

namespace ReversibleQuiver.Zigzag

variable {V A K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V]

def Homogeneous (a : ℤ) (x : Q.Zigzag K) : Prop :=
  (a ≠ 0 → x.vertex = 0) ∧ (a ≠ 1 → x.arrow = 0) ∧ (a ≠ 2 → x.token = 0)

variable {I J L : Type*}

def ProjectiveEntries (p : I → GeneratorPlacement V) (q : J → GeneratorPlacement V)
    (M : Matrix I J (Q.Zigzag K)) : Prop :=
  (∀ i j, vertexId Q (p i).color * M i j = M i j) ∧
  (∀ i j, M i j * vertexId Q (q j).color = M i j)

def MapDegree (p : I → GeneratorPlacement V) (q : J → GeneratorPlacement V)
    (n v : ℤ) (M : Matrix I J (Q.Zigzag K)) : Prop :=
  ∀ i j, ((q j).cochain ≠ (p i).cochain + n → M i j = 0) ∧
    Homogeneous Q (v + (p i).internal - (q j).internal) (M i j)

def projectiveIdentity [DecidableEq I] (p : I → GeneratorPlacement V) :
    Matrix I I (Q.Zigzag K) := Matrix.diagonal fun i => vertexId Q (p i).color

omit [Fintype A] in
lemma vertexId_eval (v w : V) :
    (vertexId Q (K := K) v).vertex w = if w = v then 1 else 0 := by
  simp only [vertex_vertexId, Pi.single_apply]

structure BasedComplex (I : Type*) [Fintype I] where
  placement : I → GeneratorPlacement V
  differential : Matrix I I (Q.Zigzag K)
  entries : ProjectiveEntries Q placement placement differential
  degree : MapDegree Q placement placement 1 0 differential
  square_zero : differential * differential = 0

namespace BasedComplex

variable [Fintype I] [Fintype J] [Fintype L]

structure Map (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J) where
  matrix : Matrix I J (Q.Zigzag K)
  entries : ProjectiveEntries Q E.placement F.placement matrix
  degree : MapDegree Q E.placement F.placement 0 0 matrix
  commute : E.differential * matrix = matrix * F.differential

end BasedComplex
end ReversibleQuiver.Zigzag
end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_Level
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin

def GeneratorPlacement.level {V : Type*} (p : GeneratorPlacement V) : ℤ :=
  p.cochain + p.internal

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Geometry_CartanRestricted
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.Geometric
open HarmonicArtin.CoxeterExchange
open scoped BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type*} [Fintype S] [DecidableEq S]

omit [Fintype S] in
lemma cartan_restricted (M : CoxeterMatrix S) (J : Set S) :
    cartan (restrictedMatrix M J)=(cartan M).submatrix Subtype.val Subtype.val := by
  ext i j
  by_cases hij : i=j
  · subst j
    simp [cartan]
  · have hval : (i:S)≠j := fun h => hij (Subtype.ext h)
    simp [cartan,hij,hval]

lemma coordinateExtension_sub (J : Set S) (x y : J → ℝ) :
    coordinateExtension J (x-y)=coordinateExtension J x-coordinateExtension J y := by
  simp only [coordinateExtension,Pi.sub_apply,sub_smul,Finset.sum_sub_distrib]

lemma coordinateExtension_smul (J : Set S) (r : ℝ) (x : J → ℝ) :
    coordinateExtension J (r • x)=r • coordinateExtension J x := by
  simp only [coordinateExtension,Pi.smul_apply,smul_eq_mul,mul_smul,Finset.smul_sum]

lemma coordinateExtension_single (J : Set S) (i : J) :
    coordinateExtension J (Pi.single i 1)=Pi.single (i:S) 1 := by
  ext k
  by_cases hk : k ∈ J
  · simpa only [Pi.single_apply,Subtype.ext_iff] using
      coordinateExtension_apply J (Pi.single i 1) ⟨k,hk⟩
  · rw [coordinateExtension_outside J _ k hk]
    have hki : k≠(i:S) := fun h => hk (h.symm ▸ i.property)
    simp [hki]

lemma rootRow_extension (M : CoxeterMatrix S) (J : Set S) (i : J) (x : J → ℝ) :
    rootRow M i (coordinateExtension J x)=rootRow (restrictedMatrix M J) i x := by
  rw [rootRow_apply,rootRow_apply]
  unfold coordinateExtension
  rw [Matrix.mulVec_sum,Finset.sum_apply]
  simp only [Matrix.mulVec_smul,Pi.smul_apply,Matrix.mulVec_single,smul_eq_mul,
    Matrix.col,Matrix.transpose_apply,MulOpposite.op_one,one_smul]
  rw [cartan_restricted]
  simp only [Matrix.mulVec,dotProduct,Matrix.submatrix_apply,mul_comm]

lemma reflection_extension (M : CoxeterMatrix S) (J : Set S) (i : J) (x : J → ℝ) :
    simpleReflection M i (coordinateExtension J x)=
      coordinateExtension J (simpleReflection (restrictedMatrix M J) i x) := by
  simp only [simpleReflection_apply,← rootRow_apply,rootRow_extension,
    coordinateExtension_sub,coordinateExtension_smul,coordinateExtension_single]

lemma representation_extension (M : CoxeterMatrix S) (J : Set S)
    (w : (restrictedMatrix M J).Group) (x : J → ℝ) :
    representation M.toCoxeterSystem (restrictionHom M J w) (coordinateExtension J x)=
      coordinateExtension J (representation (restrictedMatrix M J).toCoxeterSystem w x) := by
  induction w using (restrictedMatrix M J).toCoxeterSystem.simple_induction_left generalizing x with
  | one => simp
  | mul_simple_left w i ih =>
    rw [map_mul,map_mul,LinearEquiv.mul_apply,restrictionHom_simple,representation_simple,ih,
      map_mul,LinearEquiv.mul_apply,representation_simple,reflection_extension]

lemma coordinateExtension_nonneg_iff (J : Set S) (x : J → ℝ) :
    (∀ k,0 ≤ coordinateExtension J x k) ↔ (∀ i,0 ≤ x i) := by
  constructor
  · intro h i
    simpa only [coordinateExtension_apply] using h i
  · intro h k
    by_cases hk : k∈J
    · change 0 ≤ coordinateExtension J x (⟨k,hk⟩ : J)
      rw [coordinateExtension_apply]
      exact h _
    · rw [coordinateExtension_outside J x k hk]

theorem restriction_ascent_iff (M : CoxeterMatrix S) (J : Set S)
    (w : (restrictedMatrix M J).Group) (i : J) :
    M.toCoxeterSystem.length (restrictionHom M J w*M.toCoxeterSystem.simple i)=
        M.toCoxeterSystem.length (restrictionHom M J w)+1 ↔
      (restrictedMatrix M J).toCoxeterSystem.length (w*(restrictedMatrix M J).toCoxeterSystem.simple i)=
        (restrictedMatrix M J).toCoxeterSystem.length w+1 := by
  rw [← root_nonneg_iff_ascent,← root_nonneg_iff_ascent,
    ← coordinateExtension_single J i,representation_extension,coordinateExtension_nonneg_iff]

end HarmonicArtin.Geometric

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Geometry_RestrictionLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.Geometric
open HarmonicArtin.CoxeterExchange

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type*} [Fintype S] [DecidableEq S]

theorem restriction_length (M : CoxeterMatrix S) (J : Set S)
    (w : (restrictedMatrix M J).Group) :
    M.toCoxeterSystem.length (restrictionHom M J w)=
      (restrictedMatrix M J).toCoxeterSystem.length w := by
  induction w using (restrictedMatrix M J).toCoxeterSystem.simple_induction_right with
  | one => simp
  | mul_simple_right w i ih =>
    rw [map_mul,restrictionHom_simple]
    rcases (restrictedMatrix M J).toCoxeterSystem.length_mul_simple w i with ha | hd
    · rw [(restriction_ascent_iff M J w i).mpr ha,ha,ih]
    · rcases M.toCoxeterSystem.length_mul_simple (restrictionHom M J w) i with ha | hd'
      · have hb := (restriction_ascent_iff M J w i).mp ha
        omega
      · omega

omit [Fintype S] [DecidableEq S] in
lemma restriction_wordProd (M : CoxeterMatrix S) (J : Set S) (u : List J) :
    restrictionHom M J ((restrictedMatrix M J).toCoxeterSystem.wordProd u)=
       M.toCoxeterSystem.wordProd (u.map Subtype.val) := by
  induction u with
  | nil => simp
  | cons i u ih =>
    simp only [CoxeterSystem.wordProd_cons,map_mul,restrictionHom_simple,ih,List.map_cons]

lemma restriction_reduced_iff (M : CoxeterMatrix S) (J : Set S) (u : List J) :
    M.toCoxeterSystem.IsReduced (u.map Subtype.val) ↔
      (restrictedMatrix M J).toCoxeterSystem.IsReduced u := by
  simp only [CoxeterSystem.IsReduced,← restriction_wordProd,restriction_length,List.length_map]

end HarmonicArtin.Geometric

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Coxeter_WordProdEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.CoxeterExchange
variable {B C W H : Type*} [Group W] [Group H]
  {M : CoxeterMatrix B} {N : CoxeterMatrix C}

lemma wordProd_equiv (cs : CoxeterSystem M W) (ds : CoxeterSystem N H)
    (e : B ≃ C) (f : W ≃* H) (hf : ∀ i, f (cs.simple i)=ds.simple (e i)) (u : List B) :
    f (cs.wordProd u)=ds.wordProd (u.map e) := by
  induction u with
  | nil => simp
  | cons i u ih => simp only [CoxeterSystem.wordProd_cons,map_mul,hf,ih,List.map_cons]

lemma length_equiv (cs : CoxeterSystem M W) (ds : CoxeterSystem N H)
    (e : B ≃ C) (f : W ≃* H) (hf : ∀ i, f (cs.simple i)=ds.simple (e i)) (w : W) :
    ds.length (f w)=cs.length w := by
  apply Nat.le_antisymm
  · obtain ⟨u,hu,rfl⟩ := cs.exists_isReduced w
    rw [wordProd_equiv cs ds e f hf,hu.eq]
    simpa using ds.length_wordProd_le (u.map e)
  · have hg : ∀ j, f.symm (ds.simple j)=cs.simple (e.symm j) := by
      intro j
      apply f.injective
      simp only [f.apply_symm_apply,hf,e.apply_symm_apply]
    obtain ⟨v,hv,he⟩ := ds.exists_isReduced (f w)
    have hw : w=f.symm (ds.wordProd v) := by rw [← he]; simp
    conv_lhs => rw [hw,wordProd_equiv ds cs e.symm f.symm hg]
    rw [he,hv.eq]
    simpa using cs.length_wordProd_le (v.map e.symm)

lemma reduced_equiv (cs : CoxeterSystem M W) (ds : CoxeterSystem N H)
    (e : B ≃ C) (f : W ≃* H) (hf : ∀ i, f (cs.simple i)=ds.simple (e i)) (u : List B) :
    ds.IsReduced (u.map e) ↔ cs.IsReduced u := by
  simp only [CoxeterSystem.IsReduced,← wordProd_equiv cs ds e f hf,length_equiv cs ds e f hf,
    List.length_map]

lemma system_reduced_iff (cs : CoxeterSystem M W) (u : List B) :
    M.toCoxeterSystem.IsReduced u ↔ cs.IsReduced u := by
  simpa using reduced_equiv cs M.toCoxeterSystem (Equiv.refl B) cs.mulEquiv
    (fun i => cs.mulEquiv.apply_symm_apply _) u

lemma reindex_reduced (cs : CoxeterSystem M W) (e : B ≃ C) (u : List B) :
    (cs.reindex e).IsReduced (u.map e) ↔ cs.IsReduced u := by
  exact reduced_equiv cs (cs.reindex e) e (MulEquiv.refl W)
    (fun i => by simp) u

theorem embedding_reduced [Fintype C] [DecidableEq C]
    (f : B → C) (hi : Function.Injective f) (hm : ∀ i j, N (f i) (f j)=M i j)
    (u : List B) (hu : M.toCoxeterSystem.IsReduced u) :
    N.toCoxeterSystem.IsReduced (u.map f) := by
  classical
  let e : B ≃ Set.range f := Equiv.ofInjective f hi
  have hM : M.reindex e=restrictedMatrix N (Set.range f) := by
    ext i j
    simp only [CoxeterMatrix.reindex_apply,restrictedMatrix_apply]
    have hi' : f (e.symm i)=i.val := congrArg Subtype.val (e.apply_symm_apply i)
    have hj' : f (e.symm j)=j.val := congrArg Subtype.val (e.apply_symm_apply j)
    rw [← hi',← hj',hm]
  have he : (M.toCoxeterSystem.reindex e).IsReduced (u.map e) :=
    (reindex_reduced _ e u).mpr hu
  have he' : (M.reindex e).toCoxeterSystem.IsReduced (u.map e) :=
    (system_reduced_iff _ _).mpr he
  rw [hM] at he'
  have hh := (Geometric.restriction_reduced_iff N (Set.range f) (u.map e)).mpr he'
  simpa only [List.map_map, e, Equiv.ofInjective_apply, Function.comp_def] using hh

end HarmonicArtin.CoxeterExchange

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Diagrams_Index
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.FiveBlock

variable {T I R : Type*} [Ring R] [Fintype T] [Fintype I]

abbrev Index (T I : Type*) := T ⊕ T ⊕ T ⊕ I ⊕ T

def differential (t r θ ι : Matrix T T R) (e : Matrix T I R)
    (d : Matrix I I R) (c : Matrix I T R) : Matrix (Index T I) (Index T I) R
  | .inl u, .inl v => -t u v
  | .inl u, .inr (.inl v) => -r u v
  | .inl u, .inr (.inr (.inl v)) => -ι u v
  | .inl u, .inr (.inr (.inr (.inl j))) => e u j
  | .inr (.inl u), .inr (.inl v) => t u v
  | .inr (.inl u), .inr (.inr (.inr (.inr v))) => ι u v
  | .inr (.inr (.inl u)), .inr (.inr (.inl v)) => t u v
  | .inr (.inr (.inl u)), .inr (.inr (.inr (.inr v))) => θ u v
  | .inr (.inr (.inr (.inl i))), .inr (.inr (.inr (.inl j))) => d i j
  | .inr (.inr (.inr (.inl i))), .inr (.inr (.inr (.inr v))) => c i v
  | .inr (.inr (.inr (.inr u))), .inr (.inr (.inr (.inr v))) => -t u v
  | _, _ => 0

def projection (e : Matrix T I R) (η : Matrix I I R) : Matrix (Index T I) I R
  | .inr (.inr (.inl u)), j => e u j
  | .inr (.inr (.inr (.inl i))), j => η i j
  | _, _ => 0

def injection (c : Matrix I T R) (η : Matrix I I R) : Matrix I (Index T I) R
  | i, .inr (.inl u) => -c i u
  | i, .inr (.inr (.inr (.inl j))) => η i j
  | _, _ => 0

def homotopy (ι : Matrix T T R) : Matrix (Index T I) (Index T I) R
  | .inr (.inr (.inl u)), .inl v => ι u v
  | .inr (.inr (.inr (.inr u))), .inr (.inl v) => -ι u v
  | _, _ => 0

def identity (ι : Matrix T T R) (η : Matrix I I R) : Matrix (Index T I) (Index T I) R
  | .inl u, .inl v => ι u v
  | .inr (.inl u), .inr (.inl v) => ι u v
  | .inr (.inr (.inl u)), .inr (.inr (.inl v)) => ι u v
  | .inr (.inr (.inr (.inl i))), .inr (.inr (.inr (.inl j))) => η i j
  | .inr (.inr (.inr (.inr u))), .inr (.inr (.inr (.inr v))) => ι u v
  | _, _ => 0

lemma contraction (t r θ ι : Matrix T T R) (e : Matrix T I R)
    (d η : Matrix I I R) (c : Matrix I T R)
    (hι : ι * ι = ι) (hη : η * η = η) (hit : ι * t = t) (hti : t * ι = t)
    (hir : ι * r = r) (hθi : θ * ι = θ) (hιe : ι * e = e) (heη : e * η = e)
    (hcι : c * ι = c) (hηc : η * c = c) (hec : e * c = r + θ) :
    projection e η * injection c η = identity ι η +
      (differential t r θ ι e d c * homotopy ι +
        homotopy ι * differential t r θ ι e d c) := by
  ext i j
  rcases i with u | u | u | i | u <;> rcases j with v | v | v | j | v
  all_goals simp only [identity, Matrix.mul_apply, Matrix.add_apply, Fintype.sum_sum_type,
    differential, homotopy, projection, injection, MulZeroClass.zero_mul, MulZeroClass.mul_zero,
    Finset.sum_const_zero, _root_.neg_mul, _root_.mul_neg, neg_neg,
    Finset.sum_neg_distrib, add_zero, zero_add, neg_zero]
  all_goals try simp only [← Matrix.mul_apply]
  all_goals simp only [hι, hη, hit, hti, hir, hθi, hιe, heη, hcι, hηc, hec,
    Matrix.add_apply, neg_add, add_neg_cancel]
  exact add_comm _ _

end HarmonicArtin.FiveBlock

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Diagrams_ReverseDifferential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.FiveBlock

variable {T I R : Type*} [Ring R] [Fintype T] [Fintype I]

def reverseDifferential (t r θ ι : Matrix T T R) (e : Matrix T I R)
    (d : Matrix I I R) (c : Matrix I T R) : Matrix (Index T I) (Index T I) R
  | .inl u, .inl v => -t u v
  | .inl u, .inr (.inl v) => θ u v
  | .inl u, .inr (.inr (.inl v)) => ι u v
  | .inl u, .inr (.inr (.inr (.inl j))) => e u j
  | .inr (.inl u), .inr (.inl v) => t u v
  | .inr (.inl u), .inr (.inr (.inr (.inr v))) => -ι u v
  | .inr (.inr (.inl u)), .inr (.inr (.inl v)) => t u v
  | .inr (.inr (.inl u)), .inr (.inr (.inr (.inr v))) => -r u v
  | .inr (.inr (.inr (.inl i))), .inr (.inr (.inr (.inl j))) => d i j
  | .inr (.inr (.inr (.inl i))), .inr (.inr (.inr (.inr v))) => c i v
  | .inr (.inr (.inr (.inr u))), .inr (.inr (.inr (.inr v))) => -t u v
  | _, _ => 0

def reverseProjection (e : Matrix T I R) (η : Matrix I I R) : Matrix (Index T I) I R
  | .inr (.inr (.inl u)), j => -e u j
  | .inr (.inr (.inr (.inl i))), j => η i j
  | _, _ => 0

def reverseInjection (c : Matrix I T R) (η : Matrix I I R) : Matrix I (Index T I) R
  | i, .inr (.inl u) => c i u
  | i, .inr (.inr (.inr (.inl j))) => η i j
  | _, _ => 0

def reverseHomotopy (ι : Matrix T T R) : Matrix (Index T I) (Index T I) R
  | .inr (.inr (.inl u)), .inl v => -ι u v
  | .inr (.inr (.inr (.inr u))), .inr (.inl v) => ι u v
  | _, _ => 0

lemma reverseContraction (t r θ ι : Matrix T T R) (e : Matrix T I R)
    (d η : Matrix I I R) (c : Matrix I T R)
    (hι : ι * ι = ι) (hη : η * η = η) (hit : ι * t = t) (hti : t * ι = t)
    (hri : r * ι = r) (hiθ : ι * θ = θ) (hιe : ι * e = e) (heη : e * η = e)
    (hcι : c * ι = c) (hηc : η * c = c) (hec : e * c = r + θ) :
    reverseProjection e η * reverseInjection c η = identity ι η +
      (reverseDifferential t r θ ι e d c * reverseHomotopy ι +
        reverseHomotopy ι * reverseDifferential t r θ ι e d c) := by
  ext i j
  rcases i with u | u | u | i | u <;> rcases j with v | v | v | j | v
  all_goals simp only [identity, Matrix.mul_apply, Matrix.add_apply, Fintype.sum_sum_type,
    reverseDifferential, reverseHomotopy, reverseProjection, reverseInjection, MulZeroClass.zero_mul, MulZeroClass.mul_zero,
    Finset.sum_const_zero, _root_.neg_mul, _root_.mul_neg, neg_neg,
    Finset.sum_neg_distrib, add_zero, zero_add, neg_zero]
  all_goals try simp only [← Matrix.mul_apply]
  all_goals simp only [hι, hη, hit, hti, hri, hiθ, hιe, heη, hcι, hηc, hec,
    Matrix.add_apply, neg_add, add_neg_cancel]
  all_goals try abel

end HarmonicArtin.FiveBlock

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Quivers_Iso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver

variable {V A W B : Type*} (Q : ReversibleQuiver V A) (R : ReversibleQuiver W B)

structure Iso where
  vertex : V ≃ W
  arrow : A ≃ B
  source : ∀ a, R.source (arrow a) = vertex (Q.source a)
  target : ∀ a, R.target (arrow a) = vertex (Q.target a)
  reverse : ∀ a, R.reverse (arrow a) = arrow (Q.reverse a)

namespace Iso
variable {Q R} (e : Iso Q R)

@[simp] lemma source_symm (b:B) : Q.source (e.arrow.symm b) = e.vertex.symm (R.source b) := by
  apply e.vertex.injective
  simpa only [Equiv.apply_symm_apply] using (e.source (e.arrow.symm b)).symm

@[simp] lemma target_symm (b:B) : Q.target (e.arrow.symm b) = e.vertex.symm (R.target b) := by
  apply e.vertex.injective
  simpa only [Equiv.apply_symm_apply] using (e.target (e.arrow.symm b)).symm

@[simp] lemma reverse_symm (b:B) : Q.reverse (e.arrow.symm b) = e.arrow.symm (R.reverse b) := by
  apply e.arrow.injective
  simpa only [Equiv.apply_symm_apply] using (e.reverse (e.arrow.symm b)).symm

variable {K : Type*} [Field K] [Fintype A] [Fintype B] [DecidableEq V] [DecidableEq W]

noncomputable def zigzagLinear : Q.Zigzag K ≃ₗ[K] R.Zigzag K where
  toFun x := (x.vertex ∘ e.vertex.symm, x.arrow ∘ e.arrow.symm, x.token ∘ e.vertex.symm)
  invFun x := (x.vertex ∘ e.vertex, x.arrow ∘ e.arrow, x.token ∘ e.vertex)
  left_inv x := by apply Zigzag.ext <;> ext y <;> simp [Function.comp_def,Zigzag.vertex,Zigzag.arrow,Zigzag.token]
  right_inv x := by apply Zigzag.ext <;> ext y <;> simp [Function.comp_def,Zigzag.vertex,Zigzag.arrow,Zigzag.token]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] lemma zigzagLinear_vertex (x : Q.Zigzag K) (v : W) :
    (e.zigzagLinear x).vertex v = x.vertex (e.vertex.symm v) := rfl
@[simp] lemma zigzagLinear_arrow (x : Q.Zigzag K) (b : B) :
    (e.zigzagLinear x).arrow b = x.arrow (e.arrow.symm b) := rfl
@[simp] lemma zigzagLinear_token (x : Q.Zigzag K) (v : W) :
    (e.zigzagLinear x).token v = x.token (e.vertex.symm v) := rfl

lemma zigzagLinear_mul (x y : Q.Zigzag K) :
    e.zigzagLinear (x*y) = e.zigzagLinear x * e.zigzagLinear y := by
  apply Zigzag.ext
  · rfl
  · ext b
    simp only [zigzagLinear_arrow,Zigzag.arrow_mul,leftScale,rightScale,
      Pi.add_apply,zigzagLinear_vertex,e.source_symm,e.target_symm]
  · ext v
    simp only [zigzagLinear_token,Zigzag.token_mul,Pi.add_apply,Pi.mul_apply,
      zigzagLinear_vertex,backtrack]
    congr 1
    rw [← e.arrow.sum_comp]
    apply Finset.sum_congr rfl
    intro a _
    simp only [e.source,zigzagLinear_arrow,e.reverse,Equiv.symm_apply_apply]
    have hh : e.vertex (Q.source a)=v ↔ Q.source a=e.vertex.symm v :=
      e.vertex.eq_symm_apply.symm
    simp only [hh]

noncomputable def zigzag : Q.Zigzag K ≃+* R.Zigzag K where
  toEquiv := e.zigzagLinear.toEquiv
  map_mul' := e.zigzagLinear_mul
  map_add' := e.zigzagLinear.map_add

lemma zigzag_vertexId (v:V) : e.zigzagLinear (Zigzag.vertexId Q (K := K) v) =
    Zigzag.vertexId R (e.vertex v) := by
  apply Zigzag.ext
  · ext w
    simp only [zigzagLinear_vertex,Zigzag.vertexId_eval]
    congr 1
    exact propext e.vertex.symm_apply_eq
  · rfl
  · rfl

lemma zigzag_homogeneous {d : ℤ} {x : Q.Zigzag K} (h : Zigzag.Homogeneous Q d x) :
    Zigzag.Homogeneous R d (e.zigzagLinear x) := by
  refine ⟨?_,?_,?_⟩
  · intro hd; ext v; simp only [zigzagLinear_vertex,h.1 hd,Pi.zero_apply]
  · intro hd; ext b; simp only [zigzagLinear_arrow,h.2.1 hd,Pi.zero_apply]
  · intro hd; ext v; simp only [zigzagLinear_token,h.2.2 hd,Pi.zero_apply]

end Iso
end HarmonicArtin.ReversibleQuiver

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Quivers_Reduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag

variable {V A K I J L : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V]

namespace BasedComplex

variable [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

structure HomotopyEquivalence (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) where
  forward : Map Q E F
  backward : Map Q F E
  sourceHomotopy : Matrix I I (Q.Zigzag K)
  targetHomotopy : Matrix J J (Q.Zigzag K)
  sourceEntries : ProjectiveEntries Q E.placement E.placement sourceHomotopy
  targetEntries : ProjectiveEntries Q F.placement F.placement targetHomotopy
  sourceDegree : MapDegree Q E.placement E.placement (-1) 0 sourceHomotopy
  targetDegree : MapDegree Q F.placement F.placement (-1) 0 targetHomotopy
  sourceEquation : forward.matrix * backward.matrix = projectiveIdentity Q E.placement +
    (E.differential * sourceHomotopy + sourceHomotopy * E.differential)
  targetEquation : backward.matrix * forward.matrix = projectiveIdentity Q F.placement +
    (F.differential * targetHomotopy + targetHomotopy * F.differential)

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Functors_Placement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Iso
open Zigzag Zigzag.BasedComplex

variable {V A W B K : Type*} {Q : ReversibleQuiver V A} {R : ReversibleQuiver W B}
  (e : Iso Q R) [Field K] [Fintype A] [Fintype B] [DecidableEq V] [DecidableEq W]
  {I J L : Type*}

def placement (p : GeneratorPlacement V) : GeneratorPlacement W :=
  ⟨e.vertex p.color,p.cochain,p.internal⟩

noncomputable def matrix (M : Matrix I J (Q.Zigzag K)) : Matrix I J (R.Zigzag K) :=
  M.map e.zigzag

@[simp] lemma matrix_apply (M : Matrix I J (Q.Zigzag K)) (i:I) (j:J) :
    e.matrix M i j = e.zigzagLinear (M i j) := rfl

@[simp] lemma matrix_zero : e.matrix (0 : Matrix I J (Q.Zigzag K)) = 0 := by
  apply Matrix.ext; intro i j; exact map_zero (e.zigzag (K := K))
@[simp] lemma matrix_add (M N : Matrix I J (Q.Zigzag K)) :
    e.matrix (M+N) = e.matrix M + e.matrix N := by
  apply Matrix.ext; intro i j; exact map_add (e.zigzag (K := K)) _ _
@[simp] lemma matrix_mul [Fintype J] (M : Matrix I J (Q.Zigzag K)) (N : Matrix J L (Q.Zigzag K)) :
    e.matrix (M*N) = e.matrix M * e.matrix N := by
  exact Matrix.map_mul (f := (e.zigzag (K := K)).toRingHom)

lemma matrix_entries {p:I → GeneratorPlacement V} {q:J → GeneratorPlacement V}
    {M : Matrix I J (Q.Zigzag K)} (h : ProjectiveEntries Q p q M) :
    ProjectiveEntries R (e.placement ∘ p) (e.placement ∘ q) (e.matrix M) := by
  constructor
  · intro i j
    change vertexId R (e.vertex (p i).color) * e.zigzagLinear (M i j) = _
    rw [← e.zigzag_vertexId,← e.zigzagLinear_mul,h.1]
    rfl
  · intro i j
    change e.zigzagLinear (M i j) * vertexId R (e.vertex (q j).color) = _
    rw [← e.zigzag_vertexId,← e.zigzagLinear_mul,h.2]
    rfl

lemma matrix_degree {p:I → GeneratorPlacement V} {q:J → GeneratorPlacement V}
    {M : Matrix I J (Q.Zigzag K)} {n v:ℤ} (h : MapDegree Q p q n v M) :
    MapDegree R (e.placement ∘ p) (e.placement ∘ q) n v (e.matrix M) := by
  intro i j
  refine ⟨?_,e.zigzag_homogeneous (h i j).2⟩
  intro hn
  change e.zigzag (M i j) = 0
  rw [(h i j).1 hn,map_zero]

@[simp] lemma matrix_identity [DecidableEq I] (p : I → GeneratorPlacement V) :
    e.matrix (projectiveIdentity Q (K := K) p) = projectiveIdentity R (e.placement ∘ p) := by
  apply Matrix.ext
  intro i j
  by_cases h:i=j
  · subst j
    simp only [matrix,Matrix.map_apply,projectiveIdentity,Matrix.diagonal_apply_eq]
    change e.zigzagLinear (vertexId Q (p i).color) = vertexId R (e.vertex (p i).color)
    exact e.zigzag_vertexId (K := K) (p i).color
  · simp [matrix,projectiveIdentity,h]

noncomputable def complex [Fintype I] (E : BasedComplex Q (K := K) I) : BasedComplex R (K := K) I where
  placement := e.placement ∘ E.placement
  differential := e.matrix E.differential
  entries := e.matrix_entries E.entries
  degree := e.matrix_degree E.degree
  square_zero := by rw [← matrix_mul,E.square_zero,matrix_zero]

noncomputable def chainMap [Fintype I] [Fintype J]
    {E : BasedComplex Q (K := K) I} {F : BasedComplex Q (K := K) J} (f : Map Q E F) :
    Map R (e.complex E) (e.complex F) where
  matrix := e.matrix f.matrix
  entries := e.matrix_entries f.entries
  degree := e.matrix_degree f.degree
  commute := by
    change e.matrix E.differential * e.matrix f.matrix = e.matrix f.matrix * e.matrix F.differential
    rw [← matrix_mul,← matrix_mul,f.commute]

noncomputable def homotopyEquivalence [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {E : BasedComplex Q (K := K) I} {F : BasedComplex Q (K := K) J} (f : HomotopyEquivalence Q E F) :
    HomotopyEquivalence R (e.complex E) (e.complex F) where
  forward := e.chainMap f.forward
  backward := e.chainMap f.backward
  sourceHomotopy := e.matrix f.sourceHomotopy
  targetHomotopy := e.matrix f.targetHomotopy
  sourceEntries := e.matrix_entries f.sourceEntries
  targetEntries := e.matrix_entries f.targetEntries
  sourceDegree := e.matrix_degree f.sourceDegree
  targetDegree := e.matrix_degree f.targetDegree
  sourceEquation := by
    change e.matrix f.forward.matrix * e.matrix f.backward.matrix = _
    rw [← matrix_mul,f.sourceEquation,matrix_add,matrix_add,matrix_mul,matrix_mul,matrix_identity]
    rfl
  targetEquation := by
    change e.matrix f.backward.matrix * e.matrix f.forward.matrix = _
    rw [← matrix_mul,f.targetEquation,matrix_add,matrix_add,matrix_mul,matrix_mul,matrix_identity]
    rfl

end HarmonicArtin.ReversibleQuiver.Iso

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Quivers_Path
attribute [-simp] _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_add _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_apply _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_identity _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_mul _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.matrix_zero _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.reverse_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.source_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.target_symm _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_arrow _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_token _root_.OAI.HarmonicArtin.ReversibleQuiver.Iso.zigzagLinear_vertex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ReversibleQuiver

abbrev Path (V A : Type*) := V ⊕ A ⊕ V

namespace Zigzag

variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]

local instance pathModule : Module K (Q.Zigzag K) :=
  inferInstanceAs (Module K ((V → K) × (A → K) × (V → K)))

def pathCoordinates : Q.Zigzag K ≃ₗ[K] (Path V A → K) where
  toFun x := Sum.elim x.vertex (Sum.elim x.arrow x.token)
  invFun f := (fun v => f (.inl v), (fun a => f (.inr (.inl a))),
    fun v => f (.inr (.inr v)))
  left_inv x := by rfl
  right_inv f := by funext p; rcases p with v | a | v <;> rfl
  map_add' x y := by funext p; rcases p with v | a | v <;> rfl
  map_smul' r x := by funext p; rcases p with v | a | v <;> rfl

@[simp] lemma pathCoordinates_vertex (x : Q.Zigzag K) (v : V) :
    pathCoordinates Q x (.inl v) = x.vertex v := rfl
@[simp] lemma pathCoordinates_arrow (x : Q.Zigzag K) (a : A) :
    pathCoordinates Q x (.inr (.inl a)) = x.arrow a := rfl
@[simp] lemma pathCoordinates_token (x : Q.Zigzag K) (v : V) :
    pathCoordinates Q x (.inr (.inr v)) = x.token v := rfl

end Zigzag
end HarmonicArtin.ReversibleQuiver

end OAI
end

section
-- module Solutions.OAIQ225_AG.StdSimplexCompat
attribute [-instance] _root_.OAI.HarmonicArtin.instPreorderLiftedCell
/-!
# Standard simplex compatibility layer for ports of openai/math

This file is not OpenAI's code. OpenAI's openai/math is built on Mathlib `d13f23b`; prove2.me's
environment is Mathlib `0df444a`. Both have the structure `Convexity.StdSimplex`, but `0df444a`
lacks part of its API (the files `Mathlib.Geometry.Convex.ConvexSpace.{Topology,
CompactSpaceStdSimplex, Barycenter, PathConnectedSpaceStdSimplex}` and some lemmas of `Defs`),
and its `SimplexCategory.toTop` takes the topological simplex to be the subtype
`stdSimplex ℝ (Fin (n+1))`, where `d13f23b` takes the structure.

Part 1 adds the missing `d13f23b` API to `Convexity.StdSimplex` under its `d13f23b` names. It is
copied from Mathlib `d13f23b` (Copyright (c) 2025 Lean FRO, LLC, authors Kim Morrison, Andrew
Yang, Yaël Dillies; Copyright (c) 2026 Joël Riou; released under the Apache 2.0 license), adapted
to `0df444a` (module keywords removed).

Part 2 (`OAI.SStd`) is ours: the subtype `stdSimplex R X` on a finite type with the `d13f23b`
names, for ported code that identifies the simplex with `SimplexCategory.toTop.obj`; there the
port rewrites `Convexity.StdSimplex` to `OAI.SStd`.
-/

noncomputable section StdSimplexCompat

universe u v w

open Topology

/-! ## Part 1: the `d13f23b` API missing from `0df444a`, on `Convexity.StdSimplex` -/

namespace Convexity

namespace StdSimplex

section Semiring

variable {R : Type u} [PartialOrder R] [Semiring R] {X Y Z : Type*}

@[simp]
lemma total_of_fintype [Fintype X] (w : StdSimplex R X) :
    ∑ i, w.weights i = 1 := by
  have := w.total
  rwa [Finsupp.sum_fintype _ _ (by simp)] at this

@[simp]
lemma total_fin_two (w : StdSimplex R (Fin 2)) :
    w.weights 0 + w.weights 1 = 1 := by
  rw [← w.total_of_fintype, Fin.sum_univ_two]

lemma range_toFun_comp_weights [Fintype X] :
    Set.range (fun t ↦ t.weights : StdSimplex R X → (X → R)) =
    (⋂ (i : X), { s | 0 ≤ s i }) ∩ { s | ∑ i, s i = 1 } := by
  ext s
  simp only [Set.mem_range, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
  refine ⟨?_, ?_⟩
  · rintro ⟨s, rfl⟩
    exact ⟨s.weights_nonneg, by simp⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨{
      weights := Finsupp.equivFunOnFinite.symm s
      nonneg m := by simpa using h₁ m
      total := by simpa [Finsupp.sum_fintype] }, by simp⟩

@[simp]
lemma weights_apply_eq_one [Subsingleton X] (s : StdSimplex R X) (m : X) :
    s.weights m = 1 := by
  rw [← s.total, Finsupp.sum_eq_single m
    (fun _ _ h ↦ (h (by subsingleton)).elim) (by simp)]

instance instSubsingleton [Subsingleton X] : Subsingleton (StdSimplex R X) where
  allEq := by
    intro a b
    ext m
    simp

variable [IsStrictOrderedRing R]

@[simp]
lemma weights_apply_le_one
    (s : StdSimplex R X) (m : X) : s.weights m ≤ 1 := by
  by_cases hm : s.weights m = 0
  · simpa only [hm] using zero_le_one' R
  · rw [← s.total, Finsupp.sum]
    exact Finset.single_le_sum (fun i _ => s.weights_nonneg i) (Finsupp.mem_support_iff.mpr hm)

instance instInhabited [Inhabited X] : Inhabited (StdSimplex R X) where
  default := .single default

instance instNonempty [Nonempty X] : Nonempty (StdSimplex R X) :=
  ⟨.single (Classical.arbitrary _)⟩

instance instUnique [Unique X] : Unique (StdSimplex R X) where
  uniq := by subsingleton

lemma map_id' : map (R := R) (id : X → X) = id := by
  funext f
  exact map_id f

lemma map_comp' (g₁ : X → Y) (g₂ : Y → Z) :
    map (R := R) (g₂ ∘ g₁) = map g₂ ∘ map g₁ := by
  funext f
  exact map_comp f g₁ g₂

end Semiring

section

variable {R' : Type*} [Ring R'] [PartialOrder R'] [IsStrictOrderedRing R']

/-- The bijection between the one dimensional standard simplex and the interval `[0, 1]`. -/
@[simps -isSimp]
def equivIcc : StdSimplex R' (Fin 2) ≃ Set.Icc (0 : R') 1 where
  toFun s := ⟨s.weights 1, s.weights_nonneg 1, s.weights_apply_le_one 1⟩
  invFun t := duple (s := 1 - t) (t := t) 0 1 (sub_nonneg.mpr t.2.2) t.2.1 (by simp)
  left_inv s := by
    ext i
    fin_cases i
    · have := s.total_fin_two
      simp
      exact (eq_sub_of_add_eq this).symm
    · simp
  right_inv t := by
    ext
    simp [Finsupp.single_apply]

attribute [local simp] equivIcc_apply_coe

@[simp]
lemma equivIcc_single_zero : equivIcc (.single (R := R') 0) = 0 := by
  ext
  simp [Finsupp.single_apply]

@[simp]
lemma equivIcc_single_one : equivIcc (.single (R := R') 1) = 1 := by
  ext
  simp

@[simp]
lemma equivIcc_symm_zero : equivIcc.symm 0 = .single (R := R') 0 :=
  equivIcc.injective (by simp)

@[simp]
lemma equivIcc_symm_one : equivIcc.symm 1 = .single (R := R') 1 :=
  equivIcc.injective (by simp)

end

section ConvexSpace

variable {R : Type u} [PartialOrder R] [Semiring R] [IsStrictOrderedRing R] {I : Type*}

@[simp]
lemma iConvexComb_single (x : StdSimplex R I) :
    x.iConvexComb single = x := by
  ext : 1
  simp [weights_iConvexComb, Finsupp.smul_single_one, Finsupp.sum_single]

end ConvexSpace

end StdSimplex

/-! ### Topology (Mathlib `d13f23b`, `Geometry/Convex/ConvexSpace/Topology.lean`) -/

namespace StdSimplex

variable (R : Type u) [PartialOrder R] [Ring R] [TopologicalSpace R]

/-- The topology on `StdSimplex R ι` that is induced by the embedding
`StdSimplex R ι → (ι → R)`. This is the correct topoplogy only when
`ι` is finite, see `StdSimplex.isEmbedding_toFun_comp_weights`. -/
abbrev topologicalSpaceInduced (ι : Type*) : TopologicalSpace (StdSimplex R ι) :=
  .induced (fun t ↦ t.weights : StdSimplex R ι → ι → R) inferInstance

namespace topologicalSpaceInduced

attribute [local instance] topologicalSpaceInduced

lemma continuous_iff {T ι : Type*} [TopologicalSpace T] (f : T → StdSimplex R ι) :
    Continuous f ↔ ∀ (i : ι), Continuous (fun t ↦ (f t).weights i) := by
  rw [continuous_induced_rng]
  exact continuous_pi_iff

@[fun_prop]
lemma continuous_weights_apply {ι : Type*} (i : ι) :
    Continuous (fun (t : StdSimplex R ι) ↦ t.weights i) :=
  (continuous_apply i).comp (by rw [continuous_iff_le_induced])

open Classical in
@[fun_prop]
lemma continuous_map_weights_apply
    [IsStrictOrderedRing R] [IsTopologicalRing R] {ι₁ ι₂ : Type*}
    [Finite ι₁] (f : ι₁ → ι₂) (i₂ : ι₂) :
    Continuous (fun t ↦ (map (R := R) f t).weights i₂) := by
  have := Fintype.ofFinite ι₁
  have (t : StdSimplex R ι₁) :
      (map (R := R) f t).weights i₂ =
        ∑ i₁ with f i₁ = i₂, t.weights i₁ := by
    rw [weights_map, Finsupp.mapDomain, Finsupp.sum_fintype _ _ (by simp),
      Finsupp.finsetSum_apply]
    simp [Finsupp.single_apply, Finset.sum_filter]
  simp only [this]
  fun_prop

lemma continuous_map [IsStrictOrderedRing R] [IsTopologicalRing R]
    {ι₁ ι₂ : Type*} [Finite ι₁] (f : ι₁ → ι₂) :
    Continuous (map (R := R) f) := by
  rw [continuous_iff]
  fun_prop

end topologicalSpaceInduced

variable [IsStrictOrderedRing R] [IsTopologicalRing R]

attribute [local instance] topologicalSpaceInduced in
/-- The topology on `StdSimplex R M`: the supremum of the coinduced topologies for the maps
`StdSimplex.map f : StdSimplex R ι → StdSimplex R M` with `ι` finite. When `M` is finite it is the
topology induced by the embedding `StdSimplex R M → (M → R)`. -/
noncomputable instance topologicalSpace (M : Type v) :
    TopologicalSpace (StdSimplex R M) :=
  ⨆ (ι : Type v) (_ : Finite ι) (f : ι → M), .coinduced (map f) inferInstance

lemma topologicalSpace_eq (M : Type v) [Finite M] :
    topologicalSpace R M = topologicalSpaceInduced _ _ := by
  refine le_antisymm ?_ ?_
  · exact iSup_le (fun ι ↦ iSup_le (fun _ ↦ iSup_le
      (fun f ↦ (topologicalSpaceInduced.continuous_map R f).coinduced_le)))
  · refine le_trans ?_ (le_iSup _ M)
    refine le_trans ?_ (le_iSup _ (by assumption))
    refine le_trans ?_ (le_iSup _ id)
    rw [map_id']
    rfl

variable {R} in
lemma continuous_iff
    {M : Type v} {T : Type*} [TopologicalSpace T] (f : StdSimplex R M → T) :
    Continuous f ↔
      ∀ (ι : Type v) [Finite ι] (g : ι → M), Continuous (f ∘ map g) := by
  rw [continuous_iSup_dom]
  refine forall_congr' (fun ι ↦ ?_)
  rw [continuous_iSup_dom]
  refine forall_congr' (fun _ ↦ ?_)
  rw [continuous_iSup_dom]
  refine forall_congr' (fun M ↦ ?_)
  rw [continuous_coinduced_dom, topologicalSpace_eq]

@[fun_prop]
lemma continuous_map {M : Type*} {N : Type v} (f : M → N) :
    Continuous (map (R := R) f) := by
  wlog h : Finite M generalizing M
  · rw [continuous_iff]
    intro ι _ g
    rw [← map_comp']
    exact this (f ∘ g) inferInstance
  have H {ι : Type v} [Finite ι] (g : ι → N) : Continuous (map (R := R) g) := by
    rw [continuous_iff_coinduced_le]
    refine le_trans ?_ (le_iSup _ ι)
    refine le_trans ?_ (le_iSup _ (by assumption))
    refine le_trans ?_ (le_iSup _ g)
    rw [topologicalSpace_eq]
  obtain ⟨ι, _, ⟨e⟩⟩ : ∃ (ι : Type v) (_ : Finite ι), Nonempty (M ≃ ι) :=
    ⟨_, inferInstance, ⟨(Finite.equivFin M).trans Equiv.ulift.{v}.symm⟩⟩
  have : Continuous (map (R := R) e) := by
    rw [topologicalSpace_eq, topologicalSpace_eq]
    apply topologicalSpaceInduced.continuous_map
  convert (H (f ∘ e.symm)).comp this
  rw [← map_comp', Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id]

open topologicalSpaceInduced in
@[fun_prop]
lemma continuous_weights_apply {M : Type*} (m : M) :
    Continuous (fun (t : StdSimplex R M) ↦ t.weights m) := by
  rw [continuous_iff]
  intro ι _ g
  rw [topologicalSpace_eq]
  exact continuous_map_weights_apply R g m

lemma isEmbedding_toFun_comp_weights (M : Type*) [Finite M] :
    IsEmbedding (fun t ↦ t.weights : StdSimplex R M → M → R) where
  eq_induced := by rw [topologicalSpace_eq]
  injective _ _ h := by ext; apply congr_fun h

lemma isClosedEmbedding_toFun_comp_weights
    [OrderClosedTopology R] (M : Type*) [Finite M] :
    IsClosedEmbedding (fun t ↦ t.weights : StdSimplex R M → M → R) where
  toIsEmbedding := isEmbedding_toFun_comp_weights R M
  isClosed_range := by
    have := Fintype.ofFinite M
    rw [range_toFun_comp_weights]
    refine IsClosed.inter (isClosed_iInter (fun _ ↦ isClosed_le ?_ ?_))
      (isClosed_eq ?_ ?_)
    all_goals fun_prop

end StdSimplex

/-! ### Compactness (Mathlib `d13f23b`, `CompactSpaceStdSimplex.lean`) -/

namespace StdSimplex

instance compactSpace (R M : Type*) [Ring R] [TopologicalSpace R] [IsTopologicalRing R]
    [PartialOrder R] [IsStrictOrderedRing R] [CompactIccSpace R] [OrderClosedTopology R]
    [Finite M] :
    CompactSpace (StdSimplex R M) where
  isCompact_univ := by
    rw [(isEmbedding_toFun_comp_weights R M).isCompact_iff, Set.image_univ]
    refine IsCompact.of_isClosed_subset (s := Set.Icc 0 1) isCompact_Icc
      (isClosedEmbedding_toFun_comp_weights R M).isClosed_range ?_
    rintro _ ⟨x, rfl⟩
    exact ⟨fun i => x.weights_nonneg i, fun i => x.weights_apply_le_one i⟩

end StdSimplex

/-! ### Barycenters (Mathlib `d13f23b`, `Barycenter.lean`) -/

namespace StdSimplex

variable {K M : Type*} [Field K] [CharZero K] [LinearOrder K] [IsStrictOrderedRing K]

/-- In the standard simplex with vertices `M`, the barycenter of a nonempty finite subset `S`. -/
@[simps -isSimp]
noncomputable def subBarycenter (S : Finset M) (hS : S.Nonempty) : StdSimplex K M where
  weights := S.sum (fun m ↦ .single m (S.card : K)⁻¹)
  nonneg := Finset.sum_nonneg (fun m _ => by
    classical
    intro i
    rw [Finsupp.single_apply]
    split_ifs
    · exact inv_nonneg.mpr (Nat.cast_nonneg _)
    · exact le_rfl)
  total := by
    rw [← Finsupp.sum_finsetSum_index (by simp) (by simp)]
    simp only [Finsupp.sum_single_index, Finset.sum_const, nsmul_eq_mul]
    exact mul_inv_cancel₀ (by exact_mod_cast (Finset.card_pos.mpr hS).ne')

@[simp]
lemma subBarycenter_singleton (m : M) :
    subBarycenter (K := K) {m} (by simp) = .single m := by
  ext
  simp [weights_subBarycenter]

end StdSimplex

/-! ### Path-connectedness (Mathlib `d13f23b`, `PathConnectedSpaceStdSimplex.lean`) -/

namespace StdSimplex

/-- The standard one-dimensional simplex is homeomorphic to the unit interval. -/
noncomputable def homeomorphI : StdSimplex ℝ (Fin 2) ≃ₜ unitInterval where
  toEquiv := equivIcc
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact continuous_weights_apply ℝ 1
  continuous_invFun := by
    rw [(isEmbedding_toFun_comp_weights ℝ (Fin 2)).continuous_iff]
    refine continuous_pi (fun i ↦ ?_)
    fin_cases i
    · simp [equivIcc, Finsupp.single_apply]
      fun_prop
    · simp [equivIcc, Finsupp.single_apply]
      fun_prop

@[local simp]
lemma homeomorphI_apply_coe (s : StdSimplex ℝ (Fin 2)) :
    (homeomorphI s).val = s.weights 1 := by
  rfl

@[simp]
lemma homeomorphI_single_zero : homeomorphI (.single 0) = 0 := by
  ext
  simp [Finsupp.single_apply]

@[simp]
lemma homeomorphI_single_one : homeomorphI (.single 1) = 1 := by
  ext
  simp

@[simp]
lemma homeomorphI_symm_zero : homeomorphI.symm 0 = .single 0 :=
  homeomorphI.injective (by simp)

@[simp]
lemma homeomorphI_symm_one : homeomorphI.symm 1 = .single 1 :=
  homeomorphI.injective (by simp)

end StdSimplex

end Convexity

/-! ## Part 2: `OAI.SStd`, the subtype `stdSimplex R X` with the `d13f23b` names -/

end StdSimplexCompat
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_EarlyDelay
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open scoped unitInterval
open Topology

attribute [local instance] Classical.propDecidable
universe u v
variable {X:Type u} {Y:Type v} [TopologicalSpace X] [T2Space X] [TopologicalSpace Y]

abbrev EarlyDelay (δ:C(X,I)) := {p:I×X // p.1≤δ p.2}

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_ConeAttachmentRel
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open scoped unitInterval

universe u v
variable {A:Type u} {L:Type v} [TopologicalSpace A] [TopologicalSpace L]

inductive ConeAttachmentRel (f:C(L,A)) : (A ⊕ (I×L))→(A ⊕ (I×L))→Prop
  | base (x:L) : ConeAttachmentRel f (.inr (0,x)) (.inl (f x))
  | apex (x y:L) : ConeAttachmentRel f (.inr (1,x)) (.inr (1,y))

abbrev ConeAttachment (f:C(L,A)) := Quot (ConeAttachmentRel f)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_BinaryProductBoundary
attribute [-instance] _root_.OAI.HarmonicArtin.instPreorderLiftedCell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.decEq Classical.propDecidable
universe u
variable {A B:Type u} [PartialOrder A] [PartialOrder B] [OrderTop A] [OrderTop B]

abbrev BinaryProductBoundary (A B:Type u) [PartialOrder A] [PartialOrder B] [OrderTop A] [OrderTop B] :=
  {x:A×B //x≠⊤}

abbrev BinaryProductBox (b:A×B) := {x:A×B //x≤b ∧ x.1≠⊤}

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_QuantumNumber
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.instPreorderLiftedCell
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin

noncomputable def quantumNumber (m : ℕ) (j : ℤ) : ℝ :=
  Real.sin ((j : ℝ) * (Real.pi / m)) / Real.sin (Real.pi / m)

lemma quantumNumber_zero (m : ℕ) : quantumNumber m 0 = 0 := by
  simp [quantumNumber]

lemma quantum_denominator_pos {m : ℕ} (hm : 2 ≤ m) :
    0 < Real.sin (Real.pi / m) := by
  apply Real.sin_pos_of_pos_of_lt_pi
  · exact div_pos Real.pi_pos (by exact_mod_cast (show 0 < m by omega))
  · exact div_lt_self Real.pi_pos (by exact_mod_cast (show 1 < m by omega))

lemma quantumNumber_end {m : ℕ} (hm : 2 ≤ m) : quantumNumber m m = 0 := by
  unfold quantumNumber
  have hn : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  rw [Int.cast_natCast, mul_div_cancel₀ Real.pi hn, Real.sin_pi, zero_div]

lemma quantumNumber_pos {m : ℕ} (hm : 2 ≤ m) {j : ℤ} (hj : 0 < j) (hjm : j < m) :
    0 < quantumNumber m j := by
  unfold quantumNumber
  apply div_pos _ (quantum_denominator_pos hm)
  apply Real.sin_pos_of_pos_of_lt_pi
  · exact mul_pos (by exact_mod_cast hj)
      (div_pos Real.pi_pos (by exact_mod_cast (show 0 < m by omega)))
  · rw [← mul_div_assoc, div_lt_iff₀ (by exact_mod_cast (show 0 < m by omega) : (0 : ℝ) < m)]
    have hh : (j : ℝ) < m := by exact_mod_cast hjm
    nlinarith [Real.pi_pos]

lemma quantumNumber_recurrence (m : ℕ) (j : ℤ) :
    quantumNumber m (j-1) + quantumNumber m (j+1) =
      (2 * Real.cos (Real.pi / m)) * quantumNumber m j := by
  unfold quantumNumber
  have hminus : ((j-1 : ℤ) : ℝ) * (Real.pi / m) = (j : ℝ) * (Real.pi / m) - (Real.pi / m) := by
    push_cast <;> ring
  have hplus : ((j+1 : ℤ) : ℝ) * (Real.pi / m) = (j : ℝ) * (Real.pi / m) + (Real.pi / m) := by
    push_cast <;> ring
  rw [hminus,hplus,Real.sin_sub,Real.sin_add]
  ring

abbrev StringLabel (m : ℕ) := Fin (m-1)

noncomputable def stringWeight (m : ℕ) (j : StringLabel m) : ℝ :=
  quantumNumber m ((j.val : ℤ)+1)

def stringMultiplicity (m : ℕ) (i j : StringLabel m) : ℕ :=
  (if i.val+1=j.val then 1 else 0) + (if j.val+1=i.val then 1 else 0)

lemma stringWeight_pos {m : ℕ} (hm : 2 ≤ m) (j : StringLabel m) :
    0 < stringWeight m j := by
  apply quantumNumber_pos hm <;> have := j.isLt <;> omega

lemma stringMultiplicity_symm (m : ℕ) (i j : StringLabel m) :
    stringMultiplicity m i j = stringMultiplicity m j i := by
  unfold stringMultiplicity
  omega

lemma stringWeight_next {m : ℕ} (hm : 2 ≤ m) (i : StringLabel m) :
    (∑ j : StringLabel m, if i.val+1=j.val then stringWeight m j else 0) =
      quantumNumber m ((i.val : ℤ)+2) := by
  classical
  by_cases hi : i.val+1 < m-1
  · let k : StringLabel m := ⟨i.val+1,hi⟩
    rw [Finset.sum_eq_single k]
    · simp only [k, ite_true, if_true, stringWeight, Nat.cast_add, Nat.cast_one]
      congr 1
    · intro j _ hj
      have hh : i.val+1 ≠ j.val := by
        intro hh
        apply hj
        apply Fin.ext
        exact hh.symm
      exact ite_eq_right hh
    · intro hh
      exact (hh (Finset.mem_univ k)).elim
  · have hend : (i.val : ℤ)+2 = m := by have := i.isLt; omega
    rw [hend, quantumNumber_end hm]
    apply Finset.sum_eq_zero
    intro j _
    apply ite_eq_right
    have := j.isLt
    omega

lemma stringWeight_previous {m : ℕ} (i : StringLabel m) :
    (∑ j : StringLabel m, if j.val+1=i.val then stringWeight m j else 0) =
      quantumNumber m i.val := by
  classical
  by_cases hi : 0 < i.val
  · let k : StringLabel m := ⟨i.val-1,by have := i.isLt; omega⟩
    rw [Finset.sum_eq_single k]
    · have hk : k.val+1=i.val := by simp only [k]; omega
      rw [ite_eq_left hk]
      unfold stringWeight
      congr 1
      omega
    · intro j _ hj
      apply ite_eq_right
      intro hh
      apply hj
      apply Fin.ext
      dsimp only [k]
      omega
    · intro hh
      exact (hh (Finset.mem_univ k)).elim
  · have hz : i.val = 0 := by omega
    rw [hz, Nat.cast_zero, quantumNumber_zero]
    apply Finset.sum_eq_zero
    intro j _
    apply ite_eq_right
    omega

lemma string_dimension_identity {m : ℕ} (hm : 2 ≤ m) (i : StringLabel m) :
    (∑ j : StringLabel m, (stringMultiplicity m i j : ℝ) * stringWeight m j) =
      (2 * Real.cos (Real.pi / m)) * stringWeight m i := by
  simp only [stringMultiplicity, Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    add_mul, ite_mul, one_mul, zero_mul, Finset.sum_add_distrib]
  rw [stringWeight_next hm, stringWeight_previous, add_comm]
  have h := quantumNumber_recurrence m ((i.val : ℤ)+1)
  have h1 : (i.val : ℤ)+1-1 = i.val := by omega
  have h2 : (i.val : ℤ)+1+1 = (i.val : ℤ)+2 := by omega
  simpa only [h1, h2, stringWeight] using h

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_FusionLabel
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin

variable {E : Type*} [Fintype E] [DecidableEq E] (m : E → ℕ)

abbrev FusionLabel := (e : E) → StringLabel (m e)

noncomputable def fusionWeight (L : FusionLabel m) : ℝ :=
  ∏ e, stringWeight (m e) (L e)

omit [DecidableEq E] in
lemma fusionWeight_pos (hm : ∀ e, 2 ≤ m e) (L : FusionLabel m) :
    0 < fusionWeight m L := by
  apply Finset.prod_pos
  intro e _
  exact stringWeight_pos (hm e) (L e)

noncomputable def factorMultiplicity (e : E) (L L' : FusionLabel m) : ℕ :=
  if ∀ f, f ≠ e → L f = L' f then stringMultiplicity (m e) (L e) (L' e) else 0

lemma factorMultiplicity_symm (e : E) (L L' : FusionLabel m) :
    factorMultiplicity m e L L' = factorMultiplicity m e L' L := by
  unfold factorMultiplicity
  have hh : (∀ f, f ≠ e → L f = L' f) ↔ (∀ f, f ≠ e → L' f = L f) := by
    constructor <;> intro h f hf <;> exact (h f hf).symm
  simp only [hh, stringMultiplicity_symm]

lemma fusionWeight_update (L : FusionLabel m) (e : E) (j : StringLabel (m e)) :
    fusionWeight m (Function.update L e j) =
      stringWeight (m e) j * ∏ f ∈ Finset.univ.erase e, stringWeight (m f) (L f) := by
  unfold fusionWeight
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ e)]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro f hf
  rw [Function.update_of_ne (Finset.mem_erase.mp hf).1]

lemma factorMultiplicity_update (L : FusionLabel m) (e : E) (j : StringLabel (m e)) :
    factorMultiplicity m e L (Function.update L e j) =
      stringMultiplicity (m e) (L e) j := by
  unfold factorMultiplicity
  have hh : ∀ f, f ≠ e → L f = Function.update L e j f := by
    intro f hf
    rw [Function.update_of_ne hf]
  rw [ite_eq_left hh, Function.update_self]

lemma factor_dimension_identity (hm : ∀ e, 2 ≤ m e) (e : E) (L : FusionLabel m) :
    (∑ L' : FusionLabel m, (factorMultiplicity m e L L' : ℝ) * fusionWeight m L') =
      (2 * Real.cos (Real.pi / m e)) * fusionWeight m L := by
  classical
  have hx : Function.Injective (Function.update L e) := by
    intro i j h
    have hh := congrFun h e
    simpa only [Function.update_self] using hh
  have hs : (∑ j : StringLabel (m e),
      (stringMultiplicity (m e) (L e) j : ℝ) * fusionWeight m (Function.update L e j)) =
      ∑ L' : FusionLabel m, (factorMultiplicity m e L L' : ℝ) * fusionWeight m L' := by
    apply Fintype.sum_of_injective (Function.update L e) hx
    · intro L' hL'
      have hh : ¬ ∀ f, f ≠ e → L f = L' f := by
        intro hh
        apply hL'
        refine ⟨L' e, ?_⟩
        funext f
        by_cases hf : f=e
        · subst f; exact Function.update_self _ _ _
        · rw [Function.update_of_ne hf]
          exact hh f hf
      simp only [factorMultiplicity, ite_eq_right hh, Nat.cast_zero, zero_mul]
    · intro j
      rw [factorMultiplicity_update]
  rw [← hs]
  simp_rw [fusionWeight_update, ← mul_assoc]
  rw [← Finset.sum_mul, string_dimension_identity (hm e)]
  rw [fusionWeight, ← Finset.mul_prod_erase _ _ (Finset.mem_univ e)]
  ring

inductive FusionEdge (E : Type*)
  | units : ℕ → FusionEdge E
  | string : E → FusionEdge E

noncomputable def FusionEdge.multiplicity (d : FusionEdge E) (L L' : FusionLabel m) : ℕ :=
  match d with
  | .units n => if L = L' then n else 0
  | .string e => factorMultiplicity m e L L'

noncomputable def FusionEdge.dimension (d : FusionEdge E) : ℝ :=
  match d with
  | .units n => n
  | .string e => 2 * Real.cos (Real.pi / m e)

lemma FusionEdge.multiplicity_symm (d : FusionEdge E) (L L' : FusionLabel m) :
    d.multiplicity m L L' = d.multiplicity m L' L := by
  cases d with
  | units n => simp only [multiplicity, eq_comm]
  | string e => exact factorMultiplicity_symm m e L L'

lemma FusionEdge.dimension_identity (hm : ∀ e, 2 ≤ m e) (d : FusionEdge E)
    (L : FusionLabel m) :
    (∑ L', (d.multiplicity m L L' : ℝ) * fusionWeight m L') =
      d.dimension m * fusionWeight m L := by
  classical
  cases d with
  | units n =>
    simp only [multiplicity, Nat.cast_ite, Nat.cast_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true, if_true, dimension]
  | string e => exact factor_dimension_identity m hm e L

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_FusionVertex
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin

variable {E V : Type*} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m : E → ℕ) (d : V → V → FusionEdge E)

abbrev FusionVertex := V × FusionLabel m

abbrev FusionQuiverArrow := Σ st : FusionVertex (V := V) m × FusionVertex (V := V) m,
  Fin ((d st.1.1 st.2.1).multiplicity m st.1.2 st.2.2)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_StringAdjacent
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin

def stringAdjacent (m : ℕ) (a b : StringLabel m) : Prop :=
  a.val+1=b.val ∨ b.val+1=a.val

instance instDecidableRelStringLabelStringAdjacent (m : ℕ) : DecidableRel (stringAdjacent m) := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_FusionRest
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver

attribute [local instance] Classical.propDecidable
variable {E V : Type} [Fintype E] [DecidableEq E] (m:E → ℕ) (e:E)

abbrev FusionRest := {f:E // f ≠ e}
abbrev restLabel (L:FusionLabel m) : FusionLabel (fun f:FusionRest e => m f) := fun f => L f

def labelSplit : FusionLabel m ≃ FusionLabel (fun f:FusionRest e => m f) × StringLabel (m e) :=
  (Equiv.piSplitAt e (fun f => StringLabel (m f))).trans (Equiv.prodComm _ _)

omit [Fintype E] in
@[simp] lemma labelSplit_apply (L:FusionLabel m) : labelSplit m e L = (restLabel m e L,L e) := rfl

omit [Fintype E] in
lemma label_eq_iff (L L':FusionLabel m) :
    L=L' ↔ restLabel m e L = restLabel m e L' ∧ L e=L' e := by
  rw [← (labelSplit m e).injective.eq_iff]
  simp only [labelSplit_apply,Prod.mk.injEq]

omit [Fintype E] [DecidableEq E] in
lemma restLabel_eq_iff (L L':FusionLabel m) :
    restLabel m e L = restLabel m e L' ↔ ∀ f, f ≠ e → L f=L' f := by
  constructor
  · intro h f hf; exact congrFun h ⟨f,hf⟩
  · intro h; funext f; exact h f f.property

noncomputable def FusionEdge.usesFactor (d:FusionEdge E) : Bool :=
  match d with
  | .units _ => false
  | .string f => decide (f=e)

noncomputable def FusionEdge.removeFactor (d:FusionEdge E) : FusionEdge (FusionRest e) :=
  match d with
  | .units n => .units n
  | .string f => if h:f=e then .units 1 else .string ⟨f,h⟩

lemma stringMultiplicity_eq_ite (n:ℕ) (a b:StringLabel n) :
    stringMultiplicity n a b = if stringAdjacent n a b then 1 else 0 := by
  by_cases h₁:a.val+1=b.val
  · have h₂ : ¬ b.val+1=a.val := by omega
    simp [stringMultiplicity,stringAdjacent,h₁,h₂]
  · by_cases h₂:b.val+1=a.val <;> simp [stringMultiplicity,stringAdjacent,h₁,h₂]

lemma factorMultiplicity_split_other (f:E) (hf:f≠e) (L L':FusionLabel m) :
    factorMultiplicity m f L L' =
      if L e=L' e then
        factorMultiplicity (fun g:FusionRest e => m g) ⟨f,hf⟩ (restLabel m e L) (restLabel m e L')
      else 0 := by
  have hh : (∀ g, g ≠ f → L g=L' g) ↔
      L e=L' e ∧ ∀ g:FusionRest e, g ≠ ⟨f,hf⟩ → L g=L' g := by
    constructor
    · intro h; refine ⟨h e hf.symm,fun g hg => h g ?_⟩
      intro hgf; exact hg (Subtype.ext hgf)
    · rintro ⟨he,h⟩ g hg
      by_cases hge:g=e
      · subst g; exact he
      · exact h ⟨g,hge⟩ (fun heq => hg (congrArg Subtype.val heq))
  unfold factorMultiplicity
  simp only [hh,restLabel]
  split_ifs <;> simp_all

lemma FusionEdge.multiplicity_split (d:FusionEdge E) (L L':FusionLabel m) :
    d.multiplicity m L L' =
      if (if d.usesFactor e then stringAdjacent (m e) (L e) (L' e) else L e=L' e) then
        (d.removeFactor e).multiplicity (fun f:FusionRest e => m f) (restLabel m e L) (restLabel m e L')
      else 0 := by
  cases d with
  | units n =>
    simp only [FusionEdge.multiplicity,FusionEdge.usesFactor,FusionEdge.removeFactor,
      Bool.false_eq_true,↓reduceIte,label_eq_iff m e]
    split_ifs <;> simp_all
  | string f =>
    by_cases hf:f=e
    · subst f
      simp only [FusionEdge.multiplicity,FusionEdge.usesFactor,FusionEdge.removeFactor,
        decide_true,↓reduceIte,factorMultiplicity,← restLabel_eq_iff m e,stringMultiplicity_eq_ite]
      split_ifs <;> rfl
    · simp only [FusionEdge.multiplicity,FusionEdge.usesFactor,FusionEdge.removeFactor,
        hf,decide_false,↓reduceIte,Bool.false_eq_true]
      exact factorMultiplicity_split_other m e f hf L L'

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_FusionFactorStep
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq
variable {E V : Type} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m:E → ℕ) (e:E) (d:V → V → FusionEdge E) (hd:∀ s t,d s t=d t s)

omit [Fintype E] in
@[simp] lemma labelSplit_symm_rest (r:FusionLabel (fun f:FusionRest e => m f)) (a:StringLabel (m e)) :
    restLabel m e ((labelSplit m e).symm (r,a)) = r :=
  congrArg Prod.fst ((labelSplit m e).apply_symm_apply (r,a))

omit [Fintype E] in
@[simp] lemma labelSplit_symm_at (r:FusionLabel (fun f:FusionRest e => m f)) (a:StringLabel (m e)) :
    ((labelSplit m e).symm (r,a)) e = a :=
  congrArg Prod.snd ((labelSplit m e).apply_symm_apply (r,a))

omit [Fintype V] [DecidableEq V] in
@[ext] lemma fusionArrow_ext {a b:FusionQuiverArrow m d}
    (hl:a.1.1=b.1.1) (hr:a.1.2=b.1.2) (hk:a.2.val=b.2.val) : a=b := by
  rcases a with ⟨⟨α,β⟩,k⟩; rcases b with ⟨⟨α',β'⟩,k'⟩
  dsimp at hl hr hk
  subst α'; subst β'
  exact congrArg (Sigma.mk (α,β)) (Fin.ext hk)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_DimensionPosMultiplicityPos
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open _root_.Matrix
open scoped _root_.Matrix BigOperators

attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable
variable {E V:Type} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m:E → ℕ) (d:V → V → FusionEdge E) (hd:∀ s t,d s t=d t s)
  (hdiag:∀ s,d s s=.units 0) (hm:∀ e,2 ≤ m e)

include hm in
lemma FusionEdge.dimension_pos_of_multiplicity_pos (b:FusionEdge E) (L H:FusionLabel m)
    (h:0<b.multiplicity m L H) : 0<b.dimension m := by
  have ht:0<(b.multiplicity m L H:ℝ)*fusionWeight m H :=
    mul_pos (Nat.cast_pos.mpr h) (fusionWeight_pos m hm H)
  have hs:=lt_of_lt_of_le ht (Finset.single_le_sum
    (fun T (_:T∈Finset.univ)=>mul_nonneg (Nat.cast_nonneg (b.multiplicity m L T)) (fusionWeight_pos m hm T).le)
    (Finset.mem_univ H))
  rw [FusionEdge.dimension_identity m hm] at hs
  exact (mul_pos_iff_of_pos_right (fusionWeight_pos m hm L)).mp hs

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_FiniteFusionEdge
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin

variable {S : Type*} [LinearOrder S]

abbrev FiniteFusionEdge (M : CoxeterMatrix S) :=
  {st : S × S // st.1 < st.2 ∧ 4 ≤ M st.1 st.2}

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_PositiveDegreeHom
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CoxeterExchange

universe u
variable {S:Type u} (M:CoxeterMatrix S)

lemma positiveDegree_relations : ∀a b:FreeMonoid S,positiveBraidRelations M a b →
    FreeMonoid.lift (fun _ : S=>Multiplicative.ofAdd (1:ℕ)) a=
      FreeMonoid.lift (fun _ : S=>Multiplicative.ofAdd (1:ℕ)) b := by
  rintro a b ⟨s,t,rfl,rfl⟩
  simp [FreeMonoid.lift_ofList,List.map_const',List.prod_replicate,length_altList]

def positiveDegreeHom : PositiveArtin M →* Multiplicative ℕ :=
  PresentedMonoid.lift (fun _=>Multiplicative.ofAdd 1) (positiveDegree_relations M)

def positiveDegree (a:PositiveArtin M) : ℕ := Multiplicative.toAdd (positiveDegreeHom M a)

@[simp] lemma positiveDegree_one : positiveDegree M 1=0 :=rfl
@[simp] lemma positiveDegree_generator (s:S) : positiveDegree M (positiveGenerator M s)=1 :=rfl
@[simp] lemma positiveDegree_mul (a b:PositiveArtin M) :
    positiveDegree M (a*b)=positiveDegree M a+positiveDegree M b := by
  unfold positiveDegree
  rw [map_mul]
  rfl
@[simp] lemma positiveDegree_word (w:List S) : positiveDegree M (wordPositive M w)=w.length := by
  induction w with
  | nil=>rfl
  | cons s w ih=>
    change positiveDegree M (positiveGenerator M s*wordPositive M w)=w.length+1
    rw [positiveDegree_mul,positiveDegree_generator,ih,Nat.add_comm]

lemma positiveToCoxeter_relations : ∀a b:FreeMonoid S,positiveBraidRelations M a b →
    FreeMonoid.lift M.toCoxeterSystem.simple a=FreeMonoid.lift M.toCoxeterSystem.simple b := by
  rintro a b ⟨s,t,rfl,rfl⟩
  simpa only [FreeMonoid.lift_ofList,CoxeterSystem.wordProd] using altList_braid M.toCoxeterSystem s t

def positiveToCoxeter : PositiveArtin M →* M.Group :=
  PresentedMonoid.lift M.toCoxeterSystem.simple (positiveToCoxeter_relations M)

@[simp] lemma positiveToCoxeter_generator (s:S) :
    positiveToCoxeter M (positiveGenerator M s)=M.toCoxeterSystem.simple s :=rfl

@[simp] lemma positiveToCoxeter_word (w:List S) :
    positiveToCoxeter M (wordPositive M w)=wordCoxeter M w := by
  induction w with
  | nil=>exact map_one _
  | cons s w ih=>
    change positiveToCoxeter M (positiveGenerator M s*wordPositive M w)=M.toCoxeterSystem.simple s*wordCoxeter M w
    rw [map_mul,positiveToCoxeter_generator,ih]

noncomputable def positiveSimpleLift (w:M.Group) : PositiveArtin M :=
  wordPositive M (reducedExpression M w)

@[simp] lemma positiveDegree_simpleLift (w:M.Group) :
    positiveDegree M (positiveSimpleLift M w)=M.toCoxeterSystem.length w := by
  rw [positiveSimpleLift,positiveDegree_word,←(reducedExpression_reduced M w).eq]
  change M.toCoxeterSystem.length (wordCoxeter M (reducedExpression M w))=_
  rw [wordCoxeter_reducedExpression]

@[simp] lemma positiveToCoxeter_simpleLift (w:M.Group) :
    positiveToCoxeter M (positiveSimpleLift M w)=w := by
  rw [positiveSimpleLift,positiveToCoxeter_word,wordCoxeter_reducedExpression]

lemma positiveSimpleLift_word [Finite S] (w:List S) (h:M.toCoxeterSystem.IsReduced w) :
    positiveSimpleLift M (wordCoxeter M w)=wordPositive M w := by
  exact wordPositive_eq_of_reduced M _ w (reducedExpression_reduced M _) h (wordCoxeter_reducedExpression M _)

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_PositivePrefix
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CoxeterExchange

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type*} (M:CoxeterMatrix S)

def PositivePrefix (a b:PositiveArtin M) : Prop := ∃c:PositiveArtin M,b=a*c

variable [Fintype S]

@[simp] lemma positiveSimpleLift_simple (s:S) : positiveSimpleLift M (M.toCoxeterSystem.simple s)=positiveGenerator M s := by
  have h:M.toCoxeterSystem.IsReduced [s]:=by
    change M.toCoxeterSystem.length (M.toCoxeterSystem.simple s)=1
    exact M.toCoxeterSystem.length_simple s
  exact positiveSimpleLift_word M [s] h

@[simp] lemma positiveSimpleLift_one : positiveSimpleLift M 1=1 := by
  have h:M.toCoxeterSystem.IsReduced []:=by
    change M.toCoxeterSystem.length 1=0
    exact M.toCoxeterSystem.length_one
  exact positiveSimpleLift_word M [] h

end HarmonicArtin

end OAI
end

section
-- module Solutions.OAIQ225_AG.ArtinGroups_Harmonic_SimpleFrontLink
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin
open CoxeterExchange

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type*} [Fintype S] (M:CoxeterMatrix S)

def SimpleFrontLink (a:PositiveArtin M) (s t:S) : Prop :=
  ∃w:M.Group,PositivePrefix M (positiveSimpleLift M w) a ∧
    PositivePrefix M (positiveGenerator M s) (positiveSimpleLift M w) ∧
    PositivePrefix M (positiveGenerator M t) (positiveSimpleLift M w)

def FrontLinked (a:PositiveArtin M) : S→S→Prop := Relation.ReflTransGen (SimpleFrontLink M a)

end HarmonicArtin

end OAI
end


