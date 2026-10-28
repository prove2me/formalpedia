-- Prove2me | Definitions.Def_OAIQ66So005
-- name    : OAIQ66So005
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T02:13:38.154389+00:00
-- url     : https://prove2.me/theorems/afc1f263-6be1-467d-90ee-629e2d0dc7fe
-- title:
--   Definitions bundle OAIQ66So005 of the split of OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SimpleFInftyOvergroups.main`, carved from OpenAI's openai/math development (OpenAI, *Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)*, OpenAI Math Release, September 23, 2026, result family 250, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 717 declarations of OpenAI's Lean: 227 definitions, 38 inductive types or structures, 21 instances and 431 theorems. The definitions and types are `OAI.CoveringMapNatural.fiberMap`, `OAI.EquivariantOrderChains.orderMap`, `OAI.EquivariantOrderChains.permutationObject`, `OAI.EquivariantOrderChains.permutationRepresentation`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Absorbs`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Base.absorption`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Canonical.candidates`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Canonical.least`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Canonical.pick`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Canonical.pickStep`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Critical`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.GoodTable`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Irreducible`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Projection.left`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Projection.right`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Quotient.Mon`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Quotient.Rel`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Quotient.monoidWithZero`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Quotient.normal`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Quotient.present`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Quotient.representative`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Search.lexBool`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Search.lexFinish`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Search.lexFoldStep`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Search.value`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Selectors.BoundedEq`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.Z`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Source.groupEval`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Static.letters`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Static.words`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Step`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Steps`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Uniform.output`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Uniform.pick`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Uniform.pickStep`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Uniform.table`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.evaluate`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.iteration`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.next`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.rootNext` and 225 more.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory, in whole or in part: `BooneHigman_ActionEnvelope`, `BooneHigman_Basic`, `BooneHigman_Contracted`, `BooneHigman_MonoidAlgebras`, `BooneHigman_PartialAffine`, `BooneHigman_WordProblem`, `FiniteCompiler_Control`, `FiniteCompiler_Effectivity`, `FiniteCompiler_Machines`, `FiniteCompiler_Normalization`, `FiniteCompiler_Paths`, `FiniteCompiler_Quotients`, `FiniteCompiler_Rewriting`, `FiniteCompiler_Selectors`, `FiniteCompiler_SelfReference`, `FiniteCompiler_Simulator`, `FiniteCompiler_Surface`, `FiniteCompiler_TapeFolding`, `FiniteCompiler_Transition`, `FiniteCompiler_UniformMachines`, `FiniteCompiler_UniformPaths`, `FiniteCompiler_Validator`, `FiniteType_EquivariantOrderChains`, `FiniteType_OrderBasedComplex`, `FiniteType_RegularCoverGeometry`, `FiniteType_SemilinearCoinvariants`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ66So012`, `OAIQ66So013`, `OAIQ66So014` and `OAIQ66So015`; the statement `OAI_AscendingHNN_regular_product_homology_vanishes`; the proof of `OAI_AscendingHNN_regular_product_homology_vanishes`.
-- source:
--   OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 250; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/ComparatorChallenges/SimpleOvergroups.lean; Apache License 2.0); definitions carved from lean/OAI/GroupTheory at commit 1581d4c

import Mathlib

section
-- module Solutions.OAIQ066_SO.BooneHigman_Contracted
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-!
Contracted monoid algebras, selectors, and the simplicity criterion.
-/


namespace FiniteAlgebraicEnvelopes.Contracted
open MonoidAlgebra
open scoped Classical
noncomputable section
variable (k H : Type*) [CommRing k] [MonoidWithZero H]

/-- The one-dimensional ideal spanned by the absorbing monoid zero. -/
def zeroSupported (f : MonoidAlgebra k H) : Prop := ∀ h : H, h ≠ 0 → f.coeff h = 0

theorem zeroSupported_iff (f : MonoidAlgebra k H) :
    zeroSupported k H f ↔ f = single 0 (f.coeff 0) := by
  classical
  constructor
  · intro h
    ext a
    by_cases ha : a=0
    · subst a; simp
    · simp [h a ha,ha]
  · intro h a ha
    rw [h]
    simp [ha]

def zeroIdeal : TwoSidedIdeal (MonoidAlgebra k H) :=
  TwoSidedIdeal.mk' {f | zeroSupported k H f}
    (by intro h hh; simp)
    (by intro f g hf hg h hh; simp [hf h hh,hg h hh])
    (by intro f hf h hh; simp [hf h hh])
    (by
      intro f g hg h hh
      rw [(zeroSupported_iff k H g).mp hg]
      exact coeff_mul_single_of_forall_mul_ne _ _ (by simpa using fun _ : H => Ne.symm hh))
    (by
      intro f g hf h hh
      rw [(zeroSupported_iff k H f).mp hf]
      exact coeff_single_mul_of_forall_mul_ne _ _ (by simpa using fun _ : H => Ne.symm hh))

abbrev Algebra := (zeroIdeal k H).ringCon.Quotient

def quotient : MonoidAlgebra k H →ₐ[k] Algebra k H := (zeroIdeal k H).ringCon.mkₐ k

theorem quotient_eq (f g : MonoidAlgebra k H) :
    quotient k H f = quotient k H g ↔ ∀ h : H, h ≠ 0 → f.coeff h = g.coeff h := by
  change (zeroIdeal k H).ringCon.toQuotient f = (zeroIdeal k H).ringCon.toQuotient g ↔ _
  rw [RingCon.eq]
  change zeroSupported k H (f-g) ↔ _
  simp only [zeroSupported,
    MonoidAlgebra.coeff_sub,Finsupp.sub_apply,sub_eq_zero]

def basis (h : H) (c : k) : Algebra k H := quotient k H (single h c)
@[simp] theorem basis_mul (h g : H) (c d : k) :
    basis k H h c * basis k H g d = basis k H (h*g) (c*d) := by
  simp [basis,← map_mul]
@[simp] theorem basis_zero (c : k) : basis k H 0 c = 0 := by
  change quotient k H (single 0 c) = quotient k H 0
  rw [quotient_eq]
  intro h hh
  simp [hh]
@[simp] theorem basis_coeff_zero (h : H) : basis k H h 0 = 0 := by simp [basis]
@[simp] theorem basis_one (c : k) : basis k H 1 c = algebraMap k (Algebra k H) c := rfl
@[simp] theorem basis_identity : basis k H 1 1 = 1 := by simp

instance instNontrivialAlgebra [Nontrivial k] [Nontrivial H] : Nontrivial (Algebra k H) := by
  apply nontrivial_of_ne (1 : Algebra k H) 0
  intro h
  have h' : quotient k H 1 = quotient k H 0 := h
  have hh := (quotient_eq k H 1 0).mp h' 1 one_ne_zero
  simp at hh

variable {k H}

/-- Coefficients at nonzero monoid elements descend unchanged to the quotient. -/
def coefficient (h : H) (hh : h ≠ 0) : Algebra k H →ₗ[k] k where
  toFun := Quotient.lift (fun f : MonoidAlgebra k H => f.coeff h) (by
    intro f g hfg
    exact (quotient_eq k H f g).mp ((zeroIdeal k H).ringCon.eq.mpr hfg) h hh)
  map_add' x y := Quotient.inductionOn₂ x y (fun f g => by
    change (f+g).coeff h = f.coeff h + g.coeff h
    simp)
  map_smul' c x := Quotient.inductionOn x (fun f => by
    change (c • f).coeff h = c • f.coeff h
    simp)

@[simp] theorem coefficient_quotient (h : H) (hh : h ≠ 0) (f : MonoidAlgebra k H) :
    coefficient h hh (quotient k H f) = f.coeff h := rfl
@[simp] theorem coefficient_basis (h : H) (hh : h ≠ 0) (g : H) (c : k) :
    coefficient h hh (basis k H g c) = if h=g then c else 0 := by
  classical
  simp [basis,Finsupp.single_apply,eq_comm]

theorem coefficient_ext {x y : Algebra k H}
    (h : ∀ a (ha : a ≠ 0), coefficient a ha x = coefficient a ha y) : x=y := by
  induction x using Quotient.inductionOn with | h f =>
    induction y using Quotient.inductionOn with | h g =>
      exact (quotient_eq k H f g).mpr h

/-- The actual basis consists precisely of the nonzero monoid elements. -/
theorem basis_linearIndependent :
    LinearIndependent k (fun h : {h : H // h ≠ 0} => basis k H h 1) := by
  classical
  rw [linearIndependent_iff']
  intro S a ha h hh
  have he := congrArg (coefficient (k:=k) h.val h.property) ha
  have eqv (g : {h : H // h ≠ 0}) : h.val=g.val ↔ h=g := Subtype.ext_iff.symm
  simpa [map_sum,coefficient_basis,eqv,hh] using he

theorem basis_spans :
    (⊤ : Submodule k (Algebra k H)) ≤
      Submodule.span k (Set.range (fun h : {h : H // h ≠ 0} => basis k H h 1)) := by
  intro x hx
  clear hx
  obtain ⟨f,rfl⟩ := (zeroIdeal k H).ringCon.mkₐ_surjective (α:=k) x
  change quotient k H f ∈ _
  induction f using MonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add]; exact Submodule.add_mem _ hf hg
  | single h r =>
    by_cases hh : h=0
    · subst h; change basis k H 0 r ∈ _; simp
    · have he : quotient k H (single h r) = r • basis k H h 1 := by
        change quotient k H (single h r) = r • quotient k H (single h 1)
        rw [← map_smul]
        congr 1
        simp
      rw [he]
      apply Submodule.smul_mem
      exact Submodule.subset_span ⟨⟨h,hh⟩,rfl⟩

def monoidBasis : Module.Basis {h : H // h ≠ 0} k (Algebra k H) :=
  Module.Basis.mk basis_linearIndependent basis_spans

@[simp] theorem monoidBasis_apply (h : {h : H // h ≠ 0}) :
    monoidBasis (k:=k) h = basis k H h 1 := Module.Basis.mk_apply _ _ h

section Lift
variable {C : Type*} [Ring C] [_root_.Algebra k C]
variable (f : MonoidAlgebra k H →ₙₐ[k] C) (hz : f (single (0:H) 1)=0)

include hz in
theorem kill_zeroSupported (x : MonoidAlgebra k H) (hx : zeroSupported k H x) : f x=0 := by
  rw [(zeroSupported_iff k H x).mp hx]
  have he : single (0:H) (x.coeff 0) = x.coeff 0 • single (0:H) (1:k) := by simp
  rw [he,map_smul,hz,smul_zero]

def lift : Algebra k H →ₙₐ[k] C where
  toFun := Quotient.lift f (by
    intro x y hxy
    apply sub_eq_zero.mp
    rw [← map_sub]
    apply kill_zeroSupported f hz
    exact hxy)
  map_zero' := map_zero f
  map_add' x y := Quotient.inductionOn₂ x y (fun a b => map_add f a b)
  map_mul' x y := Quotient.inductionOn₂ x y (fun a b => map_mul f a b)
  map_smul' c x := Quotient.inductionOn x (fun a => map_smul f c a)

@[simp] theorem lift_quotient (x : MonoidAlgebra k H) :
    lift f hz (quotient k H x) = f x := rfl
end Lift

section Embedded
variable {J : Type*} [MonoidWithZero J]
variable (c : H →ₙ* J)

/-- The shift by c(0), essential because c need not preserve either 0 or 1. -/
def shifted : H →ₙ* Algebra k J where
  toFun h := basis k J (c h) 1 - basis k J (c 0) 1
  map_mul' h g := by
    simp only [sub_mul,mul_sub,basis_mul,one_mul,← map_mul,mul_zero,zero_mul]
    abel

def shiftedLift : MonoidAlgebra k H →ₙₐ[k] Algebra k J := MonoidAlgebra.liftMagma k (shifted (k:=k) c)

@[simp] theorem shiftedLift_single (h : H) (r : k) :
    shiftedLift (k:=k) c (single h r) = r • (basis k J (c h) 1 - basis k J (c 0) 1) := by
  simp [shiftedLift,MonoidAlgebra.liftMagma,shifted,smul_sub]

def embedding : Algebra k H →ₙₐ[k] Algebra k J :=
  lift (shiftedLift (k:=k) c) (by simp)

@[simp] theorem embedding_basis (h : H) (r : k) :
    embedding (k:=k) c (basis k H h r) = r • (basis k J (c h) 1 - basis k J (c 0) 1) := by
  simp [embedding,basis]

end Embedded

/-- Zero-preserving unital monoid maps induce unital maps of contracted algebras. -/
def map {J : Type*} [MonoidWithZero J] (c : H →*₀ J) : Algebra k H →ₐ[k] Algebra k J :=
  { embedding (k:=k) c.toMulHom with
    map_one' := by
      change embedding (k:=k) c.toMulHom 1 = 1
      rw [← basis_identity k H,embedding_basis]
      simp
    commutes' r := by
      change embedding (k:=k) c.toMulHom (algebraMap k (Algebra k H) r) = _
      rw [← basis_one k H r,embedding_basis]
      simp [Algebra.algebraMap_eq_smul_one] }

@[simp] theorem map_basis {J : Type*} [MonoidWithZero J] (c : H →*₀ J) (h : H) (r : k) :
    map (k:=k) c (basis k H h r) = basis k J (c h) r := by
  change embedding c.toMulHom (basis k H h r) = _
  rw [embedding_basis]
  change r • (basis k J (c h) 1 - basis k J (c 0) 1) = _
  rw [c.map_zero, basis_zero, sub_zero]
  change r • quotient k J (single (c h) 1) = quotient k J (single (c h) r)
  rw [← map_smul]
  congr 1
  simp


end
end FiniteAlgebraicEnvelopes.Contracted


/- Finite weak components and bounded normalization for the finite compiler. -/

end OAI
end

section
-- module Solutions.OAIQ066_SO.BooneHigman_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Finite signed words, computable word problem, simple embeddings, and action-envelope predicates.
-/

namespace FiniteAlgebraicEnvelopes

universe u

/-- Finite signed words, with `true` denoting a generator and `false` its inverse. -/
abbrev Word (n : ℕ) := List (Fin n × Bool)

/-- Evaluation in the specified finite generating family. -/
def evalWord {G : Type u} [Group G] {n : ℕ} (s : Fin n → G) (w : Word n) : G :=
  (w.map fun a => if a.2 then s a.1 else (s a.1)⁻¹).prod

end FiniteAlgebraicEnvelopes

end OAI
end

section
-- module Solutions.OAIQ066_SO.BooneHigman_WordProblem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Effective finite presentations, decidable word problem in simple groups, and the reverse implication.
-/

namespace FiniteAlgebraicEnvelopes

universe u

namespace WordProblem

open Primrec

theorem evalWord_eq_lift {H : Type*} [Group H] {n} (s : Fin n → H) (w : Word n) :
    evalWord s w = FreeGroup.lift s (FreeGroup.mk w) := by
  simp only [evalWord, FreeGroup.lift_mk]
  congr 1
  apply List.map_congr_left
  intro a _
  cases a.2 <;> rfl

theorem evalWord_append {H : Type*} [Group H] {n} (s : Fin n → H) (v w : Word n) :
    evalWord s (v ++ w) = evalWord s v * evalWord s w := by
  simp only [evalWord, List.map_append, List.prod_append]

end WordProblem

end FiniteAlgebraicEnvelopes

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteCompiler_Transition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Finite weak transition components and finite-scan instruction semantics.
-/

namespace FiniteAlgebraicEnvelopes.Compiler
open Relation

variable {α : Type*} {r : α → α → Prop}

/-- An internal terminal configuration has no forward transition. -/
def Terminal (r : α → α → Prop) (a : α) : Prop := ∀ b, ¬ r a b

/-- Determinism makes forward-reachability joins an equivalence relation. -/
theorem deterministic_join (hr : Relator.RightUnique r) :
    Equivalence (Join (ReflTransGen r)) := by
  apply equivalence_join_reflTransGen
  intro a b c hab hac
  have hbc := hr hab hac
  subst c
  exact ⟨b, .refl, .refl⟩

/-- Undirected internal connectivity may be converted to a common forward
    descendant; no reversibility of the simulated machine is required. -/
theorem weak_component_joins (hr : Relator.RightUnique r) {a b : α}
    (h : EqvGen r a b) : Join (ReflTransGen r) a b := by
  let : IsEquiv α (Join (ReflTransGen r)) := (deterministic_join hr).isEquiv
  exact EqvGen.eqvGen_le (fun _ y hxy => ⟨y, .single hxy, .refl⟩) _ _ h

theorem terminal_eq_of_reaches {a b : α} (ha : Terminal r a)
    (hab : ReflTransGen r a b) : a=b := by
  rcases hab.cases_head with h | ⟨c, hac, _⟩
  · exact h
  · exact False.elim (ha c hac)

/-- Every configuration in a terminal's weak component reaches that terminal.
    This is the graph-theoretic core of source Lemma compiler-components,
    and holds even without the finite-component assumption. -/
theorem reaches_terminal (hr : Relator.RightUnique r) {a b : α}
    (hb : Terminal r b) (hab : EqvGen r a b) : ReflTransGen r a b := by
  obtain ⟨c, hac, hbc⟩ := weak_component_joins hr hab
  have h := terminal_eq_of_reaches hb hbc
  exact h ▸ hac

/-- In particular there cannot be two successful terminal sectors in the same
    weak component, even with arbitrary reverse branching on dirty data. -/
theorem terminal_unique (hr : Relator.RightUnique r) {a b : α}
    (ha : Terminal r a) (hb : Terminal r b) (hab : EqvGen r a b) : a=b :=
  terminal_eq_of_reaches ha (reaches_terminal hr hb hab)

section FiniteSearch
variable [Fintype α] [DecidableEq α] (r : α → α → Prop) [DecidableRel r]

/-- One effective expansion by undirected internal edges. -/
def expand (s : Finset α) : Finset α :=
  s ∪ Finset.univ.filter (fun b => ∃ a ∈ s, r a b ∨ r b a)

@[simp] theorem mem_expand (s : Finset α) (b : α) :
    b ∈ expand r s ↔ b ∈ s ∨ ∃ a ∈ s, r a b ∨ r b a := by
  simp [expand]

theorem subset_expand (s : Finset α) : s ⊆ expand r s :=
  fun _ h => (mem_expand r _ _).mpr (Or.inl h)

/-- This finite algorithm never calls the simulated partial function. -/
def search (a : α) : ℕ → Finset α
  | 0 => {a}
  | n+1 => expand r (search a n)

theorem search_mono (a : α) : Monotone (search r a) := by
  apply monotone_nat_of_le_succ
  intro n
  exact subset_expand r _

theorem search_stabilizes (a : α) :
    search r a (Fintype.card α + 1) = search r a (Fintype.card α) := by
  have hs : ∀ n, (search r a n).card ≤ Fintype.card α :=
    fun _ => Finset.card_le_univ _
  have hm : Monotone (fun n => (search r a n).card) :=
    fun _ _ h => Finset.card_le_card (search_mono r a h)
  have hstep : ∀ n, (search r a n).card = (search r a (n+1)).card →
      (search r a (n+1)).card = (search r a (n+2)).card := by
    intro n hn
    have he : search r a n = search r a (n+1) :=
      Finset.eq_of_subset_of_card_le (search_mono r a (Nat.le_succ n)) hn.ge
    exact congrArg Finset.card (congrArg (expand r) he)
  exact (Finset.eq_of_subset_of_card_le
    (search_mono r a (Nat.le_succ (Fintype.card α)))
    (Nat.stabilises_of_monotone hm hs hstep (Nat.le_succ _)).le).symm

/-- Entire weak component, computed by at most the known number of vertices
    many finite expansions. Unlike running the machine, this always terminates. -/
def component (a : α) : Finset α := search r a (Fintype.card α)

theorem self_mem_component (a : α) : a ∈ component r a :=
  search_mono r a (Nat.zero_le _) (by simp [search])

theorem component_saturated (a b c : α) (hb : b ∈ component r a)
    (hbc : r b c ∨ r c b) : c ∈ component r a := by
  have h := (mem_expand r (component r a) c).mpr (Or.inr ⟨b, hb, hbc⟩)
  change c ∈ search r a (Fintype.card α + 1) at h
  rw [search_stabilizes] at h
  exact h

theorem mem_search_connected (a b : α) (n : ℕ) (h : b ∈ search r a n) :
    EqvGen r a b := by
  induction n generalizing b with
  | zero =>
    have : b=a := by simpa [search] using h
    subst b
    exact .refl a
  | succ n ih =>
    rcases (mem_expand r (search r a n) b).mp h with h | ⟨c, hc, hcb⟩
    · exact ih b h
    · refine EqvGen.trans _ _ _ (ih c hc) ?_
      rcases hcb with h | h
      · exact .rel _ _ h
      · exact .symm _ _ (.rel _ _ h)

/-- Exactness of the finite component search on malformed as well as genuine
    configurations. -/
theorem mem_component_iff (a b : α) : b ∈ component r a ↔ EqvGen r a b := by
  constructor
  · exact mem_search_connected r a b _
  · intro h
    have h' : ReflTransGen (SymmGen r) a b := by
      rw [EqvGen.reflTransGen_symmGen]
      exact h
    clear h
    induction h' with
    | refl => exact self_mem_component r a
    | @tail b c _ hbc ih => exact component_saturated r a b c ih hbc

end FiniteSearch

/- The actual finite-scan instruction semantics of the finite compiler.
   The immutable bases are not part of what an instruction may update. -/
inductive Base (S : Type*)
  | anchor : S → Base S
  | cutC : Base S
  | cutD : Base S
  | workspace : Base S
  deriving DecidableEq, Fintype

structure Tag (S Γ : Type*) where
  anchorRead : Bool
  workspaceFilled : Bool
  work : Γ
  outputRead : Bool
  output : Option S
  deriving DecidableEq, Fintype

/-- The same clean tag is used on every base, including its unused fields. -/
def clean {S Γ : Type*} (blank : Γ) : Tag S Γ :=
  ⟨false, false, blank, false, none⟩

inductive Direction
  | left | right
  deriving DecidableEq

instance instFintypeDirection : Fintype Direction := ⟨{.left, .right}, by intro x; cases x <;> simp⟩

structure Instruction (Head Tag : Type*) where
  head : Head
  tag : Tag
  cross : Bool
  deriving DecidableEq, Fintype

/-- Each state designates one reading side. A cell test has at most one result;
    boundary tests only change the state. A failed (or absent-boundary) test
    has no result. This is exactly the source's disjoint-case convention. -/
structure Table (Head Base Tag : Type*) where
  direction : Head → Direction
  cell : Head → Base → Tag → Option (Instruction Head Tag)
  boundary : Head → Option Head

end FiniteAlgebraicEnvelopes.Compiler

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteCompiler_Validator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Finite tape validation, scan reversal, and bounded cleanup.
-/

namespace FiniteAlgebraicEnvelopes.Compiler.Validator

section
open Relation

/-- The validator states I,J,J',N,V and its fresh machine handoff. -/
inductive Head
  | initial | left | right | workspace | suffix | start
  deriving DecidableEq

/-- A cell includes every tag field, even unused ones. -/
abbrev Cell (S Γ : Type*) := Base S × Tag S Γ

def cell {S Γ : Type*} (blank : Γ) (base : Base S) : Cell S Γ :=
  (base, clean blank)

/-- A headed sector in zipper notation. The left list is in reverse order,
    so its head is exactly the cell adjacent to the validator. -/
structure Sector (S Γ : Type*) where
  head : Head
  left : List (Cell S Γ)
  right : List (Cell S Γ)
  leftBoundary : Bool
  rightBoundary : Bool
  deriving DecidableEq

/-- Literal internal equations compiler-validation, oriented as in the source.
    There is no entry from P and no transition from the machine back here. -/
inductive Step {S Γ : Type*} (blank : Γ) : Sector S Γ → Sector S Γ → Prop
  | initial_workspace (l r : List (Cell S Γ)) (lb rb : Bool) :
      Step blank ⟨.initial, cell blank .workspace :: l, r, lb, rb⟩
        ⟨.initial, l, cell blank .workspace :: r, lb, rb⟩
  | initial_cut (l r : List (Cell S Γ)) (lb rb : Bool) :
      Step blank ⟨.initial, cell blank .cutC :: l, r, lb, rb⟩
        ⟨.left, l, cell blank .cutC :: r, lb, rb⟩
  | left_anchor (a : S) (l r : List (Cell S Γ)) (lb rb : Bool) :
      Step blank ⟨.left, cell blank (.anchor a) :: l, r, lb, rb⟩
        ⟨.left, l, cell blank (.anchor a) :: r, lb, rb⟩
  | left_boundary (r : List (Cell S Γ)) (rb : Bool) :
      Step blank ⟨.left, [], r, true, rb⟩ ⟨.right, [], r, true, rb⟩
  | right_anchor (a : S) (l r : List (Cell S Γ)) (lb rb : Bool) :
      Step blank ⟨.right, l, cell blank (.anchor a) :: r, lb, rb⟩
        ⟨.right, cell blank (.anchor a) :: l, r, lb, rb⟩
  | right_cut (l r : List (Cell S Γ)) (lb rb : Bool) :
      Step blank ⟨.right, l, cell blank .cutC :: r, lb, rb⟩
        ⟨.workspace, cell blank .cutC :: l, r, lb, rb⟩
  | workspace (l r : List (Cell S Γ)) (lb rb : Bool) :
      Step blank ⟨.workspace, l, cell blank .workspace :: r, lb, rb⟩
        ⟨.workspace, cell blank .workspace :: l, r, lb, rb⟩
  | workspace_cut (l r : List (Cell S Γ)) (lb rb : Bool) :
      Step blank ⟨.workspace, l, cell blank .cutD :: r, lb, rb⟩
        ⟨.suffix, cell blank .cutD :: l, r, lb, rb⟩
  | suffix_anchor (a : S) (l r : List (Cell S Γ)) (lb rb : Bool) :
      Step blank ⟨.suffix, l, cell blank (.anchor a) :: r, lb, rb⟩
        ⟨.suffix, cell blank (.anchor a) :: l, r, lb, rb⟩
  | suffix_boundary (l : List (Cell S Γ)) (lb : Bool) :
      Step blank ⟨.suffix, l, [], lb, true⟩ ⟨.start, l, [], lb, true⟩

theorem step_deterministic {S Γ : Type*} (blank : Γ) :
    Relator.RightUnique (@Step S Γ blank) := by
  intro a b c hab hac
  cases hab <;> cases hac <;> rfl

/-- Validator reverse determinism, not asserted for machine phases. -/
theorem step_leftUnique {S Γ : Type*} (blank : Γ) :
    Relator.LeftUnique (@Step S Γ blank) := by
  intro a b c hac hbc
  cases hac <;> cases hbc <;> rfl

/-- An entry has clean D immediately right of its I head. -/
def Entry {S Γ : Type*} (blank : Γ) (s : Sector S Γ) : Prop :=
  s.head = .initial ∧ ∃ r, s.right = cell blank .cutD :: r

theorem entry_no_predecessor {S Γ : Type*} (blank : Γ) {a b : Sector S Γ}
    (hb : Entry blank b) : ¬ Step blank a b := by
  rintro h
  rcases hb with ⟨hh, r, hr⟩
  cases h <;> simp_all [cell]

/-- Ordered cells and both flags are preserved by every internal validator step. -/
def skeleton {S Γ : Type*} (s : Sector S Γ) :
    List (Cell S Γ) × Bool × Bool :=
  (s.left.reverse ++ s.right, s.leftBoundary, s.rightBoundary)

theorem step_skeleton {S Γ : Type*} (blank : Γ) {a b : Sector S Γ}
    (hab : Step blank a b) : skeleton a = skeleton b := by
  cases hab <;> simp [skeleton, List.reverse_cons, List.append_assoc]

open Relation
variable {S Γ : Type*} (blank : Γ)

/-- Exact clean-anchor language; dirty tags are not accepted. -/
inductive Anchors : List (Cell S Γ) → Prop
  | nil : Anchors []
  | cons (a : S) {l} : Anchors l → Anchors (cell blank (.anchor a) :: l)

/-- The right suffix tested from N: clean workspace, D, then clean anchors. -/
inductive Tail : List (Cell S Γ) → Prop
  | cut {l} : Anchors blank l → Tail (cell blank .cutD :: l)
  | work {l} : Tail l → Tail (cell blank .workspace :: l)

/-- The right suffix tested from J': anchors, C, workspace, D, anchors. -/
inductive Body : List (Cell S Γ) → Prop
  | cut {l} : Tail blank l → Body (cell blank .cutC :: l)
  | anchor (a : S) {l} : Body l → Body (cell blank (.anchor a) :: l)

/-- The reversed left side tested from I: workspace, C, then anchors. -/
inductive Left : List (Cell S Γ) → Prop
  | cut {l} : Anchors blank l → Left (cell blank .cutC :: l)
  | work {l} : Left l → Left (cell blank .workspace :: l)

/-- Necessary future checks at each phase. Already-scanned cells need not be
    constrained: backwards propagation recovers exactly the checks made. -/
def Ready (s : Sector S Γ) : Prop :=
  match s.head with
  | .initial => s.leftBoundary = true ∧ s.rightBoundary = true ∧
      Left blank s.left ∧ Tail blank s.right
  | .left => s.leftBoundary = true ∧ s.rightBoundary = true ∧
      Anchors blank s.left ∧ Body blank s.right
  | .right => s.rightBoundary = true ∧ Body blank s.right
  | .workspace => s.rightBoundary = true ∧ Tail blank s.right
  | .suffix => s.rightBoundary = true ∧ Anchors blank s.right
  | .start => True

theorem ready_predecessor {a b : Sector S Γ} (h : Step blank a b) :
    Ready blank b → Ready blank a := by
  cases h with
  | initial_workspace l r lb rb =>
      rintro ⟨hl, hr, hleft, hright⟩
      refine ⟨hl, hr, .work hleft, ?_⟩
      cases hright with | work h => exact h
  | initial_cut l r lb rb =>
      rintro ⟨hl, hr, hleft, hright⟩
      refine ⟨hl, hr, .cut hleft, ?_⟩
      cases hright with | cut h => exact h
  | left_anchor c l r lb rb =>
      rintro ⟨hl, hr, hleft, hright⟩
      refine ⟨hl, hr, .cons c hleft, ?_⟩
      cases hright with | anchor _ h => exact h
  | left_boundary r rb =>
      rintro ⟨hr, hright⟩
      exact ⟨rfl, hr, .nil, hright⟩
  | right_anchor c l r lb rb =>
      rintro ⟨hr, hright⟩
      exact ⟨hr, .anchor c hright⟩
  | right_cut l r lb rb =>
      rintro ⟨hr, hright⟩
      exact ⟨hr, .cut hright⟩
  | workspace l r lb rb =>
      rintro ⟨hr, hright⟩
      exact ⟨hr, .work hright⟩
  | workspace_cut l r lb rb =>
      rintro ⟨hr, hright⟩
      exact ⟨hr, .cut hright⟩
  | suffix_anchor c l r lb rb =>
      rintro ⟨hr, hright⟩
      exact ⟨hr, .cons c hright⟩
  | suffix_boundary l lb =>
      intro _
      exact ⟨rfl, .nil⟩

theorem reaches_ready {a b : Sector S Γ} (h : ReflTransGen (Step blank) a b) :
    Ready blank b → Ready blank a := by
  induction h with
  | refl => exact id
  | tail _ h ih => exact fun hb => ih (ready_predecessor blank h hb)

theorem anchors_iff (l : List (Cell S Γ)) :
    Anchors blank l ↔ ∃ x : List S, l = x.map (fun a => cell blank (.anchor a)) := by
  constructor
  · intro h
    induction h with
    | nil => exact ⟨[], rfl⟩
    | cons a _ ih =>
        obtain ⟨x, rfl⟩ := ih
        exact ⟨a :: x, rfl⟩
  · rintro ⟨x, rfl⟩
    induction x with
    | nil => exact .nil
    | cons a x ih => exact .cons a ih

theorem left_iff (l : List (Cell S Γ)) :
    Left blank l ↔ ∃ (s : ℕ) (x : List S),
      l = List.replicate s (cell blank .workspace) ++
        cell blank .cutC :: x.map (fun a => cell blank (.anchor a)) := by
  constructor
  · intro h
    induction h with
    | cut h =>
        obtain ⟨x, rfl⟩ := (anchors_iff blank _).mp h
        exact ⟨0, x, rfl⟩
    | work _ ih =>
        obtain ⟨s, x, rfl⟩ := ih
        exact ⟨s+1, x, by simp [List.replicate_succ]⟩
  · rintro ⟨s, x, rfl⟩
    induction s with
    | zero => exact .cut ((anchors_iff blank _).mpr ⟨x, rfl⟩)
    | succ s ih => simpa [List.replicate_succ] using Left.work ih

/-- Every entry which reaches handoff has the FULL clean form in the manuscript:
    both boundaries, all clean tags, anchors on each side, and one quota.
    In particular this is not a cleanliness assumption on the input. -/
theorem passing_entry {a b : Sector S Γ} (ha : Entry blank a)
    (hab : ReflTransGen (Step blank) a b) (hb : b.head = .start) :
    ∃ (x y : List S) (s : ℕ), a =
      ⟨.initial, List.replicate s (cell blank .workspace) ++
        cell blank .cutC :: (x.map (fun c => cell blank (.anchor c))).reverse,
        cell blank .cutD :: y.map (fun c => cell blank (.anchor c)), true, true⟩ := by
  have hready : Ready blank a := reaches_ready blank hab (by simp [Ready, hb])
  rcases a with ⟨head, l, r, lb, rb⟩
  rcases ha with ⟨rfl, r', rfl⟩
  rcases hready with ⟨rfl, rfl, hl, hr⟩
  obtain ⟨s, x, rfl⟩ := (left_iff blank _).mp hl
  cases hr with
  | cut h =>
      obtain ⟨y, rfl⟩ := (anchors_iff blank _).mp h
      exact ⟨x.reverse, y, s, by simp⟩

end

open Relation
variable {S Γ : Type*} (blank : Γ)

theorem initial_workspaces (s : ℕ) (l r : List (Cell S Γ)) (lb rb : Bool) :
    ReflTransGen (Step blank)
      ⟨.initial, List.replicate s (cell blank .workspace) ++ l, r, lb, rb⟩
      ⟨.initial, l, List.replicate s (cell blank .workspace) ++ r, lb, rb⟩ := by
  induction s generalizing r with
  | zero => exact .refl
  | succ s ih =>
      simp only [List.replicate_succ, List.cons_append]
      refine (ReflTransGen.single (Step.initial_workspace _ _ _ _)).trans ?_
      convert ih (cell blank .workspace :: r) using 1
      all_goals try with_reducible_and_instances rfl
      simp only [← List.cons_append, ← List.replicate_succ, List.replicate_succ']
      simp only [List.append_assoc, List.cons_append, List.nil_append]

theorem left_anchors (x : List S) (l r : List (Cell S Γ)) (lb rb : Bool) :
    ReflTransGen (Step blank)
      ⟨.left, x.map (fun a => cell blank (.anchor a)) ++ l, r, lb, rb⟩
      ⟨.left, l, (x.map (fun a => cell blank (.anchor a))).reverse ++ r, lb, rb⟩ := by
  induction x generalizing r with
  | nil => exact .refl
  | cons a x ih =>
      refine (ReflTransGen.single (Step.left_anchor a _ _ _ _)).trans ?_
      simpa [List.reverse_cons, List.append_assoc] using
        ih (cell blank (.anchor a) :: r)

theorem right_anchors (x : List S) (l r : List (Cell S Γ)) (lb rb : Bool) :
    ReflTransGen (Step blank)
      ⟨.right, l, x.map (fun a => cell blank (.anchor a)) ++ r, lb, rb⟩
      ⟨.right, (x.map (fun a => cell blank (.anchor a))).reverse ++ l, r, lb, rb⟩ := by
  induction x generalizing l with
  | nil => exact .refl
  | cons a x ih =>
      refine (ReflTransGen.single (Step.right_anchor a _ _ _ _)).trans ?_
      simpa [List.reverse_cons, List.append_assoc] using
        ih (cell blank (.anchor a) :: l)

theorem workspace_many (s : ℕ) (l r : List (Cell S Γ)) (lb rb : Bool) :
    ReflTransGen (Step blank)
      ⟨.workspace, l, List.replicate s (cell blank .workspace) ++ r, lb, rb⟩
      ⟨.workspace, List.replicate s (cell blank .workspace) ++ l, r, lb, rb⟩ := by
  induction s generalizing l with
  | zero => exact .refl
  | succ s ih =>
      simp only [List.replicate_succ, List.cons_append]
      refine (ReflTransGen.single (Step.workspace _ _ _ _)).trans ?_
      convert ih (cell blank .workspace :: l) using 1
      all_goals try with_reducible_and_instances rfl
      simp only [← List.cons_append, ← List.replicate_succ, List.replicate_succ']
      simp only [List.append_assoc, List.cons_append, List.nil_append]

theorem suffix_anchors (x : List S) (l r : List (Cell S Γ)) (lb rb : Bool) :
    ReflTransGen (Step blank)
      ⟨.suffix, l, x.map (fun a => cell blank (.anchor a)) ++ r, lb, rb⟩
      ⟨.suffix, (x.map (fun a => cell blank (.anchor a))).reverse ++ l, r, lb, rb⟩ := by
  induction x generalizing l with
  | nil => exact .refl
  | cons a x ih =>
      refine (ReflTransGen.single (Step.suffix_anchor a _ _ _ _)).trans ?_
      simpa [List.reverse_cons, List.append_assoc] using
        ih (cell blank (.anchor a) :: l)

/-- Conversely every full clean entry passes the validator, with all cells
    left of the head at the handoff to the simulated program. -/
theorem clean_entry_reaches (x y : List S) (s : ℕ) :
    ReflTransGen (Step blank)
      ⟨.initial, List.replicate s (cell blank .workspace) ++
        cell blank .cutC :: (x.map (fun a => cell blank (.anchor a))).reverse,
        cell blank .cutD :: y.map (fun a => cell blank (.anchor a)), true, true⟩
      ⟨.start, (y.map (fun a => cell blank (.anchor a))).reverse ++
        cell blank .cutD :: (List.replicate s (cell blank .workspace) ++
        cell blank .cutC :: (x.map (fun a => cell blank (.anchor a))).reverse),
        [], true, true⟩ := by
  refine (initial_workspaces blank s _ _ true true).trans ?_
  refine (ReflTransGen.single (Step.initial_cut _ _ _ _)).trans ?_
  have hx := left_anchors blank x.reverse []
    (cell blank .cutC :: (List.replicate s (cell blank .workspace) ++
      cell blank .cutD :: y.map (fun a => cell blank (.anchor a)))) true true
  simp only [List.map_reverse, List.append_nil, List.reverse_reverse] at hx
  refine hx.trans ?_
  refine (ReflTransGen.single (Step.left_boundary _ _)).trans ?_
  refine (right_anchors blank x [] _ true true).trans ?_
  simp only [List.append_nil]
  refine (ReflTransGen.single (Step.right_cut _ _ _ _)).trans ?_
  refine (workspace_many blank s _ _ true true).trans ?_
  refine (ReflTransGen.single (Step.workspace_cut _ _ _ _)).trans ?_
  have hy := suffix_anchors blank y
    (cell blank .cutD :: (List.replicate s (cell blank .workspace) ++
      cell blank .cutC :: (x.map (fun a => cell blank (.anchor a))).reverse)) [] true true
  simp only [List.append_nil] at hy
  refine hy.trans ?_
  simpa using ReflTransGen.single (Step.suffix_boundary _ true)

end FiniteAlgebraicEnvelopes.Compiler.Validator

namespace FiniteAlgebraicEnvelopes.Compiler
open Relation
variable {α : Type*} {r : α → α → Prop}

/-- A source vertex cannot be reached from a different vertex. -/
theorem source_eq_of_reaches {a b : α} (hb : ∀ c, ¬ r c b)
    (hab : ReflTransGen r a b) : a = b := by
  rcases hab.cases_tail with h | ⟨c, _, hcb⟩
  · exact h.symm
  · exact False.elim (hb c hcb)

/-- In a reverse-deterministic graph, two sources reaching the same vertex agree. -/
theorem sources_unique_of_join (hr : Relator.LeftUnique r) {a b c : α}
    (ha : ∀ x, ¬ r x a) (hb : ∀ x, ¬ r x b)
    (hac : ReflTransGen r a c) (hbc : ReflTransGen r b c) : a = b := by
  induction hac with
  | refl => exact (source_eq_of_reaches ha hbc).symm
  | @tail c d hac hcd ih =>
      rcases hbc.cases_tail with h | ⟨x, hbx, hxd⟩
      · subst d
        exact False.elim (hb c hcd)
      · have hxc : c = x := hr hcd hxd
        subst x
        exact ih hbx

end FiniteAlgebraicEnvelopes.Compiler

namespace FiniteAlgebraicEnvelopes.Compiler.Validator
open Relation
variable {S Γ : Type*} (blank : Γ)

/-- The machine may alter tags but never these ordered bases or outer flags. -/
def baseSkeleton (s : Sector S Γ) : List (Base S) × Bool × Bool :=
  ((s.left.reverse ++ s.right).map Prod.fst, s.leftBoundary, s.rightBoundary)

theorem clean_anchors {l : List (Cell S Γ)} (h : Anchors blank l) :
    (l.map Prod.fst).map (cell blank) = l := by
  induction h with
  | nil => rfl
  | cons a h ih => simpa [cell] using congrArg (cell blank (.anchor a) :: ·) ih

theorem clean_left {l : List (Cell S Γ)} (h : Left blank l) :
    (l.map Prod.fst).map (cell blank) = l := by
  induction h with
  | cut h => simp only [List.map_cons, cell, clean_anchors blank h]
  | work h ih => simpa [cell] using congrArg (cell blank .workspace :: ·) ih

theorem clean_tail {l : List (Cell S Γ)} (h : Tail blank l) :
    (l.map Prod.fst).map (cell blank) = l := by
  induction h with
  | cut h => simp only [List.map_cons, cell, clean_anchors blank h]
  | work h ih => simpa [cell] using congrArg (cell blank .workspace :: ·) ih

theorem cutD_not_mem_left {l : List (Cell S Γ)} (h : Left blank l) :
    cell blank .cutD ∉ l := by
  obtain ⟨s, x, rfl⟩ := (left_iff blank _).mp h
  simp [cell]

/-- Passing entries are determined by their invariant base sequence, with no
    injectivity hypothesis on the subsequent simulated-machine transitions. -/
theorem passing_entries_unique {a b : Sector S Γ}
    (ha : Entry blank a) (hb : Entry blank b)
    (hra : Ready blank a) (hrb : Ready blank b)
    (hs : baseSkeleton a = baseSkeleton b) : a = b := by
  rcases a with ⟨qa, la, ra, lba, rba⟩
  rcases b with ⟨qb, lb, rb, lbb, rbb⟩
  rcases ha with ⟨rfl, ra', rfl⟩
  rcases hb with ⟨rfl, rb', rfl⟩
  rcases hra with ⟨rfl, rfl, hal, har⟩
  rcases hrb with ⟨rfl, rfl, hbl, hbr⟩
  have hcells : la.reverse ++ cell blank .cutD :: ra' =
      lb.reverse ++ cell blank .cutD :: rb' := by
    have h := congrArg (fun z => z.1.map (cell blank)) hs
    simp only [baseSkeleton, List.map_append, List.map_reverse] at h
    simpa only [clean_left blank hal, clean_left blank hbl,
      clean_tail blank har, clean_tail blank hbr] using h
  have hnot : cell blank .cutD ∉ ra' := by
    cases har with
    | cut h =>
        obtain ⟨x, rfl⟩ := (anchors_iff blank _).mp h
        simp [cell]
  have hsplit := (List.append_cons_inj_of_notMem
    (by simpa using cutD_not_mem_left blank hal) hnot).mp hcells
  rcases hsplit with ⟨hl, _, hr⟩
  have hleft : la = lb := List.reverse_injective hl
  subst lb
  subst rb'
  rfl

end FiniteAlgebraicEnvelopes.Compiler.Validator

namespace FiniteAlgebraicEnvelopes.Compiler.Validator.Extended
open Relation
variable {S Γ M : Type*} (blank : Γ)
abbrev Cfg (S Γ M : Type*) := Sector S Γ ⊕ M

/-- Only the fresh handoff and machine configurations participate in simulation;
    in particular there is no return to I,J,J',N,V. -/
def Active : Cfg S Γ M → Prop
  | .inl v => v.head = .start
  | .inr _ => True

/-- The internal graph consists of literal validator equations and simulator
    edges. These edges contain neither quota insertion nor exit to cleanup. -/
inductive Step (r : Cfg S Γ M → Cfg S Γ M → Prop) :
    Cfg S Γ M → Cfg S Γ M → Prop
  | validator {v w} : Validator.Step blank v w → Step r (.inl v) (.inl w)
  | machine {a b} : Active a → Active b → r a b → Step r a b

theorem validator_not_start {a b : Sector S Γ} (h : Validator.Step blank a b) :
    a.head ≠ .start := by
  cases h <;> simp

theorem deterministic {r : Cfg S Γ M → Cfg S Γ M → Prop}
    (hr : Relator.RightUnique r) : Relator.RightUnique (Step blank r) := by
  intro a b c hab hac
  cases hab with
  | validator hab =>
      cases hac with
      | validator hac => exact congrArg Sum.inl (Validator.step_deterministic blank hab hac)
      | machine ha _ _ => exact False.elim (validator_not_start blank hab ha)
  | machine ha _ hab =>
      cases hac with
      | validator hac => exact False.elim (validator_not_start blank hac ha)
      | machine _ _ hac => exact hr hab hac

/-- A path starting in the validator either stays there, or first reaches its
    fresh handoff. This explicitly excludes a dirty bypass of validation. -/
theorem path_decomposition {r : Cfg S Γ M → Cfg S Γ M → Prop}
    {a : Sector S Γ} {b : Cfg S Γ M} (h : ReflTransGen (Step blank r) (.inl a) b) :
    (∃ v, b = .inl v ∧ ReflTransGen (Validator.Step blank) a v) ∨
    ∃ v, ReflTransGen (Validator.Step blank) a v ∧ v.head = .start := by
  induction h with
  | refl => exact Or.inl ⟨a, rfl, .refl⟩
  | @tail b c hab hbc ih =>
      rcases ih with ⟨v, rfl, hav⟩ | hv
      · cases hbc with
        | validator h => exact Or.inl ⟨_, rfl, hav.tail h⟩
        | machine hv _ _ => exact Or.inr ⟨v, hav, hv⟩
      · exact Or.inr hv

theorem reaches_active {r : Cfg S Γ M → Cfg S Γ M → Prop}
    {a : Sector S Γ} {b : Cfg S Γ M} (h : ReflTransGen (Step blank r) (.inl a) b)
    (hb : Active b) :
    ∃ v, ReflTransGen (Validator.Step blank) a v ∧ v.head = .start := by
  rcases path_decomposition blank h with ⟨v, rfl, hav⟩ | hv
  · exact ⟨v, hav, hb⟩
  · exact hv

/-- Pulling a path back from a non-handoff validator configuration never
    encounters a simulator edge. -/
theorem path_to_validator {r : Cfg S Γ M → Cfg S Γ M → Prop}
    {a c : Cfg S Γ M} (h : ReflTransGen (Step blank r) a c)
    {b : Sector S Γ} (hc : c = .inl b) (hb : b.head ≠ .start) :
    ∃ v, a = .inl v ∧ ReflTransGen (Validator.Step blank) v b := by
  induction h generalizing b with
  | refl => exact ⟨b, hc, .refl⟩
  | @tail c d hac hcd ih =>
      subst d
      cases hcd with
      | validator h =>
          obtain ⟨v, hav, hvc⟩ := ih rfl (validator_not_start blank h)
          exact ⟨v, hav, hvc.tail h⟩
      | machine _ hd _ => exact False.elim (hb hd)

variable (bases : M → List (Base S) × Bool × Bool)

def baseSkeleton : Cfg S Γ M → List (Base S) × Bool × Bool
  | .inl v => Validator.baseSkeleton v
  | .inr q => bases q

theorem step_bases {r : Cfg S Γ M → Cfg S Γ M → Prop}
    (hr : ∀ a b, r a b → baseSkeleton bases a = baseSkeleton bases b)
    {a b : Cfg S Γ M} (h : Step blank r a b) :
    baseSkeleton bases a = baseSkeleton bases b := by
  cases h with
  | validator h =>
      have h' := Validator.step_skeleton blank h
      exact congrArg (fun z => (z.1.map Prod.fst, z.2)) h'
  | machine _ _ h => exact hr _ _ h

theorem connected_bases {r : Cfg S Γ M → Cfg S Γ M → Prop}
    (hr : ∀ a b, r a b → baseSkeleton bases a = baseSkeleton bases b)
    {a b : Cfg S Γ M} (h : EqvGen (Step blank r) a b) :
    baseSkeleton bases a = baseSkeleton bases b := by
  induction h with
  | rel _ _ h => exact step_bases blank bases hr h
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Entry uniqueness survives arbitrary reverse branching in the simulated
    machine. This is source Lemma compiler-components on all dirty sectors. -/
theorem entries_unique {r : Cfg S Γ M → Cfg S Γ M → Prop}
    (hdet : Relator.RightUnique r)
    (hbase : ∀ a b, r a b → baseSkeleton bases a = baseSkeleton bases b)
    {a b : Sector S Γ} (ha : Entry blank a) (hb : Entry blank b)
    (hab : EqvGen (Step blank r) (.inl a) (.inl b)) : a = b := by
  obtain ⟨c, hac, hbc⟩ := weak_component_joins (deterministic blank hdet) hab
  have hsame : Validator.baseSkeleton a = Validator.baseSkeleton b :=
    connected_bases blank bases hbase hab
  have hactive (hc : Active c) : a = b := by
    obtain ⟨v, hav, hv⟩ := reaches_active blank hac hc
    obtain ⟨w, hbw, hw⟩ := reaches_active blank hbc hc
    apply passing_entries_unique blank ha hb _ _ hsame
    · apply reaches_ready blank hav
      simp [Ready, hv]
    · apply reaches_ready blank hbw
      simp [Ready, hw]
  cases c with
  | inr q => exact hactive trivial
  | inl v =>
      by_cases hv : v.head = .start
      · exact hactive hv
      · obtain ⟨a', heqa, hav⟩ := path_to_validator blank hac rfl hv
        obtain ⟨b', heqb, hbv⟩ := path_to_validator blank hbc rfl hv
        cases Sum.inl.inj heqa
        cases Sum.inl.inj heqb
        exact sources_unique_of_join (step_leftUnique blank)
          (fun _ => entry_no_predecessor blank ha)
          (fun _ => entry_no_predecessor blank hb) hav hbv

end FiniteAlgebraicEnvelopes.Compiler.Validator.Extended

namespace FiniteAlgebraicEnvelopes.Compiler.Scan

/-- A list zipper for the same finite-scan semantics. Left cells are nearest
    first. This representation permits induction on literal scan paths. -/
structure Sector (Head Base Tag : Type*) where
  left : List (Base × Tag)
  head : Head
  right : List (Base × Tag)
  leftBoundary : Bool
  rightBoundary : Bool
  deriving DecidableEq

variable {H B T : Type*}

def step (table : Table H B T) (v : Sector H B T) : Option (Sector H B T) :=
  match table.direction v.head with
  | .left => match v.left with
    | (b,t) :: l => (table.cell v.head b t).map fun a =>
        if a.cross then { v with left := l, head := a.head, right := (b,a.tag) :: v.right }
        else { v with left := (b,a.tag) :: l, head := a.head }
    | [] => if v.leftBoundary then
        (table.boundary v.head).map fun q => { v with head := q } else none
  | .right => match v.right with
    | (b,t) :: r => (table.cell v.head b t).map fun a =>
        if a.cross then { v with left := (b,a.tag) :: v.left, head := a.head, right := r }
        else { v with head := a.head, right := (b,a.tag) :: r }
    | [] => if v.rightBoundary then
        (table.boundary v.head).map fun q => { v with head := q } else none

def Step (table : Table H B T) (v w : Sector H B T) : Prop := step table v = some w

theorem deterministic (table : Table H B T) : Relator.RightUnique (Step table) := by
  intro a b c hab hac
  exact Option.some.inj (hab.symm.trans hac)

def baseSkeleton (v : Sector H B T) : List B × Bool × Bool :=
  ((v.left.reverse ++ v.right).map Prod.fst, v.leftBoundary, v.rightBoundary)

theorem step_skeleton (table : Table H B T) {v w : Sector H B T}
    (h : Step table v w) : baseSkeleton v = baseSkeleton w := by
  rcases v with ⟨l,q,r,lb,rb⟩
  unfold Step step at h
  cases hd : table.direction q <;> simp only [hd] at h
  · cases l with
    | nil =>
      cases lb <;> simp only [Bool.false_eq_true, ↓reduceIte] at h
      · contradiction
      · cases hb : table.boundary q <;> simp only [hb, Option.map_none, Option.map_some] at h
        · contradiction
        · cases Option.some.inj h; rfl
    | cons a l =>
      rcases a with ⟨b,t⟩
      cases hc : table.cell q b t <;> simp only [hc, Option.map_none, Option.map_some] at h
      · contradiction
      · rename_i ins
        cases hm : ins.cross <;> simp only [hm, Bool.false_eq_true, ↓reduceIte] at h <;> cases Option.some.inj h <;>
          simp [baseSkeleton, List.reverse_cons, List.append_assoc]
  · cases r with
    | nil =>
      cases rb <;> simp only [Bool.false_eq_true, ↓reduceIte] at h
      · contradiction
      · cases hb : table.boundary q <;> simp only [hb, Option.map_none, Option.map_some] at h
        · contradiction
        · cases Option.some.inj h; rfl
    | cons a r =>
      rcases a with ⟨b,t⟩
      cases hc : table.cell q b t <;> simp only [hc, Option.map_none, Option.map_some] at h
      · contradiction
      · rename_i ins
        cases hm : ins.cross <;> simp only [hm, Bool.false_eq_true, ↓reduceIte] at h <;> cases Option.some.inj h <;>
          simp [baseSkeleton, List.reverse_cons, List.append_assoc]

end FiniteAlgebraicEnvelopes.Compiler.Scan

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteCompiler_Simulator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Literal finite-quota machine simulation and readout correctness.
-/

namespace FiniteAlgebraicEnvelopes.Compiler.Simulator

/-- Finite work alphabet, including a literal code for every input letter and
    a distinct blank. The remaining symbols are rejected by output reading. -/
structure Alphabet (S Γ : Type*) where
  blank : Γ
  input : S → Γ
  output : Γ → Option S
  output_input : ∀ a, output (input a) = some a
  output_blank : output blank = none

inductive Resume (S : Type*)
  | input | fill : S → Resume S
  | spare | first | readout | put : S → Resume S
  deriving DecidableEq, Fintype

/-- Distinct phases make every scan's designated reading side unambiguous. -/
inductive Head (S Q : Type*)
  | start
  | rewind : Resume S → Head S Q
  | scan : Resume S → Head S Q
  | run : Q → Head S Q
  | left : Q → Head S Q
  | finish | ok
  deriving DecidableEq, Fintype

end FiniteAlgebraicEnvelopes.Compiler.Simulator

namespace FiniteAlgebraicEnvelopes.Compiler.Scan
open Relation
variable {H B T : Type*}

theorem cross_right (table : Table H B T) (q : H) (hd : table.direction q = .right)
    (p l r : List (B × T)) (lb rb : Bool)
    (hp : ∀ c ∈ p, table.cell q c.1 c.2 = some ⟨q,c.2,true⟩) :
    ReflTransGen (Step table) ⟨l,q,p ++ r,lb,rb⟩ ⟨p.reverse ++ l,q,r,lb,rb⟩ := by
  induction p generalizing l with
  | nil => exact .refl
  | cons c p ih =>
    rcases c with ⟨b,t⟩
    have hc := hp (b,t) (by simp)
    have hstep : Step table ⟨l,q,(b,t)::(p++r),lb,rb⟩
        ⟨(b,t)::l,q,p++r,lb,rb⟩ := by simp [Step, step, hd, hc]
    simpa only [List.cons_append, List.reverse_cons, List.append_assoc,
      List.singleton_append, List.nil_append] using
      (ReflTransGen.head hstep (ih ((b,t)::l) fun c hc => hp c (by simp [hc])))

end FiniteAlgebraicEnvelopes.Compiler.Scan

namespace FiniteAlgebraicEnvelopes.Compiler.Simulator

section
open Relation
variable {S Γ Q : Type*}
  (A : Alphabet S Γ)
  [DecidableEq Γ]

abbrev Cells (S Γ : Type*) := List (Base S × Tag S Γ)

/-- Tags following the copy phase; unused full-tag fields remain literally
    clean, as required by the validator/simulator convention. -/
def readAnchor (a : S) (read : Bool) : Base S × Tag S Γ :=
  (.anchor a,{clean A.blank with anchorRead := read})

def filledWork (a : S) : Base S × Tag S Γ :=
  (.workspace,{clean A.blank with workspaceFilled := true, work := A.input a})

def bare (b : Base S) : Base S × Tag S Γ := (b,clean A.blank)

/-- The whole tape during copying: read and unread anchor prefixes on either
    side of the reserved workspace, with a filled prefix followed by blanks. -/
def body (xp xs yp ys w : List S) (n : ℕ) : Cells S Γ :=
  xp.map (readAnchor A · true) ++ xs.map (readAnchor A · false) ++
  [bare A .cutC] ++ w.map (filledWork A) ++ List.replicate n (bare A .workspace) ++
  [bare A .cutD] ++ yp.map (readAnchor A · true) ++ ys.map (readAnchor A · false)

end

section
open Relation
variable {S Γ Q : Type*}

/-- A literal bounded workspace. The left list is in reverse tape order, and
    an empty right list is outside the supplied quota, not a fresh blank cell. -/
structure Tape where
  state : Q
  left : List (Tag S Γ)
  right : List (Tag S Γ)

/-- Update only the simulated work track; all auxiliary tag fields are retained. -/
def writeWork (t : Tag S Γ) (a : Γ) : Tag S Γ := { t with work := a }

end

section
open Relation
variable {S Γ Q : Type*}

/-- Locate a specified item of a projected list without discarding the cells
    skipped by the projection. This handles interleaved anchors and workspace. -/
theorem split_filterMap {α β : Type*} (f : α → Option β) (l : List α)
    (p : List β) (b : β) (r : List β) (h : l.filterMap f = p ++ b::r) :
    ∃ l₁ a l₂, l = l₁ ++ a::l₂ ∧ l₁.filterMap f = p ∧
      f a = some b ∧ l₂.filterMap f = r := by
  induction l generalizing p with
  | nil => simp at h
  | cons a l ih =>
      cases hf : f a with
      | none =>
          simp only [List.filterMap_cons, hf] at h
          obtain ⟨l₁,c,l₂,hl,hp,hc,hr⟩ := ih p h
          exact ⟨a::l₁,c,l₂,by simp [hl],by simp [hf,hp],hc,hr⟩
      | some v =>
          simp only [List.filterMap_cons, hf] at h
          cases p with
          | nil =>
              simp only [List.nil_append, List.cons.injEq] at h
              exact ⟨[],a,l,by simp, rfl,by simpa [h.1] using hf,h.2⟩
          | cons v' p =>
              simp only [List.cons_append, List.cons.injEq] at h
              obtain ⟨l₁,c,l₂,hl,hp,hc,hr⟩ := ih p h.2
              exact ⟨a::l₁,c,l₂,by simp [hl],by simp [hf,hp,h.1],hc,hr⟩

end

section
open Relation
variable {S Γ Q : Type*}

/-- Semantic one-sided tape: its right end is an infinite blank tail, not an
    extra halting edge. Auxiliary simulator tags do not enter this semantics. -/
structure SemanticTape (Γ Q : Type*) where
  state : Q
  left : List Γ
  right : Stream' Γ

theorem replicate_append_const (b : Γ) (n : ℕ) :
    Stream'.appendStream' (List.replicate n b) (Stream'.const b) = Stream'.const b := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [List.replicate_succ,Stream'.appendStream',ih]
      exact (Stream'.const_eq b).symm

end

open Relation

end FiniteAlgebraicEnvelopes.Compiler.Simulator

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteCompiler_Control
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Finite control and bounded compiler orbit normalization.
-/

namespace FiniteAlgebraicEnvelopes.Compiler.Cleanup
open Relation
variable {S Γ : Type*}

inductive Head
  | cleanup | raw
  deriving DecidableEq

instance instFintypeHead : Fintype Head := ⟨{.cleanup,.raw}, by intro h; cases h <;> simp⟩

end FiniteAlgebraicEnvelopes.Compiler.Cleanup

namespace FiniteAlgebraicEnvelopes.Compiler.Scan
open Relation
variable {H B T : Type*}

/-- An explicit bounded list enumeration, used only for finite internal search.
    This bound counts cells, not grade, and thus never admits quota insertion. -/
def boundedLists (α : Type*) [Fintype α] [DecidableEq α] : ℕ → Finset (List α)
  | 0 => {[]}
  | n+1 => {[]} ∪ ((Finset.univ : Finset α) ×ˢ boundedLists α n).image (fun p => p.1::p.2)

@[simp] theorem mem_boundedLists (α : Type*) [Fintype α] [DecidableEq α]
    (n : ℕ) (l : List α) : l ∈ boundedLists α n ↔ l.length ≤ n := by
  induction n generalizing l with
  | zero => simp [boundedLists]
  | succ n ih =>
      cases l with
      | nil => simp [boundedLists]
      | cons a l => simp [boundedLists,ih]

variable [Fintype H] [Fintype B] [Fintype T]
variable [DecidableEq H] [DecidableEq B] [DecidableEq T]

/-- The finite search universe consists of actual list-zipper sectors. -/
def boundedSectors (k : ℕ) : Finset (Sector H B T) :=
  (((((Finset.univ : Finset H) ×ˢ boundedLists (B×T) k) ×ˢ boundedLists (B×T) k) ×ˢ
      (Finset.univ : Finset Bool)) ×ˢ (Finset.univ : Finset Bool)).image
    (fun p => ⟨p.1.1.1.2,p.1.1.1.1,p.1.1.2,p.1.2,p.2⟩)

@[simp] theorem mem_boundedSectors (k : ℕ) (v : Sector H B T) :
    v ∈ boundedSectors k ↔ v.left.length ≤ k ∧ v.right.length ≤ k := by
  rcases v with ⟨l,q,r,a,b⟩
  simp [boundedSectors,Sector.mk.injEq]

/-- Filtering by bases and boundary flags gives exactly the source's fixed
    internal-search state space. This is computable from the literal sector. -/
def searchUniverse (v : Sector H B T) : Finset (Sector H B T) :=
  (boundedSectors (v.left.length+v.right.length)).filter
    (fun w => baseSkeleton w = baseSkeleton v)

omit [Fintype H] [Fintype B] [Fintype T] [DecidableEq H] [DecidableEq B] [DecidableEq T] in
theorem skeleton_length {v w : Sector H B T} (h : baseSkeleton v = baseSkeleton w) :
    v.left.length+v.right.length = w.left.length+w.right.length := by
  have hl := congrArg (fun p : List B × Bool × Bool => p.1.length) h
  simpa [baseSkeleton] using hl

@[simp] theorem mem_universe (v w : Sector H B T) :
    w ∈ searchUniverse v ↔ baseSkeleton w = baseSkeleton v := by
  simp only [searchUniverse,Finset.mem_filter,mem_boundedSectors,and_iff_right_iff_imp]
  intro h
  have hl := skeleton_length h
  constructor <;> omega

abbrev Fixed (v : Sector H B T) := {w : Sector H B T // baseSkeleton w = baseSkeleton v}

instance fixedFintype (v : Sector H B T) : Fintype (Fixed v) :=
  Fintype.subtype (searchUniverse v) (mem_universe v)

def fixedSelf (v : Sector H B T) : Fixed v := ⟨v,rfl⟩

def fixedStep (table : Table H B T) (v : Sector H B T) (a b : Fixed v) : Prop :=
  Step table a.val b.val

instance fixedStepDecidable (table : Table H B T) (v : Sector H B T) :
    DecidableRel (fixedStep table v) := fun _ _ => inferInstanceAs (Decidable (_ = _))

omit [Fintype H] [Fintype B] [Fintype T] [DecidableEq H] [DecidableEq B] [DecidableEq T] in
theorem connected_skeleton (table : Table H B T) {x y : Sector H B T}
    (h : EqvGen (Step table) x y) : baseSkeleton x = baseSkeleton y := by
  induction h with
  | rel _ _ h => exact step_skeleton table h
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

omit [Fintype H] [Fintype B] [Fintype T] [DecidableEq H] [DecidableEq B] [DecidableEq T] in
/-- A weak path with fixed baselines lifts to the finite search universe. -/
theorem fixedConnected_iff (table : Table H B T) (v : Sector H B T) (a b : Fixed v) :
    EqvGen (fixedStep table v) a b ↔ EqvGen (Step table) a.val b.val := by
  constructor
  · intro h
    induction h with
    | rel _ _ h => exact .rel _ _ h
    | refl => exact .refl _
    | symm _ _ _ ih => exact .symm _ _ ih
    | trans _ _ _ _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂
  · intro h
    have lift : ∀ x y, EqvGen (Step table) x y →
        ∀ (hx : baseSkeleton x = baseSkeleton v),
        ∃ (hy : baseSkeleton y = baseSkeleton v),
          EqvGen (fixedStep table v) ⟨x,hx⟩ ⟨y,hy⟩ := by
      intro x y h
      induction h with
      | rel x y h =>
          intro hx
          exact ⟨(step_skeleton table h).symm.trans hx,.rel _ _ h⟩
      | refl x => intro hx; exact ⟨hx,.refl _⟩
      | symm x y h ih =>
          intro hy
          have hbase := connected_skeleton table h
          obtain ⟨_,hr⟩ := ih (hbase.trans hy)
          exact ⟨hbase.trans hy,.symm _ _ hr⟩
      | trans x y z _ _ ih₁ ih₂ =>
          intro hx
          obtain ⟨hy,hxy⟩ := ih₁ hx
          obtain ⟨hz,hyz⟩ := ih₂ hy
          exact ⟨hz,.trans _ _ _ hxy hyz⟩
    obtain ⟨_,h'⟩ := lift a.val b.val h a.property
    exact h'

end FiniteAlgebraicEnvelopes.Compiler.Scan

namespace FiniteAlgebraicEnvelopes.Compiler.Validator
variable {S Γ : Type*}

instance instFintypeHead : Fintype Head :=
  ⟨{.initial,.left,.right,.workspace,.suffix,.start},by intro h; cases h <;> simp⟩

end FiniteAlgebraicEnvelopes.Compiler.Validator

namespace FiniteAlgebraicEnvelopes.Compiler.Scan
variable {H H' B T : Type*}

def mapInstruction (f : H → H') (v : Instruction H T) : Instruction H' T :=
  ⟨f v.head,v.tag,v.cross⟩

end FiniteAlgebraicEnvelopes.Compiler.Scan

namespace FiniteAlgebraicEnvelopes.Compiler
variable {α : Type*}

/-- The priority order in source compiler-normalization: entry first, success
    second, and arbitrary component member only when neither is present. -/
def prioritySet (P Q : α → Prop) [DecidablePred P] [DecidablePred Q] (s : Finset α) : Finset α :=
  if (s.filter P).Nonempty then s.filter P
  else if (s.filter Q).Nonempty then s.filter Q else s

theorem prioritySet_subset (P Q : α → Prop) [DecidablePred P] [DecidablePred Q] (s : Finset α) :
    prioritySet P Q s ⊆ s := by
  unfold prioritySet
  split <;> first | exact Finset.filter_subset _ _ | skip
  split
  · exact Finset.filter_subset _ _
  · exact Finset.Subset.refl _

theorem prioritySet_nonempty (P Q : α → Prop) [DecidablePred P] [DecidablePred Q]
    (s : Finset α) (hs : s.Nonempty) : (prioritySet P Q s).Nonempty := by
  unfold prioritySet
  split
  · assumption
  · split <;> assumption

end FiniteAlgebraicEnvelopes.Compiler

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteCompiler_Surface
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Surface alphabet, preprocessing, and grading estimates.
-/

namespace FiniteAlgebraicEnvelopes.Compiler.Surface

section
open Relation

/-- The complete head alphabet; internal control excludes raw, quota and cleanup. -/
inductive Head (H : Type*)
  | raw | pending | cleanup
  | internal : H → Head H
  deriving DecidableEq, Fintype

end

open Relation
variable {S Γ H : Type*}

def cleanupHead : Cleanup.Head → Head H
  | .cleanup => .cleanup
  | .raw => .raw

end FiniteAlgebraicEnvelopes.Compiler.Surface

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteCompiler_Paths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Path alphabet, sectors, cuts, and contextual preparation.
-/

namespace FiniteAlgebraicEnvelopes.Compiler.Path

section

inductive Vertex
  | outer | left | right
  deriving DecidableEq

instance instFintypeVertex : Fintype Vertex := ⟨{.outer,.left,.right}, by intro x; cases x <;> simp⟩

/-- There are no vertex-identity letters. `zero` is the absorbing letter. -/
inductive Letter (C H : Type*)
  | zero | enter | leave
  | head : H → Letter C H
  | left : C → Letter C H
  | right : C → Letter C H
  deriving DecidableEq, Fintype

/-- Boundary type of a word; `unit` belongs only to the empty word. -/
inductive Shape
  | zero | unit
  | path : Vertex → Vertex → Shape
  deriving DecidableEq

instance instFintypeShape : Fintype Shape :=
  ⟨{.zero,.unit} ∪ Finset.univ.biUnion (fun a => Finset.univ.image (Shape.path a)), by
    intro x; cases x <;> simp⟩

def Shape.comp : Shape → Shape → Shape
  | .zero,_ => .zero
  | _,.zero => .zero
  | .unit,b => b
  | a,.unit => a
  | .path a b,.path c d => if b = c then .path a d else .zero

instance instMonoidShape : Monoid Shape where
  mul := Shape.comp
  one := .unit
  mul_assoc := by decide
  one_mul := by decide
  mul_one := by decide

@[simp] theorem unit_mul (s : Shape) : Shape.unit * s = s := one_mul s
@[simp] theorem mul_unit (s : Shape) : s * Shape.unit = s := mul_one s

@[simp] theorem zero_mul (s : Shape) : Shape.zero * s = .zero := rfl
@[simp] theorem mul_zero (s : Shape) : s * Shape.zero = .zero := by cases s <;> rfl
@[simp] theorem path_mul_path (a b c d : Vertex) :
    Shape.path a b * Shape.path c d = if b = c then .path a d else .zero := rfl

variable {C H : Type*}

def typeOf : Letter C H → Shape
  | .zero => .zero
  | .enter => .path .outer .left
  | .leave => .path .right .outer
  | .head _ => .path .left .right
  | .left _ => .path .left .left
  | .right _ => .path .right .right

def shape (w : List (Letter C H)) : Shape := (w.map typeOf).prod

@[simp] theorem shape_nil : shape ([] : List (Letter C H)) = .unit := rfl
@[simp] theorem shape_cons (a : Letter C H) (w : List (Letter C H)) :
    shape (a::w) = typeOf a * shape w := by simp [shape]
@[simp] theorem shape_append (u v : List (Letter C H)) :
    shape (u++v) = shape u * shape v := by simp [shape]
@[simp] theorem shape_singleton (a : Letter C H) : shape [a] = typeOf a := by simp

/-- Parallel nonzero equation sides preserve the complete contextual shape,
    including nonpath status. This also covers all length-decreasing cleanup. -/
theorem shape_context {u v : List (Letter C H)} (h : shape u = shape v)
    (x y : List (Letter C H)) : shape (x++u++y) = shape (x++v++y) := by simp [h]

theorem shape_zero_context (x y : List (Letter C H)) :
    shape (x ++ .zero :: y) = .zero := by simp [typeOf]

@[simp] theorem typeOf_ne_unit (a : Letter C H) : typeOf a ≠ .unit := by
  cases a <;> simp [typeOf]

/-- A headed sector written literally. Cells left of the head are supplied in
    nearest-first zipper order. -/
def headed (l : List C) (q : H) (r : List C) (lb rb : Bool) : List (Letter C H) :=
  (if lb then [.enter] else []) ++ l.reverse.map .left ++ [.head q] ++
    r.map .right ++ (if rb then [.leave] else [])

@[simp] theorem shape_left (l : List C) :
    shape (l.map (Letter.left : C → Letter C H)) =
      if l = [] then .unit else .path .left .left := by
  induction l with
  | nil => simp
  | cons a l ih =>
    cases l with
    | nil => simp [typeOf]
    | cons b l => simp_all [typeOf]

@[simp] theorem shape_right (l : List C) :
    shape (l.map (Letter.right : C → Letter C H)) =
      if l = [] then .unit else .path .right .right := by
  induction l with
  | nil => simp
  | cons a l ih =>
    cases l with
    | nil => simp [typeOf]
    | cons b l => simp_all [typeOf]

@[simp] theorem shape_headed (l : List C) (q : H) (r : List C) (lb rb : Bool) :
    shape (headed l q r lb rb) =
      .path (if lb then .outer else .left) (if rb then .outer else .right) := by
  classical
  unfold headed
  simp only [shape_append,shape_left,shape_right,shape_singleton,List.reverse_eq_nil_iff]
  cases lb <;> cases rb <;> by_cases hl : l = [] <;> by_cases hr : r = [] <;>
    simp [hl,hr,typeOf]

def heads : List (Letter C H) → List H := List.filterMap fun
  | .head q => some q
  | _ => none

def lefts : List (Letter C H) → List C := List.filterMap fun
  | .left c => some c
  | _ => none

def rights : List (Letter C H) → List C := List.filterMap fun
  | .right c => some c
  | _ => none

@[simp] theorem heads_headed (l : List C) (q : H) (r : List C) (lb rb : Bool) :
    heads (headed l q r lb rb) = [q] := by
  cases lb <;> cases rb <;> simp [headed,heads,List.filterMap_map]

@[simp] theorem lefts_headed (l : List C) (q : H) (r : List C) (lb rb : Bool) :
    lefts (headed l q r lb rb) = l.reverse := by
  cases lb <;> cases rb <;> simp [headed,lefts,List.filterMap_map]

@[simp] theorem rights_headed (l : List C) (q : H) (r : List C) (lb rb : Bool) :
    rights (headed l q r lb rb) = r := by
  cases lb <;> cases rb <;> simp [headed,rights,List.filterMap_map]

/-- Prefix a (possibly empty) fragment to the first sector, creating a sector
    only when the fragment is nonempty. -/
def glue (u : List (Letter C H)) (cs : List (List (Letter C H))) : List (List (Letter C H)) :=
  match cs with
  | c::cs => (u++c)::cs
  | [] => match u with
    | [] => []
    | _::_ => [u]

@[simp] theorem glue_nil (cs : List (List (Letter C H))) : glue [] cs = cs := by
  cases cs <;> rfl

@[simp] theorem glue_cons (u c : List (Letter C H)) (cs : List (List (Letter C H))) :
    glue u (c::cs) = (u++c)::cs := rfl

theorem glue_assoc (u v : List (Letter C H)) (cs : List (List (Letter C H))) :
    glue u (glue v cs) = glue (u++v) cs := by
  cases cs <;> cases u <;> cases v <;> simp [glue,List.append_assoc]

/-- Cut immediately after an omega, omitting the empty final sector. On paths
    every interior cut is exactly omega-alpha, including headless end sectors. -/
def cuts : List (Letter C H) → List (List (Letter C H))
  | [] => []
  | .leave::w => [.leave] :: cuts w
  | a::w => glue [a] (cuts w)

@[simp] theorem cuts_nil : cuts ([] : List (Letter C H)) = [] := rfl
@[simp] theorem cuts_leave (w : List (Letter C H)) : cuts (.leave::w) = [.leave]::cuts w := rfl

theorem cuts_cons {a : Letter C H} (ha : a ≠ .leave) (w : List (Letter C H)) :
    cuts (a::w) = glue [a] (cuts w) := by cases a <;> simp_all [cuts]

@[simp] theorem flatten_glue (u : List (Letter C H)) (cs : List (List (Letter C H))) :
    (glue u cs).flatten = u ++ cs.flatten := by
  cases cs <;> cases u <;> simp [glue,List.append_assoc]

@[simp] theorem flatten_cuts (w : List (Letter C H)) : (cuts w).flatten = w := by
  induction w with
  | nil => rfl
  | cons a w ih => cases a <;> simp [cuts,ih]

theorem cuts_append_nonleave (u v : List (Letter C H)) (hu : Letter.leave ∉ u) :
    cuts (u++v) = glue u (cuts v) := by
  induction u with
  | nil => simp
  | cons a u ih =>
    have ha : a ≠ .leave := fun h => hu (by simp [h])
    have hu' : Letter.leave ∉ u := fun h => hu (List.mem_cons_of_mem _ h)
    rw [List.cons_append,cuts_cons ha,ih hu',glue_assoc]
    rfl

theorem cuts_of_noLeave (u : List (Letter C H)) (hu : Letter.leave ∉ u) :
    cuts u = glue u [] := by simpa using cuts_append_nonleave u [] hu

@[simp] theorem headed_ne_nil (l : List C) (q : H) (r : List C) (lb rb : Bool) :
    headed l q r lb rb ≠ [] := by
  intro he
  have hh := congrArg heads he
  rw [heads_headed] at hh
  change [q] = [] at hh
  cases hh

@[simp] theorem cuts_headed (l : List C) (q : H) (r : List C) (lb rb : Bool) :
    cuts (headed l q r lb rb) = [headed l q r lb rb] := by
  have hn : (Letter.leave : Letter C H) ∉ headed l q r lb false := by
    cases lb <;> simp [headed]
  have hne := headed_ne_nil l q r lb false
  cases rb
  · rw [cuts_of_noLeave _ hn]
    cases he : headed l q r lb false with
    | nil => exact (hne he).elim
    | cons a w => rfl
  · have he : headed l q r lb true = headed l q r lb false ++ [.leave] := by
      simp [headed,List.append_assoc]
    rw [he,cuts_append_nonleave _ _ hn]
    rfl

theorem shape_append_ne_zero {u v : List (Letter C H)} (h : shape (u++v) ≠ .zero) :
    shape u ≠ .zero ∧ shape v ≠ .zero := by
  constructor <;> intro hz <;> apply h <;> simp [hz]

theorem shape_mem_flatten_ne_zero {cs : List (List (Letter C H))}
    (h : shape cs.flatten ≠ .zero) {c : List (Letter C H)} (hc : c ∈ cs) : shape c ≠ .zero := by
  induction cs with
  | nil => simp at hc
  | cons a cs ih =>
    have hh := shape_append_ne_zero h
    rcases List.mem_cons.mp hc with rfl | hc
    · exact hh.1
    · exact ih hh.2 hc

theorem shape_cut_ne_zero {w : List (Letter C H)} (hw : shape w ≠ .zero)
    {c : List (Letter C H)} (hc : c ∈ cuts w) : shape c ≠ .zero := by
  exact shape_mem_flatten_ne_zero (by simpa using hw) hc

def Shape.act : Shape → Vertex → Option Vertex
  | .zero,_ => none
  | .unit,v => some v
  | .path a b,v => if v = a then some b else none

theorem Shape.act_comp : ∀ (a b : Shape) (v : Vertex),
    (a*b).act v = (a.act v).bind b.act := by decide

def walk (v : Vertex) (w : List (Letter C H)) : Option Vertex := (shape w).act v

@[simp] theorem walk_nil (v : Vertex) : walk v ([] : List (Letter C H)) = some v := rfl

theorem walk_cons (v : Vertex) (a : Letter C H) (w : List (Letter C H)) :
    walk v (a::w) = ((typeOf a).act v).bind (fun z => walk z w) := by
  exact Shape.act_comp _ _ _

theorem exists_walk {w : List (Letter C H)} (h : shape w ≠ .zero) :
    ∃ v z, walk v w = some z := by
  cases he : shape w with
  | zero => exact (h he).elim
  | unit => exact ⟨.outer,.outer,by simp [walk,he,Shape.act]⟩
  | path a b => exact ⟨a,b,by simp [walk,he,Shape.act]⟩

/-- A sector cannot have any omega except its last letter. -/
def terminalLeave : List (Letter C H) → Prop
  | [] => True
  | .leave::w => w = []
  | _::w => terminalLeave w

theorem terminalLeave_cons {a : Letter C H} (ha : a ≠ .leave) (w : List (Letter C H)) :
    terminalLeave (a::w) ↔ terminalLeave w := by cases a <;> simp_all [terminalLeave]

theorem terminalLeave_glue (a : Letter C H) (ha : a ≠ .leave)
    (cs : List (List (Letter C H))) (h : ∀ c ∈ cs, terminalLeave c) :
    ∀ c ∈ glue [a] cs, terminalLeave c := by
  cases cs with
  | nil => simp [glue,terminalLeave_cons ha,terminalLeave]
  | cons c cs =>
    simp only [glue,List.cons_append,List.nil_append,List.mem_cons]
    intro d hd
    rcases hd with rfl | hd
    · exact (terminalLeave_cons ha c).2 (h c (by simp))
    · exact h d (List.mem_cons_of_mem _ hd)

theorem terminalLeave_cuts (w : List (Letter C H)) : ∀ c ∈ cuts w, terminalLeave c := by
  induction w with
  | nil => simp
  | cons a w ih =>
    by_cases ha : a = .leave
    · subst a
      simp only [cuts_leave,List.mem_cons]
      intro c hc
      rcases hc with rfl | hc
      · rfl
      · exact ih c hc
    · rw [cuts_cons ha]
      exact terminalLeave_glue _ ha _ ih

/-- Once a path is at R, its terminal sector consists only of right loops and
    an optional omega. This includes a headless right end-sector. -/
theorem right_form {w : List (Letter C H)} (hn : terminalLeave w) {v : Vertex}
    (h : walk .right w = some v) :
    ∃ r : List C, ∃ rb : Bool, w = r.map .right ++ (if rb then [.leave] else []) := by
  induction w with
  | nil => exact ⟨[],false,rfl⟩
  | cons a w ih =>
    cases a with
    | zero => simp [walk_cons,typeOf,Shape.act] at h
    | enter => simp [walk_cons,typeOf,Shape.act] at h
    | head q => simp [walk_cons,typeOf,Shape.act] at h
    | left c => simp [walk_cons,typeOf,Shape.act] at h
    | leave =>
      have hw : w = [] := hn
      exact ⟨[],true,by simp [hw]⟩
    | right c =>
      have hw : walk .right w = some v := by simpa [walk_cons,typeOf,Shape.act] using h
      obtain ⟨r,rb,he⟩ := ih hn hw
      exact ⟨c::r,rb,by simp [he]⟩

/-- Starting at L, a sector either has no head and only left loops, or has
    exactly one head followed by a right-only tail. -/
theorem left_form {w : List (Letter C H)} (hn : terminalLeave w) {v : Vertex}
    (h : walk .left w = some v) :
    (∃ l : List C, w = l.map .left) ∨
    (∃ l : List C, ∃ q : H, ∃ r : List C, ∃ rb : Bool,
      w = l.map .left ++ [.head q] ++ r.map .right ++ (if rb then [.leave] else [])) := by
  induction w with
  | nil => exact .inl ⟨[],rfl⟩
  | cons a w ih =>
    cases a with
    | zero => simp [walk_cons,typeOf,Shape.act] at h
    | enter => simp [walk_cons,typeOf,Shape.act] at h
    | leave => simp [walk_cons,typeOf,Shape.act] at h
    | right c => simp [walk_cons,typeOf,Shape.act] at h
    | head q =>
      have hw : walk .right w = some v := by simpa [walk_cons,typeOf,Shape.act] using h
      obtain ⟨r,rb,he⟩ := right_form (w := w) hn hw
      exact .inr ⟨[],q,r,rb,by simp [he]⟩
    | left c =>
      have hw : walk .left w = some v := by simpa [walk_cons,typeOf,Shape.act] using h
      rcases ih hn hw with ⟨l,he⟩ | ⟨l,q,r,rb,he⟩
      · exact .inl ⟨c::l,by simp [he]⟩
      · exact .inr ⟨c::l,q,r,rb,by simp [he]⟩

/-- Every nonzero sector is either literally headless or has the precise
    optional-boundary zipper grammar used by the finite component evaluator. -/
theorem sector_form {w : List (Letter C H)} (hn : terminalLeave w)
    (h : shape w ≠ .zero) : heads w = [] ∨
    ∃ l q r lb rb, w = headed l q r lb rb := by
  obtain ⟨v,z,hv⟩ := exists_walk h
  cases v with
  | right =>
    obtain ⟨r,rb,rfl⟩ := right_form hn hv
    left
    cases rb <;> simp [heads,List.filterMap_map]
  | left =>
    rcases left_form hn hv with ⟨l,rfl⟩ | ⟨l,q,r,rb,rfl⟩
    · left; simp [heads,List.filterMap_map]
    · right; exact ⟨l.reverse,q,r,false,rb,by simp [headed]⟩
  | outer =>
    cases w with
    | nil => exact .inl rfl
    | cons a w =>
      cases a with
      | zero => simp [walk_cons,typeOf,Shape.act] at hv
      | leave => simp [walk_cons,typeOf,Shape.act] at hv
      | head q => simp [walk_cons,typeOf,Shape.act] at hv
      | left c => simp [walk_cons,typeOf,Shape.act] at hv
      | right c => simp [walk_cons,typeOf,Shape.act] at hv
      | enter =>
        have hw : walk .left w = some z := by simpa [walk_cons,typeOf,Shape.act] using hv
        rcases left_form (w := w) hn hw with ⟨l,rfl⟩ | ⟨l,q,r,rb,rfl⟩
        · left; simp [heads,List.filterMap_map]
        · right; exact ⟨l.reverse,q,r,true,rb,by simp [headed]⟩

structure Sector (C H : Type*) where
  left : List C
  head : H
  right : List C
  leftBoundary : Bool
  rightBoundary : Bool
  deriving DecidableEq

def encode (v : Sector C H) : List (Letter C H) :=
  headed v.left v.head v.right v.leftBoundary v.rightBoundary

@[simp] theorem enter_mem_headed (l : List C) (q : H) (r : List C) (lb rb : Bool) :
    (Letter.enter : Letter C H) ∈ headed l q r lb rb ↔ lb = true := by
  cases lb <;> cases rb <;> simp [headed]

@[simp] theorem leave_mem_headed (l : List C) (q : H) (r : List C) (lb rb : Bool) :
    (Letter.leave : Letter C H) ∈ headed l q r lb rb ↔ rb = true := by
  cases lb <;> cases rb <;> simp [headed]

variable [DecidableEq C] [DecidableEq H]

/-- An entirely literal decoder, including a final equality check. It does not
    assume that its input is a path or that any tag is clean. -/
def decode (w : List (Letter C H)) : Option (Sector C H) :=
  match heads w with
  | [q] =>
    let v : Sector C H := ⟨(lefts w).reverse,q,rights w,
      decide (.enter ∈ w),decide (.leave ∈ w)⟩
    if encode v = w then some v else none
  | _ => none

@[simp] theorem decode_encode (v : Sector C H) : decode (encode v) = some v := by
  rcases v with ⟨l,q,r,lb,rb⟩
  simp only [encode,decode,heads_headed,lefts_headed,rights_headed,List.reverse_reverse,
    enter_mem_headed,leave_mem_headed,Bool.decide_eq_true]
  rfl

theorem decode_sound {w : List (Letter C H)} {v : Sector C H} (h : decode w = some v) :
    encode v = w := by
  unfold decode at h
  split at h
  · dsimp only at h
    split at h
    · cases h
      assumption
    · cases h
  · cases h

end

section
open Relation
variable {C H : Type*}

/-- A single literal equation step in arbitrary word context. -/
inductive Context (r : List (Letter C H) → List (Letter C H) → Prop) :
    List (Letter C H) → List (Letter C H) → Prop
  | apply (x y : List (Letter C H)) {a b} (h : r a b) :
      Context r (x++a++y) (x++b++y)

theorem context_context {r : List (Letter C H) → List (Letter C H) → Prop}
    {u v : List (Letter C H)} (h : Context r u v) (x y : List (Letter C H)) :
    Context r (x++u++y) (x++v++y) := by
  cases h with
  | apply a b h =>
    simpa only [List.append_assoc] using (Context.apply (x++a) (b++y) h)

theorem reaches_context {r : List (Letter C H) → List (Letter C H) → Prop}
    {u v : List (Letter C H)} (h : ReflTransGen (Context r) u v) (x y : List (Letter C H)) :
    ReflTransGen (Context r) (x++u++y) (x++v++y) :=
  h.lift (fun w => x++w++y) (fun _ _ hh => context_context hh x y)

/-- These are exactly the absorbing-letter and incompatible-arrow equations,
    oriented toward the zero letter. -/
inductive ZeroStep : List (Letter C H) → List (Letter C H) → Prop
  | pair (a b : Letter C H) (h : typeOf a * typeOf b = .zero) : ZeroStep [a,b] [.zero]

theorem Shape.middle_zero : ∀ (a b c : Shape), b ≠ .unit →
    ((a*b)*c = .zero ↔ a*b = .zero ∨ b*c = .zero) := by decide

theorem absorb_zero (w : List (Letter C H)) :
    ReflTransGen (Context ZeroStep) (.zero::w) [.zero] := by
  induction w with
  | nil => exact .refl
  | cons a w ih =>
    apply ReflTransGen.head ?_ ih
    exact Context.apply [] w (ZeroStep.pair .zero a rfl)

/-- Every dirty nonpath, including every occurrence of Omega, has a finite
    zero derivation. No simulation, program call, or confluence is used. -/
theorem zero_reaches {w : List (Letter C H)} (h : shape w = .zero) :
    ReflTransGen (Context ZeroStep) w [.zero] := by
  induction w with
  | nil => cases h
  | cons a w ih =>
    cases w with
    | nil =>
      cases a <;> simp only [shape_singleton,typeOf] at h
      · exact .refl
      all_goals cases h
    | cons b w =>
      have hz : (typeOf a * typeOf b) * shape w = .zero := by
        simpa only [shape_cons,mul_assoc] using h
      rcases (Shape.middle_zero _ _ _ (typeOf_ne_unit b)).mp hz with hp | ht
      · exact ReflTransGen.head (Context.apply [] w (ZeroStep.pair a b hp)) (absorb_zero w)
      · have hh := reaches_context (ih ht) [a] []
        have hh' : ReflTransGen (Context ZeroStep) (a::b::w) [a,.zero] := by simpa using hh
        exact hh'.tail (Context.apply [] [] (ZeroStep.pair a .zero (mul_zero _)))

/-- Additive grade on literal words. The head and boundary letters each have
    grade one, while all cell-tag data is ignored by a supplied base grade. -/
def letterGrade (g : C → ℕ) : Letter C H → ℕ
  | .zero => 0
  | .left c | .right c => g c
  | _ => 1

def grade (g : C → ℕ) (w : List (Letter C H)) : ℕ := (w.map (letterGrade g)).sum

@[simp] theorem grade_nil (g : C → ℕ) : grade g ([] : List (Letter C H)) = 0 := rfl
@[simp] theorem grade_cons (g : C → ℕ) (a : Letter C H) (w : List (Letter C H)) :
    grade g (a::w) = letterGrade g a + grade g w := rfl
@[simp] theorem grade_append (g : C → ℕ) (u v : List (Letter C H)) :
    grade g (u++v) = grade g u + grade g v := by simp [grade]

theorem zeroStep_grade (g : C → ℕ) {u v : List (Letter C H)} (h : ZeroStep u v) :
    grade g v ≤ grade g u := by cases h; simp [grade,letterGrade]

@[simp] theorem grade_headed (g : C → ℕ) (l : List C) (q : H) (r : List C) (lb rb : Bool) :
    grade g (headed l q r lb rb) = (l.map g).sum + 1 + (r.map g).sum +
      (if lb then 1 else 0) + (if rb then 1 else 0) := by
  cases lb <;> cases rb <;> simp [headed,grade,letterGrade,List.map_reverse,List.map_map,Function.comp_def] <;> ac_rfl

end

section
variable {C H : Type*}

 theorem glue_append_of_ne_nil (u : List (Letter C H))
    (cs ds : List (List (Letter C H))) (h : cs ≠ []) :
    glue u (cs++ds) = glue u cs ++ ds := by
  cases cs with
  | nil => exact (h rfl).elim
  | cons c cs => rfl

 theorem cuts_append_leave (u v : List (Letter C H)) :
    cuts (u ++ .leave::v) = cuts (u++[.leave]) ++ cuts v := by
  induction u with
  | nil => rfl
  | cons a u ih =>
    by_cases ha : a = .leave
    · subst a
      simp only [List.cons_append,cuts_leave,ih]
    · simp only [List.cons_append,cuts_cons ha,ih]
      apply glue_append_of_ne_nil
      intro hh
      have := congrArg List.flatten hh
      simp at this

/-- Split an arbitrary left context after its last omega. The finished part
    cannot join the sector containing a subsequently inserted head. -/
theorem split_left_context (x : List (Letter C H)) :
    ∃ p a, x = p++a ∧ (.leave : Letter C H) ∉ a ∧
      (p = [] ∨ ∃ t, p = t++[.leave]) := by
  induction x with
  | nil => exact ⟨[],[],rfl,by simp,.inl rfl⟩
  | cons c x ih =>
    obtain ⟨p,a,rfl,ha,hp⟩ := ih
    rcases hp with rfl | ⟨t,rfl⟩
    · by_cases hc : c = .leave
      · subst c
        exact ⟨[.leave],a,rfl,ha,.inr ⟨[],rfl⟩⟩
      · exact ⟨[],c::a,rfl,by simpa using And.intro (Ne.symm hc) ha,.inl rfl⟩
    · exact ⟨c::(t++[.leave]),a,rfl,ha,.inr ⟨c::t,rfl⟩⟩

/-- One delimiter frame works simultaneously for every nonempty replacement
    with no omega. This lemma makes no path or cleanliness assumption. -/
theorem context_frame (x y : List (Letter C H)) :
    ∃ cs a b ds, (.leave : Letter C H) ∉ a ∧ terminalLeave b ∧
      (∀ u : List (Letter C H), u ≠ [] → .leave ∉ u →
        cuts (x++u++y) = cs ++ (a++u++b)::ds) := by
  obtain ⟨p,a,rfl,ha,hp⟩ := split_left_context x
  have hclosed : ∀ v, cuts (p++v) = cuts p ++ cuts v := by
    intro v
    rcases hp with rfl | ⟨t,rfl⟩
    · rfl
    · simpa only [List.append_assoc,List.singleton_append] using cuts_append_leave t v
  cases hy : cuts y with
  | nil =>
    have hy' : y = [] := by simpa using congrArg List.flatten hy
    subst y
    refine ⟨cuts p,a,[],[],ha,trivial,?_⟩
    intro u hu hn
    simp only [List.append_nil,List.append_assoc]
    rw [hclosed,cuts_append_nonleave a _ ha,cuts_of_noLeave u hn]
    cases u with
    | nil => exact (hu rfl).elim
    | cons c u => simp [glue]
  | cons b ds =>
    have hb : terminalLeave b := terminalLeave_cuts y b (by simp [hy])
    refine ⟨cuts p,a,b,ds,ha,hb,?_⟩
    intro u _ hn
    simp only [List.append_assoc]
    rw [hclosed,cuts_append_nonleave a _ ha,
      cuts_append_nonleave u y hn,hy,glue_assoc]
    simp only [glue,List.append_assoc]

 theorem terminalLeave_append_nonleave (a b : List (Letter C H))
    (ha : .leave ∉ a) (hb : terminalLeave b) : terminalLeave (a++b) := by
  induction a with
  | nil => exact hb
  | cons c a ih =>
    have hc : c ≠ .leave := fun h => ha (by simp [h])
    exact (terminalLeave_cons hc _).2 (ih (fun h => ha (List.mem_cons_of_mem _ h)))

/-- The unique designated head identifies its entire host sector, even when
    the surrounding input is malformed. The only premise is literal pathhood. -/
theorem head_context_form {a b : List (Letter C H)} {q : H}
    (hn : terminalLeave (a++ .head q::b)) (h : shape (a++ .head q::b) ≠ .zero) :
    ∃ (l r : List C) (lb rb : Bool), a = (if lb then [.enter] else []) ++ l.reverse.map .left ∧
      b = r.map .right ++ (if rb then [.leave] else []) := by
  rcases sector_form hn h with hh | ⟨l,z,r,lb,rb,he⟩
  · simp only [heads,List.filterMap_append,List.filterMap_cons] at hh
    simp at hh
  · have hp : (.head q : Letter C H) ∉
        (if lb then [Letter.enter] else []) ++ l.reverse.map .left := by
      cases lb <;> simp
    have hs : (.head q : Letter C H) ∉
        r.map .right ++ (if rb then [Letter.leave] else []) := by
      cases rb <;> simp
    have he' : (if lb then [Letter.enter] else []) ++ l.reverse.map .left ++
        .head z::(r.map .right ++ (if rb then [Letter.leave] else [])) = a++ .head q::b := by
      simpa only [headed,List.append_assoc,List.singleton_append,List.cons_append,List.nil_append] using he.symm
    obtain ⟨ha,_,hb⟩ := (List.append_cons_inj_of_notMem hp hs).mp he'
    exact ⟨l,r,lb,rb,ha.symm,hb.symm⟩

/-- Extract the containing sector in an arbitrary path context. The same
    surrounding sector list works after any head change, or any added left and
    right loops. No claim that sector boundaries survive arbitrary attachment
    of context is built into the statement. -/
theorem head_frame (x y : List (Letter C H)) (q : H)
    (h : shape (x++[.head q]++y) ≠ .zero) :
    ∃ cs ds l r lb rb, ∀ (q' : H) (ls rs : List C),
      cuts (x++ls.map .left++[.head q']++rs.map .right++y) =
        cs ++ [headed (ls.reverse++l) q' (rs++r) lb rb] ++ ds := by
  obtain ⟨cs,a,b,ds,ha,hb,hframe⟩ := context_frame x y
  have hf := hframe [.head q] (by simp) (by simp)
  have hm : shape (a++ .head q::b) ≠ .zero := by
    apply shape_cut_ne_zero h
    simp only [hf,List.mem_append,List.mem_cons]
    exact .inr (.inl (by simp))
  have ht : terminalLeave (a++ .head q::b) :=
    terminalLeave_append_nonleave a _ ha ((terminalLeave_cons (by simp) b).2 hb)
  obtain ⟨l,r,lb,rb,rfl,rfl⟩ := head_context_form ht hm
  refine ⟨cs,ds,l,r,lb,rb,?_⟩
  intro q' ls rs
  have hh := hframe (ls.map .left++[.head q']++rs.map .right) (by simp) (by simp)
  simpa only [headed,List.reverse_append,List.reverse_reverse,List.map_append,
    List.append_assoc,List.singleton_append,List.cons_append,List.nil_append] using hh

 theorem split_right_context (y : List (Letter C H)) :
    ∃ b s, y = b++s ∧ terminalLeave b ∧
      (s = [] ∨ ∃ t, b = t++[.leave]) := by
  induction y with
  | nil => exact ⟨[],[],rfl,trivial,.inl rfl⟩
  | cons c y ih =>
    by_cases hc : c = .leave
    · subst c
      exact ⟨[.leave],y,rfl,rfl,.inr ⟨[],rfl⟩⟩
    · obtain ⟨b,s,rfl,hb,hs⟩ := ih
      refine ⟨c::b,s,rfl,(terminalLeave_cons hc b).2 hb,?_⟩
      rcases hs with rfl | ⟨t,rfl⟩
      · exact .inl rfl
      · exact .inr ⟨c::t,rfl⟩

/-- A two-sided delimiter frame, valid even for replacements which change the
    number of heads or create/delete internal visits to the outer vertex. -/
theorem general_context_frame (x y : List (Letter C H)) :
    ∃ cs a b ds, (.leave : Letter C H) ∉ a ∧ terminalLeave b ∧
      (∀ u, cuts (x++u++y) = cs ++ cuts (a++u++b) ++ ds) := by
  obtain ⟨p,a,rfl,ha,hp⟩ := split_left_context x
  obtain ⟨b,s,rfl,hb,hs⟩ := split_right_context y
  have hclosed : ∀ v, cuts (p++v) = cuts p ++ cuts v := by
    intro v
    rcases hp with rfl | ⟨t,rfl⟩
    · rfl
    · simpa only [List.append_assoc,List.singleton_append] using cuts_append_leave t v
  have hright : ∀ v, cuts (v++b++s) = cuts (v++b) ++ cuts s := by
    intro v
    rcases hs with rfl | ⟨t,rfl⟩
    · simp
    · simpa only [List.append_assoc,List.singleton_append] using cuts_append_leave (v++t) s
  refine ⟨cuts p,a,b,cuts s,ha,hb,?_⟩
  intro u
  rw [show (p++a)++u++(b++s) = p++((a++u)++b++s) by simp [List.append_assoc],
    hclosed,hright]
  simp only [List.append_assoc]

/-- Around a fixed head every path context is exactly an arbitrary prefix of
    finished sectors, an optional alpha and left loops, right loops and an
    optional omega, and an arbitrary suffix of sectors. This uniform literal
    identity is also valid for merge and unmerge replacements. -/
theorem word_frame (x y : List (Letter C H)) (q : H)
    (h : shape (x++[.head q]++y) ≠ .zero) :
    ∃ (cs ds : List (List (Letter C H))) (l r : List C) (lb rb : Bool), ∀ u,
      cuts (x++u++y) = cs ++
        cuts (((if lb then [.enter] else []) ++ l.reverse.map .left) ++ u ++
          (r.map .right ++ (if rb then [.leave] else []))) ++ ds := by
  obtain ⟨cs,a,b,ds,ha,hb,hframe⟩ := general_context_frame x y
  have hf := congrArg List.flatten (hframe [.head q])
  simp only [List.flatten_append,flatten_cuts] at hf
  have hm : shape (a++ .head q::b) ≠ .zero := by
    rw [hf] at h
    have hh := (shape_append_ne_zero h).1
    have hh' := (shape_append_ne_zero hh).2
    simpa using hh'
  have ht : terminalLeave (a++ .head q::b) :=
    terminalLeave_append_nonleave a _ ha ((terminalLeave_cons (by simp) b).2 hb)
  obtain ⟨l,r,lb,rb,rfl,rfl⟩ := head_context_form ht hm
  exact ⟨cs,ds,l,r,lb,rb,hframe⟩

end

section
variable {C H : Type*} [DecidableEq C] [DecidableEq H]

/-- Preprocessing is applied only to headed sectors. Headless pieces retain
    their literal words; no implicit boundary or identity generator is added. -/
def prepareChunk (P : Sector C H → List (Sector C H)) (w : List (Letter C H)) :
    List (List (Letter C H)) :=
  match decode w with
  | none => [w]
  | some v => (P v).map encode

def prepareChunks (P : Sector C H → List (Sector C H))
    (cs : List (List (Letter C H))) : List (List (Letter C H)) := cs.flatMap (prepareChunk P)

def prepare (P : Sector C H → List (Sector C H)) (w : List (Letter C H)) :
    List (List (Letter C H)) := prepareChunks P (cuts w)

@[simp] theorem prepareChunk_encode (P : Sector C H → List (Sector C H)) (v : Sector C H) :
    prepareChunk P (encode v) = (P v).map encode := by simp [prepareChunk]

@[simp] theorem prepareChunks_append (P : Sector C H → List (Sector C H))
    (cs ds : List (List (Letter C H))) :
    prepareChunks P (cs++ds) = prepareChunks P cs ++ prepareChunks P ds := by
  simp [prepareChunks]

 theorem prepareChunks_singleton (P : Sector C H → List (Sector C H)) (v : Sector C H) :
    prepareChunks P [encode v] = (P v).map encode := by simp [prepareChunks]

/-- All ordinary compiler rules can be checked on a sector with arbitrary
    extra zipper cells. This theorem transports those checks into arbitrary
    literal word contexts, without a cleanliness or boundary promise. -/
theorem prepare_context_headed (P : Sector C H → List (Sector C H))
    (x y : List (Letter C H)) (l₁ l₂ r₁ r₂ : List C) (q₁ q₂ : H)
    (h : shape (x++headed l₁ q₁ r₁ false false++y) ≠ .zero)
    (hinv : ∀ (l r : List C) (lb rb : Bool),
      P ⟨l₁++l,q₁,r₁++r,lb,rb⟩ = P ⟨l₂++l,q₂,r₂++r,lb,rb⟩) :
    prepare P (x++headed l₁ q₁ r₁ false false++y) =
      prepare P (x++headed l₂ q₂ r₂ false false++y) := by
  have hb : shape (x++[.head q₁]++y) ≠ .zero := by
    simpa only [shape_append,shape_headed,shape_singleton,typeOf,Bool.false_eq_true,ite_false] using h
  obtain ⟨cs,ds,l,r,lb,rb,hframe⟩ := head_frame x y q₁ hb
  have hf₁ := hframe q₁ l₁.reverse r₁
  have hf₂ := hframe q₂ l₂.reverse r₂
  simp only [List.reverse_reverse] at hf₁ hf₂
  have h₁ : cuts (x++headed l₁ q₁ r₁ false false++y) =
      cs++[encode (⟨l₁++l,q₁,r₁++r,lb,rb⟩ : Sector C H)]++ds := by
    simpa only [headed,encode,Bool.false_eq_true,ite_false,List.nil_append,List.append_nil,
      List.append_assoc] using hf₁
  have h₂ : cuts (x++headed l₂ q₂ r₂ false false++y) =
      cs++[encode (⟨l₂++l,q₂,r₂++r,lb,rb⟩ : Sector C H)]++ds := by
    simpa only [headed,encode,Bool.false_eq_true,ite_false,List.nil_append,List.append_nil,
      List.append_assoc] using hf₂
  simp only [prepare,h₁,h₂,prepareChunks_append,prepareChunks_singleton,hinv]

end

section
variable {C H : Type*}

 theorem prefix_end_enter {a : List (Letter C H)} {l : List C} {lb : Bool}
    (h : a++[.enter] = (if lb then [.enter] else []) ++ l.reverse.map .left) :
    a = [] ∧ l = [] ∧ lb = true := by
  cases l with
  | nil =>
    cases lb with
    | false => simp at h
    | true =>
      refine ⟨?_,rfl,rfl⟩
      apply List.append_left_injective [.enter]
      simpa using h
  | cons c l =>
    have hh := congrArg (fun w : List (Letter C H) => w.reverse.head?) h
    cases lb <;> simp [List.reverse_cons,List.reverse_append] at hh

 theorem suffix_begin_leave {b : List (Letter C H)} {r : List C} {rb : Bool}
    (h : .leave::b = r.map .right ++ (if rb then [.leave] else [])) :
    b = [] ∧ r = [] ∧ rb = true := by
  cases r with
  | nil => cases rb <;> simp_all
  | cons c r => simp at h

 theorem left_boundary_frame (x y : List (Letter C H)) (q : H)
    (h : shape (x++[.enter,.head q]++y) ≠ .zero) :
    ∃ (cs ds : List (List (Letter C H))) (r : List C) (rb : Bool), ∀ q' : H,
      cuts (x++[.enter,.head q']++y) = cs++[headed [] q' r true rb]++ds := by
  obtain ⟨cs,a,b,ds,ha,hb,hframe⟩ := context_frame x y
  have hf := hframe [.enter,.head q] (by simp) (by simp)
  have hm : shape ((a++[.enter])++ .head q::b) ≠ .zero := by
    apply shape_cut_ne_zero h
    simp only [hf,List.mem_append,List.mem_cons]
    exact .inr (.inl (by simp))
  have ht : terminalLeave ((a++[.enter])++ .head q::b) := by
    apply terminalLeave_append_nonleave
    · simpa using ha
    · exact (terminalLeave_cons (by simp) b).2 hb
  obtain ⟨l,r,lb,rb,hl,hr⟩ := head_context_form ht hm
  obtain ⟨rfl,rfl,rfl⟩ := prefix_end_enter hl
  subst b
  refine ⟨cs,ds,r,rb,?_⟩
  intro q'
  simpa [headed,List.append_assoc] using hframe [.enter,.head q'] (by simp) (by simp)

 theorem right_boundary_frame (x y : List (Letter C H)) (q : H)
    (h : shape (x++[.head q,.leave]++y) ≠ .zero) :
    ∃ (cs ds : List (List (Letter C H))) (l : List C) (lb : Bool), ∀ q' : H,
      cuts (x++[.head q',.leave]++y) = cs++[headed l q' [] lb true]++ds := by
  obtain ⟨p,a,rfl,ha,hp⟩ := split_left_context x
  have hclosed : ∀ v, cuts (p++v) = cuts p ++ cuts v := by
    intro v
    rcases hp with rfl | ⟨t,rfl⟩
    · rfl
    · simpa only [List.append_assoc,List.singleton_append] using cuts_append_leave t v
  have hf : ∀ q' : H, cuts ((p++a)++[.head q',.leave]++y) =
      cuts p ++ (a++[.head q',.leave])::cuts y := by
    intro q'
    simp only [List.append_assoc,List.cons_append,List.nil_append]
    rw [hclosed,cuts_append_nonleave a _ ha,cuts_cons (by simp),cuts_leave]
    simp [glue]
  have hm : shape (a++ .head q::[.leave]) ≠ .zero := by
    apply shape_cut_ne_zero h
    simp only [hf,List.mem_append,List.mem_cons]
    exact .inr (.inl trivial)
  have ht : terminalLeave (a++ .head q::[.leave]) :=
    terminalLeave_append_nonleave a _ ha (by trivial)
  obtain ⟨l,r,lb,rb,hl,hr⟩ := head_context_form ht hm
  obtain ⟨_,rfl,rfl⟩ := suffix_begin_leave hr
  subst a
  refine ⟨cuts p,cuts y,l,lb,?_⟩
  intro q'
  simpa [headed,List.append_assoc] using hf q'

variable [DecidableEq C] [DecidableEq H]

theorem prepare_context_left_boundary (P : Sector C H → List (Sector C H))
    (x y : List (Letter C H)) (q₁ q₂ : H)
    (h : shape (x++[.enter,.head q₁]++y) ≠ .zero)
    (hinv : ∀ (r : List C) (rb : Bool), P ⟨[],q₁,r,true,rb⟩ = P ⟨[],q₂,r,true,rb⟩) :
    prepare P (x++[.enter,.head q₁]++y) = prepare P (x++[.enter,.head q₂]++y) := by
  obtain ⟨cs,ds,r,rb,hframe⟩ := left_boundary_frame x y q₁ h
  simp only [prepare,hframe,prepareChunks_append]
  change prepareChunks P cs ++ prepareChunks P [encode ⟨[],q₁,r,true,rb⟩] ++ prepareChunks P ds =
    prepareChunks P cs ++ prepareChunks P [encode ⟨[],q₂,r,true,rb⟩] ++ prepareChunks P ds
  rw [prepareChunks_singleton,prepareChunks_singleton,hinv]

theorem prepare_context_right_boundary (P : Sector C H → List (Sector C H))
    (x y : List (Letter C H)) (q₁ q₂ : H)
    (h : shape (x++[.head q₁,.leave]++y) ≠ .zero)
    (hinv : ∀ (l : List C) (lb : Bool), P ⟨l,q₁,[],lb,true⟩ = P ⟨l,q₂,[],lb,true⟩) :
    prepare P (x++[.head q₁,.leave]++y) = prepare P (x++[.head q₂,.leave]++y) := by
  obtain ⟨cs,ds,l,lb,hframe⟩ := right_boundary_frame x y q₁ h
  simp only [prepare,hframe,prepareChunks_append]
  change prepareChunks P cs ++ prepareChunks P [encode ⟨l,q₁,[],lb,true⟩] ++ prepareChunks P ds =
    prepareChunks P cs ++ prepareChunks P [encode ⟨l,q₂,[],lb,true⟩] ++ prepareChunks P ds
  rw [prepareChunks_singleton,prepareChunks_singleton,hinv]

end

variable {C H : Type*}

 theorem cuts_join_headed (l r : List C) (q q' : H) (lb rb : Bool) :
    cuts (headed l q [] lb true ++ headed [] q' r true rb) =
      [headed l q [] lb true,headed [] q' r true rb] := by
  let a := (if lb then [Letter.enter] else []) ++ l.reverse.map .left ++ [Letter.head q]
  have ha : headed l q [] lb true = a++[.leave] := by simp [a,headed]
  rw [ha,List.append_assoc,List.singleton_append,cuts_append_leave,←ha,cuts_headed,cuts_headed]
  rfl

variable [DecidableEq C] [DecidableEq H]

/-- Literal merge invariance in every well-typed context, including incomplete
    and dirty outer sectors. The two visits to the outer vertex are explicit. -/
theorem prepare_context_merge (P : Sector C H → List (Sector C H))
    (x y : List (Letter C H)) (q p : H) (c d : C)
    (h : shape (x++[.head q,.leave,.enter,.head q]++y) ≠ .zero)
    (hinv : ∀ (l r : List C) (lb rb : Bool),
      P ⟨c::l,p,d::r,lb,rb⟩ = P ⟨l,q,[],lb,true⟩ ++ P ⟨[],q,r,true,rb⟩) :
    prepare P (x++[.head q,.leave,.enter,.head q]++y) =
      prepare P (x++[.left c,.head p,.right d]++y) := by
  have hb : shape (x++[.head q]++y) ≠ .zero := by
    simpa only [shape_append,shape_cons,shape_nil,typeOf,mul_unit,path_mul_path,
      ite_true] using h
  obtain ⟨cs,ds,l,r,lb,rb,hframe⟩ := word_frame x y q hb
  have hf₁ : cuts (x++[.head q,.leave,.enter,.head q]++y) =
      cs++[encode ⟨l,q,[],lb,true⟩,encode ⟨[],q,r,true,rb⟩]++ds := by
    rw [hframe]
    have he : ((if lb then [Letter.enter] else [])++l.reverse.map .left) ++
        [.head q,.leave,.enter,.head q] ++ (r.map .right++(if rb then [.leave] else [])) =
        headed l q [] lb true ++ headed [] q r true rb := by
      simp [headed,List.append_assoc]
    rw [he,cuts_join_headed]
    rfl
  have hf₂ : cuts (x++[.left c,.head p,.right d]++y) =
      cs++[encode ⟨c::l,p,d::r,lb,rb⟩]++ds := by
    rw [hframe]
    have he : ((if lb then [Letter.enter] else [])++l.reverse.map .left) ++
        [.left c,.head p,.right d] ++ (r.map .right++(if rb then [.leave] else [])) =
        headed (c::l) p (d::r) lb rb := by
      simp [headed,List.reverse_cons,List.map_append,List.append_assoc]
    rw [he,cuts_headed]
    rfl
  unfold prepare
  rw [hf₁,hf₂]
  simp only [prepareChunks,List.flatMap_append,List.flatMap_cons,
    List.flatMap_nil,prepareChunk_encode,List.append_nil,hinv,List.map_append,
    List.append_assoc]

end FiniteAlgebraicEnvelopes.Compiler.Path

/- Maximal full-raw-run normalization and its one exceptional equation,
   the finite compiler. Nonraw sectors are opaque separators here. -/

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteCompiler_Normalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Raw-run folds, full word compilation, partial budgets, and bounded normalization.
-/

namespace FiniteAlgebraicEnvelopes.Compiler.RawRuns
variable {C S : Type*}

/-- Budget laws are used only where the *unreduced* concatenation has bounded
    length. They are exactly the totality/length/context interface of the source. -/
structure Budget (f : List S → List S) (m : ℕ) : Prop where
  length : ∀ w, w.length ≤ m → (f w).length ≤ w.length
  context : ∀ x w y, (x++w++y).length ≤ m → f (x++f w++y) = f (x++w++y)

variable {f : List S → List S} {m : ℕ}

/-- The two bracketings of three adjacent raw inputs agree inside the same
    budget. No idempotence assumption on raw singleton sectors is made. -/
theorem triple (h : Budget f m) (x y z : List S)
    (hm : (x++y++z).length ≤ m) : f (x++f (y++z)) = f (f (x++y)++z) := by
  have h₁ := h.context x (y++z) [] (by simpa [List.append_assoc] using hm)
  have h₂ := h.context [] (x++y) z (by simpa using hm)
  simp only [List.append_nil,List.nil_append,List.append_assoc] at h₁ h₂ ⊢
  exact h₁.trans h₂.symm

end FiniteAlgebraicEnvelopes.Compiler.RawRuns

namespace FiniteAlgebraicEnvelopes.Compiler.Scan
variable {H B T K : Type*}

namespace Literal
open _root_.OAI.FiniteAlgebraicEnvelopes.Compiler.Path

/-- Zipper fragments of a literal cell instruction, before and after the
    specified cross/stay move. -/
def inLeft (d : Direction) (c : B×T) : List (B×T) := if d = .left then [c] else []
def inRight (d : Direction) (c : B×T) : List (B×T) := if d = .right then [c] else []
def outLeft (d : Direction) (cross : Bool) (c : B×T) : List (B×T) :=
  if (d = .left ∧ cross = false) ∨ (d = .right ∧ cross = true) then [c] else []
def outRight (d : Direction) (cross : Bool) (c : B×T) : List (B×T) :=
  if (d = .right ∧ cross = false) ∨ (d = .left ∧ cross = true) then [c] else []

end Literal
end FiniteAlgebraicEnvelopes.Compiler.Scan

namespace FiniteAlgebraicEnvelopes.Compiler.Path
variable {C H : Type*}

theorem context_headed {R : List (Letter C H) → List (Letter C H) → Prop}
    {l₁ l₂ r₁ r₂ : List C} {q₁ q₂ : H}
    (h : R (headed l₁ q₁ r₁ false false) (headed l₂ q₂ r₂ false false))
    (l r : List C) (lb rb : Bool) :
    Context R (headed (l₁++l) q₁ (r₁++r) lb rb)
      (headed (l₂++l) q₂ (r₂++r) lb rb) := by
  have hh := Context.apply ((if lb then [.enter] else []) ++ l.reverse.map .left)
      (r.map .right ++ (if rb then [.leave] else [])) h
  simp only [headed,Bool.false_eq_true,ite_false,List.nil_append,List.append_nil,
    List.reverse_append,List.map_append,List.append_assoc] at hh ⊢
  exact hh

end FiniteAlgebraicEnvelopes.Compiler.Path

namespace FiniteAlgebraicEnvelopes.Compiler.Path
variable {C H : Type*}

theorem context_mono {R T : List (Letter C H) → List (Letter C H) → Prop}
    {u v : List (Letter C H)} (h : Context R u v) (ht : ∀ a b, R a b → T a b) : Context T u v := by
  cases h with
  | apply x y h => exact .apply x y (ht _ _ h)

open Relation
theorem context_symm {R : List (Letter C H) → List (Letter C H) → Prop}
    {u v : List (Letter C H)} (h : Context (SymmGen R) u v) : Context (SymmGen R) v u := by
  cases h with
  | apply x y h => exact .apply x y (Or.symm h)

end FiniteAlgebraicEnvelopes.Compiler.Path

namespace FiniteAlgebraicEnvelopes.Compiler.RawRuns
variable {C S : Type*}

/-- A nonraw literal sector, an unchanged singleton raw sector, or a genuine
    program call on an entire maximal raw run. -/
inductive Action (C S : Type*)
  | keep (c : C)
  | raw (w : List S)
  | call (w : List S)
  deriving DecidableEq

end FiniteAlgebraicEnvelopes.Compiler.RawRuns

namespace FiniteAlgebraicEnvelopes.Compiler

/-- Literal domain/length/context premises of the finite compiler's bounded theorem.
    These are conditions on the given partial program, not a total replacement. -/
structure PartialBudget {S : Type*} (f : List S → Part (List S)) (m : ℕ) : Prop where
  total : ∀ w, w.length ≤ m → (f w).Dom
  length : ∀ w, w.length ≤ m → ∀ out ∈ f w, out.length ≤ w.length
  context : ∀ x w y, (x++w++y).length ≤ m →
    ∀ out ∈ f w, f (x++out++y) = f (x++w++y)

/-- Used only to state the bounded correctness proof of the partial algorithm.
    It has no place in its definition or in its claimed effective implementation. -/
noncomputable def partValue {S : Type*} (p : Part (List S)) : List S := by
  classical
  exact if h : p.Dom then p.get h else []

end FiniteAlgebraicEnvelopes.Compiler

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteCompiler_Effectivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Primitive recursive encodings and effective finite compiler data.
-/

/- Effectivity dependencies for the source compiler and its bounded recursive
   evaluator. No partial function is completed by classical choice. -/
namespace FiniteAlgebraicEnvelopes.Effect
variable {α β : Type*}

def traverse (f : α →. β) : List α →. List β
  | [] => Part.some []
  | a::l => (f a).bind fun b => (traverse f l).map (b::·)

def traverseStep (f : α →. β) : List α × List β →. List β ⊕ (List α × List β)
  | ([],acc) => Part.some (.inl acc)
  | (a::l,acc) => (f a).map fun b => .inr (l,acc++[b])

theorem traverse_fix (f : α →. β) (l : List α) (acc : List β) :
    PFun.fix (traverseStep f) (l,acc) = (traverse f l).map (acc++·) := by
  induction l generalizing acc with
  | nil =>
    apply Part.ext
    intro out
    rw [PFun.mem_fix_iff]
    simp [traverseStep,traverse]
  | cons a l ih =>
    apply Part.ext
    intro out
    rw [PFun.mem_fix_iff]
    simp only [traverseStep,Part.mem_map_iff,Sum.inr.injEq,
      Sum.inr_ne_inl,exists_false,and_false,false_or]
    constructor
    · rintro ⟨⟨l',acc'⟩,⟨b,hb,he⟩,h⟩
      rcases he with ⟨rfl,rfl⟩
      rw [ih] at h
      rcases (Part.mem_map_iff _).mp h with ⟨bs,hbs,rfl⟩
      refine ⟨b::bs,Part.mem_bind_iff.mpr ⟨b,hb,(Part.mem_map_iff _).mpr ⟨bs,hbs,rfl⟩⟩,?_⟩
      simp [List.append_assoc]
    · intro h
      rcases h with ⟨bs,hbs,rfl⟩
      change bs ∈ (f a).bind (fun b => (traverse f l).map (b::·)) at hbs
      rcases Part.mem_bind_iff.mp hbs with ⟨b,hb,hrest⟩
      rcases (Part.mem_map_iff _).mp hrest with ⟨tail,htail,rfl⟩
      refine ⟨(l,acc++[b]),⟨b,hb,rfl⟩,?_⟩
      rw [ih]
      apply (Part.mem_map_iff _).mpr
      exact ⟨tail,htail,by simp [List.append_assoc]⟩

variable [Primcodable α] [Primcodable β]

theorem partrec_traverse {f : α →. β} (hf : Partrec f) : Partrec (traverse f) := by
  have hs : Partrec (traverseStep f) := by
    have ht : Computable (fun s : List α × List β => s.1.head?) :=
      Primrec.list_head?.to_comp.comp Computable.fst
    have hb : Partrec₂ (fun (s : List α × List β) (a : α) =>
        (f a).map fun b => (Sum.inr (s.1.tail,s.2++[b]) : List β ⊕ (List α × List β))) := by
      change Partrec (fun sa : (List α × List β) × α =>
        (f sa.2).map fun b => (Sum.inr (sa.1.1.tail,sa.1.2++[b]) : List β ⊕ (List α × List β)))
      apply (hf.comp Computable.snd).map
      exact (Computable.sumInr.comp
        ((Primrec.list_tail.to_comp.comp (Computable.fst.comp (Computable.fst.comp Computable.fst))).pair
        (Primrec.list_append.to_comp.comp
          (Computable.snd.comp (Computable.fst.comp Computable.fst))
          (Primrec.list_cons.to_comp.comp Computable.snd (Computable.const []))))).to₂
    exact (Partrec.optionCasesOn_right ht
      (Computable.sumInl.comp Computable.snd) hb).of_eq
      (by intro s; rcases s with ⟨l,acc⟩; cases l <;> rfl)
  exact ((Partrec.fix hs).comp (Computable.id.pair (Computable.const []))).of_eq fun l => by
    simpa only [id_eq,List.nil_append,Part.map_id' (fun _ => rfl)] using traverse_fix f l []

end FiniteAlgebraicEnvelopes.Effect

namespace FiniteAlgebraicEnvelopes.Compiler.RawRuns
variable {C S : Type*}

def Action.code : Action C S ≃ C ⊕ (List S ⊕ List S) where
  toFun
    | .keep c => .inl c
    | .raw x => .inr (.inl x)
    | .call x => .inr (.inr x)
  invFun
    | .inl c => .keep c
    | .inr (.inl x) => .raw x
    | .inr (.inr x) => .call x
  left_inv a := by cases a <;> rfl
  right_inv a := by rcases a with c | (x|x) <;> rfl

instance instPrimcodableAction [Primcodable C] [Primcodable S] : Primcodable (Action C S) :=
  Primcodable.ofEquiv _ Action.code

variable [Primcodable C] [Primcodable S]

 theorem Action.primrec_code : Primrec (Action.code (C := C) (S := S)) := Primrec.of_equiv
 theorem Action.primrec_decode : Primrec (Action.code (C := C) (S := S)).symm := Primrec.of_equiv_symm
 theorem Action.primrec_keep : Primrec (Action.keep (C := C) (S := S)) :=
  (Action.primrec_decode.comp Primrec.sumInl).of_eq fun _ => rfl
 theorem Action.primrec_raw : Primrec (Action.raw (C := C) (S := S)) :=
  (Action.primrec_decode.comp (Primrec.sumInr.comp Primrec.sumInl)).of_eq fun _ => rfl
 theorem Action.primrec_call : Primrec (Action.call (C := C) (S := S)) :=
  (Action.primrec_decode.comp (Primrec.sumInr.comp Primrec.sumInr)).of_eq fun _ => rfl

 theorem Action.primrec_cases {α β : Type*} [Primcodable α] [Primcodable β]
    {f : α → Action C S} {k : α → C → β} {r t : α → List S → β}
    (hf : Primrec f) (hk : Primrec₂ k) (hr : Primrec₂ r) (ht : Primrec₂ t) :
    Primrec (fun a => match f a with | .keep c => k a c | .raw x => r a x | .call x => t a x) := by
  have hh : Primrec₂ (fun a (b : List S ⊕ List S) => b.elim (r a) (t a)) :=
    (Primrec.sumCasesOn Primrec.snd
      (hr.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂
      (ht.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂).to₂
  exact (Primrec.sumCasesOn (Action.primrec_code.comp hf) hk hh).of_eq fun a => by
    cases f a <;> rfl

end FiniteAlgebraicEnvelopes.Compiler.RawRuns

namespace FiniteAlgebraicEnvelopes.Effect.Graph
open Relation
variable {α : Type*} [DecidableEq α]

def expand (r : α → α → Bool) (u s : List α) : List α :=
  s ++ u.filter (fun b => s.any (fun a => r a b || r b a))

def search (r : α → α → Bool) (u : List α) (a : α) : ℕ → List α
  | 0 => [a]
  | n+1 => expand r u (search r u a n)

omit [DecidableEq α] in
@[simp] theorem mem_expand (r : α → α → Bool) (u s : List α) (b : α) :
    b ∈ expand r u s ↔ b ∈ s ∨ b ∈ u ∧ ∃ a ∈ s, r a b = true ∨ r b a = true := by
  simp [expand]

omit [DecidableEq α] in
theorem search_sub (r : α → α → Bool) {u : List α} {a : α} (ha : a ∈ u) (n : ℕ) :
    ∀ b ∈ search r u a n, b ∈ u := by
  induction n with
  | zero => simpa [search] using ha
  | succ n ih =>
    intro b hb
    rcases (mem_expand r u _ b).mp hb with hb | ⟨hb,_⟩
    · exact ih b hb
    · exact hb

theorem search_mono (r : α → α → Bool) (u : List α) (a : α) :
    Monotone (fun n => (search r u a n).toFinset) := by
  apply monotone_nat_of_le_succ
  intro n b hb
  simp only [List.mem_toFinset] at hb ⊢
  exact (mem_expand r u _ b).mpr (Or.inl hb)

theorem expand_ext (r : α → α → Bool) (u : List α) {s t : List α}
    (h : s.toFinset = t.toFinset) : (expand r u s).toFinset = (expand r u t).toFinset := by
  have hh : ∀ a, a ∈ s ↔ a ∈ t := fun a => by
    simpa only [List.mem_toFinset] using Finset.ext_iff.mp h a
  ext b
  simp only [List.mem_toFinset,mem_expand,hh]

theorem search_stable (r : α → α → Bool) {u : List α} {a : α} (ha : a ∈ u) :
    (search r u a (u.length+1)).toFinset = (search r u a u.length).toFinset := by
  have hs : ∀ n, (search r u a n).toFinset.card ≤ u.length := by
    intro n
    exact (Finset.card_le_card (fun b hb => by
      simp only [List.mem_toFinset] at hb ⊢
      exact search_sub r ha n b hb)).trans (List.toFinset_card_le u)
  have hm : Monotone (fun n => (search r u a n).toFinset.card) :=
    fun _ _ h => Finset.card_le_card (search_mono r u a h)
  have hstep : ∀ n, (search r u a n).toFinset.card = (search r u a (n+1)).toFinset.card →
      (search r u a (n+1)).toFinset.card = (search r u a (n+2)).toFinset.card := by
    intro n hn
    have he := Finset.eq_of_subset_of_card_le (search_mono r u a (Nat.le_succ n)) hn.ge
    exact congrArg Finset.card (expand_ext r u he)
  exact (Finset.eq_of_subset_of_card_le
    (search_mono r u a (Nat.le_succ u.length))
    (Nat.stabilises_of_monotone hm hs hstep (Nat.le_succ _)).le).symm

def component (r : α → α → Bool) (u : List α) (a : α) : List α := search r u a u.length

omit [DecidableEq α] in
theorem mem_search_connected (r : α → α → Bool) (u : List α) (a : α) (n : ℕ)
    {b : α} (hb : b ∈ search r u a n) : EqvGen (fun a b => r a b = true) a b := by
  induction n generalizing b with
  | zero =>
    have : b = a := by simpa [search] using hb
    subst b
    exact .refl _
  | succ n ih =>
    rcases (mem_expand r u _ b).mp hb with hb | ⟨_,c,hc,hcb | hbc⟩
    · exact ih hb
    · exact .trans _ _ _ (ih hc) (.rel _ _ hcb)
    · exact .trans _ _ _ (ih hc) (.symm _ _ (.rel _ _ hbc))

theorem mem_component_iff (r : α → α → Bool) {u : List α} {a b : α} (ha : a ∈ u)
    (hclosed : ∀ c ∈ u, ∀ d, (r c d = true ∨ r d c = true) → d ∈ u) :
    b ∈ component r u a ↔ EqvGen (fun a b => r a b = true) a b := by
  constructor
  · exact mem_search_connected r u a u.length
  · intro h
    have hh : ReflTransGen (SymmGen (fun a b => r a b = true)) a b := by
      rw [EqvGen.reflTransGen_symmGen]; exact h
    clear h
    induction hh with
    | refl =>
      have := search_mono r u a (Nat.zero_le u.length)
        (show a ∈ (search r u a 0).toFinset by simp [search])
      simpa only [List.mem_toFinset,component] using this
    | @tail c d hp hs ih =>
      have hc := search_sub r ha u.length c ih
      have hed : r c d = true ∨ r d c = true := hs
      have hd := hclosed c hc d hed
      have hm := (mem_expand r u _ d).mpr (Or.inr ⟨hd,c,ih,hed⟩)
      have he : d ∈ (search r u a (u.length+1)).toFinset := List.mem_toFinset.mpr hm
      rw [search_stable r ha] at he
      exact List.mem_toFinset.mp he

variable [Primcodable α]

omit [DecidableEq α] in
 theorem primrec_listAny {β : Type*} [Primcodable β]
    {f : β → List α} {p : β → α → Bool} (hf : Primrec f) (hp : Primrec₂ p) :
    Primrec (fun b => (f b).any (p b)) := by
  exact (Primrec.list_foldr hf (Primrec.const false)
    (Primrec.or.comp (hp.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂).of_eq fun b => by
    induction f b <;> simp_all

omit [DecidableEq α] in
 theorem primrec_listFilter {β : Type*} [Primcodable β]
    {f : β → List α} {p : β → α → Bool} (hf : Primrec f) (hp : Primrec₂ p) :
    Primrec (fun b => (f b).filter (p b)) := by
  exact (Primrec.listFilterMap hf
    (Primrec.cond hp (Primrec.option_some.comp Primrec.snd) (Primrec.const none)).to₂).of_eq
    fun b => by
      simp only [Bool.cond_eq_ite]
      induction f b with
      | nil => rfl
      | cons a l ih => cases h : p b a <;> simp [h,ih]

end FiniteAlgebraicEnvelopes.Effect.Graph

namespace FiniteAlgebraicEnvelopes.Compiler.Scan
open FiniteAlgebraicEnvelopes.Effect.Graph
variable {H B T : Type*}

variable [Primcodable H] [Primcodable B] [Primcodable T]

variable [Fintype H] [Fintype B] [Fintype T]

-- All finite choices below are literal lists. No finset or finite-connectivity
-- decision is used as a computability oracle.
noncomputable def finiteList (α : Type*) [Fintype α] : List α := (Finset.univ : Finset α).toList

@[simp] theorem mem_finiteList {α : Type*} [Fintype α] (a : α) : a ∈ finiteList α := by
  classical
  simp [finiteList]

noncomputable def wordList (α : Type*) [Fintype α] : ℕ → List (List α)
  | 0 => [[]]
  | n+1 => [] :: (finiteList α).flatMap (fun a => (wordList α n).map (a::·))

@[simp] theorem mem_wordList {α : Type*} [Fintype α] (n : ℕ) (w : List α) :
    w ∈ wordList α n ↔ w.length ≤ n := by
  induction n generalizing w with
  | zero => simp [wordList]
  | succ n ih =>
    cases w with
    | nil => simp [wordList]
    | cons a w => simp [wordList,ih]

 theorem primrec_wordList {α : Type*} [Fintype α] [Primcodable α] : Primrec (wordList α) := by
  exact (Primrec.nat_rec₁ [[]]
    (Primrec.list_cons.comp (Primrec.const [])
      (Primrec.list_flatMap (Primrec.const (finiteList α))
        (Primrec.list_map (Primrec.snd.comp Primrec.fst)
          (Primrec.list_cons.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂).to₂)).to₂).of_eq
    fun n => by induction n <;> simp_all [wordList]

end FiniteAlgebraicEnvelopes.Compiler.Scan

namespace FiniteAlgebraicEnvelopes.Compiler
variable {H T : Type*}

def Instruction.code : Instruction H T ≃ H × T × Bool where
  toFun i := (i.head,i.tag,i.cross)
  invFun p := ⟨p.1,p.2.1,p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance instPrimcodableInstruction [Primcodable H] [Primcodable T] : Primcodable (Instruction H T) :=
  Primcodable.ofEquiv _ Instruction.code

theorem Instruction.primrec_head [Primcodable H] [Primcodable T] :
    Primrec (Instruction.head (Head := H) (Tag := T)) := Primrec.fst.comp Primrec.of_equiv

theorem Instruction.primrec_tag [Primcodable H] [Primcodable T] :
    Primrec (Instruction.tag (Head := H) (Tag := T)) :=
  Primrec.fst.comp (Primrec.snd.comp Primrec.of_equiv)

theorem Instruction.primrec_cross [Primcodable H] [Primcodable T] :
    Primrec (Instruction.cross (Head := H) (Tag := T)) :=
  Primrec.snd.comp (Primrec.snd.comp Primrec.of_equiv)
end FiniteAlgebraicEnvelopes.Compiler

namespace FiniteAlgebraicEnvelopes.Effect
open FiniteAlgebraicEnvelopes.Effect.Graph
variable {α : Type*} [Primcodable α] [DecidableEq α]

 def priorityList (p q : α → Bool) (s : List α) : List α :=
  if (s.filter p).isEmpty then
    if (s.filter q).isEmpty then s else s.filter q
  else s.filter p

omit [Primcodable α] in
 theorem priorityList_toFinset (p q : α → Bool) (s : List α) :
    (priorityList p q s).toFinset =
      Compiler.prioritySet (fun a => p a = true) (fun a => q a = true) s.toFinset := by
  have hp : (s.filter p).isEmpty = true ↔ ¬ (s.toFinset.filter (fun a => p a = true)).Nonempty := by
    simp
  have hq : (s.filter q).isEmpty = true ↔ ¬ (s.toFinset.filter (fun a => q a = true)).Nonempty := by
    simp
  simp only [priorityList,Compiler.prioritySet,hp,hq]
  split_ifs <;> simp_all

 theorem primrec_listIsEmpty : Primrec (List.isEmpty (α := α)) :=
  (Primrec.eq.decide.comp Primrec.id (Primrec.const [])).of_eq fun l => by
    cases l <;> simp

 theorem primrec_priorityList {p q : α → Bool} (hp : Primrec p) (hq : Primrec q) :
    Primrec (priorityList p q) := by
  have hf := primrec_listFilter Primrec.id (hp.comp Primrec.snd).to₂
  have hg := primrec_listFilter Primrec.id (hq.comp Primrec.snd).to₂
  unfold priorityList
  simp only [← Bool.cond_eq_ite]
  exact Primrec.cond (primrec_listIsEmpty.comp hf)
    (Primrec.cond (primrec_listIsEmpty.comp hg) Primrec.id hg) hf

variable [LinearOrder α]

omit [DecidableEq α] in
 theorem primrec_listMin (hle : PrimrecRel (fun a b : α => a ≤ b)) :
    Primrec (List.min? (α := α)) := by
  have hmin : Primrec₂ (min : α → α → α) := by
    exact (Primrec.ite hle Primrec.fst Primrec.snd).of_eq fun p => by
      simp only [min_def]
  have hfold : Primrec₂ (fun (_ : List α) (p : α × List α) => some (p.2.foldl min p.1)) := by
    exact (Primrec.option_some.comp (Primrec.list_foldl (Primrec.snd.comp Primrec.snd)
      (Primrec.fst.comp Primrec.snd) (hmin.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd)).to₂)).to₂
  exact (Primrec.list_casesOn Primrec.id (Primrec.const none) hfold).of_eq fun l =>
    by cases l <;> rfl

omit [Primcodable α] in
 theorem minList_eq (s : List α) (t : Finset α) (h : t.Nonempty)
    (he : s.toFinset = t) (a : α) : s.min?.getD a = t.min' h := by
  have hm : s.min? = some (t.min' h) := by
    rw [List.min?_eq_some_iff]
    constructor
    · rw [← List.mem_toFinset,he]; exact Finset.min'_mem _ _
    · intro b hb
      exact Finset.min'_le _ _ (he ▸ List.mem_toFinset.mpr hb)
  rw [hm]; rfl

end FiniteAlgebraicEnvelopes.Effect

namespace FiniteAlgebraicEnvelopes.Effect
@[instance_reducible] noncomputable def finitePrimcodable (α : Type*) [Fintype α] : Primcodable α :=
  Primcodable.ofEquiv (Fin (Fintype.card α)) (Fintype.equivFin α)

@[instance_reducible] def codeOrder (α : Type*) [Primcodable α] : LinearOrder α :=
  LinearOrder.lift' Encodable.encode Encodable.encode_injective

theorem primrec_codeOrder (α : Type*) [Primcodable α] :
    letI := codeOrder α
    PrimrecRel (fun a b : α => a ≤ b) :=
  Primrec.nat_le.comp (Primrec.encode.comp Primrec.fst) (Primrec.encode.comp Primrec.snd)
end FiniteAlgebraicEnvelopes.Effect

namespace FiniteAlgebraicEnvelopes.Compiler.Path
open FiniteAlgebraicEnvelopes.Effect
variable {C H : Type*}

variable [Primcodable C] [Primcodable H]

variable [Fintype C] [Fintype H] [DecidableEq C] [DecidableEq H]
noncomputable instance instPrimcodableShape : Primcodable Shape := finitePrimcodable _

end FiniteAlgebraicEnvelopes.Compiler.Path

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteCompiler_Rewriting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Newman normalization, block coding, canonical representatives, and static tests.
-/

/- Rewriting layer for the self-reference construction.  No assumptions on
   either main theorem are introduced here. -/
namespace FiniteAlgebraicEnvelopes.Bootstrap

section
open Relation

section Newman
variable {α : Type*} (R : α → α → Prop)

def Irreducible (a : α) : Prop := ∀ b, ¬ R a b

theorem exists_irreducible (wf : WellFounded (flip R)) (a : α) :
    ∃ b, ReflTransGen R a b ∧ Irreducible R b := by
  classical
  induction a using wf.induction with
  | h a ih =>
    by_cases ha : Irreducible R a
    · exact ⟨a, .refl, ha⟩
    · obtain ⟨b, hab⟩ := not_forall.mp ha
      have hab : R a b := Classical.not_not.mp hab
      obtain ⟨c, hbc, hc⟩ := ih b hab
      exact ⟨c, (ReflTransGen.single hab).trans hbc, hc⟩

theorem irreducible_reaches {a b : α} (ha : Irreducible R a)
    (hab : ReflTransGen R a b) : a = b := by
  rcases hab.cases_head with hab | ⟨c,hac,_⟩
  · exact hab
  · exact False.elim (ha c hac)

end Newman

variable {S : Type*}

/-- One directed rule in an arbitrary two-sided context. -/
inductive Step (rules : List (List S × List S)) : List S → List S → Prop
  | apply {u v} (h : (u,v) ∈ rules) (x y) : Step rules (x++u++y) (x++v++y)

abbrev Steps (rules : List (List S × List S)) := ReflTransGen (Step rules)

theorem step_context {rules : List (List S × List S)} {u v : List S}
    (h : Step rules u v) (x y : List S) : Step rules (x++u++y) (x++v++y) := by
  cases h with
  | apply h a b => simpa only [List.append_assoc] using Step.apply h (x++a) (b++y)

theorem steps_context {rules : List (List S × List S)} {u v : List S}
    (h : Steps rules u v) (x y : List S) : Steps rules (x++u++y) (x++v++y) :=
  h.lift (fun w => x++w++y) (fun _ _ h => step_context h x y)

theorem lex_append_suffix {r : S → S → Prop} {u v : List S}
    (h : List.Lex r u v) (hlen : u.length = v.length) (y : List S) :
    List.Lex r (u++y) (v++y) := by
  induction h with
  | nil => simp at hlen
  | rel h => exact .rel h
  | cons h ih => exact .cons (ih (by simpa using hlen))

theorem shortlex_context {r : S → S → Prop} {u v : List S}
    (h : List.Shortlex r u v) (x y : List S) :
    List.Shortlex r (x++u++y) (x++v++y) := by
  simp only [List.append_assoc]
  apply List.Shortlex.append_left (s := x)
  rcases List.shortlex_def.mp h with h | ⟨hl,h⟩
  · apply List.Shortlex.of_length_lt
    simpa using h
  · exact List.Shortlex.of_lex (by simp [hl]) (lex_append_suffix h hl y)

theorem step_shortlex {r : S → S → Prop} {rules : List (List S × List S)}
    (dec : ∀ p ∈ rules, List.Shortlex r p.2 p.1) {u v : List S}
    (h : Step rules u v) : List.Shortlex r v u := by
  cases h with
  | apply hm x y => exact shortlex_context (dec _ hm) x y

theorem steps_length {r : S → S → Prop} {rules : List (List S × List S)}
    (dec : ∀ p ∈ rules, List.Shortlex r p.2 p.1) {u v : List S}
    (h : Steps rules u v) : v.length ≤ u.length := by
  induction h with
  | refl => rfl
  | tail huv hvw ih =>
    have hh := List.shortlex_def.mp (step_shortlex dec hvw)
    omega

theorem steps_wellFounded {r : S → S → Prop} {rules : List (List S × List S)}
    (wf : WellFounded r) (dec : ∀ p ∈ rules, List.Shortlex r p.2 p.1) :
    WellFounded (flip (Step rules)) :=
  (List.Shortlex.wf wf).mono (fun _ _ h => step_shortlex dec h)

/-- A bounded table sees precisely those rules whose left sides fit the bound. -/
theorem step_stable {rs rt : List (List S × List S)} {k : ℕ}
    (stable : ∀ p, p.1.length ≤ k → (p ∈ rs ↔ p ∈ rt)) {w v : List S}
    (hw : w.length ≤ k) : Step rs w v ↔ Step rt w v := by
  constructor
  · intro h
    cases h with
    | apply hm x y =>
      apply Step.apply ((stable _ (by simp only [List.length_append] at hw; dsimp only; omega)).mp hm)
  · intro h
    cases h with
    | apply hm x y =>
      apply Step.apply ((stable _ (by simp only [List.length_append] at hw; dsimp only; omega)).mpr hm)

variable [DecidableEq S]

/-- The fixed choice of rule at the leftmost position, then table order. -/
def rootNext (w : List S) : List (List S × List S) → Option (List S)
  | [] => none
  | (u,v)::rs => if w.take u.length = u then some (v ++ w.drop u.length) else rootNext w rs

def next (rules : List (List S × List S)) : List S → Option (List S)
  | [] => rootNext [] rules
  | a::w => (rootNext (a::w) rules).or ((next rules w).map (a::·))

theorem rootNext_sound {w v : List S} {rules : List (List S × List S)}
    (h : rootNext w rules = some v) : ∃ u t, (u,t) ∈ rules ∧
      ∃ y, w = u++y ∧ v = t++y := by
  induction rules with
  | nil => simp [rootNext] at h
  | cons p rs ih =>
    rcases p with ⟨u,t⟩
    simp only [rootNext] at h
    split at h
    next he =>
      obtain rfl := Option.some.inj h
      exact ⟨u,t,List.mem_cons_self, w.drop u.length,
        by simpa only [he] using (List.take_append_drop u.length w).symm,rfl⟩
    next he =>
      obtain ⟨u,t,hm,y,hw,hv⟩ := ih h
      exact ⟨u,t,List.mem_cons_of_mem _ hm,y,hw,hv⟩

theorem rootNext_none {w : List S} {rules : List (List S × List S)}
    (h : rootNext w rules = none) {u t y : List S} (hm : (u,t) ∈ rules) : w ≠ u ++ y := by
  induction rules with
  | nil => simp at hm
  | cons p rs ih =>
    rcases p with ⟨a,b⟩
    simp only [rootNext] at h
    split at h
    · simp at h
    next he =>
      rcases List.mem_cons.mp hm with hp | hm
      · cases hp
        intro hw
        exact he (by simp [hw])
      · exact ih h hm

theorem next_sound {rules : List (List S × List S)} {w v : List S}
    (h : next rules w = some v) : Step rules w v := by
  induction w generalizing v with
  | nil =>
      obtain ⟨u,t,hm,y,hw,hv⟩ := rootNext_sound h
      have hh : Step rules (u++y) (t++y) := by
        simpa only [List.nil_append] using Step.apply hm [] y
      rw [← hw,← hv] at hh
      exact hh
  | cons a w ih =>
      simp only [next] at h
      cases hr : rootNext (a::w) rules with
      | some z =>
          simp [hr] at h
          subst z
          obtain ⟨u,t,hm,y,hw,hv⟩ := rootNext_sound hr
          have hh : Step rules (u++y) (t++y) := by
            simpa only [List.nil_append] using Step.apply hm [] y
          rw [← hw,← hv] at hh
          exact hh
      | none =>
          simp only [hr,Option.none_or,Option.map_eq_some_iff] at h
          obtain ⟨z,hz,rfl⟩ := h
          simpa only [List.singleton_append,List.append_nil] using step_context (ih hz) [a] []

theorem next_none_root {rules : List (List S × List S)} {w : List S}
    (h : next rules w = none) : rootNext w rules = none := by
  cases w with
  | nil => exact h
  | cons a w => exact (Option.or_eq_none_iff.mp h).1

theorem next_none_tail {rules : List (List S × List S)} {a : S} {w : List S}
    (h : next rules (a::w) = none) : next rules w = none := by
  exact Option.map_eq_none_iff.mp (Option.or_eq_none_iff.mp h).2

theorem next_none {rules : List (List S × List S)} {w : List S}
    (h : next rules w = none) : Irreducible (Step rules) w := by
  intro v hv
  cases hv with
  | @apply u t hm x y =>
    induction x with
    | nil => exact rootNext_none (next_none_root h) hm rfl
    | cons a x ih => exact ih (next_none_tail h)

/-- Fully specified finite-table reduction; divergence is retained for arbitrary
    (possibly nonterminating) tables. -/
def iteration (s : List (List S × List S) × List S) :
    List S ⊕ (List (List S × List S) × List S) :=
  match next s.1 s.2 with
  | none => .inl s.2
  | some v => .inr (s.1,v)

def evaluate (rules : List (List S × List S)) (w : List S) : Part (List S) :=
  PFun.fix (fun s => Part.some (iteration s)) (rules,w)

 theorem evaluate_sound {rules : List (List S × List S)} {w v : List S}
    (h : v ∈ evaluate rules w) : Steps rules w v ∧ Irreducible (Step rules) v := by
  change v ∈ PFun.fix _ (rules,w) at h
  refine PFun.fixInduction' (C := fun s => Steps s.1 s.2 v ∧ Irreducible (Step s.1) v) h ?_ ?_
  · rintro ⟨rs,a⟩ ha
    simp only [Part.mem_some_iff,iteration] at ha
    cases hn : next rs a with
    | none =>
      simp only [hn,Sum.inl.injEq] at ha
      subst a
      exact ⟨.refl,next_none hn⟩
    | some b => simp [hn] at ha
  · rintro ⟨rs,a⟩ ⟨rt,b⟩ _ hab ih
    simp only [Part.mem_some_iff,iteration] at hab
    cases hn : next rs a with
    | none => simp [hn] at hab
    | some c =>
      simp only [hn,Sum.inr.injEq,Prod.mk.injEq] at hab
      rcases hab with ⟨rfl,rfl⟩
      exact ⟨.head (next_sound hn) ih.1,ih.2⟩

theorem evaluate_total {rules : List (List S × List S)}
    (wf : WellFounded (flip (Step rules))) (w : List S) : (evaluate rules w).Dom := by
  induction w using wf.induction with
  | h w ih =>
    cases hn : next rules w with
    | none =>
      exact Part.dom_iff_mem.mpr ⟨w,PFun.fix_stop (by simp [iteration,hn])⟩
    | some v =>
      obtain ⟨z,hz⟩ := Part.dom_iff_mem.mp (ih v (next_sound hn))
      apply Part.dom_iff_mem.mpr
      refine ⟨z,PFun.mem_fix_iff.mpr (Or.inr ⟨(rules,v),?_,hz⟩)⟩
      simp [iteration,hn]

omit [DecidableEq S] in
/-- Bounded local confluence is enough: every intervening reduction has
    nonincreasing length, so no confluence outside the source budget is used. -/
theorem evaluate_unique_on {r : S → S → Prop} {rules : List (List S × List S)}
    (wf : WellFounded r) (dec : ∀ p ∈ rules, List.Shortlex r p.2 p.1) (n : ℕ)
    (localJoin : ∀ a b c, a.length ≤ n → Step rules a b → Step rules a c →
      Join (Steps rules) b c) {a b c : List S} (ha : a.length ≤ n)
    (hab : Steps rules a b) (hac : Steps rules a c)
    (hb : Irreducible (Step rules) b) (hc : Irreducible (Step rules) c) : b = c := by
  induction a using (steps_wellFounded wf dec).induction generalizing b c with
  | h a ih =>
    rcases hab.cases_head with rfl | ⟨b₁,hab₁,hb₁b⟩
    · exact irreducible_reaches _ hb hac
    rcases hac.cases_head with rfl | ⟨c₁,hac₁,hc₁c⟩
    · exact (irreducible_reaches _ hc (.head hab₁ hb₁b)).symm
    obtain ⟨d,hb₁d,hc₁d⟩ := localJoin a b₁ c₁ ha hab₁ hac₁
    obtain ⟨e,hde,he⟩ := exists_irreducible _ (steps_wellFounded wf dec) d
    have hb₁ : b₁.length ≤ n := (steps_length dec (.single hab₁)).trans ha
    have hc₁ : c₁.length ≤ n := (steps_length dec (.single hac₁)).trans ha
    exact (ih b₁ hab₁ hb₁ hb₁b (hb₁d.trans hde) hb he).trans
      (ih c₁ hac₁ hc₁ hc₁c (hc₁d.trans hde) hc he).symm

theorem evaluate_context_on {r : S → S → Prop} {rules : List (List S × List S)}
    (wf : WellFounded r) (dec : ∀ p ∈ rules, List.Shortlex r p.2 p.1) (n : ℕ)
    (localJoin : ∀ a b c, a.length ≤ n → Step rules a b → Step rules a c →
      Join (Steps rules) b c) {w v : List S} (hv : v ∈ evaluate rules w)
    (x y : List S) (hm : (x++w++y).length ≤ n) :
    evaluate rules (x++v++y) = evaluate rules (x++w++y) := by
  obtain ⟨a,ha⟩ := Part.dom_iff_mem.mp (evaluate_total (steps_wellFounded wf dec) (x++v++y))
  obtain ⟨b,hb⟩ := Part.dom_iff_mem.mp (evaluate_total (steps_wellFounded wf dec) (x++w++y))
  obtain ⟨hva,haI⟩ := evaluate_sound ha
  obtain ⟨hwb,hbI⟩ := evaluate_sound hb
  have hab := evaluate_unique_on wf dec n localJoin hm
    ((steps_context (evaluate_sound hv).1 x y).trans hva) hwb haI hbI
  subst b
  exact (Part.eq_some_iff.mpr ha).trans (Part.eq_some_iff.mpr hb).symm

variable [Primcodable S]

 theorem primrec_rootNext : Primrec₂ (@rootNext S _) := by
  apply Primrec₂.of_eq (Primrec.list_rec Primrec.snd (Primrec.const none)
    ((Primrec.ite
      (Primrec.eq.comp
        (Primrec.list_take.comp (Primrec.list_length.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)))
          (Primrec.fst.comp Primrec.fst))
        (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)))
      (Primrec.option_some.comp (Primrec.list_append.comp
        (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.list_drop.comp
          (Primrec.list_length.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)))
          (Primrec.fst.comp Primrec.fst))))
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))).to₂)).to₂
  intro w rs
  induction rs with
  | nil => rfl
  | cons p rs ih =>
      simpa [rootNext] using (congrArg
        (fun t => if w.take p.1.length = p.1 then some (p.2++w.drop p.1.length) else t) ih)

 theorem primrec_next : Primrec₂ (@next S _) := by
  have hor : Primrec₂ (Option.or : Option (List S) → Option (List S) → Option (List S)) :=
    Primrec.option_orElse.of_eq (by intro a b; cases a <;> rfl)
  apply Primrec₂.of_eq (Primrec.list_rec Primrec.snd
    (primrec_rootNext.comp (Primrec.const []) Primrec.fst)
    ((hor.comp
      (primrec_rootNext.comp
        (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
          (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
        (Primrec.fst.comp Primrec.fst))
      (Primrec.option_map (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
        ((Primrec.list_cons.comp
          (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd).to₂))).to₂)).to₂
  intro rs w
  induction w with
  | nil => rfl
  | cons a w ih =>
      simpa [next] using (congrArg
        (fun t => (rootNext (a::w) rs).or (t.map (a::·))) ih)

 theorem primrec_iteration : Primrec (@iteration S _) := by
  exact (Primrec.option_casesOn (primrec_next.comp Primrec.fst Primrec.snd)
    (Primrec.sumInl.comp Primrec.snd)
    ((Primrec.sumInr.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)).to₂)).of_eq
    (by intro s; cases h : next s.1 s.2 <;> simp [iteration,h])

 theorem partrec_evaluate : Partrec₂ (@evaluate S _) :=
  Partrec.fix primrec_iteration.to_comp

end

/- The marker/constant-width code used in the self-reference construction.
   A block has its marker only at the start, not at the end. -/

namespace Canonical
variable {A Q : Type*} {r : A → A → Prop} (wf : WellFounded r)
variable (q : List A → Q)

/-- Exactly the bounded tested-class candidate set in the self-reference construction. -/
def candidates (w : List A) : Set (List A) := {v | v.length ≤ w.length ∧ q v=q w}

noncomputable def least (w : List A) : List A :=
  (List.Shortlex.wf wf).min (candidates q w) ⟨w,le_rfl,rfl⟩

theorem least_mem (w : List A) : least wf q w ∈ candidates q w :=
  (List.Shortlex.wf wf).min_mem _ _

theorem least_length (w : List A) : (least wf q w).length ≤ w.length :=
  (least_mem wf q w).1

theorem least_class (w : List A) : q (least wf q w)=q w := (least_mem wf q w).2

theorem least_min {w v : List A} (hv : v.length≤w.length) (hq : q v=q w) :
    ¬ List.Shortlex r v (least wf q w) :=
  (List.Shortlex.wf wf).not_lt_min (candidates q w) ⟨hv,hq⟩

theorem least_global_min {w v : List A} (hq : q v=q w) : ¬ List.Shortlex r v (least wf q w) := by
  intro hd
  have hlen : v.length≤w.length := by
    have hm := least_length wf q w
    have he := List.shortlex_def.mp hd
    omega
  exact least_min wf q hlen hq hd

/-- Changing the finite search bound to that of another same-class candidate
    cannot change the result, including when the result is empty. -/
theorem least_congr [Std.Trichotomous r] {u v : List A} (hq : q u=q v) :
    least wf q u=least wf q v := by
  apply Std.Trichotomous.trichotomous (r := List.Shortlex r)
  · exact least_global_min wf q ((least_class wf q u).trans hq)
  · exact least_global_min wf q ((least_class wf q v).trans hq.symm)

/-- Literal characterization which requires no class tests longer than w. -/
theorem eq_least_iff [Std.Trichotomous r] {w v : List A} : v=least wf q w ↔
    v.length≤w.length ∧ q v=q w ∧
      ∀ t, t.length≤w.length → q t=q w → ¬ List.Shortlex r t v := by
  constructor
  · rintro rfl
    exact ⟨least_length wf q w,least_class wf q w,fun _ ht hq => least_min wf q ht hq⟩
  · rintro ⟨hv,hq,hm⟩
    exact Std.Trichotomous.trichotomous _ _
      (least_min wf q hv hq) (hm _ (least_length wf q w) (least_class wf q w))

end Canonical

open Relation
variable {S : Type*}

theorem step_mono {rs rt : List (List S × List S)} (h : ∀ p∈rs, p∈rt)
    {u v : List S} (huv : Step rs u v) : Step rt u v := by
  cases huv with
  | apply hp x y => exact .apply (h _ hp) x y

theorem steps_mono {rs rt : List (List S × List S)} (h : ∀ p∈rs, p∈rt)
    {u v : List S} (huv : Steps rs u v) : Steps rt u v := by
  induction huv with
  | refl => exact .refl
  | tail hh hs ih => exact .tail ih (step_mono h hs)

/-- The absorbing equations, stated as finite-table membership, not as an
    additional computation oracle. -/
def Absorbs (rs : List (List S × List S)) (z : S) : Prop :=
  ∀ a, ([z,a],[z])∈rs ∧ ([a,z],[z])∈rs

theorem absorbs_context {rs : List (List S × List S)} {z : S} (hz : Absorbs rs z)
    (x y : List S) : Steps rs (x++[z]++y) [z] := by
  have hr : ∀ y : List S, Steps rs ([z]++y) [z] := by
    intro y
    induction y with
    | nil => exact .refl
    | cons a y ih =>
      have hs : Steps rs ([z]++a::y) ([z]++y) :=
        .single (by simpa using Step.apply (hz a).1 [] y)
      exact hs.trans ih
  induction x with
  | nil => exact hr y
  | cons a x ih =>
    have hh := steps_context ih [a] []
    have hs : Step rs [a,z] [z] := by simpa using Step.apply (hz a).2 [] []
    have hh' : Steps rs (a::x++[z]++y) [a,z] := by simpa using hh
    exact hh'.trans (.single hs)

theorem absorbs_mem {rs : List (List S × List S)} {z : S} (hz : Absorbs rs z)
    {w : List S} (hw : z∈w) : Steps rs w [z] := by
  induction w with
  | nil => simp at hw
  | cons a w ih =>
    rcases List.mem_cons.mp hw with rfl | hw
    · exact absorbs_context hz [] w
    · have hh := steps_context (ih hw) [a] []
      have hh' : Steps rs (a::w) [a,z] := by simpa using hh
      exact hh'.trans (.single (by simpa using Step.apply (hz a).2 [] []))

theorem step_preserves_letter {rs : List (List S × List S)} {z : S}
    (hz : ∀ p∈rs, z∈p.1 → z∈p.2) {w v : List S} (hw : z∈w) (h : Step rs w v) : z∈v := by
  cases h with
  | apply hp x y =>
    simp only [List.mem_append] at hw ⊢
    rcases hw with (hx | hu) | hy
    · exact Or.inl (Or.inl hx)
    · exact Or.inl (Or.inr (hz _ hp hu))
    · exact Or.inr hy

namespace Static
variable {A Q : Type*} [Fintype A] [DecidableEq S]
variable {r : A → A → Prop}
variable (wf : WellFounded r)
  (q : List A → Option Q)
  (z : S)

noncomputable def letters (A : Type*) [Fintype A] : List A := (Finset.univ : Finset A).toList
noncomputable def words (A : Type*) [Fintype A] : ℕ → List (List A)
  | 0 => [[]]
  | n+1 => [] :: (letters A).flatMap (fun a => (words A n).map (a::·))

@[simp] theorem mem_words (n : ℕ) (w : List A) : w∈words A n ↔ w.length≤n := by
  classical
  induction n generalizing w with
  | zero => simp [words]
  | succ n ih =>
    cases w with
    | nil => simp [words]
    | cons a w => simp [words,letters,ih]

end Static
end FiniteAlgebraicEnvelopes.Bootstrap

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteCompiler_Selectors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Literal selector envelopes, rewrite saturation, and zero recognition.
-/

/- Literal selector envelopes from the self-reference construction. -/
namespace FiniteAlgebraicEnvelopes.Bootstrap

section

open Relation
variable {S : Type*} {rs : List (List S × List S)}

theorem join_context {u v : List S} (h : Join (Steps rs) u v) (x y : List S) :
    Join (Steps rs) (x++u++y) (x++v++y) := by
  obtain ⟨z,huz,hvz⟩ := h
  exact ⟨x++z++y,steps_context huz x y,steps_context hvz x y⟩

/-- The two critical configurations, checked only inside the current length ball. -/
def Critical (rs : List (List S × List S)) (n : ℕ) : Prop :=
  (∀ u u' v v', (u,u')∈rs → (v,v')∈rs → ∀ a b, u=a++v++b → u.length≤n →
    Join (Steps rs) u' (a++v'++b)) ∧
  (∀ u u' v v', (u,u')∈rs → (v,v')∈rs → ∀ p m q, m≠[] →
    u=p++m → v=m++q → (p++m++q).length≤n →
    Join (Steps rs) (u'++q) (p++v'))

theorem critical_ordered {n : ℕ} (crit : Critical rs n)
    {u u' v v' x y a b : List S} (hu : (u,u')∈rs) (hv : (v,v')∈rs)
    (he : x++u++y=a++v++b) (hlen : (x++u++y).length≤n) (hxa : x.length≤a.length) :
    Join (Steps rs) (x++u'++y) (a++v'++b) := by
  have hp₁ : x <+: x++u++y := ⟨u++y,by simp only [List.append_assoc]⟩
  have hp₂ : a <+: x++u++y := ⟨v++b,by simpa only [List.append_assoc] using he.symm⟩
  obtain ⟨p,hp⟩ := List.prefix_of_prefix_length_le hp₁ hp₂ hxa
  subst a
  have hs : u++y=p++(v++b) :=
    List.append_cancel_left (by simpa only [List.append_assoc] using he)
  rcases List.append_eq_append_iff.mp hs with ⟨t,rfl,hy⟩ | ⟨s,huv,hvb⟩
  · subst y
    refine ⟨x++u'++t++v'++b,?_,?_⟩
    · exact .single (by simpa only [List.append_assoc] using Step.apply hv (x++u'++t) b)
    · exact .single (by simpa only [List.append_assoc] using Step.apply hu x (t++v'++b))
  · rcases List.append_eq_append_iff.mp hvb.symm with ⟨c,hvc,hy⟩ | ⟨c,hsc,hb⟩
    · by_cases hsn : s=[]
      · subst s
        simp only [List.append_nil] at huv
        subst u
        simp only [List.nil_append] at hvc
        subst v
        subst y
        refine ⟨x++u'++v'++b,?_,?_⟩
        · exact .single (by simpa only [List.append_assoc] using Step.apply hv (x++u') b)
        · exact .single (by simpa only [List.append_assoc] using Step.apply hu x (v'++b))
      · have hj := crit.2 u u' v v' hu hv p s c hsn huv hvc
          (by simp only [huv,hy,List.length_append] at hlen; simp only [List.length_append]; omega)
        have hc := join_context hj x b
        simpa only [hy,List.append_assoc] using hc
    · have hj := crit.1 u u' v v' hu hv p c
        (by simp only [huv,hsc,List.append_assoc])
        (by simp only [List.length_append] at hlen; omega)
      have hc := join_context hj x y
      simpa only [hb,List.append_assoc] using hc

theorem step_decompose {a b : List S} (h : Step rs a b) :
    ∃ u v x y, (u,v)∈rs ∧ a=x++u++y ∧ b=x++v++y := by
  cases h with
  | apply h x y => exact ⟨_,_,x,y,h,rfl,rfl⟩

/-- Critical-pair reduction, including disjoint, boundary and containment peaks. -/
theorem critical_localJoin {n : ℕ} (crit : Critical rs n) {w a b : List S}
    (hw : w.length≤n) (ha : Step rs w a) (hb : Step rs w b) : Join (Steps rs) a b := by
  obtain ⟨u,u',x,y,hu,rfl,rfl⟩ := step_decompose ha
  obtain ⟨v,v',a,b,hv,he,rfl⟩ := step_decompose hb
  rcases le_total x.length a.length with h | h
  · exact critical_ordered crit hu hv he hw h
  · obtain ⟨z,haz,hbz⟩ := critical_ordered crit hv hu he.symm (by simpa only [he] using hw) h
    exact ⟨z,hbz,haz⟩

end

section
open Relation
namespace Selectors
variable {S : Type*}
  [DecidableEq S]

variable {a}

def BoundedEq (rs rt : List (List S × List S)) (k : ℕ) : Prop :=
  ∀ p, p.1.length ≤ k → (p ∈ rs ↔ p ∈ rt)

omit [DecidableEq S] in
theorem irreducible_bounded {rs rt : List (List S × List S)} {k : ℕ}
    (hh : BoundedEq rs rt k) {w : List S} (hw : w.length ≤ k) :
    Irreducible (Step rs) w ↔ Irreducible (Step rt) w := by
  constructor <;> intro h v hv
  · exact h v ((step_stable hh hw).mpr hv)
  · exact h v ((step_stable hh hw).mp hv)

end Selectors
end

namespace Canonical
variable {A Q : Type*} {r : A → A → Prop} [DecidableEq Q] [DecidableRel (List.Shortlex r)]

def pickStep (q : Q) (best : List A) (p : List A × Q) : List A :=
  if p.2=q ∧ List.Shortlex r p.1 best then p.1 else best

def pick (pairs : List (List A × Q)) (w : List A) (q : Q) : List A :=
  pairs.foldl (pickStep (r:=r) q) w

variable (wf : WellFounded r) (q : List A → Q)

theorem pick_class {ps : List (List A × Q)} {w v : List A}
    (hps : ∀ p ∈ ps,p.2=q p.1) (hv : q v=q w) : q (pick (r:=r) ps v (q w))=q w := by
  induction ps generalizing v with
  | nil => exact hv
  | cons p ps ih =>
    simp only [pick,List.foldl_cons]
    apply ih (fun p hp => hps p (List.mem_cons_of_mem _ hp))
    simp only [pickStep]
    split
    next h => exact (hps p (List.mem_cons_self)).symm.trans h.1
    next h => exact hv

end Canonical

namespace Search

section
variable {A : Type*} [DecidableEq A]

def lexBool (r : A → A → Bool) : List A → List A → Bool
  | [],[] => false
  | [],_::_ => true
  | _::_,[] => false
  | a::u,b::v => if a=b then lexBool r u v else r a b

def lexFoldStep (r : A → A → Bool) (st : Bool ⊕ List A) (a : A) : Bool ⊕ List A :=
  match st with
  | .inl b => .inl b
  | .inr [] => .inl false
  | .inr (b::v) => if a=b then .inr v else .inl (r a b)

def lexFinish : Bool ⊕ List A → Bool := Sum.elim id (fun v => !v.isEmpty)

theorem lexFold (r : A → A → Bool) (u : List A) (st : Bool ⊕ List A) :
    lexFinish (u.foldl (lexFoldStep r) st)=st.elim id (lexBool r u) := by
  induction u generalizing st with
  | nil => cases st with
    | inl b => rfl
    | inr v => cases v <;> rfl
  | cons a u ih =>
    rw [List.foldl_cons,ih]
    cases st with
    | inl b => rfl
    | inr v =>
      cases v with
      | nil => cases u <;> rfl
      | cons b v =>
        simp only [lexFoldStep,lexBool,Sum.elim_inr]
        split <;> rfl

variable [Primcodable A]

theorem primrec_lexBool (r : A → A → Bool) (hr : Primrec₂ r) : Primrec₂ (lexBool r) := by
  have hinr : Primrec₂ (fun (p : (Bool ⊕ List A) × A) (v : List A) =>
      match v with
      | [] => (Sum.inl false : Bool ⊕ List A)
      | b::v => if p.2=b then .inr v else .inl (r p.2 b)) := by
    exact (Primrec.list_casesOn Primrec.snd (Primrec.const (.inl false))
      (Primrec.ite
        (Primrec.eq.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)) (Primrec.fst.comp Primrec.snd))
        (Primrec.sumInr.comp (Primrec.snd.comp Primrec.snd))
        (Primrec.sumInl.comp (hr.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
          (Primrec.fst.comp Primrec.snd)))).to₂).to₂.of_eq (by intro p v; cases v <;> rfl)
  have hstep : Primrec₂ (lexFoldStep r) :=
    (Primrec.sumCasesOn Primrec.fst
      (Primrec.sumInl.comp Primrec.snd).to₂ hinr).to₂.of_eq (by
        intro st a
        cases st with
        | inl b => rfl
        | inr v => cases v <;> rfl)
  have hf : Primrec (lexFinish (A:=A)) :=
    (Primrec.sumCasesOn Primrec.id (Primrec.snd.to₂)
      ((Primrec.not.comp (Effect.primrec_listIsEmpty.comp Primrec.snd)).to₂)).of_eq (fun p => by cases p <;> rfl)
  exact ((hf.comp (Primrec.list_foldl Primrec.fst
    (Primrec.sumInr.comp Primrec.snd) (hstep.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).to₂)).of_eq (fun p => lexFold r p.1 (.inr p.2))).to₂

end

variable {A S Q : Type*} [DecidableEq A] [DecidableEq S] [DecidableEq Q]
variable {r : A → A → Prop} [DecidableRel (List.Shortlex r)]

theorem traverse_map {X Y : Type*} (f : X → Part Y) (g : X → Y) (l : List X)
    (h : ∀ x∈l, g x ∈ f x) : l.map g ∈ Effect.traverse f l := by
  induction l with
  | nil => exact Part.mem_some _
  | cons x xs ih =>
    exact Part.mem_bind_iff.mpr ⟨g x,h x List.mem_cons_self,
      (Part.mem_map_iff _).mpr ⟨xs.map g,ih (fun x hx => h x (List.mem_cons_of_mem _ hx)),rfl⟩⟩

variable [Fintype A] [Std.Trichotomous r] (wf : WellFounded r) (q : List A → Option Q)

variable [Primcodable A] [Primcodable S] [Primcodable Q]
omit [Std.Trichotomous r]

omit [DecidableEq A] in
 theorem primrec_words : Primrec (Static.words A) := by
  exact (Primrec.nat_rec₁ [[]]
    (Primrec.list_cons.comp (Primrec.const [])
      (Primrec.list_flatMap (Primrec.const (Static.letters A))
        (Primrec.list_map (Primrec.snd.comp Primrec.fst)
          (Primrec.list_cons.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂).to₂)).to₂).of_eq
    fun n => by induction n <;> simp_all [Static.words]

omit [DecidableEq A] [Fintype A] in
 theorem primrec_pickStep (hr : PrimrecRel (List.Shortlex r))
    {X : Type*} [Primcodable X] {v : X → Option Q} {b : X → List A} {p : X → List A × Option Q}
    (hv : Primrec v) (hb : Primrec b) (hp : Primrec p) :
    Primrec (fun x => Canonical.pickStep (r:=r) (v x) (b x) (p x)) :=
  Primrec.ite ((Primrec.eq.comp (Primrec.snd.comp hp) hv).and
    (hr.comp (Primrec.fst.comp hp) hb)) (Primrec.fst.comp hp) hb

omit [DecidableEq A] [Fintype A] in
 theorem primrec_pick (hr : PrimrecRel (List.Shortlex r))
    {X : Type*} [Primcodable X]
    {ps : X → List (List A × Option Q)} {v : X → List A} {q : X → Option Q}
    (hp : Primrec ps) (hv : Primrec v) (hq : Primrec q) :
    Primrec (fun x => Canonical.pick (r:=r) (ps x) (v x) (q x)) :=
  Primrec.list_foldl hp hv (primrec_pickStep (Q:=Q) hr
    (hq.comp Primrec.fst) (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂

end Search
end FiniteAlgebraicEnvelopes.Bootstrap

namespace FiniteAlgebraicEnvelopes.Bootstrap.Selectors

section
variable {S : Type*} [DecidableEq S] [Primcodable S]

 theorem primrec_mem {X : Type*} [Primcodable X] : PrimrecRel (fun (x : X) (l : List X) => x∈l) :=
  (PrimrecRel.of_eq Primrec.eq.exists_mem_list (by intro l x; simp)).swap

end

end FiniteAlgebraicEnvelopes.Bootstrap.Selectors

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteCompiler_Quotients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Canonical compiler quotients and effective tested classes for word problems.
-/

namespace FiniteAlgebraicEnvelopes.Bootstrap
open Relation

namespace Base
variable {S A B Q R : Type*} [Fintype S] [Fintype A] [Fintype B]
  [DecidableEq S] [DecidableEq A] [DecidableEq B] [DecidableEq Q] [DecidableEq R]
variable {r : A → A → Prop} {s : B → B → Prop} [Std.Trichotomous r] [Std.Trichotomous s]
variable (wf : WellFounded r)
  (wg : WellFounded s)
  (f : List A → Option Q)
  (g : List B → Option R)
  (z : S)

noncomputable def absorption : List (List S × List S) :=
  (Static.letters S).flatMap fun a => [([z,a],[z]),([a,z],[z])]

omit [DecidableEq S] in
@[simp] theorem mem_absorption {u v : List S} : (u,v) ∈ absorption z ↔
    ∃ a, (u=[z,a] ∨ u=[a,z]) ∧ v=[z] := by
  simp only [absorption,Static.letters,List.mem_flatMap,Finset.mem_toList,Finset.mem_univ,true_and,
    List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq]
  aesop

end Base

open Relation
variable {S : Type*} [DecidableEq S] {r : S → S → Prop}

omit [DecidableEq S] in
theorem steps_bounded {rs rt : List (List S × List S)} {k : ℕ}
    (hh : Selectors.BoundedEq rs rt k)
    (hd : ∀ p ∈ rs,List.Shortlex r p.2 p.1) {u v : List S} (hu : u.length ≤ k)
    (h : Steps rs u v) : Steps rt u v := by
  induction h with
  | refl => exact .refl
  | tail h hs ih => exact ih.tail ((step_stable hh ((steps_length hd h).trans hu)).mp hs)

/-- The actual partial table-first procedure used at the fixed point. -/
def tableNormal (T : ℕ → Part (List (List S × List S))) (w : List S) : Part (List S) :=
  (T w.length).bind (fun rs => evaluate rs w)

/-- A successful table has all the finite mathematical certificates needed by
    the bounded Newman argument. No totality of the program is part of this. -/
def GoodTable (T : ℕ → Part (List (List S × List S))) (n : ℕ) : Prop :=
  ∃ rs ∈ T n, (∀ p ∈ rs,List.Shortlex r p.2 p.1) ∧ Critical rs n

theorem tableNormal_at {T : ℕ → Part (List (List S × List S))} {n : ℕ}
    (wf : WellFounded r) (ht : ∀ k ≤ n,GoodTable (r:=r) T k)
    (hs : ∀ k ≤ n,∀ rk ∈ T k,∀ rn ∈ T n,Selectors.BoundedEq rk rn k)
    {rn : List (List S × List S)} (hrn : rn ∈ T n) {w : List S} (hw : w.length ≤ n) :
    tableNormal T w=evaluate rn w := by
  obtain ⟨rk,hrk,hdk,hck⟩ := ht w.length hw
  obtain ⟨rt,hrt,hdt,hct⟩ := ht n le_rfl
  have he := Part.mem_unique hrt hrn
  subst rt
  obtain ⟨u,hu⟩ := Part.dom_iff_mem.mp (evaluate_total (steps_wellFounded wf hdk) w)
  obtain ⟨v,hv⟩ := Part.dom_iff_mem.mp (evaluate_total (steps_wellFounded wf hdt) w)
  obtain ⟨hwu,huI⟩ := evaluate_sound hu
  obtain ⟨hwv,hvI⟩ := evaluate_sound hv
  have hstab := hs w.length hw rk hrk rn hrn
  have hwu' := steps_bounded hstab hdk le_rfl hwu
  have huI' := (Selectors.irreducible_bounded hstab (steps_length hdk hwu)).mp huI
  have huv := evaluate_unique_on wf hdt n (fun _ _ _ h => critical_localJoin hct h)
    hw hwu' hwv huI' hvI
  subst v
  rw [tableNormal,Part.eq_some_iff.mpr hrk,Part.bind_some]
  exact (Part.eq_some_iff.mpr hu).trans (Part.eq_some_iff.mpr hv).symm

/-- This is the whole contextual-induction step, including the table at the
    shortened contextual endpoint and irreducibility in the larger table. -/
theorem tableNormal_budget {T : ℕ → Part (List (List S × List S))} {n : ℕ}
    (wf : WellFounded r) (ht : ∀ k ≤ n,GoodTable (r:=r) T k)
    (hs : ∀ k m, k ≤ m → m ≤ n → ∀ rk ∈ T k,∀ rm ∈ T m,Selectors.BoundedEq rk rm k) :
    Compiler.PartialBudget (tableNormal T) n := by
  have htotal (w : List S) (hw : w.length ≤ n) : (tableNormal T w).Dom := by
    obtain ⟨rs,hrs,hd,hc⟩ := ht w.length hw
    rw [tableNormal,Part.eq_some_iff.mpr hrs,Part.bind_some]
    exact evaluate_total (steps_wellFounded wf hd) w
  have hlen (w : List S) (hw : w.length ≤ n) (out : List S) (ho : out ∈ tableNormal T w) :
      out.length ≤ w.length := by
    obtain ⟨rs,hrs,hd,hc⟩ := ht w.length hw
    rw [tableNormal,Part.eq_some_iff.mpr hrs,Part.bind_some] at ho
    exact steps_length hd (evaluate_sound ho).1
  refine ⟨htotal,hlen,?_⟩
  intro x w y hlenxy out hout
  obtain ⟨rs,hrs,hd,hc⟩ := ht n le_rfl
  have hw : w.length ≤ n := by simp only [List.length_append] at hlenxy; omega
  have hlenout := hlen w hw out hout
  have hshort : (x++out++y).length ≤ n := by simp only [List.length_append] at hlenxy ⊢; omega
  have heq (v : List S) (hv : v.length ≤ n) : tableNormal T v = evaluate rs v :=
    tableNormal_at wf ht (fun k hk => hs k n hk le_rfl) hrs hv
  have ehw := heq w hw
  rw [ehw] at hout
  rw [heq _ hshort,heq _ hlenxy]
  exact evaluate_context_on wf hd n (fun _ _ _ h => critical_localJoin hc h) hout x y hlenxy

/-- The source's simultaneous length induction, for the table builder actually
    fed to the recursion theorem.  `build` only receives strictly smaller budgets.
    Thus this lemma never assumes the desired total/contextual program outright. -/
theorem bootstrap_length_induction (wf : WellFounded r)
    (T : ℕ → Part (List (List S × List S))) (f : List S → Part (List S))
    (fixed : f=tableNormal T)
    (stable : ∀ k n, k ≤ n → ∀ rk ∈ T k,∀ rn ∈ T n,Selectors.BoundedEq rk rn k)
    (build : ∀ n, (∀ m<n,Compiler.PartialBudget f m) → GoodTable (r:=r) T n) :
    ∀ n, GoodTable (r:=r) T n ∧ Compiler.PartialBudget f n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hn := build n (fun m hm => (ih m hm).2)
    refine ⟨hn,?_⟩
    rw [fixed]
    apply tableNormal_budget wf
    · intro k hk
      rcases lt_or_eq_of_le hk with hk | rfl
      · exact (ih k hk).1
      · exact hn
    · intro k m hkm _
      exact stable k m hkm

end FiniteAlgebraicEnvelopes.Bootstrap

namespace FiniteAlgebraicEnvelopes
namespace Effect
variable {X A B : Type*}

theorem traverse_comp (f : A → Part B) (g : X → A) (l : List X) :
    traverse (fun x => f (g x)) l=traverse f (l.map g) := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [traverse,List.map_cons,ih]

theorem traverse_domain {f : A → Part B} {l : List A} (h : (traverse f l).Dom) :
    ∀ a∈l,(f a).Dom := by
  induction l with
  | nil => simp
  | cons a l ih =>
    obtain ⟨out,ho⟩ := Part.dom_iff_mem.mp h
    obtain ⟨b,hb,ht⟩ := Part.mem_bind_iff.mp ho
    obtain ⟨bs,hbs,_⟩ := (Part.mem_map_iff _).mp ht
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hb.1
    · exact ih hbs.1 x hx

theorem partrec_traverse_parameter [Primcodable X] [Primcodable A] [Primcodable B]
    {f : X → A → Part B} (hf : Partrec₂ f) : Partrec₂ (fun x => traverse (f x)) := by
  have hp : Primrec (fun p : X × List A => p.2.map (p.1,·)) :=
    Primrec.list_map Primrec.snd ((Primrec.fst.comp Primrec.fst).pair Primrec.snd).to₂
  exact ((partrec_traverse hf).comp hp.to_comp).of_eq (by
    intro p
    exact (traverse_comp (Function.uncurry f) (p.1,·) p.2).symm)
end Effect

namespace Bootstrap
namespace Search
variable {A S Q : Type*} [DecidableEq A] [DecidableEq S] [DecidableEq Q]
variable {r : A → A → Prop} [DecidableRel (List.Shortlex r)]

noncomputable def value (f : List A → Part (Option Q)) (w : List A) : Option Q := by
  classical
  exact if h : (f w).Dom then (f w).get h else none

end Search

 theorem partrec_tableNormal_parameter {X S : Type*} [DecidableEq S]
    [Primcodable X] [Primcodable S] {T : X → ℕ → Part (List (List S × List S))}
    (ht : Partrec₂ T) : Partrec₂ (fun x => tableNormal (T x)) := by
  exact ((ht.comp Computable.fst (Primrec.list_length.to_comp.comp Computable.snd)).bind
    (partrec_evaluate.comp Computable.snd (Computable.snd.comp Computable.fst)).to₂).to₂

end Bootstrap
end FiniteAlgebraicEnvelopes

namespace FiniteAlgebraicEnvelopes.Bootstrap

section

namespace Quotient
open Relation
variable {S : Type*} [DecidableEq S]
variable (T : ℕ → Part (List (List S × List S)))

/-- Literal equations of the stabilized infinite table. Restricting a stage to
its own budget removes only premature copies of the fixed absorption rules. -/
def Rel (u v : FreeMonoid S) : Prop :=
  ∃ n rs, rs ∈ T n ∧ (u.toList,v.toList) ∈ rs ∧ u.toList.length ≤ n

abbrev Mon := PresentedMonoid (Rel T)
def present (w : List S) : Mon T := PresentedMonoid.mk (Rel T) (FreeMonoid.ofList w)
noncomputable def normal (w : List S) : List S := Compiler.partValue (tableNormal T w)

omit [DecidableEq S] in
@[simp] theorem present_nil : present T []=1 := rfl
omit [DecidableEq S] in
@[simp] theorem present_append (u v : List S) : present T (u++v)=present T u * present T v := rfl

omit [DecidableEq S] in
 theorem present_step {n : ℕ} {rs : List (List S × List S)} (hrs : rs ∈ T n)
    {u v : List S} (hu : u.length ≤ n) (h : Step rs u v) : present T u=present T v := by
  cases h with
  | @apply a b hab x y =>
    have ha : a.length ≤ n := by simp only [List.length_append] at hu; omega
    have hh : present T a=present T b :=
      PresentedMonoid.mk_eq_mk_of_rel ⟨n,rs,hrs,hab,ha⟩
    simp only [present_append,hh]

omit [DecidableEq S] in
 theorem present_steps {r : S → S → Prop} {n : ℕ} {rs : List (List S × List S)}
    (hrs : rs ∈ T n) (hd : ∀ p∈rs,List.Shortlex r p.2 p.1)
    {u v : List S} (hu : u.length ≤ n) (h : Steps rs u v) : present T u=present T v := by
  induction h with
  | refl => rfl
  | tail h hs ih => exact ih.trans (present_step T hrs ((steps_length hd h).trans hu) hs)

variable {r : S → S → Prop} (wf : WellFounded r)
  (good : ∀ n,GoodTable (r:=r) T n)
  (stable : ∀ k n,k ≤ n → ∀ rk∈T k,∀ rn∈T n,Selectors.BoundedEq rk rn k)
include wf good stable

 theorem budget (n : ℕ) : Compiler.PartialBudget (tableNormal T) n :=
  tableNormal_budget wf (fun _ _ => good _) (fun k m h _ => stable k m h)

end Quotient

open Relation

namespace Quotient
variable {S : Type*} [DecidableEq S]
variable (T : ℕ → Part (List (List S × List S)))
variable {r : S → S → Prop} (wf : WellFounded r)
  (good : ∀ n,GoodTable (r:=r) T n)
  (stable : ∀ k n,k ≤ n → ∀ rk∈T k,∀ rn∈T n,Selectors.BoundedEq rk rn k)
include wf good stable

omit [DecidableEq S] wf good stable in
 theorem present_surjective : Function.Surjective (present T) := by
  intro x
  obtain ⟨w,rfl⟩ := PresentedMonoid.surjective_mk x
  exact ⟨w.toList,rfl⟩

noncomputable def representative (x : Mon T) : List S :=
  normal T (Classical.choose (present_surjective T x))

omit [DecidableEq S] wf good stable in
 theorem irreducible_of_short {rs : List (List S × List S)} {w : List S}
    (h : ∀ p∈rs,w.length<p.1.length) : Irreducible (Step rs) w := by
  intro v hv
  cases hv with
  | @apply u v huv x y =>
    have hh := h (u,v) huv
    simp only [List.length_append] at hh
    omega

omit [DecidableEq S] wf good stable in
 theorem present_absorbs (z : S) {rs : List (List S × List S)}
    (hrs : rs∈T 2) (hz : Absorbs rs z) :
    ∀ w,present T [z]*present T w=present T [z] ∧
      present T w*present T [z]=present T [z] := by
  have hza (a : S) : present T [z]*present T [a]=present T [z] :=
    PresentedMonoid.mk_eq_mk_of_rel ⟨2,rs,hrs,(hz a).1,by simp⟩
  have haz (a : S) : present T [a]*present T [z]=present T [z] :=
    PresentedMonoid.mk_eq_mk_of_rel ⟨2,rs,hrs,(hz a).2,by simp⟩
  intro w
  induction w with
  | nil => simp
  | cons a w ih =>
    have hh : present T (a::w)=present T [a]*present T w := rfl
    rw [hh]
    exact ⟨by rw [←mul_assoc,hza,ih.1],by rw [mul_assoc,ih.2,haz]⟩

@[instance_reducible]
noncomputable def monoidWithZero (z : S) {rs : List (List S × List S)}
    (hrs : rs∈T 2) (hz : Absorbs rs z) : MonoidWithZero (Mon T) where
  __ := (inferInstance : Monoid (Mon T))
  zero := present T [z]
  zero_mul x := by
    obtain ⟨w,rfl⟩ := PresentedMonoid.surjective_mk x
    exact (present_absorbs T z hrs hz w.toList).1
  mul_zero x := by
    obtain ⟨w,rfl⟩ := PresentedMonoid.surjective_mk x
    exact (present_absorbs T z hrs hz w.toList).2

end Quotient
end

end FiniteAlgebraicEnvelopes.Bootstrap

namespace FiniteAlgebraicEnvelopes.Bootstrap

section
open Relation
variable {S : Type*}

theorem irreducible_of_no_infix {rs : List (List S × List S)} {w : List S}
    (h : ∀ p∈rs, ¬ p.1 <:+: w) : Irreducible (Step rs) w := by
  intro v hv
  cases hv with
  | @apply u v hp x y => exact h (u,v) hp ⟨x,y,rfl⟩

end

end FiniteAlgebraicEnvelopes.Bootstrap

namespace FiniteAlgebraicEnvelopes
namespace Effect
variable {X A B : Type*} [Primcodable X] [Primcodable A] [Primcodable B]

/-- Finite traversal of a total computable family is a computable list map. -/
theorem computable_map_parameter {f : X → A → B} (hf : Computable₂ f) :
    Computable₂ (fun x (l : List A) => l.map (f x)) := by
  apply (partrec_traverse_parameter hf.partrec₂).of_eq_tot
  intro p
  exact Bootstrap.Search.traverse_map _ _ _ (fun a _ => Part.mem_some _)
end Effect

namespace Bootstrap.Canonical
variable {A Q : Type*} [Fintype A] [Primcodable A]
  {r : A → A → Prop} [DecidableRel (List.Shortlex r)] [Std.Trichotomous r]
  (wf : WellFounded r) (q : List A → Q)

omit [Fintype A] [Primcodable A] [DecidableRel (List.Shortlex r)] in
/-- Equality of computed representatives is exactly equality in the semantic
    quotient, not merely equality of a chosen noncanonical encoding. -/
theorem least_eq_iff {u v : List A} : least wf q u=least wf q v ↔ q u=q v := by
  constructor
  · intro h
    exact (least_class wf q u).symm.trans ((congrArg q h).trans (least_class wf q v))
  · exact least_congr wf q

end Bootstrap.Canonical

end FiniteAlgebraicEnvelopes

namespace FiniteAlgebraicEnvelopes.WordProblem

def letterRel (n : ℕ) (a b : Fin n × Bool) : Prop := Encodable.encode a<Encodable.encode b

end FiniteAlgebraicEnvelopes.WordProblem

end OAI
end

section
-- module Solutions.OAIQ066_SO.BooneHigman_PartialAffine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Primitive recursive dyadic partial affine monoid and its six-letter presentation.
-/

namespace FiniteAlgebraicEnvelopes.PartialAffine
/-- An unreduced dyadic numerator difference and a power-of-two denominator.
    Computation never relies on Mathlib's noncomputable coding of `ℚ`. -/
abbrev Dyad := ℕ × ℕ × ℕ
namespace Dyad
def val (a : Dyad) : ℚ := ((a.1:ℚ)-a.2.1)/2^a.2.2
def zero : Dyad := (0,0,0)
def one : Dyad := (1,0,0)
def neg (a : Dyad) : Dyad := (a.2.1,a.1,a.2.2)
def add (a b : Dyad) : Dyad :=
  (a.1*2^b.2.2+b.1*2^a.2.2,a.2.1*2^b.2.2+b.2.1*2^a.2.2,a.2.2+b.2.2)
def mul (a b : Dyad) : Dyad :=
  (a.1*b.1+a.2.1*b.2.1,a.1*b.2.1+a.2.1*b.1,a.2.2+b.2.2)
def le (a b : Dyad) : Bool :=
  decide (a.1*2^b.2.2+b.2.1*2^a.2.2 ≤ b.1*2^a.2.2+a.2.1*2^b.2.2)
def eq (a b : Dyad) : Bool := le a b && le b a
def max (a b : Dyad) : Dyad := if le a b then b else a

@[simp] theorem val_zero : val zero=0 := by norm_num [val,zero]
@[simp] theorem val_one : val one=1 := by norm_num [val,one]
@[simp] theorem val_neg (a : Dyad) : val (neg a) = -val a := by simp [val,neg]; ring
@[simp] theorem val_add (a b : Dyad) : val (add a b)=val a+val b := by
  simp only [val,add,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,pow_add]
  field_simp
  ring
@[simp] theorem val_mul (a b : Dyad) : val (mul a b)=val a*val b := by
  simp only [val,mul,Nat.cast_add,Nat.cast_mul,pow_add]
  field_simp
  ring
@[simp] theorem le_correct (a b : Dyad) : le a b=true ↔ val a≤val b := by
  rw [val,val,div_le_div_iff₀ (by positivity) (by positivity)]
  simp only [le,decide_eq_true_eq]
  rw [← Nat.cast_le (α:=ℚ)]
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  constructor <;> intro h <;> nlinarith
@[simp] theorem eq_correct (a b : Dyad) : eq a b=true ↔ val a=val b := by
  rw [eq, Bool.and_eq_true, le_correct, le_correct]
  exact le_antisymm_iff.symm
@[simp] theorem val_max (a b : Dyad) : val (max a b)=Max.max (val a) (val b) := by
  unfold max
  split
  next h => exact (max_eq_right ((le_correct a b).mp h)).symm
  next h => exact (max_eq_left (le_of_not_ge fun hh => h ((le_correct a b).mpr hh))).symm

theorem primrec_pow2 : Primrec (fun n : ℕ => 2^n) :=
  (Primrec.nat_rec₁ 1 (Primrec.nat_mul.comp Primrec.snd (Primrec.const 2)).to₂).of_eq
    (by intro n; induction n <;> simp_all [pow_succ])

theorem primrec_neg : Primrec neg :=
  (Primrec.fst.comp Primrec.snd).pair (Primrec.fst.pair (Primrec.snd.comp Primrec.snd))

end Dyad

abbrev Slope := ℕ × ℕ
namespace Slope
def dyad (a : Slope) : Dyad := (2^a.1,0,a.2)
def val (a : Slope) : ℚ := Dyad.val (dyad a)
def mul (a b : Slope) : Slope := (a.1+b.1,a.2+b.2)
def inv (a : Slope) : Slope := (a.2,a.1)
@[simp] theorem val_eq (a : Slope) : val a=2^a.1/2^a.2 := by simp [val,dyad,Dyad.val]
theorem val_pos (a : Slope) : 0<val a := by rw [val_eq]; positivity
@[simp] theorem val_mul (a b : Slope) : val (mul a b)=val a*val b := by
  simp only [val_eq,mul,pow_add]
  ring
@[simp] theorem val_inv (a : Slope) : val (inv a)=(val a)⁻¹ := by simp [val_eq,inv]
theorem primrec_dyad : Primrec dyad :=
  (Dyad.primrec_pow2.comp Primrec.fst).pair ((Primrec.const 0).pair Primrec.snd)
theorem primrec_inv : Primrec inv := Primrec.snd.pair Primrec.fst
end Slope

namespace Bound
def dom : Option ℚ → ℚ → Prop
  | none,_ => True
  | some r,x => r≤x
instance instDecidableDom (r : Option ℚ) (x : ℚ) : Decidable (dom r x) := by cases r <;> unfold dom <;> infer_instance

def sup : Option Dyad → Option Dyad → Option Dyad
  | none,b => b
  | a,none => a
  | some a,some b => some (Dyad.max a b)

theorem dom_sup (a b : Option Dyad) (x : ℚ) :
    dom ((sup a b).map Dyad.val) x ↔ dom (a.map Dyad.val) x ∧ dom (b.map Dyad.val) x := by
  cases a <;> cases b <;> simp [sup,dom,Dyad.val_max]

theorem dom_preimage (r : Option Dyad) (c : Slope) (d : Dyad) (x : ℚ) :
    dom ((r.map fun r => Dyad.mul (Slope.dyad (Slope.inv c)) (Dyad.add r (Dyad.neg d))).map Dyad.val) x ↔
      dom (r.map Dyad.val) (Slope.val c*x+Dyad.val d) := by
  cases r with
  | none => simp [dom]
  | some r =>
    simp only [Option.map_some,dom,Dyad.val_mul,Dyad.val_add,Dyad.val_neg]
    rw [show Dyad.val (Slope.dyad (Slope.inv c)) = (Slope.val c)⁻¹ from Slope.val_inv c,
      ← sub_eq_add_neg]
    rw [← div_eq_inv_mul,div_le_iff₀ (Slope.val_pos c)]
    constructor <;> intro h <;> linarith

end Bound

namespace Bound
def eq : Option Dyad → Option Dyad → Bool
  | none,none => true
  | some a,some b => Dyad.eq a b
  | _,_ => false

 theorem eq_correct (a b : Option Dyad) : eq a b=true ↔ a.map Dyad.val=b.map Dyad.val := by
  cases a <;> cases b <;> simp [eq,Dyad.eq_correct]

end Bound

/-- The fixed six-letter alphabet in the algebra construction, in the order
    `u,v,u⁻¹,v⁻¹,e₀,e₁`. -/
abbrev Letter := Fin 6

end FiniteAlgebraicEnvelopes.PartialAffine

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteCompiler_Machines
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Stack, binary, TM2, and TM0 realizations of partial recursive programs.
-/

namespace FiniteAlgebraicEnvelopes.MachineRealization.StackLift
open Turing Relation
open Turing.PartrecToTM2

 def swap : K' → K'
  | .main => .rev | .rev => .main | .aux => .aux | .stack => .stack
 @[simp] theorem swap_swap (k : K') : swap (swap k) = k := by cases k <;> rfl

 variable {S Λ : Type*}
 abbrev Symbol (S : Type*) := Γ' ⊕ S
 abbrev Store (S : Type*) := Option (Symbol S)
 inductive Label (S Λ : Type*)
  | pre | emit : S → Label S Λ
  | run : Λ → Label S Λ
  | post | reject
  deriving DecidableEq, Fintype

 def proj : Store S → Option Γ'
  | some (.inl a) => some a | _ => none
 def store (v : Option Γ') : Store S := v.map Sum.inl
 @[simp] theorem proj_store (v : Option Γ') : proj (store (S := S) v) = v := by cases v <;> rfl

 def embedStacks (t : K' → List Γ') : K' → List (Symbol S) := fun k => (t (swap k)).map Sum.inl
 @[simp] theorem embedStacks_swap (t : K' → List Γ') (k : K') :
    embedStacks (S := S) t (swap k) = (t k).map Sum.inl := by simp [embedStacks]
 theorem embedStacks_update (t : K' → List Γ') (k : K') (w : List Γ') :
    embedStacks (S := S) (Function.update t k w) =
      Function.update (embedStacks t) (swap k) (w.map Sum.inl) := by
  funext j
  by_cases h : j = swap k
  · subst j; simp
  · have hh : swap j ≠ k := fun e => h (by rw [←e,swap_swap])
    simp [embedStacks,Function.update_of_ne h,Function.update_of_ne hh]

 def stmt : TM2.Stmt (fun _ : K' => Γ') Λ (Option Γ') →
    TM2.Stmt (fun _ : K' => Symbol S) (Label S Λ) (Store S)
  | .push k f q => .push (swap k) (fun v => .inl (f (proj v))) (stmt q)
  | .peek k f q => .peek (swap k) (fun v a => store (f (proj v) (proj a))) (stmt q)
  | .pop k f q => .pop (swap k) (fun v a => store (f (proj v) (proj a))) (stmt q)
  | .load f q => .load (fun v => store (f (proj v))) (stmt q)
  | .branch f p q => .branch (fun v => f (proj v)) (stmt p) (stmt q)
  | .goto f => .goto (fun v => .run (f (proj v)))
  | .halt => .goto (fun _ => .post)

 def cfg (c : TM2.Cfg (fun _ : K' => Γ') Λ (Option Γ')) :
    TM2.Cfg (fun _ : K' => Symbol S) (Label S Λ) (Store S) :=
  ⟨some (c.l.elim .post .run),store c.var,embedStacks c.stk⟩

 theorem stmt_correct (q : TM2.Stmt (fun _ : K' => Γ') Λ (Option Γ'))
    (v : Option Γ') (t : K' → List Γ') :
    TM2.stepAux (stmt (S := S) q) (store v) (embedStacks t) = cfg (TM2.stepAux q v t) := by
  induction q generalizing v t with
  | push k f q ih =>
      simp only [stmt,TM2.stepAux,proj_store,embedStacks_swap]
      rw [←List.map_cons,←embedStacks_update]
      exact ih _ _
  | peek k f q ih =>
      simp only [stmt,TM2.stepAux,proj_store,embedStacks_swap]
      have he : proj (((t k).map Sum.inl).head? : Store S) = (t k).head? := by
        cases t k <;> rfl
      rw [he]; exact ih _ _
  | pop k f q ih =>
      simp only [stmt,TM2.stepAux,proj_store,embedStacks_swap]
      have he : proj (((t k).map Sum.inl).head? : Store S) = (t k).head? := by
        cases t k <;> rfl
      rw [he,←List.map_tail,←embedStacks_update]
      exact ih _ _
  | load f q ih => simpa only [stmt,TM2.stepAux,proj_store] using ih (f v) t
  | branch f p q ihp ihq =>
      cases h : f v <;> simp only [stmt,TM2.stepAux,proj_store,h,Bool.cond_false,Bool.cond_true]
      · exact ihq _ _
      · exact ihp _ _
  | goto f => simp [stmt,TM2.stepAux,cfg]
  | halt => rfl

 variable (M : Λ → TM2.Stmt (fun _ : K' => Γ') Λ (Option Γ'))
  (W : Label S Λ → TM2.Stmt (fun _ : K' => Symbol S) (Label S Λ) (Store S))
  (hW : ∀ l, W (.run l) = stmt (M l))

 include hW
 theorem step_correct (c : TM2.Cfg (fun _ : K' => Γ') Λ (Option Γ'))
    (d : TM2.Cfg (fun _ : K' => Γ') Λ (Option Γ')) (h : d ∈ TM2.step M c) :
    cfg (S := S) d ∈ TM2.step W (cfg c) := by
  rcases c with ⟨l,v,t⟩
  cases l with
  | none => simp [TM2.step] at h
  | some l =>
      simp only [TM2.step,Option.mem_some_iff] at h
      subst d
      simpa only [cfg,Option.elim_some,TM2.step,hW,Option.mem_some_iff] using stmt_correct (M l) v t

 theorem reaches_correct {c d : TM2.Cfg (fun _ : K' => Γ') Λ (Option Γ')}
    (h : TM2.Reaches M c d) : TM2.Reaches W (cfg (S := S) c) (cfg d) := by
  induction h with
  | refl => exact .refl
  | tail _ h ih => exact ih.tail (step_correct M W hW _ _ h)

 /-- Until the original interpreter halts, the wrapper cannot escape its run
     sector. This is the divergence/soundness half, not only a terminating test. -/
 theorem path_cases {c : TM2.Cfg (fun _ : K' => Γ') Λ (Option Γ')}
    {z : TM2.Cfg (fun _ : K' => Symbol S) (Label S Λ) (Store S)}
    (h : TM2.Reaches W (cfg c) z) :
    (∃ d, TM2.Reaches M c d ∧ z = cfg d) ∨
    (∃ d, TM2.Reaches M c d ∧ d.l = none ∧ TM2.Reaches W (cfg d) z) := by
  induction h with
  | refl => exact Or.inl ⟨c,.refl,rfl⟩
  | @tail z z' _ hs ih =>
      rcases ih with ⟨d,hd,rfl⟩ | ⟨d,hd,hh,hr⟩
      · cases hl : d.l with
        | none => exact Or.inr ⟨d,hd,hl,ReflTransGen.single hs⟩
        | some l =>
            let e := TM2.stepAux (M l) d.var d.stk
            have he : e ∈ TM2.step M d := by
              rcases d with ⟨ld,vd,td⟩
              simp only at hl
              simp [TM2.step,hl,e]
            have hh := step_correct M W hW d e he
            have hz : z' = cfg e := Option.mem_unique hs hh
            exact Or.inl ⟨e,hd.tail he,hz⟩
      · exact Or.inr ⟨d,hd,hh,hr.tail hs⟩

end FiniteAlgebraicEnvelopes.MachineRealization.StackLift

namespace FiniteAlgebraicEnvelopes.MachineRealization.BinaryCode
open Turing Turing.PartrecToTM2

def value : List Γ' → ℕ
  | [] => 0
  | .bit0 :: l => 2 * value l
  | .bit1 :: l => 2 * value l + 1
  | _ :: l => value l

@[simp] theorem value_pos (n : PosNum) : value (trPosNum n) = (n : ℕ) := by
  induction n with
  | one => rfl
  | bit0 n ih => simpa [trPosNum,value,ih] using (show 2 * (n : ℕ) = (n : ℕ) + (n : ℕ) by omega)
  | bit1 n ih => simpa [trPosNum,value,ih] using (show 2 * (n : ℕ) + 1 = (n : ℕ) + (n : ℕ) + 1 by omega)

@[simp] theorem value_num (n : Num) : value (trNum n) = (n : ℕ) := by cases n <;> simp [trNum,value]
@[simp] theorem value_nat (n : ℕ) : value (trNat n) = n := by simp [trNat]

def block (n : ℕ) : List Γ' := trNat n ++ [.cons]

end FiniteAlgebraicEnvelopes.MachineRealization.BinaryCode

namespace FiniteAlgebraicEnvelopes.MachineRealization.RawTM
open Turing Turing.PartrecToTM2 Relation
open StackLift BinaryCode
variable {S Λ : Type*} [DecidableEq S] [Encodable S]

abbrev Stmt (S Λ : Type*) := TM2.Stmt (fun _ : K' => Symbol S) (Label S Λ) (Store S)
abbrev Config (S Λ : Type*) := TM2.Cfg (fun _ : K' => Symbol S) (Label S Λ) (Store S)

def tracks (out : List S) (binary : List Γ') : K' → List (Symbol S)
  | .main => out.map Sum.inr
  | .rev => binary.map Sum.inl
  | .aux | .stack => []

omit [DecidableEq S] [Encodable S] in
@[simp] theorem tracks_main (out : List S) (binary : List Γ') : tracks out binary .main = out.map Sum.inr := rfl
omit [DecidableEq S] [Encodable S] in
@[simp] theorem tracks_rev (out : List S) (binary : List Γ') : tracks out binary .rev = binary.map Sum.inl := rfl
omit [DecidableEq S] [Encodable S] in
 theorem tracks_update_main (out : List S) (binary : List Γ') (out' : List S) :
    Function.update (tracks out binary) .main (out'.map Sum.inr) = tracks out' binary := by
  funext k; cases k <;> simp [tracks]
omit [DecidableEq S] [Encodable S] in
 theorem tracks_update_rev (out : List S) (binary binary' : List Γ') :
    Function.update (tracks out binary) .rev (binary'.map Sum.inl) = tracks out binary' := by
  funext k; cases k <;> simp [tracks]

def postCfg (out : List S) (binary : List Γ') : Config S Λ := ⟨some .post,none,tracks out binary⟩
def reject : Stmt S Λ := .goto (fun _ => .reject)
def finish (pre : List Γ') : Stmt S Λ :=
  match Encodable.decode (α := S) (value pre.reverse - 1) with
  | some s => .push .main (fun _ => .inr s) (.load (fun _ => none) (.goto (fun _ => .post)))
  | none => reject

def decoder : ℕ → List Γ' → Stmt S Λ
  | n, pre => .pop .rev (fun _ a => a)
      (.branch (fun v => decide (StackLift.proj v = some .cons)) (finish pre)
        (match n with
        | 0 => reject
        | n+1 => .branch (fun v => decide (StackLift.proj v = some .bit0)) (decoder n (.bit0::pre))
            (.branch (fun v => decide (StackLift.proj v = some .bit1)) (decoder n (.bit1::pre)) reject)))

omit [DecidableEq S] in
theorem decoder_correct (fuel : ℕ) (pre l : List Γ') (tail : List Γ')
    (out : List S) (s : S) (v : Store S)
    (hlen : l.length ≤ fuel) (hbits : ∀ a ∈ l, natEnd a = false)
    (hdec : Encodable.decode (α := S) (value (pre.reverse ++ l) - 1) = some s) :
    TM2.stepAux (decoder (Λ := Λ) fuel pre) v (tracks out (l ++ .cons :: tail)) =
      postCfg (s::out) tail := by
  induction l generalizing fuel pre v with
  | nil =>
      simp only [List.append_nil] at hdec
      cases fuel <;> simp only [decoder,TM2.stepAux,tracks_rev,List.nil_append,List.map_cons,
        List.head?_cons,StackLift.proj,List.tail_cons,decide_true,Bool.cond_true,finish,hdec]
      all_goals
        rw [tracks_update_rev]
        simp only [tracks_main]
        rw [← List.map_cons,tracks_update_main]
        rfl
  | cons a l ih =>
      cases fuel with
      | zero => simp at hlen
      | succ fuel =>
          have hb := hbits a List.mem_cons_self
          have hb' : ∀ a ∈ l, natEnd a = false := fun a ha => hbits a (List.mem_cons_of_mem _ ha)
          have hl : l.length ≤ fuel := by simpa using hlen
          cases a <;> try cases hb
          · simp only [decoder,TM2.stepAux,tracks_rev,List.cons_append,List.map_cons,
              List.head?_cons,StackLift.proj,List.tail_cons,decide_true,Bool.cond_true]
            rw [tracks_update_rev]
            apply ih fuel (.bit0::pre) _ hl hb'
            simpa [List.reverse_cons,List.append_assoc] using hdec
          · simp only [decoder,TM2.stepAux,tracks_rev,List.cons_append,List.map_cons,
              List.head?_cons,StackLift.proj,List.tail_cons,decide_true,Bool.cond_true]
            rw [tracks_update_rev]
            apply ih fuel (.bit1::pre) _ hl hb'
            simpa [List.reverse_cons,List.append_assoc] using hdec

omit [DecidableEq S] in
theorem decoder_block (fuel : ℕ) (tail : List Γ') (out : List S) (s : S) (v : Store S)
    (h : (trNat (Encodable.encode s + 1)).length ≤ fuel) :
    TM2.stepAux (decoder (Λ := Λ) fuel []) v
      (tracks out (block (Encodable.encode s + 1) ++ tail)) = postCfg (s::out) tail := by
  simp only [block,List.append_assoc,List.singleton_append]
  apply decoder_correct fuel [] _ tail out s v h (trNat_natEnd _)
  simp

def pushList : List Γ' → Stmt S Λ → Stmt S Λ
  | [], q => q
  | a::l,q => pushList l (.push .rev (fun _ => .inl a) q)

omit [DecidableEq S] [Encodable S] in
theorem pushList_correct (l : List Γ') (q : Stmt S Λ) (v : Store S)
    (out : List S) (binary : List Γ') :
    TM2.stepAux (pushList l q) v (tracks out binary) =
      TM2.stepAux q v (tracks out (l ++ binary)) := by
  induction l generalizing q binary with
  | nil => rfl
  | cons a l ih =>
      rw [pushList,ih]
      simp only [TM2.stepAux,tracks_rev]
      rw [←List.map_cons,tracks_update_rev]
      rfl

def machine (B : ℕ) (M : Λ → TM2.Stmt (fun _ : K' => Γ') Λ (Option Γ')) (start : Λ) :
    Label S Λ → Stmt S Λ
  | .pre => .pop .main (fun _ a => a) (.goto (fun v =>
      match v with
      | some (.inr s) => .emit s
      | none => .run start
      | _ => .reject))
  | .emit s => pushList (block (Encodable.encode s + 1))
      (.load (fun _ => none) (.goto (fun _ => .pre)))
  | .run l => StackLift.stmt (M l)
  | .post => .peek .rev (fun _ a => a)
      (.branch (fun v => v.isNone) (.load (fun _ => none) .halt) (decoder B []))
  | .reject => reject

def preCfg (out : List S) (binary : List Γ') : Config S Λ := ⟨some .pre,none,tracks out binary⟩
def haltCfg (out : List S) : Config S Λ := ⟨none,none,tracks out []⟩
def runCfg (start : Λ) (binary : List Γ') : Config S Λ := ⟨some (.run start),none,tracks [] binary⟩

variable (B : ℕ) (M : Λ → TM2.Stmt (fun _ : K' => Γ') Λ (Option Γ')) (start : Λ)

omit [DecidableEq S] in
theorem pre_cons (s : S) (out : List S) (binary : List Γ') :
    TM2.Reaches (machine B M start) (preCfg (s::out) binary)
      (preCfg out (block (Encodable.encode s + 1) ++ binary)) := by
  let mid : Config S Λ := ⟨some (.emit s),some (.inr s),tracks out binary⟩
  apply ReflTransGen.trans (b := mid) (ReflTransGen.single ?_) (ReflTransGen.single ?_)
  · simp only [preCfg,TM2.step,machine,TM2.stepAux,tracks_main,List.map_cons,
      List.head?_cons,List.tail_cons]
    rw [tracks_update_main]
    rfl
  · simp only [mid,TM2.step,machine]
    rw [pushList_correct]
    rfl

omit [DecidableEq S] in
theorem pre_nil (binary : List Γ') :
    TM2.Reaches (machine (S := S) B M start) (preCfg [] binary) (runCfg start binary) := by
  apply ReflTransGen.single
  simp only [preCfg,TM2.step,machine,TM2.stepAux,tracks_main,List.map_nil,
    List.head?_nil,List.tail_nil]
  rw [show ([] : List (Symbol S)) = [].map Sum.inr from rfl,tracks_update_main]
  rfl

def numbers (w : List S) : List ℕ := w.map (fun s => Encodable.encode s + 1)

omit [DecidableEq S] [Encodable S] in
@[simp] theorem trList_append (u v : List ℕ) : trList (u ++ v) = trList u ++ trList v := by
  induction u with
  | nil => rfl
  | cons a u ih => simp [trList,ih,List.append_assoc]

omit [DecidableEq S] in
theorem pre_complete (w : List S) (binary : List Γ') :
    TM2.Reaches (machine B M start) (preCfg w binary)
      (runCfg start (trList (numbers w.reverse) ++ binary)) := by
  induction w generalizing binary with
  | nil => simpa [numbers] using pre_nil (S := S) B M start binary
  | cons s w ih =>
      apply (pre_cons B M start s w binary).trans
      simpa [TM2.Reaches,List.reverse_cons,numbers,List.map_append,trList,block,List.append_assoc] using
        ih (block (Encodable.encode s + 1) ++ binary)

omit [DecidableEq S] in
theorem post_cons (s : S) (w out : List S)
    (hB : (trNat (Encodable.encode s + 1)).length ≤ B) :
    TM2.Reaches (machine B M start) (postCfg out (trList (numbers (s::w))))
      (postCfg (s::out) (trList (numbers w))) := by
  apply ReflTransGen.single
  simp only [postCfg,TM2.step,machine,TM2.stepAux,tracks_rev]
  have hn : (trList (numbers (s::w))).map (Sum.inl : Γ' → Symbol S) ≠ [] := by
    simp [numbers,trList]
  rw [show ((trList (numbers (s::w))).map (Sum.inl : Γ' → Symbol S)).head?.isNone = false from by
    simpa using hn]
  simp only [Bool.cond_false,numbers,List.map_cons,trList]
  have hh := decoder_block (Λ := Λ) B (trList (numbers w)) out s
      (((trList (numbers (s::w))).map Sum.inl).head?) hB
  simpa only [Option.mem_some_iff,block,List.append_assoc,List.singleton_append,numbers,
      List.map_cons,trList,postCfg] using hh

omit [DecidableEq S] in
theorem post_nil (out : List S) :
    TM2.Reaches (machine B M start) (postCfg out []) (haltCfg out) := by
  apply ReflTransGen.single
  rfl

omit [DecidableEq S] in
theorem post_complete (w out : List S)
    (hB : ∀ s ∈ w, (trNat (Encodable.encode s + 1)).length ≤ B) :
    TM2.Reaches (machine B M start) (postCfg out (trList (numbers w))) (haltCfg (w.reverse ++ out)) := by
  induction w generalizing out with
  | nil => simpa [numbers] using post_nil B M start out
  | cons s w ih =>
      apply (post_cons B M start s w out (hB s List.mem_cons_self)).trans
      simpa [TM2.Reaches,List.reverse_cons,List.append_assoc] using
        ih (s::out) (fun a ha => hB a (List.mem_cons_of_mem _ ha))

def baseCfg (l : Option Λ) (binary : List Γ') : TM2.Cfg (fun _ : K' => Γ') Λ (Option Γ') :=
  ⟨l,none,K'.elim binary [] [] []⟩

omit [DecidableEq S] [Encodable S] in
@[simp] theorem lift_base_some (l : Λ) (binary : List Γ') :
    StackLift.cfg (S := S) (baseCfg (some l) binary) = runCfg l binary := by
  simp only [StackLift.cfg,baseCfg,runCfg,Option.elim_some]
  congr 1
  funext k; cases k <;> rfl
omit [DecidableEq S] [Encodable S] in
@[simp] theorem lift_base_none (binary : List Γ') :
    StackLift.cfg (S := S) (baseCfg (Λ := Λ) none binary) = postCfg [] binary := by
  simp only [StackLift.cfg,baseCfg,postCfg,Option.elim_none]
  congr 1
  funext k; cases k <;> rfl

omit [DecidableEq S] in
 theorem eval_run {w : List S} {f : List S →. List S}
    (hB : ∀ s : S, (trNat (Encodable.encode s + 1)).length ≤ B)
    (hM : StateTransition.eval (TM2.step M) (baseCfg (some start) (trList (numbers w))) =
      (f w).map (fun out => baseCfg none (trList (numbers out)))) :
    StateTransition.eval (TM2.step (machine B M start)) (runCfg start (trList (numbers w))) =
      (f w).map (fun out => haltCfg out.reverse) := by
  have complete : ∀ out ∈ f w, haltCfg out.reverse ∈
      StateTransition.eval (TM2.step (machine B M start)) (runCfg start (trList (numbers w))) := by
    intro out hout
    have ht : baseCfg (Λ := Λ) none (trList (numbers out)) ∈
        StateTransition.eval (TM2.step M) (baseCfg (some start) (trList (numbers w))) := by
      rw [hM]; exact Part.mem_map _ hout
    have hh := StackLift.reaches_correct (S := S) M (machine B M start) (fun _ => rfl)
      (StateTransition.mem_eval.mp ht).1
    simp only [lift_base_some,lift_base_none] at hh
    apply StateTransition.mem_eval.mpr
    refine ⟨hh.trans ?_,rfl⟩
    simpa only [TM2.Reaches,List.append_nil] using post_complete B M start out [] (fun s _ => hB s)
  apply Part.ext
  intro z
  rw [Part.mem_map_iff]
  constructor
  · intro hz
    obtain ⟨hr,ht⟩ := StateTransition.mem_eval.mp hz
    rw [←lift_base_some] at hr
    rcases StackLift.path_cases M (machine B M start) (fun _ => rfl) hr with
        ⟨d,hd,rfl⟩ | ⟨d,hd,hhalt,hdz⟩
    · simp [StackLift.cfg,TM2.step] at ht
    · have hmem : d ∈ StateTransition.eval (TM2.step M)
          (baseCfg (some start) (trList (numbers w))) := by
        apply StateTransition.mem_eval.mpr
        refine ⟨hd,?_⟩
        rcases d with ⟨l,v,t⟩
        simp only at hhalt
        simp [TM2.step,hhalt]
      rw [hM] at hmem
      obtain ⟨out,hout,he⟩ := (Part.mem_map_iff _).mp hmem
      exact ⟨out,hout,Part.mem_unique (complete out hout) hz⟩
  · rintro ⟨out,hout,rfl⟩
    exact complete out hout

omit [DecidableEq S] in
 theorem eval_pre {w : List S} {f : List S →. List S}
    (hB : ∀ s : S, (trNat (Encodable.encode s + 1)).length ≤ B)
    (hM : StateTransition.eval (TM2.step M) (baseCfg (some start) (trList (numbers w))) =
      (f w).map (fun out => baseCfg none (trList (numbers out)))) :
    StateTransition.eval (TM2.step (machine B M start)) (preCfg w.reverse []) =
      (f w).map (fun out => haltCfg out.reverse) := by
  have hp := pre_complete B M start w.reverse []
  simp only [List.reverse_reverse,List.append_nil] at hp
  rw [StateTransition.reaches_eval hp]
  exact eval_run B M start hB hM

end FiniteAlgebraicEnvelopes.MachineRealization.RawTM

/- Actual finite-state extraction from the Mathlib evaluator.  This is a
   dependency of the compiler realization, not a realization assumption. -/
namespace FiniteAlgebraicEnvelopes.MachineRealization
open Turing Relation

namespace FiniteTM2
variable {K : Type*} {Γ : K → Type*} {Λ σ : Type*} [DecidableEq Λ]

 def restrictStmt (S : Finset Λ) (q : TM2.Stmt Γ Λ σ) (h : TM2.SupportsStmt S q) :
    TM2.Stmt Γ {l // l ∈ S} σ :=
  match q with
  | .push k f q => .push k f (restrictStmt S q h)
  | .peek k f q => .peek k f (restrictStmt S q h)
  | .pop k f q => .pop k f (restrictStmt S q h)
  | .load f q => .load f (restrictStmt S q h)
  | .branch f p q => .branch f (restrictStmt S p h.1) (restrictStmt S q h.2)
  | .goto f => .goto (fun v => ⟨f v,h v⟩)
  | .halt => .halt

 def embedCfg (S : Finset Λ) (c : TM2.Cfg Γ {l // l ∈ S} σ) : TM2.Cfg Γ Λ σ :=
  ⟨c.l.map Subtype.val,c.var,c.stk⟩

 variable [DecidableEq K]
omit [DecidableEq Λ] in
 theorem embed_stepAux (S : Finset Λ) (q : TM2.Stmt Γ Λ σ) (h : TM2.SupportsStmt S q)
    (v : σ) (t : ∀ k, List (Γ k)) :
    embedCfg S (TM2.stepAux (restrictStmt S q h) v t) = TM2.stepAux q v t := by
  induction q generalizing v t with
  | push k f q ih | peek k f q ih | pop k f q ih | load f q ih =>
      exact ih h _ _
  | branch f p q ihp ihq =>
      cases hv : f v <;> simp only [restrictStmt,TM2.stepAux,hv,Bool.cond_false,Bool.cond_true]
      · exact ihq h.2 _ _
      · exact ihp h.1 _ _
  | goto f => rfl
  | halt => rfl

 variable [Inhabited Λ] (M : Λ → TM2.Stmt Γ Λ σ) (S : Finset Λ) (h : TM2.Supports M S)
 def machine (l : {l // l ∈ S}) : TM2.Stmt Γ {l // l ∈ S} σ :=
  restrictStmt S (M l.val) (h.2 _ l.property)

omit [DecidableEq Λ] in
 theorem embed_step (c : TM2.Cfg Γ {l // l ∈ S} σ) :
    (TM2.step (machine M S h) c).map (embedCfg S) = TM2.step M (embedCfg S c) := by
  rcases c with ⟨l,v,t⟩
  cases l with
  | none => rfl
  | some l => simpa only [TM2.step,embedCfg,Option.map_some,machine] using
      congrArg some (embed_stepAux S (M l.val) (h.2 _ l.property) v t)

omit [DecidableEq Λ] in
 theorem respects : StateTransition.Respects (TM2.step (machine M S h)) (TM2.step M)
    (fun a b => embedCfg S a = b) := by
  apply StateTransition.fun_respects.mpr
  intro a
  have hh := embed_step M S h a
  cases hc : TM2.step (machine M S h) a with
  | none =>
      change TM2.step M (embedCfg S a) = none
      simpa only [hc,Option.map_none] using hh.symm
  | some b =>
      apply TransGen.single
      change TM2.step M (embedCfg S a) = some (embedCfg S b)
      simpa only [hc,Option.map_some] using hh.symm

omit [DecidableEq Λ] in
 theorem eval_embed (c : TM2.Cfg Γ {l // l ∈ S} σ) :
    StateTransition.eval (TM2.step M) (embedCfg S c) =
      (StateTransition.eval (TM2.step (machine M S h)) c).map (embedCfg S) :=
  StateTransition.tr_eval' _ _ _ (respects M S h) c

end FiniteTM2

end FiniteAlgebraicEnvelopes.MachineRealization

namespace FiniteAlgebraicEnvelopes.MachineRealization.ListCode
open Turing.ToPartrec Encodable

theorem eval_comp (f g : Code) (v : List ℕ) :
    (Code.comp f g).eval v = (g.eval v).bind (fun w => f.eval w) := rfl

attribute [local simp] eval_comp

theorem fix_eval_fwd (c : Code) (w w' : List ℕ)
    (h : Sum.inr w' ∈ Part.map
      (fun v : List ℕ => if v.headI = 0 then Sum.inl v.tail else Sum.inr v.tail) (c.eval w)) :
    (Code.fix c).eval w = (Code.fix c).eval w' :=
  PFun.fix_fwd_eq (α := List ℕ) (β := List ℕ)
    (f := fun v : List ℕ => Part.map
      (fun v : List ℕ => if v.headI = 0 then Sum.inl v.tail else Sum.inr v.tail) (c.eval v))
    (a := w) (a' := w') h

 def prefix₂ : Code := .cons .head (.cons (.comp .head .tail) .nil)
 @[simp] theorem prefix₂_eval (a b : ℕ) (l : List ℕ) :
    prefix₂.eval (a::b::l) = Part.some [a,b] := by simp [prefix₂]

 theorem binary_code {f : ℕ → ℕ → ℕ} (hf : Computable₂ f) :
    ∃ c : Code, ∀ a b l, c.eval (a::b::l) = Part.some [f a b] := by
  obtain ⟨c,hc⟩ := Code.exists_code (Nat.Partrec'.part_iff₂.mpr hf.partrec₂)
  refine ⟨.comp c prefix₂,fun a b l => ?_⟩
  simp only [eval_comp,prefix₂_eval,Part.bind_some]
  have he := hc ⟨[a,b],rfl⟩
  exact he

 def test (t p q : Code) : Code := .comp (.case p (.comp q .tail)) (.cons t .id)
 theorem test_eval (t p q : Code) (w : List ℕ) {n : ℕ}
    (ht : t.eval w = Part.some [n]) :
    (test t p q).eval w = if n = 0 then p.eval w else q.eval w := by
  simp only [test,eval_comp,Code.cons_eval,Code.id_eval,ht]
  cases n <;> simp [List.headI]

 def one : Code := .comp .succ .zero
 @[simp] theorem one_eval (w : List ℕ) : one.eval w = Part.some [1] := by simp [one]

 def encodeStep (c : Code) : Code :=
  test (.comp .head .tail) (.cons .zero .head)
    (.cons one (.cons c (.comp .tail .tail)))
 def encoder (c : Code) : Code := .comp (.fix (encodeStep c)) .zero'

 theorem encodeStep_nil (c : Code) (a : ℕ) :
    (encodeStep c).eval [a] = Part.some [0,a] := by
  rw [encodeStep,test_eval _ _ _ _ (n := 0) (by simp)]
  simp
 theorem encodeStep_cons (c : Code)
    (hc : ∀ a b l, c.eval (a::b::l) = Part.some [Nat.pair (b-1) a + 1])
    (a b : ℕ) (l : List ℕ) :
    (encodeStep c).eval (a::(b+1)::l) = Part.some (1::(Nat.pair b a + 1)::l) := by
  rw [encodeStep,test_eval _ _ _ _ (n := b+1) (by simp)]
  simp [hc]

 theorem encode_loop (c : Code)
    (hc : ∀ a b l, c.eval (a::b::l) = Part.some [Nat.pair (b-1) a + 1])
    (w acc : List ℕ) :
    (Code.fix (encodeStep c)).eval (encode acc :: w.map Nat.succ) =
      Part.some [encode (w.reverse ++ acc)] := by
  induction w generalizing acc with
  | nil =>
      apply Part.eq_some_iff.mpr
      rw [Code.fix_eval]
      apply PFun.fix_stop
      simp [encodeStep_nil]
  | cons b l ih =>
      rw [List.map_cons]
      have hs : Sum.inr (encode (b::acc)::l.map Nat.succ) ∈
          ((encodeStep c).eval (encode acc::(b+1)::l.map Nat.succ)).map
            (fun v => if v.headI = 0 then Sum.inl v.tail else Sum.inr v.tail) := by
        rw [encodeStep_cons c hc]
        simp [encode_list_cons]
      rw [fix_eval_fwd _ _ _ hs,ih]
      simp [List.reverse_cons,List.append_assoc]

 theorem encoder_eval (c : Code)
    (hc : ∀ a b l, c.eval (a::b::l) = Part.some [Nat.pair (b-1) a + 1]) (w : List ℕ) :
    (encoder c).eval (w.map Nat.succ) = Part.some [encode w.reverse] := by
  simp only [encoder,eval_comp,Code.zero'_eval]
  simpa using encode_loop c hc w []

 def decodeStep (h t : Code) : Code :=
  test .head (.cons .zero .tail)
    (.cons one (.cons t (.cons h .tail)))
 def decoder (h t : Code) : Code := .fix (decodeStep h t)
 theorem decodeStep_zero (h t : Code) (l : List ℕ) :
    (decodeStep h t).eval (0::l) = Part.some (0::l) := by
  rw [decodeStep,test_eval _ _ _ _ (n := 0) (by simp)]
  simp
 theorem decodeStep_cons (h t : Code)
    (hh : ∀ n l, h.eval (n::l) = Part.some [(n-1).unpair.1+1])
    (ht : ∀ n l, t.eval (n::l) = Part.some [(n-1).unpair.2])
    (b : ℕ) (w l : List ℕ) :
    (decodeStep h t).eval (encode (b::w)::l) = Part.some (1::encode w::(b+1)::l) := by
  rw [decodeStep,test_eval _ _ _ _ (n := encode (b::w)) (by simp)]
  simp [encode_list_cons,hh,ht]

 theorem decoder_eval (h t : Code)
    (hh : ∀ n l, h.eval (n::l) = Part.some [(n-1).unpair.1+1])
    (ht : ∀ n l, t.eval (n::l) = Part.some [(n-1).unpair.2])
    (w acc : List ℕ) :
    (decoder h t).eval (encode w::acc) = Part.some (w.reverse.map Nat.succ ++ acc) := by
  induction w generalizing acc with
  | nil =>
      apply Part.eq_some_iff.mpr
      rw [decoder,Code.fix_eval]
      apply PFun.fix_stop
      simp [decodeStep_zero]
  | cons b w ih =>
      rw [decoder]
      have hs : Sum.inr (encode w::(b+1)::acc) ∈
          ((decodeStep h t).eval (encode (b::w)::acc)).map
            (fun v => if v.headI = 0 then Sum.inl v.tail else Sum.inr v.tail) := by
        rw [decodeStep_cons h t hh ht]
        simp
      rw [fix_eval_fwd _ _ _ hs]
      change (decoder h t).eval _ = _
      rw [ih]
      simp [List.reverse_cons,List.map_append,List.append_assoc]

 theorem unary_code {f : ℕ → ℕ} (hf : Computable f) :
    ∃ c : Code, ∀ n l, c.eval (n::l) = Part.some [f n] := by
  obtain ⟨c,hc⟩ := Code.exists_code (Nat.Partrec'.part_iff₁.mpr hf.partrec)
  refine ⟨.comp c .head,fun n l => ?_⟩
  simp only [eval_comp,Code.head_eval,List.headI_cons]
  rw [show (pure [n] : Part (List ℕ)) = Part.some [n] from rfl,Part.bind_some]
  have he := hc ⟨[n],rfl⟩
  exact he

 theorem exists_wordCode {f : List ℕ →. List ℕ} (hf : Partrec f) :
    ∃ c : Code, ∀ w, c.eval (w.map Nat.succ) = (f w).map (List.map Nat.succ) := by
  obtain ⟨ce,hce⟩ := binary_code
    ((Computable.succ.comp (Primrec₂.natPair.to_comp.comp
      (Primrec.nat_sub.to_comp.comp Computable.snd (Computable.const 1)) Computable.fst)).to₂)
  obtain ⟨ch,hch⟩ := unary_code
    (Computable.succ.comp (Computable.fst.comp (Primrec.unpair.to_comp.comp
      (Primrec.nat_sub.to_comp.comp Computable.id (Computable.const 1)))))
  obtain ⟨ct,hct⟩ := unary_code
    (Computable.snd.comp (Primrec.unpair.to_comp.comp
      (Primrec.nat_sub.to_comp.comp Computable.id (Computable.const 1))))
  let g : ℕ →. ℕ := fun n => (f (Denumerable.ofNat (List ℕ) n).reverse).map
    (fun l => encode l.reverse)
  have hg : Partrec g :=
    (hf.comp (Computable.list_reverse.comp (Computable.ofNat (List ℕ)))).map
      ((Computable.encode.comp Computable.list_reverse).comp Computable.snd).to₂
  obtain ⟨cf,hcf⟩ := Code.exists_code (Nat.Partrec'.part_iff₁.mpr hg)
  refine ⟨.comp (decoder ch ct) (.comp cf (encoder ce)),fun w => ?_⟩
  simp only [eval_comp,encoder_eval ce hce,Part.bind_some]
  rw [hcf ⟨[encode w.reverse],rfl⟩]
  change ((g (encode w.reverse)).map (fun n => [n])).bind (fun v => (decoder ch ct).eval v) = _
  simp only [g,Denumerable.ofNat_encode,List.reverse_reverse]
  apply Part.ext
  intro out
  simp only [Part.mem_bind_iff,Part.mem_map_iff]
  constructor
  · rintro ⟨_,⟨n,⟨l,hl,rfl⟩,rfl⟩,hd⟩
    have he := decoder_eval ch ct hch hct l.reverse []
    simp only [List.reverse_reverse,List.append_nil] at he
    rw [he,Part.mem_some_iff] at hd
    exact ⟨l,hl,hd.symm⟩
  · rintro ⟨l,hl,rfl⟩
    refine ⟨[encode l.reverse],⟨encode l.reverse,⟨l,hl,rfl⟩,rfl⟩,?_⟩
    rw [decoder_eval ch ct hch hct l.reverse []]
    simp

end FiniteAlgebraicEnvelopes.MachineRealization.ListCode

namespace FiniteAlgebraicEnvelopes.MachineRealization

section
open Turing Turing.ToPartrec Turing.PartrecToTM2
open RawTM

namespace FiniteTM2
variable {K : Type*} {Γ : K → Type*} {Λ σ : Type*} [DecidableEq Λ]
omit [DecidableEq Λ] in
 theorem embedCfg_injective (A : Finset Λ) : Function.Injective (embedCfg (Γ := Γ) (σ := σ) A) := by
  rintro ⟨l,v,t⟩ ⟨l',v',t'⟩ h
  have hl := congrArg TM2.Cfg.l h
  have hv := congrArg TM2.Cfg.var h
  have ht := congrArg TM2.Cfg.stk h
  dsimp only [embedCfg] at hl hv ht
  have he := Option.map_injective Subtype.val_injective hl
  cases he
  cases hv
  cases ht
  rfl
end FiniteTM2

 theorem part_map_injective {A B : Type*} {g : A → B} (hg : Function.Injective g) :
    Function.Injective (Part.map g) := by
  intro p q h
  apply Part.ext
  intro a
  constructor <;> intro ha
  · have hh : g a ∈ p.map g := Part.mem_map _ ha
    rw [h] at hh
    obtain ⟨b,hb,he⟩ := (Part.mem_map_iff _).mp hh
    exact (hg he) ▸ hb
  · have hh : g a ∈ q.map g := Part.mem_map _ ha
    rw [←h] at hh
    obtain ⟨b,hb,he⟩ := (Part.mem_map_iff _).mp hh
    exact (hg he) ▸ hb

namespace WordEvaluator
variable {S : Type} [Primcodable S]

 theorem exists_code {f : List S →. List S} (hf : Partrec f) :
    ∃ c : Code, ∀ w, c.eval (numbers w) = (f w).map numbers := by
  let g : List ℕ →. List ℕ := fun ns =>
    (f (ns.filterMap Encodable.decode)).map (List.map Encodable.encode)
  have hg : Partrec g :=
    (hf.comp (Primrec.listFilterMap Primrec.id (Primrec.decode.comp Primrec.snd).to₂).to_comp).map
      ((Primrec.list_map Primrec.id (Primrec.encode.comp Primrec.snd).to₂).to_comp.comp Computable.snd).to₂
  obtain ⟨c,hc⟩ := ListCode.exists_wordCode hg
  refine ⟨c,fun w => ?_⟩
  have hcc := hc (w.map Encodable.encode)
  have hlist : (w.map Encodable.encode).filterMap Encodable.decode = w := by
    induction w <;> simp_all
  change c.eval (w.map (fun s => Encodable.encode s + 1)) =
    (f w).map (fun out => out.map (fun s => Encodable.encode s + 1))
  simpa only [g,hlist,Part.map_map,List.map_map,Function.comp_def,Nat.succ_eq_add_one] using hcc

 theorem exists_finite {f : List S →. List S} (hf : Partrec f) :
    ∃ (Λ : Type) (_ : Fintype Λ) (start : Λ)
      (M : Λ → TM2.Stmt (fun _ : K' => Γ') Λ (Option Γ')),
      ∀ w, StateTransition.eval (TM2.step M) (baseCfg (some start) (trList (numbers w))) =
        (f w).map (fun out => baseCfg none (trList (numbers out))) := by
  obtain ⟨c,hc⟩ := exists_code hf
  let A := codeSupp c Cont'.halt
  let : Inhabited Λ' := ⟨trNormal c Cont'.halt⟩
  have hs : TM2.Supports tr A := tr_supports c Cont'.halt
  let start : {l // l ∈ A} := ⟨trNormal c Cont'.halt,hs.1⟩
  let M := FiniteTM2.machine tr A hs
  refine ⟨{l // l ∈ A},inferInstance,start,M,fun w => ?_⟩
  apply part_map_injective (FiniteTM2.embedCfg_injective A)
  rw [←FiniteTM2.eval_embed tr A hs]
  change StateTransition.eval (TM2.step tr) (init c (numbers w)) = _
  rw [tr_eval,hc]
  simp only [Part.map_eq_map,Part.map_map]
  rfl

variable [Fintype S]
 noncomputable def bound : ℕ := Finset.univ.sup fun s : S => (trNat (Encodable.encode s + 1)).length
 theorem le_bound (s : S) : (trNat (Encodable.encode s + 1)).length ≤ bound (S := S) :=
  Finset.le_sup (f := fun s : S => (trNat (Encodable.encode s + 1)).length) (Finset.mem_univ s)

 theorem exists_raw {f : List S →. List S} (hf : Partrec f) :
    ∃ (Λ : Type) (_ : Fintype Λ) (M : Λ → TM2.Stmt (fun _ : K' => StackLift.Symbol S) Λ (StackLift.Store S))
      (start : Λ), ∀ w,
      StateTransition.eval (TM2.step M)
        ⟨some start,none,tracks w.reverse []⟩ =
          (f w).map (fun out => ⟨none,none,tracks out.reverse []⟩) := by
  classical
  obtain ⟨Λ,hΛ,start,M,hM⟩ := exists_finite hf
  let : Fintype Λ := hΛ
  refine ⟨StackLift.Label S Λ,inferInstance,machine (bound (S := S)) M start,.pre,fun w => ?_⟩
  exact eval_pre (bound (S := S)) M start le_bound (hM w)

end WordEvaluator
end

open Turing Relation
namespace FiniteTM0
variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ] [DecidableEq Λ]
variable (M : TM0.Machine Γ Λ) (A : Finset Λ) (h : TM0.Supports M (A : Set Λ))
variable [Inhabited {l // l ∈ A}]

def machine : TM0.Machine Γ {l // l ∈ A} := fun q a =>
  (M q.val a).pmap (fun p hp => (⟨p.1,h.2 hp q.property⟩,p.2)) (fun _ hp => hp)

def embed (c : TM0.Cfg Γ {l // l ∈ A}) : TM0.Cfg Γ Λ := ⟨c.q.val,c.Tape⟩

omit [Inhabited Λ] [DecidableEq Λ] [Inhabited {l // l ∈ A}] in
theorem embed_injective : Function.Injective (embed (Γ := Γ) A) := by
  rintro ⟨q,t⟩ ⟨q',t'⟩ he
  have hq : q = q' := Subtype.ext (congrArg TM0.Cfg.q he)
  have ht := congrArg TM0.Cfg.Tape he
  cases hq
  cases ht
  rfl

omit [DecidableEq Λ] in
theorem embed_step (c : TM0.Cfg Γ {l // l ∈ A}) :
    (TM0.step (machine M A h) c).map (embed A) = TM0.step M (embed A c) := by
  rcases c with ⟨q,t⟩
  cases hc : M q.val t.head with
  | none => simp [TM0.step,machine,embed,hc]
  | some p => rcases p with ⟨q',s⟩; cases s <;> simp [TM0.step,machine,embed,hc]

omit [DecidableEq Λ] in
theorem respects : StateTransition.Respects (TM0.step (machine M A h)) (TM0.step M)
    (fun a b => embed A a = b) := by
  apply StateTransition.fun_respects.mpr
  intro a
  have hh := embed_step M A h a
  cases hc : TM0.step (machine M A h) a with
  | none =>
      change TM0.step M (embed A a) = none
      simpa only [hc,Option.map_none] using hh.symm
  | some b =>
      apply TransGen.single
      change TM0.step M (embed A a) = some (embed A b)
      simpa only [hc,Option.map_some] using hh.symm

omit [DecidableEq Λ] in
theorem eval_embed (c : TM0.Cfg Γ {l // l ∈ A}) :
    StateTransition.eval (TM0.step M) (embed A c) =
      (StateTransition.eval (TM0.step (machine M A h)) c).map (embed A) :=
  StateTransition.tr_eval' _ _ _ (respects M A h) c
end FiniteTM0

namespace StackTape
open Turing.PartrecToTM2 StackLift RawTM
variable {S Λ : Type} [Fintype S] [Fintype Λ] [Inhabited Λ]

 def slice (a : S) : ∀ _ : K', Option (Symbol S) := Function.update (fun _ => none) .main (some (.inr a))
 def stackList (w : List S) : ListBlank (∀ _ : K', Option (Symbol S)) := ListBlank.mk (w.map slice)
 def tape (w : List S) : Turing.Tape (TM2to1.Γ' K' (fun _ => Symbol S)) :=
   Turing.Tape.mk' ∅ (TM2to1.addBottom (stackList w))

omit [Fintype S] in
 theorem tracks_proj (w : List S) (k : K') :
   (stackList w).map (Turing.proj k) = ListBlank.mk (((tracks w.reverse [] k).map some).reverse) := by
  cases k <;> simp [stackList,slice,tracks,Turing.proj,ListBlank.map_mk,List.map_reverse,List.map_map,
    Function.comp_def] <;> exact Quotient.sound (Or.inr ⟨w.length,rfl⟩)

omit [Fintype S] [Fintype Λ] [Inhabited Λ] in
 theorem trCfg (w : List S) (l : Option Λ) (v : Store S) :
   TM2to1.TrCfg (⟨l,v,tracks w.reverse []⟩ : TM2.Cfg (fun _ : K' => Symbol S) Λ (Store S))
     ⟨l.map .normal,v,tape w⟩ := .mk (stackList w) (tracks_proj w)

omit [Fintype S] in
 theorem stackList_unique (w : List S) (L : ListBlank (∀ _ : K', Option (Symbol S)))
    (hL : ∀ k, L.map (Turing.proj k) = ListBlank.mk (((tracks w.reverse [] k).map some).reverse)) :
    L = stackList w := by
  apply ListBlank.ext
  intro n
  funext k
  have he := congrArg (fun l => ListBlank.nth l n) ((hL k).trans (tracks_proj w k).symm)
  simpa only [ListBlank.nth_map,Turing.proj,PointedMap.mk_val] using he

omit [Fintype S] [Fintype Λ] [Inhabited Λ] in
 theorem trCfg_unique (w : List S) (l : Option Λ) (v : Store S)
    {c : TM1.Cfg (TM2to1.Γ' K' (fun _ => Symbol S)) (TM2to1.Λ' K' (fun _ => Symbol S) Λ (Store S)) (Store S)}
    (hc : TM2to1.TrCfg (⟨l,v,tracks w.reverse []⟩ : TM2.Cfg (fun _ : K' => Symbol S) Λ (Store S)) c) :
    c = ⟨l.map .normal,v,tape w⟩ := by
  cases hc with
  | mk L hL => rw [stackList_unique w L hL]; rfl

 variable (M : Λ → TM2.Stmt (fun _ : K' => Symbol S) Λ (Store S))
omit [Fintype S] [Fintype Λ] [Inhabited Λ] in
 theorem eval_tape {f : List S →. List S} (start : Λ)
   (hM : ∀ w, StateTransition.eval (TM2.step M) ⟨some start,none,tracks w.reverse []⟩ =
      (f w).map (fun out => ⟨none,none,tracks out.reverse []⟩)) (w : List S) :
   StateTransition.eval (TM1.step (TM2to1.tr M)) ⟨some (.normal start),none,tape w⟩ =
     (f w).map (fun out => ⟨none,none,tape out⟩) := by
  apply Part.ext
  intro c
  constructor
  · intro hc
    obtain ⟨b,hbc,hb⟩ := StateTransition.tr_eval_rev (TM2to1.tr_respects M) (trCfg w (some start) none) hc
    rw [hM] at hb
    obtain ⟨out,hout,rfl⟩ := (Part.mem_map_iff _).mp hb
    rw [trCfg_unique out none none hbc]
    exact Part.mem_map _ hout
  · intro hc
    obtain ⟨out,hout,rfl⟩ := (Part.mem_map_iff _).mp hc
    have hb : (⟨none,none,tracks out.reverse []⟩ : TM2.Cfg (fun _ : K' => Symbol S) Λ (Store S)) ∈
       StateTransition.eval (TM2.step M) ⟨some start,none,tracks w.reverse []⟩ := by
      rw [hM]; exact Part.mem_map _ hout
    obtain ⟨b,hb,hbe⟩ := StateTransition.tr_eval (TM2to1.tr_respects M) (trCfg w (some start) none) hb
    simpa only [trCfg_unique out none none hb,Option.map_none,Option.map_some] using hbe

omit [Fintype S] [Fintype Λ] in
 theorem eval_post {f : List S →. List S} (start : Λ)
   (hM : ∀ w, StateTransition.eval (TM2.step M) ⟨some start,none,tracks w.reverse []⟩ =
      (f w).map (fun out => ⟨none,none,tracks out.reverse []⟩)) (w : List S) :
   StateTransition.eval (TM0.step (TM1to0.tr (TM2to1.tr M)))
     (TM1to0.trCfg (TM2to1.tr M) ⟨some (.normal start),none,tape w⟩) =
     (f w).map (fun out => (⟨(none,none),tape out⟩ : TM0.Cfg _ _)) := by
   rw [StateTransition.tr_eval' _ _ _ (TM1to0.tr_respects (TM2to1.tr M)),eval_tape M start hM]
   simp only [Part.map_eq_map,Part.map_map]
   rfl

end StackTape

end FiniteAlgebraicEnvelopes.MachineRealization

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteCompiler_TapeFolding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Safe tapes, literal folding, and uniform code-machine realization.
-/

namespace FiniteAlgebraicEnvelopes.MachineRealization.OneSided
open Compiler.Simulator Turing Relation
variable {Γ Q : Type*}

structure Cfg (Γ Q : Type*) where
  state : Q
  pos : ℕ
  cell : ℕ → Γ

 theorem append_at (l : List Γ) (s : Stream' Γ) (n : ℕ) :
   Stream'.appendStream' l s (l.length+n) = s n := by
  induction l with
  | nil => simp only [List.length_nil,Nat.zero_add,Stream'.appendStream']
  | cons a l ih => simpa only [List.length_cons,Nat.succ_add,Stream'.appendStream',Stream'.cons] using ih

 theorem replace_at (l : List Γ) (s : Stream' Γ) (a : Γ) :
   Stream'.appendStream' l (Stream'.cons a s.tail) =
     Function.update (Stream'.appendStream' l s) l.length a := by
  unfold Stream' at *
  funext n
  induction l generalizing n with
  | nil => cases n <;> simp [Stream'.appendStream',Stream'.cons,Stream'.tail,Stream'.get]
  | cons b l ih =>
    cases n with
    | zero => simp [Stream'.appendStream',Stream'.cons,Function.update]
    | succ n =>
      by_cases hn : n = l.length
      · subst n
        simpa [Stream'.appendStream',Stream'.cons,Function.update] using ih l.length
      · simpa [Stream'.appendStream',Stream'.cons,Function.update,hn] using ih n

end FiniteAlgebraicEnvelopes.MachineRealization.OneSided

namespace FiniteAlgebraicEnvelopes.MachineRealization.TapeFold
open Turing Relation Compiler.Simulator
variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

inductive Side | pos | neg deriving DecidableEq
instance instFintypeSide : Fintype Side := ⟨{.pos,.neg},by intro x; cases x <;> simp⟩
structure Cell (Γ : Type*) where
  origin : Bool
  pos : Γ
  neg : Γ
  deriving DecidableEq, Fintype

def position : Side → ℕ → ℤ
  | .pos,n => n
  | .neg,n => -(n+1 : ℤ)

def read (d : Side) (a : Cell Γ) : Γ := match d with | .pos => a.pos | .neg => a.neg

/-- The two halves of the integer tape share one physical cell. The immutable
origin flag makes crossing the fold a finite-control, zero-movement operation. -/
def Rel (c : TM0.Cfg Γ Λ) (s : OneSided.Cfg (Cell Γ) (Side × Λ)) : Prop :=
  s.state.2 = c.q ∧ ∀ n,
    (s.cell n).origin = decide (n = 0) ∧
    (s.cell n).pos = c.Tape.nth ((n:ℤ) - position s.state.1 s.pos) ∧
    (s.cell n).neg = c.Tape.nth (-(n+1:ℤ) - position s.state.1 s.pos)

omit [Inhabited Λ] in
theorem read_head {c : TM0.Cfg Γ Λ} {s : OneSided.Cfg (Cell Γ) (Side × Λ)} (h : Rel c s) :
    read s.state.1 (s.cell s.pos) = c.Tape.head := by
  obtain ⟨_,hs⟩ := h
  obtain ⟨_,hp,hn⟩ := hs s.pos
  cases hd : s.state.1 <;> simp only [read,hd,position,sub_self,Tape.nth_zero] at * <;> assumption

end FiniteAlgebraicEnvelopes.MachineRealization.TapeFold

namespace FiniteAlgebraicEnvelopes.MachineRealization.TapeSafety
open Turing
variable {K : Type} {Γ : K → Type} {Λ σ : Type}

/-- Every writing subinstruction preserves the bottom track. -/
def Safe : TM1.Stmt (TM2to1.Γ' K Γ) Λ σ → Prop
  | .move _ q => Safe q
  | .write f q => (∀ a v, (f a v).1 = a.1) ∧ Safe q
  | .load _ q => Safe q
  | .branch _ q r => Safe q ∧ Safe r
  | .goto _ => True
  | .halt => True

theorem safe_stAct [DecidableEq K] {k : K}
    {q : TM1.Stmt (TM2to1.Γ' K Γ) (TM2to1.Λ' K Γ Λ σ) σ} (hq : Safe q)
    (a : TM2to1.StAct K Γ σ k) : Safe (TM2to1.trStAct q a) := by
  cases a <;> simp [TM2to1.trStAct,Safe,hq]

theorem safe_normal (q : TM2.Stmt Γ Λ σ) : Safe (TM2to1.trNormal q) := by
  induction q <;> simp_all [TM2to1.trNormal,Safe]

theorem safe_tr [DecidableEq K] (M : Λ → TM2.Stmt Γ Λ σ) (q : TM2to1.Λ' K Γ Λ σ) :
    Safe (TM2to1.tr M q) := by
  cases q with
  | normal q => exact safe_normal _
  | go k a q =>
      change Safe (TM2to1.trStAct (.goto fun _ _ => .ret q) a) ∧ True
      exact ⟨safe_stAct (q := .goto fun _ _ => .ret q) trivial a,trivial⟩
  | ret q => simp [TM2to1.tr,Safe,safe_normal]

theorem safe_sub {q r : TM1.Stmt (TM2to1.Γ' K Γ) Λ σ}
    (h : q ∈ TM1.stmts₁ r) (hr : Safe r) : Safe q := by
  classical
  induction r with
    simp only [TM1.stmts₁,Safe,Finset.mem_insert,Finset.mem_union,Finset.mem_singleton] at h hr
  | move d r ih => rcases h with rfl | h; exact hr; exact ih h hr
  | write f r ih => rcases h with rfl | h; exact hr; exact ih h hr.2
  | load f r ih => rcases h with rfl | h; exact hr; exact ih h hr
  | branch p r s ihr ihs => rcases h with rfl | h | h; exact hr; exact ihr h hr.1; exact ihs h hr.2
  | goto l => subst q; trivial
  | halt => subst q; trivial

theorem safe_stmts (M : Λ → TM1.Stmt (TM2to1.Γ' K Γ) Λ σ) (B : Finset Λ)
    (hm : ∀ q, Safe (M q)) {q : TM1.Stmt (TM2to1.Γ' K Γ) Λ σ}
    (hq : some q ∈ TM1.stmts M B) : Safe q := by
  classical
  simp only [TM1.stmts,Finset.mem_insertNone,Option.mem_def,Option.some.injEq,forall_eq',Finset.mem_biUnion] at hq
  obtain ⟨l,_,hl⟩ := hq
  exact safe_sub hl (hm l)

theorem trAux_write (M : Λ → TM1.Stmt (TM2to1.Γ' K Γ) Λ σ)
    (a : TM2to1.Γ' K Γ) (q : TM1.Stmt (TM2to1.Γ' K Γ) Λ σ) (v : σ)
    (hq : Safe q) (b : TM2to1.Γ' K Γ)
    (he : (TM1to0.trAux M a q v).2 = .write b) : b.1 = a.1 := by
  induction q generalizing v with
  | move d q ih => cases he
  | write f q ih => cases he; exact hq.1 a v
  | load f q ih => exact ih _ hq he
  | branch p q r ihq ihr =>
      cases hp : p a v <;> simp only [TM1to0.trAux,hp,Bool.cond_false,Bool.cond_true] at he
      · exact ihr _ hq.2 he
      · exact ihq _ hq.1 he
  | goto l => cases he; rfl
  | halt => cases he; rfl

/-- A machine preserves the distinguished bottom marker on every write. -/
def Preserves {L : Type*} [Inhabited L] (M : TM0.Machine (TM2to1.Γ' K Γ) L) : Prop :=
  ∀ q a q' b, M q a = some (q',.write b) → b.1 = a.1

theorem finite_preserves [Inhabited Λ] [Inhabited σ] [Fintype σ]
    (M : Λ → TM1.Stmt (TM2to1.Γ' K Γ) Λ σ) (B : Finset Λ)
    (hB : TM1.Supports M B) (hm : ∀ q, Safe (M q))
    [Inhabited {l // l ∈ TM1to0.trStmts M B}] :
    Preserves (FiniteTM0.machine (TM1to0.tr M) (TM1to0.trStmts M B) (TM1to0.tr_supports M hB)) := by
  classical
  intro q a q' b he
  have hq := q.property
  rcases q with ⟨⟨q,v⟩,hq'⟩
  cases q with
  | none => simp [FiniteTM0.machine,TM1to0.tr] at he
  | some q =>
    have hqm : some q ∈ TM1.stmts M B := (Finset.mem_product.mp hq').1
    have hs := safe_stmts M B hm hqm
    have hx : (TM1to0.trAux M a q v).2 = .write b := by
      have := congrArg (Option.map (fun (x : {l // l ∈ TM1to0.trStmts M B} × TM0.Stmt _) => x.2)) he
      simpa [FiniteTM0.machine,TM1to0.tr] using this
    exact trAux_write M a q v hs b hx

end FiniteAlgebraicEnvelopes.MachineRealization.TapeSafety

namespace FiniteAlgebraicEnvelopes.MachineRealization
open Turing
namespace WordEvaluator
open Turing.PartrecToTM2 StackLift RawTM StackTape
variable {S : Type} [Fintype S] [Primcodable S]
 theorem exists_safe_tape {f : List S →. List S} (hf : Partrec f) :
   ∃ (Λ : Type) (_ : Fintype Λ) (_ : Inhabited Λ)
     (M : TM0.Machine (TM2to1.Γ' K' (fun _ => Symbol S)) Λ) (start stop : Λ),
     TapeSafety.Preserves M ∧ ∀ w, StateTransition.eval (TM0.step M) ⟨start,tape w⟩ =
       (f w).map (fun out => ⟨stop,tape out⟩) := by
  classical
  obtain ⟨Λ,hΛ,M,start,hM⟩ := exists_raw hf
  let : Fintype Λ := hΛ
  let : Inhabited Λ := ⟨start⟩
  let N := TM2to1.tr M
  let P := TM1to0.tr N
  let B := TM2to1.trSupp M Finset.univ
  have hU : TM2.Supports M Finset.univ := by
    refine ⟨Finset.mem_univ _,fun q _ => ?_⟩
    induction M q <;> simp_all [TM2.SupportsStmt]
  have hB : TM1.Supports N B := TM2to1.tr_supports M hU
  let C := TM1to0.trStmts N B
  have hC : TM0.Supports P (C : Set _) := TM1to0.tr_supports N hB
  let : Inhabited {l // l ∈ C} := ⟨⟨default,hC.1⟩⟩
  have hs : (none,none) ∈ C := by
    change (none,none) ∈ (TM1.stmts N B) ×ˢ (Finset.univ : Finset (Store S))
    exact Finset.mem_product.mpr ⟨Finset.none_mem_insertNone,Finset.mem_univ _⟩
  refine ⟨{l // l ∈ C},inferInstance,inferInstance,FiniteTM0.machine P C hC,default,⟨(none,none),hs⟩,TapeSafety.finite_preserves N B hB (TapeSafety.safe_tr M),fun w => ?_⟩
  apply part_map_injective (FiniteTM0.embed_injective C)
  rw [←FiniteTM0.eval_embed P C hC]
  change StateTransition.eval (TM0.step P) (TM1to0.trCfg N ⟨some (.normal start),none,tape w⟩) = _
  rw [eval_post M start hM]
  simp only [Part.map_map]
  rfl

end WordEvaluator
end FiniteAlgebraicEnvelopes.MachineRealization

namespace FiniteAlgebraicEnvelopes.MachineRealization.TapeFold
open Turing Relation Compiler.Simulator
variable {K : Type} {Γ : K → Type} {Λ : Type} [Inhabited Λ]

 def Marked (s : OneSided.Cfg (Cell (TM2to1.Γ' K Γ)) (Side × Λ)) : Prop :=
  ∀ n, (s.cell n).pos.1 = decide (n=0) ∧ (s.cell n).neg.1 = false

end FiniteAlgebraicEnvelopes.MachineRealization.TapeFold

namespace FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral

section
open Turing Relation Compiler.Simulator TapeFold Turing.PartrecToTM2 StackLift RawTM StackTape
variable {S : Type} {Λ : Type} [Inhabited Λ]
abbrev Gamma (S : Type) := Cell (TM2to1.Γ' K' (fun _ => Symbol S))

theorem cell_ext (a b : Cell (TM2to1.Γ' K' (fun _ => Symbol S)))
    (ho : a.origin=b.origin) (hp : a.pos=b.pos) (hn : a.neg=b.neg) : a=b := by
  cases a; cases b; cases ho; cases hp; cases hn; rfl

def blank : Gamma S := ⟨false,default,default⟩
def input (a : S) : Gamma S := ⟨false,(false,slice a),default⟩
def raw (w : List S) : ℕ → Gamma S := Stream'.appendStream' (w.map input) (Stream'.const blank)
def canon (q : Λ) (w : List S) : OneSided.Cfg (Gamma S) (Side × Λ) :=
  ⟨(.pos,q),0,fun n => ⟨decide (n=0),(tape w).nth n,(tape w).nth (-(n+1:ℤ))⟩⟩

omit [Inhabited Λ] in
theorem canon_rel (q : Λ) (w : List S) : Rel (⟨q,tape w⟩ : TM0.Cfg _ _) (canon q w) := by
  refine ⟨rfl,fun n => ?_⟩
  simp [canon,position]

theorem tape_neg (w : List S) (n : ℕ) : (tape w).nth (-(n+1:ℤ)) = default := by
  change ListBlank.nth (∅ : ListBlank _) n = default
  rfl

theorem tape_fst (w : List S) (n : ℕ) : ((tape w).nth n).1 = decide (n=0) := by
  rw [tape,Tape.mk'_nth_nat]
  cases n with
  | zero => simpa only [ListBlank.nth_zero,decide_true] using TM2to1.addBottom_head_fst (stackList w)
  | succ n => exact TM2to1.addBottom_nth_succ_fst _ n

omit [Inhabited Λ] in
theorem canon_marked (q : Λ) (w : List S) : Marked (canon q w) := by
  intro n
  exact ⟨tape_fst w n,congrArg Prod.fst (tape_neg w n)⟩

theorem raw_cell (w : List S) (n : ℕ) : raw w n = ⟨false,(false,(stackList w).nth n),default⟩ := by
  induction w generalizing n with
  | nil => simp [raw,blank,stackList,ListBlank.nth_mk]; rfl
  | cons a w ih =>
    cases n with
    | zero => rfl
    | succ n => simpa only [raw,List.map_cons,Stream'.appendStream',Stream'.cons,stackList,ListBlank.nth_mk,List.getI_cons_succ] using ih n

def mark (c : Gamma S) : Gamma S := ⟨true,(true,c.pos.2),c.neg⟩
def clear (c : Gamma S) : Gamma S := ⟨false,(false,c.pos.2),c.neg⟩

omit [Inhabited Λ] in
theorem canon_cells (q : Λ) (w : List S) : (canon q w).cell = Function.update (raw w) 0 (mark (raw w 0)) := by
  funext n
  have hh : (canon q w).cell n = ⟨decide (n=0),(decide (n=0),(stackList w).nth n),default⟩ := by
    apply cell_ext
    · rfl
    · exact Prod.ext (tape_fst w n) (by
        change ((tape w).nth (n:ℤ)).2 = _
        rw [tape,Tape.mk'_nth_nat]
        exact TM2to1.addBottom_nth_snd (stackList w) n)
    · exact tape_neg w n
  rw [hh]
  by_cases hn : n=0
  · subst n
    rw [Function.update_self,raw_cell]
    rfl
  · rw [Function.update_of_ne hn,raw_cell]
    simp only [hn,decide_false]

omit [Inhabited Λ] in
theorem canon_clear (q : Λ) (w : List S) :
    Function.update (canon q w).cell 0 (clear ((canon q w).cell 0)) = raw w := by
  rw [canon_cells]
  simp only [Function.update_self]
  have hh : clear (mark (raw w 0)) = raw w 0 := by rw [raw_cell]; rfl
  rw [hh,Function.update_idem,Function.update_eq_self]

omit [Inhabited Λ] in
theorem rel_canon_unique {s : OneSided.Cfg (Gamma S) (Side × Λ)}
    (q : Λ) (w : List S) (hr : Rel (⟨q,tape w⟩ : TM0.Cfg _ _) s) (hm : Marked s) : s = canon q w := by
  have hh := congrArg Prod.fst (read_head hr)
  have hb : (tape w).head.1 = true := TM2to1.addBottom_head_fst _
  rw [hb] at hh
  have hp : s.state.1 = .pos ∧ s.pos = 0 := by
    cases hd : s.state.1 with
    | pos =>
      simp only [hd,TapeFold.read] at hh
      rw [(hm s.pos).1] at hh
      exact ⟨rfl,of_decide_eq_true hh⟩
    | neg => simp only [hd,TapeFold.read,(hm s.pos).2] at hh; cases hh
  rcases s with ⟨⟨d,l⟩,p,c⟩
  obtain ⟨rfl,rfl⟩ := hp
  obtain ⟨rfl,hc⟩ := hr
  congr 1
  funext n
  obtain ⟨ho,hp,hn⟩ := hc n
  apply cell_ext
  · exact ho
  · simpa only [canon,position,Int.natCast_zero,sub_zero] using hp
  · simpa only [canon,position,Int.natCast_zero,sub_zero] using hn

end

open Turing Relation Compiler.Simulator TapeFold Turing.PartrecToTM2 StackLift RawTM StackTape

end FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral

namespace FiniteAlgebraicEnvelopes.MachineRealization.After
open Relation StateTransition
variable {α β : Type*} (f : α → Option α) (g : β → Option β) (lift finish : α → β)
variable (hs : ∀ a, g (lift a) = (f a).elim (some (finish a)) (fun b => some (lift b)))
variable (hf : ∀ a, g (finish a) = none)
include hs hf

theorem path_cases {a : α} {z : β} (h : Reaches g (lift a) z) :
    (∃ b, Reaches f a b ∧ z=lift b) ∨ (∃ b, b ∈ eval f a ∧ z=finish b) := by
  induction h with
  | refl => exact Or.inl ⟨a,.refl,rfl⟩
  | @tail z z' _ hz ih =>
    change g z = some z' at hz
    rcases ih with ⟨b,hb,rfl⟩ | ⟨b,hb,rfl⟩
    · rw [hs] at hz
      cases hc : f b with
      | none =>
        simp only [hc,Option.elim_none,Option.some.injEq] at hz
        exact Or.inr ⟨b,mem_eval.mpr ⟨hb,hc⟩,hz.symm⟩
      | some c =>
        simp only [hc,Option.elim_some,Option.some.injEq] at hz
        exact Or.inl ⟨c,hb.tail hc,hz.symm⟩
    · rw [hf] at hz; cases hz

omit hf in
theorem lift_reaches {a b : α} (h : Reaches f a b) : Reaches g (lift a) (lift b) := by
  induction h with
  | refl => exact .refl
  | tail _ hc ih => exact ih.tail (by rw [hs,hc]; rfl)

theorem eval_lift (a : α) : eval g (lift a) = (eval f a).map finish := by
  apply Part.ext
  intro z
  constructor
  · intro hz
    obtain ⟨hp,hz⟩ := mem_eval.mp hz
    rcases path_cases f g lift finish hs hf hp with ⟨b,_,rfl⟩ | ⟨b,hb,rfl⟩
    · rw [hs] at hz
      cases hc : f b <;> simp [hc] at hz
    · exact Part.mem_map _ hb
  · intro hz
    obtain ⟨b,hb,rfl⟩ := (Part.mem_map_iff _).mp hz
    obtain ⟨hr,hb⟩ := mem_eval.mp hb
    apply mem_eval.mpr
    exact ⟨(lift_reaches f g lift finish hs hr).tail (by rw [hs,hb]; rfl),hf b⟩

end FiniteAlgebraicEnvelopes.MachineRealization.After

namespace FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral

section
open Turing Relation Compiler.Simulator TapeFold Turing.PartrecToTM2 StackLift RawTM StackTape
variable {S Λ : Type} [Inhabited Λ]
abbrev State (Λ : Type) := Option (Option (Side × Λ))

def lift (s : OneSided.Cfg (Gamma S) (Side × Λ)) : OneSided.Cfg (Gamma S) (State Λ) :=
  ⟨some (some s.state),s.pos,s.cell⟩
def finish (s : OneSided.Cfg (Gamma S) (Side × Λ)) : OneSided.Cfg (Gamma S) (State Λ) :=
  ⟨some none,s.pos,Function.update s.cell s.pos (clear (s.cell s.pos))⟩
def initial (w : List S) : OneSided.Cfg (Gamma S) (State Λ) := ⟨none,0,raw w⟩
def final (w : List S) : OneSided.Cfg (Gamma S) (State Λ) := ⟨some none,0,raw w⟩

variable (M : TM0.Machine (TM2to1.Γ' K' (fun _ => Symbol S)) Λ) (start : Λ)

omit [Inhabited Λ] in
theorem finish_canon (q : Λ) (w : List S) : finish (canon q w) = final (Λ := Λ) w := by
  simp only [finish,canon,final]
  congr 1
  exact canon_clear q w

end

open Turing Compiler.Simulator Turing.PartrecToTM2 StackLift StackTape
variable {S : Type} [DecidableEq S]

instance instFintypeK'_solutions : Fintype K' := ⟨{.main,.rev,.aux,.stack},by intro k; cases k <;> simp⟩

instance instDecidableEqΓ'K'Symbol : DecidableEq (TM2to1.Γ' K' (fun _ => Symbol S)) := by
  unfold TM2to1.Γ'; infer_instance

def output (c : Gamma S) : Option S := match c.pos.2 .main with
  | some (.inr a) => if c = input a then some a else none
  | _ => none

theorem output_decode (c : Gamma S) (a : S) (he : output c = some a) : c = input a := by
  unfold output at he
  cases hc : c.pos.2 .main with
  | none => simp [hc] at he
  | some s =>
    cases s with
    | inl b => simp [hc] at he
    | inr b =>
      simp only [hc] at he
      split_ifs at he with h
      · cases he; exact h

end FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral

namespace FiniteAlgebraicEnvelopes.Compiler.Simulator
open Relation
variable {S Γ Q : Type*} (A : Alphabet S Γ)

theorem take_constant (a : Γ) (n : ℕ) : Stream'.take n (Stream'.const a) = List.replicate n a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Stream'.take_succ,Stream'.tail_const,ih,List.replicate_succ]; rfl

end FiniteAlgebraicEnvelopes.Compiler.Simulator

namespace FiniteAlgebraicEnvelopes.MachineRealization.CodeMachine
open Turing Turing.ToPartrec Turing.PartrecToTM2 StackLift RawTM StackTape

variable (S : Type) [Fintype S] [Primcodable S] [DecidableEq S]

/-- A literal raw-letter stack program, with its finite control part. -/
structure Raw where
  Q : Type
  finiteQ : Fintype Q
  start : Q
  code : Q → TM2.Stmt (fun _ : K' => Symbol S) Q (Store S)

attribute [instance] Raw.finiteQ

/-- A finite tape machine with distinguished literal input/output states. -/
structure TapeProgram where
  Q : Type
  finiteQ : Fintype Q
  [inhabitedQ : Inhabited Q]
  start : Q
  stop : Q
  code : TM0.Machine (TM2to1.Γ' K' (fun _ => Symbol S)) Q
  safe : TapeSafety.Preserves code

attribute [instance] TapeProgram.finiteQ TapeProgram.inhabitedQ

end FiniteAlgebraicEnvelopes.MachineRealization.CodeMachine

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteCompiler_UniformMachines
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Parameterized effective machine realization and uniform finite data.
-/

namespace FiniteAlgebraicEnvelopes.MachineRealization.ParameterMachine
open Compiler.Simulator OneSided Turing Relation
variable {S Γ Q : Type*}

inductive State (Q : Type*) (n : ℕ)
  | start | scan | emit : Fin (n+2) → State Q n
  | rewind | run : Q → State Q n
  deriving DecidableEq, Fintype

variable (A : Alphabet S Γ)
  [DecidableEq Γ]

variable (p : S) (n : ℕ)

def lift (c : Cfg Γ Q) : Cfg (Bool × Γ) (State Q n) :=
  ⟨.run c.state,c.pos,fun i => (false,c.cell i)⟩

end FiniteAlgebraicEnvelopes.MachineRealization.ParameterMachine

namespace FiniteAlgebraicEnvelopes.MachineRealization.ParameterCode
open Compiler.Simulator ParameterMachine
variable {S Γ Q : Type*}

/-- A common, countably coded state space for all unary-initialized programs. -/
abbrev Control (Q : Type*) := ℕ ⊕ Q

def encode (n : ℕ) : State Q n → Control Q
  | .start => .inl 0
  | .scan => .inl 1
  | .rewind => .inl 2
  | .emit k => .inl (k.val+3)
  | .run q => .inr q

def decode (n : ℕ) : Control Q → Option (State Q n)
  | .inr q => some (.run q)
  | .inl 0 => some .start
  | .inl 1 => some .scan
  | .inl 2 => some .rewind
  | .inl (k+3) => if h : k<n+2 then some (.emit ⟨k,h⟩) else none

@[simp] theorem decode_encode (n : ℕ) (q : State Q n) : decode n (encode n q)=some q := by
  cases q <;> simp [encode,decode]

 theorem encode_injective (n : ℕ) : Function.Injective (encode (Q := Q) n) := by
  intro a b h
  have h' := congrArg (decode n) h
  simpa only [decode_encode, Option.some.injEq] using h'

variable (A : Alphabet S Γ)
  [DecidableEq Γ]
  (p : S)

variable [Fintype Q] [Fintype Γ] [Primcodable Q] [Primcodable Γ]

noncomputable def support (n : ℕ) : List (Control Q) :=
  ((List.range (n+5)).map Sum.inl) ++ (((Finset.univ : Finset Q).toList).map Sum.inr)

omit [Primcodable Q] in
 theorem mem_support (n : ℕ) (q : State Q n) : encode n q ∈ support (Q := Q) n := by
  cases q <;> simp [support,encode]

 theorem primrec_support : Primrec (support (Q := Q)) := by
  exact Primrec.list_append.comp
    (Primrec.list_map (Primrec.list_range.comp (Primrec.nat_add.comp Primrec.id (Primrec.const 5)))
      (Primrec.sumInl.comp Primrec.snd).to₂) (Primrec.const _)

end FiniteAlgebraicEnvelopes.MachineRealization.ParameterCode

namespace FiniteAlgebraicEnvelopes.Effect.Graph
variable {P α : Type*} [Primcodable P] [Primcodable α] [DecidableEq α]

omit [DecidableEq α] in
/-- Finite weak-component search is primitive recursive uniformly in a
    primitive-recursive edge table, not just separately at every table. -/
theorem primrec_expand_family {r : P → α → α → Bool}
    (hr : Primrec (fun x : P × α × α => r x.1 x.2.1 x.2.2)) :
    Primrec (fun x : P × List α × List α => expand (r x.1) x.2.1 x.2.2) := by
  apply Primrec.list_append.comp (Primrec.snd.comp Primrec.snd)
  apply primrec_listFilter (Primrec.fst.comp Primrec.snd)
  unfold Primrec₂
  apply primrec_listAny (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  unfold Primrec₂
  let X := ((P × List α × List α) × α) × α
  have hp : Primrec (fun x : X => x.1.1.1) := Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have ha : Primrec (fun x : X => x.2) := Primrec.snd
  have hb : Primrec (fun x : X => x.1.2) := Primrec.snd.comp Primrec.fst
  exact Primrec.or.comp (hr.comp (hp.pair (ha.pair hb))) (hr.comp (hp.pair (hb.pair ha)))

omit [DecidableEq α] in
theorem primrec_search_family {r : P → α → α → Bool}
    (hr : Primrec (fun x : P × α × α => r x.1 x.2.1 x.2.2)) :
    Primrec (fun x : (P × List α × α) × ℕ => search (r x.1.1) x.1.2.1 x.1.2.2 x.2) := by
  change Primrec₂ (fun (x : P × List α × α) n => search (r x.1) x.2.1 x.2.2 n)
  exact (Primrec.nat_rec
    (Primrec.list_cons.comp (Primrec.snd.comp Primrec.snd) (Primrec.const []))
    ((primrec_expand_family hr).comp
      ((Primrec.fst.comp Primrec.fst).pair
        ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair
          (Primrec.snd.comp Primrec.snd)))).to₂).of_eq
            (fun x n => by induction n <;> simp_all [search])

omit [DecidableEq α] in
theorem primrec_component_family {r : P → α → α → Bool}
    (hr : Primrec (fun x : P × α × α => r x.1 x.2.1 x.2.2)) :
    Primrec (fun x : P × List α × α => component (r x.1) x.2.1 x.2.2) :=
  (primrec_search_family hr).comp
    (Primrec.id.pair (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd)))

end FiniteAlgebraicEnvelopes.Effect.Graph

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteCompiler_UniformPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Uniform surface and path normalization with recursive compiler interfaces.
-/

namespace FiniteAlgebraicEnvelopes.Effect
variable {α β γ : Type*} [Primcodable α] [Primcodable β] [Primcodable γ]
theorem primrec_sumElim {f : α → γ} {g : β → γ} (hf : Primrec f) (hg : Primrec g) :
    Primrec (Sum.elim f g) := by
  exact (Primrec.sumCasesOn Primrec.id (hf.comp Primrec.snd).to₂
    (hg.comp Primrec.snd).to₂).of_eq fun x => by cases x <;> rfl
end FiniteAlgebraicEnvelopes.Effect

namespace FiniteAlgebraicEnvelopes.Effect.Graph
variable {α β : Type*}
variable (i : α → β) (r : α → α → Bool) (s : β → β → Bool)
variable (h : ∀ a b,s (i a) (i b)=r a b)

include h in
theorem expand_map (u v : List α) : expand s (u.map i) (v.map i)=(expand r u v).map i := by
  simp only [expand,List.map_append,List.any_map]
  rw [List.filter_map]
  simp only [Function.comp_def,h]

include h in
theorem search_map (u : List α) (a : α) (n : ℕ) :
    search s (u.map i) (i a) n=(search r u a n).map i := by
  induction n with
  | zero => rfl
  | succ n ih => rw [search,ih,expand_map i r s h,←search]

include h in
theorem component_map (u : List α) (a : α) :
    component s (u.map i) (i a)=(component r u a).map i := by
  simp only [component,List.length_map,search_map i r s h]

end FiniteAlgebraicEnvelopes.Effect.Graph

namespace FiniteAlgebraicEnvelopes.Effect.Graph
variable {α : Type*} [DecidableEq α]

theorem expand_ext_universe (r : α → α → Bool) {u v s t : List α}
    (hu : u.toFinset=v.toFinset) (hs : s.toFinset=t.toFinset) :
    (expand r u s).toFinset=(expand r v t).toFinset := by
  have huu : ∀ a,a∈u ↔ a∈v := fun a => by simpa using Finset.ext_iff.mp hu a
  have hss : ∀ a,a∈s ↔ a∈t := fun a => by simpa using Finset.ext_iff.mp hs a
  ext a
  simp only [List.mem_toFinset,mem_expand,huu,hss]

theorem search_ext_universe (r : α → α → Bool) {u v : List α}
    (hu : u.toFinset=v.toFinset) (a : α) (n : ℕ) :
    (search r u a n).toFinset=(search r v a n).toFinset := by
  induction n with
  | zero => rfl
  | succ n ih => exact expand_ext_universe r hu ih

theorem search_add_stable (r : α → α → Bool) {u : List α} {a : α} (ha : a∈u) (k : ℕ) :
    (search r u a (u.length+k)).toFinset=(component r u a).toFinset := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (expand r u (search r u a (u.length+k))).toFinset=(component r u a).toFinset
    rw [expand_ext r u ih]
    exact search_stable r ha

theorem component_ext_universe (r : α → α → Bool) {u v : List α}
    (hu : u.toFinset=v.toFinset) {a : α} (ha : a∈u) :
    (component r u a).toFinset=(component r v a).toFinset := by
  have hv : a∈v := by
    apply List.mem_toFinset.mp
    rw [←hu]
    exact List.mem_toFinset.mpr ha
  rw [←search_add_stable r ha v.length,←search_add_stable r hv u.length,Nat.add_comm v.length]
  exact search_ext_universe r hu a _
end FiniteAlgebraicEnvelopes.Effect.Graph

namespace FiniteAlgebraicEnvelopes.Effect
variable {P α β : Type*} [Primcodable P] [Primcodable α] [Primcodable β]

omit [Primcodable P] [Primcodable α] [Primcodable β] in
theorem traverse_map_parameter (f : P × α → Part β) (p : P) (l : List α) :
    traverse f (l.map (p,·))=traverse (fun a => f (p,a)) l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons,traverse,ih]

theorem partrec_traverse_family {f : P × α → Part β} (hf : Partrec f) :
    Partrec (fun x : P × List α => traverse (fun a => f (x.1,a)) x.2) := by
  have hp : Primrec (fun x : P × List α => x.2.map (x.1,·)) :=
    Primrec.list_map Primrec.snd ((Primrec.fst.comp Primrec.fst).pair Primrec.snd).to₂
  exact ((partrec_traverse hf).comp hp.to_comp).of_eq fun x => traverse_map_parameter f x.1 x.2
end FiniteAlgebraicEnvelopes.Effect

namespace FiniteAlgebraicEnvelopes.Effect
variable {α β : Type*}

theorem priorityList_map (i : α → β) (p q : α → Bool) (p' q' : β → Bool)
    (hp : ∀ a,p' (i a)=p a) (hq : ∀ a,q' (i a)=q a) (s : List α) :
    priorityList p' q' (s.map i)=(priorityList p q s).map i := by
  have he (f : α → Bool) (g : β → Bool) (h : ∀ a,g (i a)=f a) :
      (s.map i).filter g=(s.filter f).map i := by
    rw [List.filter_map]; simp only [Function.comp_def,h]
  simp only [priorityList,he p p' hp,he q q' hq,List.isEmpty_map]
  split <;> first | rfl | (split <;> rfl)

theorem priorityList_ext [Primcodable α] [DecidableEq α] (p q : α → Bool) {s t : List α}
    (he : s.toFinset=t.toFinset) :
    (priorityList p q s).toFinset=(priorityList p q t).toFinset := by
  simp only [priorityList_toFinset,he]

variable [LinearOrder α] [LinearOrder β]

theorem minList_map (i : α → β) (hi : Monotone i) (s : List α) :
    (s.map i).min?=s.min?.map i := by
  cases h : s.min? with
  | none =>
    have hs := List.min?_eq_none_iff.mp h
    subst s; rfl
  | some a =>
    simp only [Option.map_some]
    obtain ⟨ha,hm⟩ := List.min?_eq_some_iff.mp h
    apply List.min?_eq_some_iff.mpr
    refine ⟨List.mem_map.mpr ⟨a,ha,rfl⟩,?_⟩
    rintro b hb
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hb
    exact hi (hm c hc)

theorem minList_ext [DecidableEq α] {s t : List α} (he : s.toFinset=t.toFinset) :
    s.min?=t.min? := by
  have hm : ∀ a,a∈s ↔ a∈t := fun a => by simpa using Finset.ext_iff.mp he a
  apply Option.ext
  intro a
  simp only [List.min?_eq_some_iff,hm]

end FiniteAlgebraicEnvelopes.Effect

namespace FiniteAlgebraicEnvelopes.MachineRealization.ParameterCode

section
open Compiler Compiler.Simulator ParameterMachine
variable {S Γ Q : Type*}

variable (A : Alphabet S Γ)
  [DecidableEq Γ]
  (p : S)

variable [Fintype Q] [Fintype Γ] [Primcodable Q] [Primcodable Γ]

omit [Primcodable Q] in
theorem mem_support_iff (n : ℕ) (q : Control Q) :
    q∈support n ↔ ∃ a : State Q n,encode n a=q := by
  constructor
  · intro h
    cases q with
    | inr q => exact ⟨.run q,rfl⟩
    | inl k =>
      have hk : k<n+5 := by simpa [support] using h
      by_cases h0 : k=0
      · subst k; exact ⟨.start,rfl⟩
      by_cases h1 : k=1
      · subst k; exact ⟨.scan,rfl⟩
      by_cases h2 : k=2
      · subst k; exact ⟨.rewind,rfl⟩
      refine ⟨.emit ⟨k-3,by omega⟩,?_⟩
      simp only [encode,Sum.inl.injEq]
      omega
  · rintro ⟨a,rfl⟩
    exact mem_support n a

end

open Compiler Compiler.Simulator ParameterMachine

end FiniteAlgebraicEnvelopes.MachineRealization.ParameterCode

namespace FiniteAlgebraicEnvelopes.Compiler.RawRuns
variable {C D S : Type*} (i : C → D)

def Action.mapKeep : Action C S → Action D S
  | .keep c => .keep (i c)
  | .raw w => .raw w
  | .call w => .call w

end FiniteAlgebraicEnvelopes.Compiler.RawRuns

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteCompiler_SelfReference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Controlled shorter-input evaluator calls, fixed points, totality, and tested-class realization.
-/

namespace FiniteAlgebraicEnvelopes.Bootstrap
namespace Projection
variable {A B : Type*}
def left (w : List (A ⊕ B)) : List A :=
  w.filterMap (fun a => match a with | .inl a => some a | .inr _ => none)
def right (w : List (A ⊕ B)) : List B :=
  w.filterMap (fun a => match a with | .inl _ => none | .inr b => some b)

@[simp] theorem left_append (u v : List (A ⊕ B)) : left (u++v)=left u++left v := List.filterMap_append
@[simp] theorem right_append (u v : List (A ⊕ B)) : right (u++v)=right u++right v := List.filterMap_append

variable [Primcodable A] [Primcodable B]
 theorem primrec_left : Primrec (left (A:=A) (B:=B)) := by
  have hh : Primrec (fun a : A ⊕ B => match a with | .inl a => some a | .inr _ => none) :=
    (Primrec.sumCasesOn Primrec.id (Primrec.option_some.comp Primrec.snd).to₂
      (Primrec.const none).to₂).of_eq (by intro a; cases a <;> rfl)
  exact Primrec.listFilterMap Primrec.id (hh.comp Primrec.snd).to₂
 theorem primrec_right : Primrec (right (A:=A) (B:=B)) := by
  have hh : Primrec (fun a : A ⊕ B => match a with | .inl _ => none | .inr b => some b) :=
    (Primrec.sumCasesOn Primrec.id (Primrec.const none).to₂
      (Primrec.option_some.comp Primrec.snd).to₂).of_eq (by intro a; cases a <;> rfl)
  exact Primrec.listFilterMap Primrec.id (hh.comp Primrec.snd).to₂
end Projection

end FiniteAlgebraicEnvelopes.Bootstrap

namespace FiniteAlgebraicEnvelopes.Bootstrap.Uniform

section
variable {P A S Q : Type*} [DecidableEq A] [DecidableEq S] [DecidableEq Q]

def pickStep (lt : List A → List A → Bool) (q : Option Q) (best : List A)
    (v : List A × Option Q) : List A :=
  if v.2=q ∧ lt v.1 best=true then v.1 else best

def pick (lt : List A → List A → Bool) (ps : List (List A × Option Q))
    (w : List A) (q : Option Q) : List A := ps.foldl (pickStep lt q) w

def output (code : List A → List S) (lt : List A → List A → Bool) (z : S)
    (ps : List (List A × Option Q)) (v : List A × Option Q) : List S :=
  if v.2=none then [z] else code (pick lt ps v.1 v.2)

def table (code : List A → List S) (lt : List A → List A → Bool) (z : S)
    (ps : List (List A × Option Q)) : List (List S × List S) :=
  ps.flatMap fun v => if v.1≠[] ∧ output code lt z ps v≠code v.1 then
    [(code v.1,output code lt z ps v)] else []

section Computability
variable [Primcodable P] [Primcodable A] [Primcodable S] [Primcodable Q]
  (code : P → List A → List S) (lt : P → List A → List A → Bool) (z : S)
  (hc : Primrec₂ code) (hl : Primrec (fun x : P × List A × List A => lt x.1 x.2.1 x.2.2))
variable {X : Type*} [Primcodable X]

omit [DecidableEq A] in
include hl in
 theorem primrec_pickStep {p : X → P} {q : X → Option Q} {best : X → List A}
    {v : X → List A × Option Q} (hp : Primrec p) (hq : Primrec q)
    (hb : Primrec best) (hv : Primrec v) :
    Primrec (fun x => pickStep (lt (p x)) (q x) (best x) (v x)) :=
  Primrec.ite ((Primrec.eq.comp (Primrec.snd.comp hv) hq).and
    (Primrec.eq.comp (hl.comp (hp.pair ((Primrec.fst.comp hv).pair hb))) (Primrec.const true)))
    (Primrec.fst.comp hv) hb

omit [DecidableEq A] in
include hl in
 theorem primrec_pick {p : X → P} {q : X → Option Q} {w : X → List A}
    {ps : X → List (List A × Option Q)} (hp : Primrec p) (hq : Primrec q)
    (hw : Primrec w) (hps : Primrec ps) :
    Primrec (fun x => pick (lt (p x)) (ps x) (w x) (q x)) :=
  Primrec.list_foldl hps hw (primrec_pickStep lt hl (hp.comp Primrec.fst)
    (hq.comp Primrec.fst) (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂

omit [DecidableEq A] [DecidableEq S] in
include hc hl in
 theorem primrec_output : Primrec (fun x : P × List (List A × Option Q) × (List A × Option Q) =>
    output (code x.1) (lt x.1) z x.2.1 x.2.2) := by
  have hv : Primrec (fun x : P × List (List A × Option Q) × (List A × Option Q) => x.2.2) :=
    Primrec.snd.comp Primrec.snd
  exact Primrec.ite (Primrec.eq.comp (Primrec.snd.comp hv) (Primrec.const none))
    (Primrec.const [z]) (hc.comp Primrec.fst (primrec_pick lt hl Primrec.fst
      (Primrec.snd.comp hv) (Primrec.fst.comp hv) (Primrec.fst.comp Primrec.snd)))

omit [DecidableEq A] in
include hc hl in
 theorem primrec_table : Primrec (fun x : P × List (List A × Option Q) => table (code x.1) (lt x.1) z x.2) := by
  apply Primrec.list_flatMap Primrec.snd
  have hp : Primrec (fun x : (P × List (List A × Option Q)) × (List A × Option Q) => x.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hout := (primrec_output code lt z hc hl).comp
    (hp.pair ((Primrec.snd.comp Primrec.fst).pair Primrec.snd))
  have hcode := hc.comp hp (Primrec.fst.comp Primrec.snd)
  exact (Primrec.ite ((Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const [])).not.and
    (Primrec.eq.comp hout hcode).not)
    (Primrec.list_cons.comp (hcode.pair hout) (Primrec.const [])) (Primrec.const [])).to₂

end Computability

end

end FiniteAlgebraicEnvelopes.Bootstrap.Uniform

namespace FiniteAlgebraicEnvelopes.Bootstrap.Source
open Compiler Compiler.Simulator MachineRealization

variable {G : Type*} [Group G] {k : ℕ} (s : Fin k → G)
variable {Γ Q : Type*} [Fintype Γ] [Fintype Q] [DecidableEq Γ] [DecidableEq Q]
  [Primcodable Γ] [Primcodable Q]
abbrev Z (k : ℕ) := Fin k × Bool

end FiniteAlgebraicEnvelopes.Bootstrap.Source

end OAI
end

section
-- module Solutions.OAIQ066_SO.BooneHigman_MonoidAlgebras
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Finite compiler monoids, zero products, both F₂ algebras, and selector constructions.
-/

namespace FiniteAlgebraicEnvelopes

namespace Bootstrap
namespace Projection
variable {A B C D : Type*}
@[simp] theorem left_map (f : A → C) (g : B → D) (w : List (A ⊕ B)) :
    left (w.map (Sum.map f g))=(left w).map f := by
  induction w with
  | nil => rfl
  | cons a w ih => cases a with
    | inl a => exact congrArg (f a :: ·) ih
    | inr b => exact ih
@[simp] theorem right_map (f : A → C) (g : B → D) (w : List (A ⊕ B)) :
    right (w.map (Sum.map f g))=(right w).map g := by
  induction w with
  | nil => rfl
  | cons a w ih => cases a with
    | inl a => exact ih
    | inr b => exact congrArg (g b :: ·) ih
end Projection

end Bootstrap

end FiniteAlgebraicEnvelopes

namespace FiniteAlgebraicEnvelopes.Bootstrap.Source
open Compiler Compiler.Simulator MachineRealization
variable {G : Type*} [Group G] {k : ℕ} (s : Fin k → G)
variable (h : ComputablePred (fun w : FiniteAlgebraicEnvelopes.Word k => evalWord s w=1))

def groupEval : FreeMonoid (Z k) →* G where
  toFun w := evalWord s w.toList
  map_one' := rfl
  map_mul' u v := WordProblem.evalWord_append s u.toList v.toList

 theorem groupEval_surjective (hs : Subgroup.closure (Set.range s)=⊤) : Function.Surjective (groupEval s) := by
  intro g
  obtain ⟨w,hw⟩ := FreeGroup.lift_surjective_iff_closure_range_eq_top.mpr hs g
  refine ⟨FreeMonoid.ofList (FreeGroup.toWord w),?_⟩
  change evalWord s (FreeGroup.toWord w)=g
  rw [WordProblem.evalWord_eq_lift,FreeGroup.mk_toWord]
  exact hw

end FiniteAlgebraicEnvelopes.Bootstrap.Source

namespace FiniteAlgebraicEnvelopes.ContractedPresentation

section
variable (k S : Type*) [CommRing k]
variable (rel : FreeMonoid S → FreeMonoid S → Prop)
variable {M : Type*} [MonoidWithZero M] (e : PresentedMonoid rel ≃* M)
variable (z : FreeMonoid S) (hz : e (PresentedMonoid.mk rel z)=0)

def word : FreeMonoid S →* FreeAlgebra k S := FreeMonoid.lift (FreeAlgebra.ι k)

def Rel (a b : FreeAlgebra k S) : Prop :=
  (∃ u v, rel u v ∧ a=word k S u ∧ b=word k S v) ∨ (a=word k S z ∧ b=0)

abbrev Presentation := RingQuot (Rel k S rel z)

def generator (x : S) : Presentation k S rel z :=
  RingQuot.mkAlgHom k (Rel k S rel z) (FreeAlgebra.ι k x)

theorem word_generator (u : FreeMonoid S) :
    FreeMonoid.lift (generator k S rel z) u=RingQuot.mkAlgHom k (Rel k S rel z) (word k S u) := by
  have hh : FreeMonoid.lift (generator k S rel z)=
      (RingQuot.mkAlgHom k (Rel k S rel z)).toMonoidHom.comp (word k S) := by
    apply FreeMonoid.hom_eq
    intro x
    rfl
  exact DFunLike.congr_fun hh u

def monoidEval : M →* Presentation k S rel z :=
  (PresentedMonoid.lift (generator k S rel z) (by
    intro a b hab
    rw [word_generator,word_generator]
    exact RingQuot.mkAlgHom_rel k (Or.inl ⟨a,b,hab,rfl,rfl⟩))).comp e.symm.toMonoidHom

theorem monoidEval_mk (u : FreeMonoid S) :
    monoidEval k S rel e z (e (PresentedMonoid.mk rel u))=
      RingQuot.mkAlgHom k (Rel k S rel z) (word k S u) := by
  unfold monoidEval
  simp only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,e.symm_apply_apply]
  exact word_generator k S rel z u

include hz in
theorem monoidEval_zero : monoidEval k S rel e z 0=0 := by
  rw [←hz,monoidEval_mk]
  have he := RingQuot.mkAlgHom_rel k (s:=Rel k S rel z) (Or.inr ⟨rfl,rfl⟩)
  simpa only [map_zero] using he

def toPresentation : Contracted.Algebra k M →ₐ[k] Presentation k S rel z :=
  let f := MonoidAlgebra.lift k (Presentation k S rel z) M (monoidEval k S rel e z)
  let hf : f (MonoidAlgebra.single (0:M) 1)=0 := by
    rw [MonoidAlgebra.lift_single,one_smul,monoidEval_zero k S rel e z hz]
  let g := Contracted.lift f.toNonUnitalAlgHom hf
  { g with
    map_one' := by
      change g (Contracted.quotient k M 1)=1
      exact (Contracted.lift_quotient f.toNonUnitalAlgHom hf 1).trans (map_one f)
    commutes' := by
      intro r
      change g (algebraMap k (Contracted.Algebra k M) r)=_
      rw [Algebra.algebraMap_eq_smul_one,map_smul]
      have he : g 1=1 := by
        change g (Contracted.quotient k M 1)=1
        exact (Contracted.lift_quotient f.toNonUnitalAlgHom hf 1).trans (map_one f)
      rw [he,Algebra.algebraMap_eq_smul_one] }

@[simp] theorem toPresentation_basis (m : M) (r : k) :
    toPresentation k S rel e z hz (Contracted.basis k M m r)=r • monoidEval k S rel e z m := by
  exact MonoidAlgebra.lift_single _ _ _

def monoidBasis : M →* Contracted.Algebra k M where
  toFun m := Contracted.basis k M m 1
  map_one' := Contracted.basis_identity k M
  map_mul' a b := by rw [Contracted.basis_mul,one_mul]

def freeEval : FreeAlgebra k S →ₐ[k] Contracted.Algebra k M :=
  FreeAlgebra.lift k (fun x => monoidBasis k (e (PresentedMonoid.of rel x)))

theorem freeEval_word (u : FreeMonoid S) :
    freeEval k S rel e (word k S u)=Contracted.basis k M (e (PresentedMonoid.mk rel u)) 1 := by
  have hh : (freeEval k S rel e).toMonoidHom.comp (word k S)=
      (monoidBasis k).comp (e.toMonoidHom.comp (PresentedMonoid.mk rel)) := by
    apply FreeMonoid.hom_eq
    intro x
    simp [word,freeEval]
    rfl
  exact DFunLike.congr_fun hh u

include hz in
theorem freeEval_respects : ∀ ⦃a b⦄, Rel k S rel z a b → freeEval k S rel e a=freeEval k S rel e b := by
  intro a b hab
  rcases hab with ⟨u,v,hu,rfl,rfl⟩|⟨rfl,rfl⟩
  · rw [freeEval_word,freeEval_word,PresentedMonoid.mk_eq_mk_of_rel hu]
  · rw [freeEval_word,hz,Contracted.basis_zero,map_zero]

def fromPresentation : Presentation k S rel z →ₐ[k] Contracted.Algebra k M :=
  RingQuot.liftAlgHom k ⟨freeEval k S rel e,freeEval_respects k S rel e z hz⟩

@[simp] theorem fromPresentation_mk (a : FreeAlgebra k S) :
    fromPresentation k S rel e z hz (RingQuot.mkAlgHom k (Rel k S rel z) a)=freeEval k S rel e a := by
  exact RingQuot.liftAlgHom_mkAlgHom_apply _ _ _ _

end

variable (k S : Type*) [CommRing k]
variable (rel : FreeMonoid S → FreeMonoid S → Prop)
variable {M : Type*} [MonoidWithZero M] (e : PresentedMonoid rel ≃* M)
variable (z : FreeMonoid S) (hz : e (PresentedMonoid.mk rel z)=0)

theorem from_to_basis (m : M) (r : k) :
    fromPresentation k S rel e z hz (toPresentation k S rel e z hz (Contracted.basis k M m r))=
      Contracted.basis k M m r := by
  obtain ⟨u,hu⟩ := PresentedMonoid.surjective_mk (e.symm m)
  have hm : m=e (PresentedMonoid.mk rel u) := by rw [hu,e.apply_symm_apply]
  rw [hm,toPresentation_basis,map_smul,monoidEval_mk,fromPresentation_mk,freeEval_word]
  simp [Contracted.basis,←map_smul]

theorem from_to : (fromPresentation k S rel e z hz).comp (toPresentation k S rel e z hz)=AlgHom.id k _ := by
  apply DFunLike.ext
  intro a
  obtain ⟨a,rfl⟩ := (Contracted.zeroIdeal k M).ringCon.mkₐ_surjective (α:=k) a
  change fromPresentation k S rel e z hz (toPresentation k S rel e z hz (Contracted.quotient k M a))=Contracted.quotient k M a
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add,ha,hb]
  | single m r => exact from_to_basis k S rel e z hz m r

theorem to_from : (toPresentation k S rel e z hz).comp (fromPresentation k S rel e z hz)=AlgHom.id k _ := by
  apply RingQuot.ringQuot_ext'
  apply FreeAlgebra.hom_ext
  funext x
  change toPresentation k S rel e z hz
    (fromPresentation k S rel e z hz (RingQuot.mkAlgHom k (Rel k S rel z) (FreeAlgebra.ι k x)))=_
  rw [fromPresentation_mk]
  change toPresentation k S rel e z hz
    (FreeAlgebra.lift k _ (FreeAlgebra.ι k x))=_
  rw [FreeAlgebra.lift_ι_apply]
  change toPresentation k S rel e z hz
    (Contracted.basis k M (e (PresentedMonoid.mk rel (FreeMonoid.of x))) 1)=_
  rw [toPresentation_basis,one_smul,monoidEval_mk]
  rfl

/-- Exact finite algebra presentation: replace the monoid equations by the same
    free-algebra equations and set a representative of monoid zero equal to zero. -/
def equivalence : Presentation k S rel z ≃ₐ[k] Contracted.Algebra k M :=
  AlgEquiv.ofAlgHom (fromPresentation k S rel e z hz) (toPresentation k S rel e z hz)
    (from_to k S rel e z hz) (to_from k S rel e z hz)

theorem finite_relations (hrel : {p : FreeMonoid S × FreeMonoid S | rel p.1 p.2}.Finite) :
    {p : FreeAlgebra k S × FreeAlgebra k S | Rel k S rel z p.1 p.2}.Finite := by
  apply ((hrel.image (fun p => (word k S p.1, word k S p.2))).union
    (Set.finite_singleton (word k S z,0))).subset
  rintro ⟨a,b⟩ hab
  rcases hab with ⟨u,v,hu,rfl,rfl⟩|⟨rfl,rfl⟩
  · exact Or.inl ⟨(u,v),hu,rfl⟩
  · exact Or.inr rfl

end FiniteAlgebraicEnvelopes.ContractedPresentation

namespace FiniteAlgebraicEnvelopes.ZeroProduct
variable (K P : Type*) [MonoidWithZero K] [Monoid P]

/-- Collapse precisely the pairs whose first coordinate is zero. This quotient
    is the zero product `(K \ {0}) × P ⊔ {0}` from the algebra construction. -/
def cong : Con (K × P) where
  r a b := a=b ∨ a.1=0 ∧ b.1=0
  iseqv := {
    refl := fun _ => Or.inl rfl
    symm := by intro a b h; rcases h with h | h; exact Or.inl h.symm; exact Or.inr h.symm
    trans := by
      intro a b c hab hbc
      rcases hab with rfl | hab
      · exact hbc
      rcases hbc with rfl | hbc
      · exact Or.inr hab
      exact Or.inr ⟨hab.1,hbc.2⟩ }
  mul' := by
    intro a b c d hab hcd
    rcases hab with rfl | hab
    · rcases hcd with rfl | hcd
      · exact Or.inl rfl
      · exact Or.inr ⟨by simp [hcd.1],by simp [hcd.2]⟩
    · exact Or.inr ⟨by simp [hab.1],by simp [hab.2]⟩

abbrev Mon := (cong K P).Quotient

def pair : K × P →* Mon K P := (cong K P).mk'

instance instZeroMon : Zero (Mon K P) := ⟨pair K P (0,1)⟩

 theorem pair_eq_iff (a b : K × P) : pair K P a=pair K P b ↔ a=b ∨ a.1=0 ∧ b.1=0 :=
  (cong K P).eq

 theorem pair_zero (p : P) : pair K P (0,p)=0 :=
  (pair_eq_iff K P _ _).mpr (Or.inr ⟨rfl,rfl⟩)

 theorem pair_eq_zero (a : K × P) : pair K P a=0 ↔ a.1=0 := by
  rw [show (0 : Mon K P)=pair K P (0,1) from rfl,pair_eq_iff]
  constructor
  · rintro (h | h)
    · exact congrArg Prod.fst h
    · exact h.1
  · exact fun h => Or.inr ⟨h,rfl⟩

 theorem pair_surjective : Function.Surjective (pair K P) := by
  intro a
  induction a using Con.induction_on
  exact ⟨_,rfl⟩

instance instMonoidWithZeroMon : MonoidWithZero (Mon K P) where
  __ := (inferInstance : Monoid (Mon K P))
  zero := pair K P (0,1)
  zero_mul a := by
    obtain ⟨a,rfl⟩ := pair_surjective K P a
    change pair K P (0,1)*pair K P a=0
    rw [←map_mul]
    exact (pair_eq_zero K P _).mpr (zero_mul _)
  mul_zero a := by
    obtain ⟨a,rfl⟩ := pair_surjective K P a
    change pair K P a*pair K P (0,1)=0
    rw [←map_mul]
    exact (pair_eq_zero K P _).mpr (mul_zero _)

end FiniteAlgebraicEnvelopes.ZeroProduct

section
namespace FiniteAlgebraicEnvelopes.Contracted
open MonoidAlgebra
variable {k H J : Type*} [CommRing k] [MonoidWithZero H] [MonoidWithZero J]

theorem coefficient_map (c : H →*₀ J) (hc : Function.Injective c)
    (h : H) (hh : h≠0) (x : Algebra k H) :
    coefficient (c h) (fun he => hh (hc (he.trans c.map_zero.symm))) (map (k:=k) c x)=coefficient h hh x := by
  obtain ⟨f,rfl⟩ := (zeroIdeal k H).ringCon.mkₐ_surjective (α:=k) x
  change coefficient (c h) _ (map c (quotient k H f))=coefficient h hh (quotient k H f)
  induction f using MonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg => simpa only [map_add] using congrArg₂ (·+·) hf hg
  | single g r =>
    change coefficient (c h) _ (map c (basis k H g r))=coefficient h hh (basis k H g r)
    rw [map_basis,coefficient_basis,coefficient_basis]
    congr 1
    exact propext hc.eq_iff

theorem map_injective (c : H →*₀ J) (hc : Function.Injective c) :
    Function.Injective (map (k:=k) c) := by
  intro x y he
  apply coefficient_ext
  intro h hh
  rw [←coefficient_map c hc h hh,←coefficient_map c hc h hh,he]
end FiniteAlgebraicEnvelopes.Contracted

end

namespace FiniteAlgebraicEnvelopes.ZeroProduct
open scoped TensorProduct
open Contracted
variable (k K P : Type*) [CommRing k] [MonoidWithZero K] [Monoid P]

def left₀ : K →*₀ Mon K P where
  toFun a := pair K P (a,1)
  map_one' := map_one (pair K P)
  map_mul' a b := by simpa using (pair K P).map_mul (a,1) (b,1)
  map_zero' := pair_zero K P 1

def rightBasis : P →* Contracted.Algebra k (Mon K P) where
  toFun p := basis k (Mon K P) (pair K P (1,p)) 1
  map_one' := by
    rw [show pair K P (1,1)=1 from map_one (pair K P)]
    exact basis_identity k (Mon K P)
  map_mul' a b := by
    rw [basis_mul,one_mul,←map_mul]
    simp only [Prod.mk_mul_mk,one_mul]

def leftAlgebra : Contracted.Algebra k K →ₐ[k] Contracted.Algebra k (Mon K P) := Contracted.map (left₀ K P)
def rightAlgebra : MonoidAlgebra k P →ₐ[k] Contracted.Algebra k (Mon K P) :=
  MonoidAlgebra.lift k _ P (rightBasis k K P)

@[simp] theorem leftAlgebra_basis (a : K) (r : k) :
    leftAlgebra k K P (basis k K a r)=basis k (Mon K P) (pair K P (a,1)) r :=
  Contracted.map_basis (left₀ K P) a r

@[simp] theorem rightAlgebra_single (p : P) (r : k) :
    rightAlgebra k K P (MonoidAlgebra.single p r)=basis k (Mon K P) (pair K P (1,p)) r := by
  rw [rightAlgebra,MonoidAlgebra.lift_single]
  change r • quotient k (Mon K P) (MonoidAlgebra.single (pair K P (1,p)) 1)=_
  rw [←map_smul]
  simp [basis]

theorem left_right_commute (x : Contracted.Algebra k K) (y : MonoidAlgebra k P) :
    Commute (leftAlgebra k K P x) (rightAlgebra k K P y) := by
  obtain ⟨f,rfl⟩ := (zeroIdeal k K).ringCon.mkₐ_surjective (α:=k) x
  change leftAlgebra k K P (quotient k K f)*rightAlgebra k K P y=
    rightAlgebra k K P y*leftAlgebra k K P (quotient k K f)
  induction f using MonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add,add_mul,mul_add,hf,hg]
  | single a r =>
    change leftAlgebra k K P (basis k K a r)*rightAlgebra k K P y=
      rightAlgebra k K P y*leftAlgebra k K P (basis k K a r)
    rw [leftAlgebra_basis]
    induction y using MonoidAlgebra.induction_linear with
    | zero => simp
    | add f g hf hg => simp only [map_add,add_mul,mul_add,hf,hg]
    | single p t =>
      simp only [rightAlgebra_single,basis_mul,←map_mul,Prod.mk_mul_mk,one_mul,mul_one]
      rw [mul_comm r t]

def tensorMap : Contracted.Algebra k K ⊗[k] MonoidAlgebra k P →ₐ[k] Contracted.Algebra k (Mon K P) :=
  Algebra.TensorProduct.lift (leftAlgebra k K P) (rightAlgebra k K P) (left_right_commute k K P)

@[simp] theorem tensorMap_basis (a : K) (p : P) (r t : k) :
    tensorMap k K P (basis k K a r ⊗ₜ[k] MonoidAlgebra.single p t)=
      basis k (Mon K P) (pair K P (a,p)) (r*t) := by
  rw [tensorMap,Algebra.TensorProduct.lift_tmul,leftAlgebra_basis,rightAlgebra_single,basis_mul,←map_mul]
  simp

end FiniteAlgebraicEnvelopes.ZeroProduct

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.BooneHigman_ActionEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Full finitely presented faithful two-transitive action envelope and type-(A) applications.
-/

section
namespace FiniteAlgebraicEnvelopes.Contracted
instance countableAlgebra (k H : Type*) [CommRing k] [MonoidWithZero H] [Countable k] [Countable H] :
    Countable (Algebra k H) := by
  let : Countable (MonoidAlgebra k H) := MonoidAlgebra.coeff_injective.countable
  exact (zeroIdeal k H).ringCon.mkₐ_surjective (α:=k) |>.countable
end FiniteAlgebraicEnvelopes.Contracted
end

namespace FiniteAlgebraicEnvelopes.AffinePermutation
variable {Q V : Type*} [Group Q] [Group V] (α : Q →* MulAut V)

instance action : MulAction (V ⋊[α] Q) V where
  smul a v := a.left * α a.right v
  one_smul v := by
    change (1 : V) * α (1 : Q) v = v
    simp
  mul_smul a b v := by
    change (a*b).left * α (a*b).right v = a.left * α a.right (b.left * α b.right v)
    simp [map_mul,mul_assoc]

@[simp] theorem smul_apply (a : V ⋊[α] Q) (v : V) : a • v=a.left*α a.right v := rfl

end FiniteAlgebraicEnvelopes.AffinePermutation

namespace FiniteAlgebraicEnvelopes

section
universe u
namespace LiftedAction
variable {Γ X : Type*} [Group Γ] [MulAction Γ X]

@[instance_reducible] def action : MulAction (ULift.{u} Γ) (ULift.{u} X) where
  smul g x := ⟨g.down • x.down⟩
  one_smul x := by cases x; exact congrArg ULift.up (one_smul Γ _)
  mul_smul g h x := by cases x; exact congrArg ULift.up (mul_smul g.down h.down _)

attribute [local instance] action

@[simp] lemma down_smul (g : ULift.{u} Γ) (x : ULift.{u} X) : (g • x).down=g.down • x.down := rfl

instance faithful [FaithfulSMul Γ X] : FaithfulSMul (ULift.{u} Γ) (ULift.{u} X) where
  eq_of_smul_eq_smul := by
    intro g h he
    apply ULift.ext
    apply eq_of_smul_eq_smul (α:=X)
    intro x
    exact congrArg ULift.down (he (ULift.up x))

end LiftedAction

open scoped commutatorElement

end

end FiniteAlgebraicEnvelopes

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_RegularCoverGeometry
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Function Topology
noncomputable section
open Set Function
open scoped unitInterval
open scoped unitInterval
open Set
namespace RegularCoverGeometry
open Set
variable {X E : Type*} [TopologicalSpace X] [TopologicalSpace E]
variable {p : E → X} (cov : IsCoveringMap p) (e₀ : E)

theorem pathConnected_of_monodromy_transitive [PathConnectedSpace X]
    (h : Function.Surjective (fun γ : FundamentalGroup X (p e₀) =>
      cov.monodromy γ ⟨e₀,rfl⟩)) : PathConnectedSpace E := by
  have hj : ∀ e : E, Joined e₀ e := by
    intro e
    let γ : Path.Homotopic.Quotient (p e) (p e₀) :=
      .mk (PathConnectedSpace.somePath (p e) (p e₀))
    let e' : p ⁻¹' {p e₀} := cov.monodromy γ ⟨e,rfl⟩
    have he : Joined e e'.1 := ⟨(cov.liftPathQuotient γ ⟨e,rfl⟩).out⟩
    obtain ⟨δ,hδ⟩ := h e'
    have h₀ : Joined e₀ (cov.monodromy δ ⟨e₀,rfl⟩).1 :=
      ⟨(cov.liftPathQuotient δ ⟨e₀,rfl⟩).out⟩
    have h₀' : Joined e₀ e'.1 := (congrArg Subtype.val hδ) ▸ h₀
    exact h₀'.trans he.symm
  exact ⟨⟨e₀⟩,fun a b => (hj a).symm.trans (hj b)⟩

theorem simplyConnected_of_monodromy_bijective [PathConnectedSpace X]
    (h : Function.Bijective (fun γ : FundamentalGroup X (p e₀) =>
      cov.monodromy γ ⟨e₀,rfl⟩)) : SimplyConnectedSpace E := by
  let : PathConnectedSpace E := pathConnected_of_monodromy_transitive cov e₀ h.2
  let : Subsingleton (FundamentalGroup E e₀) := ⟨by
    intro a b
    apply cov.injective_path_homotopic_map e₀ e₀
    apply h.1
    exact (cov.monodromy_map a).trans (cov.monodromy_map b).symm⟩
  apply simply_connected_iff_loops_nullhomotopic.mpr
  refine ⟨inferInstance,fun x γ => ?_⟩
  let e := FundamentalGroup.fundamentalGroupMulEquivOfPathConnected e₀ x
  have : Subsingleton (FundamentalGroup E x) := e.symm.injective.subsingleton
  exact Path.Homotopic.Quotient.eq.mp
    (Subsingleton.elim (α := FundamentalGroup E x) (Path.Homotopic.Quotient.mk γ)
      (Path.Homotopic.Quotient.mk (Path.refl x)))

end RegularCoverGeometry

namespace CoveringMapNatural
open Set
variable {X Y E F : Type} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace E] [TopologicalSpace F]
  {p : E → X} {q : F → Y} (cp : IsCoveringMap p) (cq : IsCoveringMap q)
  (f : C(X,Y)) (g : C(E,F)) (comm : q ∘ g = f ∘ p)

def fiberMap (x : X) : p ⁻¹' {x} → q ⁻¹' {f x} :=
  fun e => ⟨g e.1,(congrFun comm e.1).trans (congrArg f e.2)⟩

lemma natural {x y : X} (γ : Path.Homotopic.Quotient x y) (e : p ⁻¹' {x}) :
    cq.monodromy (γ.map f) (fiberMap f g comm x e) =
      fiberMap f g comm y (cp.monodromy γ e) := by
  apply cq.monodromy_eq_of_map_eq ((cp.liftPathQuotient γ e).map g)
  erw [← Path.Homotopic.Quotient.map_comp]
  have he : (⟨q,cq.continuous⟩ : C(F,Y)).comp g = f.comp ⟨p,cp.continuous⟩ :=
    ContinuousMap.ext (congrFun comm)
  apply eq_of_heq
  have hh : HEq ((cp.liftPathQuotient γ e).map ((⟨q,cq.continuous⟩ : C(F,Y)).comp g))
      ((cp.liftPathQuotient γ e).map (f.comp ⟨p,cp.continuous⟩)) := by rw [he]
  apply hh.trans
  erw [Path.Homotopic.Quotient.map_comp,cp.map_liftPathQuotient,
    Path.Homotopic.Quotient.map_cast]
  exact (Path.Homotopic.Quotient.cast_heq _ _).trans (Path.Homotopic.Quotient.cast_heq _ _).symm

lemma monodromy_point_bijective [SimplyConnectedSpace E] (e : E) :
    Function.Bijective (fun γ : FundamentalGroup X (p e) => cp.monodromy γ ⟨e,rfl⟩) := by
  constructor
  · intro γ δ h
    have hh : cp.liftPathQuotient γ ⟨e,rfl⟩ =
        (cp.liftPathQuotient δ ⟨e,rfl⟩).cast rfl (congrArg Subtype.val h) :=
      Subsingleton.elim _ _
    have hh' := congrArg (fun κ => κ.map (⟨p,cp.continuous⟩ : C(E,X))) hh
    erw [cp.map_liftPathQuotient,Path.Homotopic.Quotient.map_cast,
      cp.map_liftPathQuotient,Path.Homotopic.Quotient.cast_cast] at hh'
    exact eq_of_heq ((Path.Homotopic.Quotient.cast_heq _ _).symm.trans
      ((heq_of_eq hh').trans (Path.Homotopic.Quotient.cast_heq _ _)))
  · intro z
    let Γ : Path.Homotopic.Quotient e z.1 := .mk (PathConnectedSpace.somePath e z.1)
    refine ⟨(Γ.map ⟨p,cp.continuous⟩).cast rfl z.2.symm,?_⟩
    apply cp.monodromy_eq_of_map_eq Γ
    erw [Path.Homotopic.Quotient.cast_cast]
    exact eq_of_heq (Path.Homotopic.Quotient.cast_heq _ _).symm

include cp cq in

theorem simplyConnected_of_old [PathConnectedSpace Y] [SimplyConnectedSpace E]
    (e : E) (hs : Function.Surjective (FundamentalGroup.map f (p e)))
    (hb : Function.Bijective (fiberMap f g comm (p e))) : SimplyConnectedSpace F := by
  apply RegularCoverGeometry.simplyConnected_of_monodromy_bijective cq (g e)
  have hbase : q (g e) = f (p e) := congrFun comm e
  let e' : q ⁻¹' {f (p e)} := fiberMap f g comm (p e) ⟨e,rfl⟩
  have hn (γ : FundamentalGroup X (p e)) :
      cq.monodromy (FundamentalGroup.map f (p e) γ) e' =
        fiberMap f g comm (p e) (cp.monodromy γ ⟨e,rfl⟩) :=
    natural cp cq f g comm γ ⟨e,rfl⟩
  have hm : Function.Bijective (fun γ : FundamentalGroup Y (f (p e)) => cq.monodromy γ e') := by
    constructor
    · intro α β h
      obtain ⟨γ,rfl⟩ := hs α
      obtain ⟨δ,rfl⟩ := hs β
      dsimp only at h
      rw [hn,hn] at h
      exact congrArg (FundamentalGroup.map f (p e))
        ((monodromy_point_bijective cp e).1 (hb.1 h))
    · intro z
      obtain ⟨w,rfl⟩ := hb.2 z
      obtain ⟨γ,rfl⟩ := (monodromy_point_bijective cp e).2 w
      exact ⟨FundamentalGroup.map f (p e) γ,hn γ⟩
  have transport {y : Y} (z : q ⁻¹' {y})
      (hz : Function.Bijective (fun γ : FundamentalGroup Y y => cq.monodromy γ z)) :
      Function.Bijective (fun γ : FundamentalGroup Y (q z.1) => cq.monodromy γ ⟨z.1,rfl⟩) := by
    obtain ⟨z,hz'⟩ := z
    change q z = y at hz'
    subst y
    exact hz
  exact transport e' hm

end CoveringMapNatural

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SemilinearCoinvariants
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.CategoryTheory
open _root_.CategoryTheory MonoidalCategory _root_.Representation TensorProduct
open _root_.CategoryTheory CategoryTheory.Limits

namespace StandardTensor
section
open _root_.CategoryTheory MonoidalCategory _root_.Representation TensorProduct
variable {R G : Type} [CommRing R] [Group G] {A B : Rep R G}

def coefficientMap (α : A ⟶ B) :
    (Rep.standardComplex R G).coinvariantsTensorObj A ⟶
      (Rep.standardComplex R G).coinvariantsTensorObj B :=
  (NatTrans.mapHomologicalComplex ((Rep.coinvariantsTensor R G).map α) _).app _

@[simp] lemma coefficientMap_f_mk_tmul (α : A ⟶ B) (n : ℕ) (a : A)
    (z : MonoidAlgebra R (Fin (n+1) → G)) :
    (coefficientMap α).f n (Coinvariants.mk _ (a ⊗ₜ[R] z)) =
      Coinvariants.mk _ (α a ⊗ₜ[R] z) := rfl

lemma chain_ext {Q : ChainComplex (ModuleCat R) ℕ}
    {u v : (Rep.standardComplex R G).coinvariantsTensorObj A ⟶ Q}
    (h : ∀ (n : ℕ) (a : A) (s : Fin (n+1) → G),
      u.f n (Coinvariants.mk _ (a ⊗ₜ[R] MonoidAlgebra.single s 1)) =
      v.f n (Coinvariants.mk _ (a ⊗ₜ[R] MonoidAlgebra.single s 1))) : u=v := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply Coinvariants.hom_ext
  apply TensorProduct.ext
  apply LinearMap.ext
  intro a
  apply MonoidAlgebra.lhom_ext'
  intro s
  apply LinearMap.ext_ring
  exact h n a s

end

open _root_.CategoryTheory MonoidalCategory _root_.Representation TensorProduct

end StandardTensor

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_OrderBasedComplex
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory CategoryTheory.Limits _root_.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
namespace OrderBasedComplex

variable {B : Type*}

variable {M : Type*}
  [AddCommGroup M]
  (d : M →ₗ[ℤ] M)
  (aug : M →ₗ[ℤ] ℤ)

lemma map_mem_of_support {N : Type*} [AddCommGroup N]
    (f : (B →₀ ℤ) →ₗ[ℤ] N) (K : Submodule ℤ N) (c : B →₀ ℤ)
    (h : ∀ b ∈ c.support, f (Finsupp.single b 1) ∈ K) : f c ∈ K := by
  classical
  rw [← Finsupp.sum_single c, Finsupp.sum, map_sum]
  apply Submodule.sum_mem
  intro b hb
  have he : Finsupp.single b (c b) = (c b) • Finsupp.single b 1 := by simp
  rw [he, LinearMap.map_smul]
  exact K.smul_mem _ (h b hb)

end OrderBasedComplex

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_EquivariantOrderChains
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory CategoryTheory.Limits _root_.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
open _root_.CategoryTheory CategoryTheory.Limits
namespace EquivariantOrderChains
variable {G P : Type} [Group G] [Preorder P] [MulAction G P]
  [CovariantClass G P HSMul.hSMul LE.le]

def orderMap (g : G) : P →o P := ⟨(g • ·),fun _ _ h => smul_le_smul_left g h⟩

attribute [-instance] AddCommGroup.toIntModule
attribute [instance] AddCommGroup.toIntModule

variable (G) in
def permutationRepresentation (V : Type) [MulAction G V] : Representation ℤ G (V →₀ ℤ) where
  toFun g := Finsupp.lmapDomain ℤ ℤ (g • ·)
  map_one' := by apply Finsupp.lhom_ext; intro v r; simp
  map_mul' g h := by apply Finsupp.lhom_ext; intro v r; simp [mul_smul]

variable (G) in
def permutationObject (V : Type) [MulAction G V] : Rep ℤ G := Rep.of (permutationRepresentation G V)

end EquivariantOrderChains

open _root_.CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
namespace OrderBrown
attribute [-instance] AddCommGroup.toIntModule
open EquivariantOrderChains
end OrderBrown

end

end OAI
end


