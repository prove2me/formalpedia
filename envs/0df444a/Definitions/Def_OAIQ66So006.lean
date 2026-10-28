-- Prove2me | Definitions.Def_OAIQ66So006
-- name    : OAIQ66So006
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T02:11:26.323976+00:00
-- url     : https://prove2.me/theorems/0a26d88d-c60d-4d17-9f3a-0457b5b8e3af
-- title:
--   Definitions bundle OAIQ66So006 of the split of OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SimpleFInftyOvergroups.main`, carved from OpenAI's openai/math development (OpenAI, *Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)*, OpenAI Math Release, September 23, 2026, result family 250, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 238 declarations of OpenAI's Lean: 94 definitions, 2 inductive types or structures, 1 instance and 141 theorems. The definitions and types are `OAI.FiniteAlgebraicEnvelopes.PartialAffine.tail`, `OAI.FiniteAlgebraicEnvelopes.Steinberg.elementary`, `OAI.FiniteAlgebraicEnvelopes.WordProgramming.eval`, `OAI.FiniteExtension.N`, `OAI.FiniteExtension.Pre`, `OAI.FiniteExtension.Presented`, `OAI.FiniteExtension.Q`, `OAI.FiniteExtension.cocycle`, `OAI.FiniteExtension.conjRel`, `OAI.FiniteExtension.evaluate`, `OAI.FiniteExtension.evaluatePre`, `OAI.FiniteExtension.factor`, `OAI.FiniteExtension.inK`, `OAI.FiniteExtension.incl`, `OAI.FiniteExtension.letter`, `OAI.FiniteExtension.mulRel`, `OAI.FiniteExtension.pi`, `OAI.FiniteExtension.presentationEquiv`, `OAI.FiniteExtension.quot`, `OAI.FiniteExtension.rels`, `OAI.FiniteExtension.retract`, `OAI.FiniteExtension.sectionMap`, `OAI.FiniteExtension.t`, `OAI.FiniteExtension.twist`, `OAI.FiniteIdempotentDiagrams.OrthogonalAdditive`, `OAI.FiniteIdempotentDiagrams.OrthogonalAdditiveOn`, `OAI.FiniteIndexRegular.coords`, `OAI.FiniteIndexRegular.slice`, `OAI.FreeTensor.Chains`, `OAI.FreeTensor.lift`, `OAI.FreeTensor.map`, `OAI.FreeTensor.pure`, `OAI.FunctionalTree.path`, `OAI.HomStabilizer.conjugateTuple`, `OAI.HomStabilizer.enumeratedSubset`, `OAI.HomStabilizer.fixedTuple`, `OAI.HomStabilizer.preimageEquiv`, `OAI.InducedFree.backward`, `OAI.InducedFree.forward`, `OAI.InducedFree.iso` and 56 more.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory, in whole or in part: `BooneHigman_PartialAffine`, `BooneHigman_Steinberg`, `BooneHigman_WordProblem`, `FiniteCompiler_TapeFolding`, `FiniteType_AscendingHNNInnerTwist`, `FiniteType_BinaryPrefixOperators`, `FiniteType_ClassifyingSpaces`, `FiniteType_CoreDeck`, `FiniteType_CoreDeckLeftQuotientCovering`, `FiniteType_FiniteIdempotentDiagrams`, `FiniteType_FiniteIndexRegular`, `FiniteType_FreeTensor`, `FiniteType_FreeTensorPureMem`, `FiniteType_HomStabilizer`, `FiniteType_HurewiczInverse`, `FiniteType_InducedFree`, `FiniteType_ListChains`, `FiniteType_ListChainsHasPropagation`, `FiniteType_ListChainsMapChainComp`, `FiniteType_PosetTransport`, `FiniteType_PresentationGeometry`, `FiniteType_PresentationGeometryDescend`, `FiniteType_PresentationGeometryFiniteStage`, `FiniteType_PresentationVanKampen`, `FiniteType_PresentationVanKampenRectanglePaths`, `FiniteType_RepresentationKilling`, `FiniteType_SequentialColimit`, `FiniteType_SequentialColimitRangeInclMono`, `FiniteType_StandardShapiro`, `SimpleOvergroups_ThreeCodes`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ66So013`, `OAIQ66So014` and `OAIQ66So015`.
-- source:
--   OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 250; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/ComparatorChallenges/SimpleOvergroups.lean; Apache License 2.0); definitions carved from lean/OAI/GroupTheory at commit 1581d4c

import Mathlib

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

theorem invRev_primrec (n : ℕ) : Primrec (@FreeGroup.invRev (Fin n)) := by
  unfold FreeGroup.invRev
  apply Primrec.list_reverse.comp
  apply Primrec.list_map Primrec.id
  exact Primrec.pair (Primrec.fst.comp Primrec.snd)
    (Primrec.not.comp <| Primrec.snd.comp Primrec.snd)

end WordProblem

end FiniteAlgebraicEnvelopes

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

/-- Partial identities on rational tails, in the ambient partial-map monoid. -/
def tail (r : ℚ) : Function.End (Option ℚ) :=
  fun o => o.bind (fun x => if r≤x then some x else none)

 theorem tail_mul (r s : ℚ) : tail r*tail s=tail (max r s) := by
  funext o
  cases o with
  | none => rfl
  | some x =>
    change ((if s≤x then some x else none).bind
      (fun y => if r≤y then some y else none)) = if max r s≤x then some x else none
    by_cases hr : r ≤ x <;> by_cases hs : s ≤ x <;> simp [hr,hs]

 theorem tail_injective : Function.Injective tail := by
  intro r s h
  have hr := congrFun h (some r)
  have hs := congrFun h (some s)
  simp only [tail,Option.bind_some,le_refl,↓reduceIte] at hr hs
  have hsr : s ≤ r := by by_contra hn; simp [hn] at hr
  have hrs : r ≤ s := by by_contra hn; simp [hn] at hs
  exact le_antisymm hrs hsr

end FiniteAlgebraicEnvelopes.PartialAffine

end OAI
end

section
-- module Solutions.OAIQ066_SO.BooneHigman_Steinberg
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-!
Nonunital correction, Steinberg groups, corners, and kernel annihilation.
-/


namespace FiniteAlgebraicEnvelopes

universe u


/-! The correction for a nonunital coefficient map in the affine transition and product identities.
The proof works over a noncommutative ring. -/


/-! The Steinberg presentation in the Steinberg kernel argument.  No stability or centrality
 theorem is assumed.  Root indices are restricted to the off-diagonal. -/
namespace Steinberg
open scoped commutatorElement

variable {ι R S : Type*} [Ring R] [Ring S]

section MatrixRepresentation
variable [Fintype ι] [DecidableEq ι]

/-- Elementary matrices over an arbitrary, possibly noncommutative, ring. -/
def elementary (i j : ι) (h : i ≠ j) (a : R) : (Matrix ι ι R)ˣ where
  val := 1 + Matrix.single i j a
  inv := 1 - Matrix.single i j a
  val_inv := by
    have h0 : Matrix.single i j a * Matrix.single i j a = 0 :=
      Matrix.single_mul_single_of_ne a i j i h.symm a
    calc
      (1 + Matrix.single i j a) * (1 - Matrix.single i j a) =
          1 - Matrix.single i j a * Matrix.single i j a := by noncomm_ring
      _ = 1 := by rw [h0, sub_zero]
  inv_val := by
    have h0 : Matrix.single i j a * Matrix.single i j a = 0 :=
      Matrix.single_mul_single_of_ne a i j i h.symm a
    calc
      (1 - Matrix.single i j a) * (1 + Matrix.single i j a) =
          1 - Matrix.single i j a * Matrix.single i j a := by noncomm_ring
      _ = 1 := by rw [h0, sub_zero]

@[simp] theorem elementary_val (i j : ι) (h : i ≠ j) (a : R) :
    (elementary i j h a : Matrix ι ι R) = 1 + Matrix.single i j a := rfl

@[simp] theorem elementary_inv_val (i j : ι) (h : i ≠ j) (a : R) :
    ((elementary i j h a)⁻¹).val = 1 - Matrix.single i j a := rfl

end MatrixRepresentation


/-! Orthogonal equivalent corners, as specified by (corner-equivalence)
in the Steinberg kernel argument. The symbol `e` below is the specified d*, not an involution. -/

end Steinberg

end FiniteAlgebraicEnvelopes

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

namespace FiniteAlgebraicEnvelopes.WordProgramming
open Encodable
variable {S : Type} [Primcodable S]

/-- An acceptable word-program numbering obtained from the pinned universal
    partial-recursive evaluator. Invalid decoded results remain undefined. -/
def eval (c : Nat.Partrec.Code) (w : List S) : Part (List S) :=
  (c.eval (encode w)).bind (fun n => Part.ofOption (decode n))

theorem partrec_eval : Partrec₂ (eval (S := S)) :=
  ((Nat.Partrec.Code.eval_part.comp Computable.fst
    (Computable.encode.comp Computable.snd)).bind
      ((Computable.decode.comp Computable.snd).ofOption).to₂).to₂

/-- The source fixed-point equation for word algorithms, as literal equality of
    partial functions, including their domains. -/
theorem fixed_point {F : Nat.Partrec.Code → List S →. List S}
    (hF : Partrec₂ F) : ∃ c, eval c = F c := by
  let G : Nat.Partrec.Code → ℕ →. ℕ := fun c n =>
    (F c ((decode n).getD [])).map encode
  have hG : Partrec₂ G := by
    exact ((hF.comp Computable.fst
      ((Computable.option_getD (Computable.decode.comp Computable.snd)
        (Computable.const [])))).map (Computable.encode.comp Computable.snd).to₂).to₂
  obtain ⟨c,hc⟩ := Nat.Partrec.Code.fixed_point₂ hG
  refine ⟨c,?_⟩
  funext w
  simp only [eval,hc,G,encodek,Option.getD_some]
  apply Part.ext
  intro out
  simp [encodek]

end FiniteAlgebraicEnvelopes.WordProgramming

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_PresentationGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Function Topology

noncomputable section

namespace PresentationGeometry

namespace Cells

def boundaryVector (d : ℕ) : Fin d → ℝ := fun _ => -1

theorem boundaryVector_mem_sphere {d : ℕ} (hd : 0 < d) :
    boundaryVector d ∈ Metric.sphere (0 : Fin d → ℝ) 1 := by
  let : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  change ‖(fun _ : Fin d => (-1 : ℝ)) - 0‖ = 1
  simp

end Cells

end PresentationGeometry

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_PresentationVanKampen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Function Topology
noncomputable section
open Set Function
open scoped unitInterval
namespace PresentationVanKampen

def intervalPath (a b : I) : Path a b where
  toFun t := ⟨(1 - (t : ℝ)) * (a : ℝ) + (t : ℝ) * (b : ℝ),
    (convex_Icc (0 : ℝ) 1) a.property b.property
      (by linarith [t.property.2]) t.property.1 (by ring)⟩
  continuous_toFun := by fun_prop
  source' := by apply Subtype.ext; simp
  target' := by apply Subtype.ext; simp

@[simp] theorem intervalPath_self (a : I) : intervalPath a a = Path.refl a := by
  ext t
  change (1 - (t : ℝ)) * (a : ℝ) + (t : ℝ) * (a : ℝ) = (a : ℝ)
  ring

@[simp] theorem intervalPath_zero_one : intervalPath 0 1 = Path.id := by
  ext t
  simp [intervalPath]

theorem intervalPath_mem {a b : I} (hab : a ≤ b) (t : I) :
    intervalPath a b t ∈ Icc a b := by
  constructor
  · change (a : ℝ) ≤ (1 - (t : ℝ)) * (a : ℝ) + (t : ℝ) * (b : ℝ)
    have := mul_nonneg t.property.1 (sub_nonneg.mpr hab)
    nlinarith
  · change (1 - (t : ℝ)) * (a : ℝ) + (t : ℝ) * (b : ℝ) ≤ (b : ℝ)
    have := mul_nonneg (sub_nonneg.mpr t.property.2) (sub_nonneg.mpr hab)
    nlinarith

variable {X : Type*} [TopologicalSpace X] {x y : X}

def portion (p : Path x y) (a b : I) : Path (p a) (p b) :=
  (intervalPath a b).map p.continuous

@[simp] theorem portion_self (p : Path x y) (a : I) :
    portion p a a = Path.refl (p a) := by
  ext t
  simp [portion]

theorem portion_trans (p : Path x y) (a b c : I) :
    ((portion p a b).trans (portion p b c)).Homotopic (portion p a c) := by
  let : ContractibleSpace I := (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, by simp⟩
  have h := (SimplyConnectedSpace.paths_homotopic
    ((intervalPath a b).trans (intervalPath b c)) (intervalPath a c)).map p.toContinuousMap
  simpa only [portion, Path.map_trans] using h

theorem portion_mem {p : Path x y} {a b : I} (hab : a ≤ b)
    {s : Set X} (h : Icc a b ⊆ p ⁻¹' s) :
    Set.range (portion p a b) ⊆ s := by
  rintro _ ⟨t, rfl⟩
  exact h (intervalPath_mem hab t)

theorem path_induction_open_cover {ι : Type*} (U : ι → Set X)
    (hU : ∀ i, IsOpen (U i)) (hcover : univ ⊆ ⋃ i, U i)
    (P : ∀ {a b : X}, Path a b → Prop)
    (hrefl : ∀ a, P (Path.refl a))
    (htrans : ∀ {a b c} (p : Path a b) (q : Path b c), P p → P q → P (p.trans q))
    (hhom : ∀ {a b} (p q : Path a b), p.Homotopic q → P p → P q)
    (hlocal : ∀ {a b} (p : Path a b) i, Set.range p ⊆ U i → P p)
    (p : Path x y) : P p := by
  obtain ⟨t, ht0, hmono, ⟨n, hn⟩, hsub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval
      (fun i => (hU i).preimage p.continuous)
      (by intro a _; simpa only [mem_iUnion, mem_preimage] using hcover (mem_univ (p a)))
  have hall : ∀ j, P (portion p (t 0) (t j)) := by
    intro j
    induction j with
    | zero => simpa only [portion_self] using hrefl (p (t 0))
    | succ j ih =>
      obtain ⟨i, hi⟩ := hsub j
      exact hhom _ _ (portion_trans p _ _ _) (htrans _ _ ih
        (hlocal _ i (portion_mem (hmono (Nat.le_succ j)) hi)))
  have hh := hall n
  rw [ht0, hn n le_rfl] at hh
  have heq : (portion p 0 1).cast p.source.symm p.target.symm = p := by
    ext a
    change p (intervalPath 0 1 a) = p a
    rw [intervalPath_zero_one]
    rfl
  have hcast : ∀ {a b a' b' : X} (q : Path a b) (ha : a' = a) (hb : b' = b),
      P q → P (q.cast ha hb) := by
    intro a b a' b' q ha hb
    subst a'; subst b'
    exact id
  have hh' := hcast _ p.source.symm p.target.symm hh
  rwa [heq] at hh' 

def basedPathClass (b : X) (s : ∀ a : X, Path b a)
    {a c : X} (p : Path a c) : FundamentalGroup X b :=
  (Path.Homotopic.Quotient.mk (s a)).trans
    ((Path.Homotopic.Quotient.mk p).trans (Path.Homotopic.Quotient.mk (s c)).symm)

@[simp] theorem basedPathClass_refl (b : X) (s : ∀ a : X, Path b a) (a : X) :
    basedPathClass b s (Path.refl a) = 1 := by
  simp only [basedPathClass, Path.Homotopic.Quotient.mk_refl,
    Path.Homotopic.Quotient.refl_trans, Path.Homotopic.Quotient.trans_symm]
  rfl

theorem basedPathClass_trans (b : X) (s : ∀ a : X, Path b a)
    {a c d : X} (p : Path a c) (q : Path c d) :
    basedPathClass b s (p.trans q) = basedPathClass b s q * basedPathClass b s p := by
  simp only [basedPathClass, FundamentalGroup.mul_def, Path.Homotopic.Quotient.mk_trans]
  simp only [Path.Homotopic.Quotient.trans_assoc,
    ← Path.Homotopic.Quotient.trans_assoc (Path.Homotopic.Quotient.mk (s c)).symm,
    Path.Homotopic.Quotient.symm_trans, Path.Homotopic.Quotient.refl_trans]

theorem basedPathClass_homotopic (b : X) (s : ∀ a : X, Path b a)
    {a c : X} (p q : Path a c) (h : p.Homotopic q) :
    basedPathClass b s p = basedPathClass b s q := by
  have hh : Path.Homotopic.Quotient.mk p = Path.Homotopic.Quotient.mk q := Quotient.sound h
  simp only [basedPathClass, hh]

theorem basedPathClass_loop (b : X) (s : ∀ a : X, Path b a)
    (hs : (s b).Homotopic (Path.refl b)) (p : Path b b) :
    basedPathClass b s p = Path.Homotopic.Quotient.mk p := by
  have hh : Path.Homotopic.Quotient.mk (s b) = Path.Homotopic.Quotient.refl b :=
    Quotient.sound hs
  simp only [basedPathClass, hh, Path.Homotopic.Quotient.refl_trans]
  have hr : (Path.Homotopic.Quotient.refl b).symm = Path.Homotopic.Quotient.refl b := rfl
  rw [hr, Path.Homotopic.Quotient.trans_refl]

theorem subgroup_eq_top_of_open_cover {ι : Type*} (U : ι → Set X)
    (hU : ∀ i, IsOpen (U i)) (hcover : univ ⊆ ⋃ i, U i)
    (b : X) (s : ∀ a : X, Path b a) (hs : (s b).Homotopic (Path.refl b))
    (H : Subgroup (FundamentalGroup X b))
    (hlocal : ∀ {a c} (p : Path a c) i, Set.range p ⊆ U i → basedPathClass b s p ∈ H) :
    H = ⊤ := by
  apply top_unique
  intro g _
  obtain ⟨p, rfl⟩ := Path.Homotopic.Quotient.mk_surjective g
  rw [← basedPathClass_loop b s hs p]
  apply path_induction_open_cover U hU hcover (fun p => basedPathClass b s p ∈ H)
    (fun a => by rw [basedPathClass_refl]; exact H.one_mem)
  · intro a c d p q hp hq
    rw [basedPathClass_trans]
    exact H.mul_mem hq hp
  · intro a c p q hpq hp
    rwa [← basedPathClass_homotopic b s p q hpq]
  · exact hlocal

def pathIn {a c : X} (p : Path a c) {U : Set X} (h : Set.range p ⊆ U) :
    Path (⟨a, h p.source_mem_range⟩ : U) ⟨c, h p.target_mem_range⟩ where
  toFun t := ⟨p t, h ⟨t, rfl⟩⟩
  continuous_toFun := p.continuous.subtype_mk _
  source' := Subtype.ext p.source
  target' := Subtype.ext p.target

@[simp] theorem pathIn_map {a c : X} (p : Path a c) {U : Set X}
    (h : Set.range p ⊆ U) :
    (pathIn p h).map continuous_subtype_val = p := by ext t; rfl

theorem homotopic_in_simplyConnected {U : Set X} [SimplyConnectedSpace U]
    {a c : X} (p q : Path a c) (hp : Set.range p ⊆ U) (hq : Set.range q ⊆ U) :
    p.Homotopic q := by
  have h := (SimplyConnectedSpace.paths_homotopic (pathIn p hp) (pathIn q hq)).map
    (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X))
  simpa only [pathIn_map] using h

def Replaceable (U : Set X) (r : X → U) (spoke : ∀ a : X, Path (r a : X) a)
    {a c : X} (p : Path a c) : Prop :=
  ∃ q : Path (r a : X) (r c : X), Set.range q ⊆ U ∧
    ((spoke a).trans p).Homotopic (q.trans (spoke c))

theorem replaceable_refl (U : Set X) (r : X → U) (spoke : ∀ a : X, Path (r a : X) a)
    (a : X) : Replaceable U r spoke (Path.refl a) := by
  refine ⟨Path.refl (r a : X), ?_, ?_⟩
  · rintro _ ⟨t, rfl⟩; exact (r a).property
  · exact (Path.Homotopic.trans_refl _).trans (Path.Homotopic.refl_trans _).symm

theorem replaceable_trans (U : Set X) (r : X → U) (spoke : ∀ a : X, Path (r a : X) a)
    {a c d : X} {p : Path a c} {q : Path c d}
    (hp : Replaceable U r spoke p) (hq : Replaceable U r spoke q) :
    Replaceable U r spoke (p.trans q) := by
  obtain ⟨p', hp', hpp'⟩ := hp
  obtain ⟨q', hq', hqq'⟩ := hq
  refine ⟨p'.trans q', ?_, ?_⟩
  · simpa only [Path.trans_range] using union_subset hp' hq'
  · exact (Path.Homotopic.trans_assoc _ _ _).symm |>.trans
      (hpp'.hcomp (Path.Homotopic.refl q)) |>.trans
      (Path.Homotopic.trans_assoc _ _ _) |>.trans
      ((Path.Homotopic.refl p').hcomp hqq') |>.trans
      (Path.Homotopic.trans_assoc _ _ _).symm

theorem replaceable_homotopic (U : Set X) (r : X → U) (spoke : ∀ a : X, Path (r a : X) a)
    {a c : X} {p q : Path a c} (hpq : p.Homotopic q) (hp : Replaceable U r spoke p) :
    Replaceable U r spoke q := by
  obtain ⟨p', hp', hpp'⟩ := hp
  exact ⟨p', hp', ((Path.Homotopic.refl (spoke a)).hcomp hpq).symm.trans hpp'⟩

theorem replaceable_of_range_subset (U : Set X) (r : X → U)
    (spoke : ∀ a : X, Path (r a : X) a)
    {a c : X} (p : Path a c) (hp : Set.range p ⊆ U)
    (ha : Set.range (spoke a) ⊆ U) (hc : Set.range (spoke c) ⊆ U) :
    Replaceable U r spoke p := by
  refine ⟨((spoke a).trans p).trans (spoke c).symm, ?_, ?_⟩
  · simpa only [Path.trans_range, Path.symm_range] using union_subset (union_subset ha hp) hc
  · apply Path.Homotopic.symm
    exact (Path.Homotopic.trans_assoc _ _ _).trans
      ((Path.Homotopic.refl _).hcomp (Path.Homotopic.symm_trans _)) |>.trans
      (Path.Homotopic.trans_refl _)

theorem replaceable_of_simplyConnected (U V : Set X) [SimplyConnectedSpace V]
    (hUV : IsPathConnected (U ∩ V)) (r : X → U) (spoke : ∀ a : X, Path (r a : X) a)
    {a c : X} (p : Path a c) (hp : Set.range p ⊆ V)
    (ha : Set.range (spoke a) ⊆ V) (hc : Set.range (spoke c) ⊆ V) :
    Replaceable U r spoke p := by
  have hpath := hUV.joinedIn (r a : X) ⟨(r a).property, ha (spoke a).source_mem_range⟩
    (r c : X) ⟨(r c).property, hc (spoke c).source_mem_range⟩
  refine ⟨hpath.somePath, ?_, ?_⟩
  · rintro _ ⟨t, rfl⟩; exact (hpath.somePath_mem t).1
  · apply homotopic_in_simplyConnected (U := V)
    · simpa only [Path.trans_range] using union_subset ha hp
    · rw [Path.trans_range]
      refine union_subset ?_ hc
      rintro _ ⟨t, rfl⟩; exact (hpath.somePath_mem t).2

theorem replaceable_of_open_cover {ι : Type*} (O : ι → Set X)
    (hO : ∀ i, IsOpen (O i)) (hcover : univ ⊆ ⋃ i, O i)
    (U : Set X) (r : X → U) (spoke : ∀ a : X, Path (r a : X) a)
    (hlocal : ∀ {a c} (p : Path a c) i, Set.range p ⊆ O i → Replaceable U r spoke p)
    {a c : X} (p : Path a c) : Replaceable U r spoke p :=
  path_induction_open_cover O hO hcover (Replaceable U r spoke)
    (replaceable_refl U r spoke) (fun _ _ hp hq => replaceable_trans U r spoke hp hq)
    (fun _ _ hpq hp => replaceable_homotopic U r spoke hpq hp) hlocal p

theorem cancel_spoke {a c ra rc : X} (sa : Path ra a) (sc : Path rc c)
    (p : Path a c) (q : Path ra rc) (h : (sa.trans p).Homotopic (q.trans sc)) :
    p.Homotopic ((sa.symm.trans q).trans sc) := by
  exact (Path.Homotopic.refl_trans p).symm |>.trans
    (((Path.Homotopic.symm_trans sa).hcomp (Path.Homotopic.refl p)).symm) |>.trans
    (Path.Homotopic.trans_assoc _ _ _) |>.trans
    ((Path.Homotopic.refl sa.symm).hcomp h) |>.trans
    (Path.Homotopic.trans_assoc _ _ _).symm

theorem fundamentalGroupMap_surjective_of_open_cover
    {ι : Type*} (U : Set X) (V : ι → Set X)
    (hU : IsOpen U) (hV : ∀ i, IsOpen (V i))
    (hcover : U ∪ ⋃ i, V i = univ)
    (hUV : ∀ i, IsPathConnected (U ∩ V i))
    (hsc : ∀ i, SimplyConnectedSpace (V i))
    (r : X → U) (spoke : ∀ a : X, Path (r a : X) a)
    (hspU : ∀ a ∈ U, Set.range (spoke a) ⊆ U)
    (hspV : ∀ i a, a ∈ V i → Set.range (spoke a) ⊆ V i)
    (b : U) : Function.Surjective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)) b) := by
  let O : Option ι → Set X := fun i => i.elim U V
  have hO : ∀ i, IsOpen (O i) := by intro i; cases i <;> simp [O, hU, hV]
  have hcov : univ ⊆ ⋃ i, O i := by
    intro x _
    have hx : x ∈ U ∪ ⋃ i, V i := by rw [hcover]; trivial
    rcases hx with hx | hx
    · exact mem_iUnion.mpr ⟨none, hx⟩
    · rcases mem_iUnion.mp hx with ⟨i, hi⟩
      exact mem_iUnion.mpr ⟨some i, hi⟩
  have hp : ∀ {a c} (p : Path a c), Replaceable U r spoke p := by
    intro a c p
    apply replaceable_of_open_cover O hO hcov U r spoke _ p
    intro a c p i hi
    cases i with
    | none =>
      exact replaceable_of_range_subset U r spoke p hi
        (hspU a (hi p.source_mem_range)) (hspU c (hi p.target_mem_range))
    | some i =>
      let := hsc i
      exact replaceable_of_simplyConnected U (V i) (hUV i) r spoke p hi
        (hspV i a (hi p.source_mem_range)) (hspV i c (hi p.target_mem_range))
  intro g
  obtain ⟨p, rfl⟩ := Path.Homotopic.Quotient.mk_surjective g
  obtain ⟨q, hq, hh⟩ := hp p
  let p' := ((spoke (b : X)).symm.trans q).trans (spoke (b : X))
  have hp' : Set.range p' ⊆ U := by
    have hs := hspU b b.property
    simpa only [p', Path.trans_range, Path.symm_range] using
      union_subset (union_subset hs hq) hs
  refine ⟨Path.Homotopic.Quotient.mk (pathIn p' hp'), ?_⟩
  change Path.Homotopic.Quotient.mk ((pathIn p' hp').map continuous_subtype_val) =
    Path.Homotopic.Quotient.mk p
  rw [pathIn_map]
  exact Quotient.sound (cancel_spoke _ _ _ _ hh).symm

theorem exists_compatible_spokes {ι : Type*} (U : Set X) (V : ι → Set X)
    (hcover : U ∪ ⋃ i, V i = univ)
    (hdisj : Pairwise (Disjoint on V))
    (hUV : ∀ i, (U ∩ V i).Nonempty)
    (hpc : ∀ i, IsPathConnected (V i)) :
    ∃ (r : X → U) (spoke : ∀ a : X, Path (r a : X) a),
      (∀ a ∈ U, Set.range (spoke a) ⊆ U) ∧
      (∀ i a, a ∈ V i → Set.range (spoke a) ⊆ V i) := by
  classical
  have hpoint : ∀ a : X, ∃ u : U, ∃ p : Path (u : X) a,
      (a ∈ U → Set.range p ⊆ U) ∧
      (∀ i, a ∈ V i → Set.range p ⊆ V i) := by
    intro a
    by_cases ha : a ∈ U
    · refine ⟨⟨a, ha⟩, Path.refl a, ?_, ?_⟩
      · intro _ z hz; obtain ⟨t, rfl⟩ := hz; exact ha
      · intro i hi z hz; obtain ⟨t, rfl⟩ := hz; exact hi
    · have hac : a ∈ U ∪ ⋃ i, V i := by rw [hcover]; trivial
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hac.resolve_left ha)
      obtain ⟨u, huU, huV⟩ := hUV i
      let hpath := (hpc i).joinedIn u huV a hi
      refine ⟨⟨u, huU⟩, hpath.somePath, fun h => False.elim (ha h), ?_⟩
      intro j hj z hz
      have hij : i = j := by
        by_contra hij
        exact Set.disjoint_left.mp (hdisj hij) hi hj
      subst j
      obtain ⟨t, rfl⟩ := hz
      exact hpath.somePath_mem t
  choose r spoke hU hV using hpoint
  exact ⟨r, spoke, hU, fun i a => hV a i⟩

theorem fundamentalGroupMap_surjective_of_disjoint_open_cover
    {ι : Type*} (U : Set X) (V : ι → Set X)
    (hU : IsOpen U) (hV : ∀ i, IsOpen (V i))
    (hcover : U ∪ ⋃ i, V i = univ)
    (hdisj : Pairwise (Disjoint on V))
    (hUV : ∀ i, IsPathConnected (U ∩ V i))
    (hsc : ∀ i, SimplyConnectedSpace (V i)) (b : U) :
    Function.Surjective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)) b) := by
  obtain ⟨r, spoke, hsU, hsV⟩ := exists_compatible_spokes U V hcover hdisj
    (fun i => (hUV i).nonempty) (fun i => by
      let := hsc i
      exact isPathConnected_iff_pathConnectedSpace.mpr inferInstance)
  exact fundamentalGroupMap_surjective_of_open_cover U V hU hV hcover hUV hsc
    r spoke hsU hsV b

end PresentationVanKampen

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_PresentationGeometryDescend
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Function Topology
noncomputable section
open Set Function
open scoped unitInterval
namespace PresentationGeometry
namespace Cells

open Metric

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
variable {k d : ℕ}

theorem annulus_pathConnected (hd : 1 < d) :
    IsPathConnected {v : Fin d → ℝ | (1 / 2 : ℝ) < ‖v‖ ∧ ‖v‖ < 1} := by
  let A : Set (Fin d → ℝ) := {v | (1 / 2 : ℝ) < ‖v‖ ∧ ‖v‖ < 1}
  have hs : IsPathConnected (sphere (0 : Fin d → ℝ) 1) :=
    isPathConnected_sphere (by simpa using hd) 0 (by norm_num)
  have ht : IsPathConnected (Ioo (1 / 2 : ℝ) 1) :=
    (convex_Ioo (1 / 2 : ℝ) 1).isPathConnected ⟨3 / 4, by norm_num⟩
  have he : (fun p : (Fin d → ℝ) × ℝ => p.2 • p.1) ''
      (sphere (0 : Fin d → ℝ) 1 ×ˢ Ioo (1 / 2 : ℝ) 1) = A := by
    ext v
    constructor
    · rintro ⟨⟨u, t⟩, ⟨hu, ht⟩, rfl⟩
      have hu' : ‖u‖ = 1 := mem_sphere_zero_iff_norm.mp hu
      change (1 / 2 : ℝ) < ‖t • u‖ ∧ ‖t • u‖ < 1
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith [ht.1]), hu', mul_one]
      exact ht
    · intro hv
      have hv' : (1 / 2 : ℝ) < ‖v‖ ∧ ‖v‖ < 1 := hv
      have hn : ‖v‖ ≠ 0 := by linarith [hv'.1]
      refine ⟨(‖v‖⁻¹ • v, ‖v‖), ⟨?_, hv'⟩, ?_⟩
      · rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
      · change ‖v‖ • (‖v‖⁻¹ • v) = v
        rw [smul_smul, mul_inv_cancel₀ hn, one_smul]
  change IsPathConnected A
  rw [← he]
  exact (hs.prod ht).image (continuous_snd.smul continuous_fst)

end Cells
end PresentationGeometry

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_FiniteIdempotentDiagrams
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace FiniteIdempotentDiagrams
section

variable {R T : Type*} [NonUnitalRing R] [AddCommGroup T]

def OrthogonalAdditive (z : R → T) : Prop :=
  ∀ E P, E * E = E → P * P = P → E * P = 0 → P * E = 0 →
    z (E + P) = z E + z P

open Matrix
open scoped Matrix

end

section

open Matrix
open scoped Matrix

variable {K R T : Type*} [CommRing K] [Ring R] [AddCommGroup T]

def OrthogonalAdditiveOn (S : Set R) (z : R → T) : Prop :=
  ∀ E P, E ∈ S → P ∈ S → E + P ∈ S → E * P = 0 → P * E = 0 →
    z (E + P) = z E + z P

end

open Matrix
open scoped Matrix

end FiniteIdempotentDiagrams

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SequentialColimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SequentialColimit
section
open Set Topology
universe u v
variable (X : ℕ → Type u) [∀ n, TopologicalSpace (X n)]
  (f : ∀ i j, i ≤ j → C(X i,X j)) [DirectedSystem X (f · · ·)]

abbrev Space := DirectLimit X f

def incl (i : ℕ) : C(X i,Space X f) :=
  ⟨fun x => ⟦⟨i,x⟩⟧,continuous_quotient_mk'.comp continuous_sigmaMk⟩

@[simp] lemma incl_map (i j : ℕ) (h : i ≤ j) (x : X i) :
    incl X f j (f i j h x) = incl X f i x := DirectLimit.mk_apply (f:=f) _ _ _ _

lemma incl_injective (hf : ∀ i j h, Function.Injective (f i j h)) (i : ℕ) :
    Function.Injective (incl X f i) := DirectLimit.mk_injective f hf i

def lift {Y : Type v} [TopologicalSpace Y] (g : ∀ i, C(X i,Y))
    (hg : ∀ i j h x, g i x = g j (f i j h x)) : C(Space X f,Y) :=
  ⟨DirectLimit.lift f (fun i => g i) hg,by
    apply isQuotientMap_quotient_mk'.continuous_iff.mpr
    exact continuous_sigma (fun i => (g i).continuous)⟩

@[simp] lemma lift_incl {Y : Type v} [TopologicalSpace Y] (g : ∀ i, C(X i,Y))
    (hg : ∀ i j h x, g i x = g j (f i j h x)) (i : ℕ) (x : X i) :
    lift X f g hg (incl X f i x) = g i x := rfl

variable [∀ n, NormalSpace (X n)] (hc : ∀ i j h, IsClosedEmbedding (f i j h))

def extendOne (i : ℕ) (g : C(X i,ℝ)) : C(X (i+1),ℝ) :=
  (g.exists_extension_forall_mem_of_isClosedEmbedding (t:=univ)
    (fun _ => mem_univ _) (by simp) (hc i (i+1) (by omega))).choose

lemma extendOne_eq (X : ℕ → Type u) [∀ n, TopologicalSpace (X n)]
    (f : ∀ i j, i ≤ j → C(X i,X j)) [DirectedSystem X (f · · ·)]
    [∀ n, NormalSpace (X n)] (hc : ∀ i j h, IsClosedEmbedding (f i j h))
    (i : ℕ) (g : C(X i,ℝ)) (x : X i) :
    extendOne X f hc i g (f i (i+1) (by omega) x) = g x :=
  congrFun (g.exists_extension_forall_mem_of_isClosedEmbedding (t:=univ)
    (fun _ => mem_univ _) (by simp) (hc i (i+1) (by omega))).choose_spec.2 x

def extendTail (n : ℕ) (g : C(X n,ℝ)) : ∀ k, C(X (n+k),ℝ)
  | 0 => g
  | k+1 => extendOne X f hc (n+k) (extendTail n g k)

lemma extendTail_compat (n : ℕ) (g : C(X n,ℝ)) {i j : ℕ} (h : i ≤ j) (x : X (n+i)) :
    extendTail X f hc n g j (f (n+i) (n+j) (by omega) x) = extendTail X f hc n g i x := by
  induction j,h using Nat.le_induction with
  | base => rw [DirectedSystem.map_self']
  | succ j hj ih =>
    rw [show f (n+i) (n+(j+1)) (by omega) x =
      f (n+j) (n+j+1) (by omega) (f (n+i) (n+j) (by omega) x) from
        (DirectedSystem.map_map' f _ _ x).symm]
    exact (extendOne_eq X f hc _ _ _).trans ih

def extendFamily (n : ℕ) (g : C(X n,ℝ)) (i : ℕ) : C(X i,ℝ) :=
  (extendTail X f hc n g i).comp (f i (n+i) (by omega))

lemma extendFamily_compat (n : ℕ) (g : C(X n,ℝ)) (i j : ℕ) (h : i ≤ j) (x : X i) :
    extendFamily X f hc n g i x = extendFamily X f hc n g j (f i j h x) := by
  change extendTail X f hc n g i (f _ _ _ x) =
    extendTail X f hc n g j (f _ _ _ (f _ _ _ x))
  rw [DirectedSystem.map_map']
  rw [← extendTail_compat X f hc n g h (f i (n+i) (by omega) x),DirectedSystem.map_map']

def extend (n : ℕ) (g : C(X n,ℝ)) : C(Space X f,ℝ) :=
  lift X f (extendFamily X f hc n g) (extendFamily_compat X f hc n g)

lemma extend_eq (n : ℕ) (g : C(X n,ℝ)) (x : X n) :
    extend X f hc n g (incl X f n x) = g x := by
  change extendTail X f hc n g n (f n (n+n) (by omega) x) = g x
  exact extendTail_compat X f hc n g (i:=0) (by omega) x

variable [∀ n, T2Space (X n)]

include hc in

theorem hausdorff : T2Space (Space X f) := by
  constructor
  intro x y hxy
  obtain ⟨n,a,b,rfl,rfl⟩ := DirectLimit.exists_eq_mk₂ f x y
  have hab : a ≠ b := by intro he; subst b; exact hxy rfl
  obtain ⟨g,hga,hgb,-⟩ := exists_continuous_zero_one_of_isClosed
    (s:={a}) (t:={b}) isClosed_singleton isClosed_singleton (by simpa using hab)
  apply separated_by_continuous (extend X f hc n g).continuous
  change extend X f hc n g (incl X f n a) ≠ extend X f hc n g (incl X f n b)
  rw [extend_eq,extend_eq,hga (by simp),hgb (by simp)]
  norm_num

include hc in
lemma incl_isClosedEmbedding [∀ n, CompactSpace (X n)] (i : ℕ) :
    IsClosedEmbedding (incl X f i) := by
  let := hausdorff X f hc
  exact (incl X f i).continuous.isClosedEmbedding (incl_injective X f (fun i j h => (hc i j h).injective) i)

end

open Set Topology
universe u v
variable (X : ℕ → Type u) [∀ n, TopologicalSpace (X n)]
  (f : ∀ i j, i ≤ j → C(X i,X j)) [DirectedSystem X (f · · ·)]

lemma isOpen_iff_stages (U : Set (Space X f)) :
    IsOpen U ↔ ∀ i, IsOpen (incl X f i ⁻¹' U) := by
  rw [← isQuotientMap_quotient_mk'.isCoinducing.isOpen_preimage,isOpen_sigma_iff]
  rfl

lemma continuousOn_of_stages {Y : Type v} [TopologicalSpace Y]
    (g : Space X f → Y) (U : Set (Space X f)) (hU : IsOpen U)
    (hg : ∀ i, ContinuousOn (g ∘ incl X f i) (incl X f i ⁻¹' U)) : ContinuousOn g U := by
  apply (continuousOn_open_iff hU).mpr
  intro V hV
  apply (isOpen_iff_stages X f _).mpr
  intro i
  exact (hg i).isOpen_inter_preimage (hU.preimage (incl X f i).continuous) hV

end SequentialColimit

namespace SequentialCore
open Set Topology
universe u v w
variable (X : ℕ → Type u) [∀ n, TopologicalSpace (X n)]
  (f : ∀ i j, i ≤ j → C(X i,X j)) [DirectedSystem X (f · · ·)]
  {ι : Type v} {Q : Type w} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
  (U : ι → ∀ n, Set (X n)) (pot : ι → ∀ n, X n → Q)
  (hU : ∀ a i j (h : i ≤ j) x, x ∈ U a i ↔ f i j h x ∈ U a j)
  (hpot : ∀ a i j (h : i ≤ j) x, pot a j (f i j h x) = pot a i x)

def baseSet (a : ι) : Set (SequentialColimit.Space X f) :=
  fun x => DirectLimit.lift f (fun i x => x ∈ U a i)
    (fun i j h x => propext (hU a i j h x)) x

def potential (a : ι) : SequentialColimit.Space X f → Q :=
  DirectLimit.lift f (pot a) (fun i j h x => (hpot a i j h x).symm)

@[simp] lemma mem_baseSet_incl (a : ι) (n : ℕ) (x : X n) :
    SequentialColimit.incl X f n x ∈ baseSet X f U hU a ↔ x ∈ U a n := Iff.rfl

@[simp] lemma potential_incl (X : ℕ → Type u) [∀ n, TopologicalSpace (X n)]
    (f : ∀ i j, i ≤ j → C(X i,X j)) [DirectedSystem X (f · · ·)]
    {ι : Type v} {Q : Type w} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    (pot : ι → ∀ n, X n → Q)
    (hpot : ∀ a i j (h : i ≤ j) x, pot a j (f i j h x) = pot a i x)
    (a : ι) (n : ℕ) (x : X n) :
    potential X f pot hpot a (SequentialColimit.incl X f n x) = pot a n x := rfl

include hU in
lemma baseSet_open (hop : ∀ a n, IsOpen (U a n)) (a : ι) :
    IsOpen (baseSet X f U hU a) :=
  (SequentialColimit.isOpen_iff_stages X f _).mpr (hop a)

include hU in
lemma baseSet_cover (hcov : ∀ n (x : X n), ∃ a, x ∈ U a n)
    (x : SequentialColimit.Space X f) : ∃ a, x ∈ baseSet X f U hU a := by
  obtain ⟨n,x,rfl⟩ := DirectLimit.exists_eq_mk f x
  exact hcov n x

variable (hop : ∀ a n, IsOpen (U a n))
  (hcov : ∀ n (x : X n), ∃ a, x ∈ U a n)
  (hcont : ∀ a b n, ContinuousOn (fun x => pot b n x * (pot a n x)⁻¹) (U a n ∩ U b n))

include hop hcont in
lemma continuousOn_transition (a b : ι) :
    ContinuousOn (fun z : SequentialColimit.Space X f × Q =>
      potential X f pot hpot b z.1 * (potential X f pot hpot a z.1)⁻¹ * z.2)
      ((baseSet X f U hU a ∩ baseSet X f U hU b) ×ˢ univ) := by
  have hc : ContinuousOn (fun x => potential X f pot hpot b x * (potential X f pot hpot a x)⁻¹)
      (baseSet X f U hU a ∩ baseSet X f U hU b) := by
    apply SequentialColimit.continuousOn_of_stages X f
    · exact (baseSet_open X f U hU hop a).inter (baseSet_open X f U hU hop b)
    · exact fun n => hcont a b n
  exact (hc.comp continuous_fst.continuousOn (fun _ hz => hz.1)).mul continuous_snd.continuousOn

noncomputable def core : FiberBundleCore ι (SequentialColimit.Space X f) Q where
  baseSet := baseSet X f U hU
  isOpen_baseSet := baseSet_open X f U hU hop
  indexAt x := (baseSet_cover X f U hU hcov x).choose
  mem_baseSet_at x := (baseSet_cover X f U hU hcov x).choose_spec
  coordChange a b x q := potential X f pot hpot b x * (potential X f pot hpot a x)⁻¹ * q
  coordChange_self := by intros; simp
  continuousOn_coordChange := continuousOn_transition X f U pot hU hpot hop hcont
  coordChange_comp := by intros; group

end SequentialCore

namespace SequentialCoreTower
section
open Set Topology
universe u v w
variable (X : ℕ → Type u) [∀ n, TopologicalSpace (X n)]
  (f : ∀ i j, i ≤ j → C(X i,X j)) [DirectedSystem X (f · · ·)]
  (I : ℕ → Type v) (δ : ∀ i j, i ≤ j → I i ↪ I j)
  [DirectedSystem I (δ · · ·)]
  {Q : Type w} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
  (Z : ∀ n, FiberBundleCore (I n) (X n) Q)
  (pot : ∀ n, I n → X n → Q)
  (hBase : ∀ i j (h : i ≤ j) a x,
    x ∈ (Z i).baseSet a ↔ f i j h x ∈ (Z j).baseSet (δ i j h a))
  (hPot : ∀ i j (h : i ≤ j) a x,
    pot j (δ i j h a) (f i j h x) = pot i a x)
  (hCoord : ∀ n a b x q, (Z n).coordChange a b x q = pot n b x * (pot n a x)⁻¹ * q)

abbrev Index := Σ i, I i

def stageSet (a : Index I) (n : ℕ) : Set (X n) :=
  (f n (max a.1 n) (le_max_right _ _)) ⁻¹'
    (Z (max a.1 n)).baseSet (δ a.1 (max a.1 n) (le_max_left _ _) a.2)

def stagePot (a : Index I) (n : ℕ) (x : X n) : Q :=
  pot (max a.1 n) (δ a.1 (max a.1 n) (le_max_left _ _) a.2)
    (f n (max a.1 n) (le_max_right _ _) x)

lemma stageSet_common (X : ℕ → Type u) [∀ n, TopologicalSpace (X n)]
    (f : ∀ i j, i ≤ j → C(X i,X j)) [DirectedSystem X (f · · ·)]
    (I : ℕ → Type v) (δ : ∀ i j, i ≤ j → I i ↪ I j)
    [DirectedSystem I (δ · · ·)]
    {Q : Type w} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    (Z : ∀ n, FiberBundleCore (I n) (X n) Q)
    (hBase : ∀ i j (h : i ≤ j) a x,
      x ∈ (Z i).baseSet a ↔ f i j h x ∈ (Z j).baseSet (δ i j h a))
    (a : Index I) (n k : ℕ) (hi : a.1 ≤ k) (hn : n ≤ k) (x : X n) :
    x ∈ stageSet X f I δ Z a n ↔
      f n k hn x ∈ (Z k).baseSet (δ a.1 k hi a.2) := by
  change f n (max a.1 n) _ x ∈ (Z (max a.1 n)).baseSet _ ↔ _
  rw [hBase (max a.1 n) k (max_le hi hn),DirectedSystem.map_map',DirectedSystem.map_map']

lemma stagePot_common (X : ℕ → Type u) [∀ n, TopologicalSpace (X n)]
    (f : ∀ i j, i ≤ j → C(X i,X j)) [DirectedSystem X (f · · ·)]
    (I : ℕ → Type v) (δ : ∀ i j, i ≤ j → I i ↪ I j)
    [DirectedSystem I (δ · · ·)]
    {Q : Type w} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    (pot : ∀ n, I n → X n → Q)
    (hPot : ∀ i j (h : i ≤ j) a x,
      pot j (δ i j h a) (f i j h x) = pot i a x)
    (a : Index I) (n k : ℕ) (hi : a.1 ≤ k) (hn : n ≤ k) (x : X n) :
    stagePot X f I δ pot a n x = pot k (δ a.1 k hi a.2) (f n k hn x) := by
  unfold stagePot
  rw [← hPot (max a.1 n) k (max_le hi hn),DirectedSystem.map_map',DirectedSystem.map_map']

include hBase in
lemma stageSet_compat (a : Index I) (i j : ℕ) (h : i ≤ j) (x : X i) :
    x ∈ stageSet X f I δ Z a i ↔ f i j h x ∈ stageSet X f I δ Z a j := by
  rw [stageSet_common X f I δ Z hBase a i (max a.1 j) (le_max_left _ _) (by omega)]
  change _ ↔ f j (max a.1 j) _ (f i j h x) ∈
    (Z (max a.1 j)).baseSet (δ a.1 (max a.1 j) (le_max_left _ _) a.2)
  rw [DirectedSystem.map_map']

include hPot in
lemma stagePot_compat (a : Index I) (i j : ℕ) (h : i ≤ j) (x : X i) :
    stagePot X f I δ pot a j (f i j h x) = stagePot X f I δ pot a i x := by
  rw [stagePot_common X f I δ pot hPot a i (max a.1 j) (le_max_left _ _) (by omega)]
  unfold stagePot
  rw [DirectedSystem.map_map']

lemma stageSet_open (X : ℕ → Type u) [∀ n, TopologicalSpace (X n)]
    (f : ∀ i j, i ≤ j → C(X i,X j)) [DirectedSystem X (f · · ·)]
    (I : ℕ → Type v) (δ : ∀ i j, i ≤ j → I i ↪ I j)
    [DirectedSystem I (δ · · ·)]
    {Q : Type w} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    (Z : ∀ n, FiberBundleCore (I n) (X n) Q)
    (a : Index I) (n : ℕ) : IsOpen (stageSet X f I δ Z a n) :=
  ((Z _).isOpen_baseSet _).preimage (f _ _ _).continuous

include hBase in
lemma stageSet_cover (n : ℕ) (x : X n) : ∃ a, x ∈ stageSet X f I δ Z a n := by
  refine ⟨⟨n,(Z n).indexAt x⟩,?_⟩
  apply (stageSet_common X f I δ Z hBase _ n n (le_refl _) (le_refl _) x).mpr
  simpa only [DirectedSystem.map_self'] using (Z n).mem_baseSet_at x

include hBase hPot hCoord in
lemma transition_cont (a b : Index I) (n : ℕ) :
    ContinuousOn (fun x => stagePot X f I δ pot b n x *
      (stagePot X f I δ pot a n x)⁻¹)
      (stageSet X f I δ Z a n ∩ stageSet X f I δ Z b n) := by
  let k := max (max a.1 b.1) n
  have ha : a.1 ≤ k := by dsimp [k]; omega
  have hb : b.1 ≤ k := by dsimp [k]; omega
  have hn : n ≤ k := le_max_right _ _
  have hc := ((Z k).continuousOn_coordChange (δ _ _ ha a.2) (δ _ _ hb b.2)).comp
    ((f n k hn).continuous.prodMk continuous_const).continuousOn
    (s := stageSet X f I δ Z a n ∩ stageSet X f I δ Z b n) (t :=
      ((Z k).baseSet (δ _ _ ha a.2) ∩ (Z k).baseSet (δ _ _ hb b.2)) ×ˢ univ)
    (fun x hx => ⟨⟨(stageSet_common X f I δ Z hBase a n k ha hn x).mp hx.1,
      (stageSet_common X f I δ Z hBase b n k hb hn x).mp hx.2⟩,mem_univ (1:Q)⟩)
  apply hc.congr
  intro x hx
  dsimp [Function.comp_def]
  rw [hCoord,mul_one,stagePot_common X f I δ pot hPot a n k ha hn x,
    stagePot_common X f I δ pot hPot b n k hb hn x]

noncomputable def core : FiberBundleCore (Index I) (SequentialColimit.Space X f) Q :=
  SequentialCore.core X f (stageSet X f I δ Z) (stagePot X f I δ pot)
    (stageSet_compat X f I δ Z hBase) (stagePot_compat X f I δ pot hPot)
    (stageSet_open X f I δ Z) (stageSet_cover X f I δ Z hBase)
    (transition_cont X f I δ Z pot hBase hPot hCoord)

end

open Set Topology
variable (X : ℕ → Type) [∀ n, TopologicalSpace (X n)]
  (f : ∀ i j, i ≤ j → C(X i,X j)) [DirectedSystem X (f · · ·)]
  (I : ℕ → Type) (δ : ∀ i j, i ≤ j → I i ↪ I j)
  [DirectedSystem I (δ · · ·)]
  {Q : Type} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
  (Z : ∀ n, FiberBundleCore (I n) (X n) Q)
  (pot : ∀ n, I n → X n → Q)
  (hBase : ∀ i j (h : i ≤ j) a x,
    x ∈ (Z i).baseSet a ↔ f i j h x ∈ (Z j).baseSet (δ i j h a))
  (hPot : ∀ i j (h : i ≤ j) a x,
    pot j (δ i j h a) (f i j h x) = pot i a x)
  (hCoord : ∀ n a b x q, (Z n).coordChange a b x q = pot n b x * (pot n a x)⁻¹ * q)

lemma baseSet_incl (n : ℕ) (a : I n) (x : X n) :
    SequentialColimit.incl X f n x ∈ (core X f I δ Z pot hBase hPot hCoord).baseSet ⟨n,a⟩ ↔
      x ∈ (Z n).baseSet a := by
  change x ∈ stageSet X f I δ Z ⟨n,a⟩ n ↔ _
  rw [stageSet_common X f I δ Z hBase ⟨n,a⟩ n n (le_refl _) (le_refl _)]
  simp only [DirectedSystem.map_self']

lemma coordChange_incl (n : ℕ) (a b : I n) (x : X n) (q : Q) :
    (core X f I δ Z pot hBase hPot hCoord).coordChange ⟨n,a⟩ ⟨n,b⟩
      (SequentialColimit.incl X f n x) q = (Z n).coordChange a b x q := by
  change stagePot X f I δ pot ⟨n,b⟩ n x * (stagePot X f I δ pot ⟨n,a⟩ n x)⁻¹ * q = _
  rw [stagePot_common X f I δ pot hPot ⟨n,a⟩ n n (le_refl _) (le_refl _),
    stagePot_common X f I δ pot hPot ⟨n,b⟩ n n (le_refl _) (le_refl _)]
  simp only [DirectedSystem.map_self',hCoord]

end SequentialCoreTower

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SequentialColimitRangeInclMono
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SequentialCW
open Set Topology Metric
universe u
variable (X : ℕ → Type u) [∀ i, TopologicalSpace (X i)] [∀ i, T2Space (X i)]
  [∀ i, CompactSpace (X i)] [∀ i, Nonempty (X i)]
  [∀ i, CWComplex (univ : Set (X i))]
  (f : ∀ i j, i ≤ j → C(X i,X j)) [DirectedSystem X (f · · ·)]
  (hf : ∀ i j h, IsClosedEmbedding (f i j h))
abbrev Cell (i n : ℕ) := RelCWComplex.cell (univ : Set (X i)) n
variable (δ : ∀ i j, i ≤ j → ∀ n, Cell X i n ↪ Cell X j n)
  [∀ n, DirectedSystem (fun i => Cell X i n) (fun i j h => δ i j h n)]
  (hδ : ∀ i j h n (c : Cell X i n) v, v ∈ closedBall (0 : Fin n → ℝ) 1 →
    f i j h (RelCWComplex.map n c v) = RelCWComplex.map n (δ i j h n c) v)

abbrev FinalCell (n : ℕ) := DirectLimit (fun i => Cell X i n) (fun i j h => δ i j h n)
def cellMk (i n : ℕ) (c : Cell X i n) : FinalCell X δ n := ⟦⟨i,c⟩⟧
def repr (n : ℕ) (c : FinalCell X δ n) : Σ i, Cell X i n :=
  ⟨(DirectLimit.exists_eq_mk _ c).choose,(DirectLimit.exists_eq_mk _ c).choose_spec.choose⟩
lemma repr_eq (X : ℕ → Type u) [∀ i, TopologicalSpace (X i)] [∀ i, T2Space (X i)]
    [∀ i, CompactSpace (X i)] [∀ i, Nonempty (X i)]
    [∀ i, CWComplex (univ : Set (X i))]
    (δ : ∀ i j, i ≤ j → ∀ n, Cell X i n ↪ Cell X j n)
    [∀ n, DirectedSystem (fun i => Cell X i n) (fun i j h => δ i j h n)]
    (n : ℕ) (c : FinalCell X δ n) :
    cellMk X δ (repr X δ n c).1 n (repr X δ n c).2 = c :=
  (DirectLimit.exists_eq_mk _ c).choose_spec.choose_spec.symm

end SequentialCW

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_HurewiczInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Topology Metric
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open _root_.CategoryTheory AlgebraicTopology Limits
open Set Topology
open scoped unitInterval
open Set Topology
open scoped unitInterval

namespace HurewiczConstruction

open CategoryTheory.Limits
variable {X : Type} [TopologicalSpace X]

lemma homotopy_zero [PathConnectedSpace X] (x : X) :
    Subsingleton (HomotopyGroup (Fin 0) X x) :=
  HomotopyGroup.pi0EquivZerothHomotopy.injective.subsingleton

lemma homotopy_one [SimplyConnectedSpace X] (x : X) :
    Subsingleton (HomotopyGroup (Fin 1) X x) :=
  HomotopyGroup.pi1EquivFundamentalGroup.injective.subsingleton

end HurewiczConstruction

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_RepresentationKilling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace RepresentationKilling
attribute [-instance] AddCommGroup.toIntModule
variable {G M N : Type} [Group G] [AddCommGroup M] [Module ℤ M]
  [AddCommGroup N] [Module ℤ N] (ρ : Representation ℤ G M)
  (φ : M →ₗ[ℤ] N)

def stableKernel : Submodule (MonoidAlgebra ℤ G) ρ.asModule where
  carrier := {x | ∀ g : G, φ (ρ g (ρ.asModuleEquiv x)) = 0}
  zero_mem' := by intro g; simp
  add_mem' := by intro x y hx hy g; simp only [map_add,hx g,hy g,add_zero]
  smul_mem' := by
    intro r x hx g
    induction r using MonoidAlgebra.induction_linear with
    | zero => simp
    | add r s hr hs => simp only [add_smul,map_add,hr,hs,add_zero]
    | single h a =>
      rw [Representation.asModuleEquiv_map_smul,Representation.asAlgebraHom_single]
      simp only [LinearMap.smul_apply]
      rw [(ρ g).map_smul, φ.map_smul]
      have hh := hx (g*h)
      rw [map_mul] at hh
      change φ (ρ g (ρ h (ρ.asModuleEquiv x))) = 0 at hh
      rw [hh,smul_zero]

theorem eq_zero {ι : Type} (z : ι → ρ.asModule)
    (hz : Submodule.span (MonoidAlgebra ℤ G) (Set.range z) = ⊤)
    (hk : ∀ g i, φ (ρ g (ρ.asModuleEquiv (z i))) = 0) : φ = 0 := by
  have hle : Submodule.span (MonoidAlgebra ℤ G) (Set.range z) ≤ stableKernel ρ φ := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact fun g => hk g i
  rw [hz] at hle
  ext x
  have h := hle (Submodule.mem_top (x:=ρ.asModuleEquiv.symm x)) (1 : G)
  simpa using h
attribute [instance] AddCommGroup.toIntModule
end RepresentationKilling

namespace CWCellular
section
open Set Topology _root_.CategoryTheory HomologicalComplex
attribute [-instance] AddCommGroup.toIntModule

attribute [instance] AddCommGroup.toIntModule
end

section
open Set Topology _root_.CategoryTheory HomologicalComplex
attribute [-instance] AddCommGroup.toIntModule

attribute [instance] AddCommGroup.toIntModule
end

open Set Topology _root_.CategoryTheory HomologicalComplex
end CWCellular

attribute [-instance] AddCommGroup.toIntModule

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_CoreDeck
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoreDeck
attribute [-instance] AddCommGroup.toIntModule
open Set Topology _root_.CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [instance] AddCommGroup.toIntModule
end CoreDeck

namespace PresentationVanKampen
open scoped unitInterval

variable {X : Type*} [TopologicalSpace X]

theorem rectangle_homotopic (H : C(I × I, X)) :
    (((Path.id.map (continuous_const.prodMk continuous_id)).map H.continuous).trans
      ((Path.id.map (continuous_id.prodMk continuous_const)).map H.continuous) :
      Path (H (0,0)) (H (1,1))).Homotopic
    (((Path.id.map (continuous_id.prodMk continuous_const)).map H.continuous).trans
      ((Path.id.map (continuous_const.prodMk continuous_id)).map H.continuous) :
      Path (H (0,0)) (H (1,1))) := by
  let : ContractibleSpace I := (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, by simp⟩
  have h := SimplyConnectedSpace.paths_homotopic
    ((Path.id.map (continuous_const.prodMk continuous_id) : Path ((0 : I), (0 : I)) (0,1)).trans
      (Path.id.map (continuous_id.prodMk continuous_const) : Path ((0 : I), (1 : I)) (1,1)))
    ((Path.id.map (continuous_id.prodMk continuous_const) : Path ((0 : I), (0 : I)) (1,0)).trans
      (Path.id.map (continuous_const.prodMk continuous_id) : Path ((1 : I), (0 : I)) (1,1)))
  simpa only [Path.map_trans] using h.map H

end PresentationVanKampen

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_PresentationVanKampenRectanglePaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PresentationVanKampen
open scoped unitInterval
variable {X : Type*} [TopologicalSpace X]

theorem rectangle_paths {a b c d : X} (p : Path a b) (q : Path b d)
    (r : Path a c) (s : Path c d) (H : C(I × I, X))
    (hp : ∀ t, H (0,t) = p t) (hq : ∀ t, H (t,1) = q t)
    (hr : ∀ t, H (t,0) = r t) (hs : ∀ t, H (1,t) = s t) :
    (p.trans q).Homotopic (r.trans s) := by
  let pH : Path (H (0,0)) (H (0,1)) :=
    (Path.id.map (continuous_const.prodMk continuous_id)).map H.continuous
  let qH : Path (H (0,1)) (H (1,1)) :=
    (Path.id.map (continuous_id.prodMk continuous_const)).map H.continuous
  let rH : Path (H (0,0)) (H (1,0)) :=
    (Path.id.map (continuous_id.prodMk continuous_const)).map H.continuous
  let sH : Path (H (1,0)) (H (1,1)) :=
    (Path.id.map (continuous_const.prodMk continuous_id)).map H.continuous
  have ha : a = H (0,0) := ((hp 0).trans p.source).symm
  have hd : d = H (1,1) := ((hq 1).trans q.target).symm
  have he₁ : (pH.trans qH).cast ha hd = p.trans q := by
    ext t
    change (pH.trans qH) t = (p.trans q) t
    rw [Path.trans_apply, Path.trans_apply]
    split_ifs
    · exact hp _
    · exact hq _
  have he₂ : (rH.trans sH).cast ha hd = r.trans s := by
    ext t
    change (rH.trans sH) t = (r.trans s) t
    rw [Path.trans_apply, Path.trans_apply]
    split_ifs
    · exact hr _
    · exact hs _
  have h := (rectangle_homotopic H).pathCast ha hd
  change ((pH.trans qH).cast ha hd).Homotopic ((rH.trans sH).cast ha hd) at h
  rwa [he₁, he₂] at h

end PresentationVanKampen

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_CoreDeckLeftQuotientCovering
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PresentationGeometry.FiniteStage
attribute [-instance] AddCommGroup.toIntModule
open Set Topology Metric _root_.CategoryTheory CategoryTheory.Limits Cells
open HurewiczConstruction
variable (Q : Type) [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]

structure Stage (n : ℕ) where
  X : Type
  [topology : TopologicalSpace X]
  [t2 : T2Space X]
  [compact : CompactSpace X]
  [cw : CWComplex (univ : Set X)]
  [finite : RelCWComplex.Finite (univ : Set X)]
  point : X
  dimension : ∀ m, RelCWComplex.cell (univ : Set X) m → m < n+3
  I : Type
  core : FiberBundleCore I X Q
  pot : I → X → Q
  coord : ∀ i j x q, core.coordChange i j x q = pot j x * (pot i x)⁻¹ * q
  [simply : SimplyConnectedSpace core.TotalSpace]
  connectivity : ∀ p ≤ n+1, ∀ z : core.TotalSpace,
    Subsingleton (HomotopyGroup (Fin p) core.TotalSpace z)

attribute [instance] Stage.topology Stage.t2 Stage.compact Stage.cw Stage.finite Stage.simply
instance instNonemptyX {n : ℕ} (S : Stage Q n) : Nonempty S.X := ⟨S.point⟩

attribute [instance] AddCommGroup.toIntModule
end PresentationGeometry.FiniteStage

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_PresentationGeometryFiniteStage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ListChains

variable (G : Type*)

abbrev Simplex := G × List G
abbrev Chain := Simplex G →₀ ℤ

def simplexVertex (a : G) : Simplex G := (a, [])
def simplexCone (a : G) (s : Simplex G) : Simplex G := (a, s.1 :: s.2)
def vertex (a : G) : Chain G := Finsupp.single (simplexVertex G a) 1

def cone (a : G) : Chain G →ₗ[ℤ] Chain G :=
  Finsupp.lmapDomain ℤ ℤ (simplexCone G a)

@[simp] lemma cone_single (a : G) (s : Simplex G) (r : ℤ) :
    cone G a (Finsupp.single s r) = Finsupp.single (simplexCone G a s) r := by
  simp [cone]

lemma single_cons (a b : G) (l : List G) (r : ℤ) :
    Finsupp.single (a,b::l) r = cone G a (Finsupp.single (b,l) r) :=
  (cone_single G a (b,l) r).symm

def augmentation : Chain G →ₗ[ℤ] ℤ :=
  Finsupp.linearCombination ℤ (fun s : Simplex G => if s.2 = [] then 1 else 0)

@[simp] lemma augmentation_single (s : Simplex G) (r : ℤ) :
    augmentation G (Finsupp.single s r) = if s.2 = [] then r else 0 := by
  simp only [augmentation, Finsupp.linearCombination_single, smul_eq_mul]
  split_ifs <;> simp

@[simp] lemma augmentation_vertex (a : G) : augmentation G (vertex G a) = 1 := by
  simp [vertex, simplexVertex]

@[simp] lemma augmentation_cone (a : G) (c : Chain G) :
    augmentation G (cone G a c) = 0 := by
  have h : augmentation G ∘ₗ cone G a = 0 := by
    apply Finsupp.lhom_ext
    intro s r
    simp [simplexCone]
  exact LinearMap.congr_fun h c

def K (a : G) : Chain G →ₗ[ℤ] Chain G :=
  Finsupp.lsingle (simplexVertex G a) ∘ₗ augmentation G

@[simp] lemma K_apply (a : G) (c : Chain G) : K G a c = augmentation G c • vertex G a := by
  simp [K, vertex]

@[simp] lemma augmentation_K (a : G) (c : Chain G) :
    augmentation G (K G a c) = augmentation G c := by
  simp

def boundaryAux (a : G) : List G → Chain G
  | [] => 0
  | b :: l => Finsupp.single (b,l) 1 - cone G a (boundaryAux b l) -
    (if l = [] then vertex G a else 0)

def boundary : Chain G →ₗ[ℤ] Chain G :=
  Finsupp.linearCombination ℤ (fun s => boundaryAux G s.1 s.2)

@[simp] lemma boundary_single (s : Simplex G) (r : ℤ) :
    boundary G (Finsupp.single s r) = r • boundaryAux G s.1 s.2 := by
  simp [boundary]

@[simp] lemma boundary_vertex (a : G) : boundary G (vertex G a) = 0 := by
  simp [vertex, simplexVertex, boundaryAux]

@[simp] lemma boundary_K (a : G) (c : Chain G) : boundary G (K G a c) = 0 := by
  simp

lemma boundary_cone (a : G) (c : Chain G) :
    boundary G (cone G a c) = c - cone G a (boundary G c) - K G a c := by
  have h : boundary G ∘ₗ cone G a = LinearMap.id - cone G a ∘ₗ boundary G - K G a := by
    apply Finsupp.lhom_ext
    rintro ⟨b,l⟩ r
    simp only [LinearMap.comp_apply, cone_single, boundary_single, simplexCone, boundaryAux,
      LinearMap.sub_apply, LinearMap.id_apply, K_apply, augmentation_single, map_smul]
    split_ifs <;> simp [smul_sub, Finsupp.smul_single]
  exact LinearMap.congr_fun h c

@[simp] lemma augmentation_boundary (c : Chain G) : augmentation G (boundary G c) = 0 := by
  have h : augmentation G ∘ₗ boundary G = 0 := by
    apply Finsupp.lhom_ext
    rintro ⟨a,l⟩ r
    cases l with
    | nil => simp [boundaryAux]
    | cons b l =>
      change augmentation G (boundary G (Finsupp.single (a,b::l) r)) = 0
      rw [single_cons]
      rw [boundary_cone]
      simp only [map_sub, augmentation_cone, augmentation_K, sub_zero, sub_self]
  exact LinearMap.congr_fun h c

@[simp] lemma K_boundary (a : G) (c : Chain G) : K G a (boundary G c) = 0 := by
  simp

@[simp] lemma boundary_boundary (c : Chain G) : boundary G (boundary G c) = 0 := by
  have hb (l : List G) (a : G) :
      boundary G (boundary G (Finsupp.single (a,l) 1)) = 0 := by
    induction l generalizing a with
    | nil =>
      change boundary G (boundary G (vertex G a)) = 0
      rw [boundary_vertex, map_zero]
    | cons b l ih =>
      rw [single_cons]
      rw [boundary_cone, map_sub, map_sub, boundary_cone, ih b]
      simp only [map_zero, K_boundary, boundary_K, sub_zero, sub_self]
  have h : boundary G ∘ₗ boundary G = 0 := by
    apply Finsupp.lhom_ext
    intro s r
    have hr : Finsupp.single s r = r • Finsupp.single s 1 := by simp
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, hr, map_smul, hb s.2 s.1,
      smul_zero]
  exact LinearMap.congr_fun h c

def degree (s : Simplex G) : ℕ := s.2.length

def mapChain {H : Type*} (f : G → H) : Chain G →ₗ[ℤ] Chain H :=
  Finsupp.lmapDomain ℤ ℤ (fun s => (f s.1, s.2.map f))

@[simp] lemma mapChain_single {H : Type*} (f : G → H) (s : Simplex G) (r : ℤ) :
    mapChain G f (Finsupp.single s r) = Finsupp.single (f s.1, s.2.map f) r := by
  simp [mapChain]

@[simp] lemma mapChain_vertex {H : Type*} (f : G → H) (a : G) :
    mapChain G f (vertex G a) = vertex H (f a) := by
  simp [vertex, simplexVertex]

@[simp] lemma augmentation_mapChain {H : Type*} (f : G → H) (c : Chain G) :
    augmentation H (mapChain G f c) = augmentation G c := by
  have h : augmentation H ∘ₗ mapChain G f = augmentation G := by
    apply Finsupp.lhom_ext
    intro s r
    simp
  exact LinearMap.congr_fun h c

lemma mapChain_K {H : Type*} (f : G → H) (a : G) (c : Chain G) :
    mapChain G f (K G a c) = K H (f a) (mapChain G f c) := by
  simp

def sign : Chain G →ₗ[ℤ] Chain G :=
  Finsupp.linearCombination ℤ (fun s : Simplex G => (-1 : ℤ) ^ degree G s • Finsupp.single s 1)

@[simp] lemma sign_single (s : Simplex G) (r : ℤ) :
    sign G (Finsupp.single s r) = (-1 : ℤ) ^ degree G s • Finsupp.single s r := by
  simp [sign, mul_comm]

@[simp] lemma sign_vertex (a : G) : sign G (vertex G a) = vertex G a := by
  simp [vertex, degree, simplexVertex]

@[simp] lemma augmentation_sign (c : Chain G) : augmentation G (sign G c) = augmentation G c := by
  have h : augmentation G ∘ₗ sign G = augmentation G := by
    apply Finsupp.lhom_ext
    rintro ⟨a,l⟩ r
    simp only [LinearMap.comp_apply, sign_single, map_smul, augmentation_single]
    cases l <;> simp [degree]
  exact LinearMap.congr_fun h c

@[simp] lemma sign_K (a : G) (c : Chain G) : sign G (K G a c) = K G a c := by
  simp

@[simp] lemma K_sign (a : G) (c : Chain G) : K G a (sign G c) = K G a c := by
  simp

def Supported (P : Simplex G → Prop) (c : Chain G) : Prop := ∀ s ∈ c.support, P s

lemma supported_add {P : Simplex G → Prop} {c d : Chain G}
    (hc : Supported G P c) (hd : Supported G P d) : Supported G P (c+d) := by
  classical
  intro s hs
  obtain hs | hs := Finset.mem_union.mp (Finsupp.support_add hs)
  · exact hc s hs
  · exact hd s hs

lemma supported_smul {P : Simplex G → Prop} {c : Chain G}
    (r : ℤ) (hc : Supported G P c) : Supported G P (r • c) :=
  fun s hs => hc s (Finsupp.support_smul hs)

end ListChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_FreeTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace FreeTensor

variable (ι κ : Type*)
abbrev Chains := (ι × κ) →₀ ℤ

def pure : (ι →₀ ℤ) →ₗ[ℤ] (κ →₀ ℤ) →ₗ[ℤ] Chains ι κ :=
  Finsupp.linearCombination ℤ (fun i =>
    Finsupp.linearCombination ℤ (fun k => Finsupp.single (i,k) 1))

@[simp] lemma pure_single_single (i : ι) (k : κ) (r s : ℤ) :
    pure ι κ (Finsupp.single i r) (Finsupp.single k s) = Finsupp.single (i,k) (r*s) := by
  simp [pure]

lemma pure_single_one (i : ι) (k : κ) :
    pure ι κ (Finsupp.single i 1) (Finsupp.single k 1) = Finsupp.single (i,k) 1 := by
  simp

variable {ι κ}

lemma ext {M : Type*} [AddCommGroup M] [Module ℤ M]
    {f g : Chains ι κ →ₗ[ℤ] M}
    (h : ∀ x y, f (pure ι κ x y) = g (pure ι κ x y)) : f = g := by
  apply Finsupp.lhom_ext
  rintro ⟨i,k⟩ r
  have hr : Finsupp.single (i,k) r = r • pure ι κ (Finsupp.single i 1) (Finsupp.single k 1) := by
    simp
  rw [hr, LinearMap.map_smul, LinearMap.map_smul, h]

variable (ι κ)

def map {ι' κ' : Type*} (f : (ι →₀ ℤ) →ₗ[ℤ] (ι' →₀ ℤ))
    (g : (κ →₀ ℤ) →ₗ[ℤ] (κ' →₀ ℤ)) : Chains ι κ →ₗ[ℤ] Chains ι' κ' :=
  Finsupp.linearCombination ℤ (fun s => pure ι' κ' (f (Finsupp.single s.1 1))
    (g (Finsupp.single s.2 1)))

lemma map_pure {ι' κ' : Type*} (f : (ι →₀ ℤ) →ₗ[ℤ] (ι' →₀ ℤ))
    (g : (κ →₀ ℤ) →ₗ[ℤ] (κ' →₀ ℤ)) (x : ι →₀ ℤ) (y : κ →₀ ℤ) :
    map ι κ f g (pure ι κ x y) = pure ι' κ' (f x) (g y) := by
  have h : ((pure ι κ).compr₂ (map ι κ f g)) =
      ((pure ι' κ').comp f).compl₂ g := by
    apply Finsupp.lhom_ext
    intro i r
    apply Finsupp.lhom_ext
    intro k s
    simp only [LinearMap.compr₂_apply, LinearMap.compl₂_apply, LinearMap.comp_apply,
      pure_single_single, map, Finsupp.linearCombination_single]
    have hi : Finsupp.single i r = r • Finsupp.single i 1 := by simp
    have hk : Finsupp.single k s = s • Finsupp.single k 1 := by simp
    rw [hi, hk, LinearMap.map_smul, LinearMap.map_smul, LinearMap.map_smul,
      LinearMap.smul_apply, LinearMap.map_smul, smul_smul]
  exact LinearMap.congr_fun (LinearMap.congr_fun h x) y

def lift {M : Type*} [AddCommGroup M] (f : (ι →₀ ℤ) →ₗ[ℤ] (κ →₀ ℤ) →ₗ[ℤ] M) :
    Chains ι κ →ₗ[ℤ] M :=
  Finsupp.linearCombination ℤ (fun s => f (Finsupp.single s.1 1) (Finsupp.single s.2 1))

lemma lift_pure {M : Type*} [AddCommGroup M]
    (f : (ι →₀ ℤ) →ₗ[ℤ] (κ →₀ ℤ) →ₗ[ℤ] M) (x : ι →₀ ℤ) (y : κ →₀ ℤ) :
    lift ι κ f (pure ι κ x y) = f x y := by
  have h : (pure ι κ).compr₂ (lift ι κ f) = f := by
    apply Finsupp.lhom_ext
    intro i r
    apply Finsupp.lhom_ext
    intro k s
    simp only [LinearMap.compr₂_apply, pure_single_single, lift,
      Finsupp.linearCombination_single]
    have hi : Finsupp.single i r = r • Finsupp.single i 1 := by simp
    have hk : Finsupp.single k s = s • Finsupp.single k 1 := by simp
    simp only [hi, hk, LinearMap.map_smul, LinearMap.smul_apply, smul_smul]
  exact LinearMap.congr_fun (LinearMap.congr_fun h x) y

end FreeTensor

namespace ListChains
section

variable (G H : Type*)

abbrev BiChain := FreeTensor.Chains (Simplex G) (Simplex H)

abbrev tensor : Chain G →ₗ[ℤ] Chain H →ₗ[ℤ] BiChain G H :=
  FreeTensor.pure (Simplex G) (Simplex H)

end

variable (G : Type*)

def vertices (s : Simplex G) : Set G := {a | a = s.1 ∨ a ∈ s.2}

@[simp] lemma mem_vertices (s : Simplex G) (a : G) :
    a ∈ vertices G s ↔ a = s.1 ∨ a ∈ s.2 := Iff.rfl

def degreeModule (n : ℕ) : Submodule ℤ (Chain G) :=
  Finsupp.supported ℤ ℤ {s | degree G s = n}

end ListChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_FreeTensorPureMem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace FreeTensor

variable (ι κ : Type*)

lemma single_mem_supported {α : Type*} (S : Set α) {s : α} (hs : s ∈ S) (r : ℤ) :
    Finsupp.single s r ∈ Finsupp.supported ℤ ℤ S := by
  classical
  intro t ht
  have he : t = s := Finset.mem_singleton.mp (Finsupp.support_single_subset ht)
  simpa only [he] using hs

end FreeTensor

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_ListChains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ListChains
section

variable (G H : Type*)

def includeLeft (b : H) : Chain G →ₗ[ℤ] BiChain G H := (tensor G H).flip (vertex H b)
def includeRight (a : G) : Chain H →ₗ[ℤ] BiChain G H := tensor G H (vertex G a)

@[simp] lemma includeLeft_apply (b : H) (x : Chain G) :
    includeLeft G H b x = tensor G H x (vertex H b) := rfl
@[simp] lemma includeRight_apply (a : G) (y : Chain H) :
    includeRight G H a y = tensor G H (vertex G a) y := rfl

end

end ListChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_ListChainsHasPropagation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ListChains
section

variable (G H : Type*) [Group G] [Group H]

def hasPropagation (A : Set G) (s : Simplex G) : Prop :=
  ∀ x ∈ vertices G s, ∀ y ∈ vertices G s, x⁻¹ * y ∈ A

def controlledModule (A : Set G) : Submodule ℤ (Chain G) :=
  Finsupp.supported ℤ ℤ {s | hasPropagation G A s}

lemma controlledModule_mono {A B : Set G} (h : A ⊆ B) :
    controlledModule G A ≤ controlledModule G B := by
  intro c hc s hs x hx y hy
  exact h (hc hs x hx y hy)

end

variable (G : Type*) [Group G]

structure IsBound (A : Set G) : Prop where
  finite : A.Finite
  one_mem : 1 ∈ A
  inv_mem : ∀ a ∈ A, a⁻¹ ∈ A

lemma IsBound.union {A B : Set G} (ha : IsBound G A) (hb : IsBound G B) :
    IsBound G (A ∪ B) where
  finite := ha.finite.union hb.finite
  one_mem := Or.inl ha.one_mem
  inv_mem a h := h.elim (fun h => Or.inl (ha.inv_mem a h)) (fun h => Or.inr (hb.inv_mem a h))

end ListChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_ListChainsMapChainComp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ListChains
section

variable (G : Type*)

@[simp] lemma mapChain_comp {H K : Type*} (f : G → H) (g : H → K) (c : Chain G) :
    mapChain H g (mapChain G f c) = mapChain G (g ∘ f) c := by
  have h : mapChain H g ∘ₗ mapChain G f = mapChain G (g ∘ f) := by
    apply Finsupp.lhom_ext
    intro s r
    simp [List.map_map]
  exact LinearMap.congr_fun h c

@[simp] lemma mapChain_id (c : Chain G) : mapChain G id c = c := by
  have h : mapChain G id = LinearMap.id := by
    apply Finsupp.lhom_ext
    intro s r
    simp
  exact LinearMap.congr_fun h c

open scoped Pointwise

end

section

variable (G : Type*) [Group G]

def inDegree (n : ℕ) (v : Simplex G → Chain G) : Chain G →ₗ[ℤ] Chain G :=
  Finsupp.linearCombination ℤ (fun s => if degree G s = n then v s else 0)

omit [Group G] in
@[simp] lemma inDegree_single (n : ℕ) (v : Simplex G → Chain G) (s : Simplex G) :
    inDegree G n v (Finsupp.single s 1) = if degree G s = n then v s else 0 := by
  simp [inDegree]

end

variable (G : Type*) [Group G]

@[simp] lemma mapChain_K_one (g : G →* G) (c : Chain G) :
    mapChain G g (K G 1 c) = K G 1 c := by
  rw [mapChain_K]
  simp only [map_one,K_apply,augmentation_mapChain]

end ListChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_BinaryPrefixOperators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ListChains

variable (G : Type*) {H K C D E : Type*}

def cosetMap (σ : C → D) (ψ : C → G → H) :
    (C →₀ Chain G) →ₗ[ℤ] (D →₀ Chain H) :=
  Finsupp.lsum ℤ (fun c => (Finsupp.lsingle (σ c)).comp (mapChain G (ψ c)))

@[simp] lemma cosetMap_single (σ : C → D) (ψ : C → G → H) (c : C) (z : Chain G) :
    cosetMap G σ ψ (Finsupp.single c z) = Finsupp.single (σ c) (mapChain G (ψ c) z) := by
  simp [cosetMap]

@[simp] lemma cosetMap_id (z : C →₀ Chain G) : cosetMap G id (fun _ => id) z = z := by
  have h : cosetMap G (id : C → C) (fun _ => id) = LinearMap.id := by
    apply Finsupp.lhom_ext
    intro c z
    simp only [cosetMap_single,mapChain_id,id_eq,LinearMap.id_apply]
  exact LinearMap.congr_fun h z

def cosetBoundary : (C →₀ Chain G) →ₗ[ℤ] (C →₀ Chain G) :=
  Finsupp.mapRange.linearMap (boundary G)

@[simp] lemma cosetBoundary_apply (z : C →₀ Chain G) (c : C) :
    cosetBoundary G z c = boundary G (z c) := rfl

end ListChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_StandardShapiro
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.CategoryTheory
open _root_.CategoryTheory MonoidalCategory _root_.Representation TensorProduct

namespace FunctionalTree
section

variable {R V M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

def path (p : V → V) (n : ℕ) (v : V) (a : M) : V →₀ M :=
  ∑ k ∈ Finset.range n, Finsupp.single (p^[k] v) a

end

open _root_.CategoryTheory

end FunctionalTree

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_ClassifyingSpaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace FiniteExtension
universe u
variable {L : Type u} [Group L] (K : Subgroup L) [K.Normal]
abbrev Q := L ⧸ K
def pi : L →* Q K := QuotientGroup.mk' K

def sectionMap (c : Q K) : L := by
  classical
  exact if c = 1 then 1 else Classical.choose (QuotientGroup.mk'_surjective K c)
@[simp] lemma section_one : sectionMap K 1 = 1 := by simp [sectionMap]
@[simp] lemma pi_section (c : Q K) : pi K (sectionMap K c) = c := by
  by_cases h : c=1
  · simp [h]
  · simpa [sectionMap,h,pi] using Classical.choose_spec (QuotientGroup.mk'_surjective K c)
@[simp] lemma pi_coe (k : K) : pi K (k : L) = 1 :=
  (QuotientGroup.eq_one_iff _).mpr k.property

def factor (x : L) : K := ⟨x * (sectionMap K (pi K x))⁻¹, by
  apply (QuotientGroup.eq_one_iff _).mp
  change pi K (x * (sectionMap K (pi K x))⁻¹)=1
  simp⟩
def twist (c : Q K) : K →* K :=
  ((MulAut.conj (sectionMap K c)).toMonoidHom.comp K.subtype).codRestrict K
    (fun k => (inferInstance : K.Normal).conj_mem k k.property (sectionMap K c))
def cocycle (c d : Q K) : K := factor K (sectionMap K c * sectionMap K d)
@[simp] lemma factor_one : factor K 1 = 1 := by ext; simp [factor]
@[simp] lemma factor_coe (k : K) : factor K (k : L) = k := by ext; simp [factor]
@[simp] lemma factor_section (c : Q K) : factor K (sectionMap K c) = 1 := by
  ext; simp [factor]
@[simp] lemma twist_coe (c : Q K) (k : K) :
    ((twist K c k : K) : L) = sectionMap K c * k * (sectionMap K c)⁻¹ := rfl
@[simp] lemma cocycle_coe (c d : Q K) :
    ((cocycle K c d : K) : L) =
      sectionMap K c * sectionMap K d * (sectionMap K (c*d))⁻¹ := by simp [cocycle,factor]
lemma factor_mul (x y : L) : factor K (x*y) =
    factor K x * twist K (pi K x) (factor K y) * cocycle K (pi K x) (pi K y) := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul,twist_coe,cocycle_coe,factor,map_mul]
  group

abbrev Pre := Monoid.Coprod K (FreeGroup (Q K))
def inK : K →* Pre K := Monoid.Coprod.inl
def letter (c : Q K) : Pre K := Monoid.Coprod.inr (FreeGroup.of c)
def mulRel (c d : Q K) : Pre K :=
  letter K c * letter K d * (inK K (cocycle K c d) * letter K (c*d))⁻¹
def conjRel (c : Q K) (k : K) : Pre K :=
  letter K c * inK K k * (inK K (twist K c k) * letter K c)⁻¹

def rels (S : Set K) : Set (Pre K) := {letter K 1} ∪
    Set.range (fun p : Q K × Q K => mulRel K p.1 p.2) ∪
    (fun p : Q K × K => conjRel K p.1 p.2) '' (Set.univ ×ˢ S)
abbrev N (S : Set K) := Subgroup.normalClosure (rels K S)
abbrev Presented (S : Set K) := Pre K ⧸ N K S
def quot (S : Set K) : Pre K →* Presented K S := QuotientGroup.mk' (N K S)
def incl (S : Set K) : K →* Presented K S := (quot K S).comp (inK K)
def t (S : Set K) (c : Q K) : Presented K S := quot K S (letter K c)

lemma rel_eq_one (S : Set K) {r : Pre K} (hr : r ∈ rels K S) : quot K S r=1 :=
  (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure hr)
@[simp] lemma t_one (S : Set K) : t K S 1 = 1 :=
  rel_eq_one K S (Or.inl (Or.inl rfl))
lemma t_mul (S : Set K) (c d : Q K) :
    t K S c * t K S d = incl K S (cocycle K c d) * t K S (c*d) := by
  have h := rel_eq_one K S (Or.inl (Or.inr ⟨(c,d),rfl⟩))
  simpa only [mulRel,map_mul,map_inv,mul_inv_eq_one,t,incl,MonoidHom.comp_apply] using h
lemma t_conj_gen (S : Set K) (c : Q K) (k : K) (hk : k∈S) :
    t K S c * incl K S k = incl K S (twist K c k) * t K S c := by
  have h := rel_eq_one K S (Or.inr ⟨(c,k),⟨Set.mem_univ _,hk⟩,rfl⟩)
  simpa only [conjRel,map_mul,map_inv,mul_inv_eq_one,t,incl,MonoidHom.comp_apply] using h
lemma t_conj (S : Set K) (hS : Subgroup.closure S = ⊤) (c : Q K) (k : K) :
    t K S c * incl K S k = incl K S (twist K c k) * t K S c := by
  have h : (MulAut.conj (t K S c)).toMonoidHom.comp (incl K S) =
      (incl K S).comp (twist K c) := by
    apply MonoidHom.eq_of_eqOn_dense hS
    intro k hk
    change t K S c * incl K S k * (t K S c)⁻¹ = incl K S (twist K c k)
    rw [t_conj_gen K S c k hk,mul_inv_cancel_right]
  have hh := DFunLike.congr_fun h k
  change t K S c * incl K S k * (t K S c)⁻¹ = incl K S (twist K c k) at hh
  exact (mul_inv_eq_iff_eq_mul).mp hh

def retract (S : Set K) (hS : Subgroup.closure S = ⊤) : L →* Presented K S where
  toFun x := incl K S (factor K x) * t K S (pi K x)
  map_one' := by simp
  map_mul' x y := by
    simp only [factor_mul,map_mul]
    rw [show incl K S (factor K x) * t K S (pi K x) *
        (incl K S (factor K y) * t K S (pi K y)) =
      incl K S (factor K x) * (t K S (pi K x) * incl K S (factor K y)) *
        t K S (pi K y) by group]
    rw [t_conj K S hS]
    simp only [mul_assoc,← t_mul K S]

@[simp] lemma retract_coe (S : Set K) (hS : Subgroup.closure S = ⊤) (k : K) :
    retract K S hS (k : L) = incl K S k := by simp [retract]
@[simp] lemma retract_section (S : Set K) (hS : Subgroup.closure S = ⊤) (c : Q K) :
    retract K S hS (sectionMap K c) = t K S c := by simp [retract]

def evaluatePre : Pre K →* L := Monoid.Coprod.lift K.subtype (FreeGroup.lift (sectionMap K))
@[simp] lemma evaluatePre_inK (k : K) : evaluatePre K (inK K k) = k := by
  simp [evaluatePre,inK]
@[simp] lemma evaluatePre_letter (c : Q K) : evaluatePre K (letter K c) = sectionMap K c := by
  simp [evaluatePre,letter]
lemma rels_ker (S : Set K) : rels K S ⊆ (evaluatePre K).ker := by
  rintro x ((h|⟨⟨c,d⟩,rfl⟩)|⟨⟨c,k⟩,_,rfl⟩)
  · rcases h with rfl
    change evaluatePre K (letter K 1)=1
    simp
  · change evaluatePre K (mulRel K c d)=1
    simp only [mulRel,map_mul,map_inv,evaluatePre_letter,evaluatePre_inK,
      cocycle_coe]
    group
  · change evaluatePre K (conjRel K c k)=1
    simp only [conjRel,map_mul,map_inv,evaluatePre_letter,evaluatePre_inK,
      twist_coe]
    group

def evaluate (S : Set K) : Presented K S →* L :=
  QuotientGroup.lift (N K S) (evaluatePre K) (Subgroup.normalClosure_le_normal (rels_ker K S))
@[simp] lemma evaluate_quot (S : Set K) (x : Pre K) :
    evaluate K S (quot K S x) = evaluatePre K x := rfl
@[simp] lemma evaluate_incl (S : Set K) (k : K) : evaluate K S (incl K S k) = k := by
  change evaluatePre K (inK K k)=k
  simp
@[simp] lemma evaluate_t (S : Set K) (c : Q K) :
    evaluate K S (t K S c) = sectionMap K c := by
  change evaluatePre K (letter K c)=sectionMap K c
  simp
lemma evaluate_retract (S : Set K) (hS : Subgroup.closure S = ⊤) (x : L) :
    evaluate K S (retract K S hS x) = x := by simp [retract,factor]
lemma retract_evaluate (S : Set K) (hS : Subgroup.closure S = ⊤) (x : Presented K S) :
    retract K S hS (evaluate K S x) = x := by
  obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective (N K S) x
  change ((retract K S hS).comp (evaluatePre K)) y = quot K S y
  have h : (retract K S hS).comp (evaluatePre K) = quot K S := by
    apply Monoid.Coprod.hom_ext
    · ext k
      change retract K S hS (evaluatePre K (inK K k)) = incl K S k
      simp
    · apply FreeGroup.ext_hom
      intro c
      change retract K S hS (evaluatePre K (letter K c)) = t K S c
      simp
  exact DFunLike.congr_fun h y

def presentationEquiv (S : Set K) (hS : Subgroup.closure S = ⊤) : Presented K S ≃* L :=
  { evaluate K S with
    invFun := retract K S hS
    left_inv := retract_evaluate K S hS
    right_inv := evaluate_retract K S hS }

end FiniteExtension

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_FiniteIndexRegular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace FiniteIndexRegular
open _root_.CategoryTheory _root_.Representation FiniteExtension
variable {L : Type} [Group L] (K : Subgroup L) [K.Normal] (I : Type)
open scoped Classical TensorProduct MonoidAlgebra

noncomputable def coords : L ≃ Q K × K where
  toFun x := (pi K x, factor K x)
  invFun p := (p.2 : L) * sectionMap K p.1
  left_inv x := by simp [factor]
  right_inv p := by
    rcases p with ⟨c,k⟩
    apply Prod.ext
    · simp
    · apply Subtype.ext
      simp [factor]

@[simp] lemma coords_mul_section (k : K) (c : Q K) :
    coords K ((k : L)*sectionMap K c) = (c,k) := (coords K).apply_symm_apply (c,k)

noncomputable def slice (c : Q K) : (L →₀ ℤ) →ₗ[ℤ] (K →₀ ℤ) :=
  (Finsupp.lapply c).comp ((Finsupp.curryLinearEquiv ℤ).toLinearMap.comp
    (Finsupp.domLCongr (coords K)).toLinearMap)

@[simp] lemma slice_single (c : Q K) (x : L) (z : ℤ) :
    slice K c (Finsupp.single x z) =
      Finsupp.single (pi K x) (Finsupp.single (factor K x) z) c := by
  simp [slice, coords, Finsupp.curry_single]

@[simp] lemma factor_coemul (k : K) (h : L) :
    factor K ((k : L)*h) = k*factor K h := by
  apply Subtype.ext
  simp [factor, mul_assoc]

variable [Fintype (Q K)]

lemma sum_slices (a : L →₀ ℤ) :
    (∑ c : Q K, Finsupp.lmapDomain ℤ ℤ (fun k : K => (k : L)*sectionMap K c)
      (slice K c a)) = a := by
  have heq : (∑ c : Q K, (Finsupp.lmapDomain ℤ ℤ
        (fun k : K => (k : L)*sectionMap K c)).comp (slice K c)) =
      (LinearMap.id : (L →₀ ℤ) →ₗ[ℤ] (L →₀ ℤ)) := by
    apply Finsupp.lhom_ext
    intro x z
    simp only [LinearMap.sum_apply, LinearMap.comp_apply, slice_single,
      Finsupp.single_apply, apply_ite, map_zero]
    rw [Finset.sum_ite_eq]
    simp [factor]
  simpa only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.id_apply]
    using LinearMap.congr_fun heq a

end FiniteIndexRegular

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_AscendingHNNInnerTwist
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Pointwise

namespace HomStabilizer
variable {G H X : Type*} [Group G] [Group H]

def fixedTuple (ρ : G →* Equiv.Perm X) {J : Type*} (v : J → X) : Subgroup G where
  carrier := {g | ∀ j, ρ g (v j) = v j}
  one_mem' := by intro j; simp
  mul_mem' := by intro g h hg hh j; simp only [map_mul,Equiv.Perm.mul_apply]; rw [hh j,hg j]
  inv_mem' := by
    intro g hg j
    have h := congrArg (ρ g).symm (hg j)
    simpa only [map_inv,Equiv.Perm.inv_def,Equiv.symm_apply_apply] using h.symm

@[simp] lemma mem_fixedTuple (ρ : G →* Equiv.Perm X) {J : Type*} (v : J → X) (g : G) :
    g ∈ fixedTuple ρ v ↔ ∀ j, ρ g (v j)=v j := Iff.rfl

def preimageEquiv (e : G ≃* H) (K : Subgroup H) : K.comap e.toMonoidHom ≃* K where
  toFun g := ⟨e g,g.property⟩
  invFun h := ⟨e.symm h,by change e (e.symm h.val) ∈ K; simpa only [e.apply_symm_apply] using h.property⟩
  left_inv g := Subtype.ext (e.symm_apply_apply g.val)
  right_inv h := Subtype.ext (e.apply_symm_apply h.val)
  map_mul' g h := Subtype.ext (e.map_mul g.val h.val)

end HomStabilizer

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_HomStabilizer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Pointwise
namespace HomStabilizer
variable {G X J : Type} [Group G]
                                                                                  
def conjugateTuple (ρ : G →* Equiv.Perm X) (x y : J → X) (q : G)
    (h : ∀ j, ρ q (x j) = y j) : fixedTuple ρ x ≃* fixedTuple ρ y where
  toFun g := ⟨q * g.val * q⁻¹, by
    intro j
    rw [← h j,map_mul,map_mul,map_inv]
    change ρ q (ρ g.val ((ρ q).symm (ρ q (x j)))) = ρ q (x j)
    rw [Equiv.symm_apply_apply,g.property j]⟩
  invFun g := ⟨q⁻¹ * g.val * q, by
    intro j
    rw [map_mul,map_mul,map_inv]
    change (ρ q).symm (ρ g.val (ρ q (x j))) = x j
    rw [h j,g.property j,←h j,Equiv.symm_apply_apply]⟩
  left_inv g := by apply Subtype.ext; change q⁻¹ * (q * g.val * q⁻¹) * q = g.val; group
  right_inv g := by apply Subtype.ext; change q * (q⁻¹ * g.val * q) * q⁻¹ = g.val; group
  map_mul' g g' := by
    apply Subtype.ext
    change q * (g.val * g'.val) * q⁻¹ = (q*g.val*q⁻¹)*(q*g'.val*q⁻¹)
    group

def enumeratedSubset [MulAction G X] (y : J → X) (s : Set X)
    (h : Set.range y=s) : fixedTuple (MulAction.toPermHom G X) y ≃* fixingSubgroup G s where
  toFun g := ⟨g.val, (mem_fixingSubgroup_iff G).mpr (by
    intro x hx
    obtain ⟨j,rfl⟩ := h.symm.subset hx
    exact g.property j)⟩
  invFun g := ⟨g.val, by
    intro j
    exact (mem_fixingSubgroup_iff G).mp g.property (y j) (h.subset ⟨j,rfl⟩)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

end HomStabilizer

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_InducedFree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory CategoryTheory.Limits
open _root_.CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open _root_.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped MonoidalCategory
open Classical
open _root_.CategoryTheory CategoryTheory.Limits
open _root_.CategoryTheory CategoryTheory.Limits _root_.Representation
namespace InducedFree
variable {k G H : Type} [CommRing k] [Group G] [Group H]
variable (φ : G →* H) (α : Type)

def unit (j : α) : Rep.free k G α := Finsupp.single j (.single 1 1)
def seed : Rep.free k G α ⟶ Rep.res φ (Rep.free k H α) :=
  Rep.freeLift k G _ (fun j => unit (k := k) (G := H) α j)
def forward : Rep.ind φ (Rep.free k G α) ⟶ Rep.free k H α :=
  (Rep.indResHomEquiv φ _ _).symm (seed φ α)
def backward : Rep.free k H α ⟶ Rep.ind φ (Rep.free k G α) :=
  Rep.freeLift k H _ (fun j => IndV.mk φ (Rep.free k G α).ρ 1 (unit α j))

lemma forward_mk (h : H) (a : Rep.free k G α) :
    forward φ α (IndV.mk φ (Rep.free k G α).ρ h a) =
      (Rep.free k H α).ρ h⁻¹ (seed φ α a) := by
  simp [forward,Rep.indResHomEquiv]

lemma seed_unit (j : α) : seed (k := k) φ α (unit α j) = unit α j := by
  simp [seed,unit,Rep.freeLift,Representation.freeLift]
lemma backward_unit (j : α) : backward (k := k) φ α (unit α j) =
    IndV.mk φ (Rep.free k G α).ρ 1 (unit α j) := by
  simp [backward,unit,Rep.freeLift,Representation.freeLift]

lemma backward_forward : backward (k := k) φ α ≫ forward φ α = 𝟙 _ := by
  apply Rep.free_ext
  intro j
  change forward φ α (backward φ α (unit α j)) = unit α j
  rw [backward_unit,forward_mk,seed_unit]
  simp

lemma forward_backward : forward (k := k) φ α ≫ backward φ α = 𝟙 _ := by
  apply (Rep.indResHomEquiv φ _ _).injective
  apply Rep.free_ext
  intro j
  change backward φ α (forward φ α (IndV.mk φ (Rep.free k G α).ρ 1 (unit α j))) =
    IndV.mk φ (Rep.free k G α).ρ 1 (unit α j)
  rw [forward_mk,seed_unit]
  simpa only [inv_one,map_one,Module.End.one_apply] using backward_unit (k := k) φ α j

def iso : Rep.ind φ (Rep.free k G α) ≅ Rep.free k H α where
  hom := forward φ α
  inv := backward φ α
  hom_inv_id := forward_backward φ α
  inv_hom_id := backward_forward φ α
end InducedFree

open _root_.CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_PosetTransport
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
namespace PosetTransport
section
universe u v w
variable {P : Type u} [Preorder P] {Q : Type v} [Preorder Q]
variable {H : Type w} [Group H]

def Adj (x y : P) : Prop := x ≤ y ∨ y ≤ x
end

end PosetTransport

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_ThreeCodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SimpleFInftyOvergroups.ContextualEncoding
noncomputable section
open FiniteAlgebraicEnvelopes

namespace ThreeCodes
abbrev Alphabet := Option (Fin 3 × Fin 4)

end ThreeCodes
end
end SimpleFInftyOvergroups.ContextualEncoding

end OAI
end


