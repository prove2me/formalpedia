-- Prove2me | Definitions.Def_OAIQ66So000
-- name    : OAIQ66So000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T02:10:20.146543+00:00
-- url     : https://prove2.me/theorems/2f929190-da79-4848-b251-df43c76ae26f
-- title:
--   Definitions bundle OAIQ66So000 of the split of OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SimpleFInftyOvergroups.main`, carved from OpenAI's openai/math development (OpenAI, *Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)*, OpenAI Math Release, September 23, 2026, result family 250, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 314 declarations of OpenAI's Lean: 116 definitions, 7 inductive types or structures, 13 instances and 178 theorems. The definitions and types are `Convexity.StdSimplex.barycenter`, `Convexity.StdSimplex.equivIcc`, `Convexity.StdSimplex.subBarycenter`, `Convexity.StdSimplex.topologicalSpaceInduced`, `OAI.ActionPresentation.LiftModel`, `OAI.ActionPresentation.LiftModel.hom`, `OAI.ActionPresentation.LiftModel.obstruction`, `OAI.ActionPresentation.descend`, `OAI.ActionPresentation.killProjection`, `OAI.ActionPresentation.liftModel`, `OAI.ActionTransport.Edge`, `OAI.ActionTransport.Edge.diag`, `OAI.ActionTransport.Frames`, `OAI.ActionTransport.Frames.stab`, `OAI.ActionTransport.Gauge`, `OAI.ActionTransport.Gauge.map`, `OAI.ActionTransport.IsMonotoneAction`, `OAI.ActionTransport.LiftedFrames`, `OAI.ActionTransport.LiftedFrames.eval`, `OAI.ActionTransport.LiftedFrames.gauge`, `OAI.ActionTransport.Triangle`, `OAI.ActionTransport.Triangle.e01`, `OAI.ActionTransport.Triangle.e02`, `OAI.ActionTransport.Triangle.e12`, `OAI.ActionTransport.cocycleOfFlat`, `OAI.ActionTransport.edgeLeftHom`, `OAI.ActionTransport.edgeRightHom`, `OAI.ActionTransport.edgeTransport`, `OAI.ActionTransport.orbitFrames`, `OAI.ActionTransport.rawEdge`, `OAI.AcyclicChain.chainRow`, `OAI.AcyclicChain.cycles`, `OAI.AcyclicChain.inclusion`, `OAI.AcyclicChain.projection`, `OAI.AcyclicChain.row`, `OAI.AcyclicResolution.complexRow`, `OAI.AcyclicResolution.differential`, `OAI.AcyclicResolution.row`, `OAI.AffineChains.chains`, `OAI.AffineChains.cone` and 83 more.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory, in whole or in part: `FiniteType_ActionTransport`, `FiniteType_AffineSimplex`, `FiniteType_AscendingHNN`, `FiniteType_AscendingHNNInnerTwist`, `FiniteType_AscendingTorus`, `FiniteType_PosetTransport`, `FiniteType_PresentationGeometry`, `FiniteType_PresentationGeometryCellCoverExtension`, `FiniteType_SequentialLimit`, `FiniteType_SingularSphereCycle`, `FiniteType_SingularSubdivision`, `FiniteType_SingularSupport`, `FiniteType_SourceCorner`, `FiniteType_SurjectiveTrivialInduction`, `FiniteType_TorusAction`, `FiniteType_TwistedBrinBasisMatching`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ66So010`, `OAIQ66So011`, `OAIQ66So012`, `OAIQ66So014` and `OAIQ66So015`.
-- source:
--   OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 250; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/ComparatorChallenges/SimpleOvergroups.lean; Apache License 2.0); definitions carved from lean/OAI/GroupTheory at commit 1581d4c

import Mathlib

section
-- module Solutions.OAIQ066_SO.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
end OAICompat434

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

namespace AttachingLoops

open scoped unitInterval

def complexVector (z : ℂ) : Fin 2 → ℝ := ![z.re, z.im]

end AttachingLoops

end PresentationGeometry

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_PresentationGeometryCellCoverExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open _root_.CategoryTheory AlgebraicTopology Limits
open scoped Simplicial
namespace AffineChains
section

def vertices (V : Type) : SSet where
  obj n := Fin (n.unop.len+1) → V
  map f := ↾fun v => v ∘ f.unop.toOrderHom
  map_id _ := rfl
  map_comp _ _ := rfl

abbrev chains (V : Type) := (vertices V).chainComplex (ModuleCat.of ℤ ℤ)

variable {V W : Type}

def generator {n : ℕ} (v : Fin (n+1) → V) : ModuleCat.of ℤ ℤ ⟶ (chains V).X n :=
  (vertices V).ιChainComplex v

lemma generator_boundary {n : ℕ} (v : Fin (n+2) → V) :
    generator v ≫ (chains V).d (n+1) n =
      ∑ i : Fin (n+2), (-1:ℤ)^i.val • generator (v ∘ i.succAbove) := by
  exact SSet.ιChainComplex_d (R := ModuleCat.of ℤ ℤ) (X := vertices V) v

def desc {n : ℕ} {A : ModuleCat ℤ} (b : (Fin (n+1) → V) → (ModuleCat.of ℤ ℤ ⟶ A)) :
    (chains V).X n ⟶ A := Sigma.desc b

@[reassoc (attr := simp)] lemma generator_desc {n : ℕ} {A : ModuleCat ℤ}
    (b : (Fin (n+1) → V) → (ModuleCat.of ℤ ℤ ⟶ A)) (v : Fin (n+1) → V) :
    generator v ≫ desc b = b v := by
  exact Sigma.ι_desc _ _

lemma hom_ext {n : ℕ} {A : ModuleCat ℤ} {f g : (chains V).X n ⟶ A}
    (h : ∀ v : Fin (n+1) → V, generator v ≫ f = generator v ≫ g) : f = g :=
  SSet.chainComplex_hom_ext h

def verticesMap (f : V → W) : vertices V ⟶ vertices W where
  app _ := ↾fun v => f ∘ v
  naturality _ _ _ := rfl

def map (f : V → W) : chains V ⟶ chains W :=
  SSet.chainComplexMap (verticesMap f) (ModuleCat.of ℤ ℤ)

@[reassoc (attr := simp)] lemma generator_map {n : ℕ} (v : Fin (n+1) → V) (f : V → W) :
    generator v ≫ (map f).f n = generator (f ∘ v) := by
  exact SSet.ι_chainComplexMap_f (vertices V) (vertices W) (verticesMap f) (ModuleCat.of ℤ ℤ) v

def cone (x : V) (n : ℕ) : (chains V).X n ⟶ (chains V).X (n+1) :=
  desc (fun v => generator (Fin.cons x v))

@[reassoc (attr := simp)] lemma generator_cone {n : ℕ} (v : Fin (n+1) → V) (x : V) :
    generator v ≫ cone x n = generator (Fin.cons x v) := generator_desc _ _

lemma cons_face_zero {n : ℕ} (v : Fin (n+1) → V) (x : V) :
    Fin.cons x v ∘ (0 : Fin (n+2)).succAbove = v := by
  funext i
  simp

lemma cons_face_succ {n : ℕ} (v : Fin (n+2) → V) (x : V) (i : Fin (n+2)) :
    Fin.cons x v ∘ i.succ.succAbove = Fin.cons x (v ∘ i.succAbove) := by
  funext j
  induction j using Fin.cases with
  | zero => simp
  | succ j => simp

lemma cone_boundary_zero (x : V) :
    cone x 0 ≫ (chains V).d 1 0 = 𝟙 _ - (map (fun _ : V => x)).f 0 := by
  apply hom_ext
  intro v
  simp only [← Category.assoc,generator_cone,generator_boundary,
    Preadditive.comp_sub,Category.comp_id,generator_map]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero,pow_zero,one_smul,cons_face_zero,Fin.sum_univ_one,
    Fin.val_succ,Fin.val_zero,zero_add,pow_one,neg_smul,one_smul]
  rw [sub_eq_add_neg]
  congr 2
  apply congrArg generator
  funext i
  fin_cases i
  simp

lemma cone_boundary_succ (x : V) (n : ℕ) :
    cone x (n+1) ≫ (chains V).d (n+2) (n+1) =
      𝟙 _ - (chains V).d (n+1) n ≫ cone x n := by
  apply hom_ext
  intro v
  simp only [← Category.assoc,generator_cone,generator_boundary,
    Preadditive.comp_sub,Category.comp_id,Preadditive.sum_comp,Preadditive.zsmul_comp]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero,pow_zero,one_smul,cons_face_zero,Fin.val_succ,pow_succ,
    mul_neg_one,neg_smul,cons_face_succ]
  rw [Finset.sum_neg_distrib]
  exact sub_eq_add_neg _ _ |>.symm

end

section
open _root_.CategoryTheory AlgebraicTopology Limits
variable {V : Type}

lemma boundary_constant (x : V) :
    (chains V).d 1 0 ≫ (map (fun _ : V => x)).f 0 = 0 := by
  apply hom_ext
  intro v
  rw [← Category.assoc,generator_boundary]
  simp only [Preadditive.sum_comp,Preadditive.zsmul_comp,generator_map,comp_zero]
  change (∑ i : Fin 2, (-1:ℤ)^i.val • generator (fun _ : Fin 1 => x)) = 0
  simp [Fin.sum_univ_two]

variable (b : ∀ {n : ℕ}, (Fin (n+1) → V) → V)

def subdiv (b : ∀ {n : ℕ}, (Fin (n+1) → V) → V) (n : ℕ) : (chains V).X n ⟶ (chains V).X n :=
  match n with
  | 0 => 𝟙 _
  | n+1 => desc (fun v => generator v ≫ (chains V).d (n+1) n ≫ subdiv b n ≫ cone (b v) n)

@[simp] lemma subdiv_zero : subdiv b (V := V) 0 = 𝟙 _ := rfl

@[reassoc (attr := simp)] lemma generator_subdiv_succ {n : ℕ} (v : Fin (n+2) → V) :
    generator v ≫ subdiv b (n+1) =
      generator v ≫ (chains V).d (n+1) n ≫ subdiv b n ≫ cone (b v) n :=
  generator_desc _ _

lemma subdiv_comm (n : ℕ) :
    subdiv b (V := V) (n+1) ≫ (chains V).d (n+1) n =
      (chains V).d (n+1) n ≫ subdiv b n := by
  induction n with
  | zero =>
    apply hom_ext
    intro v
    rw [← Category.assoc,generator_subdiv_succ]
    simp only [subdiv_zero,Category.id_comp,Category.comp_id,Category.assoc]
    rw [cone_boundary_zero,Preadditive.comp_sub,Category.comp_id]
    rw [boundary_constant,sub_zero]
  | succ n ih =>
    apply hom_ext
    intro v
    rw [← Category.assoc,generator_subdiv_succ]
    simp only [Category.assoc]
    rw [cone_boundary_succ,Preadditive.comp_sub,Category.comp_id]
    rw [← Category.assoc (subdiv b (n+1)),ih]
    simp only [Preadditive.comp_sub,Category.assoc]
    rw [← Category.assoc ((chains V).d (n+2) (n+1))]
    simp only [HomologicalComplex.d_comp_d,zero_comp,comp_zero,sub_zero]

def prism (b : ∀ {n : ℕ}, (Fin (n+1) → V) → V) (n : ℕ) : (chains V).X n ⟶ (chains V).X (n+1) :=
  match n with
  | 0 => 0
  | n+1 => desc (fun v =>
      (generator v - generator v ≫ subdiv b (n+1) -
        generator v ≫ (chains V).d (n+1) n ≫ prism b n) ≫ cone (b v) (n+1))

@[simp] lemma prism_zero : prism b (V := V) 0 = 0 := rfl

@[reassoc (attr := simp)] lemma generator_prism_succ {n : ℕ} (v : Fin (n+2) → V) :
    generator v ≫ prism b (n+1) =
      (generator v - generator v ≫ subdiv b (n+1) -
        generator v ≫ (chains V).d (n+1) n ≫ prism b n) ≫ cone (b v) (n+1) :=
  generator_desc _ _

lemma prism_boundary (n : ℕ) :
    prism b (V := V) (n+1) ≫ (chains V).d (n+2) (n+1) =
      𝟙 _ - subdiv b (n+1) - (chains V).d (n+1) n ≫ prism b n := by
  induction n with
  | zero =>
    apply hom_ext
    intro v
    rw [← Category.assoc,generator_prism_succ,Category.assoc,cone_boundary_succ]
    simp only [prism_zero,comp_zero,sub_zero,Preadditive.comp_sub,Category.comp_id]
    rw [← Category.assoc,Preadditive.sub_comp,Category.assoc,subdiv_comm,
      subdiv_zero,Category.comp_id,sub_self,zero_comp,sub_zero]
  | succ n ih =>
    apply hom_ext
    intro v
    rw [← Category.assoc,generator_prism_succ,Category.assoc,cone_boundary_succ]
    simp only [Preadditive.comp_sub,Category.comp_id]
    have hz : (generator v - generator v ≫ subdiv b (n+2) -
        generator v ≫ (chains V).d (n+2) (n+1) ≫ prism b (n+1)) ≫
          (chains V).d (n+2) (n+1) = 0 := by
      simp only [Preadditive.sub_comp,Category.assoc]
      rw [subdiv_comm,ih]
      simp only [Preadditive.comp_sub,Category.comp_id]
      rw [← Category.assoc ((chains V).d (n+2) (n+1))]
      simp only [HomologicalComplex.d_comp_d,zero_comp,comp_zero,sub_zero,sub_self]
    have hz' := congrArg (fun k => k ≫ cone (b v) (n+1)) hz
    simp only [Category.assoc,zero_comp] at hz'
    try simp only [Category.assoc]
    rw [hz',sub_zero]

end

open _root_.CategoryTheory AlgebraicTopology Limits
variable {V W : Type}

lemma map_cone (f : V → W) (x : V) (n : ℕ) :
    (map f).f n ≫ cone (f x) n = cone x n ≫ (map f).f (n+1) := by
  apply hom_ext
  intro v
  simp only [← Category.assoc,generator_map,generator_cone]
  congr 1
  funext i
  induction i using Fin.cases with
  | zero => rfl
  | succ i => rfl

variable (b : ∀ {n : ℕ}, (Fin (n+1) → V) → V)
  (c : ∀ {n : ℕ}, (Fin (n+1) → W) → W) (f : V → W)
  (hf : ∀ {n : ℕ} (v : Fin (n+1) → V), f (b v) = c (f ∘ v))

include hf
lemma subdiv_map (n : ℕ) :
    subdiv b n ≫ (map f).f n = (map f).f n ≫ subdiv c n := by
  induction n with
  | zero => simp
  | succ n ih =>
    apply hom_ext
    intro v
    rw [← Category.assoc,generator_subdiv_succ]
    simp only [Category.assoc]
    rw [← map_cone,← Category.assoc (subdiv b n),ih]
    simp only [Category.assoc]
    rw [← Category.assoc ((chains V).d (n+1) n),← (map f).comm]
    simp only [Category.assoc]
    simp only [generator_map_assoc,generator_subdiv_succ,hf]

lemma prism_map (n : ℕ) :
    prism b n ≫ (map f).f (n+1) = (map f).f n ≫ prism c n := by
  induction n with
  | zero => simp
  | succ n ih =>
    apply hom_ext
    intro v
    rw [← Category.assoc,generator_prism_succ]
    simp only [Category.assoc]
    rw [← map_cone,← Category.assoc]
    have inner : (generator v - generator v ≫ subdiv b (n+1) -
        generator v ≫ (chains V).d (n+1) n ≫ prism b n) ≫ (map f).f (n+1) =
        generator (f ∘ v) - generator (f ∘ v) ≫ subdiv c (n+1) -
          generator (f ∘ v) ≫ (chains W).d (n+1) n ≫ prism c n := by
      simp only [Preadditive.sub_comp,Category.assoc]
      rw [subdiv_map b c f hf,ih]
      rw [← Category.assoc ((chains V).d (n+1) n),← (map f).comm]
      simp only [Category.assoc,generator_map,generator_map_assoc]
    rw [inner,hf]
    rw [generator_map_assoc,generator_prism_succ]

end AffineChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.StdSimplexCompat
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

lemma mem_range_map_iff
    (f : X → Y) (s : StdSimplex R Y) :
    s ∈ Set.range (map f) ↔ ∀ (x : Y), x ∉ Set.range f → s.weights x = 0 := by
  classical
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨s, rfl⟩
    intro x hx
    simpa using Finsupp.mapDomain_of_notMem_range s.weights x hx
  · have (i : s.weights.support) : ∃ (m : X), f m = i := by
      by_contra hne
      simp only [not_exists] at hne
      exact (Finsupp.mem_support_iff.mp i.2) (h i (by rintro ⟨m, hm⟩; exact hne m hm))
    choose m hm using this
    refine ⟨{
      weights := ∑ (y : s.weights.support), .single (m y) (s.weights y)
      nonneg := by
        intro x
        simp only [Finsupp.coe_finsetSum, Finset.sum_apply,
          Finsupp.coe_zero, Pi.zero_apply]
        refine Finset.sum_nonneg fun y _ ↦ ?_
        rw [Finsupp.single_apply]
        split_ifs
        · exact s.weights_nonneg _
        · exact le_rfl
      total := by
        rw [← Finsupp.sum_finsetSum_index (by simp) (by simp)]
        simp only [Finsupp.sum_single_index]
        rw [← s.total, Finsupp.sum, Finset.univ_eq_attach]
        exact Finset.sum_attach s.weights.support (fun y => s.weights y) }, ?_⟩
    ext y
    by_cases hy : y ∈ s.weights.support
    · simp only [Finset.univ_eq_attach, weights_map, Finsupp.mapDomain_finsetSum,
        Finsupp.mapDomain_single, Finsupp.coe_finsetSum, Finset.sum_apply, hm]
      rw [Finset.sum_eq_single ⟨y, hy⟩ ?_ (by simp)]
      · simp
      · intro z _ hz'
        rw [Finsupp.single_apply, if_neg]
        intro hzy
        exact hz' (Subtype.ext hzy)
    · rw [Finsupp.notMem_support_iff] at hy
      rw [hy]
      simp only [Finset.univ_eq_attach, weights_map, Finsupp.mapDomain_finsetSum,
        Finsupp.mapDomain_single, Finsupp.coe_finsetSum, Finset.sum_apply, hm]
      refine Finset.sum_eq_zero (fun z _ ↦ Finsupp.single_eq_of_ne ?_)
      rintro rfl
      exact (Finsupp.mem_support_iff.mp z.2) hy

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

section Real

variable (M : Type*)

lemma range_toFun_comp_weights_subset_closedBall [Fintype M] :
    Set.range (fun t ↦ t.weights : StdSimplex ℝ M → M → ℝ) ⊆ Metric.closedBall 0 1 := by
  rintro _ ⟨x, rfl⟩
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨by linarith [x.weights_nonneg i], x.weights_apply_le_one i⟩

lemma isBounded_range_toFun_comp_weights [Finite M] :
    Bornology.IsBounded (Set.range (fun t ↦ t.weights : StdSimplex ℝ M → M → ℝ)) := by
  have := Fintype.ofFinite M
  exact Bornology.IsBounded.subset Metric.isBounded_closedBall
    (range_toFun_comp_weights_subset_closedBall M)

lemma diam_range_toFun_comp_weights_subset_closedBall [Fintype M] :
    Metric.diam (Set.range (fun t ↦ t.weights : StdSimplex ℝ M → M → ℝ)) ≤ 1 :=
  Metric.diam_le_of_forall_dist_le (by simp) (by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    rw [dist_pi_le_iff zero_le_one]
    intro i
    rw [Real.dist_eq, abs_le]
    have := x.weights_nonneg i
    have := y.weights_nonneg i
    have := x.weights_apply_le_one i
    have := y.weights_apply_le_one i
    constructor <;> linarith)

end Real

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

/-- The barycenter of the standard simplex. -/
noncomputable abbrev barycenter [Nonempty M] [Fintype M] : StdSimplex K M :=
  subBarycenter .univ (by simp)

lemma weights_barycenter_apply [Nonempty M] [Fintype M] (m : M) :
    (barycenter (K := K) (M := M)).weights m = (Fintype.card M : K)⁻¹ := by
  classical
  simp [barycenter, weights_subBarycenter, Finsupp.single_apply]

end StdSimplex

/-! ### Path-connectedness (Mathlib `d13f23b`, `PathConnectedSpaceStdSimplex.lean`) -/

namespace StdSimplex

open Classical in
@[fun_prop]
lemma continuous_convexCombPair {M : Type*} (x y : StdSimplex ℝ M) :
    Continuous (fun t ↦ convexCombPair (R := ℝ) (unitInterval.symm t) t
        (unitInterval.nonneg _) (unitInterval.nonneg _) (by simp) x y) := by
  wlog hM : Finite M
  · let s : Finset M := x.weights.support ∪ y.weights.support
    let ι : s → M := Subtype.val
    obtain ⟨x', hx⟩ := (mem_range_map_iff ι x).2 (by
      intro m hm
      by_contra hne
      exact hm ⟨⟨m, Finset.mem_union_left _ (Finsupp.mem_support_iff.mpr hne)⟩, rfl⟩)
    obtain ⟨y', hy⟩ := (mem_range_map_iff ι y).2 (by
      intro m hm
      by_contra hne
      exact hm ⟨⟨m, Finset.mem_union_right _ (Finsupp.mem_support_iff.mpr hne)⟩, rfl⟩)
    simp only [← hx, ← hy]
    convert (StdSimplex.continuous_map ℝ ι).comp
      (this x' y' (by dsimp [s]; infer_instance)) using 1
    ext t : 1
    exact ((isAffineMap_map ℝ ι).map_convexCombPair ..).symm
  rw [(StdSimplex.isEmbedding_toFun_comp_weights _ _).continuous_iff]
  unfold Function.comp
  refine continuous_pi (fun i ↦ ?_)
  simp only [unitInterval.coe_symm_eq, weights_convexCombPair, Finsupp.coe_add,
    Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  fun_prop

@[fun_prop]
lemma continuous_duple {M : Type*} (x y : M) :
    Continuous (fun t ↦ duple (R := ℝ) x y
      (unitInterval.nonneg (unitInterval.symm t)) (unitInterval.nonneg t) (by simp)) := by
  convert continuous_convexCombPair (.single x) (.single y) using 1
  ext t : 1
  ext : 1
  simp [weights_convexCombPair]

instance pathConnectedSpace
    (M : Type*) [Nonempty M] : PathConnectedSpace (StdSimplex ℝ M) where
  nonempty := by infer_instance
  joined x y :=
  ⟨{toContinuousMap := ⟨_, continuous_convexCombPair x y⟩
    source' := by simp [convexCombPair_one]
    target' := by simp [convexCombPair_zero] }⟩

end StdSimplex

end Convexity

/-! ## Part 2: `OAI.SStd`, the subtype `stdSimplex R X` with the `d13f23b` names -/

namespace OAI

/-- The standard simplex on a finite type, as the subtype `stdSimplex R X`
(the topological simplex of this Mathlib's `SimplexCategory.toTop`). -/
abbrev SStd (R : Type*) [Semiring R] [PartialOrder R] (X : Type*) [Fintype X] : Type _ :=
  ↥(stdSimplex R X)

namespace SStd

section Semiring

variable {R : Type*} [Semiring R] [PartialOrder R]
variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]

/-- The weights as a finitely supported function. -/
noncomputable def weights (s : SStd R X) : X →₀ R := Finsupp.equivFunOnFinite.symm s.1

lemma weights_apply (s : SStd R X) (x : X) : s.weights x = s.1 x := rfl

lemma weights_nonneg (s : SStd R X) (x : X) : 0 ≤ s.weights x := s.2.1 x

lemma total_of_fintype (s : SStd R X) : ∑ x, s.weights x = 1 := s.2.2

lemma ext {s t : SStd R X} (h : s.weights = t.weights) : s = t :=
  Subtype.ext (congrArg (fun f : X →₀ R => (f : X → R)) h)

@[simp] lemma weights_inj {s t : SStd R X} : s.weights = t.weights ↔ s = t :=
  ⟨ext, fun h => h ▸ rfl⟩

/-- The structure `Convexity.StdSimplex` with the same weights. -/
noncomputable def toStdSimplex (s : SStd R X) : Convexity.StdSimplex R X where
  weights := s.weights
  nonneg := fun x => s.weights_nonneg x
  total := by rw [Finsupp.sum_fintype _ _ (by simp)]; exact s.total_of_fintype

/-- The point of the subtype with the weights of a `Convexity.StdSimplex`. -/
def ofStdSimplex (s : Convexity.StdSimplex R X) : SStd R X :=
  ⟨⇑s.weights, fun x => s.weights_nonneg x, by
    have := s.total
    rwa [Finsupp.sum_fintype _ _ (by simp)] at this⟩

@[simp] lemma weights_toStdSimplex (s : SStd R X) : s.toStdSimplex.weights = s.weights := rfl

@[simp] lemma weights_ofStdSimplex (s : Convexity.StdSimplex R X) :
    (ofStdSimplex s).weights = s.weights := by
  ext x
  rfl

/-- `SStd R X` and `Convexity.StdSimplex R X` are in bijection, weights preserved. -/
noncomputable def equivStdSimplex : SStd R X ≃ Convexity.StdSimplex R X where
  toFun := toStdSimplex
  invFun := ofStdSimplex
  left_inv s := ext (by simp)
  right_inv s := by
    ext : 1
    simp

end Semiring

section OrderedRing

variable {R : Type*} [Ring R] [PartialOrder R] [IsOrderedRing R]
variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]

/-- Push a simplex point forward along a map of index types (this Mathlib's `stdSimplex.map`). -/
noncomputable def map (g : X → Y) (s : SStd R X) : SStd R Y := stdSimplex.map g s

lemma map_val_apply [DecidableEq Y] (g : X → Y) (s : SStd R X) (y : Y) :
    (map g s).1 y = ∑ x ∈ Finset.univ.filter (fun x => g x = y), s.1 x := by
  change (FunOnFinite.linearMap R R g s.1) y = _
  rw [FunOnFinite.linearMap_apply_apply]

@[simp] lemma weights_map (g : X → Y) (s : SStd R X) :
    (map g s).weights = s.weights.mapDomain g := by
  classical
  ext y
  rw [weights_apply, map_val_apply, Finsupp.mapDomain, Finsupp.sum_fintype _ _ (by simp),
    Finsupp.finsetSum_apply]
  simp [Finsupp.single_apply, Finset.sum_filter, weights_apply]

@[simp] lemma map_id (s : SStd R X) : map id s = s := stdSimplex.map_id_apply s

end OrderedRing

end SStd

end OAI

end StdSimplexCompat
end

section
-- module Solutions.OAIQ066_SO.FiniteType_AffineSimplex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.CategoryTheory AlgebraicTopology Limits Convexity
open scoped Simplicial
namespace AffineSimplex
open Set Topology
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι κ : Type} [Fintype ι] [Fintype κ]

def linear (v : ι → E) : (ι → ℝ) →ₗ[ℝ] E where
  toFun c := ∑ i, c i • v i
  map_add' a b := by simp [add_smul,Finset.sum_add_distrib]
  map_smul' r c := by simp [mul_smul,Finset.smul_sum]

def simplex (v : ι → E) : C(StdSimplex ℝ ι,E) :=
  ⟨fun s => linear v s.weights,(linear v).continuous_of_finiteDimensional.comp
    (StdSimplex.isEmbedding_toFun_comp_weights ℝ ι).continuous⟩

@[simp] lemma simplex_apply (v : ι → E) (s : StdSimplex ℝ ι) :
    simplex v s = ∑ i, s.weights i • v i := rfl

lemma simplex_mem_convex (v : ι → E) {C : Set E} (hC : Convex ℝ C)
    (hv : ∀ i, v i ∈ C) (s : StdSimplex ℝ ι) : simplex v s ∈ C := by
  exact hC.sum_mem (fun i _ => s.weights_nonneg i) s.total_of_fintype (fun i _ => hv i)

lemma simplex_mem_hull (v : ι → E) (s : StdSimplex ℝ ι) :
    simplex v s ∈ convexHull ℝ (range v) :=
  simplex_mem_convex v (convex_convexHull ℝ _) (fun i => subset_convexHull ℝ _ (mem_range_self i)) s

lemma simplex_map (v : κ → E) (f : ι → κ) (s : StdSimplex ℝ ι) :
    simplex v (StdSimplex.map f s) = simplex (v ∘ f) s := by
  change ∑ coord, (s.weights.mapDomain f) coord • v coord =
    ∑ coord, s.weights coord • v (f coord)
  rw [← Finsupp.sum_fintype (s.weights.mapDomain f)
    (fun coord coeff => coeff • v coord) (by simp),
    Finsupp.sum_mapDomain_index (by simp) (by simp [add_smul])]
  exact Finsupp.sum_fintype _ _ (by simp)

variable [DecidableEq ι]

@[simp] lemma simplex_vertex (v : ι → E) (i : ι) :
    simplex v (StdSimplex.single i) = v i := by
  simp [simplex_apply,Finsupp.single_apply]

end AffineSimplex

namespace ConvexSimplex
open Set Topology
abbrev Std (n : ℕ) := StdSimplex ℝ (Fin (n+1))

def affine {m n : ℕ} (v : Fin (m+1) → Std n) : C(Std m,Std n) := by
  refine ⟨fun point => {
    weights := ∑ vertex, point.weights vertex • (v vertex).weights
    nonneg := Finset.sum_nonneg (fun vertex _ =>
      smul_nonneg (point.weights_nonneg vertex) (v vertex).nonneg)
    total := ?_ }, ?_⟩
  · rw [Finsupp.sum_fintype _ _ (by simp)]
    simp only [Finsupp.coe_finsetSum,Finset.sum_apply,Finsupp.smul_apply,smul_eq_mul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum,StdSimplex.total_of_fintype,mul_one]
    exact point.total_of_fintype
  · apply (StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n+1))).continuous_iff.mpr
    change Continuous (fun point : Std m =>
      ((∑ vertex, point.weights vertex • (v vertex).weights : Fin (n+1) →₀ ℝ) : Fin (n+1) → ℝ))
    simp only [Finsupp.coe_finsetSum,Finsupp.coe_smul]
    fun_prop

@[simp] lemma affine_coe {m n : ℕ} (v : Fin (m+1) → Std n) (s : Std m) :
    (affine v s).weights = ∑ i, s.weights i • (v i).weights := rfl

@[simp] lemma affine_vertex {m n : ℕ} (v : Fin (m+1) → Std n) (i : Fin (m+1)) :
    affine v (StdSimplex.single i) = v i := by
  apply StdSimplex.ext
  simp [affine_coe,Finsupp.single_apply]

@[simp] lemma affine_id (n : ℕ) :
    affine (fun i : Fin (n+1) => StdSimplex.single i) = ContinuousMap.id (Std n) := by
  ext s : 1
  apply StdSimplex.ext
  ext coord
  simp [affine_coe]

lemma affine_map {k m n : ℕ} (v : Fin (m+1) → Std n) (f : Fin (k+1) → Fin (m+1))
    (s : Std k) : affine v (StdSimplex.map f s) = affine (v ∘ f) s := by
  apply StdSimplex.ext
  apply DFunLike.coe_injective
  simpa only [affine_coe,Finsupp.coe_finsetSum,Finsupp.coe_smul,
    AffineSimplex.simplex_apply,Function.comp_apply] using
    AffineSimplex.simplex_map (fun vertex => ((v vertex).weights : Fin (n+1) → ℝ)) f s

lemma affine_comp {k m n : ℕ} (v : Fin (m+1) → Std n) (w : Fin (k+1) → Std m) :
    (affine v).comp (affine w) = affine (affine v ∘ w) := by
  ext s : 1
  apply StdSimplex.ext
  change (affine v (affine w s)).weights = (affine (affine v ∘ w) s).weights
  simp only [affine_coe]
  ext j
  simp only [affine_coe,Finsupp.coe_finsetSum,Finset.sum_apply,Finsupp.smul_apply,
    smul_eq_mul,Function.comp_apply,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro l _
  ring

def center {n : ℕ} {m : ℕ} (v : Fin (m+1) → Std n) : Std n :=
  affine v StdSimplex.barycenter

lemma affine_center {k m n : ℕ} (v : Fin (m+1) → Std n) (w : Fin (k+1) → Std m) :
    affine v (center w) = center (affine v ∘ w) :=
  congrArg (fun f : C(Std k,Std n) => f StdSimplex.barycenter) (affine_comp v w)

@[simp] lemma center_coe {m n : ℕ} (v : Fin (m+1) → Std n) :
    (center v).weights = ((m+1:ℝ)⁻¹) • ∑ i, (v i).weights := by
  simp [center,StdSimplex.weights_barycenter_apply,Finset.smul_sum]

lemma stdMap_affine {m n : ℕ} (f : Fin (m+1) → Fin (n+1)) (s : Std m) :
    StdSimplex.map f s = affine (StdSimplex.single ∘ f) s := by
  rw [← affine_map,affine_id]
  rfl

end ConvexSimplex
namespace SingularChains
open Set Topology _root_.CategoryTheory AlgebraicTopology Limits
open scoped Simplicial unitInterval

abbrev Std (n : ℕ) := StdSimplex ℝ (Fin (n+1))
abbrev singular (X : Type) [TopologicalSpace X] := TopCat.toSSet.obj (TopCat.of X)
abbrev chains (X : Type) [TopologicalSpace X] : ChainComplex (ModuleCat ℤ) ℕ :=
  (singular X).chainComplex (ModuleCat.of ℤ ℤ)

variable {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

noncomputable def stdBridge (n : ℕ) : OAI.SStd ℝ (Fin (n+1)) ≃ₜ Std n :=
  { toEquiv := OAI.SStd.equivStdSimplex
    continuous_toFun := by
      apply (StdSimplex.isEmbedding_toFun_comp_weights ℝ _).continuous_iff.mpr
      exact continuous_pi fun k => (continuous_apply k).comp continuous_subtype_val
    continuous_invFun := by
      refine Continuous.subtype_mk ?_ _
      refine continuous_pi fun k => ?_
      exact StdSimplex.continuous_weights_apply ℝ k }

lemma stdBridge_map {n m : ℕ} (g : Fin (n+1) → Fin (m+1)) (x : OAI.SStd ℝ (Fin (n+1))) :
    stdBridge m (OAI.SStd.map g x) = StdSimplex.map g (stdBridge n x) := by
  apply StdSimplex.ext
  ext k
  simp [stdBridge, OAI.SStd.equivStdSimplex, OAI.SStd.toStdSimplex,
    OAI.SStd.weights_map, StdSimplex.weights_map]

def br (n : ℕ) : C(OAI.SStd ℝ (Fin (n+1)),Std n) := ⟨stdBridge n,(stdBridge n).continuous⟩
def brs (n : ℕ) : C(Std n,OAI.SStd ℝ (Fin (n+1))) := ⟨(stdBridge n).symm,(stdBridge n).symm.continuous⟩

lemma br_brs (n : ℕ) : (br n).comp (brs n) = ContinuousMap.id _ := by
  ext x; simp [br, brs]

lemma brs_br (n : ℕ) : (brs n).comp (br n) = ContinuousMap.id _ := by
  ext x; simp [br, brs]

noncomputable def simplex {n : ℕ} (f : C(Std n,X)) : (singular X) _⦋n⦌ :=
  (TopCat.toSSetObjEquiv (TopCat.of X) _).symm (f.comp (br n))

noncomputable def unsimplex {n : ℕ} (f : (singular X) _⦋n⦌) : C(Std n,X) :=
  (TopCat.toSSetObjEquiv (TopCat.of X) _ f).comp (brs n)

@[simp] lemma simplex_unsimplex {n : ℕ} (f : (singular X) _⦋n⦌) : simplex (unsimplex f) = f := by
  simp only [simplex, unsimplex, ContinuousMap.comp_assoc, brs_br, ContinuousMap.comp_id]
  exact Equiv.symm_apply_apply _ _
@[simp] lemma unsimplex_simplex {n : ℕ} (f : C(Std n,X)) : unsimplex (simplex f) = f := by
  simp only [simplex, unsimplex, Equiv.apply_symm_apply, ContinuousMap.comp_assoc, br_brs,
    ContinuousMap.comp_id]

def face {n : ℕ} (i : Fin (n+2)) : C(Std n,Std (n+1)) :=
  ⟨StdSimplex.map i.succAbove,StdSimplex.continuous_map ℝ _⟩

lemma simplex_face {n : ℕ} (f : C(Std (n+1),X)) (i : Fin (n+2)) :
    (singular X).δ i (simplex f) = simplex (f.comp (face i)) := by
  apply (TopCat.toSSetObjEquiv (TopCat.of X) _).injective
  ext x
  change f (br (n+1) (OAI.SStd.map i.succAbove x)) = f (face i (br n x))
  exact congrArg f (stdBridge_map i.succAbove x)

lemma simplex_map {n : ℕ} (f : C(Std n,X)) (g : C(X,Y)) :
    (TopCat.toSSet.map (TopCat.ofHom g)).app _ (simplex f) = simplex (g.comp f) := by
  apply (TopCat.toSSetObjEquiv (TopCat.of Y) _).injective
  ext x
  rfl

def generator {n : ℕ} (f : C(Std n,X)) : ModuleCat.of ℤ ℤ ⟶ (chains X).X n :=
  (singular X).ιChainComplex (simplex f)

@[reassoc] lemma generator_boundary {n : ℕ} (f : C(Std (n+1),X)) :
    generator f ≫ (chains X).d (n+1) n =
      ∑ i : Fin (n+2), (-1:ℤ)^i.val • generator (f.comp (face i)) := by
  simp only [generator,SSet.ιChainComplex_d,simplex_face]

def map (f : C(X,Y)) : chains X ⟶ chains Y :=
  SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f)) (ModuleCat.of ℤ ℤ)

@[reassoc (attr := simp)] lemma generator_map {n : ℕ} (f : C(Std n,X)) (g : C(X,Y)) :
    generator f ≫ (map g).f n = generator (g.comp f) := by
  simp only [generator,map,SSet.ι_chainComplexMap_f,simplex_map]

def desc {n : ℕ} {A : ModuleCat ℤ} (b : C(Std n,X) → (ModuleCat.of ℤ ℤ ⟶ A)) :
    (chains X).X n ⟶ A := Sigma.desc (fun s => b (unsimplex s))

@[reassoc (attr := simp)] lemma generator_desc {n : ℕ} {A : ModuleCat ℤ}
    (b : C(Std n,X) → (ModuleCat.of ℤ ℤ ⟶ A)) (f : C(Std n,X)) :
    generator f ≫ desc b = b f := by
  exact (Limits.Sigma.ι_desc _ _).trans (congrArg b (unsimplex_simplex f))

lemma hom_ext {n : ℕ} {A : ModuleCat ℤ} {f g : (chains X).X n ⟶ A}
    (h : ∀ s : C(Std n,X), generator s ≫ f = generator s ≫ g) : f = g := by
  apply SSet.chainComplex_hom_ext
  intro s
  simpa only [generator,simplex_unsimplex] using h (unsimplex s)

@[simp] lemma map_id : map (ContinuousMap.id X) = 𝟙 (chains X) := by
  ext n : 1
  apply hom_ext
  intro s
  simp only [HomologicalComplex.id_f,Category.comp_id,generator_map,ContinuousMap.id_comp]

end SingularChains

namespace AffineRealization
section
open _root_.CategoryTheory AlgebraicTopology Limits ConvexSimplex
open scoped Simplicial

def singular (n : ℕ) : AffineChains.vertices (Std n) ⟶ SingularChains.singular (Std n) where
  app _ := ↾fun v => SingularChains.simplex (affine v)
  naturality k m f := by
    ext v
    apply (TopCat.toSSetObjEquiv (TopCat.of (Std n)) m).injective
    ext s : 1
    change affine (v ∘ f.unop.toOrderHom) (SingularChains.br _ s) =
      affine v (SingularChains.br _ (OAI.SStd.map f.unop.toOrderHom s))
    exact (affine_map _ _ _).symm.trans (congrArg (affine v) (SingularChains.stdBridge_map _ s).symm)

def realize (n : ℕ) : AffineChains.chains (Std n) ⟶ SingularChains.chains (Std n) :=
  SSet.chainComplexMap (singular n) (ModuleCat.of ℤ ℤ)

@[reassoc (attr := simp)] lemma generator_realize {m n : ℕ} (v : Fin (m+1) → Std n) :
    AffineChains.generator v ≫ (realize n).f m = SingularChains.generator (affine v) := by
  exact SSet.ι_chainComplexMap_f (AffineChains.vertices (Std n))
    (SingularChains.singular (Std n)) (singular n) (ModuleCat.of ℤ ℤ) v

@[reassoc] lemma realize_affine {m n k : ℕ} (v : Fin (m+1) → Std n) :
    (AffineChains.map (affine v)).f k ≫ (realize n).f k =
      (realize m).f k ≫ (SingularChains.map (affine v)).f k := by
  apply AffineChains.hom_ext
  intro w
  simp only [AffineChains.generator_map_assoc,generator_realize,
    generator_realize_assoc,SingularChains.generator_map,affine_comp]

def basis (n : ℕ) : Fin (n+1) → Std n := StdSimplex.single

@[simp] lemma basis_affine (n : ℕ) : affine (basis n) = ContinuousMap.id (Std n) :=
  affine_id n

lemma basis_map_affine {m n : ℕ} (v : Fin (m+1) → Std n) :
    affine v ∘ basis m = v := by
  funext j
  exact affine_vertex v j

end

open _root_.CategoryTheory AlgebraicTopology Limits ConvexSimplex
lemma face_affine {n : ℕ} (i : Fin (n+2)) :
    SingularChains.face i = affine (basis (n+1) ∘ i.succAbove) := by
  ext s : 1
  exact stdMap_affine _ s

@[reassoc] lemma realize_face {n k : ℕ} (i : Fin (n+2)) :
    (AffineChains.map (SingularChains.face i)).f k ≫ (realize (n+1)).f k =
      (realize n).f k ≫ (SingularChains.map (SingularChains.face i)).f k := by
  rw [face_affine]
  exact realize_affine _

end AffineRealization

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SingularSubdivision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.CategoryTheory AlgebraicTopology Limits
open scoped Simplicial
namespace SingularSubdivision
section
open _root_.CategoryTheory AlgebraicTopology Limits ConvexSimplex AffineRealization

abbrev sd (n : ℕ) := AffineChains.subdiv (@center n) n

def simplexChain (n : ℕ) : ModuleCat.of ℤ ℤ ⟶ (AffineChains.chains (Std n)).X n :=
  AffineChains.generator (basis n) ≫ sd n

def prismChain (n : ℕ) : ModuleCat.of ℤ ℤ ⟶ (AffineChains.chains (Std n)).X (n+1) :=
  AffineChains.generator (basis n) ≫ AffineChains.prism (@center n) n

@[reassoc] lemma simplexChain_affine {m n : ℕ} (v : Fin (m+1) → Std n) :
    simplexChain m ≫ (AffineChains.map (affine v)).f m =
      AffineChains.generator v ≫ AffineChains.subdiv (@center n) m := by
  rw [simplexChain,Category.assoc,AffineChains.subdiv_map (@center m) (@center n)
    (affine v) (fun w => affine_center v w),← Category.assoc,
    AffineChains.generator_map,basis_map_affine]

@[reassoc] lemma prismChain_affine {m n : ℕ} (v : Fin (m+1) → Std n) :
    prismChain m ≫ (AffineChains.map (affine v)).f (m+1) =
      AffineChains.generator v ≫ AffineChains.prism (@center n) m := by
  rw [prismChain,Category.assoc,AffineChains.prism_map (@center m) (@center n)
    (affine v) (fun w => affine_center v w),← Category.assoc,
    AffineChains.generator_map,basis_map_affine]

@[reassoc] lemma simplexChain_face {n : ℕ} (i : Fin (n+2)) :
    simplexChain n ≫ (AffineChains.map (SingularChains.face i)).f n =
      AffineChains.generator (basis (n+1) ∘ i.succAbove) ≫ AffineChains.subdiv (@center (n+1)) n := by
  rw [face_affine]
  exact simplexChain_affine _

@[reassoc] lemma prismChain_face {n : ℕ} (i : Fin (n+2)) :
    prismChain n ≫ (AffineChains.map (SingularChains.face i)).f (n+1) =
      AffineChains.generator (basis (n+1) ∘ i.succAbove) ≫ AffineChains.prism (@center (n+1)) n := by
  rw [face_affine]
  exact prismChain_affine _

@[reassoc] lemma simplexChain_boundary (n : ℕ) :
    simplexChain (n+1) ≫ (AffineChains.chains (Std (n+1))).d (n+1) n =
      ∑ i : Fin (n+2), (-1:ℤ)^i.val •
        (simplexChain n ≫ (AffineChains.map (SingularChains.face i)).f n) := by
  rw [simplexChain,Category.assoc,AffineChains.subdiv_comm,
    ← Category.assoc,AffineChains.generator_boundary]
  simp only [Preadditive.sum_comp,Preadditive.zsmul_comp,simplexChain_face]

@[reassoc] lemma prismChain_boundary (n : ℕ) :
    prismChain (n+1) ≫ (AffineChains.chains (Std (n+1))).d (n+2) (n+1) =
      AffineChains.generator (basis (n+1)) - simplexChain (n+1) -
        ∑ i : Fin (n+2), (-1:ℤ)^i.val •
          (prismChain n ≫ (AffineChains.map (SingularChains.face i)).f (n+1)) := by
  rw [prismChain,Category.assoc,AffineChains.prism_boundary]
  simp only [Preadditive.comp_sub,Category.comp_id]
  rw [← Category.assoc,AffineChains.generator_boundary]
  simp only [Preadditive.sum_comp,Preadditive.zsmul_comp,prismChain_face]
  rfl

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

def subdiv (n : ℕ) : (SingularChains.chains X).X n ⟶ (SingularChains.chains X).X n :=
  SingularChains.desc (fun f => simplexChain n ≫ (realize n).f n ≫ (SingularChains.map f).f n)

@[reassoc (attr := simp)] lemma generator_subdiv {n : ℕ} (f : C(Std n,X)) :
    SingularChains.generator f ≫ subdiv n =
      simplexChain n ≫ (realize n).f n ≫ (SingularChains.map f).f n :=
  SingularChains.generator_desc _ _

@[reassoc] lemma generator_affine_subdiv {m n : ℕ} (v : Fin (m+1) → Std n) :
    SingularChains.generator (affine v) ≫ subdiv m =
      AffineChains.generator v ≫ AffineChains.subdiv (@center n) m ≫ (realize n).f m := by
  rw [generator_subdiv,← realize_affine,← Category.assoc,simplexChain_affine,Category.assoc]

end

open _root_.CategoryTheory AlgebraicTopology Limits ConvexSimplex AffineRealization
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

def prism (n : ℕ) : (SingularChains.chains X).X n ⟶ (SingularChains.chains X).X (n+1) :=
  SingularChains.desc (fun f => prismChain n ≫ (realize n).f (n+1) ≫ (SingularChains.map f).f (n+1))

@[reassoc (attr := simp)] lemma generator_prism {n : ℕ} (f : C(Std n,X)) :
    SingularChains.generator f ≫ prism n =
      prismChain n ≫ (realize n).f (n+1) ≫ (SingularChains.map f).f (n+1) :=
  SingularChains.generator_desc _ _

@[simp] lemma subdiv_zero : subdiv (X := X) 0 = 𝟙 _ := by
  apply SingularChains.hom_ext
  intro f
  simp only [generator_subdiv,simplexChain,sd,AffineChains.subdiv_zero,Category.comp_id,
    generator_realize_assoc,basis_affine,SingularChains.generator_map,ContinuousMap.comp_id]

@[simp] lemma prism_zero : prism (X := X) 0 = 0 := by
  apply SingularChains.hom_ext
  intro f
  simp [generator_prism,prismChain]

end SingularSubdivision

namespace AffineSupport
open _root_.CategoryTheory AlgebraicTopology Limits
variable {V W : Type} {n m : ℕ}

abbrev gen (v : Fin (n+1) → V) : (AffineChains.chains V).X n := AffineChains.generator v 1

def span (P : (Fin (n+1) → V) → Prop) : Submodule ℤ ((AffineChains.chains V).X n) :=
  Submodule.span ℤ {x | ∃ v, P v ∧ x = gen v}

lemma gen_mem {P : (Fin (n+1) → V) → Prop} (v : Fin (n+1) → V) (hv : P v) : gen v ∈ span P :=
  Submodule.subset_span ⟨v,hv,rfl⟩

lemma span_mono {P Q : (Fin (n+1) → V) → Prop} (h : ∀ v, P v → Q v) : span P ≤ span Q := by
  apply Submodule.span_le.mpr
  rintro _ ⟨v,hv,rfl⟩
  exact gen_mem v (h v hv)

lemma map_mem {P : (Fin (n+1) → V) → Prop}
    {A : ModuleCat ℤ} {S : Submodule ℤ A}
    (f : (AffineChains.chains V).X n ⟶ A)
    (hf : ∀ v, P v → f (gen v) ∈ S) {c : (AffineChains.chains V).X n} (hc : c ∈ span P) : f c ∈ S := by
  induction hc using Submodule.span_induction with
  | mem x hx => obtain ⟨v,hv,rfl⟩ := hx; exact hf v hv
  | zero => simp
  | add x y hx hy ihx ihy => simpa using S.add_mem ihx ihy
  | smul a x hx ih => simpa using S.smul_mem a ih

lemma induction_on (S : Submodule ℤ ((AffineChains.chains V).X n))
    (hS : ∀ v : Fin (n+1) → V, gen v ∈ S) (c : (AffineChains.chains V).X n) : c ∈ S := by
  let : Module ℤ (((AffineChains.chains V).X n) ⧸ S) := Submodule.Quotient.module S
  let q : (AffineChains.chains V).X n ⟶ ModuleCat.of ℤ (((AffineChains.chains V).X n) ⧸ S) :=
    ModuleCat.ofHom S.mkQ
  have hq : q = 0 := by
    apply AffineChains.hom_ext
    intro v
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    change S.mkQ (gen v) = 0
    change gen v ∈ LinearMap.ker S.mkQ
    rw [Submodule.ker_mkQ]
    exact hS v
  have hc := congrArg (fun h => h c) hq
  change S.mkQ c = 0 at hc
  have hc' : c ∈ LinearMap.ker S.mkQ := hc
  simpa only [Submodule.ker_mkQ] using hc'

@[simp] lemma map_gen (v : Fin (n+1) → V) (f : V → W) :
    (AffineChains.map f).f n (gen v) = gen (f ∘ v) := by
  exact congrArg (fun h : ModuleCat.of ℤ ℤ ⟶ (AffineChains.chains W).X n => h 1)
    (AffineChains.generator_map v f)

@[simp] lemma cone_gen (v : Fin (n+1) → V) (x : V) :
    AffineChains.cone x n (gen v) = gen (Fin.cons x v) := by
  exact congrArg (fun h : ModuleCat.of ℤ ℤ ⟶ (AffineChains.chains V).X (n+1) => h 1)
    (AffineChains.generator_cone v x)

lemma boundary_gen (v : Fin (n+2) → V) :
    (AffineChains.chains V).d (n+1) n (gen v) =
      ∑ i : Fin (n+2), (-1:ℤ)^i.val • gen (v ∘ i.succAbove) := by
  have h := congrArg (fun h : ModuleCat.of ℤ ℤ ⟶ (AffineChains.chains V).X n => h 1)
    (AffineChains.generator_boundary v)
  simpa using h

lemma subdiv_gen (b : ∀ {n : ℕ}, (Fin (n+1) → V) → V) (v : Fin (n+2) → V) :
    AffineChains.subdiv b (n+1) (gen v) =
      ∑ i : Fin (n+2), (-1:ℤ)^i.val •
        AffineChains.cone (b v) n (AffineChains.subdiv b n (gen (v ∘ i.succAbove))) := by
  have h := congrArg (fun h : ModuleCat.of ℤ ℤ ⟶ (AffineChains.chains V).X (n+1) => h 1)
    (AffineChains.generator_subdiv_succ b v)
  change AffineChains.subdiv b (n+1) (gen v) =
    AffineChains.cone (b v) n (AffineChains.subdiv b n ((AffineChains.chains V).d (n+1) n (gen v))) at h
  rw [h,boundary_gen]
  simp

end AffineSupport

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SingularSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.CategoryTheory AlgebraicTopology Limits
open scoped Simplicial
namespace SingularSupport
open _root_.CategoryTheory AlgebraicTopology Limits SingularChains
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {n m : ℕ}

abbrev gen (f : C(Std n,X)) : (chains X).X n := generator f 1

@[simp] lemma map_gen (f : C(Std n,X)) (g : C(X,Y)) : (map g).f n (gen f) = gen (g.comp f) :=
  congrArg (fun h : ModuleCat.of ℤ ℤ ⟶ (chains Y).X n => h 1) (generator_map f g)

end SingularSupport

namespace AffineMesh
open Set Topology
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def center {n : ℕ} (v : Fin (n+1) → E) : E := ((n+1:ℝ)⁻¹) • ∑ i, v i

def ratio (n : ℕ) : ℝ := (n:ℝ)/(n+1)

lemma ratio_nonneg (n : ℕ) : 0 ≤ ratio n := by unfold ratio; positivity
lemma ratio_lt_one (n : ℕ) : ratio n < 1 := by
  unfold ratio
  exact (div_lt_one (by positivity)).mpr (by linarith)
lemma ratio_mono {m n : ℕ} (h : m ≤ n) : ratio m ≤ ratio n := by
  unfold ratio
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have : (m:ℝ) ≤ n := Nat.cast_le.mpr h
  nlinarith

lemma center_mem_hull {n : ℕ} (v : Fin (n+1) → E) : center v ∈ convexHull ℝ (range v) := by
  have he : center v = AffineSimplex.simplex v Convexity.StdSimplex.barycenter := by
    simp [center,AffineSimplex.simplex_apply,
      Convexity.StdSimplex.weights_barycenter_apply,Finset.smul_sum]
  rw [he]
  exact AffineSimplex.simplex_mem_hull _ _

lemma center_sub {n : ℕ} (v : Fin (n+1) → E) (i : Fin (n+1)) :
    center v - v i = ((n+1:ℝ)⁻¹) • ∑ j, (v j - v i) := by
  rw [Finset.sum_sub_distrib,smul_sub]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℝ,smul_smul]
  have h : ((n+1:ℝ)⁻¹) * (n+1) = 1 := inv_mul_cancel₀ (by positivity)
  simp only [Nat.cast_add,Nat.cast_one,h,one_smul]
  rfl

lemma center_dist_vertex {n : ℕ} (v : Fin (n+1) → E) {D : ℝ} (_hD : 0 ≤ D)
    (hv : ∀ i j, dist (v i) (v j) ≤ D) (i : Fin (n+1)) :
    dist (center v) (v i) ≤ ratio n * D := by
  rw [dist_eq_norm,center_sub,norm_smul,Real.norm_of_nonneg (by positivity)]
  have hs : ∑ j : Fin (n+1), ‖v j - v i‖ ≤ (n:ℝ) * D := by
    classical
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    simp only [sub_self,norm_zero,add_zero]
    calc
      _ ≤ ∑ j ∈ Finset.univ.erase i, D := Finset.sum_le_sum (fun j _ => by
        simpa only [dist_eq_norm] using hv j i)
      _ = (n:ℝ) * D := by simp
  calc
    _ ≤ ((n+1:ℝ)⁻¹) * (∑ j, ‖v j - v i‖) :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ ((n+1:ℝ)⁻¹) * ((n:ℝ) * D) := mul_le_mul_of_nonneg_left hs (by positivity)
    _ = ratio n * D := by unfold ratio; ring

lemma center_dist_hull {n : ℕ} (v : Fin (n+1) → E) {D : ℝ} (hD : 0 ≤ D)
    (hv : ∀ i j, dist (v i) (v j) ≤ D) {p : E} (hp : p ∈ convexHull ℝ (range v)) :
    dist (center v) p ≤ ratio n * D := by
  have hc : convexHull ℝ (range v) ⊆ Metric.closedBall (center v) (ratio n * D) := by
    apply convexHull_min _ (convex_closedBall _ _)
    rintro _ ⟨i,rfl⟩
    rw [Metric.mem_closedBall,dist_comm]
    exact center_dist_vertex v hD hv i
  simpa only [Metric.mem_closedBall,dist_comm] using hc hp

lemma hull_dist {n : ℕ} (v : Fin (n+1) → E) {D : ℝ} (_hD : 0 ≤ D)
    (hv : ∀ i j, dist (v i) (v j) ≤ D) {p q : E}
    (hp : p ∈ convexHull ℝ (range v)) (hq : q ∈ convexHull ℝ (range v)) : dist p q ≤ D := by
  have hi : ∀ i, convexHull ℝ (range v) ⊆ Metric.closedBall (v i) D := by
    intro i
    apply convexHull_min _ (convex_closedBall _ _)
    rintro _ ⟨j,rfl⟩
    exact hv j i
  have hc : convexHull ℝ (range v) ⊆ Metric.closedBall q D := by
    apply convexHull_min _ (convex_closedBall _ _)
    rintro _ ⟨i,rfl⟩
    simpa only [Metric.mem_closedBall,dist_comm] using hi i hq
  exact hc hp

end AffineMesh

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SingularSphereCycle
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

namespace BasedSimplex
open Set Topology Metric
open scoped unitInterval
universe u
variable {X : Type u} [TopologicalSpace X] {n : ℕ} {x : X}
abbrev Std (n : ℕ) := Convexity.StdSimplex ℝ (Fin (n+1))
def Boundary (n : ℕ) : Set (Std n) := {s | ∃ i, s.weights i = 0}

end BasedSimplex

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SequentialLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Pointwise
open scoped commutatorElement
namespace SequentialLimit

structure End (A : Type*) where
  toFun : A → A

instance endFunLike (A : Type*) : FunLike (End A) A A where
  coe := End.toFun
  coe_injective := by rintro ⟨f⟩ ⟨g⟩ h; cases h; rfl

variable {X Y : Type*}

def transition (s : X → X) (i j : ℕ) (_ : i ≤ j) : End X := ⟨s^[j - i]⟩

@[simp] lemma transition_apply (s : X → X) (i j : ℕ) (h : i ≤ j) (x : X) :
    transition s i j h x = s^[j-i] x := rfl

instance directed (s : X → X) :
    DirectedSystem (fun _ : ℕ => X) (transition s · · ·) where
  map_self {i} x := by simp only [transition_apply, Nat.sub_self, Function.iterate_zero, id_eq]
  map_map {k j i} hij hjk x := by
    simp only [transition_apply]
    rw [← Function.iterate_add_apply]
    congr 1
    omega

abbrev Limit (s : X → X) := DirectLimit (fun _ : ℕ => X) (transition s)

abbrev of (s : X → X) (i : ℕ) (x : X) : Limit s := Quotient.mk _ ⟨i, x⟩

lemma of_advance (s : X → X) (i j : ℕ) (h : i ≤ j) (x : X) :
    of s i x = of s j (s^[j-i] x) := DirectLimit.eq_of_le (f := transition s) ⟨i,x⟩ j h

@[simp] lemma of_succ (s : X → X) (i : ℕ) (x : X) :
    of s (i + 1) (s x) = of s i x := by
  simp only [of_advance s i (i+1) (Nat.le_succ i) x, Nat.add_sub_cancel_left,
    Function.iterate_one]

lemma exists_rep (s : X → X) (x : Limit s) : ∃ i y, x = of s i y :=
  DirectLimit.exists_eq_mk _ x

@[elab_as_elim] lemma induction {s : X → X} {P : Limit s → Prop}
    (h : ∀ i x, P (of s i x)) (x : Limit s) : P x := DirectLimit.induction _ h x

lemma iterate_compat (s : X → X) (t : Y → Y) (f : X → Y)
    (hf : ∀ x, t (f x) = f (s x)) (n : ℕ) (x : X) :
    t^[n] (f x) = f (s^[n] x) := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [Function.iterate_succ_apply', ih] using hf (s^[n] x)

def map (s : X → X) (t : Y → Y) (f : X → Y)
    (hf : ∀ x, t (f x) = f (s x)) : Limit s → Limit t :=
  DirectLimit.map _ _ (fun _ => f) (fun _ _ _ x => iterate_compat s t f hf _ x)

@[simp] lemma map_of (s : X → X) (t : Y → Y) (f : X → Y)
    (hf : ∀ x, t (f x) = f (s x)) (i : ℕ) (x : X) :
    map s t f hf (of s i x) = of t i (f x) := rfl

def shift (s : X → X) : Equiv.Perm (Limit s) where
  toFun := DirectLimit.lift _ (fun i x => of s (i+1) x) (by
    intro i j h x
    simpa only [Nat.add_sub_add_right, transition_apply] using
      of_advance s (i+1) (j+1) (Nat.succ_le_succ h) x)
  invFun := map s s s (fun _ => rfl)
  left_inv := by
    intro x
    induction x using SequentialLimit.induction with | h i x =>
      exact of_succ s i x
  right_inv := by
    intro x
    induction x using SequentialLimit.induction with | h i x =>
      exact of_succ s i x

@[simp] lemma shift_of (s : X → X) (i : ℕ) (x : X) :
    shift s (of s i x) = of s (i+1) x := rfl

@[simp] lemma shift_symm_of (s : X → X) (i : ℕ) (x : X) :
    (shift s).symm (of s i x) = of s i (s x) := rfl

lemma pair_rep (s : X → X) (t : Y → Y) (x : Limit s) (y : Limit t) :
    ∃ (i : ℕ) (a : X) (b : Y), x = of s i a ∧ y = of t i b := by
  obtain ⟨i,a,rfl⟩ := exists_rep s x
  obtain ⟨j,b,rfl⟩ := exists_rep t y
  exact ⟨max i j, s^[max i j-i] a, t^[max i j-j] b,
    of_advance s _ _ (le_max_left _ _) _, of_advance t _ _ (le_max_right _ _) _⟩

end SequentialLimit

namespace SequentialAction

open SequentialLimit

variable {U X : Type*} [Group U] [MulAction U X]
variable (f : U →* U) (s : X → X) (heq : ∀ g x, s (g • x) = f g • s x)

def transitionHom (i j : ℕ) (h : i ≤ j) : U →* U where
  toFun := transition f i j h
  map_one' := by
    change (f : U → U)^[j-i] 1 = 1
    generalize j-i = n
    induction n with
    | zero => rfl
    | succ n ih => simp only [Function.iterate_succ_apply', ih, map_one]
  map_mul' x y := by
    change (f : U → U)^[j-i] (x*y) = (f : U → U)^[j-i] x * (f : U → U)^[j-i] y
    generalize j-i = n
    induction n with
    | zero => rfl
    | succ n ih => simp only [Function.iterate_succ_apply', ih, map_mul]

instance homDirected : DirectedSystem (fun _ : ℕ => U) (transitionHom f · · ·) :=
  SequentialLimit.directed f

instance limitGroup : Group (Limit f) :=
  inferInstanceAs (Group (DirectLimit (fun _ : ℕ => U) (transitionHom f)))

def ofGroup (i : ℕ) : U →* Limit f where
  toFun := of f i
  map_one' := (DirectLimit.one_def (f := transitionHom f) i).symm
  map_mul' x y := (DirectLimit.mul_def (G := fun _ : ℕ => U) (f := transitionHom f) i x y).symm

include heq in
lemma iterate_equivariant (n : ℕ) (g : U) (x : X) :
    s^[n] (g • x) = (f : U → U)^[n] g • s^[n] x := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply', ih, heq]

def act : Limit f → Limit s → Limit s :=
  DirectLimit.map₂ (transition f) (transition s) (transition s)
    (fun _ => (· • ·)) (by
      intro i j _ g x
      simpa only [transition_apply] using iterate_equivariant f s heq (j-i) g x)

@[simp] lemma act_of (i : ℕ) (g : U) (x : X) :
    act f s heq (of f i g) (of s i x) = of s i (g • x) :=
  DirectLimit.map₂_def ..

@[instance_reducible] def limitAction : MulAction (Limit f) (Limit s) where
  smul := act f s heq
  one_smul x := by
    induction x using SequentialLimit.induction with | h i x =>
      change act f s heq 1 (of s i x) = _
      have hone : (1 : Limit f) = of f i 1 := DirectLimit.one_def (f := transitionHom f) i
      rw [hone, act_of, one_smul]
  mul_smul g h x := by
    obtain ⟨i, g, h, rfl, rfl⟩ := DirectLimit.exists_eq_mk₂ (transition f) g h
    obtain ⟨j, x, rfl⟩ := exists_rep s x
    let k := max i j
    change act f s heq (of f i g * of f i h) (of s j x) =
      act f s heq (of f i g) (act f s heq (of f i h) (of s j x))
    rw [of_advance f i k (le_max_left _ _) g, of_advance f i k (le_max_left _ _) h,
      of_advance s j k (le_max_right _ _) x]
    have hmul (g h : U) : of f k g * of f k h = of f k (g*h) :=
      DirectLimit.mul_def (G := fun _ : ℕ => U) (f := transitionHom f) k g h
    rw [hmul, act_of, act_of, act_of, mul_smul]

@[simp] lemma of_smul (i : ℕ) (g : U) (x : X) :
    letI := limitAction f s heq
    of f i g • of s i x = of s i (g • x) := act_of ..

@[simp] lemma of_mul (i : ℕ) (g h : U) :
    of f i (g*h) = of f i g * of f i h := (ofGroup f i).map_mul g h

@[simp] lemma of_one (i : ℕ) : of f i 1 = 1 := (ofGroup f i).map_one

def shiftGroup : MulAut (Limit f) where
  toEquiv := shift f
  map_mul' g h := by
    obtain ⟨i,g,h,rfl,rfl⟩ := DirectLimit.exists_eq_mk₂ (transition f) g h
    change shift f (of f i g * of f i h) = shift f (of f i g) * shift f (of f i h)
    rw [← of_mul]
    change of f (i+1) (g*h) = of f (i+1) g * of f (i+1) h
    exact of_mul f _ _ _

@[simp] lemma shiftGroup_of (i : ℕ) (g : U) :
    shiftGroup f (of f i g) = of f (i+1) g := rfl

end SequentialAction

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_AscendingHNN
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.CategoryTheory CategoryTheory.Limits
open _root_.CategoryTheory MonoidalCategory _root_.Representation TensorProduct
open _root_.CategoryTheory
namespace AscendingHNN
section

variable {U : Type*} [Group U] (f : U →* U) (hf : Function.Injective f)

def associatedEquiv : (⊤ : Subgroup U) ≃* f.range :=
  (Subgroup.topEquiv).trans (MonoidHom.ofInjective hf)

abbrev Torus := HNNExtension U ⊤ f.range (associatedEquiv f hf)

def embed : U →* Torus f hf := HNNExtension.of

def stable : Torus f hf := HNNExtension.t⁻¹

lemma embed_injective : Function.Injective (embed f hf) := HNNExtension.of_injective (associatedEquiv f hf)

lemma embed_mul_stable (u : U) :
    embed f hf u * stable f hf = stable f hf * embed f hf (f u) := by
  exact HNNExtension.of_mul_inv_t (⟨u,Subgroup.mem_top u⟩ : (⊤ : Subgroup U))

def heightHom : Torus f hf →* Multiplicative ℤ :=
  HNNExtension.lift 1 (Multiplicative.ofAdd (-1)) (by intro a; simp)

def height (j : Torus f hf) : ℤ := Multiplicative.toAdd (heightHom f hf j)

@[simp] lemma height_mul (j k : Torus f hf) :
    height f hf (j*k) = height f hf j + height f hf k := by
  simp [height]

@[simp] lemma height_embed (u : U) : height f hf (embed f hf u) = 0 := by
  simp [height,heightHom,embed]

@[simp] lemma height_stable : height f hf (stable f hf) = 1 := by
  simp [height,heightHom,stable]

@[simp] lemma height_inv (j : Torus f hf) : height f hf j⁻¹ = -height f hf j := by
  simp [height]

abbrev Vertex := Torus f hf ⧸ (embed f hf).range

def parent : Vertex f hf → Vertex f hf :=
  Quotient.map' (fun j => j * stable f hf) (by
    intro a b h
    apply QuotientGroup.leftRel_apply.mpr
    obtain ⟨u,hu⟩ := QuotientGroup.leftRel_apply.mp h
    refine ⟨f u,?_⟩
    have hc : (stable f hf)⁻¹ * embed f hf u * stable f hf = embed f hf (f u) := by
      rw [mul_assoc,embed_mul_stable]
      group
    rw [← hc,hu]
    group)

@[simp] lemma parent_mk (j : Torus f hf) :
    parent f hf (QuotientGroup.mk j) = QuotientGroup.mk (j * stable f hf) := rfl

def vertexHeight : Vertex f hf → ℤ :=
  Quotient.lift (height f hf) (by
    intro a b h
    obtain ⟨u,hu⟩ := QuotientGroup.leftRel_apply.mp h
    have hh : height f hf (a⁻¹*b) = 0 := by rw [← hu,height_embed]
    simp only [height_mul,height_inv] at hh
    omega)

@[simp] lemma vertexHeight_mk (j : Torus f hf) :
    vertexHeight f hf (QuotientGroup.mk j) = height f hf j := rfl

end

open _root_.CategoryTheory

end AscendingHNN

namespace AscendingHNN
section
open _root_.CategoryTheory
variable {U P : Type} [Group U] [Group P] [Group.FG P]
variable (a : U →* P) (b : P →* U) (hf : Function.Injective (b.comp a))

abbrev baseEquiv : U ≃* (embed (b.comp a) hf).range :=
  MonoidHom.ofInjective (embed_injective (b.comp a) hf)

abbrev baseShift : (embed (b.comp a) hf).range →* (embed (b.comp a) hf).range :=
  ((baseEquiv a b hf).toMonoidHom.comp (b.comp a)).comp (baseEquiv a b hf).symm.toMonoidHom

end

variable {U V : Type*} [Group U] [Group V]
variable (f : U →* U) (hf : Function.Injective f)

@[ext] lemma hom_ext {i j : Torus f hf →* V}
    (hi : ∀ u, i (embed f hf u)=j (embed f hf u))
    (ht : i (stable f hf)=j (stable f hf)) : i=j := by
  apply HNNExtension.hom_ext
  · ext u
    exact hi u
  · apply inv_injective
    exact (map_inv i _).symm.trans (ht.trans (map_inv j _))

variable (i : U →* V) (t : V) (ht : ∀ u, i u*t=t*i (f u))

include ht in
lemma inv_conjugation (u : U) : t⁻¹ * i u = i (f u) * t⁻¹ := by
  calc
    _ = t⁻¹*(i u*t)*t⁻¹ := by group
    _ = _ := by rw [ht]; group

def evaluation : Torus f hf →* V :=
  HNNExtension.lift i t⁻¹ (fun u => inv_conjugation f i t ht u)

@[simp] lemma evaluation_embed (u : U) : evaluation f hf i t ht (embed f hf u)=i u :=
  HNNExtension.lift_of _ _ _ u

@[simp] lemma evaluation_stable : evaluation f hf i t ht (stable f hf)=t := by
  change (HNNExtension.lift i t⁻¹ (fun u : (⊤ : Subgroup U) => inv_conjugation f i t ht u))
    HNNExtension.t⁻¹ = t
  rw [map_inv]
  exact (congrArg Inv.inv (HNNExtension.lift_t _ _ _)).trans (inv_inv t)

end AscendingHNN

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_AscendingTorus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.CategoryTheory CategoryTheory.Limits
open _root_.CategoryTheory MonoidalCategory _root_.Representation TensorProduct
open _root_.CategoryTheory
namespace AscendingTorus

open Monoid.Coprod Multiplicative

universe u

variable {U : Type u} [Group U]

def relation (f : U →* U) (x : U) : Monoid.Coprod U (Multiplicative ℤ) :=
  inl x * inr (ofAdd 1) * (inl (f x))⁻¹ * (inr (ofAdd 1))⁻¹

abbrev relations (f : U →* U) : Subgroup (Monoid.Coprod U (Multiplicative ℤ)) :=
  Subgroup.normalClosure (Set.range (relation f))

abbrev Torus (f : U →* U) : Type u :=
  Monoid.Coprod U (Multiplicative ℤ) ⧸ relations f

def of (f : U →* U) : U →* Torus f :=
  (QuotientGroup.mk' (relations f)).comp inl

def t (f : U →* U) : Torus f :=
  QuotientGroup.mk' (relations f) (inr (ofAdd 1))

theorem of_mul_t (f : U →* U) (x : U) :
    of f x * t f = t f * of f (f x) := by
  have hr : QuotientGroup.mk' (relations f) (relation f x) = 1 :=
    (QuotientGroup.eq_one_iff _).2 (Subgroup.subset_normalClosure ⟨x, rfl⟩)
  have hr' : of f x * t f * (of f (f x))⁻¹ * (t f)⁻¹ = 1 := by
    change (QuotientGroup.mk' (relations f)) (inl x) *
      (QuotientGroup.mk' (relations f)) (inr (ofAdd 1)) *
      ((QuotientGroup.mk' (relations f)) (inl (f x)))⁻¹ *
      ((QuotientGroup.mk' (relations f)) (inr (ofAdd 1)))⁻¹ = 1
    simpa only [relation, map_mul, map_inv] using hr
  have h := congrArg (fun z => z * t f * of f (f x)) hr'
  simpa [mul_assoc] using h

variable {V : Type*} [Group V]

def lift (f : U →* U) (k : U →* V) (s : V)
    (hs : ∀ x, k x * s = s * k (f x)) : Torus f →* V :=
  QuotientGroup.lift (relations f) (Monoid.Coprod.lift k (zpowersHom V s))
    (Subgroup.normalClosure_le_normal (by
      rintro _ ⟨x, rfl⟩
      change Monoid.Coprod.lift k (zpowersHom V s) (relation f x) = 1
      simp only [relation, map_mul, map_inv, Monoid.Coprod.lift_apply_inl,
        Monoid.Coprod.lift_apply_inr]
      simp [hs x, mul_assoc]))

@[simp] theorem lift_of (f : U →* U) (k : U →* V) (s : V)
    (hs : ∀ x, k x * s = s * k (f x)) (x : U) :
    lift f k s hs (of f x) = k x := by
  rfl

@[simp] theorem lift_t (f : U →* U) (k : U →* V) (s : V)
    (hs : ∀ x, k x * s = s * k (f x)) :
    lift f k s hs (t f) = s := by
  change s ^ (1 : ℤ) = s
  exact zpow_one s

@[ext] theorem hom_ext (f : U →* U) {k l : Torus f →* V}
    (hU : k.comp (of f) = l.comp (of f)) (ht : k (t f) = l (t f)) : k = l := by
  apply (MonoidHom.cancel_right (QuotientGroup.mk'_surjective (relations f))).1
  exact Monoid.Coprod.hom_ext hU (MonoidHom.ext_mint ht)

theorem conj_of_image (f : U →* U) (x : U) :
    t f * of f (f x) * (t f)⁻¹ = of f x := by
  rw [← of_mul_t]
  simp [mul_assoc]

variable {P : Type*} [Group P]

def interleaveForward (a : U →* P) (b : P →* U) :
    Torus (b.comp a) →* Torus (a.comp b) :=
  lift (b.comp a) ((of (a.comp b)).comp a) (t (a.comp b)) (by
    intro x
    exact of_mul_t (a.comp b) (a x))

def interleaveBase (a : U →* P) (b : P →* U) : P →* Torus (b.comp a) :=
  (MulAut.conj (t (b.comp a))).toMonoidHom.comp ((of (b.comp a)).comp b)

@[simp] theorem interleaveBase_apply (a : U →* P) (b : P →* U) (x : P) :
    interleaveBase a b x =
      t (b.comp a) * of (b.comp a) (b x) * (t (b.comp a))⁻¹ := rfl

def interleaveBackward (a : U →* P) (b : P →* U) :
    Torus (a.comp b) →* Torus (b.comp a) :=
  lift (a.comp b) (interleaveBase a b) (t (b.comp a)) (by
    intro x
    change t (b.comp a) * of (b.comp a) (b x) * (t (b.comp a))⁻¹ * t (b.comp a) =
      t (b.comp a) * (t (b.comp a) * of (b.comp a) ((b.comp a) (b x)) *
        (t (b.comp a))⁻¹)
    rw [conj_of_image]
    simp [mul_assoc])

@[simp] theorem interleaveBackward_forward (a : U →* P) (b : P →* U) :
    (interleaveBackward a b).comp (interleaveForward a b) =
      MonoidHom.id (Torus (b.comp a)) := by
  apply hom_ext
  · ext x
    change interleaveBackward a b (interleaveForward a b (of (b.comp a) x)) =
      of (b.comp a) x
    simp only [interleaveForward, interleaveBackward, lift_of, MonoidHom.comp_apply,
      interleaveBase_apply]
    exact conj_of_image (b.comp a) x
  · simp [interleaveForward, interleaveBackward]

@[simp] theorem interleaveForward_backward (a : U →* P) (b : P →* U) :
    (interleaveForward a b).comp (interleaveBackward a b) =
      MonoidHom.id (Torus (a.comp b)) := by
  apply hom_ext
  · ext x
    change interleaveForward a b (interleaveBackward a b (of (a.comp b) x)) =
      of (a.comp b) x
    simp only [interleaveBackward, lift_of, interleaveBase_apply, map_mul, map_inv]
    simp only [interleaveForward, lift_t, lift_of, MonoidHom.comp_apply]
    exact conj_of_image (a.comp b) x
  · simp [interleaveForward, interleaveBackward]

end AscendingTorus

namespace AscendingHNN
variable {U : Type*} [Group U] (f : U →* U) (hf : Function.Injective f)

def toPresentation : Torus f hf →* AscendingTorus.Torus f :=
  evaluation f hf (AscendingTorus.of f) (AscendingTorus.t f) (AscendingTorus.of_mul_t f)

def fromPresentation : AscendingTorus.Torus f →* Torus f hf :=
  AscendingTorus.lift f (embed f hf) (stable f hf) (embed_mul_stable f hf)

@[simp] lemma toPresentation_embed (u : U) :
    toPresentation f hf (embed f hf u)=AscendingTorus.of f u := evaluation_embed _ _ _ _ _ _
@[simp] lemma toPresentation_stable :
    toPresentation f hf (stable f hf)=AscendingTorus.t f := evaluation_stable _ _ _ _ _
@[simp] lemma fromPresentation_of (u : U) :
    fromPresentation f hf (AscendingTorus.of f u)=embed f hf u := AscendingTorus.lift_of _ _ _ _ _
@[simp] lemma fromPresentation_t :
    fromPresentation f hf (AscendingTorus.t f)=stable f hf := AscendingTorus.lift_t _ _ _ _

end AscendingHNN

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_TorusAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Pointwise
section
open scoped commutatorElement
namespace TorusAction
open SequentialLimit SequentialAction AscendingHNN
variable {U X : Type*} [Group U] [MulAction U X]
variable (f : U →* U) (hf : Function.Injective f)
variable (s : X → X) (heq : ∀ g x, s (g • x) = f g • s x)

def basePerm : U →* Equiv.Perm (Limit s) := by
  letI := limitAction f s heq
  exact (MulAction.toPermHom (Limit f) (Limit s)).comp (ofGroup f 0)

end TorusAction

end

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
namespace AscendingHNN
variable {U : Type*} [Group U] (f : U →* U) (hf : Function.Injective f) (a : U)

def innerTwist : U →* U := (MulAut.conj a).toMonoidHom.comp f

@[simp] lemma innerTwist_apply (u : U) : innerTwist f a u = a * f u * a⁻¹ := rfl

end AscendingHNN

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SourceCorner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory CategoryTheory.Limits
namespace AcyclicResolution
variable {k G : Type} [CommRing k] [Group G]

variable (Z C : ℕ → Rep.{0} k G)
  (f : ∀ i, Z (i+1) ⟶ C i) (g : ∀ i, C i ⟶ Z i)
  (w : ∀ i, f i ≫ g i = 0)

def row (i : ℕ) := ShortComplex.mk (f i) (g i) (w i)
def differential (i : ℕ) : C (i+1) ⟶ C i := g (i+1) ≫ f i
include w in
lemma differential_squared (i : ℕ) : differential Z C f g (i+1) ≫ differential Z C f g i = 0 := by
  simp only [differential,Category.assoc,← Category.assoc (f (i+1)),w,zero_comp,comp_zero]

def complexRow (i : ℕ) := ShortComplex.mk (differential Z C f g (i+1))
  (differential Z C f g i) (differential_squared Z C f g w i)

end AcyclicResolution

noncomputable section
open _root_.CategoryTheory CategoryTheory.Limits
namespace AcyclicChain
variable {k G : Type} [CommRing k] [Group G]
variable (D : ℕ → Rep.{0} k G) (δ : ∀ i, D (i+1) ⟶ D i)
  (w : ∀ i, δ (i+1) ≫ δ i = 0)
def cycles : ℕ → Rep k G
  | 0 => D 0
  | i+1 => kernel (δ i)
def inclusion (i : ℕ) : cycles D δ (i+1) ⟶ D (i+1) := kernel.ι (δ i)
def projection : ∀ i, D (i+1) ⟶ cycles D δ i
  | 0 => δ 0
  | i+1 => kernel.lift (δ i) (δ (i+1)) (w i)
lemma row_zero (i : ℕ) : inclusion D δ i ≫ projection D δ w i = 0 := by
  cases i with
  | zero => exact kernel.condition _
  | succ i =>
    apply (cancel_mono (kernel.ι (δ i))).mp
    change (kernel.ι (δ (i+1)) ≫ kernel.lift (δ i) (δ (i+1)) (w i)) ≫
      kernel.ι (δ i) = _
    simp only [Category.assoc,kernel.lift_ι,kernel.condition]
    exact (zero_comp (f := kernel.ι (δ i))).symm

def row (i : ℕ) := ShortComplex.mk (inclusion D δ i) (projection D δ w i) (row_zero D δ w i)
def chainRow (i : ℕ) := ShortComplex.mk (δ (i+1)) (δ i) (w i)

end AcyclicChain

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SurjectiveTrivialInduction
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
namespace SurjectiveTrivialInduction
open _root_.CategoryTheory _root_.Representation
attribute [-instance] AddCommGroup.toIntModule
end SurjectiveTrivialInduction

open _root_.CategoryTheory CategoryTheory.Limits
namespace ProductGroupHomology
section
attribute [-instance] AddCommGroup.toIntModule

open scoped MonoidalCategory
end

open _root_.CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
attribute [-instance] AddCommGroup.toIntModule
end ProductGroupHomology

attribute [instance] AddCommGroup.toIntModule

namespace ActionPresentation
section
universe u v w
variable {Q : Type u} {G : Type v} [Group Q] [Group G]

variable {F : Type*} {H : Type*} {R : Type*} [Group F] [Group H] [Group R]

noncomputable def descend (f : F →* H) (hf : Function.Surjective f)
    (g : F →* R) (hg : f.ker ≤ g.ker) : H →* R :=
  (QuotientGroup.lift f.ker g hg).comp
    (QuotientGroup.quotientKerEquivOfSurjective f hf).symm.toMonoidHom

structure LiftModel (p : Q →* G) (f : H →* G) where
  n : ℕ
  present : FreeGroup (Fin n) →* H
  surjective : Function.Surjective present
  lift : FreeGroup (Fin n) →* Q
  commutes : p.comp lift = f.comp present
  rels : Set (FreeGroup (Fin n))
  finite : rels.Finite
  kernel : Subgroup.normalClosure rels = present.ker

noncomputable def liftModel [Group.IsFinitelyPresented H] (p : Q →* G)
    (hp : Function.Surjective p) (f : H →* G) : LiftModel p f := Classical.choice (by
  classical
  obtain ⟨n,a,ha,T,hT,he⟩ := (inferInstance : Group.IsFinitelyPresented H).out
  choose b hb using fun i : Fin n => hp (f (a (FreeGroup.of i)))
  refine ⟨⟨n,a,ha,FreeGroup.lift b,?_,T,hT,he⟩⟩
  ext i
  simpa using hb i)

namespace LiftModel
variable {p : Q →* G} {f : H →* G} (M : LiftModel p f)
def obstruction : Set Q := M.lift '' M.rels
lemma ker_le (q : Q →* R) (hq : ∀ r ∈ M.obstruction, q r = 1) :
    M.present.ker ≤ (q.comp M.lift).ker := by
  rw [← M.kernel]
  apply Subgroup.normalClosure_le_normal
  intro r hr
  exact hq _ ⟨r,hr,rfl⟩
noncomputable def hom (q : Q →* R) (hq : ∀ r ∈ M.obstruction, q r = 1) : H →* R :=
  descend M.present M.surjective (q.comp M.lift) (M.ker_le q hq)
end LiftModel

def killProjection (p : Q →* G) (S : Set Q) (hS : S ⊆ p.ker) :
    Q ⧸ Subgroup.normalClosure S →* G :=
  QuotientGroup.lift _ p (Subgroup.normalClosure_le_normal hS)

end

universe u v w
end ActionPresentation

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
structure Cocycle (P : Type u) [Preorder P] (H : Type w) [Group H] where
  edge : ∀ {x y : P}, x ≤ y → H
  refl : ∀ x, edge (le_refl x) = 1
  comp : ∀ {x y z : P} (h : x ≤ y) (k : y ≤ z), edge h * edge k = edge (h.trans k)
namespace Cocycle
@[ext] lemma ext {c d : Cocycle P H}
    (h : ∀ {x y} (hxy : x ≤ y), c.edge hxy = d.edge hxy) : c = d := by
  cases c with
  | mk e r k =>
    cases d with
    | mk e' r' k' =>
      have he : @e = @e' := by funext x y hxy; exact h hxy
      subst e'
      rfl
end Cocycle

end

end PosetTransport

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_TwistedBrinBasisMatching
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

namespace ActionTransport
section
open PosetTransport
universe u v w
variable {G : Type u} [Group G] {P : Type v} [Preorder P] [MulAction G P]
variable {Q : Type w} [Group Q]

structure Gauge (p : Q →* G) (t : P → G) where
  value : G → P → Q
  one : ∀ x, value 1 x = 1
  mul : ∀ g h x, value (g*h) x = value g (h • x) * value h x
  projects : ∀ g x, p (value g x) = (t (g • x))⁻¹ * g * t x

end

section
open PosetTransport
open scoped Pointwise
universe u v w
variable {G : Type u} [Group G] {P : Type v} [Preorder P] [MulAction G P]
class IsMonotoneAction (G P : Type*) [Group G] [Preorder P] [MulAction G P] : Prop where
  mono : ∀ g : G, Monotone (g • · : P → P)

structure Frames (G : Type u) [Group G] (P : Type v) [MulAction G P] where
  Index : Type v
  rep : Index → P
  index : P → Index
  index_rep : ∀ i, index (rep i) = i
  index_smul : ∀ (g : G) x, index (g • x) = index x
  element : P → G
  frame : ∀ x, element x • rep (index x) = x

namespace Frames
variable {X : Type v} [MulAction G X] (F : Frames G X)
def stab (i : F.Index) : Subgroup G := MulAction.stabilizer G (F.rep i)
lemma mem_stab (i : F.Index) (g : G) : g ∈ F.stab i ↔ g • F.rep i = F.rep i := Iff.rfl
lemma difference_mem (g : G) (x : X) :
    (F.element (g • x))⁻¹ * g * F.element x ∈ F.stab (F.index x) := by
  rw [mem_stab,mul_smul,mul_smul,F.frame]
  apply inv_smul_eq_iff.mpr
  simpa only [F.index_smul] using (F.frame (g • x)).symm
end Frames

variable [IsMonotoneAction G P]
lemma act_mono (g : G) : Monotone (g • · : P → P) := IsMonotoneAction.mono g

def Edge (P : Type v) [Preorder P] := {xy : P × P // xy.1 ≤ xy.2}
namespace Edge
instance instMulAction : MulAction G (Edge P) where
  smul g e := ⟨(g • e.val.1,g • e.val.2),act_mono g e.property⟩
  one_smul e := by
    apply Subtype.ext
    change (1 • e.val.1, 1 • e.val.2) = e.val
    simp
  mul_smul g h e := by
    apply Subtype.ext
    change ((g*h) • e.val.1, (g*h) • e.val.2) = (g • h • e.val.1,g • h • e.val.2)
    simp [mul_smul]
@[simp] lemma fst_smul (g : G) (e : Edge P) : (g • e).val.1 = g • e.val.1 := rfl
@[simp] lemma snd_smul (g : G) (e : Edge P) : (g • e).val.2 = g • e.val.2 := rfl
end Edge

end

section
open PosetTransport
universe u v w
variable {G : Type u} [Group G] {P : Type v} [Preorder P] [MulAction G P]
variable {Q : Type w} [Group Q]
structure LiftedFrames (F : Frames G P) (p : Q →* G) where
  hom : ∀ i, F.stab i →* Q
  projects : ∀ i h, p (hom i h) = (h : G)
namespace LiftedFrames
variable {F : Frames G P} {p : Q →* G} (J : LiftedFrames F p)
noncomputable def eval (i : F.Index) (g : G) : Q := by
  classical
  exact if h : g ∈ F.stab i then J.hom i ⟨g,h⟩ else 1
omit [Preorder P] in
lemma eval_valid [Preorder P] (i : F.Index) (g : G) (h : g ∈ F.stab i) :
    J.eval i g = J.hom i ⟨g,h⟩ := by
  classical
  exact dite_eq_left h
lemma eval_one (i : F.Index) : J.eval i 1 = 1 := by
  rw [J.eval_valid i 1 (F.stab i).one_mem]
  exact (J.hom i).map_one
lemma eval_mul (i : F.Index) (g h : G) (hg : g ∈ F.stab i) (hh : h ∈ F.stab i) :
    J.eval i (g*h) = J.eval i g * J.eval i h := by
  rw [J.eval_valid _ _ ((F.stab i).mul_mem hg hh),J.eval_valid _ _ hg,J.eval_valid _ _ hh]
  exact (J.hom i).map_mul ⟨g,hg⟩ ⟨h,hh⟩
lemma eval_projects (i : F.Index) (g : G) (hg : g ∈ F.stab i) : p (J.eval i g) = g := by
  rw [J.eval_valid _ _ hg]
  exact J.projects _ _
noncomputable def gauge : Gauge p F.element where
  value g x := J.eval (F.index x) ((F.element (g • x))⁻¹ * g * F.element x)
  one x := by simpa using J.eval_one (F.index x)
  mul g h x := by
    simp only [F.index_smul,mul_smul]
    have hg : (F.element (g • h • x))⁻¹ * g * F.element (h • x) ∈ F.stab (F.index x) := by
      simpa only [F.index_smul] using F.difference_mem g (h • x)
    rw [← J.eval_mul _ _ _ hg (F.difference_mem h x)]
    congr 1
    group
  projects g x := J.eval_projects _ _ (F.difference_mem g x)
end LiftedFrames

variable [IsMonotoneAction G P]
variable {p : Q →* G}

def edgeTransport (F : Frames G P) (E : Frames G (Edge P))
    (d : Gauge p F.element) (L : E.Index → Q) (i : E.Index) (g : G) : Q :=
  d.value g (E.rep i).val.1 * L i * (d.value g (E.rep i).val.2)⁻¹
noncomputable def rawEdge (F : Frames G P) (E : Frames G (Edge P))
    (d : Gauge p F.element) (L : E.Index → Q) (e : Edge P) : Q :=
  edgeTransport F E d L (E.index e) (E.element e)

end

open PosetTransport
universe u v w z
variable {G : Type u} [Group G] {P : Type v} [Preorder P] [MulAction G P]
variable {Q : Type w} [Group Q] {R : Type z} [Group R]
namespace Gauge
variable {p : Q →* G} {t : P → G}
def map (d : Gauge p t) (q : Q →* R) (p' : R →* G) (hp' : p'.comp q = p) : Gauge p' t where
  value g x := q (d.value g x)
  one x := by rw [d.one,map_one]
  mul g h x := by rw [d.mul,map_mul]
  projects g x := (DFunLike.congr_fun hp' _).trans (d.projects g x)
end Gauge
variable [IsMonotoneAction G P]
namespace Edge
def diag (x : P) : Edge P := ⟨(x,x),le_rfl⟩
@[simp] lemma diag_smul (g : G) (x : P) : diag (g • x) = g • diag x := rfl
end Edge

def Triangle (P : Type v) [Preorder P] :=
  {xyz : P × P × P // xyz.1 ≤ xyz.2.1 ∧ xyz.2.1 ≤ xyz.2.2}
namespace Triangle
instance instMulAction : MulAction G (Triangle P) where
  smul g t := ⟨(g • t.val.1,g • t.val.2.1,g • t.val.2.2),
    act_mono g t.property.1,act_mono g t.property.2⟩
  one_smul t := by
    apply Subtype.ext
    change (1 • t.val.1,1 • t.val.2.1,1 • t.val.2.2) = t.val
    simp
  mul_smul g h t := by
    apply Subtype.ext
    change ((g*h) • t.val.1,(g*h) • t.val.2.1,(g*h) • t.val.2.2) =
      (g • h • t.val.1,g • h • t.val.2.1,g • h • t.val.2.2)
    simp only [mul_smul]
def e01 (t : Triangle P) : Edge P := ⟨(t.val.1,t.val.2.1),t.property.1⟩
def e12 (t : Triangle P) : Edge P := ⟨(t.val.2.1,t.val.2.2),t.property.2⟩
def e02 (t : Triangle P) : Edge P := ⟨(t.val.1,t.val.2.2),t.property.1.trans t.property.2⟩
@[simp] lemma e01_smul (g : G) (t : Triangle P) : e01 (g • t) = g • e01 t := rfl
@[simp] lemma e12_smul (g : G) (t : Triangle P) : e12 (g • t) = g • e12 t := rfl
@[simp] lemma e02_smul (g : G) (t : Triangle P) : e02 (g • t) = g • e02 t := rfl
end Triangle

lemma flat_triangle_translate {p : Q →* G} {f : P → G} (d : Gauge p f)
    (c : Edge P → Q)
    (heq : ∀ g e, c (g • e) = d.value g e.val.1 * c e * (d.value g e.val.2)⁻¹)
    (t : Triangle P) (ht : c t.e01 * c t.e12 = c t.e02) (g : G) :
    c (g • t).e01 * c (g • t).e12 = c (g • t).e02 := by
  simp only [Triangle.e01_smul,Triangle.e12_smul,Triangle.e02_smul,heq]
  change (d.value g t.val.1 * c t.e01 * (d.value g t.val.2.1)⁻¹) *
    (d.value g t.val.2.1 * c t.e12 * (d.value g t.val.2.2)⁻¹) =
      d.value g t.val.1 * c t.e02 * (d.value g t.val.2.2)⁻¹
  rw [← ht]
  group

noncomputable def cocycleOfFlat (F : Frames G P) (T : Frames G (Triangle P))
    {p : Q →* G} (d : Gauge p F.element) (c : Edge P → Q)
    (heq : ∀ g e, c (g • e) = d.value g e.val.1 * c e * (d.value g e.val.2)⁻¹)
    (hdiag : ∀ i, c (Edge.diag (F.rep i)) = 1)
    (htri : ∀ i, c (T.rep i).e01 * c (T.rep i).e12 = c (T.rep i).e02) : Cocycle P Q where
  edge h := c ⟨(_, _),h⟩
  refl x := by
    change c (Edge.diag x) = 1
    rw [← F.frame x,Edge.diag_smul,heq,hdiag]
    change d.value _ (F.rep _) * 1 * (d.value _ (F.rep _))⁻¹ = 1
    group
  comp {x y z} h k := by
    let t : Triangle P := ⟨(x,y,z),h,k⟩
    change c t.e01 * c t.e12 = c t.e02
    rw [← T.frame t]
    exact flat_triangle_translate d c heq _ (htri _) _

end ActionTransport

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_ActionTransport
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
namespace ActionTransport

section
open PosetTransport ActionPresentation
universe u v w
variable {G : Type u} [Group G] {P : Type v} [Preorder P] [MulAction G P]
variable {Q : Type w} [Group Q] [IsMonotoneAction G P]
variable {p : Q →* G} {t : P → G}

def edgeLeftHom (d : Gauge p t) (e : Edge P) : MulAction.stabilizer G e →* Q where
  toFun g := d.value g.val e.val.1
  map_one' := d.one _
  map_mul' g h := by
    have hh := congrArg (fun e : Edge P => e.val.1) h.property
    change h.val • e.val.1 = e.val.1 at hh
    change d.value (g.val * h.val) e.val.1 = _
    rw [d.mul,hh]

def edgeRightHom (d : Gauge p t) (e : Edge P) (L : Q) : MulAction.stabilizer G e →* Q where
  toFun g := L * d.value g.val e.val.2 * L⁻¹
  map_one' := by
    change L * d.value 1 e.val.2 * L⁻¹ = 1
    rw [d.one]
    group
  map_mul' g h := by
    have hh := congrArg (fun e : Edge P => e.val.2) h.property
    change h.val • e.val.2 = e.val.2 at hh
    change L * d.value (g.val * h.val) e.val.2 * L⁻¹ = _
    rw [d.mul,hh]
    group

end

universe u v w
variable {G : Type u} [Group G] {X : Type v} [MulAction G X]
noncomputable def orbitFrames (G : Type u) [Group G] (X : Type v) [MulAction G X] : Frames G X where
  Index := MulAction.orbitRel.Quotient G X
  rep := Quotient.out
  index := Quotient.mk _
  index_rep := Quotient.out_eq
  index_smul _ _ := MulAction.orbitRel.Quotient.quotient_smul_eq
  element x := Classical.choose (show ∃ g : G, g • (Quotient.mk (MulAction.orbitRel G X) x).out = x from
    Quotient.exact (Quotient.out_eq (Quotient.mk (MulAction.orbitRel G X) x)).symm)
  frame x := Classical.choose_spec (show ∃ g : G, g • (Quotient.mk (MulAction.orbitRel G X) x).out = x from
    Quotient.exact (Quotient.out_eq (Quotient.mk (MulAction.orbitRel G X) x)).symm)

end ActionTransport

end

end OAI
end


