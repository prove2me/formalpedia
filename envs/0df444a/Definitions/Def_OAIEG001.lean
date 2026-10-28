-- Prove2me | Definitions.Def_OAIEG001
-- name    : OAIEG001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-24T23:48:54.718236+00:00
-- url     : https://prove2.me/theorems/35889d35-19b7-46ae-a1df-105acc6bad30
-- title:
--   Definitions bundle OAIEG001 of the split of OpenAI, A finitely generated counterexample to the Eilenberg–Ganea conjecture
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.EilenbergGanea.source_main`, carved from OpenAI's openai/math development (OpenAI, *A finitely generated counterexample to the Eilenberg–Ganea conjecture*, OpenAI Math Release, September 23, 2026, result family 249, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 107 declarations of OpenAI's Lean: 72 definitions, 1 inductive type or structure, 2 instances and 32 theorems. The definitions and types are `OAI.EilenbergGanea.CWCollar.lowerSkeleton`, `OAI.EilenbergGanea.CWSubspace.Cell`, `OAI.EilenbergGanea.CWSubspace.lower`, `OAI.EilenbergGanea.CWSubspace.lowerHomeomorph`, `OAI.EilenbergGanea.CoverKernel.fundamentalKernelEquiv`, `OAI.EilenbergGanea.CoverKernel.inclusion`, `OAI.EilenbergGanea.CoverKernel.projection`, `OAI.EilenbergGanea.CoverKernel.toBase`, `OAI.EilenbergGanea.CoverKernel.toTotal`, `OAI.EilenbergGanea.CoverKernel.totalInclusion`, `OAI.EilenbergGanea.CoverMonodromy.traversalEquiv`, `OAI.EilenbergGanea.CoverTopology.deckGroup`, `OAI.EilenbergGanea.CubeRealization.CliqueIndex`, `OAI.EilenbergGanea.ForestCover.ThinPaths`, `OAI.EilenbergGanea.ForestCover.componentRoot`, `OAI.EilenbergGanea.ForestCover.componentStem`, `OAI.EilenbergGanea.ForestCover.inclusion`, `OAI.EilenbergGanea.ForestCover.rightLabel`, `OAI.EilenbergGanea.IntegralGroupRing`, `OAI.EilenbergGanea.IntegralTrivialModule`, `OAI.EilenbergGanea.KernelCycles.AbKernel`, `OAI.EilenbergGanea.KernelCycles.Kernel`, `OAI.EilenbergGanea.NormalFactor`, `OAI.EilenbergGanea.PathTransport.Compression`, `OAI.EilenbergGanea.PathTransport.liftCube`, `OAI.EilenbergGanea.PathTransport.subpath`, `OAI.EilenbergGanea.SeedChainCertificate.d1Data`, `OAI.EilenbergGanea.SeedChainCertificate.d1Data_0`, `OAI.EilenbergGanea.SeedChainCertificate.d1Data_1`, `OAI.EilenbergGanea.SeedChainCertificate.d1Data_2`, `OAI.EilenbergGanea.SeedChainCertificate.d1Data_3`, `OAI.EilenbergGanea.SeedChainCertificate.d1Data_4`, `OAI.EilenbergGanea.SeedChainCertificate.d1Data_5`, `OAI.EilenbergGanea.SeedChainCertificate.d1Data_6`, `OAI.EilenbergGanea.SeedChainCertificate.d1Row`, `OAI.EilenbergGanea.SeedChainCertificate.d₁`, `OAI.EilenbergGanea.SeedChainCertificate.edgeData_0`, `OAI.EilenbergGanea.SeedChainCertificate.edgeData_1`, `OAI.EilenbergGanea.SeedChainCertificate.edgeData_10`, `OAI.EilenbergGanea.SeedChainCertificate.edgeData_11` and 33 more.
--
--   **Sources.** They come from these modules of lean/OAI/Topology/EilenbergGanea, lean/OAI/AlgebraicTopology, lean/OAI/GroupTheory, in whole or in part: `CWComplex_CellularPaths`, `CWComplex_Collar`, `CWComplex_Cover`, `CWComplex_CoverTopology`, `CubicalCover`, `Cubical_Realization`, `IntegralModules`, `Integral_Contraction`, `Presentation_KernelCycles`, `RightAngledArtin_ResidualFiniteness`, `RightAngledArtin_TraceWords`, `SeedChains`, `SeedContraction`, `SmallHolonomy`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIEG011`, `OAIEG012`, `OAIEG013`, `OAIEG014`, `OAIEG015`, `OAIEG016`, `OAIEG017`, `OAIEG018`, `OAIEG031`, `OAIEG032`, `OAIEG033`, `OAIEG034` and `OAIEG035`.
-- source:
--   OpenAI, A finitely generated counterexample to the Eilenberg–Ganea conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 249; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-finitely-generated-counterexample-to-the-Eilenberg-Ganea-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Topology/EilenbergGanea, lean/OAI/AlgebraicTopology, lean/OAI/GroupTheory at commit adc7f12

import Mathlib

section
-- module Solutions.OAIEG.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
/-- Mathlib's newer case names for `FreeGroup.induction_on` (`one`, where ours says `C1`). -/
@[elab_as_elim]
theorem freeGroupInductionOn {α : Type*} {C : FreeGroup α → Prop} (z : FreeGroup α) (one : C 1)
    (of : ∀ x, C (FreeGroup.of x)) (inv_of : ∀ x, C (FreeGroup.of x) → C (FreeGroup.of x)⁻¹)
    (mul : ∀ x y, C x → C y → C (x * y)) : C z :=
  FreeGroup.induction_on z one of inv_of mul
end OAICompat434

end OAI
end

section
-- module Solutions.OAIEG.CWComplex_Cover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set Metric Topology

/-! Actual characteristic-cell lifts for an ordinary Whitehead CW complex.
This is a dependency toward (not an assumption replacing) the arbitrary-CW
presentation and cellular-cycle bridge. -/
open Set Metric Topology

namespace EilenbergGanea.CWCover
open Classical
variable {X E : Type*} [TopologicalSpace X] [TopologicalSpace E]
variable [CWComplex (univ : Set X)] {p : E → X} (cov : IsCoveringMap p)

include cov in
omit [CWComplex (univ : Set X)] in
/-- The total space of an ordinary covering of a Hausdorff space is Hausdorff;
no Hausdorff hypothesis is added to the source's definition of K(G,1). -/
theorem t2Space [T2Space X] : T2Space E := by
  refine ⟨fun e f hne => ?_⟩
  by_cases h : p e = p f
  · exact cov.isSeparatedMap e f h hne
  · obtain ⟨U,V,hU,hV,he,hf,hd⟩ := t2_separation h
    exact ⟨p ⁻¹' U,p ⁻¹' V,hU.preimage cov.continuous,hV.preimage cov.continuous,
      he,hf,hd.preimage p⟩

end EilenbergGanea.CWCover


end

end OAI
end

section
-- module Solutions.OAIEG.CWComplex_Collar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set Metric Topology

namespace EilenbergGanea.CWCollar
open Classical Set Metric Topology CWCover
variable {X : Type*} [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)]

def lowerSkeleton (m : ℕ) : Set X := CWComplex.skeletonLT (univ : Set X) m

end EilenbergGanea.CWCollar


end

end OAI
end

section
-- module Solutions.OAIEG.CWComplex_CellularPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set Metric Topology

namespace EilenbergGanea.PathTransport
open Set
variable {X G : Type*} [TopologicalSpace X] [Group G]

namespace TwoPotential
variable {U V : Set X}

theorem cover_open (hU : IsOpen U) (hV : IsOpen V) : ∀ W ∈ ({U,V} : Set (Set X)), IsOpen W := by
  rintro W (rfl | rfl)
  · exact hU
  · exact hV

omit [TopologicalSpace X] in
theorem cover_univ (hUV : U ∪ V = univ) : ⋃₀ ({U,V} : Set (Set X)) = univ := by
  simpa only [sUnion_insert,sUnion_singleton] using hUV

end TwoPotential
end EilenbergGanea.PathTransport

namespace EilenbergGanea.ForestCover
open Set PathTransport
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Every path component is simply connected; no connectedness is imposed. -/
def ThinPaths (Y : Type*) [TopologicalSpace Y] : Prop :=
  ∀ (x y : Y) (p p' : Path x y), Path.Homotopic p p'

def componentRoot (x : Y) : Y := (ZerothHomotopy.mk x).out

def componentStem (x : Y) : Path (componentRoot x) x :=
  (Quotient.exact (Quotient.out_eq (ZerothHomotopy.mk x)) : Joined (componentRoot x) x).somePath

theorem componentRoot_eq {x y : Y} (p : Path x y) : componentRoot x = componentRoot y :=
  congrArg Quotient.out (ZerothHomotopy.sound p)

variable {r : X} (q : ∀ x, Path r x)

variable (U V : Set X)

def inclusion (U : Set X) : C(U,X) := ⟨Subtype.val,continuous_subtype_val⟩

def rightLabel (x : X) : FreeGroup (ZerothHomotopy (U ∩ V : Set X)) :=
  if h : x ∈ U ∩ V then FreeGroup.of (ZerothHomotopy.mk ⟨x,h⟩) else 1

end EilenbergGanea.ForestCover

namespace EilenbergGanea.PathTransport
open Set ForestCover
variable {X G : Type*} [TopologicalSpace X] [Group G]

def liftCube {Y : Type*} [TopologicalSpace Y] (U : Set X) (γ : C(Y,X))
    (h : Set.range γ ⊆ U) : C(Y,U) := ⟨fun t => ⟨γ t,h ⟨t,rfl⟩⟩,γ.continuous.subtype_mk _⟩

end EilenbergGanea.PathTransport


namespace EilenbergGanea.CWSubspace
open Set Metric Topology CWCover CWCollar
variable {X : Type*} [TopologicalSpace X] [T2Space X] (C : Set X) [CWComplex C]
abbrev Cell (n : ℕ) := RelCWComplex.cell C n

def lower (m : ℕ) : Set C := Subtype.val ⁻¹' (CWComplex.skeletonLT C m : Set X)

end EilenbergGanea.CWSubspace


namespace EilenbergGanea.CWSubspace
open Set Metric Topology CWCover
variable {X : Type*} [TopologicalSpace X] [T2Space X] (C : Set X) [CWComplex C]

def lowerHomeomorph (m : ℕ) : lower C m ≃ₜ (CWComplex.skeletonLT C m : Set X) where
  toFun z := ⟨z.val.val,z.property⟩
  invFun z := ⟨⟨z.val,(CWComplex.skeletonLT C m).subset_complex z.property⟩,z.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

end EilenbergGanea.CWSubspace



end

end OAI
end

section
-- module Solutions.OAIEG.CWComplex_CoverTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set Metric Topology


open Set Topology
open scoped unitInterval
namespace EilenbergGanea.CoverTopology
variable {A E X : Type*} [TopologicalSpace A] [TopologicalSpace E] [TopologicalSpace X]
variable {p : E → X} (cov : IsCoveringMap p)

include cov

/-- A contractible domain admits based covering lifts without a separate
local path-connectivity hypothesis: lift a contraction and reverse its base path. -/
theorem existsUnique_lift_contractible [ContractibleSpace A]
    (f : C(A,X)) (a₀ : A) (e₀ : E) (he : p e₀ = f a₀) :
    ∃! g : C(A,E), g a₀ = e₀ ∧ p ∘ g = f := by
  obtain ⟨a,⟨H⟩⟩ := id_nullhomotopic A
  let β : C(unitInterval,X) := f.comp (H.evalAt a₀).toContinuousMap
  have hβ : β 0 = p e₀ := by
    change f ((H.evalAt a₀) 0) = p e₀
    rw [Path.source]
    exact he.symm
  let β' := cov.liftPath β e₀ hβ
  let e := β' 1
  have he' : p e = f a := by
    have h := congrFun (cov.liftPath_lifts β e₀ hβ) 1
    change p e = β 1 at h
    change p e = f ((H.evalAt a₀) 1) at h
    rw [(H.evalAt a₀).target] at h
    exact h
  let B : C(unitInterval × A,X) := f.comp H.symm.toContinuousMap
  have hB : ∀ z, B (0,z) = p ((ContinuousMap.const A e) z) := by
    intro z
    change f (H.symm (0,z)) = p e
    simpa only [ContinuousMap.Homotopy.apply_zero,ContinuousMap.const_apply] using he'.symm
  let L := cov.liftHomotopy B (ContinuousMap.const A e) hB
  let g : C(A,E) := L.comp ⟨fun z => (1,z),by fun_prop⟩
  have hg : p ∘ g = f := by
    ext z
    change p (g z) = f z
    have h := congrFun (cov.liftHomotopy_lifts B (ContinuousMap.const A e) hB) (1,z)
    change p (g z) = f (H.symm (1,z)) at h
    simpa only [ContinuousMap.Homotopy.apply_one,ContinuousMap.id_apply] using h
  have hbase : g a₀ = e₀ := by
    let k : C(unitInterval,E) := L.comp ⟨fun t => (t,a₀),by fun_prop⟩
    let k' : C(unitInterval,E) := β'.comp ⟨unitInterval.symm,unitInterval.symmHomeomorph.continuous⟩
    have hk : (k : unitInterval → E) = k' := cov.eq_of_comp_eq k.continuous k'.continuous (by
      ext t
      change p (L (t,a₀)) = p (β' (unitInterval.symm t))
      rw [show p (L (t,a₀)) = B (t,a₀) from
        congrFun (cov.liftHomotopy_lifts B (ContinuousMap.const A e) hB) (t,a₀)]
      rw [show p (β' (unitInterval.symm t)) = β (unitInterval.symm t) from
        congrFun (cov.liftPath_lifts β e₀ hβ) (unitInterval.symm t)]
      rfl) 0 (by
        change L (0,a₀) = β' (unitInterval.symm 0)
        rw [unitInterval.symm_zero]
        exact cov.liftHomotopy_zero B (ContinuousMap.const A e) hB a₀)
    have h := congrFun hk 1
    change g a₀ = β' (unitInterval.symm 1) at h
    rw [unitInterval.symm_one] at h
    exact h.trans (cov.liftPath_zero β e₀ hβ)
  refine ⟨g,⟨hbase,hg⟩,?_⟩
  intro k hk
  apply DFunLike.ext'
  exact cov.eq_of_comp_eq k.continuous g.continuous (hk.2.trans hg.symm) a₀
    (hk.1.trans hbase.symm)

end EilenbergGanea.CoverTopology

namespace EilenbergGanea.CoverTopology
variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
variable (p : E → X)

/-- The actual group of self-homeomorphisms over a covering projection. -/
def deckGroup : Subgroup (E ≃ₜ E) where
  carrier := {d | ∀ e, p (d e) = p e}
  one_mem' := fun _ => rfl
  mul_mem' := fun {d e} hd he x => (hd (e x)).trans (he x)
  inv_mem' := by
    intro d hd e
    simpa only [Homeomorph.inv_apply,Homeomorph.apply_symm_apply] using (hd (d.symm e)).symm

instance deckMulAction : MulAction (deckGroup p) E where
  smul d e := d.val e
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

omit [TopologicalSpace X] in
@[simp] theorem deck_smul (d : deckGroup p) (e : E) : d • e = d.val e := rfl
omit [TopologicalSpace X] in
theorem deck_project (d : deckGroup p) (e : E) : p (d • e) = p e := d.property e

instance deckContinuous : ContinuousConstSMul (deckGroup p) E where
  continuous_const_smul d := d.val.continuous

variable {p} (cov : IsCoveringMap p)
include cov

theorem deck_ext [PreconnectedSpace E] {d e : deckGroup p} (x : E)
    (hx : d • x = e • x) : d = e := by
  apply Subtype.ext
  apply Homeomorph.ext
  exact congrFun (cov.eq_of_comp_eq d.val.continuous e.val.continuous
    (by ext z; exact (d.property z).trans (e.property z).symm) x hx)

/-- Every two points in a fiber of a contractible covering are related by a
unique genuine deck homeomorphism. No local-connectivity hypothesis is added. -/
theorem existsUnique_deck [ContractibleSpace E] (x y : E) (hxy : p x = p y) :
    ∃! d : deckGroup p, d • x = y := by
  let P : C(E,X) := ⟨p,cov.continuous⟩
  obtain ⟨f,hf,_⟩ := existsUnique_lift_contractible cov P x y hxy.symm
  obtain ⟨g,hg,_⟩ := existsUnique_lift_contractible cov P y x hxy
  have hgf : g ∘ f = id := cov.eq_of_comp_eq
    (g.continuous.comp f.continuous) continuous_id (by
      ext z
      change p (g (f z)) = p z
      exact (congrFun hg.2 (f z)).trans (congrFun hf.2 z)) x (by
        change g (f x) = x
        rw [hf.1,hg.1])
  have hfg : f ∘ g = id := cov.eq_of_comp_eq
    (f.continuous.comp g.continuous) continuous_id (by
      ext z
      change p (f (g z)) = p z
      exact (congrFun hf.2 (g z)).trans (congrFun hg.2 z)) y (by
        change f (g y) = y
        rw [hg.1,hf.1])
  let d : deckGroup p := ⟨{
      toFun := f
      invFun := g
      left_inv := fun z => congrFun hgf z
      right_inv := fun z => congrFun hfg z
      continuous_toFun := f.continuous
      continuous_invFun := g.continuous }, fun z => congrFun hf.2 z⟩
  refine ⟨d,hf.1,?_⟩
  intro d' hd'
  exact deck_ext cov x (hd'.trans hf.1.symm)

/-- A surjective contractible covering is literally a quotient covering by its
deck group, with a free properly discontinuous action. -/
theorem isQuotientCoveringMap_deck [ContractibleSpace E] (hs : Function.Surjective p) :
    IsQuotientCoveringMap p (deckGroup p) where
  __ := cov.isQuotientMap hs
  __ := deckContinuous p
  apply_eq_iff_mem_orbit := by
    intro x y
    constructor
    · intro h
      obtain ⟨d,hd,_⟩ := existsUnique_deck cov y x h.symm
      exact ⟨d,hd⟩
    · rintro ⟨d,rfl⟩
      exact deck_project p d y
  disjoint := by
    intro x
    obtain ⟨U,hU,hxU,hinj⟩ := cov.isLocalHomeomorph.isLocallyInjective x
    refine ⟨U,hU.mem_nhds hxU,?_⟩
    rintro d ⟨z,⟨y,hyU,rfl⟩,hzU⟩
    apply deck_ext cov y
    exact hinj hzU hyU (deck_project p d y)

end EilenbergGanea.CoverTopology


namespace EilenbergGanea.PathTransport
open Set
variable {X : Type*} [TopologicalSpace X]

def subpath (W : Set X) {x y : X} (p : Path x y) (hp : Set.range p ⊆ W) :
    Path (⟨x,hp ⟨0,p.source⟩⟩ : W) ⟨y,hp ⟨1,p.target⟩⟩ where
  toFun t := ⟨p t,hp ⟨t,rfl⟩⟩
  continuous_toFun := p.continuous.subtype_mk _
  source' := Subtype.ext p.source
  target' := Subtype.ext p.target

structure Compression (U V : Set X) where
  select : X → U
  bridge : ∀ x, Path x (select x).val
  left : ∀ x, x ∈ U → Set.range (bridge x) ⊆ U
  right : ∀ x, x ∈ V → Set.range (bridge x) ⊆ V
  join : ∀ x y : (U ∩ V : Set X), Nonempty (Path (⟨x.val,x.property.2⟩ : V) ⟨y.val,y.property.2⟩) → Nonempty (Path x y)

end EilenbergGanea.PathTransport



open Classical Set
namespace EilenbergGanea.CoverKernel
variable {X E : Type*} [TopologicalSpace X] [TopologicalSpace E]
variable {p : E → X} (cov : IsCoveringMap p) (U : Set X)

def projection : C(p ⁻¹' U,U) := ⟨U.restrictPreimage p,(cov.continuous.comp continuous_subtype_val).subtype_mk _⟩
def inclusion : C(U,X) := ⟨Subtype.val,continuous_subtype_val⟩
def totalInclusion : C(p ⁻¹' U,E) := ⟨Subtype.val,continuous_subtype_val⟩

theorem lift_loop_closed {e : E} (γ : Path (p e) (p e))
    (h : γ.Homotopic (Path.refl (p e))) : cov.liftPath γ e γ.source 1 = e := by
  have he := cov.liftPath_apply_one_eq_of_homotopicRel h e γ.source rfl
  change cov.liftPath γ e γ.source 1 = cov.liftPath (ContinuousMap.const _ (p e)) e rfl 1 at he
  rw [cov.liftPath_const (e := e) rfl] at he
  exact he

variable (e : p ⁻¹' U)

def toBase : (FundamentalGroup (p ⁻¹' U) e)ᵐᵒᵖ →* (FundamentalGroup U (projection cov U e))ᵐᵒᵖ :=
  (FundamentalGroup.map (projection cov U) e).op

def toTotal : (FundamentalGroup U (projection cov U e))ᵐᵒᵖ →* (FundamentalGroup X (p e.val))ᵐᵒᵖ :=
  (FundamentalGroup.map (inclusion U) (projection cov U e)).op

theorem toBase_injective : Function.Injective (toBase cov U e) := by
  intro a b he
  apply MulOpposite.unop_injective
  exact (cov.restrictPreimage U).injective_path_homotopic_map e e (congrArg MulOpposite.unop he)

/-- Closed lifting, proved using homotopy lifting, identifies the full kernel. -/
theorem toBase_range [SimplyConnectedSpace E] : (toBase cov U e).range = (toTotal cov U e).ker := by
  apply le_antisymm
  · rintro w ⟨v,rfl⟩
    obtain ⟨γ,hγ⟩ := Quotient.exists_rep v.unop
    have hg : MulOpposite.op (Path.Homotopic.Quotient.mk γ) = v := congrArg MulOpposite.op hγ
    rw [← hg]
    change toTotal cov U e (toBase cov U e (MulOpposite.op (Path.Homotopic.Quotient.mk γ))) = 1
    apply MulOpposite.unop_injective
    change Path.Homotopic.Quotient.mk ((γ.map (projection cov U).continuous).map (inclusion U).continuous) = Path.Homotopic.Quotient.mk (Path.refl (p e.val))
    apply Path.Homotopic.Quotient.eq.mpr
    exact (SimplyConnectedSpace.paths_homotopic (γ.map (totalInclusion U).continuous) (Path.refl e.val)).map ⟨p,cov.continuous⟩
  · intro w hw
    obtain ⟨γ,hγ⟩ := Quotient.exists_rep w.unop
    have hg : MulOpposite.op (Path.Homotopic.Quotient.mk γ) = w := congrArg MulOpposite.op hγ
    have hnull : (γ.map (inclusion U).continuous).Homotopic (Path.refl (p e.val)) := by
      apply Path.Homotopic.Quotient.eq.mp
      change ((toTotal cov U e) (MulOpposite.op (Path.Homotopic.Quotient.mk γ))).unop = (1 : FundamentalGroup X (p e.val))
      rw [hg]
      exact congrArg MulOpposite.unop hw
    let cp := cov.restrictPreimage U
    let t := cp.liftPath γ e γ.source
    have he : (totalInclusion U).comp t = cov.liftPath (γ.map (inclusion U).continuous) e.val (congrArg Subtype.val γ.source) := by
      apply (cov.eq_liftPath_iff' _).mpr
      constructor
      · ext s
        exact congrArg Subtype.val (congrFun (cp.liftPath_lifts γ e γ.source) s)
      · change (t 0).val = e.val
        exact congrArg Subtype.val (cp.liftPath_zero γ e γ.source)
    have ht : t 1 = e := by
      apply Subtype.ext
      change ((totalInclusion U).comp t) 1 = e.val
      rw [he]
      exact lift_loop_closed cov _ hnull
    let δ : Path e e := ⟨t,cp.liftPath_zero γ e γ.source,ht⟩
    refine ⟨MulOpposite.op (Path.Homotopic.Quotient.mk δ),?_⟩
    rw [← hg]
    apply MulOpposite.unop_injective
    change Path.Homotopic.Quotient.mk (δ.map (projection cov U).continuous) = Path.Homotopic.Quotient.mk γ
    apply congrArg Path.Homotopic.Quotient.mk
    apply Path.ext
    funext s
    exact congrFun (cp.liftPath_lifts γ e γ.source) s

/-- This is an equivalence with the actual kernel, not an assumed presentation. -/
def fundamentalKernelEquiv [SimplyConnectedSpace E] :
    (FundamentalGroup (p ⁻¹' U) e)ᵐᵒᵖ ≃* (toTotal cov U e).ker :=
  (MonoidHom.ofInjective (toBase_injective cov U e)).trans
    (MulEquiv.subgroupCongr (toBase_range cov U e))

end EilenbergGanea.CoverKernel


namespace EilenbergGanea.CoverMonodromy
open scoped ContinuousMap
variable {X E G : Type*} [TopologicalSpace X] [TopologicalSpace E]
variable [Group G] [MulAction G E] {p : E → X}
variable (hp : IsQuotientCoveringMap p G) [SimplyConnectedSpace E] (e : E)

def traversalEquiv : (FundamentalGroup X (p e))ᵐᵒᵖ ≃* G :=
  (hp.fundamentalGroupEquiv (⟨e,rfl⟩ : p ⁻¹' {p e})).op.trans (MulEquiv.opOp G).symm

end EilenbergGanea.CoverMonodromy




end

end OAI
end

section
-- module Solutions.OAIEG.RightAngledArtin_ResidualFiniteness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set

namespace EilenbergGanea
universe u
/-! Finite permutation separation for free groups. -/


section FiniteSemidirectSeparation

variable {N D K : Type*} [Group N] [Group D] [Group K]

/-- The right translation action on a group-valued function space. -/
def functionShift (D K : Type*) [Group D] [Group K] : D →* MulAut (D → K) where
  toFun d :=
    { toFun := fun f x => f (x * d)
      invFun := fun f x => f (x * d⁻¹)
      left_inv := by intro f; funext x; simp [mul_assoc]
      right_inv := by intro f; funext x; simp [mul_assoc]
      map_mul' := by intro f g; rfl }
  map_one' := by ext f x; simp
  map_mul' d e := by ext f x; simp [mul_assoc]

end FiniteSemidirectSeparation


end EilenbergGanea

end

end OAI
end

section
-- module Solutions.OAIEG.RightAngledArtin_TraceWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set

namespace EilenbergGanea
/-! Signed trace normal forms and slowly varying barycentric directions. -/

namespace TraceWords

variable {V : Type*} (L : SimpleGraph V)

variable {L}

variable (L)

variable {L}

variable (L)

variable {L}

variable (L)

variable {L}

variable (L)

variable {L}

variable (L)

variable {L}

variable (L)

variable {L}

variable (L)

variable {L}

variable (L)

variable {L}

variable (L)


/-! The occurrence-level normal form is now used to control an actual generator
step. No geometric normal-form or direction-vector assertion is assumed. -/

variable {L}


section RootCounts
variable [LinearOrder V]
variable (L)

variable {L}

/-- Every assigned root occurs as a minimal occurrence, and the root directions
of the whole state form a clique. These assertions simultaneously express
support in a simplex and permanence of old assignments. -/
def RootInvariant (L : SimpleGraph V) (s : Multiset (V × V)) : Prop :=
  (∀ p ∈ s, (p.2,p.2) ∈ s) ∧
    ∀ p ∈ s, ∀ q ∈ s, p.2 ≠ q.2 → L.Adj p.2 q.2

end RootCounts

end TraceWords

end EilenbergGanea

end

end OAI
end

section
-- module Solutions.OAIEG.Cubical_Realization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set Topology

open Classical Set Topology

open Classical Set Topology

namespace EilenbergGanea.CubeRealization

section
variable {G V : Type*} [Group G] [Fintype V]
variable (L : SimpleGraph V) (f : V → G)
variable (comm : ∀ v w, L.Adj v w → Commute (f v) (f w))

/-- Actual finite cliques, including the empty clique. -/
abbrev CliqueIndex := {s : Finset V // (s : Set V).Pairwise L.Adj}

end

end EilenbergGanea.CubeRealization

end

end OAI
end

section
-- module Solutions.OAIEG.SmallHolonomy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set Filter Topology MeasureTheory
open scoped Quaternion ContDiff

namespace EilenbergGanea

variable {Γ S H : Type*} [Group Γ] [Group H]

def labelLift (v : S → Γ) (a : Γ → S → H) :
    FreeGroup S →* ((Γ → H) ⋊[functionShift Γ H] Γ) :=
  FreeGroup.lift (fun s => ⟨fun g => a g s, v s⟩)

def wordValue (v : S → Γ) : FreeGroup S →* Γ := FreeGroup.lift v

def pathProduct (v : S → Γ) (a : Γ → S → H) (w : FreeGroup S) (g : Γ) : H :=
  (labelLift v a w).left g

 theorem labelLift_right (v : S → Γ) (a : Γ → S → H) (w : FreeGroup S) :
    (labelLift v a w).right = wordValue v w := by
  have he : (SemidirectProduct.rightHom : ((Γ → H) ⋊[functionShift Γ H] Γ) →* Γ).comp
      (labelLift v a) = wordValue v := by
    apply FreeGroup.ext_hom
    intro s
    simp [labelLift, wordValue]
  exact congrArg (fun f : FreeGroup S →* Γ => f w) he

@[simp] theorem pathProduct_one (v : S → Γ) (a : Γ → S → H) (g : Γ) :
    pathProduct v a 1 g = 1 := by simp [pathProduct]
@[simp] theorem pathProduct_of (v : S → Γ) (a : Γ → S → H) (s : S) (g : Γ) :
    pathProduct v a (FreeGroup.of s) g = a g s := by simp [pathProduct, labelLift]
 theorem pathProduct_mul (v : S → Γ) (a : Γ → S → H) (w z : FreeGroup S) (g : Γ) :
    pathProduct v a (w*z) g = pathProduct v a w g * pathProduct v a z (g * wordValue v w) := by
  simp only [pathProduct, map_mul, SemidirectProduct.mul_left, Pi.mul_apply, labelLift_right]
  rfl
 theorem pathProduct_inv (v : S → Γ) (a : Γ → S → H) (w : FreeGroup S) (g : Γ) :
    pathProduct v a w⁻¹ g = (pathProduct v a w (g * (wordValue v w)⁻¹))⁻¹ := by
  simp only [pathProduct, map_inv, SemidirectProduct.inv_left, labelLift_right]
  rfl

 def pathChain (v : S → Γ) (w : FreeGroup S) (g : Γ) : (Γ × S) →₀ ℤ :=
  (pathProduct v (fun p s => Multiplicative.ofAdd (Finsupp.single (p,s) 1)) w g).toAdd

@[simp] theorem pathChain_one (v : S → Γ) (g : Γ) : pathChain v 1 g = 0 := by
  simp [pathChain]
@[simp] theorem pathChain_of (v : S → Γ) (s : S) (g : Γ) :
    pathChain v (FreeGroup.of s) g = Finsupp.single (g,s) 1 := by simp [pathChain]
 theorem pathChain_mul (v : S → Γ) (w z : FreeGroup S) (g : Γ) :
    pathChain v (w*z) g = pathChain v w g + pathChain v z (g * wordValue v w) := by
  simp only [pathChain, pathProduct_mul, toAdd_mul]
 theorem pathChain_inv (v : S → Γ) (w : FreeGroup S) (g : Γ) :
    pathChain v w⁻¹ g = -pathChain v w (g * (wordValue v w)⁻¹) := by
  simp only [pathChain, pathProduct_inv, toAdd_inv]

variable {R : Type*}
abbrev NormalFactor (S R : Type*) := FreeGroup S × R × Bool

 def relatorChainMap (v : S → Γ) (r : R → FreeGroup S) :
    ((Γ × R) →₀ ℤ) →ₗ[ℤ] ((Γ × S) →₀ ℤ) :=
  Finsupp.linearCombination ℤ (fun i => pathChain v (r i.2) i.1)

end EilenbergGanea

open scoped Quaternion


end

end OAI
end

section
-- module Solutions.OAIEG.CubicalCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set Topology
open scoped Quaternion

open Classical Topology

open Classical Set Topology

namespace EilenbergGanea.CubeRealization

variable {G Q V : Type*} [Group G] [Group Q] [Fintype V]
variable {L : SimpleGraph V} (f : V → G)
variable (comm : ∀ v w, L.Adj v w → Commute (f v) (f w))
variable (q : G →* Q)

include comm in
omit [Fintype V] in
theorem mappedComm : ∀ v w, L.Adj v w → Commute ((q ∘ f) v) ((q ∘ f) w) :=
  fun v w hvw => (comm v w hvw).map q

end EilenbergGanea.CubeRealization

end

end OAI
end

section
-- module Solutions.OAIEG.IntegralModules
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set

/-! Group-ring augmentation and literal two-syzygy dimension criterion. -/
namespace EilenbergGanea
open CategoryTheory

section CayleyModules
variable {Γ S : Type} [Group Γ]

abbrev IntegralGroupRing (Γ : Type) [Group Γ] := MonoidAlgebra ℤ Γ
abbrev IntegralTrivialModule (Γ : Type) [Group Γ] :=
  (Representation.trivial ℤ Γ ℤ).asModule

def cayleyAugmentation : IntegralGroupRing Γ →ₗ[IntegralGroupRing Γ] IntegralTrivialModule Γ :=
  LinearMap.toSpanSingleton (IntegralGroupRing Γ) _
    ((Representation.trivial ℤ Γ ℤ).asModuleEquiv.symm 1)

@[simp] theorem cayleyAugmentation_single (g : Γ) (n : ℤ) :
    cayleyAugmentation (MonoidAlgebra.single g n) =
      (Representation.trivial ℤ Γ ℤ).asModuleEquiv.symm n := by
  change (MonoidAlgebra.single g n : IntegralGroupRing Γ) •
    ((Representation.trivial ℤ Γ ℤ).asModuleEquiv.symm 1) = _
  rw [Representation.single_smul]
  change (n : ℤ) * 1 = n
  exact mul_one n

def cayleyDifferential (v : S → Γ) :
    (S →₀ IntegralGroupRing Γ) →ₗ[IntegralGroupRing Γ] IntegralGroupRing Γ :=
  Finsupp.linearCombination _ (fun s => MonoidAlgebra.single (v s) 1 - 1)

@[simp] theorem cayleyDifferential_single (v : S → Γ) (s : S) (r : IntegralGroupRing Γ) :
    cayleyDifferential v (Finsupp.single s r) = r * (MonoidAlgebra.single (v s) 1 - 1) := by
  simp [cayleyDifferential]

@[simp] theorem cayleyAugmentation_one :
    cayleyAugmentation (1 : IntegralGroupRing Γ) =
      (Representation.trivial ℤ Γ ℤ).asModuleEquiv.symm 1 :=
  cayleyAugmentation_single (1 : Γ) 1

@[simp] theorem cayleyAugmentation_difference (g : Γ) :
    cayleyAugmentation (MonoidAlgebra.single g 1 - 1) = 0 := by
  rw [map_sub, cayleyAugmentation_single, cayleyAugmentation_one, sub_self]

end CayleyModules
end EilenbergGanea

end

end OAI
end

section
-- module Solutions.OAIEG.Integral_Contraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set

open Classical
namespace FiniteIntegralContraction
variable {I J K : Type*}

def rowEval (r : List (I × ℤ)) (c : I → ℤ) : ℤ :=
  (r.map (fun p => p.2 * c p.1)).sum

def rowsMap (r : J → List (I × ℤ)) : (I → ℤ) →ₗ[ℤ] (J → ℤ) :=
  LinearMap.pi (fun j => ((r j).map (fun p => p.2 • LinearMap.proj p.1)).sum)

@[simp] theorem rowsMap_apply (r : J → List (I × ℤ)) (c : I → ℤ) (j : J) :
    rowsMap r c j = rowEval (r j) c := by
  simp only [rowsMap,LinearMap.pi_apply]
  induction r j with
  | nil => rfl
  | cons p r ih => simp [rowEval,List.map_cons,ih]

def matrixMap [Fintype I] (a : I → J → ℤ) : (I → ℤ) →ₗ[ℤ] (J → ℤ) :=
  Matrix.mulVecLin (fun j i => a i j)

@[simp] theorem matrixMap_single [Fintype I] (a : I → J → ℤ) (i : I) :
    matrixMap a (Pi.single i 1) = a i := by
  funext j
  change ∑ k : I, a k j * ((Pi.single i (1 : ℤ) : I → ℤ) k) = a i j
  simp [Pi.single_apply]

variable [Fintype I] [Fintype J] [Fintype K]
    (edge : J → I × I) (face : K → J × J × J)
    (r₁ : I → List (J × ℤ)) (r₂ : J → List (K × ℤ))
    (a₀ : I → J → ℤ) (a₁ : J → K → ℤ) (root : I)

omit [Fintype J] in
 theorem certificate_bottom (h : ∀ i v, rowEval (r₁ i) (a₀ v) =
    (if i = v then 1 else 0) - (if i = root then 1 else 0)) (v : I) :
    rowsMap r₁ (matrixMap a₀ (Pi.single v 1)) = Pi.single v 1 - Pi.single root 1 := by
  rw [matrixMap_single]
  funext i
  simpa only [rowsMap_apply,Pi.sub_apply,Pi.single_apply] using h i v

end FiniteIntegralContraction

namespace FiniteIntegralContraction
noncomputable section
open Classical
variable {I J K : Type} [Fintype I] [Fintype J] [Fintype K]

def corrected (d₁ : (J → ℤ) →ₗ[ℤ] (I → ℤ)) (h₀ : (I → ℤ) →ₗ[ℤ] (J → ℤ))
    (h₁ : (J → ℤ) →ₗ[ℤ] (K → ℤ)) := h₁.comp (LinearMap.id - h₀.comp d₁)

end
end FiniteIntegralContraction



end

end OAI
end

section
-- module Solutions.OAIEG.Presentation_KernelCycles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set Filter Topology MeasureTheory
open scoped Quaternion ContDiff



namespace EilenbergGanea.KernelCycles
open Classical
variable {G A : Type*} [Group G] (a : A → G)
abbrev Kernel := (wordValue a).ker
abbrev AbKernel := Additive (Abelianization (Kernel a))

end EilenbergGanea.KernelCycles


end

end OAI
end

section
-- module Solutions.OAIEG.SeedChains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set

namespace EilenbergGanea.SeedChainCertificate
def edgeData_0 : List (Fin 103 × Fin 103) := [
  (0,7),
  (0,9),
  (0,10),
  (0,12),
  (0,13),
  (0,16),
  (0,19),
  (0,22),
  (0,25),
  (0,28),
  (0,31),
  (0,34),
  (0,37),
  (0,40),
  (0,43),
  (0,46)]

def edgeData_1 : List (Fin 103 × Fin 103) := [
  (0,49),
  (0,52),
  (0,55),
  (0,58),
  (0,60),
  (0,61),
  (0,63),
  (0,64),
  (0,66),
  (0,67),
  (0,69),
  (0,70),
  (0,72),
  (0,73),
  (0,75),
  (0,76)]

def edgeData_2 : List (Fin 103 × Fin 103) := [
  (0,78),
  (0,79),
  (0,81),
  (0,82),
  (0,84),
  (0,85),
  (0,87),
  (0,88),
  (0,90),
  (0,91),
  (0,93),
  (0,94),
  (0,96),
  (0,97),
  (0,99),
  (0,100)]

def edgeData_3 : List (Fin 103 × Fin 103) := [
  (0,102),
  (1,7),
  (1,8),
  (1,14),
  (1,17),
  (1,35),
  (1,38),
  (1,45),
  (1,51),
  (1,57),
  (1,58),
  (1,59),
  (1,61),
  (1,62),
  (1,79),
  (1,80)]

def edgeData_10 : List (Fin 103 × Fin 103) := [
  (5,26),
  (5,27),
  (5,28),
  (5,29),
  (5,30),
  (5,31),
  (5,32),
  (5,33),
  (5,58),
  (5,59),
  (5,60),
  (5,61),
  (5,62),
  (5,63),
  (5,64),
  (5,65)]

def edgeData_11 : List (Fin 103 × Fin 103) := [
  (5,66),
  (5,67),
  (5,68),
  (5,69),
  (5,70),
  (5,71),
  (5,72),
  (5,73),
  (5,74),
  (5,75),
  (5,76),
  (5,77),
  (5,78),
  (6,34),
  (6,35),
  (6,36)]

def edgeData_12 : List (Fin 103 × Fin 103) := [
  (6,37),
  (6,38),
  (6,39),
  (6,40),
  (6,41),
  (6,42),
  (6,43),
  (6,44),
  (6,45),
  (6,46),
  (6,47),
  (6,48),
  (6,49),
  (6,50),
  (6,51),
  (6,52)]

def edgeData_13 : List (Fin 103 × Fin 103) := [
  (6,53),
  (6,54),
  (6,55),
  (6,56),
  (6,57),
  (6,79),
  (6,80),
  (6,81),
  (6,82),
  (6,83),
  (6,84),
  (6,85),
  (6,86),
  (6,87),
  (6,88),
  (6,89)]

def edgeData_14 : List (Fin 103 × Fin 103) := [
  (6,90),
  (6,91),
  (6,92),
  (6,93),
  (6,94),
  (6,95),
  (6,96),
  (6,97),
  (6,98),
  (6,99),
  (6,100),
  (6,101),
  (6,102),
  (7,58),
  (7,61),
  (7,79)]

def edgeData_15 : List (Fin 103 × Fin 103) := [
  (7,82),
  (7,90),
  (7,96),
  (7,102),
  (8,59),
  (8,62),
  (8,80),
  (8,83),
  (8,89),
  (8,95),
  (8,101),
  (9,60),
  (9,63),
  (9,81),
  (9,84),
  (9,88)]

def edgeData_16 : List (Fin 103 × Fin 103) := [
  (9,94),
  (9,100),
  (10,66),
  (10,69),
  (10,72),
  (10,75),
  (10,78),
  (10,85),
  (10,91),
  (10,97),
  (11,65),
  (11,68),
  (11,71),
  (11,74),
  (11,77),
  (11,86)]

def edgeData_17 : List (Fin 103 × Fin 103) := [
  (11,92),
  (11,98),
  (12,64),
  (12,67),
  (12,70),
  (12,73),
  (12,76),
  (12,87),
  (12,93),
  (12,99),
  (13,58),
  (13,78),
  (14,58),
  (14,59),
  (15,59),
  (15,60)]

def edgeData_18 : List (Fin 103 × Fin 103) := [
  (16,60),
  (16,61),
  (17,61),
  (17,62),
  (18,62),
  (18,63),
  (19,63),
  (19,64),
  (20,64),
  (20,65),
  (21,65),
  (21,66),
  (22,66),
  (22,67),
  (23,67),
  (23,68)]

def edgeData_19 : List (Fin 103 × Fin 103) := [
  (24,68),
  (24,69),
  (25,69),
  (25,70),
  (26,70),
  (26,71),
  (27,71),
  (27,72),
  (28,72),
  (28,73),
  (29,73),
  (29,74),
  (30,74),
  (30,75),
  (31,75),
  (31,76)]

def edgeData_20 : List (Fin 103 × Fin 103) := [
  (32,76),
  (32,77),
  (33,77),
  (33,78),
  (34,79),
  (34,102),
  (35,79),
  (35,80),
  (36,80),
  (36,81),
  (37,81),
  (37,82),
  (38,82),
  (38,83),
  (39,83),
  (39,84)]

def edgeData_21 : List (Fin 103 × Fin 103) := [
  (40,84),
  (40,85),
  (41,85),
  (41,86),
  (42,86),
  (42,87),
  (43,87),
  (43,88),
  (44,88),
  (44,89),
  (45,89),
  (45,90),
  (46,90),
  (46,91),
  (47,91),
  (47,92)]

def edgeData_22 : List (Fin 103 × Fin 103) := [
  (48,92),
  (48,93),
  (49,93),
  (49,94),
  (50,94),
  (50,95),
  (51,95),
  (51,96),
  (52,96),
  (52,97),
  (53,97),
  (53,98),
  (54,98),
  (54,99),
  (55,99),
  (55,100)]

def edgeData_23 : List (Fin 103 × Fin 103) := [
  (56,100),
  (56,101),
  (57,101),
  (57,102)]

end EilenbergGanea.SeedChainCertificate


end

end OAI
end

section
-- module Solutions.OAIEG.SeedContraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set

namespace EilenbergGanea.SeedChainCertificate
def d1Data_0 : List (List (Fin 372 × ℤ)) := [
  [(0,-1),(1,-1),(2,-1),(3,-1),(4,-1),(5,-1),(6,-1),(7,-1),(8,-1),(9,-1),(10,-1),(11,-1),(12,-1),(13,-1),(14,-1),(15,-1),(16,-1),(17,-1),(18,-1),(19,-1),(20,-1),(21,-1),(22,-1),(23,-1),(24,-1),(25,-1),(26,-1),(27,-1),(28,-1),(29,-1),(30,-1),(31,-1),(32,-1),(33,-1),(34,-1),(35,-1),(36,-1),(37,-1),(38,-1),(39,-1),(40,-1),(41,-1),(42,-1),(43,-1),(44,-1),(45,-1),(46,-1),(47,-1),(48,-1)],
  [(49,-1),(50,-1),(51,-1),(52,-1),(53,-1),(54,-1),(55,-1),(56,-1),(57,-1),(58,-1),(59,-1),(60,-1),(61,-1),(62,-1),(63,-1),(64,-1),(65,-1),(66,-1),(67,-1),(68,-1),(69,-1),(70,-1),(71,-1)],
  [(72,-1),(73,-1),(74,-1),(75,-1),(76,-1),(77,-1),(78,-1),(79,-1),(80,-1),(81,-1),(82,-1),(83,-1),(84,-1),(85,-1),(86,-1),(87,-1),(88,-1),(89,-1),(90,-1),(91,-1),(92,-1),(93,-1),(94,-1)],
  [(95,-1),(96,-1),(97,-1),(98,-1),(99,-1),(100,-1),(101,-1),(102,-1),(103,-1),(104,-1),(105,-1),(106,-1),(107,-1),(108,-1),(109,-1),(110,-1),(111,-1),(112,-1),(113,-1),(114,-1),(115,-1),(116,-1),(117,-1),(118,-1),(119,-1),(120,-1)],
  [(121,-1),(122,-1),(123,-1),(124,-1),(125,-1),(126,-1),(127,-1),(128,-1),(129,-1),(130,-1),(131,-1),(132,-1),(133,-1),(134,-1),(135,-1),(136,-1),(137,-1),(138,-1),(139,-1),(140,-1),(141,-1),(142,-1),(143,-1),(144,-1),(145,-1),(146,-1)],
  [(147,-1),(148,-1),(149,-1),(150,-1),(151,-1),(152,-1),(153,-1),(154,-1),(155,-1),(156,-1),(157,-1),(158,-1),(159,-1),(160,-1),(161,-1),(162,-1),(163,-1),(164,-1),(165,-1),(166,-1),(167,-1),(168,-1),(169,-1),(170,-1),(171,-1),(172,-1),(173,-1),(174,-1),(175,-1),(176,-1),(177,-1),(178,-1),(179,-1),(180,-1),(181,-1),(182,-1),(183,-1),(184,-1),(185,-1),(186,-1),(187,-1),(188,-1)],
  [(189,-1),(190,-1),(191,-1),(192,-1),(193,-1),(194,-1),(195,-1),(196,-1),(197,-1),(198,-1),(199,-1),(200,-1),(201,-1),(202,-1),(203,-1),(204,-1),(205,-1),(206,-1),(207,-1),(208,-1),(209,-1),(210,-1),(211,-1),(212,-1),(213,-1),(214,-1),(215,-1),(216,-1),(217,-1),(218,-1),(219,-1),(220,-1),(221,-1),(222,-1),(223,-1),(224,-1),(225,-1),(226,-1),(227,-1),(228,-1),(229,-1),(230,-1),(231,-1),(232,-1),(233,-1),(234,-1),(235,-1),(236,-1)],
  [(0,1),(49,1),(237,-1),(238,-1),(239,-1),(240,-1),(241,-1),(242,-1),(243,-1)],
  [(50,1),(72,1),(244,-1),(245,-1),(246,-1),(247,-1),(248,-1),(249,-1),(250,-1)],
  [(1,1),(73,1),(251,-1),(252,-1),(253,-1),(254,-1),(255,-1),(256,-1),(257,-1)],
  [(2,1),(95,1),(258,-1),(259,-1),(260,-1),(261,-1),(262,-1),(263,-1),(264,-1),(265,-1)],
  [(96,1),(121,1),(266,-1),(267,-1),(268,-1),(269,-1),(270,-1),(271,-1),(272,-1),(273,-1)],
  [(3,1),(122,1),(274,-1),(275,-1),(276,-1),(277,-1),(278,-1),(279,-1),(280,-1),(281,-1)],
  [(4,1),(147,1),(282,-1),(283,-1)],
  [(51,1),(148,1),(284,-1),(285,-1)],
  [(74,1),(149,1),(286,-1),(287,-1)]]

def d1Data_1 : List (List (Fin 372 × ℤ)) := [
  [(5,1),(150,1),(288,-1),(289,-1)],
  [(52,1),(151,1),(290,-1),(291,-1)],
  [(75,1),(152,1),(292,-1),(293,-1)],
  [(6,1),(153,1),(294,-1),(295,-1)],
  [(123,1),(154,1),(296,-1),(297,-1)],
  [(97,1),(155,1),(298,-1),(299,-1)],
  [(7,1),(156,1),(300,-1),(301,-1)],
  [(124,1),(157,1),(302,-1),(303,-1)],
  [(98,1),(158,1),(304,-1),(305,-1)],
  [(8,1),(159,1),(306,-1),(307,-1)],
  [(125,1),(160,1),(308,-1),(309,-1)],
  [(99,1),(161,1),(310,-1),(311,-1)],
  [(9,1),(162,1),(312,-1),(313,-1)],
  [(126,1),(163,1),(314,-1),(315,-1)],
  [(100,1),(164,1),(316,-1),(317,-1)],
  [(10,1),(165,1),(318,-1),(319,-1)]]

def d1Data_2 : List (List (Fin 372 × ℤ)) := [
  [(127,1),(166,1),(320,-1),(321,-1)],
  [(101,1),(167,1),(322,-1),(323,-1)],
  [(11,1),(189,1),(324,-1),(325,-1)],
  [(53,1),(190,1),(326,-1),(327,-1)],
  [(76,1),(191,1),(328,-1),(329,-1)],
  [(12,1),(192,1),(330,-1),(331,-1)],
  [(54,1),(193,1),(332,-1),(333,-1)],
  [(77,1),(194,1),(334,-1),(335,-1)],
  [(13,1),(195,1),(336,-1),(337,-1)],
  [(102,1),(196,1),(338,-1),(339,-1)],
  [(128,1),(197,1),(340,-1),(341,-1)],
  [(14,1),(198,1),(342,-1),(343,-1)],
  [(78,1),(199,1),(344,-1),(345,-1)],
  [(55,1),(200,1),(346,-1),(347,-1)],
  [(15,1),(201,1),(348,-1),(349,-1)],
  [(103,1),(202,1),(350,-1),(351,-1)]]

def d1Data_3 : List (List (Fin 372 × ℤ)) := [
  [(129,1),(203,1),(352,-1),(353,-1)],
  [(16,1),(204,1),(354,-1),(355,-1)],
  [(79,1),(205,1),(356,-1),(357,-1)],
  [(56,1),(206,1),(358,-1),(359,-1)],
  [(17,1),(207,1),(360,-1),(361,-1)],
  [(104,1),(208,1),(362,-1),(363,-1)],
  [(130,1),(209,1),(364,-1),(365,-1)],
  [(18,1),(210,1),(366,-1),(367,-1)],
  [(80,1),(211,1),(368,-1),(369,-1)],
  [(57,1),(212,1),(370,-1),(371,-1)],
  [(19,1),(58,1),(168,1),(237,1),(282,1),(284,1)],
  [(59,1),(81,1),(169,1),(244,1),(285,1),(286,1)],
  [(20,1),(82,1),(170,1),(251,1),(287,1),(288,1)],
  [(21,1),(60,1),(171,1),(238,1),(289,1),(290,1)],
  [(61,1),(83,1),(172,1),(245,1),(291,1),(292,1)],
  [(22,1),(84,1),(173,1),(252,1),(293,1),(294,1)]]

def d1Data_4 : List (List (Fin 372 × ℤ)) := [
  [(23,1),(131,1),(174,1),(274,1),(295,1),(296,1)],
  [(105,1),(132,1),(175,1),(266,1),(297,1),(298,1)],
  [(24,1),(106,1),(176,1),(258,1),(299,1),(300,1)],
  [(25,1),(133,1),(177,1),(275,1),(301,1),(302,1)],
  [(107,1),(134,1),(178,1),(267,1),(303,1),(304,1)],
  [(26,1),(108,1),(179,1),(259,1),(305,1),(306,1)],
  [(27,1),(135,1),(180,1),(276,1),(307,1),(308,1)],
  [(109,1),(136,1),(181,1),(268,1),(309,1),(310,1)],
  [(28,1),(110,1),(182,1),(260,1),(311,1),(312,1)],
  [(29,1),(137,1),(183,1),(277,1),(313,1),(314,1)],
  [(111,1),(138,1),(184,1),(269,1),(315,1),(316,1)],
  [(30,1),(112,1),(185,1),(261,1),(317,1),(318,1)],
  [(31,1),(139,1),(186,1),(278,1),(319,1),(320,1)],
  [(113,1),(140,1),(187,1),(270,1),(321,1),(322,1)],
  [(32,1),(114,1),(188,1),(262,1),(283,1),(323,1)],
  [(33,1),(62,1),(213,1),(239,1),(324,1),(326,1)]]

def d1Data_5 : List (List (Fin 372 × ℤ)) := [
  [(63,1),(85,1),(214,1),(246,1),(327,1),(328,1)],
  [(34,1),(86,1),(215,1),(253,1),(329,1),(330,1)],
  [(35,1),(64,1),(216,1),(240,1),(331,1),(332,1)],
  [(65,1),(87,1),(217,1),(247,1),(333,1),(334,1)],
  [(36,1),(88,1),(218,1),(254,1),(335,1),(336,1)],
  [(37,1),(115,1),(219,1),(263,1),(337,1),(338,1)],
  [(116,1),(141,1),(220,1),(271,1),(339,1),(340,1)],
  [(38,1),(142,1),(221,1),(279,1),(341,1),(342,1)],
  [(39,1),(89,1),(222,1),(255,1),(343,1),(344,1)],
  [(66,1),(90,1),(223,1),(248,1),(345,1),(346,1)],
  [(40,1),(67,1),(224,1),(241,1),(347,1),(348,1)],
  [(41,1),(117,1),(225,1),(264,1),(349,1),(350,1)],
  [(118,1),(143,1),(226,1),(272,1),(351,1),(352,1)],
  [(42,1),(144,1),(227,1),(280,1),(353,1),(354,1)],
  [(43,1),(91,1),(228,1),(256,1),(355,1),(356,1)],
  [(68,1),(92,1),(229,1),(249,1),(357,1),(358,1)]]

def d1Data_6 : List (List (Fin 372 × ℤ)) := [
  [(44,1),(69,1),(230,1),(242,1),(359,1),(360,1)],
  [(45,1),(119,1),(231,1),(265,1),(361,1),(362,1)],
  [(120,1),(145,1),(232,1),(273,1),(363,1),(364,1)],
  [(46,1),(146,1),(233,1),(281,1),(365,1),(366,1)],
  [(47,1),(93,1),(234,1),(257,1),(367,1),(368,1)],
  [(70,1),(94,1),(235,1),(250,1),(369,1),(370,1)],
  [(48,1),(71,1),(236,1),(243,1),(325,1),(371,1)]]

def d1Data : List (List (Fin 372 × ℤ)) := [d1Data_0,d1Data_1,d1Data_2,d1Data_3,d1Data_4,d1Data_5,d1Data_6].flatten

def h0CodeData_0 : List (ℕ) := [
  30845763132983623646676132847120415275432388327850830776275238156836250477758584148305225547723898846914127085549256666623981397233701038190608963867846750005174775441901880612974669250480303065484027051800816630341467198805,
  30845763132983623646676132847120415275432388327850830776275238156836250477758584148305225547723898846914127085549256666623981397233701038190608963867846750005174775441901880612974669250480303065167114401743759279967291397462,
  30845763132983623646676132847120415275432388327850830776275238156836250477758584148305225547723898846914127085549256666623981397233701038190608963867846750005174775441901880612974580047499508942991460908927726036895443277145,
  30845763132983623646676132847120415275432388327850830776275238156836250477758584148305225547723898846914127085549256666623981397233701038190608963867846750005174775440332605179127999059521355709682110447775227769225458570597,
  30845763132983623646676132847120415275432388327850830776275238156836250477758584148305225547723898846914127085549256666623981397233701038190608963867818480452138321292628547852962782554227063323134017148470870931120785282453,
  30845763132983623646676132847120415275432388327850830776275238156836250477758584148305225547723898846914127085549256666623981397233701006361921833641501652060710894045368114183781018220226386875789505889593007828205433083477,
  30845763132983623646676132847120415275432388327850830776275238156836250477758584148305225547723898846914127084933600319805317659541841036625864998163475823904152171255209796171635266570836387262136116819224009742737909044565,
  30845763132983623646676132847120415275432388327850830776275238156836250477758584148305225547723898846914127085549256666623981397233701038190608963867846750005174775441901880612974669250480303065484027051800816630341467198806,
  30845763132983623646676132847120415275432388327850830776275238156836250477758584148305225547723898846914127085549256666623981397233701038190608963867846750005174775441901880612974669250480303066434765001971988681463994602838,
  30845763132983623646676132847120415275432388327850830776275238156836250477758584148305225547723898846914127085549256666623981397233701038190608963867846750005174775441901880612974669250480303065484027051800816630341467198809,
  30845763132983623646676132847120415275432388327850830776275238156836250477758584148305225547723898846914127085549256666623981397233701038190608963867846750005174775441901880612974669250480303065484027051800816630341467198821,
  30845763132983623646676132847120415275432388327850830776275238156836250477758584148305225547723898846914127085549256666623981397233701038190608963867846750005174775446609706914514679823357145132889776863877583213689493083493,
  30845763132983623646676132847120415275432388327850830776275238156836250477758584148305225547723898846914127085549256666623981397233701038190608963867846750005174775441901880612974669250480303065484027051800816630341467198869,
  30845763132983623646676132847120415275432388327850830776275238156836250477758584148305225547723898846914127085549256666623981397233701038190608963867846750005174775441901880612974669250480303065484027051800816630341467199061,
  30845763132983623646676132847120415275432388327850829810140857402521664303920611415308389472992066420305377421240443803744195824843594904142167318387202259389270767566357586271705003989733389129756858685030629456371141399893,
  30845763132983623646676132847120415275432388327850768943674869880702735352128329236507716764886623543954148569785233442317704764266908459090343653106599350587318271407067042771716092562677811178945251578508837479747941651797]

def h0CodeData_1 : List (ℕ) := [
  30845763132983623646676132847120415275432388327850830776275238156836250477758584148305225547723898846914127085549256666623981397233701038190608963867846750005174775441901880612974669250480303065484027051800816630341467199829,
  30845763132983623646676132847120415275432388327846873489851668484291282437422269793264663446138279457475502076651770311022276887358975975773629075148013187262358517212472258772425761231120822327002396761114150926385134523733,
  30845763132983623646676132847120415275432388327597564445166779113958295896234465425709251046244257922842126516110129908114892765251297043503896085798498734464934248758406082817844556011473535802659688447854211313253385327957,
  30845763132983623646676132847120415275432388327850830776275238156836250477758584148305225547723898846914127085549256666623981397233701038190608963867846750005174775441901880612974669250480303065484027051800816630341467202901,
  30845763132983623646676132847120415275432388311641785585333859412647157260214985902162857453026879706306090641445144122042308950359845378240984767429573755429781067698170821724647421954047198244726356399218075281173064799573,
  30845763132983623646676132847120415275432387290471938556026998528734284554968296395193667487114673847999794662886053813396944797306938801414660391818375097179977479843114111760030842278761594536993105286505366061439062988117,
  30845763132983623646676132847120415275432388327850830776275238156836250477758584148305225547723898846914127085549256666623981397233701038190608963867846750005174775441901880612974669250480303065484027051800816630341467215189,
  30845763132983623646676132847120415275432321935601728680387901958310431419180167949165509668733498916396852035104274060093639001920917884529900352701660969192547857119484674024569743060482957242065034072891963332088995075413,
  30845763132983623646676132847120415275428139223908296639485721451183830728739947403363409292338303293808523857070369848682068097215579203905257849231956777997052002807200658955059393090650170366668476401634137988188840744277,
  30845763132983623646676132847120415275432388327850830776275238156836250477758584148305225547723898846914127085549256666623981397233701038190608963867846750005174775441901880612974669250480303065484027051800816630341467264341,
  30845763132983623646676132847120415275160445675528646021746168995081386540565832472028985203045783448155520462900500318341530196073903643928137627170888541485317326821023694506396995021351810341288785441133113316595731879253,
  30845763132983623646676132847120415258028058579231006486414811804524958497422476866625843488324513326363303236028850376547104523006667805392443415262521404734298063705697969792003518586256768716988563969066723686703837828437,
  30845763132983623646676132847120415275432388327850830776275238156836250477758584148305225547723898846914127085549256666623981397233701038190608963867846750005174775441901880612974669250480303065484027051800816630341467460949,
  30845763132983623646676132847120414161555284416182076225207951608913563736247718120824773746163225531661400716243254101703861446703574139108013853127024652669065224324851588070821026740174104761774389756814544781890911819093,
  30845763132983623646676132847120343987297737981050539507968899089784299021063158389556310247840806670739639449965092511736304563305579496904521876455232520494163503950683157915141548590883611628067240172662124506936820192597,
  30845763132983623646676132847120415275432388327850830776275238156836250477758584148305225547723898846914127085549256666623981397233701038190608963867846750005174775441901880612974669250480303065484027051800816630341468247381]

def h0CodeData_2 : List (ℕ) := [
  30845763132983623646676132847115852834814766132632189604669537865511357249251335588374646355205999571746918408162750753812664025833922395881035369460536061300453400003903627951654947036292051070809666786855345442167647982933,
  30845763132983623646676132846828419075904567833857795793510419512043083853294676312748157226578345236212771732812878246699669627647867930377898921799962672903006747410013710288512447542432175406324970095013959426111394108757,
  30845763132983623646676132847120415275432388327850830776275238156836250477758584148305225547723898846914127085549256666623981397233701038190608963867846750005174775441901880612974669250480303065484027051800816630341471393109,
  30845763132983623646676132828432658505651876712296591879326844890073586512068482672652852994408467762027384510421037791468028143740382138177166271523265815466420981401058979847392479935400132879304381816335150915194216338773,
  30845763132983623646676131651103982009479644932379541371578069084025756673592089706553382135536309414162602277343248656642973173661291437330276653814666939524931956827956231615714553085349411149986731977570992283227119768917,
  30845763132983623646676132847120415275432388327850830776275238156836250477758584148305225547723898846914127085549256666623981397233701038190608963867846750005174775441901880612974669250480303065484027051800816630341483976021,
  30845763132983623646676056302068686254456811017688308875656417496964647011102939876187247167718175150816539360364744027839455088599486583129341120464338879269634384149380344788327234682103220473657142283383184104262062134613,
  30845763132983623646671233963809757932995440477449429136670715925053628611797350732754609227357582296668512673740447784414297644643975914269466986043343022930589732720523587835538856874347017188563401802236837718214864885077,
  30845763132983623646676132847120415275432388327850830776275238156836250477758584148305225547723898846914127085549256666623981397233701038190608963867846750005174775441901880612974669250480303065484027051800816630341534307669,
  30845763132983623646362604315238345359467725902161125841585815322748451056239645553065781044279639631194804729785488205204221231491293107237522383099608217231732041273691142857082677177950006942564010796364177282060206298453,
  30845763132983623626610306806667940653693993083709714956152176775217087500546514052980777327291309040877496316668075135759330789719593457193067794700580652504839788676414664235887176608541351198602985570487942451625918289237,
  30845763132983623646676132847120415275432388327850830776275238156836250477758584148305225547723898846914127085549256666623981397233701038190608963867846750005174775441901880612974669250480303065484027051800816630341735634261,
  30845763132983622362463266258162039484175092702819418288399309733209819936186098047540539440038151260569757877153638691286342516330815854347974137162816509983735622450720032479375140166387383585097367714305045637686931838293,
  30845763132983541457052671153784364634965468325840431552215819044744695817119473699365314655836053320874497748229706245015093019449049272261980054745911388633068984006263600062604807868533456320737811318184178881013583533397,
  30845763132983623646676132847120415275432388327850830776275238156836250477758584148305225547723898846914127085549256666623981397233701038190608963867846750005174775441901880612974669250480303065484027051800816630342540940629,
  30845763132978363510774584473613174285549508199185280436472414982976752196855515416150928466901785180377849497098029683655125219015988018758358780063983622190404123561051925389303540805882111401726147564786823795606430242133]

def h0CodeData_6 : List (ℕ) := [
  30845763132983623646676132847120415275432388327850830776275238156836250477758584148305225547723898846914127085549256666623981397233701038190608963867846750005174775441901880612974669250480303065484336536810637975410191979861,
  30845763132983623646676132847120415275432388327850830776275238156836250477758584148305225547723898846914127085549256666623981397233701038190608963867846750005174775441901880612974669250480303065485264991840102010616366323029,
  30845763132983623646676132847120415275432388327850830776275238156836250477758584148305225547723898846914127085549256666623981397233701038190608963867848516852239553824662188476628741978037183193578986066733349375426751190373,
  30845763132983623646676132847120415275432388327850830776275238156836250477758584148305225547723898846914127085549256666623981397233701038190608963867846750005174775441901880612974669250480303065488978811957958151441063695701,
  30845763132983623646676132847120415275432388327850830776275238156836250477758584148305225547723898846914127085549256666623981397233701038190608963867846750005174775441901880612974669250480303065503834092429382714739853186389,
  30845763132983623646676132847120415275432388327850830776275238156836250477758584148305225547723898846914127085549256666623981397233701038190608963867846750005174775441901880612974670644276877973331060747726151320489885521238,
  30845763132983623646676132847120415275432388327850830776275238156836250477758584148305225547723898846914127085549256666623981397233701038190608963867846750005174775441901880612974669250480303065563255214315080967935011149141]

def d1Row (v : Fin 103) : List (Fin 372 × ℤ) := d1Data.getD v.val []

def rowEval {I : Type*} (r : List (I × ℤ)) (c : I → ℤ) : ℤ :=
  (r.map (fun p => p.2 * c p.1)).sum

theorem fin_ite {n : ℕ} (i j : Fin n) (a b : ℤ) :
    @ite ℤ (i = j) (Classical.propDecidable _) a b =
      @ite ℤ (i = j) (instDecidableEqFin n i j) a b := by
  by_cases h : i = j <;> simp [h]

local instance instDecidableEqFinOfNatNat_solutions : DecidableEq (Fin 103) := Classical.decEq _

noncomputable def d₁ := FiniteIntegralContraction.rowsMap d1Row

end EilenbergGanea.SeedChainCertificate


end

end OAI
end


