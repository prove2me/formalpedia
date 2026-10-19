-- Prove2me | Definitions.Def_OAI_GroupTheory_Kervaire_Conjugation
-- name    : OAI_GroupTheory_Kervaire_Conjugation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T17:05:58.671379+00:00
-- url     : https://prove2.me/theorems/9c98413b-3f89-4de5-ab77-54e81627815e
-- title:
--   Conjugating ribbon values by letters and coefficients
-- statement:
--   These notions belong to a formal proof of the Kervaire conjecture in its unimodular form. For a group $A$ and an element $w$ of the free product $A*\langle t\rangle$ whose exponent sum in $t$ is $\pm1$, the natural map from $A$ to $(A*\langle t\rangle)/\langle\!\langle w\rangle\!\rangle$ is injective, so adjoining one generator and one such relation never kills a nontrivial group. The proof writes $w$ with unit $t$-exponents and represents elements of the normal closure by planar ribbon diagrams. These are pairs of permutations of darts satisfying an Euler equation, whose disks read off copies of the relator. A capping induction removes cancelling pairs of darts. Its key rigidity step at relator corners is proved analytically, with the fractional spectral phase of unitary operators over the group von Neumann algebra of $A$, which is subadditive under a trace.
--
--   1. **Conjugation by the letter.** From an outer ribbon with value $w$, a ribbon with value $t^{\pm1}wt^{\mp1}$. It is obtained by whiskering two new darts of opposite signs onto the boundary circle at the marker.
--   2. **Conjugation by a coefficient.** From an outer ribbon with value $w$ and $g\in A$, a ribbon with value $gwg^{-1}$. It is obtained by shifting the potential at the marker.
--
--   In both constructions the edge involution never sends a dart to the marker. So realized elements are closed under conjugation by generators of $A*\langle t\rangle$, as in
--   $$
--   w\ \mapsto\ g\,w\,g^{-1}.
--   $$
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/Conjugation.lean

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/Conjugation.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the Kervaire mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_Kervaire
import Definitions.Def_OAI_GroupTheory_Kervaire_Reductions
import Definitions.Def_OAI_GroupTheory_Kervaire_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Kervaire_Components
import Definitions.Def_OAI_GroupTheory_Kervaire_Suppression
import Definitions.Def_OAI_GroupTheory_Kervaire_ComponentFibers
import Definitions.Def_OAI_GroupTheory_Kervaire_StrongLimits
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralMeasures
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralLogarithm
import Definitions.Def_OAI_GroupTheory_Kervaire_ScalarPhase
import Definitions.Def_OAI_GroupTheory_Kervaire_TraceCalculus
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralApproximation
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseSubadditivity
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseNaturality
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseGrids
import Definitions.Def_OAI_GroupTheory_Kervaire_RegularOperators
import Definitions.Def_OAI_GroupTheory_Kervaire_MatrixTrace
import Definitions.Def_OAI_GroupTheory_Kervaire_MatrixShifts
import Definitions.Def_OAI_GroupTheory_Kervaire_WeightedCycles
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseFaithfulness
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseDimension
import Definitions.Def_OAI_GroupTheory_Kervaire_MixingOperators
import Definitions.Def_OAI_GroupTheory_Kervaire_HaarCurrents
import Definitions.Def_OAI_GroupTheory_Kervaire_CurrentPullback
import Definitions.Def_OAI_GroupTheory_Kervaire_IncidenceSpaces
import Definitions.Def_OAI_GroupTheory_Kervaire_IncidenceTangent
import Definitions.Def_OAI_GroupTheory_Kervaire_UnitaryHomotopy
import Definitions.Def_OAI_GroupTheory_Kervaire_IncidenceDegree
import Definitions.Def_OAI_GroupTheory_Kervaire_CurrentExistence
import Definitions.Def_OAI_GroupTheory_Kervaire_SignedIncidence
import Definitions.Def_OAI_GroupTheory_Kervaire_FixedSpaces
import Definitions.Def_OAI_GroupTheory_Kervaire_Traversal
import Definitions.Def_OAI_GroupTheory_Kervaire_BoundaryFlow
import Definitions.Def_OAI_GroupTheory_Kervaire_RelatorRigidity
import Definitions.Def_OAI_GroupTheory_Kervaire_VertexJoin
import Definitions.Def_OAI_GroupTheory_Kervaire_Circles
import Definitions.Def_OAI_GroupTheory_Kervaire_Splicing
import Definitions.Def_OAI_GroupTheory_Kervaire_Capping
import Definitions.Def_OAI_GroupTheory_Kervaire_OuterRibbon
import Definitions.Def_OAI_GroupTheory_Kervaire_RibbonProducts

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

noncomputable section

namespace KervaireRibbon

section
open Equiv Equiv.Perm Monoid Multiplicative
open scoped Classical
variable {V I D A : Type*} [Fintype V] [Fintype I] [Fintype D] [DecidableEq D] [Group A]

def OuterRibbon.conjLetter {ρ : Perm I} {a : I → A} {s : I → ℤ} {o : D} {l : List D}
    (r : OuterRibbon (V := V) ρ a s o l) (n : ℤ) (hn : n=1 ∨ n = -1) :
    OuterRibbon (V := V) ρ a s (Sum.inl o) (Sum.inr false :: l.map Sum.inl ++ [Sum.inr true]) := by
  let σ := whisker r.σ o
  let θ := r.θ.sumCongr (swap false true)
  let t : D ⊕ Bool → ℤ := Sum.elim r.t (fun b ↦ if b then -n else n)
  let u : D ⊕ Bool → A := Sum.elim r.u (fun _ ↦ r.u o)
  have hd (vi : V × I) : r.atlas.disk vi ≠ o := fun he ↦ r.disjoint vi (by simp [he])
  have hs (v : V) (i : I) : r.σ (r.atlas.disk (v,i)) ≠ o := by rw [r.atlas.next]; exact hd _
  let b : DiskAtlas (V := V) ρ a s σ t := {
    disk := r.atlas.disk.trans ⟨Sum.inl,Sum.inl_injective⟩
    ε := r.atlas.ε
    polarity := r.atlas.polarity
    next := by intro v i; change whisker r.σ o (Sum.inl (r.atlas.disk (v,i))) = _
               rw [whisker_inl _ _ _ (hd _),ite_eq_right (hs _ _)]; exact congrArg Sum.inl (r.atlas.next v i)
    sign := r.atlas.sign }
  refine {
    σ := σ, θ := θ, t := t, u := u, atlas := b
    involutive := ?_, planar' := planar_whisker _ _ _ r.marker r.planar'
    opposite := ?_, marker := congrArg Sum.inl r.marker, marker_sign := r.marker_sign
    circle := circle_whisker _ _ _ r.circle (List.nodup_cons.mp r.nodup).1
    nodup := ?_, unit := ?_, disjoint := ?_, cover := ?_, corners := ?_ }
  · rintro (d|d)
    · exact congrArg Sum.inl (r.involutive d)
    · simp only [θ,Equiv.Perm.sumCongr_apply,Sum.map_inr,swap_apply_self]
  · rintro (d|d)
    · exact r.opposite d
    · cases d <;> simp [θ,t]
  · have hl : (l.map (Sum.inl : D → D ⊕ Bool) ++ [Sum.inr true]).Nodup := by
      apply List.nodup_append.mpr
      refine ⟨r.nodup.of_cons.map Sum.inl_injective,by simp,?_⟩
      intro d hd e he hde
      obtain ⟨x,_,rfl⟩ := List.mem_map.mp hd
      have he' : e = Sum.inr true := List.mem_singleton.mp he
      exact Sum.inl_ne_inr (hde.trans he')
    apply List.nodup_cons.mpr
    constructor
    · simpa only [List.mem_cons,List.mem_append,List.mem_map,List.mem_singleton,
        Sum.inl_ne_inr,List.not_mem_nil,or_false,false_or,Sum.inl.injEq,exists_eq_right] using
        (List.nodup_cons.mp r.nodup).1
    · apply List.nodup_cons.mpr
      exact ⟨by simp [List.mem_map],hl⟩
  · intro d hd'
    simp only [List.cons_append,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hd'
    rcases hd' with rfl | hd' | rfl
    · exact hn
    · obtain ⟨d,hmem,rfl⟩ := List.mem_map.mp hd'
      exact r.unit d hmem
    · rcases hn with h|h <;> simp [t,h]
  · intro vi he
    have hh : r.atlas.disk vi ∈ o::l := by simpa [b,List.mem_map] using he
    exact r.disjoint vi hh
  · rintro (d|d)
    · obtain ⟨vi,hi⟩ | hi | ⟨hs',hθ⟩ := r.cover d
      · exact Or.inl ⟨vi,congrArg Sum.inl hi⟩
      · exact Or.inr (Or.inl (by simpa [List.mem_map] using hi))
      · by_cases he : d=o
        · subst d; exact Or.inr (Or.inl (by simp))
        · refine Or.inr (Or.inr ⟨?_,congrArg Sum.inl hθ⟩)
          change whisker r.σ o (Sum.inl d) = Sum.inl d
          rw [whisker_inl _ _ _ he,hs',ite_eq_right he]
    · cases d <;> exact Or.inr (Or.inl (by simp))
  · intro v i
    rw [r.corners]
    change corner r.σ r.θ r.u (r.atlas.disk (v,i)) = corner σ θ u (Sum.inl (r.atlas.disk (v,i)))
    simp only [corner,σ,whisker_inl _ _ _ (hd _),hs,ite_false,θ,Equiv.Perm.sumCongr_apply,Sum.map_inl,u,Sum.elim_inl]

omit [Fintype V] [Fintype I] in
lemma OuterRibbon.value_conjLetter {ρ : Perm I} {a : I → A} {s : I → ℤ} {o : D} {l : List D}
    (r : OuterRibbon (V := V) ρ a s o l) (n : ℤ) (hn : n=1 ∨ n = -1) :
    (r.conjLetter n hn).value = Coprod.inr (ofAdd n)*r.value*(Coprod.inr (ofAdd n))⁻¹ := by
  rw [OuterRibbon.value_formula,OuterRibbon.value_formula]
  change Coprod.inl (r.u o) *
    transportEval (r.θ.sumCongr (swap false true)) (Sum.elim r.t (fun b ↦ if b then -n else n))
      (Sum.elim r.u (fun _ ↦ r.u o)) (Sum.inr false :: l.map Sum.inl ++ [Sum.inr true]) *
    (Coprod.inl (r.u o))⁻¹ = _
  have he := transportEval_map_gauge r.θ (r.θ.sumCongr (swap false true)) r.t
    (Sum.elim r.t (fun b ↦ if b then -n else n)) r.u (Sum.elim r.u (fun _ ↦ r.u o))
    Sum.inl 1 (fun _ ↦ rfl) (fun _ ↦ rfl) (fun d ↦ (mul_one _).symm) l
  simp only [map_one,inv_one,one_mul,mul_one] at he
  rw [show Sum.inr false :: l.map Sum.inl ++ [Sum.inr true] =
      [Sum.inr false] ++ l.map Sum.inl ++ [Sum.inr true] from rfl,
    transportEval_append,transportEval_append,he]
  simp only [transportEval,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,
    transportLetter,Equiv.Perm.sumCongr_apply,Sum.map_inr,swap_apply_left,swap_apply_right,
    Sum.elim_inr,Bool.false_eq_true,ite_false,ite_true,ofAdd_neg,map_inv]
  group
end

open Equiv Equiv.Perm Monoid Multiplicative
open scoped Classical
variable {V I D A : Type*} [Fintype V] [Fintype I] [Fintype D] [DecidableEq D] [Group A]

omit [Fintype V] [Fintype I] [DecidableEq D] in
lemma OuterRibbon.theta_ne_marker {ρ : Perm I} {a : I → A} {s : I → ℤ} {o : D} {l : List D}
    (r : OuterRibbon (V := V) ρ a s o l) {d : D} (hd : d ≠ o) : r.θ d ≠ o :=
  fun he ↦ hd (r.θ.injective (he.trans r.marker.symm))

def OuterRibbon.conjCoefficient {ρ : Perm I} {a : I → A} {s : I → ℤ} {o : D} {l : List D}
    (r : OuterRibbon (V := V) ρ a s o l) (g : A) : OuterRibbon (V := V) ρ a s o l := by
  refine { r with u := Function.update r.u o (g*r.u o), corners := ?_ }
  intro v i
  have hn (vi : V × I) : r.atlas.disk vi ≠ o := fun he ↦ r.disjoint vi (by simp [he])
  have hs : r.σ (r.atlas.disk (v,i)) ≠ o := by rw [r.atlas.next]; exact hn _
  rw [r.corners]
  simp only [corner,Function.update_of_ne (r.theta_ne_marker (hn _)),Function.update_of_ne hs]

omit [Fintype V] [Fintype I] in
lemma OuterRibbon.value_conjCoefficient {ρ : Perm I} {a : I → A} {s : I → ℤ} {o : D} {l : List D}
    (r : OuterRibbon (V := V) ρ a s o l) (g : A) :
    (r.conjCoefficient g).value = Coprod.inl g*r.value*(Coprod.inl g)⁻¹ := by
  have ht : transportEval r.θ r.t (Function.update r.u o (g*r.u o)) l = transportEval r.θ r.t r.u l := by
    apply congrArg List.prod
    apply List.map_congr_left
    intro d hd
    have hn : d ≠ o := fun he ↦ (List.nodup_cons.mp r.nodup).1 (he ▸ hd)
    simp only [transportLetter,Function.update_of_ne hn,Function.update_of_ne (r.theta_ne_marker hn)]
  rw [OuterRibbon.value_formula,OuterRibbon.value_formula]
  change Coprod.inl (Function.update r.u o (g*r.u o) o) *
    transportEval r.θ r.t (Function.update r.u o (g*r.u o)) l *
    (Coprod.inl (Function.update r.u o (g*r.u o) o))⁻¹ = _
  rw [Function.update_self,ht,map_mul]
  group
end KervaireRibbon

end

end OAI


