-- Prove2me | Definitions.Def_OAI_GroupTheory_Kervaire_Realization
-- name    : OAI_GroupTheory_Kervaire_Realization
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T17:16:44.652103+00:00
-- url     : https://prove2.me/theorems/5c88e99c-311d-46bc-99c4-25ce349f8df9
-- title:
--   Realized elements form a normal subgroup
-- statement:
--   These notions belong to a formal proof of the Kervaire conjecture in its unimodular form. For a group $A$ and an element $w$ of the free product $A*\langle t\rangle$ whose exponent sum in $t$ is $\pm1$, the natural map from $A$ to $(A*\langle t\rangle)/\langle\!\langle w\rangle\!\rangle$ is injective, so adjoining one generator and one such relation never kills a nontrivial group. The proof writes $w$ with unit $t$-exponents and represents elements of the normal closure by planar ribbon diagrams. These are pairs of permutations of darts satisfying an Euler equation, whose disks read off copies of the relator. A capping induction removes cancelling pairs of darts. Its key rigidity step at relator corners is proved analytically, with the fractional spectral phase of unitary operators over the group von Neumann algebra of $A$, which is subadditive under a trace.
--
--   1. **Trivial ribbon.** The ribbon on a single isolated marker dart with no disks, of value $1$.
--   2. **Realized elements.** $w\in A*\langle t\rangle$ is realized for the relator data $(\rho,a,s)$ if some outer ribbon, on some finite set of darts, has value $w$.
--   3. **Realized subgroup.** The set of realized elements.
--
--   It is closed under products, by splicing ribbons, and under inverses, by reversing ribbons. Conjugation by letters and coefficients preserves it, so it is a normal subgroup:
--   $$
--   \{w:\ w\text{ is realized}\}\trianglelefteq A*\langle t\rangle .
--   $$
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/Realization.lean

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/Realization.lean by skeleton subtraction
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
import Definitions.Def_OAI_GroupTheory_Kervaire_Conjugation
import Definitions.Def_OAI_GroupTheory_Kervaire_Inversion

namespace OAI

section
noncomputable section

namespace KervaireRibbon
open Equiv Equiv.Perm Monoid Multiplicative
open scoped Classical
variable {I : Type} {A : Type*} [Group A]

def OuterRibbon.one (ρ : Perm I) (a : I → A) (s : I → ℤ) :
    OuterRibbon (V := (PEmpty : Type)) ρ a s (PUnit.unit : (PUnit : Type)) [] := by
  let b : DiskAtlas (V := (PEmpty : Type)) ρ a s (1 : Perm (PUnit : Type)) (fun _ ↦ 0) := {
    disk := ⟨fun vi ↦ vi.1.elim,by rintro ⟨v,i⟩; exact v.elim⟩
    ε := fun v ↦ v.elim
    polarity := fun v ↦ v.elim
    next := fun v ↦ v.elim
    sign := fun v ↦ v.elim }
  exact {
    σ := 1, θ := 1, t := fun _ ↦ 0, u := fun _ ↦ 1, atlas := b
    involutive := fun _ ↦ rfl, planar' := planar_one_right 1
    opposite := fun _ ↦ (neg_zero : -(0:ℤ)=0).symm
    marker := rfl, marker_sign := rfl
    circle := by simp [Circle]
    nodup := by simp
    unit := by simp
    disjoint := fun vi ↦ vi.1.elim
    cover := fun d ↦ Or.inr (Or.inr ⟨rfl,rfl⟩)
    corners := fun v ↦ v.elim }

lemma OuterRibbon.value_one (ρ : Perm I) (a : I → A) (s : I → ℤ) :
    (OuterRibbon.one ρ a s).value = 1 := by
  simp [OuterRibbon.value,OuterRibbon.one,dartEval,dartLetter,corner]

/-- A word is realized by a finite genus-zero relator ribbon. The dart and vertex
sets range over ordinary finite types; the coefficient group has arbitrary universe. -/
def Realized (ρ : Perm I) (a : I → A) (s : I → ℤ) (w : FreeProd A) : Prop :=
  ∃ (D V : Type) (_ : Fintype D) (_ : DecidableEq D) (_ : Fintype V)
    (o : D) (l : List D) (r : OuterRibbon (V := V) ρ a s o l), r.value = w

lemma Realized.one (ρ : Perm I) (a : I → A) (s : I → ℤ) : Realized ρ a s 1 :=
  ⟨PUnit,PEmpty,inferInstance,inferInstance,inferInstance,PUnit.unit,[],OuterRibbon.one ρ a s,
    OuterRibbon.value_one ρ a s⟩

lemma Realized.mul {ρ : Perm I} {a : I → A} {s : I → ℤ} {w z : FreeProd A}
    (h : Realized ρ a s w) (k : Realized ρ a s z) : Realized ρ a s (w*z) := by
  obtain ⟨D,V,fd,dd,fv,o,l,r,rfl⟩ := h
  obtain ⟨E,W,fe,de,fw,p,m,q,rfl⟩ := k
  exact ⟨D⊕E,V⊕W,inferInstance,inferInstance,inferInstance,Sum.inl o,
    l.map Sum.inl ++ m.map Sum.inr,r.mul q,r.value_mul q⟩

lemma Realized.inv {ρ : Perm I} {a : I → A} {s : I → ℤ} {w : FreeProd A}
    (h : Realized ρ a s w) : Realized ρ a s w⁻¹ := by
  obtain ⟨D,V,fd,dd,fv,o,l,r,rfl⟩ := h
  exact ⟨D,V,fd,dd,fv,o,l.reverse,r.inv,r.value_inv⟩

lemma Realized.conjCoefficient {ρ : Perm I} {a : I → A} {s : I → ℤ} {w : FreeProd A}
    (h : Realized ρ a s w) (g : A) : Realized ρ a s (Coprod.inl g*w*(Coprod.inl g)⁻¹) := by
  obtain ⟨D,V,fd,dd,fv,o,l,r,rfl⟩ := h
  exact ⟨D,V,fd,dd,fv,o,l,r.conjCoefficient g,r.value_conjCoefficient g⟩

lemma Realized.conjLetter {ρ : Perm I} {a : I → A} {s : I → ℤ} {w : FreeProd A}
    (h : Realized ρ a s w) (n : ℤ) (hn : n=1 ∨ n = -1) :
    Realized ρ a s (Coprod.inr (ofAdd n)*w*(Coprod.inr (ofAdd n))⁻¹) := by
  obtain ⟨D,V,fd,dd,fv,o,l,r,rfl⟩ := h
  exact ⟨D⊕Bool,V,inferInstance,inferInstance,fv,Sum.inl o,
    Sum.inr false :: l.map Sum.inl ++ [Sum.inr true],r.conjLetter n hn,r.value_conjLetter n hn⟩

def realizedSubgroup (ρ : Perm I) (a : I → A) (s : I → ℤ) : Subgroup (FreeProd A) where
  carrier := Realized ρ a s
  one_mem' := Realized.one ρ a s
  mul_mem' := Realized.mul
  inv_mem' := Realized.inv

lemma Realized.conjZpow {ρ : Perm I} {a : I → A} {s : I → ℤ} {w : FreeProd A}
    (h : Realized ρ a s w) (n : ℤ) :
    Realized ρ a s (Coprod.inr (ofAdd n)*w*(Coprod.inr (ofAdd n))⁻¹) := by
  induction n using Int.induction_on with
  | zero => simpa using h
  | succ n ih =>
    have hh := ih.conjLetter 1 (Or.inl rfl)
    convert hh using 1
    rw [add_comm,ofAdd_add,map_mul]
    group
  | pred n ih =>
    have hh := ih.conjLetter (-1) (Or.inr rfl)
    convert hh using 1
    rw [sub_eq_add_neg,add_comm,ofAdd_add,map_mul]
    group

lemma Realized.conj {ρ : Perm I} {a : I → A} {s : I → ℤ} {w : FreeProd A}
    (h : Realized ρ a s w) (x : FreeProd A) : Realized ρ a s (x*w*x⁻¹) := by
  induction x using Coprod.induction_on generalizing w with
  | inl g => exact h.conjCoefficient g
  | inr n => exact h.conjZpow (toAdd n)
  | mul x y hx hy =>
    have hh := hx (hy h)
    convert hh using 1
    group

instance realizedSubgroup_normal (ρ : Perm I) (a : I → A) (s : I → ℤ) :
    (realizedSubgroup ρ a s).Normal where
  conj_mem := fun _ hw x ↦ hw.conj x

end KervaireRibbon

end
end

end OAI


