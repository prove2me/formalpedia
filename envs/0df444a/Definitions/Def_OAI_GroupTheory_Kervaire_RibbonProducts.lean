-- Prove2me | Definitions.Def_OAI_GroupTheory_Kervaire_RibbonProducts
-- name    : OAI_GroupTheory_Kervaire_RibbonProducts
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T17:03:09.397822+00:00
-- url     : https://prove2.me/theorems/1d06d1b2-7681-4770-b492-293c81dd43c9
-- title:
--   Transport words and products of ribbons
-- statement:
--   These notions belong to a formal proof of the Kervaire conjecture in its unimodular form. For a group $A$ and an element $w$ of the free product $A*\langle t\rangle$ whose exponent sum in $t$ is $\pm1$, the natural map from $A$ to $(A*\langle t\rangle)/\langle\!\langle w\rangle\!\rangle$ is injective, so adjoining one generator and one such relation never kills a nontrivial group. The proof writes $w$ with unit $t$-exponents and represents elements of the normal closure by planar ribbon diagrams. These are pairs of permutations of darts satisfying an Euler equation, whose disks read off copies of the relator. A capping induction removes cancelling pairs of darts. Its key rigidity step at relator corners is proved analytically, with the fractional spectral phase of unitary operators over the group von Neumann algebra of $A$, which is subadditive under a trace.
--
--   1. **Transport letters.** For an involution $\theta$, signs $t$ and potentials $u$, the letter
--   $$
--   u(d)^{-1}\,t^{t(d)}\,u(\theta d),
--   $$
--   and its products along lists. Along a path in a boundary circle, the dart word equals a transport word conjugated by potentials.
--   2. **Product of ribbons.** Two outer ribbons are combined by splicing their boundary circles at the markers. The edge involutions and atlases are taken disjointly, and the potentials of the second ribbon are shifted by a constant so the corners agree. The value of the product ribbon is the product of the values.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/RibbonProducts.lean

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/RibbonProducts.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

noncomputable section

namespace KervaireRibbon

section
open Equiv Equiv.Perm Monoid Multiplicative
open scoped Classical
variable {D A : Type*} [Group A]

def transportLetter (θ : Perm D) (t : D → ℤ) (u : D → A) (d : D) : FreeProd A :=
  (Coprod.inl (u d))⁻¹ * Coprod.inr (ofAdd (t d)) * Coprod.inl (u (θ d))
def transportEval (θ : Perm D) (t : D → ℤ) (u : D → A) (l : List D) : FreeProd A :=
  (l.map (transportLetter θ t u)).prod

lemma dartEval_path (σ θ : Perm D) (t : D → ℤ) (u : D → A) (o x : D) (l : List D)
    (hc : (x::(l++[o])).IsChain (fun a b ↦ σ a = b)) :
    (Coprod.inl (u (σ x)))⁻¹ * dartEval t (corner σ θ u) l =
      transportEval θ t u l * (Coprod.inl (u o))⁻¹ := by
  induction l generalizing x with
  | nil =>
    have hh : σ x = o := by simpa only [List.nil_append,List.isChain_cons_cons,List.isChain_singleton,and_true] using hc
    simp only [hh,dartEval,transportEval,List.map_nil,List.prod_nil,mul_one,one_mul]
  | cons d l ih =>
    obtain ⟨hs,ht⟩ := List.isChain_cons_cons.mp hc
    have hi := ih d ht
    simp only [transportEval,List.map_cons,List.prod_cons] at hi ⊢
    rw [hs,dartEval_cons]
    simp only [dartLetter,corner,map_mul,map_inv,transportLetter]
    calc
      _ = ((Coprod.inl (u d))⁻¹ * Coprod.inr (ofAdd (t d)) * Coprod.inl (u (θ d))) *
        ((Coprod.inl (u (σ d)))⁻¹ * dartEval t (corner σ θ u) l) := by group
      _ = _ := by rw [hi]; group

variable {V I : Type*} [Fintype V] [Fintype I] [Fintype D] [DecidableEq D]
omit [Fintype V] [Fintype I] [DecidableEq D] in
lemma OuterRibbon.value_formula {ρ : Perm I} {a : I → A} {s : I → ℤ} {o : D} {l : List D}
    (r : OuterRibbon (V := V) ρ a s o l) :
    r.value = Coprod.inl (r.u o) * transportEval r.θ r.t r.u l * (Coprod.inl (r.u o))⁻¹ := by
  have hh := dartEval_path r.σ r.θ r.t r.u o o l r.circle
  simp only [OuterRibbon.value,dartEval_cons,dartLetter,r.marker_sign,ofAdd_zero,map_one,one_mul,
    corner,r.marker,map_mul,map_inv]
  rw [mul_assoc,hh]
  group
end

open Equiv Equiv.Perm Monoid Multiplicative
open scoped Classical
variable {V W I D E A : Type*} [Fintype V] [Fintype W] [Fintype I]
  [Fintype D] [Fintype E] [DecidableEq D] [DecidableEq E] [Group A]

omit [Fintype V] [Fintype W] [Fintype I] [Fintype D] [Fintype E] [DecidableEq D] [DecidableEq E] in
lemma transportEval_map_gauge (θ : Perm D) (η : Perm E) (t : D → ℤ) (t' : E → ℤ)
    (u : D → A) (u' : E → A) (f : D → E) (h : A)
    (hθ : ∀ d, η (f d) = f (θ d)) (ht : ∀ d, t' (f d) = t d)
    (hu : ∀ d, u' (f d) = u d*h) (l : List D) :
    transportEval η t' u' (l.map f) = (Coprod.inl h)⁻¹ * transportEval θ t u l * Coprod.inl h := by
  induction l with
  | nil => simp [transportEval]
  | cons d l ih =>
    simp only [transportEval,List.map_cons,List.prod_cons] at ih ⊢
    rw [ih]
    simp only [transportLetter,hθ,ht,hu,map_mul,mul_inv_rev]
    group

omit [Fintype V] [Fintype W] [Fintype I] [Fintype D] [Fintype E] [DecidableEq D] [DecidableEq E] in
lemma transportEval_append (θ : Perm D) (t : D → ℤ) (u : D → A) (l m : List D) :
    transportEval θ t u (l++m) = transportEval θ t u l * transportEval θ t u m := by
  simp only [transportEval,List.map_append,List.prod_append]

/-- Gluing the marked outside disks along a zero-sign corner concatenates their
words. The second potential is gauged to agree at the glued marker. -/
def OuterRibbon.mul {ρ : Perm I} {a : I → A} {s : I → ℤ}
    {o : D} {p : E} {l : List D} {m : List E}
    (r : OuterRibbon (V := V) ρ a s o l) (q : OuterRibbon (V := W) ρ a s p m) :
    OuterRibbon (V := V ⊕ W) ρ a s (Sum.inl o) (l.map Sum.inl ++ m.map Sum.inr) := by
  let σ := splice r.σ q.σ o p
  let θ := r.θ.sumCongr q.θ
  let t : D ⊕ E → ℤ := Sum.elim r.t q.t
  let h := (q.u p)⁻¹*r.u o
  let u : D ⊕ E → A := Sum.elim r.u (fun d ↦ q.u d*h)
  let ε : V ⊕ W → ℤ := Sum.elim r.atlas.ε q.atlas.ε
  let f : (V ⊕ W) × I → D ⊕ E := fun vi ↦ match vi.1 with
    | Sum.inl v => Sum.inl (r.atlas.disk (v,vi.2))
    | Sum.inr v => Sum.inr (q.atlas.disk (v,vi.2))
  have hf : Function.Injective f := by
    rintro ⟨v,i⟩ ⟨w,j⟩ he
    cases v <;> cases w
    · have hh := r.atlas.disk.injective (Sum.inl.inj he)
      cases hh; rfl
    · exact False.elim (Sum.inl_ne_inr he)
    · exact False.elim (Sum.inr_ne_inl he)
    · have hh := q.atlas.disk.injective (Sum.inr.inj he)
      cases hh; rfl
  have hrd (vi : V × I) : r.atlas.disk vi ≠ o := fun he ↦ r.disjoint vi (by simp [he])
  have hqd (vi : W × I) : q.atlas.disk vi ≠ p := fun he ↦ q.disjoint vi (by simp [he])
  have hrs (v : V) (i : I) : r.σ (r.atlas.disk (v,i)) ≠ o := by
    rw [r.atlas.next]; exact hrd _
  have hqs (v : W) (i : I) : q.σ (q.atlas.disk (v,i)) ≠ p := by
    rw [q.atlas.next]; exact hqd _
  let b : DiskAtlas (V := V ⊕ W) ρ a s σ t := {
    disk := ⟨f,hf⟩
    ε := ε
    polarity := by rintro (v|v); exact r.atlas.polarity v; exact q.atlas.polarity v
    next := by
      rintro (v|v) i
      · change splice r.σ q.σ o p (Sum.inl (r.atlas.disk (v,i))) = _
        rw [splice_inl,ite_eq_right (hrs v i),r.atlas.next]
        rfl
      · change splice r.σ q.σ o p (Sum.inr (q.atlas.disk (v,i))) = _
        rw [splice_inr _ _ _ _ _ (hqd _),ite_eq_right (hqs v i),q.atlas.next]
        rfl
    sign := by rintro (v|v) i; exact r.atlas.sign v i; exact q.atlas.sign v i }
  refine {
    σ := σ, θ := θ, t := t, u := u, atlas := b
    involutive := ?_, planar' := planar_splice _ _ _ _ _ _ r.planar' q.planar'
    opposite := ?_, marker := ?_, marker_sign := r.marker_sign
    circle := circle_splice _ _ _ _ _ _ r.circle q.circle (List.nodup_cons.mp r.nodup).1 (List.nodup_cons.mp q.nodup).1
    nodup := ?_, unit := ?_, disjoint := ?_, cover := ?_, corners := ?_ }
  · rintro (d|d)
    · exact congrArg Sum.inl (r.involutive d)
    · exact congrArg Sum.inr (q.involutive d)
  · rintro (d|d); exact r.opposite d; exact q.opposite d
  · exact congrArg Sum.inl r.marker
  · change ((o::l).map Sum.inl ++ m.map Sum.inr).Nodup
    apply List.nodup_append.mpr
    refine ⟨r.nodup.map Sum.inl_injective,q.nodup.of_cons.map Sum.inr_injective,?_⟩
    intro d hd e he hh
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hd
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp he
    exact Sum.inl_ne_inr hh
  · intro d hd
    obtain hd | hd := List.mem_append.mp hd
    · obtain ⟨d,hx,rfl⟩ := List.mem_map.mp hd
      exact r.unit d hx
    · obtain ⟨d,hx,rfl⟩ := List.mem_map.mp hd
      exact q.unit d hx
  · rintro ⟨v|v,i⟩ he
    · have hh : r.atlas.disk (v,i) ∈ o::l := by simpa [b,f,List.mem_map] using he
      exact r.disjoint (v,i) hh
    · have hh : q.atlas.disk (v,i) ∈ m := by simpa [b,f,List.mem_map] using he
      exact q.disjoint (v,i) (by simp [hh])
  · rintro (d|d)
    · obtain ⟨⟨v,i⟩,hi⟩ | hi | ⟨hs,hθ⟩ := r.cover d
      · exact Or.inl ⟨(Sum.inl v,i),congrArg Sum.inl hi⟩
      · exact Or.inr (Or.inl (by simpa [List.mem_map] using hi))
      · by_cases hd : d=o
        · subst d; exact Or.inr (Or.inl (by simp))
        · apply Or.inr ∘ Or.inr
          constructor
          · change splice r.σ q.σ o p (Sum.inl d) = Sum.inl d
            rw [splice_inl,hs,ite_eq_right hd]
          · exact congrArg Sum.inl hθ
    · obtain ⟨⟨v,i⟩,hi⟩ | hi | ⟨hs,hθ⟩ := q.cover d
      · exact Or.inl ⟨(Sum.inr v,i),congrArg Sum.inr hi⟩
      · rcases List.mem_cons.mp hi with hd | hd
        · subst d
          exact Or.inr (Or.inr ⟨splice_marker _ _ _ _,congrArg Sum.inr q.marker⟩)
        · exact Or.inr (Or.inl (by simp [List.mem_map,hd]))
      · apply Or.inr ∘ Or.inr
        constructor
        · change splice r.σ q.σ o p (Sum.inr d) = Sum.inr d
          by_cases hd : d=p
          · subst d; exact splice_marker _ _ _ _
          · rw [splice_inr _ _ _ _ _ hd,hs,ite_eq_right hd]
        · exact congrArg Sum.inr hθ
  · rintro (v|v) i
    · change vertexCorner ρ a r.atlas.ε (v,i) = corner σ θ u (Sum.inl (r.atlas.disk (v,i)))
      rw [r.corners]
      unfold corner
      simp only [σ,θ,splice_inl,hrs,ite_false,Equiv.Perm.sumCongr_apply,Sum.map_inl,u,Sum.elim_inl]
    · change vertexCorner ρ a q.atlas.ε (v,i) = corner σ θ u (Sum.inr (q.atlas.disk (v,i)))
      rw [q.corners]
      unfold corner
      simp only [σ,θ,splice_inr _ _ _ _ _ (hqd _),hqs,ite_false,Equiv.Perm.sumCongr_apply,Sum.map_inr,u,Sum.elim_inr]
      group

omit [Fintype V] [Fintype W] [Fintype I] in
lemma OuterRibbon.value_mul {ρ : Perm I} {a : I → A} {s : I → ℤ}
    {o : D} {p : E} {l : List D} {m : List E}
    (r : OuterRibbon (V := V) ρ a s o l) (q : OuterRibbon (V := W) ρ a s p m) :
    (r.mul q).value = r.value*q.value := by
  rw [OuterRibbon.value_formula,OuterRibbon.value_formula,OuterRibbon.value_formula,transportEval_append]
  change Coprod.inl (r.u o) *
    (transportEval (r.θ.sumCongr q.θ) (Sum.elim r.t q.t)
      (Sum.elim r.u (fun d ↦ q.u d*((q.u p)⁻¹*r.u o))) (l.map Sum.inl) *
     transportEval (r.θ.sumCongr q.θ) (Sum.elim r.t q.t)
      (Sum.elim r.u (fun d ↦ q.u d*((q.u p)⁻¹*r.u o))) (m.map Sum.inr)) * (Coprod.inl (r.u o))⁻¹ = _
  rw [transportEval_map_gauge r.θ _ r.t _ r.u _ Sum.inl 1 (fun _ ↦ rfl) (fun _ ↦ rfl) (fun d ↦ (mul_one _).symm),
    transportEval_map_gauge q.θ _ q.t _ q.u _ Sum.inr ((q.u p)⁻¹*r.u o) (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)]
  simp only [map_one,inv_one,one_mul,mul_one,map_mul,map_inv]
  group
end KervaireRibbon

end

end OAI


