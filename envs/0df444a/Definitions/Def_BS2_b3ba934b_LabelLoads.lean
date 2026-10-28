-- Prove2me | Definitions.Def_BS2_b3ba934b_LabelLoads
-- name    : BS2_b3ba934b_LabelLoads
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T03:59:51.343868+00:00
-- url     : https://prove2.me/theorems/b56c0033-f2cd-429d-ae97-7f13675d869c
-- title:
--   Sensitivity separation: LabelLoads (complete source module)
-- statement:
--   Complete Lean source module `LabelLoads` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/LabelLoads.lean; original SHA-256 f14b990f8155357bd8a8ceb9a14f3ba10128ad28c642118f2c8b7c0f5295bd70; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Reassembled from supplied accepted Prove2me source proofs. See provenance.json. -/
import Definitions.Def_BS2_b3ba934b_LabelMarked

namespace Sensitivity10007Labeling


/- Source: Sol_Paley11987Verified_CompactLabeling11987_family_coordinate_load_le.lean -/
set_option autoImplicit false
set_option Elab.async false
section z8

section

set_option maxHeartbeats 6000000
open scoped Classical BigOperators

namespace ZL
noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

















































theorem dominatedSupport_card (R : V → V → Prop)
    (hloop : ∀ x, ¬ R x x)
    (htour : ∀ x y, x ≠ y → (R x y ↔ ¬ R y x))
    (A M : Finset V) (hdis : Disjoint A M)
    (hdom : ∀ x ∈ M, ∀ y ∈ A, R x y) :
    (markedSupport R A M).card = A.card.choose 2 + M.card * A.card := by
  have hcross : crossEdges R M A = M ×ˢ A := by
    apply Finset.filter_eq_self.mpr
    intro e he
    exact hdom e.1 (Finset.mem_product.mp he).1 e.2 (Finset.mem_product.mp he).2
  have hd : Disjoint (internalEdges R A) (crossEdges R M A) := by
    apply Finset.disjoint_left.mpr
    intro e he hf
    exact Finset.disjoint_left.mp hdis
      (Finset.mem_product.mp (Finset.mem_filter.mp he).1).1
      (Finset.mem_product.mp (Finset.mem_filter.mp hf).1).1
  rw [markedSupport, Finset.card_union_of_disjoint hd,
    _root_.Sensitivity10007Labeling.Paley10007Verified.CompactLabeling.card_internalEdges R hloop htour, hcross, Finset.card_product]

end
end ZL
end
end z8

section z9

section

set_option maxHeartbeats 8000000
open scoped Classical BigOperators

namespace ZL
noncomputable section

namespace SupportedFamily
variable {V D : Type*} [Fintype V] [DecidableEq V] [Fintype D] [DecidableEq D]
variable (F : SupportedFamily V D)





end SupportedFamily






















end
end ZL
end
end z9

section z12

section

set_option maxHeartbeats 200000
open scoped Classical BigOperators

namespace ZL
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem coherent_assignment_count (S : Finset (V × V)) (A : Finset V)
    (hheads : ∀ e ∈ S, e.2 ∈ A) :
    Fintype.card {ell : V × V → Fin 2 //
      ∃ color : V → Fin 2, ∀ e ∈ S, ell e = color e.2} ≤
      2 ^ A.card * 2 ^ (Fintype.card (V × V) - S.card) := by
  let C := {ell : V × V → Fin 2 //
    ∃ color : V → Fin 2, ∀ e ∈ S, ell e = color e.2}
  let color (ell : C) : V → Fin 2 := Classical.choose ell.property
  have hcolor (ell : C) : ∀ e ∈ S, ell.val e = color ell e.2 :=
    Classical.choose_spec ell.property
  let encode : C → (A → Fin 2) × ((Sᶜ : Finset (V × V)) → Fin 2) := fun ell =>
    ⟨fun x => color ell x.val,fun e => ell.val e.val⟩
  have hinj : Function.Injective encode := by
    intro ell ell' heq
    apply Subtype.ext
    funext e
    by_cases he : e ∈ S
    · rw [hcolor ell e he,hcolor ell' e he]
      exact congrArg (fun p : (A → Fin 2) × ((Sᶜ : Finset (V × V)) → Fin 2) =>
        p.1 ⟨e.2,hheads e he⟩) heq
    · exact congrArg (fun p : (A → Fin 2) × ((Sᶜ : Finset (V × V)) → Fin 2) =>
        p.2 ⟨e,Finset.mem_compl.mpr he⟩) heq
  have hc := Fintype.card_le_of_injective encode hinj
  simpa only [C,Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,
    Fintype.card_coe,Finset.card_compl] using hc

theorem markedSupport_heads (R : V → V → Prop) (A M : Finset V) :
    ∀ e ∈ markedSupport R A M, e.2 ∈ A := by
  intro e he
  obtain he | he := Finset.mem_union.mp he
  · exact (Finset.mem_product.mp (Finset.mem_filter.mp he).1).2
  · exact (Finset.mem_product.mp (Finset.mem_filter.mp he).1).2

theorem coherent_marked_count (R : V → V → Prop) (A M : Finset V) :
    Fintype.card {ell : V × V → Fin 2 // ∃ color, Coherent R ell A M color} ≤
      2 ^ A.card * 2 ^ (Fintype.card (V × V) - (markedSupport R A M).card) := by
  let e : {ell : V × V → Fin 2 // ∃ color, Coherent R ell A M color} ≃
      {ell : V × V → Fin 2 // ∃ color : V → Fin 2,
        ∀ e ∈ markedSupport R A M, ell e = color e.2} :=
    Equiv.subtypeEquivRight (fun _ => Iff.rfl)
  rw [Fintype.card_congr e]
  exact coherent_assignment_count (markedSupport R A M) A (markedSupport_heads R A M)

end
end ZL
end
end z12

section z13

section

set_option maxHeartbeats 8000000
open scoped Classical BigOperators

namespace ZL
noncomputable section
open RowCounting
variable {V D : Type*} [Fintype V] [DecidableEq V] [Fintype D] [DecidableEq D]





theorem coherent_localProbability_le (F : SupportedFamily (V × V) D) (d : D)
    (R : V → V → Prop) (A M : Finset V)
    (hs : F.support d = markedSupport R A M)
    (hb : ∀ ell, F.bad d ell ↔ ∃ color, Coherent R ell A M color) :
    F.localProbability d ≤ (2 ^ A.card : ℚ) / 2 ^ (markedSupport R A M).card := by
  rw [← hs]
  have h := F.localProbability_le_of_global d (2 ^ A.card) (by
    rw [Fintype.card_congr (Equiv.subtypeEquivRight hb),hs]
    exact coherent_marked_count R A M)
  simpa only [Nat.cast_pow,Nat.cast_ofNat] using h









end
end ZL
end
end z13

section z16

section
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 12000000
set_option maxRecDepth 200000
set_option exponentiation.threshold 32768
open scoped Classical BigOperators

namespace CompactLabeling10007
open ZL ZL.RowCounting




















































theorem basic_constants : N=10007 ∧ degree=5003 ∧ common=2501 ∧ 1 < lam ∧ lam^2 < 2 := by
  simp only [N,degree,common,lam,scale,ordinaryCutoffs,ordinaryA,ordinaryLo,ordinaryRem,ordinaryLowValue,ordinaryHighValue,ordinaryProduct,ordinaryLoad,sourceLoad,dominatorLoad,MarkedParameters.C,MarkedParameters.W,MarkedParameters.B,MarkedParameters.load,marked0,marked1,marked2,marked3,marked4,marked5,marked6,marked7,marked8,marked9,marked10,marked11,markedParameters,marked,ordinaryCeilings,ordinaryCeiling,sourceCeiling,dominatorCeiling,markedCeiling,headErrorFactor,orientationWeight,rowPatterns,Nat.choose_eq_fast_choose]
  decide +kernel

theorem elementary_ordinary : ∀ q : Fin 9,
    2 ≤ ordinaryA q ∧ ordinaryA q ≤ N ∧
    0 < ordinaryLowValue q ∧ 0 < ordinaryHighValue q ∧
    ordinaryRem q ≤ ordinaryA q ∧
    ordinaryLo q * ordinaryA q + ordinaryRem q = (ordinaryA q).choose 2 := by
  simp only [N,degree,common,lam,scale,ordinaryCutoffs,ordinaryA,ordinaryLo,ordinaryRem,ordinaryLowValue,ordinaryHighValue,ordinaryProduct,ordinaryLoad,sourceLoad,dominatorLoad,MarkedParameters.C,MarkedParameters.W,MarkedParameters.B,MarkedParameters.load,marked0,marked1,marked2,marked3,marked4,marked5,marked6,marked7,marked8,marked9,marked10,marked11,markedParameters,marked,ordinaryCeilings,ordinaryCeiling,sourceCeiling,dominatorCeiling,markedCeiling,headErrorFactor,orientationWeight,rowPatterns,Nat.choose_eq_fast_choose]
  decide +kernel

theorem ordinary_tangent_0 : ∀ d : Fin (ordinaryA 0),
    rowPatterns 0 d.val * ordinaryLowValue 0^d.val * ordinaryHighValue 0^ordinaryLo 0 ≤
      ordinaryLowValue 0^(ordinaryLo 0+1) * ordinaryHighValue 0^d.val := by
  simp only [N,degree,common,lam,scale,ordinaryCutoffs,ordinaryA,ordinaryLo,ordinaryRem,ordinaryLowValue,ordinaryHighValue,ordinaryProduct,ordinaryLoad,sourceLoad,dominatorLoad,MarkedParameters.C,MarkedParameters.W,MarkedParameters.B,MarkedParameters.load,marked0,marked1,marked2,marked3,marked4,marked5,marked6,marked7,marked8,marked9,marked10,marked11,markedParameters,marked,ordinaryCeilings,ordinaryCeiling,sourceCeiling,dominatorCeiling,markedCeiling,headErrorFactor,orientationWeight,rowPatterns,Nat.choose_eq_fast_choose]
  decide +kernel

theorem ordinary_tangent_1 : ∀ d : Fin (ordinaryA 1),
    rowPatterns 1 d.val * ordinaryLowValue 1^d.val * ordinaryHighValue 1^ordinaryLo 1 ≤
      ordinaryLowValue 1^(ordinaryLo 1+1) * ordinaryHighValue 1^d.val := by
  simp only [N,degree,common,lam,scale,ordinaryCutoffs,ordinaryA,ordinaryLo,ordinaryRem,ordinaryLowValue,ordinaryHighValue,ordinaryProduct,ordinaryLoad,sourceLoad,dominatorLoad,MarkedParameters.C,MarkedParameters.W,MarkedParameters.B,MarkedParameters.load,marked0,marked1,marked2,marked3,marked4,marked5,marked6,marked7,marked8,marked9,marked10,marked11,markedParameters,marked,ordinaryCeilings,ordinaryCeiling,sourceCeiling,dominatorCeiling,markedCeiling,headErrorFactor,orientationWeight,rowPatterns,Nat.choose_eq_fast_choose]
  decide +kernel

theorem ordinary_tangent_2 : ∀ d : Fin (ordinaryA 2),
    rowPatterns 2 d.val * ordinaryLowValue 2^d.val * ordinaryHighValue 2^ordinaryLo 2 ≤
      ordinaryLowValue 2^(ordinaryLo 2+1) * ordinaryHighValue 2^d.val := by
  simp only [N,degree,common,lam,scale,ordinaryCutoffs,ordinaryA,ordinaryLo,ordinaryRem,ordinaryLowValue,ordinaryHighValue,ordinaryProduct,ordinaryLoad,sourceLoad,dominatorLoad,MarkedParameters.C,MarkedParameters.W,MarkedParameters.B,MarkedParameters.load,marked0,marked1,marked2,marked3,marked4,marked5,marked6,marked7,marked8,marked9,marked10,marked11,markedParameters,marked,ordinaryCeilings,ordinaryCeiling,sourceCeiling,dominatorCeiling,markedCeiling,headErrorFactor,orientationWeight,rowPatterns,Nat.choose_eq_fast_choose]
  decide +kernel

theorem ordinary_tangent_3 : ∀ d : Fin (ordinaryA 3),
    rowPatterns 3 d.val * ordinaryLowValue 3^d.val * ordinaryHighValue 3^ordinaryLo 3 ≤
      ordinaryLowValue 3^(ordinaryLo 3+1) * ordinaryHighValue 3^d.val := by
  simp only [N,degree,common,lam,scale,ordinaryCutoffs,ordinaryA,ordinaryLo,ordinaryRem,ordinaryLowValue,ordinaryHighValue,ordinaryProduct,ordinaryLoad,sourceLoad,dominatorLoad,MarkedParameters.C,MarkedParameters.W,MarkedParameters.B,MarkedParameters.load,marked0,marked1,marked2,marked3,marked4,marked5,marked6,marked7,marked8,marked9,marked10,marked11,markedParameters,marked,ordinaryCeilings,ordinaryCeiling,sourceCeiling,dominatorCeiling,markedCeiling,headErrorFactor,orientationWeight,rowPatterns,Nat.choose_eq_fast_choose]
  decide +kernel

theorem ordinary_tangent_4 : ∀ d : Fin (ordinaryA 4),
    rowPatterns 4 d.val * ordinaryLowValue 4^d.val * ordinaryHighValue 4^ordinaryLo 4 ≤
      ordinaryLowValue 4^(ordinaryLo 4+1) * ordinaryHighValue 4^d.val := by
  simp only [N,degree,common,lam,scale,ordinaryCutoffs,ordinaryA,ordinaryLo,ordinaryRem,ordinaryLowValue,ordinaryHighValue,ordinaryProduct,ordinaryLoad,sourceLoad,dominatorLoad,MarkedParameters.C,MarkedParameters.W,MarkedParameters.B,MarkedParameters.load,marked0,marked1,marked2,marked3,marked4,marked5,marked6,marked7,marked8,marked9,marked10,marked11,markedParameters,marked,ordinaryCeilings,ordinaryCeiling,sourceCeiling,dominatorCeiling,markedCeiling,headErrorFactor,orientationWeight,rowPatterns,Nat.choose_eq_fast_choose]
  decide +kernel

theorem ordinary_tangent_5 : ∀ d : Fin (ordinaryA 5),
    rowPatterns 5 d.val * ordinaryLowValue 5^d.val * ordinaryHighValue 5^ordinaryLo 5 ≤
      ordinaryLowValue 5^(ordinaryLo 5+1) * ordinaryHighValue 5^d.val := by
  simp only [N,degree,common,lam,scale,ordinaryCutoffs,ordinaryA,ordinaryLo,ordinaryRem,ordinaryLowValue,ordinaryHighValue,ordinaryProduct,ordinaryLoad,sourceLoad,dominatorLoad,MarkedParameters.C,MarkedParameters.W,MarkedParameters.B,MarkedParameters.load,marked0,marked1,marked2,marked3,marked4,marked5,marked6,marked7,marked8,marked9,marked10,marked11,markedParameters,marked,ordinaryCeilings,ordinaryCeiling,sourceCeiling,dominatorCeiling,markedCeiling,headErrorFactor,orientationWeight,rowPatterns,Nat.choose_eq_fast_choose]
  decide +kernel

theorem ordinary_tangent_6 : ∀ d : Fin (ordinaryA 6),
    rowPatterns 6 d.val * ordinaryLowValue 6^d.val * ordinaryHighValue 6^ordinaryLo 6 ≤
      ordinaryLowValue 6^(ordinaryLo 6+1) * ordinaryHighValue 6^d.val := by
  simp only [N,degree,common,lam,scale,ordinaryCutoffs,ordinaryA,ordinaryLo,ordinaryRem,ordinaryLowValue,ordinaryHighValue,ordinaryProduct,ordinaryLoad,sourceLoad,dominatorLoad,MarkedParameters.C,MarkedParameters.W,MarkedParameters.B,MarkedParameters.load,marked0,marked1,marked2,marked3,marked4,marked5,marked6,marked7,marked8,marked9,marked10,marked11,markedParameters,marked,ordinaryCeilings,ordinaryCeiling,sourceCeiling,dominatorCeiling,markedCeiling,headErrorFactor,orientationWeight,rowPatterns,Nat.choose_eq_fast_choose]
  decide +kernel

theorem ordinary_tangent_7 : ∀ d : Fin (ordinaryA 7),
    rowPatterns 7 d.val * ordinaryLowValue 7^d.val * ordinaryHighValue 7^ordinaryLo 7 ≤
      ordinaryLowValue 7^(ordinaryLo 7+1) * ordinaryHighValue 7^d.val := by
  simp only [N,degree,common,lam,scale,ordinaryCutoffs,ordinaryA,ordinaryLo,ordinaryRem,ordinaryLowValue,ordinaryHighValue,ordinaryProduct,ordinaryLoad,sourceLoad,dominatorLoad,MarkedParameters.C,MarkedParameters.W,MarkedParameters.B,MarkedParameters.load,marked0,marked1,marked2,marked3,marked4,marked5,marked6,marked7,marked8,marked9,marked10,marked11,markedParameters,marked,ordinaryCeilings,ordinaryCeiling,sourceCeiling,dominatorCeiling,markedCeiling,headErrorFactor,orientationWeight,rowPatterns,Nat.choose_eq_fast_choose]
  decide +kernel

theorem ordinary_tangent_8 : ∀ d : Fin (ordinaryA 8),
    rowPatterns 8 d.val * ordinaryLowValue 8^d.val * ordinaryHighValue 8^ordinaryLo 8 ≤
      ordinaryLowValue 8^(ordinaryLo 8+1) * ordinaryHighValue 8^d.val := by
  simp only [N,degree,common,lam,scale,ordinaryCutoffs,ordinaryA,ordinaryLo,ordinaryRem,ordinaryLowValue,ordinaryHighValue,ordinaryProduct,ordinaryLoad,sourceLoad,dominatorLoad,MarkedParameters.C,MarkedParameters.W,MarkedParameters.B,MarkedParameters.load,marked0,marked1,marked2,marked3,marked4,marked5,marked6,marked7,marked8,marked9,marked10,marked11,markedParameters,marked,ordinaryCeilings,ordinaryCeiling,sourceCeiling,dominatorCeiling,markedCeiling,headErrorFactor,orientationWeight,rowPatterns,Nat.choose_eq_fast_choose]
  decide +kernel

theorem marked_tangents_0 : ∀ d : Fin marked0.a, ∀ t : Fin (marked0.q+1),
    (rowPatterns t.val d.val : ℚ) ≤ marked0.C t.val * marked0.u^d.val := by
  simp only [N,degree,common,lam,scale,ordinaryCutoffs,ordinaryA,ordinaryLo,ordinaryRem,ordinaryLowValue,ordinaryHighValue,ordinaryProduct,ordinaryLoad,sourceLoad,dominatorLoad,MarkedParameters.C,MarkedParameters.W,MarkedParameters.B,MarkedParameters.load,marked0,marked1,marked2,marked3,marked4,marked5,marked6,marked7,marked8,marked9,marked10,marked11,markedParameters,marked,ordinaryCeilings,ordinaryCeiling,sourceCeiling,dominatorCeiling,markedCeiling,headErrorFactor,orientationWeight,rowPatterns,Nat.choose_eq_fast_choose]
  decide +kernel

theorem marked_parameters_0 :
    0 < marked0.a.choose 2 ∧ marked0.a.choose 2+marked0.m*marked0.a ≤ 2*marked0.a.choose 2 ∧
    0 ≤ marked0.u ∧ 0 ≤ marked0.gamma ∧ 0 ≤ marked0.wm ∧ 0 ≤ marked0.W ∧
    (∀ t : Fin (marked0.q+1), 0 ≤ marked0.C t.val) ∧
    (∀ f : Fin (marked0.m+1),
      orientationWeight marked0.q marked0.C f.val ≤ marked0.wm ∧
      orientationWeight marked0.q marked0.C f.val ≤
        marked0.alpha+marked0.beta*f.val+marked0.gamma*(f.val.choose 2)) := by
  simp only [N,degree,common,lam,scale,ordinaryCutoffs,ordinaryA,ordinaryLo,ordinaryRem,ordinaryLowValue,ordinaryHighValue,ordinaryProduct,ordinaryLoad,sourceLoad,dominatorLoad,MarkedParameters.C,MarkedParameters.W,MarkedParameters.B,MarkedParameters.load,marked0,marked1,marked2,marked3,marked4,marked5,marked6,marked7,marked8,marked9,marked10,marked11,markedParameters,marked,ordinaryCeilings,ordinaryCeiling,sourceCeiling,dominatorCeiling,markedCeiling,headErrorFactor,orientationWeight,rowPatterns,Nat.choose_eq_fast_choose]
  decide +kernel

theorem marked_tangents_1 : ∀ d : Fin marked1.a, ∀ t : Fin (marked1.q+1),
    (rowPatterns t.val d.val : ℚ) ≤ marked1.C t.val * marked1.u^d.val := by
  simp only [N,degree,common,lam,scale,ordinaryCutoffs,ordinaryA,ordinaryLo,ordinaryRem,ordinaryLowValue,ordinaryHighValue,ordinaryProduct,ordinaryLoad,sourceLoad,dominatorLoad,MarkedParameters.C,MarkedParameters.W,MarkedParameters.B,MarkedParameters.load,marked0,marked1,marked2,marked3,marked4,marked5,marked6,marked7,marked8,marked9,marked10,marked11,markedParameters,marked,ordinaryCeilings,ordinaryCeiling,sourceCeiling,dominatorCeiling,markedCeiling,headErrorFactor,orientationWeight,rowPatterns,Nat.choose_eq_fast_choose]
  decide +kernel

theorem marked_parameters_1 :
    0 < marked1.a.choose 2 ∧ marked1.a.choose 2+marked1.m*marked1.a ≤ 2*marked1.a.choose 2 ∧
    0 ≤ marked1.u ∧ 0 ≤ marked1.gamma ∧ 0 ≤ marked1.wm ∧ 0 ≤ marked1.W ∧
    (∀ t : Fin (marked1.q+1), 0 ≤ marked1.C t.val) ∧
    (∀ f : Fin (marked1.m+1),
      orientationWeight marked1.q marked1.C f.val ≤ marked1.wm ∧
      orientationWeight marked1.q marked1.C f.val ≤
        marked1.alpha+marked1.beta*f.val+marked1.gamma*(f.val.choose 2)) := by
  simp only [N,degree,common,lam,scale,ordinaryCutoffs,ordinaryA,ordinaryLo,ordinaryRem,ordinaryLowValue,ordinaryHighValue,ordinaryProduct,ordinaryLoad,sourceLoad,dominatorLoad,MarkedParameters.C,MarkedParameters.W,MarkedParameters.B,MarkedParameters.load,marked0,marked1,marked2,marked3,marked4,marked5,marked6,marked7,marked8,marked9,marked10,marked11,markedParameters,marked,ordinaryCeilings,ordinaryCeiling,sourceCeiling,dominatorCeiling,markedCeiling,headErrorFactor,orientationWeight,rowPatterns,Nat.choose_eq_fast_choose]
  decide +kernel

theorem marked_tangents_2 : ∀ d : Fin marked2.a, ∀ t : Fin (marked2.q+1),
    (rowPatterns t.val d.val : ℚ) ≤ marked2.C t.val * marked2.u^d.val := by
  simp only [N,degree,common,lam,scale,ordinaryCutoffs,ordinaryA,ordinaryLo,ordinaryRem,ordinaryLowValue,ordinaryHighValue,ordinaryProduct,ordinaryLoad,sourceLoad,dominatorLoad,MarkedParameters.C,MarkedParameters.W,MarkedParameters.B,MarkedParameters.load,marked0,marked1,marked2,marked3,marked4,marked5,marked6,marked7,marked8,marked9,marked10,marked11,markedParameters,marked,ordinaryCeilings,ordinaryCeiling,sourceCeiling,dominatorCeiling,markedCeiling,headErrorFactor,orientationWeight,rowPatterns,Nat.choose_eq_fast_choose]
  decide +kernel

theorem marked_parameters_2 :
    0 < marked2.a.choose 2 ∧ marked2.a.choose 2+marked2.m*marked2.a ≤ 2*marked2.a.choose 2 ∧
    0 ≤ marked2.u ∧ 0 ≤ marked2.gamma ∧ 0 ≤ marked2.wm ∧ 0 ≤ marked2.W ∧
    (∀ t : Fin (marked2.q+1), 0 ≤ marked2.C t.val) ∧
    (∀ f : Fin (marked2.m+1),
      orientationWeight marked2.q marked2.C f.val ≤ marked2.wm ∧
      orientationWeight marked2.q marked2.C f.val ≤
        marked2.alpha+marked2.beta*f.val+marked2.gamma*(f.val.choose 2)) := by
  simp only [N,degree,common,lam,scale,ordinaryCutoffs,ordinaryA,ordinaryLo,ordinaryRem,ordinaryLowValue,ordinaryHighValue,ordinaryProduct,ordinaryLoad,sourceLoad,dominatorLoad,MarkedParameters.C,MarkedParameters.W,MarkedParameters.B,MarkedParameters.load,marked0,marked1,marked2,marked3,marked4,marked5,marked6,marked7,marked8,marked9,marked10,marked11,markedParameters,marked,ordinaryCeilings,ordinaryCeiling,sourceCeiling,dominatorCeiling,markedCeiling,headErrorFactor,orientationWeight,rowPatterns,Nat.choose_eq_fast_choose]
  decide +kernel

theorem marked_tangents_3 : ∀ d : Fin marked3.a, ∀ t : Fin (marked3.q+1),
    (rowPatterns t.val d.val : ℚ) ≤ marked3.C t.val * marked3.u^d.val := by
  simp only [N,degree,common,lam,scale,ordinaryCutoffs,ordinaryA,ordinaryLo,ordinaryRem,ordinaryLowValue,ordinaryHighValue,ordinaryProduct,ordinaryLoad,sourceLoad,dominatorLoad,MarkedParameters.C,MarkedParameters.W,MarkedParameters.B,MarkedParameters.load,marked0,marked1,marked2,marked3,marked4,marked5,marked6,marked7,marked8,marked9,marked10,marked11,markedParameters,marked,ordinaryCeilings,ordinaryCeiling,sourceCeiling,dominatorCeiling,markedCeiling,headErrorFactor,orientationWeight,rowPatterns,Nat.choose_eq_fast_choose]
  decide +kernel

theorem marked_parameters_3 :
    0 < marked3.a.choose 2 ∧ marked3.a.choose 2+marked3.m*marked3.a ≤ 2*marked3.a.choose 2 ∧
    0 ≤ marked3.u ∧ 0 ≤ marked3.gamma ∧ 0 ≤ marked3.wm ∧ 0 ≤ marked3.W ∧
    (∀ t : Fin (marked3.q+1), 0 ≤ marked3.C t.val) ∧
    (∀ f : Fin (marked3.m+1),
      orientationWeight marked3.q marked3.C f.val ≤ marked3.wm ∧
      orientationWeight marked3.q marked3.C f.val ≤
        marked3.alpha+marked3.beta*f.val+marked3.gamma*(f.val.choose 2)) := by
  simp only [N,degree,common,lam,scale,ordinaryCutoffs,ordinaryA,ordinaryLo,ordinaryRem,ordinaryLowValue,ordinaryHighValue,ordinaryProduct,ordinaryLoad,sourceLoad,dominatorLoad,MarkedParameters.C,MarkedParameters.W,MarkedParameters.B,MarkedParameters.load,marked0,marked1,marked2,marked3,marked4,marked5,marked6,marked7,marked8,marked9,marked10,marked11,markedParameters,marked,ordinaryCeilings,ordinaryCeiling,sourceCeiling,dominatorCeiling,markedCeiling,headErrorFactor,orientationWeight,rowPatterns,Nat.choose_eq_fast_choose]
  decide +kernel

theorem marked_tangents_4 : ∀ d : Fin marked4.a, ∀ t : Fin (marked4.q+1),
    (rowPatterns t.val d.val : ℚ) ≤ marked4.C t.val * marked4.u^d.val := by
  simp only [N,degree,common,lam,scale,ordinaryCutoffs,ordinaryA,ordinaryLo,ordinaryRem,ordinaryLowValue,ordinaryHighValue,ordinaryProduct,ordinaryLoad,sourceLoad,dominatorLoad,MarkedParameters.C,MarkedParameters.W,MarkedParameters.B,MarkedParameters.load,marked0,marked1,marked2,marked3,marked4,marked5,marked6,marked7,marked8,marked9,marked10,marked11,markedParameters,marked,ordinaryCeilings,ordinaryCeiling,sourceCeiling,dominatorCeiling,markedCeiling,headErrorFactor,orientationWeight,rowPatterns,Nat.choose_eq_fast_choose]
  decide +kernel

theorem marked_parameters_4 :
    0 < marked4.a.choose 2 ∧ marked4.a.choose 2+marked4.m*marked4.a ≤ 2*marked4.a.choose 2 ∧
    0 ≤ marked4.u ∧ 0 ≤ marked4.gamma ∧ 0 ≤ marked4.wm ∧ 0 ≤ marked4.W ∧
    (∀ t : Fin (marked4.q+1), 0 ≤ marked4.C t.val) ∧
    (∀ f : Fin (marked4.m+1),
      orientationWeight marked4.q marked4.C f.val ≤ marked4.wm ∧
      orientationWeight marked4.q marked4.C f.val ≤
        marked4.alpha+marked4.beta*f.val+marked4.gamma*(f.val.choose 2)) := by
  simp only [N,degree,common,lam,scale,ordinaryCutoffs,ordinaryA,ordinaryLo,ordinaryRem,ordinaryLowValue,ordinaryHighValue,ordinaryProduct,ordinaryLoad,sourceLoad,dominatorLoad,MarkedParameters.C,MarkedParameters.W,MarkedParameters.B,MarkedParameters.load,marked0,marked1,marked2,marked3,marked4,marked5,marked6,marked7,marked8,marked9,marked10,marked11,markedParameters,marked,ordinaryCeilings,ordinaryCeiling,sourceCeiling,dominatorCeiling,markedCeiling,headErrorFactor,orientationWeight,rowPatterns,Nat.choose_eq_fast_choose]
  decide +kernel

theorem marked_tangents_5 : ∀ d : Fin marked5.a, ∀ t : Fin (marked5.q+1),
    (rowPatterns t.val d.val : ℚ) ≤ marked5.C t.val * marked5.u^d.val := by
  simp only [N,degree,common,lam,scale,ordinaryCutoffs,ordinaryA,ordinaryLo,ordinaryRem,ordinaryLowValue,ordinaryHighValue,ordinaryProduct,ordinaryLoad,sourceLoad,dominatorLoad,MarkedParameters.C,MarkedParameters.W,MarkedParameters.B,MarkedParameters.load,marked0,marked1,marked2,marked3,marked4,marked5,marked6,marked7,marked8,marked9,marked10,marked11,markedParameters,marked,ordinaryCeilings,ordinaryCeiling,sourceCeiling,dominatorCeiling,markedCeiling,headErrorFactor,orientationWeight,rowPatterns,Nat.choose_eq_fast_choose]
  decide +kernel

theorem marked_parameters_5 :
    0 < marked5.a.choose 2 ∧ marked5.a.choose 2+marked5.m*marked5.a ≤ 2*marked5.a.choose 2 ∧
    0 ≤ marked5.u ∧ 0 ≤ marked5.gamma ∧ 0 ≤ marked5.wm ∧ 0 ≤ marked5.W ∧
    (∀ t : Fin (marked5.q+1), 0 ≤ marked5.C t.val) ∧
    (∀ f : Fin (marked5.m+1),
      orientationWeight marked5.q marked5.C f.val ≤ marked5.wm ∧
      orientationWeight marked5.q marked5.C f.val ≤
        marked5.alpha+marked5.beta*f.val+marked5.gamma*(f.val.choose 2)) := by
  simp only [N,degree,common,lam,scale,ordinaryCutoffs,ordinaryA,ordinaryLo,ordinaryRem,ordinaryLowValue,ordinaryHighValue,ordinaryProduct,ordinaryLoad,sourceLoad,dominatorLoad,MarkedParameters.C,MarkedParameters.W,MarkedParameters.B,MarkedParameters.load,marked0,marked1,marked2,marked3,marked4,marked5,marked6,marked7,marked8,marked9,marked10,marked11,markedParameters,marked,ordinaryCeilings,ordinaryCeiling,sourceCeiling,dominatorCeiling,markedCeiling,headErrorFactor,orientationWeight,rowPatterns,Nat.choose_eq_fast_choose]
  decide +kernel

theorem marked_tangents_6 : ∀ d : Fin marked6.a, ∀ t : Fin (marked6.q+1),
    (rowPatterns t.val d.val : ℚ) ≤ marked6.C t.val * marked6.u^d.val := by
  simp only [N,degree,common,lam,scale,ordinaryCutoffs,ordinaryA,ordinaryLo,ordinaryRem,ordinaryLowValue,ordinaryHighValue,ordinaryProduct,ordinaryLoad,sourceLoad,dominatorLoad,MarkedParameters.C,MarkedParameters.W,MarkedParameters.B,MarkedParameters.load,marked0,marked1,marked2,marked3,marked4,marked5,marked6,marked7,marked8,marked9,marked10,marked11,markedParameters,marked,ordinaryCeilings,ordinaryCeiling,sourceCeiling,dominatorCeiling,markedCeiling,headErrorFactor,orientationWeight,rowPatterns,Nat.choose_eq_fast_choose]
  decide +kernel

theorem marked_parameters_6 :
    0 < marked6.a.choose 2 ∧ marked6.a.choose 2+marked6.m*marked6.a ≤ 2*marked6.a.choose 2 ∧
    0 ≤ marked6.u ∧ 0 ≤ marked6.gamma ∧ 0 ≤ marked6.wm ∧ 0 ≤ marked6.W ∧
    (∀ t : Fin (marked6.q+1), 0 ≤ marked6.C t.val) ∧
    (∀ f : Fin (marked6.m+1),
      orientationWeight marked6.q marked6.C f.val ≤ marked6.wm ∧
      orientationWeight marked6.q marked6.C f.val ≤
        marked6.alpha+marked6.beta*f.val+marked6.gamma*(f.val.choose 2)) := by
  simp only [N,degree,common,lam,scale,ordinaryCutoffs,ordinaryA,ordinaryLo,ordinaryRem,ordinaryLowValue,ordinaryHighValue,ordinaryProduct,ordinaryLoad,sourceLoad,dominatorLoad,MarkedParameters.C,MarkedParameters.W,MarkedParameters.B,MarkedParameters.load,marked0,marked1,marked2,marked3,marked4,marked5,marked6,marked7,marked8,marked9,marked10,marked11,markedParameters,marked,ordinaryCeilings,ordinaryCeiling,sourceCeiling,dominatorCeiling,markedCeiling,headErrorFactor,orientationWeight,rowPatterns,Nat.choose_eq_fast_choose]
  decide +kernel

theorem marked_tangents_7 : ∀ d : Fin marked7.a, ∀ t : Fin (marked7.q+1),
    (rowPatterns t.val d.val : ℚ) ≤ marked7.C t.val * marked7.u^d.val := by
  simp only [N,degree,common,lam,scale,ordinaryCutoffs,ordinaryA,ordinaryLo,ordinaryRem,ordinaryLowValue,ordinaryHighValue,ordinaryProduct,ordinaryLoad,sourceLoad,dominatorLoad,MarkedParameters.C,MarkedParameters.W,MarkedParameters.B,MarkedParameters.load,marked0,marked1,marked2,marked3,marked4,marked5,marked6,marked7,marked8,marked9,marked10,marked11,markedParameters,marked,ordinaryCeilings,ordinaryCeiling,sourceCeiling,dominatorCeiling,markedCeiling,headErrorFactor,orientationWeight,rowPatterns,Nat.choose_eq_fast_choose]
  decide +kernel

theorem marked_parameters_7 :
    0 < marked7.a.choose 2 ∧ marked7.a.choose 2+marked7.m*marked7.a ≤ 2*marked7.a.choose 2 ∧
    0 ≤ marked7.u ∧ 0 ≤ marked7.gamma ∧ 0 ≤ marked7.wm ∧ 0 ≤ marked7.W ∧
    (∀ t : Fin (marked7.q+1), 0 ≤ marked7.C t.val) ∧
    (∀ f : Fin (marked7.m+1),
      orientationWeight marked7.q marked7.C f.val ≤ marked7.wm ∧
      orientationWeight marked7.q marked7.C f.val ≤
        marked7.alpha+marked7.beta*f.val+marked7.gamma*(f.val.choose 2)) := by
  simp only [N,degree,common,lam,scale,ordinaryCutoffs,ordinaryA,ordinaryLo,ordinaryRem,ordinaryLowValue,ordinaryHighValue,ordinaryProduct,ordinaryLoad,sourceLoad,dominatorLoad,MarkedParameters.C,MarkedParameters.W,MarkedParameters.B,MarkedParameters.load,marked0,marked1,marked2,marked3,marked4,marked5,marked6,marked7,marked8,marked9,marked10,marked11,markedParameters,marked,ordinaryCeilings,ordinaryCeiling,sourceCeiling,dominatorCeiling,markedCeiling,headErrorFactor,orientationWeight,rowPatterns,Nat.choose_eq_fast_choose]
  decide +kernel

theorem marked_tangents_8 : ∀ d : Fin marked8.a, ∀ t : Fin (marked8.q+1),
    (rowPatterns t.val d.val : ℚ) ≤ marked8.C t.val * marked8.u^d.val := by
  simp only [N,degree,common,lam,scale,ordinaryCutoffs,ordinaryA,ordinaryLo,ordinaryRem,ordinaryLowValue,ordinaryHighValue,ordinaryProduct,ordinaryLoad,sourceLoad,dominatorLoad,MarkedParameters.C,MarkedParameters.W,MarkedParameters.B,MarkedParameters.load,marked0,marked1,marked2,marked3,marked4,marked5,marked6,marked7,marked8,marked9,marked10,marked11,markedParameters,marked,ordinaryCeilings,ordinaryCeiling,sourceCeiling,dominatorCeiling,markedCeiling,headErrorFactor,orientationWeight,rowPatterns,Nat.choose_eq_fast_choose]
  decide +kernel

theorem marked_parameters_8 :
    0 < marked8.a.choose 2 ∧ marked8.a.choose 2+marked8.m*marked8.a ≤ 2*marked8.a.choose 2 ∧
    0 ≤ marked8.u ∧ 0 ≤ marked8.gamma ∧ 0 ≤ marked8.wm ∧ 0 ≤ marked8.W ∧
    (∀ t : Fin (marked8.q+1), 0 ≤ marked8.C t.val) ∧
    (∀ f : Fin (marked8.m+1),
      orientationWeight marked8.q marked8.C f.val ≤ marked8.wm ∧
      orientationWeight marked8.q marked8.C f.val ≤
        marked8.alpha+marked8.beta*f.val+marked8.gamma*(f.val.choose 2)) := by
  simp only [N,degree,common,lam,scale,ordinaryCutoffs,ordinaryA,ordinaryLo,ordinaryRem,ordinaryLowValue,ordinaryHighValue,ordinaryProduct,ordinaryLoad,sourceLoad,dominatorLoad,MarkedParameters.C,MarkedParameters.W,MarkedParameters.B,MarkedParameters.load,marked0,marked1,marked2,marked3,marked4,marked5,marked6,marked7,marked8,marked9,marked10,marked11,markedParameters,marked,ordinaryCeilings,ordinaryCeiling,sourceCeiling,dominatorCeiling,markedCeiling,headErrorFactor,orientationWeight,rowPatterns,Nat.choose_eq_fast_choose]
  decide +kernel

theorem marked_tangents_9 : ∀ d : Fin marked9.a, ∀ t : Fin (marked9.q+1),
    (rowPatterns t.val d.val : ℚ) ≤ marked9.C t.val * marked9.u^d.val := by
  simp only [N,degree,common,lam,scale,ordinaryCutoffs,ordinaryA,ordinaryLo,ordinaryRem,ordinaryLowValue,ordinaryHighValue,ordinaryProduct,ordinaryLoad,sourceLoad,dominatorLoad,MarkedParameters.C,MarkedParameters.W,MarkedParameters.B,MarkedParameters.load,marked0,marked1,marked2,marked3,marked4,marked5,marked6,marked7,marked8,marked9,marked10,marked11,markedParameters,marked,ordinaryCeilings,ordinaryCeiling,sourceCeiling,dominatorCeiling,markedCeiling,headErrorFactor,orientationWeight,rowPatterns,Nat.choose_eq_fast_choose]
  decide +kernel

theorem marked_parameters_9 :
    0 < marked9.a.choose 2 ∧ marked9.a.choose 2+marked9.m*marked9.a ≤ 2*marked9.a.choose 2 ∧
    0 ≤ marked9.u ∧ 0 ≤ marked9.gamma ∧ 0 ≤ marked9.wm ∧ 0 ≤ marked9.W ∧
    (∀ t : Fin (marked9.q+1), 0 ≤ marked9.C t.val) ∧
    (∀ f : Fin (marked9.m+1),
      orientationWeight marked9.q marked9.C f.val ≤ marked9.wm ∧
      orientationWeight marked9.q marked9.C f.val ≤
        marked9.alpha+marked9.beta*f.val+marked9.gamma*(f.val.choose 2)) := by
  simp only [N,degree,common,lam,scale,ordinaryCutoffs,ordinaryA,ordinaryLo,ordinaryRem,ordinaryLowValue,ordinaryHighValue,ordinaryProduct,ordinaryLoad,sourceLoad,dominatorLoad,MarkedParameters.C,MarkedParameters.W,MarkedParameters.B,MarkedParameters.load,marked0,marked1,marked2,marked3,marked4,marked5,marked6,marked7,marked8,marked9,marked10,marked11,markedParameters,marked,ordinaryCeilings,ordinaryCeiling,sourceCeiling,dominatorCeiling,markedCeiling,headErrorFactor,orientationWeight,rowPatterns,Nat.choose_eq_fast_choose]
  decide +kernel

theorem marked_tangents_10 : ∀ d : Fin marked10.a, ∀ t : Fin (marked10.q+1),
    (rowPatterns t.val d.val : ℚ) ≤ marked10.C t.val * marked10.u^d.val := by
  simp only [N,degree,common,lam,scale,ordinaryCutoffs,ordinaryA,ordinaryLo,ordinaryRem,ordinaryLowValue,ordinaryHighValue,ordinaryProduct,ordinaryLoad,sourceLoad,dominatorLoad,MarkedParameters.C,MarkedParameters.W,MarkedParameters.B,MarkedParameters.load,marked0,marked1,marked2,marked3,marked4,marked5,marked6,marked7,marked8,marked9,marked10,marked11,markedParameters,marked,ordinaryCeilings,ordinaryCeiling,sourceCeiling,dominatorCeiling,markedCeiling,headErrorFactor,orientationWeight,rowPatterns,Nat.choose_eq_fast_choose]
  decide +kernel

theorem marked_parameters_10 :
    0 < marked10.a.choose 2 ∧ marked10.a.choose 2+marked10.m*marked10.a ≤ 2*marked10.a.choose 2 ∧
    0 ≤ marked10.u ∧ 0 ≤ marked10.gamma ∧ 0 ≤ marked10.wm ∧ 0 ≤ marked10.W ∧
    (∀ t : Fin (marked10.q+1), 0 ≤ marked10.C t.val) ∧
    (∀ f : Fin (marked10.m+1),
      orientationWeight marked10.q marked10.C f.val ≤ marked10.wm ∧
      orientationWeight marked10.q marked10.C f.val ≤
        marked10.alpha+marked10.beta*f.val+marked10.gamma*(f.val.choose 2)) := by
  simp only [N,degree,common,lam,scale,ordinaryCutoffs,ordinaryA,ordinaryLo,ordinaryRem,ordinaryLowValue,ordinaryHighValue,ordinaryProduct,ordinaryLoad,sourceLoad,dominatorLoad,MarkedParameters.C,MarkedParameters.W,MarkedParameters.B,MarkedParameters.load,marked0,marked1,marked2,marked3,marked4,marked5,marked6,marked7,marked8,marked9,marked10,marked11,markedParameters,marked,ordinaryCeilings,ordinaryCeiling,sourceCeiling,dominatorCeiling,markedCeiling,headErrorFactor,orientationWeight,rowPatterns,Nat.choose_eq_fast_choose]
  decide +kernel

theorem marked_tangents_11 : ∀ d : Fin marked11.a, ∀ t : Fin (marked11.q+1),
    (rowPatterns t.val d.val : ℚ) ≤ marked11.C t.val * marked11.u^d.val := by
  simp only [N,degree,common,lam,scale,ordinaryCutoffs,ordinaryA,ordinaryLo,ordinaryRem,ordinaryLowValue,ordinaryHighValue,ordinaryProduct,ordinaryLoad,sourceLoad,dominatorLoad,MarkedParameters.C,MarkedParameters.W,MarkedParameters.B,MarkedParameters.load,marked0,marked1,marked2,marked3,marked4,marked5,marked6,marked7,marked8,marked9,marked10,marked11,markedParameters,marked,ordinaryCeilings,ordinaryCeiling,sourceCeiling,dominatorCeiling,markedCeiling,headErrorFactor,orientationWeight,rowPatterns,Nat.choose_eq_fast_choose]
  decide +kernel

theorem marked_parameters_11 :
    0 < marked11.a.choose 2 ∧ marked11.a.choose 2+marked11.m*marked11.a ≤ 2*marked11.a.choose 2 ∧
    0 ≤ marked11.u ∧ 0 ≤ marked11.gamma ∧ 0 ≤ marked11.wm ∧ 0 ≤ marked11.W ∧
    (∀ t : Fin (marked11.q+1), 0 ≤ marked11.C t.val) ∧
    (∀ f : Fin (marked11.m+1),
      orientationWeight marked11.q marked11.C f.val ≤ marked11.wm ∧
      orientationWeight marked11.q marked11.C f.val ≤
        marked11.alpha+marked11.beta*f.val+marked11.gamma*(f.val.choose 2)) := by
  simp only [N,degree,common,lam,scale,ordinaryCutoffs,ordinaryA,ordinaryLo,ordinaryRem,ordinaryLowValue,ordinaryHighValue,ordinaryProduct,ordinaryLoad,sourceLoad,dominatorLoad,MarkedParameters.C,MarkedParameters.W,MarkedParameters.B,MarkedParameters.load,marked0,marked1,marked2,marked3,marked4,marked5,marked6,marked7,marked8,marked9,marked10,marked11,markedParameters,marked,ordinaryCeilings,ordinaryCeiling,sourceCeiling,dominatorCeiling,markedCeiling,headErrorFactor,orientationWeight,rowPatterns,Nat.choose_eq_fast_choose]
  decide +kernel

theorem ordinary_load_0 : ordinaryLoad 0 ≤ ordinaryCeiling 0 := by
  simp only [N,degree,common,lam,scale,ordinaryCutoffs,ordinaryA,ordinaryLo,ordinaryRem,ordinaryLowValue,ordinaryHighValue,ordinaryProduct,ordinaryLoad,sourceLoad,dominatorLoad,MarkedParameters.C,MarkedParameters.W,MarkedParameters.B,MarkedParameters.load,marked0,marked1,marked2,marked3,marked4,marked5,marked6,marked7,marked8,marked9,marked10,marked11,markedParameters,marked,ordinaryCeilings,ordinaryCeiling,sourceCeiling,dominatorCeiling,markedCeiling,headErrorFactor,orientationWeight,rowPatterns,Nat.choose_eq_fast_choose]
  decide +kernel
theorem ordinary_load_1 : ordinaryLoad 1 ≤ ordinaryCeiling 1 := by
  simp only [N,degree,common,lam,scale,ordinaryCutoffs,ordinaryA,ordinaryLo,ordinaryRem,ordinaryLowValue,ordinaryHighValue,ordinaryProduct,ordinaryLoad,sourceLoad,dominatorLoad,MarkedParameters.C,MarkedParameters.W,MarkedParameters.B,MarkedParameters.load,marked0,marked1,marked2,marked3,marked4,marked5,marked6,marked7,marked8,marked9,marked10,marked11,markedParameters,marked,ordinaryCeilings,ordinaryCeiling,sourceCeiling,dominatorCeiling,markedCeiling,headErrorFactor,orientationWeight,rowPatterns,Nat.choose_eq_fast_choose]
  decide +kernel
theorem ordinary_load_2 : ordinaryLoad 2 ≤ ordinaryCeiling 2 := by
  simp only [N,degree,common,lam,scale,ordinaryCutoffs,ordinaryA,ordinaryLo,ordinaryRem,ordinaryLowValue,ordinaryHighValue,ordinaryProduct,ordinaryLoad,sourceLoad,dominatorLoad,MarkedParameters.C,MarkedParameters.W,MarkedParameters.B,MarkedParameters.load,marked0,marked1,marked2,marked3,marked4,marked5,marked6,marked7,marked8,marked9,marked10,marked11,markedParameters,marked,ordinaryCeilings,ordinaryCeiling,sourceCeiling,dominatorCeiling,markedCeiling,headErrorFactor,orientationWeight,rowPatterns,Nat.choose_eq_fast_choose]
  decide +kernel
theorem ordinary_load_3 : ordinaryLoad 3 ≤ ordinaryCeiling 3 := by
  simp only [N,degree,common,lam,scale,ordinaryCutoffs,ordinaryA,ordinaryLo,ordinaryRem,ordinaryLowValue,ordinaryHighValue,ordinaryProduct,ordinaryLoad,sourceLoad,dominatorLoad,MarkedParameters.C,MarkedParameters.W,MarkedParameters.B,MarkedParameters.load,marked0,marked1,marked2,marked3,marked4,marked5,marked6,marked7,marked8,marked9,marked10,marked11,markedParameters,marked,ordinaryCeilings,ordinaryCeiling,sourceCeiling,dominatorCeiling,markedCeiling,headErrorFactor,orientationWeight,rowPatterns,Nat.choose_eq_fast_choose]
  decide +kernel
theorem ordinary_load_4 : ordinaryLoad 4 ≤ ordinaryCeiling 4 := by
  simp only [N,degree,common,lam,scale,ordinaryCutoffs,ordinaryA,ordinaryLo,ordinaryRem,ordinaryLowValue,ordinaryHighValue,ordinaryProduct,ordinaryLoad,sourceLoad,dominatorLoad,MarkedParameters.C,MarkedParameters.W,MarkedParameters.B,MarkedParameters.load,marked0,marked1,marked2,marked3,marked4,marked5,marked6,marked7,marked8,marked9,marked10,marked11,markedParameters,marked,ordinaryCeilings,ordinaryCeiling,sourceCeiling,dominatorCeiling,markedCeiling,headErrorFactor,orientationWeight,rowPatterns,Nat.choose_eq_fast_choose]
  decide +kernel
theorem ordinary_load_5 : ordinaryLoad 5 ≤ ordinaryCeiling 5 := by
  simp only [N,degree,common,lam,scale,ordinaryCutoffs,ordinaryA,ordinaryLo,ordinaryRem,ordinaryLowValue,ordinaryHighValue,ordinaryProduct,ordinaryLoad,sourceLoad,dominatorLoad,MarkedParameters.C,MarkedParameters.W,MarkedParameters.B,MarkedParameters.load,marked0,marked1,marked2,marked3,marked4,marked5,marked6,marked7,marked8,marked9,marked10,marked11,markedParameters,marked,ordinaryCeilings,ordinaryCeiling,sourceCeiling,dominatorCeiling,markedCeiling,headErrorFactor,orientationWeight,rowPatterns,Nat.choose_eq_fast_choose]
  decide +kernel
theorem ordinary_load_6 : ordinaryLoad 6 ≤ ordinaryCeiling 6 := by
  simp only [N,degree,common,lam,scale,ordinaryCutoffs,ordinaryA,ordinaryLo,ordinaryRem,ordinaryLowValue,ordinaryHighValue,ordinaryProduct,ordinaryLoad,sourceLoad,dominatorLoad,MarkedParameters.C,MarkedParameters.W,MarkedParameters.B,MarkedParameters.load,marked0,marked1,marked2,marked3,marked4,marked5,marked6,marked7,marked8,marked9,marked10,marked11,markedParameters,marked,ordinaryCeilings,ordinaryCeiling,sourceCeiling,dominatorCeiling,markedCeiling,headErrorFactor,orientationWeight,rowPatterns,Nat.choose_eq_fast_choose]
  decide +kernel
theorem ordinary_load_7 : ordinaryLoad 7 ≤ ordinaryCeiling 7 := by
  simp only [N,degree,common,lam,scale,ordinaryCutoffs,ordinaryA,ordinaryLo,ordinaryRem,ordinaryLowValue,ordinaryHighValue,ordinaryProduct,ordinaryLoad,sourceLoad,dominatorLoad,MarkedParameters.C,MarkedParameters.W,MarkedParameters.B,MarkedParameters.load,marked0,marked1,marked2,marked3,marked4,marked5,marked6,marked7,marked8,marked9,marked10,marked11,markedParameters,marked,ordinaryCeilings,ordinaryCeiling,sourceCeiling,dominatorCeiling,markedCeiling,headErrorFactor,orientationWeight,rowPatterns,Nat.choose_eq_fast_choose]
  decide +kernel
theorem ordinary_load_8 : ordinaryLoad 8 ≤ ordinaryCeiling 8 := by
  simp only [N,degree,common,lam,scale,ordinaryCutoffs,ordinaryA,ordinaryLo,ordinaryRem,ordinaryLowValue,ordinaryHighValue,ordinaryProduct,ordinaryLoad,sourceLoad,dominatorLoad,MarkedParameters.C,MarkedParameters.W,MarkedParameters.B,MarkedParameters.load,marked0,marked1,marked2,marked3,marked4,marked5,marked6,marked7,marked8,marked9,marked10,marked11,markedParameters,marked,ordinaryCeilings,ordinaryCeiling,sourceCeiling,dominatorCeiling,markedCeiling,headErrorFactor,orientationWeight,rowPatterns,Nat.choose_eq_fast_choose]
  decide +kernel
theorem source_load : sourceLoad ≤ sourceCeiling := by
  simp only [N,degree,common,lam,scale,ordinaryCutoffs,ordinaryA,ordinaryLo,ordinaryRem,ordinaryLowValue,ordinaryHighValue,ordinaryProduct,ordinaryLoad,sourceLoad,dominatorLoad,MarkedParameters.C,MarkedParameters.W,MarkedParameters.B,MarkedParameters.load,marked0,marked1,marked2,marked3,marked4,marked5,marked6,marked7,marked8,marked9,marked10,marked11,markedParameters,marked,ordinaryCeilings,ordinaryCeiling,sourceCeiling,dominatorCeiling,markedCeiling,headErrorFactor,orientationWeight,rowPatterns,Nat.choose_eq_fast_choose]
  decide +kernel
theorem dominator_load : dominatorLoad ≤ dominatorCeiling := by
  simp only [N,degree,common,lam,scale,ordinaryCutoffs,ordinaryA,ordinaryLo,ordinaryRem,ordinaryLowValue,ordinaryHighValue,ordinaryProduct,ordinaryLoad,sourceLoad,dominatorLoad,MarkedParameters.C,MarkedParameters.W,MarkedParameters.B,MarkedParameters.load,marked0,marked1,marked2,marked3,marked4,marked5,marked6,marked7,marked8,marked9,marked10,marked11,markedParameters,marked,ordinaryCeilings,ordinaryCeiling,sourceCeiling,dominatorCeiling,markedCeiling,headErrorFactor,orientationWeight,rowPatterns,Nat.choose_eq_fast_choose]
  decide +kernel
theorem marked_load_0 : marked0.load ≤ (marked0.ceiling : ℚ)/scale := by
  simp only [N,degree,common,lam,scale,ordinaryCutoffs,ordinaryA,ordinaryLo,ordinaryRem,ordinaryLowValue,ordinaryHighValue,ordinaryProduct,ordinaryLoad,sourceLoad,dominatorLoad,MarkedParameters.C,MarkedParameters.W,MarkedParameters.B,MarkedParameters.load,marked0,marked1,marked2,marked3,marked4,marked5,marked6,marked7,marked8,marked9,marked10,marked11,markedParameters,marked,ordinaryCeilings,ordinaryCeiling,sourceCeiling,dominatorCeiling,markedCeiling,headErrorFactor,orientationWeight,rowPatterns,Nat.choose_eq_fast_choose]
  decide +kernel
theorem marked_load_1 : marked1.load ≤ (marked1.ceiling : ℚ)/scale := by
  simp only [N,degree,common,lam,scale,ordinaryCutoffs,ordinaryA,ordinaryLo,ordinaryRem,ordinaryLowValue,ordinaryHighValue,ordinaryProduct,ordinaryLoad,sourceLoad,dominatorLoad,MarkedParameters.C,MarkedParameters.W,MarkedParameters.B,MarkedParameters.load,marked0,marked1,marked2,marked3,marked4,marked5,marked6,marked7,marked8,marked9,marked10,marked11,markedParameters,marked,ordinaryCeilings,ordinaryCeiling,sourceCeiling,dominatorCeiling,markedCeiling,headErrorFactor,orientationWeight,rowPatterns,Nat.choose_eq_fast_choose]
  decide +kernel
theorem marked_load_2 : marked2.load ≤ (marked2.ceiling : ℚ)/scale := by
  simp only [N,degree,common,lam,scale,ordinaryCutoffs,ordinaryA,ordinaryLo,ordinaryRem,ordinaryLowValue,ordinaryHighValue,ordinaryProduct,ordinaryLoad,sourceLoad,dominatorLoad,MarkedParameters.C,MarkedParameters.W,MarkedParameters.B,MarkedParameters.load,marked0,marked1,marked2,marked3,marked4,marked5,marked6,marked7,marked8,marked9,marked10,marked11,markedParameters,marked,ordinaryCeilings,ordinaryCeiling,sourceCeiling,dominatorCeiling,markedCeiling,headErrorFactor,orientationWeight,rowPatterns,Nat.choose_eq_fast_choose]
  decide +kernel
theorem marked_load_3 : marked3.load ≤ (marked3.ceiling : ℚ)/scale := by
  simp only [N,degree,common,lam,scale,ordinaryCutoffs,ordinaryA,ordinaryLo,ordinaryRem,ordinaryLowValue,ordinaryHighValue,ordinaryProduct,ordinaryLoad,sourceLoad,dominatorLoad,MarkedParameters.C,MarkedParameters.W,MarkedParameters.B,MarkedParameters.load,marked0,marked1,marked2,marked3,marked4,marked5,marked6,marked7,marked8,marked9,marked10,marked11,markedParameters,marked,ordinaryCeilings,ordinaryCeiling,sourceCeiling,dominatorCeiling,markedCeiling,headErrorFactor,orientationWeight,rowPatterns,Nat.choose_eq_fast_choose]
  decide +kernel
theorem marked_load_4 : marked4.load ≤ (marked4.ceiling : ℚ)/scale := by
  simp only [N,degree,common,lam,scale,ordinaryCutoffs,ordinaryA,ordinaryLo,ordinaryRem,ordinaryLowValue,ordinaryHighValue,ordinaryProduct,ordinaryLoad,sourceLoad,dominatorLoad,MarkedParameters.C,MarkedParameters.W,MarkedParameters.B,MarkedParameters.load,marked0,marked1,marked2,marked3,marked4,marked5,marked6,marked7,marked8,marked9,marked10,marked11,markedParameters,marked,ordinaryCeilings,ordinaryCeiling,sourceCeiling,dominatorCeiling,markedCeiling,headErrorFactor,orientationWeight,rowPatterns,Nat.choose_eq_fast_choose]
  decide +kernel
theorem marked_load_5 : marked5.load ≤ (marked5.ceiling : ℚ)/scale := by
  simp only [N,degree,common,lam,scale,ordinaryCutoffs,ordinaryA,ordinaryLo,ordinaryRem,ordinaryLowValue,ordinaryHighValue,ordinaryProduct,ordinaryLoad,sourceLoad,dominatorLoad,MarkedParameters.C,MarkedParameters.W,MarkedParameters.B,MarkedParameters.load,marked0,marked1,marked2,marked3,marked4,marked5,marked6,marked7,marked8,marked9,marked10,marked11,markedParameters,marked,ordinaryCeilings,ordinaryCeiling,sourceCeiling,dominatorCeiling,markedCeiling,headErrorFactor,orientationWeight,rowPatterns,Nat.choose_eq_fast_choose]
  decide +kernel
theorem marked_load_6 : marked6.load ≤ (marked6.ceiling : ℚ)/scale := by
  simp only [N,degree,common,lam,scale,ordinaryCutoffs,ordinaryA,ordinaryLo,ordinaryRem,ordinaryLowValue,ordinaryHighValue,ordinaryProduct,ordinaryLoad,sourceLoad,dominatorLoad,MarkedParameters.C,MarkedParameters.W,MarkedParameters.B,MarkedParameters.load,marked0,marked1,marked2,marked3,marked4,marked5,marked6,marked7,marked8,marked9,marked10,marked11,markedParameters,marked,ordinaryCeilings,ordinaryCeiling,sourceCeiling,dominatorCeiling,markedCeiling,headErrorFactor,orientationWeight,rowPatterns,Nat.choose_eq_fast_choose]
  decide +kernel
theorem marked_load_7 : marked7.load ≤ (marked7.ceiling : ℚ)/scale := by
  simp only [N,degree,common,lam,scale,ordinaryCutoffs,ordinaryA,ordinaryLo,ordinaryRem,ordinaryLowValue,ordinaryHighValue,ordinaryProduct,ordinaryLoad,sourceLoad,dominatorLoad,MarkedParameters.C,MarkedParameters.W,MarkedParameters.B,MarkedParameters.load,marked0,marked1,marked2,marked3,marked4,marked5,marked6,marked7,marked8,marked9,marked10,marked11,markedParameters,marked,ordinaryCeilings,ordinaryCeiling,sourceCeiling,dominatorCeiling,markedCeiling,headErrorFactor,orientationWeight,rowPatterns,Nat.choose_eq_fast_choose]
  decide +kernel
theorem marked_load_8 : marked8.load ≤ (marked8.ceiling : ℚ)/scale := by
  simp only [N,degree,common,lam,scale,ordinaryCutoffs,ordinaryA,ordinaryLo,ordinaryRem,ordinaryLowValue,ordinaryHighValue,ordinaryProduct,ordinaryLoad,sourceLoad,dominatorLoad,MarkedParameters.C,MarkedParameters.W,MarkedParameters.B,MarkedParameters.load,marked0,marked1,marked2,marked3,marked4,marked5,marked6,marked7,marked8,marked9,marked10,marked11,markedParameters,marked,ordinaryCeilings,ordinaryCeiling,sourceCeiling,dominatorCeiling,markedCeiling,headErrorFactor,orientationWeight,rowPatterns,Nat.choose_eq_fast_choose]
  decide +kernel
theorem marked_load_9 : marked9.load ≤ (marked9.ceiling : ℚ)/scale := by
  simp only [N,degree,common,lam,scale,ordinaryCutoffs,ordinaryA,ordinaryLo,ordinaryRem,ordinaryLowValue,ordinaryHighValue,ordinaryProduct,ordinaryLoad,sourceLoad,dominatorLoad,MarkedParameters.C,MarkedParameters.W,MarkedParameters.B,MarkedParameters.load,marked0,marked1,marked2,marked3,marked4,marked5,marked6,marked7,marked8,marked9,marked10,marked11,markedParameters,marked,ordinaryCeilings,ordinaryCeiling,sourceCeiling,dominatorCeiling,markedCeiling,headErrorFactor,orientationWeight,rowPatterns,Nat.choose_eq_fast_choose]
  decide +kernel
theorem marked_load_10 : marked10.load ≤ (marked10.ceiling : ℚ)/scale := by
  simp only [N,degree,common,lam,scale,ordinaryCutoffs,ordinaryA,ordinaryLo,ordinaryRem,ordinaryLowValue,ordinaryHighValue,ordinaryProduct,ordinaryLoad,sourceLoad,dominatorLoad,MarkedParameters.C,MarkedParameters.W,MarkedParameters.B,MarkedParameters.load,marked0,marked1,marked2,marked3,marked4,marked5,marked6,marked7,marked8,marked9,marked10,marked11,markedParameters,marked,ordinaryCeilings,ordinaryCeiling,sourceCeiling,dominatorCeiling,markedCeiling,headErrorFactor,orientationWeight,rowPatterns,Nat.choose_eq_fast_choose]
  decide +kernel
theorem marked_load_11 : marked11.load ≤ (marked11.ceiling : ℚ)/scale := by
  simp only [N,degree,common,lam,scale,ordinaryCutoffs,ordinaryA,ordinaryLo,ordinaryRem,ordinaryLowValue,ordinaryHighValue,ordinaryProduct,ordinaryLoad,sourceLoad,dominatorLoad,MarkedParameters.C,MarkedParameters.W,MarkedParameters.B,MarkedParameters.load,marked0,marked1,marked2,marked3,marked4,marked5,marked6,marked7,marked8,marked9,marked10,marked11,markedParameters,marked,ordinaryCeilings,ordinaryCeiling,sourceCeiling,dominatorCeiling,markedCeiling,headErrorFactor,orientationWeight,rowPatterns,Nat.choose_eq_fast_choose]
  decide +kernel



end CompactLabeling10007
end
end z16

section z17

section

set_option maxHeartbeats 6000000
open scoped Classical BigOperators

namespace ZL
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]






































theorem sourceIndex_dom (R : V → V → Prop) (a : ℕ) (I : SourceIndex R a) :
    ∀ y ∈ I.2.val, R I.1 y := by
  intro y hy
  exact (Finset.mem_filter.mp ((Finset.mem_powersetCard.mp I.2.property).1 hy)).2

theorem sourceIndex_disjoint (R : V → V → Prop) (hloop : ∀ x, ¬ R x x)
    (a : ℕ) (I : SourceIndex R a) : Disjoint I.2.val {I.1} := by
  apply Finset.disjoint_left.mpr
  intro x hx hs
  have he : x = I.1 := Finset.mem_singleton.mp hs
  subst x
  exact hloop I.1 (sourceIndex_dom R a I I.1 hx)

theorem dominatorIndex_dom (R : V → V → Prop) (a : ℕ) (I : DominatorIndex R a) :
    ∀ x ∈ I.1.val, ∀ y ∈ I.2.val, R x y := by
  intro x hx y hy
  exact (Finset.mem_filter.mp ((Finset.mem_powersetCard.mp I.2.property).1 hy)).2 x hx

theorem dominatorIndex_disjoint (R : V → V → Prop) (hloop : ∀ x, ¬ R x x)
    (a : ℕ) (I : DominatorIndex R a) : Disjoint I.2.val I.1.val := by
  apply Finset.disjoint_left.mpr
  intro x hx hm
  exact hloop x (dominatorIndex_dom R a I x hm x hx)

end
end ZL
end
end z17

section z22

set_option maxHeartbeats 3000000
open scoped Classical BigOperators
noncomputable section

namespace ZL
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem source_incidence_le (R : V → V → Prop) (D c a : ℕ) (ha : 2 ≤ a)
    (hout : ∀ x, (outOn R univ x).card = D)
    (hcommon : ∀ x y, x ≠ y →
      (univ.filter fun z => R z x ∧ R z y).card = c)
    (u v : V) (huv : u ≠ v) (F : Finset (V × Finset V))
    (hF : ∀ p ∈ F, p.2.card = a ∧ (∀ x ∈ p.2, R p.1 x) ∧
      ((u ∈ p.2 ∧ v ∈ p.2) ∨ (p.1 = u ∧ v ∈ p.2))) :
    F.card ≤ D.choose (a-1) + c * D.choose (a-2) := by
  let roots := univ.filter fun z => R z u ∧ R z v
  let Cross : Finset (V × Finset V) :=
    ((outOn R univ u).powersetCard (a-1)).image fun B => (u,insert v B)
  let Ints : Finset (V × Finset V) := roots.biUnion fun z =>
    ((outOn R univ z).powersetCard (a-2)).image fun B => (z,insert u (insert v B))
  have hsub : F ⊆ Cross ∪ Ints := by
    intro p hp
    obtain ⟨hsize,hdom,hcase⟩ := hF p hp
    rcases hcase with ⟨hu,hv⟩ | ⟨hs,hv⟩
    · apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨p.1,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hdom u hu,hdom v hv⟩,?_⟩
      apply Finset.mem_image.mpr
      refine ⟨(p.2.erase u).erase v,?_,?_⟩
      · apply Finset.mem_powersetCard.mpr
        refine ⟨?_,?_⟩
        · intro x hx
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            hdom x (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx))⟩
        · have hv' : v ∈ p.2.erase u := Finset.mem_erase.mpr ⟨huv.symm,hv⟩
          rw [Finset.card_erase_of_mem hv',Finset.card_erase_of_mem hu,hsize]
          omega
      · have hv' : v ∈ p.2.erase u := Finset.mem_erase.mpr ⟨huv.symm,hv⟩
        simp only [Finset.insert_erase hv',Finset.insert_erase hu,Prod.eta]
    · apply Finset.mem_union_left
      apply Finset.mem_image.mpr
      refine ⟨p.2.erase v,?_,?_⟩
      · apply Finset.mem_powersetCard.mpr
        refine ⟨?_,?_⟩
        · intro x hx
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hs ▸ hdom x (Finset.mem_of_mem_erase hx)⟩
        · rw [Finset.card_erase_of_mem hv,hsize]
      · simp only [Finset.insert_erase hv,← hs,Prod.eta]
  have hCross : Cross.card ≤ D.choose (a-1) := by
    calc
      Cross.card ≤ ((outOn R univ u).powersetCard (a-1)).card := Finset.card_image_le
      _ = D.choose (a-1) := by rw [Finset.card_powersetCard,hout]
  have hInts : Ints.card ≤ c * D.choose (a-2) := by
    calc
      Ints.card ≤ ∑ z ∈ roots,
          (((outOn R univ z).powersetCard (a-2)).image
            fun B => (z,insert u (insert v B))).card := Finset.card_biUnion_le
      _ ≤ ∑ _z ∈ roots, D.choose (a-2) := by
        apply Finset.sum_le_sum
        intro z hz
        exact (Finset.card_image_le).trans_eq (by rw [Finset.card_powersetCard,hout])
      _ = c * D.choose (a-2) := by simp [roots,hcommon u v huv]
  exact (Finset.card_le_card hsub).trans
    ((Finset.card_union_le _ _).trans (Nat.add_le_add hCross hInts))

end ZL
end
end z22

section z23

set_option maxHeartbeats 200000
open scoped Classical BigOperators
noncomputable section

namespace ZL
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]



theorem card_commonOutSet_two (R : V → V → Prop) (c : ℕ)
    (hc : ∀ x y, x ≠ y → (univ.filter fun z => R x z ∧ R y z).card = c)
    (M : Finset V) (hM : M.card = 2) : (commonOutSet R M).card = c := by
  obtain ⟨x,y,hxy,rfl⟩ := Finset.card_eq_two.mp hM
  simpa only [commonOutSet,Finset.mem_insert,Finset.mem_singleton,
    forall_eq_or_imp,forall_eq] using hc x y hxy

theorem two_dominator_incidence_le (R : V → V → Prop) (D c a : ℕ) (ha : 2 ≤ a)
    (hin : ∀ x, (univ.filter fun z => R z x).card = D)
    (hcommonIn : ∀ x y, x ≠ y →
      (univ.filter fun z => R z x ∧ R z y).card = c)
    (hcommonOut : ∀ x y, x ≠ y →
      (univ.filter fun z => R x z ∧ R y z).card = c)
    (u v : V) (huv : u ≠ v) (F : Finset (Finset V × Finset V))
    (hF : ∀ p ∈ F, p.1.card = a ∧ p.2.card = 2 ∧
      (∀ y ∈ p.2, ∀ x ∈ p.1, R y x) ∧
      ((u ∈ p.1 ∧ v ∈ p.1) ∨ (u ∈ p.2 ∧ v ∈ p.1))) :
    F.card ≤ c.choose 2 * c.choose (a-2) + D * c.choose (a-1) := by
  let roots := univ.filter fun z => R z u ∧ R z v
  let Pred := (univ.filter fun z => R z v).erase u
  let Ints : Finset (Finset V × Finset V) := (roots.powersetCard 2).biUnion fun M =>
    ((commonOutSet R M).powersetCard (a-2)).image fun B => (insert u (insert v B),M)
  let CrossPart (w : V) : Finset (Finset V × Finset V) :=
    ((commonOutSet R {u,w}).powersetCard (a-1)).image fun B => (insert v B,{u,w})
  let Cross : Finset (Finset V × Finset V) := Pred.biUnion CrossPart
  have hsub : F ⊆ Ints ∪ Cross := by
    intro p hp
    obtain ⟨hsize,hMsize,hdom,hcase⟩ := hF p hp
    rcases hcase with ⟨hu,hv⟩ | ⟨hu,hv⟩
    · apply Finset.mem_union_left
      apply Finset.mem_biUnion.mpr
      refine ⟨p.2,Finset.mem_powersetCard.mpr ⟨?_,hMsize⟩,?_⟩
      · intro y hy
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hdom y hy u hu,hdom y hy v hv⟩
      · apply Finset.mem_image.mpr
        refine ⟨(p.1.erase u).erase v,?_,?_⟩
        · apply Finset.mem_powersetCard.mpr
          refine ⟨?_,?_⟩
          · intro x hx
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun y hy =>
              hdom y hy x (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx))⟩
          · have hv' : v ∈ p.1.erase u := Finset.mem_erase.mpr ⟨huv.symm,hv⟩
            rw [Finset.card_erase_of_mem hv',Finset.card_erase_of_mem hu,hsize]
            omega
        · have hv' : v ∈ p.1.erase u := Finset.mem_erase.mpr ⟨huv.symm,hv⟩
          simp only [Finset.insert_erase hv',Finset.insert_erase hu,Prod.eta]
    · have hecard : (p.2.erase u).card = 1 := by
        rw [Finset.card_erase_of_mem hu,hMsize]
      obtain ⟨w,hw⟩ := Finset.card_eq_one.mp hecard
      have hwm : w ∈ p.2.erase u := hw.symm ▸ Finset.mem_singleton_self w
      have hwu : w ≠ u := (Finset.mem_erase.mp hwm).1
      have hM : p.2 = {u,w} := by rw [← Finset.insert_erase hu,hw]
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨w,Finset.mem_erase.mpr ⟨hwu,Finset.mem_filter.mpr
        ⟨Finset.mem_univ _,hdom w (Finset.mem_of_mem_erase hwm) v hv⟩⟩,?_⟩
      apply Finset.mem_image.mpr
      refine ⟨p.1.erase v,?_,?_⟩
      · apply Finset.mem_powersetCard.mpr
        refine ⟨?_,?_⟩
        · intro x hx
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_univ _,?_⟩
          intro y hy
          exact hdom y (hM.symm ▸ hy) x (Finset.mem_of_mem_erase hx)
        · rw [Finset.card_erase_of_mem hv,hsize]
      · exact Prod.ext (Finset.insert_erase hv) hM.symm
  have hInts : Ints.card ≤ c.choose 2 * c.choose (a-2) := by
    calc
      Ints.card ≤ ∑ M ∈ roots.powersetCard 2,
          (((commonOutSet R M).powersetCard (a-2)).image
            fun B => (insert u (insert v B),M)).card := Finset.card_biUnion_le
      _ ≤ ∑ _M ∈ roots.powersetCard 2, c.choose (a-2) := by
        apply Finset.sum_le_sum
        intro M hM
        exact Finset.card_image_le.trans_eq (by
          rw [Finset.card_powersetCard,
            card_commonOutSet_two R c hcommonOut M (Finset.mem_powersetCard.mp hM).2])
      _ = c.choose 2 * c.choose (a-2) := by
        simp [roots,hcommonIn u v huv,Finset.card_powersetCard]
  have hCross : Cross.card ≤ D * c.choose (a-1) := by
    calc
      Cross.card ≤ ∑ w ∈ Pred, (CrossPart w).card := Finset.card_biUnion_le
      _ ≤ ∑ _w ∈ Pred, c.choose (a-1) := by
        apply Finset.sum_le_sum
        intro w hw
        have hwu : w ≠ u := (Finset.mem_erase.mp hw).1
        have hcard : (commonOutSet R ({u,w} : Finset V)).card = c :=
          card_commonOutSet_two R c hcommonOut {u,w} (by simp [hwu.symm])
        calc
          (CrossPart w).card ≤ ((commonOutSet R {u,w}).powersetCard (a-1)).card :=
            Finset.card_image_le
          _ = c.choose (a-1) := by rw [Finset.card_powersetCard,hcard]
      _ = Pred.card * c.choose (a-1) := by simp
      _ ≤ D * c.choose (a-1) := Nat.mul_le_mul_right _
        ((Finset.card_le_card (Finset.erase_subset u _)).trans_eq (hin v))
  exact (Finset.card_le_card hsub).trans
    ((Finset.card_union_le _ _).trans (Nat.add_le_add hInts hCross))

end ZL
end
end z23

section z24

set_option maxHeartbeats 3000000
open scoped Classical BigOperators
noncomputable section

namespace ZL
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem mem_markedSupport_adj (R : V → V → Prop) (A M : Finset V) (e : V × V)
    (he : e ∈ markedSupport R A M) : R e.1 e.2 := by
  rcases Finset.mem_union.mp he with hi | hc
  · exact (Finset.mem_filter.mp hi).2
  · exact (Finset.mem_filter.mp hc).2



theorem sourceEncode_injective (R : V → V → Prop) (a : ℕ) :
    Function.Injective (sourceEncode R a) := by
  rintro ⟨s,A⟩ ⟨t,B⟩ he
  have hs : s = t := congrArg Prod.fst he
  subst t
  have hA : A = B := Subtype.ext (congrArg Prod.snd he)
  subst B
  rfl

theorem source_family_incidence_le (R : V → V → Prop) (hloop : ∀ x, ¬ R x x)
    (D c a : ℕ) (ha : 2 ≤ a) (hout : ∀ x, (outOn R univ x).card = D)
    (hcommon : ∀ x y, x ≠ y →
      (univ.filter fun z => R z x ∧ R z y).card = c)
    (e : V × V) :
    (univ.filter fun I : SourceIndex R a => e ∈ (sourceFamily R a).support I).card ≤
      D.choose (a-1) + c * D.choose (a-2) := by
  let Is := univ.filter fun I : SourceIndex R a => e ∈ (sourceFamily R a).support I
  by_cases hedge : R e.1 e.2
  · have hne : e.1 ≠ e.2 := by rintro he; exact hloop e.1 (he.symm ▸ hedge)
    have hcard : Is.card = (Is.image (sourceEncode R a)).card :=
      (Finset.card_image_of_injective Is (sourceEncode_injective R a)).symm
    change Is.card ≤ _
    rw [hcard]
    apply source_incidence_le R D c a ha hout hcommon e.1 e.2 hne
    intro p hp
    obtain ⟨I,hi,rfl⟩ := Finset.mem_image.mp hp
    refine ⟨(Finset.mem_powersetCard.mp I.2.property).2,sourceIndex_dom R a I,?_⟩
    have he := (Finset.mem_filter.mp hi).2
    rcases Finset.mem_union.mp he with hi | hc
    · exact Or.inl (Finset.mem_product.mp (Finset.mem_filter.mp hi).1)
    · obtain ⟨hs,ha⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hc).1
      exact Or.inr ⟨(Finset.mem_singleton.mp hs).symm,ha⟩
  · have hz : Is = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro I hi
      exact hedge (mem_markedSupport_adj R I.2.val {I.1} e (Finset.mem_filter.mp hi).2)
    change Is.card ≤ _
    simp only [hz,Finset.card_empty,Nat.zero_le]



theorem dominatorEncode_injective (R : V → V → Prop) (a : ℕ) :
    Function.Injective (dominatorEncode R a) := by
  rintro ⟨M,A⟩ ⟨N,B⟩ he
  have hM : M = N := Subtype.ext (congrArg Prod.snd he)
  subst N
  have hA : A = B := Subtype.ext (congrArg Prod.fst he)
  subst B
  rfl

theorem dominator_family_incidence_le (R : V → V → Prop) (hloop : ∀ x, ¬ R x x)
    (D c a : ℕ) (ha : 2 ≤ a)
    (hin : ∀ x, (univ.filter fun z => R z x).card = D)
    (hcommonIn : ∀ x y, x ≠ y →
      (univ.filter fun z => R z x ∧ R z y).card = c)
    (hcommonOut : ∀ x y, x ≠ y →
      (univ.filter fun z => R x z ∧ R y z).card = c)
    (e : V × V) :
    (univ.filter fun I : DominatorIndex R a => e ∈ (dominatorFamily R a).support I).card ≤
      c.choose 2 * c.choose (a-2) + D * c.choose (a-1) := by
  let Is := univ.filter fun I : DominatorIndex R a => e ∈ (dominatorFamily R a).support I
  by_cases hedge : R e.1 e.2
  · have hne : e.1 ≠ e.2 := by rintro he; exact hloop e.1 (he.symm ▸ hedge)
    have hcard : Is.card = (Is.image (dominatorEncode R a)).card :=
      (Finset.card_image_of_injective Is (dominatorEncode_injective R a)).symm
    change Is.card ≤ _
    rw [hcard]
    apply two_dominator_incidence_le R D c a ha hin hcommonIn hcommonOut e.1 e.2 hne
    intro p hp
    obtain ⟨I,hi,rfl⟩ := Finset.mem_image.mp hp
    refine ⟨(Finset.mem_powersetCard.mp I.2.property).2,
      (Finset.mem_powersetCard.mp I.1.property).2,dominatorIndex_dom R a I,?_⟩
    have he := (Finset.mem_filter.mp hi).2
    rcases Finset.mem_union.mp he with hi | hc
    · exact Or.inl (Finset.mem_product.mp (Finset.mem_filter.mp hi).1)
    · exact Or.inr (Finset.mem_product.mp (Finset.mem_filter.mp hc).1)
  · have hz : Is = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro I hi
      exact hedge (mem_markedSupport_adj R I.2.val I.1.val e (Finset.mem_filter.mp hi).2)
    change Is.card ≤ _
    simp only [hz,Finset.card_empty,Nat.zero_le]

end ZL
end
end z24

section z25

section

set_option maxHeartbeats 6000000
open scoped Classical BigOperators

namespace ZL
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]







theorem sourceFamily_support_bounds (R : V → V → Prop)
    (hloop : ∀ x, ¬ R x x)
    (htour : ∀ x y, x ≠ y → (R x y ↔ ¬ R y x))
    (a : ℕ) (I : SourceIndex R a) :
    ((sourceFamily R a).support I).card = a.choose 2+a := by
  have hc := (Finset.mem_powersetCard.mp I.2.property).2
  have hd := dominatedSupport_card R hloop htour I.2.val {I.1}
    (sourceIndex_disjoint R hloop a I) (by
      intro x hx y hy
      have he := Finset.mem_singleton.mp hx
      subst x
      exact sourceIndex_dom R a I y hy)
  simpa only [sourceFamily,hc,Finset.card_singleton,one_mul] using hd

theorem dominatorFamily_support_bounds (R : V → V → Prop)
    (hloop : ∀ x, ¬ R x x)
    (htour : ∀ x y, x ≠ y → (R x y ↔ ¬ R y x))
    (a : ℕ) (I : DominatorIndex R a) :
    ((dominatorFamily R a).support I).card = a.choose 2+2*a := by
  have hc := (Finset.mem_powersetCard.mp I.2.property).2
  have hm := (Finset.mem_powersetCard.mp I.1.property).2
  have hd := dominatedSupport_card R hloop htour I.2.val I.1.val
    (dominatorIndex_disjoint R hloop a I) (dominatorIndex_dom R a I)
  simpa only [dominatorFamily,hc,hm] using hd

end
end ZL
end
end z25

section z26

set_option maxHeartbeats 2000000
open scoped Classical BigOperators
namespace ZL
noncomputable section
variable {V D : Type*} [Fintype V] [DecidableEq V] [Fintype D] [DecidableEq D]

theorem family_load_of_uniform_probability (F : SupportedFamily V D)
    (M I : ℕ) (p lam : ℚ) (hp0 : 0 ≤ p) (hlam0 : 0 ≤ lam)
    (hp : ∀ d, F.localProbability d ≤ p) (v : V)
    (hi : (Finset.univ.filter (fun d => v ∈ F.support d)).card ≤ I) :
    (∑ d ∈ Finset.univ.filter (fun d => v ∈ F.support d),
      F.localProbability d * lam^M) / 2 ≤ (I : ℚ)*p*lam^M/2 := by
  rw [← Finset.sum_mul]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg hlam0 _)
  calc
    (∑ d ∈ Finset.univ.filter (fun d => v ∈ F.support d), F.localProbability d) ≤
      ∑ _d ∈ Finset.univ.filter (fun d => v ∈ F.support d), p :=
        Finset.sum_le_sum fun d _ => hp d
    _ = ((Finset.univ.filter (fun d => v ∈ F.support d)).card : ℚ)*p := by
      simp only [Finset.sum_const,nsmul_eq_mul]
    _ ≤ (I : ℚ)*p := mul_le_mul_of_nonneg_right (by exact_mod_cast hi) hp0

theorem sourceFamily_load_le (R : V → V → Prop)
    (hloop : ∀ x, ¬ R x x)
    (htour : ∀ x y, x ≠ y → (R x y ↔ ¬ R y x))
    (deg c a : ℕ) (ha : 2 ≤ a)
    (hout : ∀ x, (outOn R Finset.univ x).card = deg)
    (hcommon : ∀ x y, x ≠ y →
      (Finset.univ.filter fun z => R z x ∧ R z y).card = c)
    (lam : ℚ) (hlam : 0 ≤ lam) (e : V × V) :
    (∑ I ∈ Finset.univ.filter (fun I => e ∈ (sourceFamily R a).support I),
      (sourceFamily R a).localProbability I * lam^(a.choose 2+a)) / 2 ≤
      ((deg.choose (a-1)+c*deg.choose (a-2) : ℕ) : ℚ) *
        ((2 : ℚ)^a/(2 : ℚ)^(a.choose 2+a)) * lam^(a.choose 2+a) / 2 := by
  apply family_load_of_uniform_probability (sourceFamily R a) _ _ _ lam (by positivity) hlam
  · intro I
    have h := coherent_localProbability_le (sourceFamily R a) I R I.2.val {I.1}
      rfl (fun _ => Iff.rfl)
    have hA := (Finset.mem_powersetCard.mp I.2.property).2
    have hS := sourceFamily_support_bounds R hloop htour a I
    change (markedSupport R I.2.val {I.1}).card = _ at hS
    simpa only [hA,hS] using h
  · exact source_family_incidence_le R hloop deg c a ha hout hcommon e

theorem dominatorFamily_load_le (R : V → V → Prop)
    (hloop : ∀ x, ¬ R x x)
    (htour : ∀ x y, x ≠ y → (R x y ↔ ¬ R y x))
    (deg c a : ℕ) (ha : 2 ≤ a)
    (hin : ∀ x, (Finset.univ.filter fun z => R z x).card = deg)
    (hcommonIn : ∀ x y, x ≠ y →
      (Finset.univ.filter fun z => R z x ∧ R z y).card = c)
    (hcommonOut : ∀ x y, x ≠ y →
      (Finset.univ.filter fun z => R x z ∧ R y z).card = c)
    (lam : ℚ) (hlam : 0 ≤ lam) (e : V × V) :
    (∑ I ∈ Finset.univ.filter (fun I => e ∈ (dominatorFamily R a).support I),
      (dominatorFamily R a).localProbability I * lam^(a.choose 2+2*a)) / 2 ≤
      ((c.choose 2*c.choose (a-2)+deg*c.choose (a-1) : ℕ) : ℚ) *
        ((2 : ℚ)^a/(2 : ℚ)^(a.choose 2+2*a)) * lam^(a.choose 2+2*a) / 2 := by
  apply family_load_of_uniform_probability (dominatorFamily R a) _ _ _ lam (by positivity) hlam
  · intro I
    have h := coherent_localProbability_le (dominatorFamily R a) I R I.2.val I.1.val
      rfl (fun _ => Iff.rfl)
    have hA := (Finset.mem_powersetCard.mp I.2.property).2
    have hS := dominatorFamily_support_bounds R hloop htour a I
    change (markedSupport R I.2.val I.1.val).card = _ at hS
    simpa only [hA,hS] using h
  · exact dominator_family_incidence_le R hloop deg c a ha hin hcommonIn hcommonOut e

end
end ZL
end z26

section z28

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
open scoped Classical BigOperators
noncomputable section

namespace CompactLabeling10007
open ZL ZL.RowCounting
attribute [local irreducible] N degree common lam
variable {V : Type*} [Fintype V] [DecidableEq V]

















theorem ordinary_tangent (q : Fin 9) : ∀ d : Fin (ordinaryA q),
    rowPatterns q.val d.val * ordinaryLowValue q^d.val * ordinaryHighValue q^ordinaryLo q ≤
      ordinaryLowValue q^(ordinaryLo q+1) * ordinaryHighValue q^d.val := by
  fin_cases q
  · exact ordinary_tangent_0
  · exact ordinary_tangent_1
  · exact ordinary_tangent_2
  · exact ordinary_tangent_3
  · exact ordinary_tangent_4
  · exact ordinary_tangent_5
  · exact ordinary_tangent_6
  · exact ordinary_tangent_7
  · exact ordinary_tangent_8

theorem marked_tangents (i : Fin 12) : ∀ d : Fin (marked i).a, ∀ t : Fin ((marked i).q+1),
    (rowPatterns t.val d.val : ℚ) ≤ (marked i).C t.val * (marked i).u^d.val := by
  fin_cases i
  · exact marked_tangents_0
  · exact marked_tangents_1
  · exact marked_tangents_2
  · exact marked_tangents_3
  · exact marked_tangents_4
  · exact marked_tangents_5
  · exact marked_tangents_6
  · exact marked_tangents_7
  · exact marked_tangents_8
  · exact marked_tangents_9
  · exact marked_tangents_10
  · exact marked_tangents_11

theorem marked_parameters (i : Fin 12) :
    0 < (marked i).a.choose 2 ∧ (marked i).a.choose 2+(marked i).m*(marked i).a ≤ 2*(marked i).a.choose 2 ∧
    0 ≤ (marked i).u ∧ 0 ≤ (marked i).gamma ∧ 0 ≤ (marked i).wm ∧ 0 ≤ (marked i).W ∧
    (∀ t : Fin ((marked i).q+1), 0 ≤ (marked i).C t.val) ∧
    (∀ f : Fin ((marked i).m+1),
      orientationWeight (marked i).q (marked i).C f.val ≤ (marked i).wm ∧
      orientationWeight (marked i).q (marked i).C f.val ≤
        (marked i).alpha+(marked i).beta*f.val+(marked i).gamma*(f.val.choose 2)) := by
  fin_cases i
  · exact marked_parameters_0
  · exact marked_parameters_1
  · exact marked_parameters_2
  · exact marked_parameters_3
  · exact marked_parameters_4
  · exact marked_parameters_5
  · exact marked_parameters_6
  · exact marked_parameters_7
  · exact marked_parameters_8
  · exact marked_parameters_9
  · exact marked_parameters_10
  · exact marked_parameters_11

theorem ordinary_load (q : Fin 9) : ordinaryLoad q ≤ ordinaryCeiling q := by
  fin_cases q
  · exact ordinary_load_0
  · exact ordinary_load_1
  · exact ordinary_load_2
  · exact ordinary_load_3
  · exact ordinary_load_4
  · exact ordinary_load_5
  · exact ordinary_load_6
  · exact ordinary_load_7
  · exact ordinary_load_8

theorem marked_load (i : Fin 12) : (marked i).load ≤ markedCeiling i := by
  fin_cases i
  · exact marked_load_0
  · exact marked_load_1
  · exact marked_load_2
  · exact marked_load_3
  · exact marked_load_4
  · exact marked_load_5
  · exact marked_load_6
  · exact marked_load_7
  · exact marked_load_8
  · exact marked_load_9
  · exact marked_load_10
  · exact marked_load_11





theorem _root_.Sensitivity10007Labeling.Paley10007Verified.CompactLabeling10007.family_coordinate_load_le (R : V → V → Prop)
    (hn : Fintype.card V=N)
    (hloop : ∀ x, ¬ R x x)
    (htour : ∀ x y, x ≠ y → (R x y ↔ ¬ R y x))
    (hout : ∀ x, (outOn R Finset.univ x).card = degree)
    (hin : ∀ x, (inOn R Finset.univ x).card = degree)
    (hcommonIn : ∀ x y, x ≠ y →
      (Finset.univ.filter fun z => R z x ∧ R z y).card = common)
    (hcommonOut : ∀ x y, x ≠ y →
      (Finset.univ.filter fun z => R x z ∧ R y z).card = common)
    (t : FamilyKind) (e : V × V) :
    (∑ d ∈ Finset.univ.filter (fun d => e ∈ (family R t).support d),
      (family R t).localProbability d * lam^exponent t) / 2 ≤ ceiling t := by
  have hlam : 0 ≤ lam := le_trans (by norm_num) (le_of_lt basic_constants.2.2.2.1)
  rcases t with q | i | b
  · obtain ⟨hA2,hAN,hL,hH,hr,hd⟩ := elementary_ordinary q
    have ht : ∀ d < ordinaryA q,
        rowPatterns q.val d * ordinaryLowValue q^d * ordinaryHighValue q^ordinaryLo q ≤
          ordinaryLowValue q^(ordinaryLo q+1) * ordinaryHighValue q^d :=
      fun d hd => ordinary_tangent q ⟨d,hd⟩
    have h := _root_.Sensitivity10007Labeling.Paley10007Verified.CompactLabeling.ordinaryFamily_load_le R N hn hloop htour q.val (ordinaryA q)
      (ordinaryLo q) (ordinaryRem q) (ordinaryLowValue q) (ordinaryHighValue q)
      lam hlam hr hL hH hd ht e.1 e.2
    exact h.trans (ordinary_load q)
  · obtain ⟨hE,hM,hu,hg,hw,hW,hC,hf⟩ := marked_parameters i
    have hC' : ∀ t ≤ (marked i).q, 0 ≤ (marked i).C t :=
      fun t ht => hC ⟨t,Nat.lt_succ_of_le ht⟩
    have ht : ∀ k < (marked i).a, ∀ t ≤ (marked i).q,
        (rowPatterns t k : ℚ) ≤ (marked i).C t*(marked i).u^k :=
      fun k hk t ht => marked_tangents i ⟨k,hk⟩ ⟨t,Nat.lt_succ_of_le ht⟩
    have hp : ∀ f ≤ (marked i).m, orientationWeight (marked i).q (marked i).C f ≤
        (marked i).alpha+(marked i).beta*f+(marked i).gamma*f.choose 2 :=
      fun f hf' => (hf ⟨f,Nat.lt_succ_of_le hf'⟩).2
    have hm : ∀ f ≤ (marked i).m, orientationWeight (marked i).q (marked i).C f ≤ (marked i).wm :=
      fun f hf' => (hf ⟨f,Nat.lt_succ_of_le hf'⟩).1
    have h := _root_.Sensitivity10007Labeling.Paley10007Verified.CompactLabeling.markedFamily_load_le R N degree common hn hloop htour hin hcommonIn
      (marked i).q (marked i).a (marked i).m (marked i).B
      (marked i).u (marked i).C (marked i).alpha (marked i).beta (marked i).gamma
      (marked i).wm (marked i).W lam hu hC' hg hw hW hlam ht hp hm rfl e.1 e.2
    exact h.trans (marked_load i)
  · cases b
    · have h := sourceFamily_load_le R hloop htour degree common 20 (by decide) hout hcommonIn lam hlam e
      have h1 : (20 : ℕ)-1=19 := by decide
      have h2 : (20 : ℕ)-2=18 := by decide
      have hE : (20 : ℕ).choose 2+20=(21 : ℕ).choose 2 := by decide
      rw [h1,h2,hE] at h
      exact h.trans source_load
    · have h := dominatorFamily_load_le R hloop htour degree common 18 (by decide) hin
        hcommonIn hcommonOut lam hlam e
      have h1 : (18 : ℕ)-1=17 := by decide
      have h2 : (18 : ℕ)-2=16 := by decide
      have hE : (18 : ℕ).choose 2+2*18=189 := by decide
      rw [h1,h2,hE] at h
      exact h.trans dominator_load



end CompactLabeling10007
end
end z28

end Sensitivity10007Labeling


