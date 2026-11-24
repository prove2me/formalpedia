-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MixedFieldContraction_ContractMixedFieldStatement
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MixedFieldContraction_ContractMixedFieldStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:42:31.878069+00:00
-- url     : https://prove2.me/theorems/3b843454-d9a2-4b89-b9c9-3ad487f96388
-- title:
--   Contract Mixed Field Statement
-- statement:
--   Definitions and structural lemmas for Contract Mixed Field Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MixedFieldContraction/ContractMixedFieldStatement.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MixedFieldContraction_GenericFibreKerTarget
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_RationalSections_IsRatSectionOn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_DiagonalDivisors_InhabitBaseStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.AI.I4
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2
section General
def ContractStatement : Prop :=
  ∀ (I : AllFam), I.IsFamily →
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
      (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (d d' : ℕ)
      (L : Fin d' → HermLine ι) (L' : Fin d' → HermLine ι'),
      IsBlockMap κ v → IsArithVar P' d' → IsArithVar (imageZ v P') d → d < d' →
      (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPullHerm κ v (L j) (L' j)) →
      I K' ι' P' d' L' = 0
def ContractMixedStatement : Prop :=
  ∀ (I : AllFam), I.IsFamily →
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
      (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (d₀ d r : ℕ)
      (L : Fin d → HermLine ι) (L' : Fin d → HermLine ι') (N : Fin r → HermLine ι'),
      IsBlockMap κ v → IsArithVar P' (d + r) → IsArithVar (imageZ v P') d₀ → d₀ < d →
      (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPullHerm κ v (L j) (L' j)) → (∀ j, IsSmoothHerm (N j)) →
      I K' ι' P' (d + r) (Fin.append L' N) = 0
def ContractMixedFieldStatement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (J' : IFamily F ι'),
    IsFieldIntersection J' →
    ∀ (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (V' : Ideal (MRingOver F ι')) (d₀ d r : ℕ)
      (L : Fin d → K → ℤ) (N : Fin r → K' → ℤ),
      IsBlockMap κ v → IsProjVarF V' (d + r) → IsProjVarF (imageVar F v V') d₀ → d₀ < d →
      J' V' (d + r) (Fin.append (fun j => pullDeg κ (L j)) N) = 0
def PFStatement : Prop :=
  ∀ (I : AllFam), I.IsFamily →
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
      (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (d r : ℕ)
      (G : GenFibre v P') (J : IFamily G.Φ (fibreIdx ι' κ))
      (L : Fin d → HermLine ι) (L' : Fin d → HermLine ι') (N : Fin r → HermLine ι'),
      IsBlockMap κ v → IsArithVar P' (d + r) → IsArithVar (imageZ v P') d → IsFieldIntersection J →
      (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPullHerm κ v (L j) (L' j)) → (∀ j, IsSmoothHerm (N j)) →
      I K' ι' P' (d + r) (Fin.append L' N) =
        (J (fibreIdeal κ G) r (fun j => fibreDeg κ (N j).a) : ℝ) * I K ι (imageZ v P') d L
def GenDegStatement : Prop :=
  ∀ (I : AllFam), I.IsFamily →
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
      (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (d : ℕ)
      (G : GenFibre v P') (J : IFamily G.Φ (fibreIdx ι' κ))
      (L : Fin d → HermLine ι) (L' : Fin d → HermLine ι'),
      IsBlockMap κ v → IsArithVar P' d → IsArithVar (imageZ v P') d → IsFieldIntersection J →
      (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPullHerm κ v (L j) (L' j)) →
      I K' ι' P' d L' = (J (fibreIdeal κ G) 0 Fin.elim0 : ℝ) * I K ι (imageZ v P') d L
def PFSumStatement : Prop :=
  ∀ (I : AllFam), I.IsFamily →
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (K₂ : Type) [Fintype K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)]
      (P₂ : Ideal (MRing (Sum.elim ι ι₂))) (d : ℕ) (G : GenFibre inlV P₂)
      (J : IFamily G.Φ (fibreIdx (Sum.elim ι ι₂) (Sum.inl : K → K ⊕ K₂)))
      (L : Fin d → HermLine ι) (L' : Fin d → HermLine (Sum.elim ι ι₂)),
      IsArithVar P₂ d → IsArithVar (imageZ inlV P₂) d → IsFieldIntersection J →
      (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPullHerm Sum.inl inlV (L j) (L' j)) →
      I (K ⊕ K₂) (Sum.elim ι ι₂) P₂ d L' = (J (fibreIdeal Sum.inl G) 0 Fin.elim0 : ℝ) * I K ι (imageZ inlV P₂) d L
def ImageCoordStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (Ω : Type) [Field Ω] (y : (Σ k', ι' k') → Ω),
    IsBlockMap κ v → imageZ v (mCoordIdeal y) = mCoordIdeal (y ∘ v)
def PFCoordStatement : Prop :=
  ∀ (I : AllFam), I.IsFamily →
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
      (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (Ω : Type) [Field Ω] [CharZero Ω]
      (y : (Σ k', ι' k') → Ω) (d : ℕ) (L : Fin d → HermLine ι) (L' : Fin d → HermLine ι'),
      IsBlockMap κ v → IsArithVar (mCoordIdeal y) d → IsArithVar (imageZ v (mCoordIdeal y)) d →
      (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPullHerm κ v (L j) (L' j)) →
      I K' ι' (mCoordIdeal y) d L' =
        (IntermediateField.relfinrank (blockFnField (y ∘ v)) (blockFnField y) : ℝ) *
          I K ι (imageZ v (mCoordIdeal y)) d L
def ImageArithStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (d' : ℕ),
    Nonempty K → IsBlockMap κ v → IsArithVar P' d' → ∃ d ≤ d', IsArithVar (imageZ v P') d
def GenFibreExistsStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (d' : ℕ),
    IsBlockMap κ v → IsArithVar P' d' → Nonempty (GenFibre v P')
def FibreDimStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (d r : ℕ) (G : GenFibre v P'),
    IsBlockMap κ v → IsArithVar P' (d + r) → IsArithVar (imageZ v P') d → IsProjVarF (fibreIdeal κ G) r
def PullExistsStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (A : HermLine ι),
    IsBlockMap κ v → ∃ A' : HermLine ι', IsPullHerm κ v A A' ∧ (IsSmoothHerm A → IsSmoothHerm A')
def LineFibreStatement : Prop :=
  ∀ (F : Type) [Field F] (ι₀ : Type) [Fintype ι₀] (Q : Ideal (MRingOver F fun _ : Unit => ι₀))
    (J : IFamily F fun _ : Unit => ι₀),
    IsProjVarF Q 1 → (∃ S : Set (MRingOver F fun _ : Unit => ι₀),
      (∀ f ∈ S, IsMultiHomog f fun _ => 1) ∧ Q = Ideal.span S) → IsFieldIntersection J →
    ∀ m : ℤ, J Q 1 ![fun _ => m] = m
end General
section Graph
def GraphStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K₂ : Type) [Fintype K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)]
    (P : Ideal (MRing ι)) (d : ℕ) (g : (Σ k, ι₂ k) → MRing ι) (δ : K₂ → K → ℕ),
    IsArithVar P d → (∀ q, IsMultiHomog (g q) (δ q.1)) → (∀ k₂, ∃ j, g ⟨k₂, j⟩ ∉ P) →
    IsArithVar (graphIdeal P g) d ∧ imageZ inlV (graphIdeal P g) = P ∧
      ∀ (G : GenFibre inlV (graphIdeal P g)) (J : IFamily G.Φ (fibreIdx (Sum.elim ι ι₂) (Sum.inl : K → K ⊕ K₂))),
        IsFieldIntersection J → J (fibreIdeal Sum.inl G) 0 Fin.elim0 = 1
def ChangeOfModelStatement : Prop :=
  ∀ (I : AllFam), I.IsFamily →
    ∀ (K : Type) [Fintype K] (ι ι₂ : K → Type) [∀ k, Fintype (ι k)] [∀ k, Fintype (ι₂ k)]
      (P : Ideal (MRing ι)) (d : ℕ) (A : ∀ k, ι₂ k → ι k → ℤ)
      (G : GenFibre inrV (graphIdeal P (linForm A)))
      (J : IFamily G.Φ (fibreIdx (Sum.elim ι ι₂) (Sum.inr : K → K ⊕ K)))
      (L : Fin d → HermLine ι₂) (L₁ : Fin d → HermLine ι),
      IsArithVar P d → IsBasePtFree P (linForm A) → IsArithVar (imageZ inrV (graphIdeal P (linForm A))) d →
      IsFieldIntersection J → (∀ j, IsSmoothHerm (L j)) → (∀ j, IsSmoothHerm (L₁ j)) →
      (∀ j, (L₁ j).a = (L j).a) → (∀ j, ∀ z ∈ mcPts P, (L₁ j).h z = (L j).h (linApply A z)) →
      I K ι P d L₁ = (J (fibreIdeal Sum.inr G) 0 Fin.elim0 : ℝ) * I K ι₂ (imageZ inrV (graphIdeal P (linForm A))) d L
end Graph
section WW
def diagonalBlockIndex (j : Fin 2) : T.YBlk → T.WBlk
  | .base => .base
  | .det => .det
  | .line => if j = 0 then .line0 else .line1
def otherLine (j : Fin 2) : T.WBlk := if j = 0 then .line1 else .line0
def PullbackFibresAreLines : Prop :=
  ∀ (I : AllFam), I.IsFamily →
    ∀ (Ω : Type) [Field Ω] (ι ν κ : Type) [Fintype ι] [Fintype ν] [Fintype κ] (E : Type) [AddCommGroup E]
      [Module Ω E] (Φ : Type) [Field Φ] [Algebra Ω Φ] (x : ι → Ω) (B : ChartBundle ℤ x 2 E)
      (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) (δ : ν → Ω) (a : Fin 2 → Φ) (j : Fin 2) (D : ℕ)
      (L : Fin (D + 1) → HermLine (T.yyIdx ι ν κ)) (L' : Fin (D + 1) → HermLine (T.wwIdx ι ν κ))
      (N : HermLine (T.wwIdx ι ν κ)),
      T.IsTwistedDualSec B φ → T.IsTwistedDualGen B φ → T.IsTwistedDetGen B e δ → (∃ i, x i ≠ 0) →
      AlgebraicIndependent Ω a →
      IsArithVar (T.yyIdeal x δ e φ (a j)) (D + 1) → IsArithVar (T.wwIdeal x δ e φ (a 0) (a 1)) (D + 2) →
      (∀ i, IsSmoothHerm (L i)) → (∀ i, IsPullHerm (diagonalBlockIndex j) (T.yyEmb j) (L i) (L' i)) → IsSmoothHerm N →
      I T.WBlk (T.wwIdx ι ν κ) (T.wwIdeal x δ e φ (a 0) (a 1)) (D + 2) (Fin.snoc (α := fun _ => _) L' N) =
        (N.a (otherLine j) : ℝ) * I T.YBlk (T.yyIdx ι ν κ) (T.yyIdeal x δ e φ (a j)) (D + 1) L
def PullbackProductVanishing : Prop :=
  ∀ (I : AllFam), I.IsFamily →
    ∀ (Ω : Type) [Field Ω] (ι ν κ : Type) [Fintype ι] [Fintype ν] [Fintype κ] (E : Type) [AddCommGroup E]
      [Module Ω E] (Φ : Type) [Field Φ] [Algebra Ω Φ] (x : ι → Ω) (B : ChartBundle ℤ x 2 E)
      (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) (δ : ν → Ω) (a : Fin 2 → Φ) (j : Fin 2) (D : ℕ)
      (L : Fin (D + 2) → HermLine (T.yyIdx ι ν κ)) (L' : Fin (D + 2) → HermLine (T.wwIdx ι ν κ)),
      T.IsTwistedDualSec B φ → T.IsTwistedDualGen B φ → T.IsTwistedDetGen B e δ → (∃ i, x i ≠ 0) →
      AlgebraicIndependent Ω a →
      IsArithVar (T.yyIdeal x δ e φ (a j)) (D + 1) → IsArithVar (T.wwIdeal x δ e φ (a 0) (a 1)) (D + 2) →
      (∀ i, IsSmoothHerm (L i)) → (∀ i, IsPullHerm (diagonalBlockIndex j) (T.yyEmb j) (L i) (L' i)) →
      I T.WBlk (T.wwIdx ι ν κ) (T.wwIdeal x δ e φ (a 0) (a 1)) (D + 2) L' = 0
def YYBlockMapStatement : Prop :=
  ∀ (ι ν κ : Type) (j : Fin 2), IsBlockMap (diagonalBlockIndex j) (T.yyEmb (ι := ι) (ν := ν) (κ := κ) j)
end WW
section Inhabit
def InhabitIdStatement : Prop :=
  IsArithVar (⊥ : Ideal (MRing (PBlk 2))) 2 ∧ imageZ id (⊥ : Ideal (MRing (PBlk 2))) = ⊥ ∧
    Nonempty (GenFibre (ι := PBlk 2) (ι' := PBlk 2) id ⊥)
def InhabitLineStatement : Prop :=
  IsArithVar (⊥ : Ideal (MRing (Sum.elim (PBlk 1) (PBlk 2)))) 2 ∧
    IsArithVar (imageZ inlV (⊥ : Ideal (MRing (Sum.elim (PBlk 1) (PBlk 2))))) 1 ∧
    Nonempty (GenFibre (inlV (ι := PBlk 1) (ι₂ := PBlk 2)) ⊥) ∧
    ∀ (G : GenFibre (inlV (ι := PBlk 1) (ι₂ := PBlk 2)) ⊥)
      (J : IFamily G.Φ (fibreIdx (Sum.elim (PBlk 1) (PBlk 2)) (Sum.inl : Unit → Unit ⊕ Unit))),
      IsFieldIntersection J → ∀ m : ℤ, J (fibreIdeal Sum.inl G) 1 ![fun _ => m] = m
def idMat (n : ℕ) : ∀ _ : Unit, Fin n → Fin n → ℤ := fun _ i j => if i = j then 1 else 0
def InhabitModelStatement : Prop :=
  IsArithVar (⊥ : Ideal (MRing (PBlk 2))) 2 ∧ IsBasePtFree (⊥ : Ideal (MRing (PBlk 2))) (linForm (idMat 2)) ∧
    IsArithVar (imageZ inrV (graphIdeal (⊥ : Ideal (MRing (PBlk 2))) (linForm (idMat 2)))) 2 ∧
    Nonempty (GenFibre (inrV (ι := PBlk 2) (ι₂ := PBlk 2)) (graphIdeal ⊥ (linForm (idMat 2))))
end Inhabit
end ReciprocityTheory.ChartRestriction.G.AI.I4


