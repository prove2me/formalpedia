-- Prove2me | Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RightIdealImageOfSurjective
-- name    : Formalism_WachLatticeTwists_RamifiedBlockRings_RightIdealImageOfSurjective
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:47:48.560651+00:00
-- url     : https://prove2.me/theorems/03bd1e3f-446b-4a27-842f-8388a31e5248
-- title:
--   Right Ideal Image Of Surjective
-- statement:
--   Definitions and structural lemmas for Right Ideal Image Of Surjective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WachLatticeTwists/RamifiedBlockRings/RightIdealImageOfSurjective.lean

import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_DistinctEigenvalueCornerPerturbation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
namespace Formalism.RepresentationBoundsCohomology.ringDataObjects
open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities
def StatSpanAlg : Prop :=
  ∀ (O K : Type) [CommRing O] [CommRing K] [Algebra O K] (X : Type) (T : Subalgebra O (X → O))
    (d : Type) [Fintype d] [DecidableEq d] (G : Type) [Monoid G] (r : G →* (X → Matrix d d K)),
    ∃ R : Subalgebra O (X → Matrix d d K), (∀ a, a ∈ R ↔ a ∈ tSpan T r) ∧
      ∀ f ∈ T, ∀ a ∈ R, (fun x => algebraMap O K (f x) • a x) ∈ R
def StatOntoSpan : Prop :=
  ∀ (O : Type) [CommRing O] [IsLocalRing O] (n : Type) [Fintype n] [DecidableEq n] (G : Type)
    [Monoid G] (ρ : G →* Matrix n n O), AbsIrr (fun g => (ρ g).map (IsLocalRing.residue O)) →
    Submodule.span O (Set.range ρ) = ⊤
def StatNoeth : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (X' : Type) [Finite X']
    (d : Type) [Fintype d] [DecidableEq d] (R' : Subalgebra O (X' → Matrix d d (FractionRing O))),
    (∀ a ∈ R', ∀ x' i j, ∃ c : O, algebraMap O (FractionRing O) c = a x' i j) → IsNoetherian R' R'
def StatEMat : Prop :=
  ∀ (K : Type) [Field K] (d : Type) [Fintype d] [DecidableEq d] (e x : Matrix d d K) (t : ℕ)
    (α : ℕ → K), 1 ≤ t → e * e = e → e * x = x → x * e = x →
    blockPoly e x = ∏ i ∈ Finset.range t, (Polynomial.X - Polynomial.C (α i)) →
    (∀ i j, i < t → j < t → α i = α j → i = j) →
    let E := e * ((List.range t).tail.map fun i => x - α i • e).prod
    E * E = (∏ i ∈ Finset.Ioo 0 t, (α 0 - α i)) • E ∧ E.rank = 1 ∧ x * E = α 0 • E ∧
      e * E = E ∧ E * e = E ∧ (∏ i ∈ Finset.Ioo 0 t, (α 0 - α i)) ≠ 0
def StatEDiag : Prop :=
  ∀ (A : Type) [CommRing A] (d : Type) [Fintype d] [DecidableEq d] (S : d → Prop) (β : d → A) (t : ℕ)
    (α : ℕ → A),
    let e : Matrix d d A := Matrix.diagonal fun a => if S a then 1 else 0
    let x : Matrix d d A := Matrix.diagonal fun a => if S a then β a else 0
    e * ((List.range t).tail.map fun i => x - α i • e).prod =
      Matrix.diagonal fun a => if S a then ∏ i ∈ Finset.Ioo 0 t, (β a - α i) else 0
def StatIdemKO : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (n : Type) [Fintype n]
    [DecidableEq n] (e : Matrix n n O), e * e = e →
    (e.map (algebraMap O (FractionRing O))).rank = 1 →
    Nonempty (↥(LinearMap.range (matEnd O (KO O) n e)) ≃ₗ[O] KO O)
def SplitPts {O X : Type} [CommRing O] (t : ℕ) (P : X → Polynomial O) : Type :=
  {y : X × (Fin t → O) // P y.1 = ∏ i, (Polynomial.X - Polynomial.C (y.2 i))}
def splitRoot {O X : Type} [CommRing O] (t : ℕ) (P : X → Polynomial O) (i : Fin t) :
    SplitPts t P → O := fun y => y.1.2 i
def splitT {O X : Type} [CommRing O] (T : Subalgebra O (X → O)) (t : ℕ) (P : X → Polynomial O) :
    Subalgebra O (SplitPts t P → O) :=
  Algebra.adjoin O ({f' | ∃ f ∈ T, f' = fun y => f y.1.1} ∪ Set.range (splitRoot t P))
def StatSplitPts : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] (X : Type) (T : Subalgebra O (X → O)) (t : ℕ)
    (P : X → Polynomial O), (∀ k, (fun x => (P x).coeff k) ∈ T) →
    (∀ x, ∃ α : Fin t → O, Function.Injective α ∧
      P x = ∏ i, (Polynomial.X - Polynomial.C (α i))) →
    ∃ b : Fin t.factorial → (SplitPts t P → O),
      (∀ k, b k ∈ splitT T t P) ∧
      (∀ f' ∈ splitT T t P, ∃ a : Fin t.factorial → (X → O), (∀ k, a k ∈ T) ∧
        f' = ∑ k, (fun y => a k y.1.1) * b k) ∧
      (∀ x, ∀ a : Fin t.factorial → O,
        (∀ y : SplitPts t P, y.1.1 = x → ∑ k, a k * b k y = 0) → a = 0)
def StatRootsInt : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (P : Polynomial O) (t : ℕ)
    (α : Fin t → FractionRing O),
    P.map (algebraMap O (FractionRing O)) = ∏ i, (Polynomial.X - Polynomial.C (α i)) →
    ∃ β : Fin t → O, (∀ i, algebraMap O (FractionRing O) (β i) = α i) ∧
      P = ∏ i, (Polynomial.X - Polynomial.C (β i))
def RightIdealImageOfSurjective : Prop :=
  ∀ (O R' : Type) [CommRing O] [Ring R'] [Algebra O R'] (n : Type) [Fintype n] [DecidableEq n]
    (ρ : R' →ₐ[O] Matrix n n O), Function.Surjective ρ → ∀ e₁ : R',
    ∀ A : Matrix n n O, (∃ B, A = ρ e₁ * B) ↔ ∃ a : R', A = ρ (e₁ * a)
def BlockRingDecompositionLemma : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (X d G : Type)
    [Fintype d] [DecidableEq d] [Group G] (t : ℕ) (ht : 1 ≤ t) (bl : d → Fin (t + 1))
    (T : Subalgebra O (X → O)) (D : RingData O X d G t bl) [IsNoetherian D.R' D.R']
    [∀ k, SMulCommClass D.R' O (blockRestrictedRepresentationType bl D.ρk k)], D.Top T ht →
    ∀ (Z : Set X) (NN : Type) [AddCommGroup NN] [Module D.R' NN] (g₀ : ℕ) (n : Fin g₀ → NN),
      Submodule.span D.R' (Set.range n) = ⊤ →
      (∀ x', D.p x' ∉ Z → ∃ φ : NN →ₗ[D.R'] EvalSp O d D.R' x', φ ≠ 0) →
      ((g₀ * Fintype.card d : ℕ) : Cardinal) < Cardinal.mk (IsLocalRing.ResidueField O) →
      vcc T Z (D.p D.π') ≤ ∑ k : Fin (t + 1), Module.length O (NN →ₗ[D.R'] blockRestrictedRepresentationType bl D.ρk k)
end Formalism.RepresentationBoundsCohomology.ringDataObjects


