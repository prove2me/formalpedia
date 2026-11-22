-- Prove2me | Definitions.Def_Formalism_CharacterColumnKernels_StatementGC
-- name    : Formalism_CharacterColumnKernels_StatementGC
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:07:51.942807+00:00
-- url     : https://prove2.me/theorems/26ebc60f-2a58-475a-aa6d-9a4c94560b1a
-- title:
--   Statement GC
-- statement:
--   Definitions and structural lemmas for Statement GC, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/StatementGC.lean

import Definitions.Def_Formalism_CharacterColumnKernels_StatGlobalModule
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
namespace Formalism.NG
instance evalSpSMulComm (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {X' : Type*}
    (d : Type*) [Fintype d] [DecidableEq d] (R' : Subalgebra O (X' → Matrix d d (FractionRing O)))
    (x' : X') : SMulCommClass R' (FractionRing O) (EvalSp O d R' x') :=
  ⟨fun r c v => by
    show (matEnd (FractionRing O) (FractionRing O) d (evalAt O d R' x' r)) (c • v) =
      c • (matEnd (FractionRing O) (FractionRing O) d (evalAt O d R' x' r)) v
    exact LinearMap.map_smul _ c v⟩
def StatGlobalColumn : Prop :=
  ∀ (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (X X' : Type*)
    (T : Subalgebra O (X → O)) (T' : Subalgebra O (X' → O)) (Z : Set X) (p : X' → X) (q : ℕ)
    (b : Fin q → (X' → O)),
    (∀ f' ∈ T', ∃ a : Fin q → (X → O), (∀ k, a k ∈ T) ∧ f' = ∑ k, (a k ∘ p) * b k) →
    (∀ x ∉ Z, ∀ a : Fin q → O, (∀ x', p x' = x → ∑ k, a k * b k x' = 0) → a = 0) →
    ∀ (d : Type) [Fintype d] [DecidableEq d] (R' : Subalgebra O (X' → Matrix d d (FractionRing O)))
      [IsNoetherian R' R'],
    (∀ (g : Type) [Fintype g] [DecidableEq g] (Θ : Matrix g g R'), ∃ f ∈ T', ∀ x',
      algebraMap O (FractionRing O) (f x') =
        (bigMat (fun r : R' => (r : X' → Matrix d d (FractionRing O)) x') Θ).det) →
    ∀ (Tc : Type*) [CommRing Tc] [Algebra Tc R'] [∀ x', Module Tc (EvalSp O d R' x')]
      [∀ x', IsScalarTower Tc R' (EvalSp O d R' x')]
      (G : Type*) [Group G] (r : G →* R') (χ : G →* Tcˣ) (E e₁ : R') (δ : Tc)
      (ι : Type*) [Fintype ι] [DecidableEq ι] (D : ι → Subgroup G) (j : ι → ℕ)
      (Kc : ∀ l, Fin (j l) → G → R') (k0 : ι → G → R'),
      E * E = algebraMap Tc R' δ * E → e₁ * e₁ = e₁ →
    (∀ x', p x' ∉ Z →
      ∃ δx : FractionRing O, δx ≠ 0 ∧ (∀ v : EvalSp O d R' x', δ • v = δx • v) ∧
      Module.finrank (FractionRing O)
        (LinearMap.range (DistribSMul.toLinearMap (FractionRing O) (EvalSp O d R' x') E)) = 1 ∧
      Module.finrank (FractionRing O)
        (LinearMap.range (DistribSMul.toLinearMap (FractionRing O) (EvalSp O d R' x') e₁)) = 1 ∧
      (∀ η ∈ LinearMap.range (DistribSMul.toLinearMap (FractionRing O) (EvalSp O d R' x') E), η ≠ 0 →
        ∃ g : G, ((((χ g)⁻¹ : Tcˣ) : Tc) • r g) • η ≠ η) ∧
      (∀ l, ∃ L : Submodule (FractionRing O) (D l → EvalSp O d R' x'),
        LinearMap.range (colD (K := FractionRing O) (V := EvalSp O d R' x') r χ (D l)) ≤ L ∧
        (∀ a, ∀ s ∈ LinearMap.range
            (DistribSMul.toLinearMap (FractionRing O) (EvalSp O d R' x') e₁),
          (fun g : D l => Kc l a g • s) ∈ L) ∧
        (∀ s ∈ LinearMap.range (DistribSMul.toLinearMap (FractionRing O) (EvalSp O d R' x') E),
          (fun g : D l => k0 l g • s) ∈ L) ∧
        Module.rank (FractionRing O)
            (L ⧸ (LinearMap.range (colD (K := FractionRing O) (V := EvalSp O d R' x') r χ (D l))).comap
              L.subtype) ≤
          (j l + Module.finrank (FractionRing O)
            (LinearMap.ker (colD (K := FractionRing O) (V := EvalSp O d R' x') r χ (D l))) : ℕ))) →
    ∀ (g₀ : ℕ) (n : Fin g₀ → ColNNJ r χ E e₁ δ D j Kc k0),
      Submodule.span R' (Set.range n) = ⊤ →
    ∀ (π' : X') (ρπ : R' →ₐ[O] Matrix d d O),
      (∀ r : R', (ρπ r).map (algebraMap O (FractionRing O)) = (r : X' → Matrix d d (FractionRing O)) π') →
    ∀ (α : Type) [LinearOrder α] [Fintype α] (bl : d → α), (∀ r, (ρπ r).BlockTriangular bl) →
    ∀ (ρk : ∀ k : α, R' →ₐ[O] Matrix {a // bl a = k} {a // bl a = k} O),
      (∀ k, Function.Surjective (ρk k)) → (∀ r k, (ρπ r).toSquareBlock bl k = ρk k r) →
      [∀ k, SMulCommClass R' O (LatQ O {a // bl a = k} (ρk k).toRingHom)] →
      ((g₀ * ∑ k : α, Fintype.card {a // bl a = k} : ℕ) : Cardinal) <
        Cardinal.mk (IsLocalRing.ResidueField O) →
      vcc T Z (p π') ≤
        ∑ k ∈ univ.image bl,
          Module.length O (ColNNJ r χ E e₁ δ D j Kc k0 →ₗ[R'] LatQ O {a // bl a = k} (ρk k).toRingHom)
end Formalism.NG


