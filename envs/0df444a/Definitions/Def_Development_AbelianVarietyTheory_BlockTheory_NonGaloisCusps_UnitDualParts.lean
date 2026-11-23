-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_UnitDualParts
-- name    : Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_UnitDualParts
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:05:16.938822+00:00
-- url     : https://prove2.me/theorems/1327ea4b-74a3-4ac3-be51-d8d8d135b20b
-- title:
--   Unit Dual Parts
-- statement:
--   Definitions and structural lemmas for Unit Dual Parts, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/NonGaloisCusps/UnitDualParts.lean

import Mathlib
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_Statement
import Definitions.Def_Formalism_CoboundaryTransfers_Statement
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.UnitDualParts
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct
def extMul {O : Type} [CommRing O] (R : Type) [CommRing R] [Algebra O R] {M M' M'' : Type}
    [AddCommGroup M] [Module O M] [AddCommGroup M'] [Module O M'] [AddCommGroup M''] [Module O M'']
    (m : M ⊗[O] M' →ₗ[O] M'') (x : R ⊗[O] M) (y : R ⊗[O] M') : R ⊗[O] M'' :=
  m.baseChange R ((AlgebraTensorModule.distribBaseChange O R M M').symm (x ⊗ₜ[R] y))
def extPair {O : Type} [CommRing O] (R : Type) [CommRing R] [Algebra O R] {M M' : Type}
    [AddCommGroup M] [Module O M] [AddCommGroup M'] [Module O M']
    (β : M →ₗ[O] M' →ₗ[O] O) (x : R ⊗[O] M) (y : R ⊗[O] M') : R :=
  TensorProduct.rid O R (extMul R (TensorProduct.lift β) x y)
section Generic
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
def IsSumLat {T T' T'' : LocLat G Qp LL O} (i : LatHom T.L T''.L) (i' : LatHom T'.L T''.L) : Prop :=
  Function.Bijective (fun p : T.V × T'.V => i.f p.1 + i'.f p.2) ∧
    ∀ z ∈ T''.L.T, ∃ x ∈ T.L.T, ∃ y ∈ T'.L.T, z = i.f x + i'.f y
def IsTensorLat {T T' T'' : LocLat G Qp LL O} (m : ↥T.L.T ⊗[O] ↥T'.L.T ≃ₗ[O] ↥T''.L.T) : Prop :=
  ∀ (g : G) (x : ↥T.L.T) (y : ↥T'.L.T),
    m (T.actT g x ⊗ₜ[O] T'.actT g y) = T''.actT g (m (x ⊗ₜ[O] y))
def SumFor (W : LocWach PD LL O v n) : Prop :=
  ∀ (T T' T'' : LocLat G Qp LL O), IsCrys PD T.ρ → IsCrys PD T'.ρ →
    ∀ (i : LatHom T.L T''.L) (i' : LatHom T'.L T''.L), IsSumLat i i' →
      ∃ σ : (W.DD T × W.DD T') ≃ₗ[W.EE] W.DD T'',
        (∀ x y, σ (x, y) = W.map i x + W.map i' y) ∧
        (∀ x y, W.φD T'' (σ (x, y)) = σ (W.φD T x, W.φD T' y)) ∧
        (∀ (g : W.Gam) x y, W.γD T'' g (σ (x, y)) = σ (W.γD T g x, W.γD T' g y)) ∧
        ∀ x y, σ (x, y) ∈ W.N T'' ↔ (x ∈ W.N T ∧ y ∈ W.N T')
variable {W : LocWach PD LL O v n} {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}
def UnitFor (E : EtTie W RA RW inclR φR gR πA) : Prop :=
  ∀ e₀ : ↥W.one.L.T, Submodule.span O {e₀} = ⊤ →
    ∃ e : W.DD W.one,
      E.jD W.one e = (1 : RW) ⊗ₜ[O] e₀ ∧
      Function.Bijective (fun c : W.EE => c • e) ∧
      W.φD W.one e = e ∧
      (∀ g : W.Gam, W.γD W.one g e = e) ∧
      W.N W.one = Submodule.span (LetA O n) {e}
def TensorFor (E : EtTie W RA RW inclR φR gR πA) : Prop :=
  ∀ (T T' T'' : LocLat G Qp LL O), IsCrys PD T.ρ → IsCrys PD T'.ρ →
    ∀ m : ↥T.L.T ⊗[O] ↥T'.L.T ≃ₗ[O] ↥T''.L.T, IsTensorLat m →
      ∃ μ : W.DD T →ₗ[W.EE] W.DD T' →ₗ[W.EE] W.DD T'',
        (∀ x y, E.jD T'' (μ x y) = extMul RW m.toLinearMap (E.jD T x) (E.jD T' y)) ∧
        Function.Bijective (TensorProduct.lift μ) ∧
        (∀ x y, W.φD T'' (μ x y) = μ (W.φD T x) (W.φD T' y)) ∧
        (∀ (g : W.Gam) x y, W.γD T'' g (μ x y) = μ (W.γD T g x) (W.γD T' g y)) ∧
        ∃ ν : ↥(W.N T) ⊗[LetA O n] ↥(W.N T') ≃ₗ[LetA O n] ↥(W.N T''),
          ∀ (x : ↥(W.N T)) (y : ↥(W.N T')),
            ((ν (x ⊗ₜ[LetA O n] y) : ↥(W.N T'')) : W.DD T'') = μ (x : W.DD T) (y : W.DD T')
def DualFor (E : EtTie W RA RW inclR φR gR πA) : Prop :=
  ∀ (T T' : LocLat G Qp LL O), IsCrys PD T.ρ →
    ∀ Pr : T.V →ₗ[LL] T'.V →ₗ[LL] LL, IsDualLat T.L T'.L Pr →
      ∃ (β : ↥T.L.T →ₗ[O] ↥T'.L.T →ₗ[O] O) (b : W.DD T →ₗ[W.EE] W.DD T' →ₗ[W.EE] W.EE),
        (∀ (x : ↥T.L.T) (y : ↥T'.L.T), Pr (x : T.V) (y : T'.V) = algebraMap O LL (β x y)) ∧
        (∀ x y, E.ioE (b x y) = extPair RW β (E.jD T x) (E.jD T' y)) ∧
        Function.Bijective b ∧ Function.Bijective b.flip ∧
        (∀ x y, b (W.φD T x) (W.φD T' y) = W.φE (b x y)) ∧
        (∀ (g : W.Gam) x y, b (W.γD T g x) (W.γD T' g y) = W.γE g (b x y)) ∧
        (∀ y, y ∈ W.N T' ↔
          ∀ x ∈ W.N T, ∃ a : LetA O n, b x y = algebraMap (LetA O n) W.EE a) ∧
        ∃ δ : ↥(W.N T') ≃ₗ[LetA O n] Module.Dual (LetA O n) ↥(W.N T),
          ∀ (x : ↥(W.N T)) (y : ↥(W.N T')),
            b (x : W.DD T) (y : W.DD T') = algebraMap (LetA O n) W.EE (δ y x)
example {T T' T'' : LocLat G Qp LL O} (μ : W.DD T →ₗ[W.EE] W.DD T' →ₗ[W.EE] W.DD T'')
    (ν : ↥(W.N T) ⊗[LetA O n] ↥(W.N T') ≃ₗ[LetA O n] ↥(W.N T''))
    (hν : ∀ (x : ↥(W.N T)) (y : ↥(W.N T')),
      ((ν (x ⊗ₜ[LetA O n] y) : ↥(W.N T'')) : W.DD T'') = μ (x : W.DD T) (y : W.DD T')) :
    W.N T'' = Submodule.span (LetA O n) {z | ∃ x ∈ W.N T, ∃ y ∈ W.N T', z = μ x y} := by
  apply le_antisymm
  · intro z hz
    obtain ⟨w, hw⟩ := ν.surjective ⟨z, hz⟩
    have hz' : z = ((ν w : ↥(W.N T'')) : W.DD T'') := by rw [hw]
    rw [hz']
    clear hw hz' hz
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => rw [hν]; exact Submodule.subset_span ⟨x, x.2, y, y.2, rfl⟩
    | add a b ha hb => rw [map_add, Submodule.coe_add]; exact Submodule.add_mem _ ha hb
  · rw [Submodule.span_le]
    rintro z ⟨x, hx, y, hy, rfl⟩
    have := hν ⟨x, hx⟩ ⟨y, hy⟩
    simp only at this
    rw [← this]
    exact (ν _).2
end Generic
def UnitPart (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (H : LocHW l P)
    (F : LocFon l P AI H) : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), UnitFor (F.E K s LL h).tie
def SumPart (l : ℕ) [Fact l.Prime] (P : LocPrime l) (H : LocHW l P) : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), SumFor (H.W K s LL h)
def TensorPart (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (H : LocHW l P)
    (F : LocFon l P AI H) : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), TensorFor (F.E K s LL h).tie
def DualPart (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (H : LocHW l P)
    (F : LocFon l P AI H) : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), DualFor (F.E K s LL h).tie
def UnitSumTensorDual (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (H : LocHW l P)
    (F : LocFon l P AI H) : Prop :=
  UnitPart l P AI H F ∧ SumPart l P H ∧ TensorPart l P AI H F ∧ DualPart l P AI H F
end GlobalTheory.IndefiniteRowSideFullHecke.UnitDualParts


