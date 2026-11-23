-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_TensorLatticeUnitPart
-- name    : Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_TensorLatticeUnitPart
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:05:20.864127+00:00
-- url     : https://prove2.me/theorems/ef6a3993-38cc-4ca1-9082-3bc12a7cff55
-- title:
--   Tensor Lattice Unit Part
-- statement:
--   Definitions and structural lemmas for Tensor Lattice Unit Part, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/NonGaloisCusps/TensorLatticeUnitPart.lean

import Mathlib
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
namespace GlobalTheory.IndefiniteRowSideFullHecke.TensorLatticeUnitPart
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct
section Bilinear
variable {O : Type} [CommRing O] (R : Type) [CommRing R] [Algebra O R]
  {M M' M'' : Type} [AddCommGroup M] [AddCommGroup M'] [AddCommGroup M'']
  [Module O M] [Module O M'] [Module O M'']
def extBil (b : M →ₗ[O] M' →ₗ[O] M'') (u : R ⊗[O] M) (w : R ⊗[O] M') : R ⊗[O] M'' :=
  TensorProduct.map (LinearMap.mul' O R) (TensorProduct.lift b)
    (TensorProduct.tensorTensorTensorComm O R M R M' (u ⊗ₜ[O] w))
def extForm (b : M →ₗ[O] M' →ₗ[O] O) (u : R ⊗[O] M) (w : R ⊗[O] M') : R :=
  TensorProduct.rid O R (extBil R b u w)
end Bilinear
section Generic
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
def IsSumLat {T T' T'' : LocLat G Qp LL O} (i : LatHom T.L T''.L) (i' : LatHom T'.L T''.L) : Prop :=
  Function.Bijective (i.f.coprod i'.f) ∧
    ∀ z ∈ T''.L.T, ∃ x ∈ T.L.T, ∃ y ∈ T'.L.T, z = i.f x + i'.f y
def IsTensorLat {T T' T'' : LocLat G Qp LL O} (b : ↥T.L.T →ₗ[O] ↥T'.L.T →ₗ[O] ↥T''.L.T) : Prop :=
  Function.Bijective (TensorProduct.lift b) ∧
    ∀ (g : G) (x : ↥T.L.T) (y : ↥T'.L.T), b (T.actT g x) (T'.actT g y) = T''.actT g (b x y)
variable (W : LocWach PD LL O v n) {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}
def UnitAt (E : EtTie W RA RW inclR φR gR πA) : Prop :=
  ∀ e₀ : ↥W.one.L.T, Submodule.span O {e₀} = ⊤ →
    ∃ e : W.DD W.one, E.jD W.one e = (1 : RW) ⊗ₜ[O] e₀ ∧
      Function.Bijective (fun a : W.EE => a • e) ∧
      W.φD W.one e = e ∧ (∀ g : W.Gam, W.γD W.one g e = e) ∧
      W.N W.one = Submodule.span (LetA O n) {e}
example (E : EtTie W RA RW inclR φR gR πA) : ∃ e₀ : ↥W.one.L.T, Submodule.span O {e₀} = ⊤ := by
  obtain ⟨_, e₀, h, _⟩ := E.one_e
  exact ⟨e₀, h⟩
def SumAt : Prop :=
  ∀ (T T' T'' : LocLat G Qp LL O) (i : LatHom T.L T''.L) (i' : LatHom T'.L T''.L),
    IsCrys PD T.ρ → IsCrys PD T'.ρ → IsSumLat i i' →
      IsCrys PD T''.ρ ∧
      Function.Bijective ((W.map i).coprod (W.map i')) ∧
      (∀ x y, W.φD T'' (W.map i x + W.map i' y) = W.map i (W.φD T x) + W.map i' (W.φD T' y)) ∧
      (∀ (g : W.Gam) x y,
        W.γD T'' g (W.map i x + W.map i' y) = W.map i (W.γD T g x) + W.map i' (W.γD T' g y)) ∧
      ∀ z, z ∈ W.N T'' ↔ ∃ x ∈ W.N T, ∃ y ∈ W.N T', z = W.map i x + W.map i' y
def TensorAt (E : EtTie W RA RW inclR φR gR πA) : Prop :=
  ∀ (T T' T'' : LocLat G Qp LL O) (b : ↥T.L.T →ₗ[O] ↥T'.L.T →ₗ[O] ↥T''.L.T),
    IsCrys PD T.ρ → IsCrys PD T'.ρ → IsTensorLat b →
      IsCrys PD T''.ρ ∧
      ∃ β : W.DD T →ₗ[W.EE] W.DD T' →ₗ[W.EE] W.DD T'',
        (∀ x y, E.jD T'' (β x y) = extBil RW b (E.jD T x) (E.jD T' y)) ∧
        Function.Bijective (TensorProduct.lift β) ∧
        (∀ x y, W.φD T'' (β x y) = β (W.φD T x) (W.φD T' y)) ∧
        (∀ (g : W.Gam) x y, W.γD T'' g (β x y) = β (W.γD T g x) (W.γD T' g y)) ∧
        W.N T'' = Submodule.span (LetA O n) {z | ∃ x ∈ W.N T, ∃ y ∈ W.N T', z = β x y} ∧
        ∃ βN : ↥(W.N T) →ₗ[LetA O n] ↥(W.N T') →ₗ[LetA O n] ↥(W.N T''),
          (∀ x y, (βN x y : W.DD T'') = β (x : W.DD T) (y : W.DD T')) ∧
          Function.Bijective (TensorProduct.lift βN)
def DualAt (E : EtTie W RA RW inclR φR gR πA) : Prop :=
  ∀ (T T' : LocLat G Qp LL O) (Pr : T.V →ₗ[LL] T'.V →ₗ[LL] LL),
    IsCrys PD T.ρ → IsDualLat T.L T'.L Pr →
      IsCrys PD T'.ρ ∧
      ∃ PT : ↥T.L.T →ₗ[O] ↥T'.L.T →ₗ[O] O,
        (∀ x y, algebraMap O LL (PT x y) = Pr (x : T.V) (y : T'.V)) ∧
        ∃ β : W.DD T →ₗ[W.EE] W.DD T' →ₗ[W.EE] W.EE,
          (∀ x y, E.ioE (β x y) = extForm RW PT (E.jD T x) (E.jD T' y)) ∧
          Function.Bijective β ∧ Function.Bijective β.flip ∧
          (∀ x y, β (W.φD T x) (W.φD T' y) = W.φE (β x y)) ∧
          (∀ (g : W.Gam) x y, β (W.γD T g x) (W.γD T' g y) = W.γE g (β x y)) ∧
          (∀ y, y ∈ W.N T' ↔
            ∀ x ∈ W.N T, ∃ a : LetA O n, β x y = algebraMap (LetA O n) W.EE a) ∧
          ∀ f : ↥(W.N T) →ₗ[LetA O n] LetA O n, ∃ y ∈ W.N T',
            ∀ x : ↥(W.N T), β (x : W.DD T) y = algebraMap (LetA O n) W.EE (f x)
end Generic
variable (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (H : LocHW l P)
  (F : LocFon l P AI H)
def UnitPart : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    UnitAt (H.W K s LL h) (F.E K s LL h).tie
def SumPart : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), SumAt (H.W K s LL h)
def TensorPart : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    TensorAt (H.W K s LL h) (F.E K s LL h).tie
def DualPart : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    DualAt (H.W K s LL h) (F.E K s LL h).tie
def WachMonoidal : Prop :=
  UnitPart l P AI H F ∧ SumPart l P H ∧ TensorPart l P AI H F ∧ DualPart l P AI H F
end GlobalTheory.IndefiniteRowSideFullHecke.TensorLatticeUnitPart


