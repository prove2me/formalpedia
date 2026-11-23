-- Prove2me | Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CocyclesFunctorial
-- name    : Formalism_WeaklyAdmissibleFiltrations_CocyclesFunctorial
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:04:35.174123+00:00
-- url     : https://prove2.me/theorems/439898b8-b74a-49b0-9ec9-15d251e74d36
-- title:
--   Cocycles Functorial
-- statement:
--   Definitions and structural lemmas for Cocycles Functorial, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WeaklyAdmissibleFiltrations/CocyclesFunctorial.lean

import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.WeaklyAdmissibleFiltrations
open Module TensorProduct
def THWindow : Prop :=
  ∀ (LL : Type) [Field LL] (D : Type) [AddCommGroup D] [Module LL D] [FiniteDimensional LL D]
    (n : ℕ) (Emb : Type) [Fintype Emb] (F : FilPhi LL D n Emb) (D' : Submodule LL D) (l h : ℤ),
    l ≤ F.lo → F.hi ≤ h → F.tHw D' l h = F.tH D'
def DimSum : Prop :=
  ∀ (LL : Type) [Field LL] (D : Type) [AddCommGroup D] [Module LL D] [FiniteDimensional LL D]
    (n : ℕ) (Emb : Type) [Fintype Emb] (F : FilPhi LL D n Emb) (D' : Submodule LL D) (τ : Emb),
    ∑ a ∈ Finset.Ico F.lo F.hi, F.mult D' τ a = (finrank LL ↥(F.Dl (F.letter τ) ⊓ D') : ℤ)
def JumpsIcc : Prop :=
  ∀ (LL : Type) [Field LL] (D : Type) [AddCommGroup D] [Module LL D]
    (n : ℕ) (Emb : Type) [Fintype Emb] (F : FilPhi LL D n Emb) (τ : Emb) (l h : ℤ),
    F.JumpsIn τ (Set.Icc l h) ↔ F.Fil τ l = F.Dl (F.letter τ) ∧ F.Fil τ (h + 1) = ⊥
def SubTopBot : Prop :=
  ∀ (LL : Type) [Field LL] (D : Type) [AddCommGroup D] [Module LL D]
    (n : ℕ) (Emb : Type) [Fintype Emb] (F : FilPhi LL D n Emb), F.IsSub ⊤ ∧ F.IsSub ⊥
def RankOneWA : Prop :=
  ∀ (LL : Type) [Field LL] (D : Type) [AddCommGroup D] [Module LL D] [FiniteDimensional LL D]
    (n : ℕ) [NeZero n] (Emb : Type) [Fintype Emb] (F : FilPhi LL D n Emb)
    (v : AddValuation LL (WithTop ℚ)), (∀ i, finrank LL ↥(F.Dl i) = 1) →
    (F.WeaklyAdmissible v ↔
      (((F.tH ⊤ : ℚ)) : WithTop ℚ) = F.e • v (LinearMap.det (F.φ : D →ₗ[LL] D)))
def ExWA : Prop :=
  ∀ (LL : Type) [Field LL] (v : AddValuation LL (WithTop ℚ)) (l : LL), v l = 1 →
    ∀ (n : ℕ) [NeZero n], ∃ (D : Type) (_ : AddCommGroup D) (_ : Module LL D)
      (_ : FiniteDimensional LL D) (F F' : FilPhi LL D n (ZMod n)),
      F.WeaklyAdmissible v ∧ (∀ τ, F.IsJump τ (-1)) ∧ ¬ F'.WeaklyAdmissible v
def CobF : Prop :=
  ∀ (G : Type) [Group G] (Qp K₀ K : Type) [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    (B BdR : Type) [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B]
    [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR]
    [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) (LL : Type) [Field LL] [Algebra Qp LL]
    (V : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V) [TopologicalSpace G] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousConstSMul LL V],
    (∀ x, Continuous fun g => ρ g x) → B1 ρ ≤ finiteCocycles PD ρ ∧ finiteCocycles PD ρ ≤ continuousCocycles ρ
def TorsFreeT : Prop :=
  ∀ (G : Type) [Group G] (Qp K₀ K : Type) [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    (B BdR : Type) [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B]
    [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR]
    [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) (LL : Type) [Field LL] [Algebra Qp LL]
    (O : Type) [CommRing O] [Algebra O LL]
    (V : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [Module O V] [IsScalarTower O LL V]
    (ρ : Representation LL G V) [TopologicalSpace G] [TopologicalSpace V]
    [ContinuousAdd V] [ContinuousConstSMul LL V] (L : Lattice (O := O) ρ) (c : G → V) (a : O),
    c ∈ latticeCocycles L → algebraMap O LL a ≠ 0 → a • c ∈ latticeFiniteCocycles PD L → c ∈ latticeFiniteCocycles PD L
def CocyclesFunctorial : Prop :=
  ∀ (G : Type) [Group G] (Qp K₀ K : Type) [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    (B BdR : Type) [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B]
    [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR]
    [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) (LL : Type) [Field LL] [Algebra Qp LL]
    (V V' : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    (ρ : Representation LL G V) (ρ' : Representation LL G V') [TopologicalSpace G]
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]
    [TopologicalSpace V'] [ContinuousAdd V'] [ContinuousConstSMul LL V']
    (f : V →ₗ[LL] V'), Continuous f → (∀ g x, f (ρ g x) = ρ' g (f x)) →
    ∀ c, (c ∈ continuousCocycles ρ → f ∘ c ∈ continuousCocycles ρ') ∧ (c ∈ finiteCocycles PD ρ → f ∘ c ∈ finiteCocycles PD ρ')
def ImFLe : Prop :=
  ∀ (G : Type) [Group G] (Qp K₀ K : Type) [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    (B BdR : Type) [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B]
    [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR]
    [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) (LL : Type) [Field LL] [Algebra Qp LL]
    (O : Type) [CommRing O] [Algebra O LL]
    (V V' : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [Module O V] [IsScalarTower O LL V]
    [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    [Module O V'] [IsScalarTower O LL V']
    (ρ : Representation LL G V) (ρ' : Representation LL G V') [TopologicalSpace G]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousConstSMul LL V]
    [TopologicalSpace V'] [IsTopologicalAddGroup V'] [ContinuousConstSMul LL V']
    (L : Lattice (O := O) ρ) (L' : Lattice (O := O) ρ') (F : LatHom L L'),
    (∀ x, Continuous fun g => ρ' g x) → F.ImF PD ≤ latticeFiniteCocycles PD L' ∧ (F.col PD = 0 ↔ F.LiftF PD 0)
def TrivCrys : Prop :=
  ∀ (G : Type) [Group G] (Qp K₀ K : Type) [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    (B BdR : Type) [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B]
    [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR]
    [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) (LL : Type) [Field LL] [Algebra Qp LL]
    [FiniteDimensional Qp LL] [FiniteDimensional Qp K₀],
    IsCrys PD (1 : Representation LL G LL)
def ExLattice : Prop :=
  ∀ (G : Type) [Group G] (LL : Type) [Field LL] (O : Type) [CommRing O] [IsDomain O]
    [Algebra O LL], Function.Injective (algebraMap O LL) →
    Nonempty (Lattice (O := O) (1 : Representation LL G LL))
def ExPD : Prop :=
  Nonempty (PeriodData (Multiplicative ℤ) ℚ ℚ ℚ (LaurentPolynomial ℚ) (LaurentPolynomial ℚ))
def WachCol : Prop :=
  ∀ (G : Type) [Group G] (Qp K₀ K : Type) [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    (B BdR : Type) [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B]
    [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR]
    [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) (LL : Type) [Field LL] [Algebra Qp LL]
    (O : Type) [CommRing O] [Algebra O LL]
    (V V' : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [Module O V] [IsScalarTower O LL V]
    [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    [Module O V'] [IsScalarTower O LL V']
    (ρ : Representation LL G V) (ρ' : Representation LL G V') [TopologicalSpace G]
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]
    [TopologicalSpace V'] [ContinuousAdd V'] [ContinuousConstSMul LL V']
    (L : Lattice (O := O) ρ) (L' : Lattice (O := O) ρ') (F : LatHom L L')
    (A D D' : Type) [CommRing A] [Algebra O A] [AddCommGroup D] [Module A D] [Module O D]
    [IsScalarTower O A D] [AddCommGroup D'] [Module A D'] [Module O D'] [IsScalarTower O A D']
    (Bw : Formalism.CoboundaryTransfers.Base O A) (M : ℕ) (W : Formalism.CoboundaryTransfers.WachMod Bw M D)
    (W' : Formalism.CoboundaryTransfers.WachMod Bw M D') (Fw : Formalism.CoboundaryTransfers.Hom W W')
    (cl : W.Z1 →ₗ[O] LatticeCohomology L) (cl' : W'.Z1 →ₗ[O] LatticeCohomology L'),
    Bw.p = PD.p → WachLink PD L W cl → WachLink PD L' W' cl' →
    (∀ (pr : W.Z1) (pr' : W'.Z1), (pr' : D' × D') = Fw.f2 pr → F.H1map (cl pr) = cl' pr') →
    F.col PD = Fw.col ∧ ∀ e, F.LiftF PD e ↔ Fw.LiftF e
end Formalism.WeaklyAdmissibleFiltrations


