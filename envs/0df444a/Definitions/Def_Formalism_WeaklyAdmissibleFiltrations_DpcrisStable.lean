-- Prove2me | Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_DpcrisStable
-- name    : Formalism_WeaklyAdmissibleFiltrations_DpcrisStable
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:25:33.925928+00:00
-- url     : https://prove2.me/theorems/1085cd50-6de2-4853-880b-4f49fbc5da67
-- title:
--   Dpcris Stable
-- statement:
--   Definitions and structural lemmas for Dpcris Stable, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WeaklyAdmissibleFiltrations/DpcrisStable.lean

import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_StatementPC
import Definitions.Def_Formalism_CoboundaryTransfers_StatementAPI
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
def LiftGal : Prop :=
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
    (A D₀ D₁ D₂ : Type) [CommRing A] [Algebra O A]
    [AddCommGroup D₀] [Module A D₀] [Module O D₀] [IsScalarTower O A D₀]
    [AddCommGroup D₁] [Module A D₁] [Module O D₁] [IsScalarTower O A D₁]
    [AddCommGroup D₂] [Module A D₂] [Module O D₂] [IsScalarTower O A D₂]
    (Bw : Formalism.CoboundaryTransfers.Base O A) (M : ℕ) (W₀ : Formalism.CoboundaryTransfers.WachMod Bw M D₀)
    (W₁ : Formalism.CoboundaryTransfers.WachMod Bw M D₁) (W₂ : Formalism.CoboundaryTransfers.WachMod Bw M D₂) (S : Formalism.CoboundaryTransfers.SES W₀ W₁ W₂)
    (cl₁ : W₁.Z1 →ₗ[O] LatticeCohomology L) (cl₂ : W₂.Z1 →ₗ[O] LatticeCohomology L') (eW e : ℕ)
    (δ : D₀ →ₗ[O] D₀) (R : Polynomial O) (a k : ℕ) (u : O),
    WachLink PD L W₁ cl₁ → WachLink PD L' W₂ cl₂ →
    (∀ (pr : W₁.Z1) (pr' : W₂.Z1), (pr' : D₂ × D₂) = S.π.f2 pr → F.H1map (cl₁ pr) = cl₂ pr') →
    Formalism.CoboundaryTransfers.HfInt W₂ cl₂ (latticeFiniteCohomology PD L') eW →
    Formalism.CoboundaryTransfers.CokerKilled S e → Formalism.CoboundaryTransfers.RatSurj S → Bw.PhiX k → M ≤ k * (a + 1) →
    (∀ y, Bw.X • δ y = W₀.γ y - y) →
    (∀ y, W₀.QInv y → Polynomial.aeval δ (Polynomial.X * R) y ∈ W₀.N) →
    (∀ y, W₀.QInv y → (Bw.p : O) • y ∈ W₀.N → y ∈ W₀.N) →
    (∀ y, W₀.QInv y → (∏ i ∈ Finset.Icc 1 a, (1 - u ^ i)) • y ∈ W₀.N → y ∈ W₀.N) →
    (∀ i, 1 ≤ i → i ≤ a → ∀ n ∈ W₀.N, ∃ n' ∈ W₀.N,
      W₀.γ (Bw.X ^ i • n) = u ^ i • (Bw.X ^ i • n) + Bw.X ^ (i + 1) • n') →
    (∀ n ∈ W₀.N, ∃ z ∈ W₀.N,
      Bw.X ^ (a + 1) • n = Bw.X ^ (a + 1) • z - W₀.φ (Bw.X ^ (a + 1) • z)) →
    ∀ κ ∈ latticeFiniteCohomology PD L', ∃ κ₁ ∈ latticeFiniteCohomology PD L, F.H1map κ₁ =
      ((Bw.p : O) ^ eW * ((Bw.p : O) ^ e * (R.eval 0 * ∏ i ∈ Finset.Icc 1 a, (1 - u ^ i)))) • κ
def NegJumps : Prop :=
  ∀ (G : Type) [Group G] (Qp K₀ K : Type) [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    (B BdR : Type) [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B]
    [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR]
    [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) (LL : Type) [Field LL] [Algebra Qp LL]
    (V : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL) (lo : ℤ),
    FiniteDimensional LL ↥(DdRE PD ρ τ) → lo ≤ 0 → FildR PD ρ τ lo = DdRE PD ρ τ →
    ∑ a ∈ Finset.Ico lo 0, multV PD ρ τ a =
      (finrank LL ↥(DdRE PD ρ τ) : ℤ) - finrank LL ↥(FildR PD ρ τ 0)
def DpcrisStable : Prop :=
  ∀ (G : Type) [Group G] (Qp K₀ K K₀' K' : Type) [Field Qp] [Field K₀] [Field K]
    [Field K₀'] [Field K']
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    [Algebra Qp K₀'] [Algebra Qp K'] [Algebra K₀' K'] [IsScalarTower Qp K₀' K']
    (B BdR : Type) [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra K₀' B] [IsScalarTower Qp K₀' B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    [Algebra K₀' BdR] [Algebra K' BdR] [IsScalarTower Qp K' BdR]
    [IsScalarTower K₀' K' BdR] [IsScalarTower Qp K₀' BdR]
    (PC : PotCrysData G Qp K₀ K K₀' K' B BdR) (LL : Type) [Field LL] [Algebra Qp LL]
    (V : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V) (g : G),
    ∀ x ∈ PC.Dpcris ρ, actVB PC.PD ρ g x ∈ PC.Dpcris ρ
def ExPC : Prop :=
  ∀ (G : Type) [Group G] (Qp K₀ K : Type) [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    (B BdR : Type) [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B]
    [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR]
    [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR),
    ∃ PC : PotCrysData G Qp K₀ K K₀ K B BdR, PC.H = ⊤ ∧ PC.PD = PD
end Formalism.WeaklyAdmissibleFiltrations


