-- Prove2me | Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ConstantCoeffPolyAdd
-- name    : Formalism_SharpRestriction_Divisibility_GeneratorPowers_ConstantCoeffPolyAdd
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:44:17.720808+00:00
-- url     : https://prove2.me/theorems/0345f08d-c33a-41ec-82a4-3b635858a0e2
-- title:
--   Constant Coeff Poly Add
-- statement:
--   Definitions and structural lemmas for Constant Coeff Poly Add, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ConstantCoeffPolyAdd.lean

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndEncPf
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsExpChart
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_KillAdd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
namespace Formalism.MainNotions.ModuliIntegralCharts.H1
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
def colIdx {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {n : ℕ}
    (m : LtN Dw n →₀ ℕ) : Fin n × Fin (dL Dw) →₀ ℕ :=
  Finsupp.mapDomain (fun p : LtN Dw n => (p.2.2, ltIdx Dw ⟨p.1, p.2.1⟩)) m
def mVal {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {n : ℕ}
    {S : Type} [CommRing S] (G : MvPowerSeries (Fin n × Fin (dL Dw)) S) (m : LtN Dw n →₀ ℕ) : S :=
  (m.prod fun _ e => (e.factorial : S)) * MvPowerSeries.coeff (colIdx m) G
def KillAddValColSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] (k n : ℕ)
    (G : MvPowerSeries (Fin n × Fin (dL Dw)) S) (β : Matrix (Fin (dL Dw)) (Fin (dL Dw)) S),
    PsiCoverSt H →
    (∀ i j, β i j ≠ 0 → ((ltIdx Dw).symm j).1 = ComplexEmbedding.conjugate ((ltIdx Dw).symm i).1) →
    ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n →
      ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) *
          mVal (Germ.FB.expS S (-((k : S)) • TB.quadCol (n := n) β) * G) m =
        ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * mVal G m
namespace KAV
open MvPowerSeries
end KAV
namespace KAV
open MvPowerSeries
end KAV
namespace KAV
open MvPowerSeries
end KAV
namespace KAV
open MvPowerSeries
theorem colEmb_inj {n d : ℕ} (b : Fin n) : Function.Injective (fun p : Fin 1 × Fin d => ((b, p.2) : Fin n × Fin d)) :=
  fun p q h => by
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (Subsingleton.elim _ _) h.2
def colPart {n d : ℕ} (b : Fin n) (M : Fin n × Fin d →₀ ℕ) : Fin 1 × Fin d →₀ ℕ :=
  Finsupp.comapDomain (fun p : Fin 1 × Fin d => ((b, p.2) : Fin n × Fin d)) M (colEmb_inj b).injOn
end KAV
def ProdColSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (S : Type) [CommRing S]
    (n : ℕ) (g : Fin n → MvPowerSeries (Fin 1 × Fin (dL Dw)) S) (m : LtN Dw n →₀ ℕ),
    mVal (∏ b, MvPowerSeries.rename (fun p : Fin 1 × Fin (dL Dw) => ((b, p.2) : Fin n × Fin (dL Dw))) (g b)) m =
      ∏ b, expVal (g b) (colOf m b)
end Formalism.MainNotions.ModuliIntegralCharts.H1


