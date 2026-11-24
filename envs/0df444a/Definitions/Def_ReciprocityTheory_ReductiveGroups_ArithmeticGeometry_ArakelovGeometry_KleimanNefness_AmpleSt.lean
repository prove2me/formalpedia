-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_AmpleSt
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_AmpleSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:24:22.977296+00:00
-- url     : https://prove2.me/theorems/f9885d87-eb8f-417f-a666-6490bf4dcdfc
-- title:
--   Ample St
-- statement:
--   Definitions and structural lemmas for Ample St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/KleimanNefness/AmpleSt.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_AlgDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_KleimanSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
def quotPart (S : Type*) [CommRing S] {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    (V : Ideal (MRingOver S ι)) (c : K → ℤ) : Submodule S (MRingOver S ι ⧸ V) :=
  Submodule.span S ((Ideal.Quotient.mk V) ''
    {p | (∀ k, 0 ≤ c k) ∧ IsMultiHomog p (fun k => (c k).toNat)})
def GeneratedV (S : Type*) [CommRing S] {K : Type*} [Fintype K] [LinearOrder K] {ι : K → Type*}
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] (V : Ideal (MRingOver S ι)) (n : K → ℤ) : Prop :=
  ∀ I : Cell K ι 0, ∃ (r : ℕ) (z : Fin r → CechC S ι (MRingOver S ι ⧸ V) 0)
    (u : Fin r → LocalizedModule (cellMon S I.1) (MRingOver S ι ⧸ V)),
    (∀ j, z j ∈ cechZc ι (quotPart S V) n 0) ∧
    (∀ j, u j ∈ locPart ι (quotPart S V) (cellMon S I.1) (-n)) ∧
    ∑ j, u j * z j I = 1
def AmpleV (S : Type*) [CommRing S] {K : Type*} [Fintype K] [LinearOrder K] {ι : K → Type*}
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] (V : Ideal (MRingOver S ι)) (N : K → ℤ) : Prop :=
  ∃ q : ℕ, 1 ≤ q ∧ GeneratedV S V (q • N) ∧
    ∀ e : K → ℤ, ∃ c₁ : ℕ, ∀ c : ℕ, c₁ ≤ c → Subsingleton (cechHc ι (quotPart S V) (e + (c * q) • N) 1)
def SerreGenStatement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] (V : Ideal (MRingOver S ι)) (e : K → ℤ),
    IsNoetherianRing S → IsMultiHomogIdeal V →
    ∃ c₀ : ℕ, ∀ c : ℕ, c₀ ≤ c → GeneratedV S V (e + fun _ => (c : ℤ))
def KAmpStatement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] (I : IFamily F ι) (V : Ideal (MRingOver F ι)) (d : ℕ)
    (α : K → ℤ) (b a : ℕ),
    IsFieldIntersection I → IsProjVarF V d → NefOnF I V α → 1 ≤ b → 1 ≤ a →
    AmpleV F V (b • α + fun _ => (a : ℤ))
def SiuStatement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] (I : IFamily F ι) (V : Ideal (MRingOver F ι)) (D : ℕ)
    (α β : K → ℤ) (q : ℕ),
    IsFieldIntersection I → IsProjVarF V (D + 1) → 1 ≤ q → GeneratedV F V (q • α) → GeneratedV F V (q • β) →
    ((D + 1 : ℕ) : ℤ) * I V (D + 1) (Fin.snoc (α := fun _ => K → ℤ) (fun _ : Fin D => α) β) <
      I V (D + 1) (fun _ => α) →
    ∃ k : ℕ, 1 ≤ k ∧ ∃ z ∈ cechZc ι (quotPart F V) (k • (α - β)) 0, z ≠ 0
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH


