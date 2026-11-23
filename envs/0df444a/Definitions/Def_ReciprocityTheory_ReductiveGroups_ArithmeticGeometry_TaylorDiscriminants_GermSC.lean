-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_GermSC
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_GermSC
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:41:52.062939+00:00
-- url     : https://prove2.me/theorems/f9260164-4a2f-4981-a714-bc07c320fec3
-- title:
--   Germ SC
-- statement:
--   Definitions and structural lemmas for Germ SC, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/GermSC.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
namespace ReciprocityTheory.ChartRestriction.G.TB
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k]
def ordNabla (B : FB R d O) (h : PS k 2 d) (m : ℕ) {ι : Type} [Fintype ι] (s : ι → Bool)
    (ξ : ι → (Fin d → k) × (Fin d → k)) (P : MvPolynomial ι k) (G : AA k d) : AA k d :=
  ∑ n ∈ P.support, C (P.coeff n) *
    ((Finset.univ : Finset ι).toList.filter (fun l => s l)).foldr
      (fun l g => (nabla k B h m (ξ l).1 (ξ l).2)^[n l] g)
      (((Finset.univ : Finset ι).toList.filter (fun l => !s l)).foldr
        (fun l g => (nabla k B h m (ξ l).1 (ξ l).2)^[n l] g) G)
def pairMin {ι π : Type} [Fintype ι] [Fintype π] [DecidableEq π] (c : ι → π) (s : ι → Bool) (n : ι →₀ ℕ) : ℕ :=
  ∑ q : π, min (∑ l ∈ Finset.univ.filter (fun l => c l = q ∧ s l = true), n l)
    (∑ l ∈ Finset.univ.filter (fun l => c l = q ∧ s l = false), n l)
def OppositePairVanishing {ι π : Type} (c : ι → π) (s : ι → Bool) (A A' : ι → (Fin d → k) × (Fin d → k)) : Prop :=
  ∀ l l', ¬ (c l = c l' ∧ s l ≠ s l') → betaH k (A l) (A' l') = 0
def SCSt : Prop :=
  ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k]
    [Algebra R k], IsRQ (R := R) k → ∀ (J : Submodule R k), (1 : k) ∈ J →
    ∀ (B : FB R d O) (h : PS k 2 d), B.IsCanonGauge k h → ∀ (w0 : O), w0 + star w0 = 1 → ∀ (m : ℕ)
    (ι π : Type) [Fintype ι] [Fintype π] [DecidableEq π] (c : ι → π) (s : ι → Bool)
    (ξh : ι → (Fin d → k) × (Fin d → k)) (ψ : ι → Fin d → k),
    (∀ l, ξh l ∈ Hset (R := R) k h) → (∀ l i, ψ l i ∈ J) →
    OppositePairVanishing k c s ξh ξh → OppositePairVanishing k c s (fun l => (0, ψ l)) ξh → OppositePairVanishing k c s ξh (fun l => (0, ψ l)) →
    ∀ (P : MvPolynomial ι k), (∀ n, P.coeff n ∈ (algebraMap R k).range) →
    ∀ (e : ℕ), (∀ n ∈ P.support, pairMin c s n ≤ e) →
    ∀ f : PS k 1 d, IntAA (R := R) k f →
      constantCoeff (ordNabla k B h m s (fun l => ξh l + (0, ψ l)) P
        (liftX k (FB.expS k ((m : k) • B.hL k h w0) * f))) ∈ J ^ e
def LemmaHSt : Prop :=
  ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k]
    [Algebra R k] (B : FB R d O) (h : PS k 2 d), ev (n := 1) ![0, pt k d 0] h = 0 → ∀ (m : ℕ)
    (ι π : Type) [Fintype ι] [DecidableEq π] (c : ι → π) (s : ι → Bool) (u φ : ι → Fin d → k),
    OppositePairVanishing k c s (fun l => (u l, 0)) (fun l => (u l, 0)) → OppositePairVanishing k c s (fun l => (u l, 0)) (fun l => (0, φ l)) →
    OppositePairVanishing k c s (fun l => (0, φ l)) (fun l => (u l, 0)) →
    ∀ P : MvPolynomial ι k,
      secondOrder k (fun l l' => if c l = c l' ∧ s l = true ∧ s l' = false then
        (m : k) * betaH k (0, φ l) (u l', 0) else 0) P = 0 →
    ∀ g : PS k 1 d, constantCoeff (ordNabla k B h m s (fun l => (u l, φ l)) P (liftX k g)) =
      constantCoeff (DpolyOf (B.FK k) u P g)
end ReciprocityTheory.ChartRestriction.G.TB


