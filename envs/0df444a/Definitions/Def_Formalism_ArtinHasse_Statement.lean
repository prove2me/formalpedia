-- Prove2me | Definitions.Def_Formalism_ArtinHasse_Statement
-- name    : Formalism_ArtinHasse_Statement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:39:20.050107+00:00
-- url     : https://prove2.me/theorems/853d9d4b-58fc-4312-87c3-69ee1d7df1e0
-- title:
--   Statement
-- statement:
--   Definitions and structural lemmas for Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ArtinHasse/Statement.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
namespace Formalism.FT
def tSeries : PowerSeries (MvPolynomial ℕ ℚ) :=
  PowerSeries.mk fun m => if m = 0 then 0 else MvPolynomial.X m
def Hpoly (k : ℕ) : MvPolynomial ℕ ℚ :=
  coeff k ((PowerSeries.exp (MvPolynomial ℕ ℚ)).subst tSeries)
def HDeriv : Prop :=
  ∀ r k : ℕ, 1 ≤ r →
    MvPolynomial.pderiv r (Hpoly k) = if r ≤ k then Hpoly (k - r) else 0
def HAtPsum : Prop :=
  ∀ (n k : ℕ),
    MvPolynomial.aeval (fun m : ℕ => (m : ℚ)⁻¹ • MvPolynomial.psum (Fin n) ℚ m) (Hpoly k) =
      MvPolynomial.hsymm (Fin n) ℚ k
abbrev hPS (R : Type*) [CommRing R] (n k : ℕ) : MvPowerSeries (Fin n) R :=
  ((MvPolynomial.hsymm (Fin n) R k : MvPolynomial (Fin n) R) : MvPowerSeries (Fin n) R)
def SymmSeriesHsymm : Prop :=
  ∀ (R : Type) [CommRing R] (n : ℕ) (F : MvPowerSeries (Fin n) R),
    (∀ π : Equiv.Perm (Fin n),
      F.subst (fun i => (MvPowerSeries.X (π i) : MvPowerSeries (Fin n) R)) = F) →
    ∃! G : MvPowerSeries (Fin n) R, G.subst (fun j : Fin n => hPS R n (j.val + 1)) = F
def HsymmStable : Prop :=
  ∀ (R : Type) [CommRing R] (n k : ℕ),
    MvPolynomial.aeval
        (fun i : Fin (n + 1) => if h : i.val < n then (MvPolynomial.X ⟨i.val, h⟩ : MvPolynomial (Fin n) R) else 0)
        (MvPolynomial.hsymm (Fin (n + 1)) R k) =
      MvPolynomial.hsymm (Fin n) R k
def ltLogQ (p : ℕ) : PowerSeries ℚ :=
  PowerSeries.mk fun n => by
    classical exact if ∃ j : ℕ, p ^ j = n then ((n : ℚ))⁻¹ else 0
def artinHasse (p : ℕ) : PowerSeries ℚ := (PowerSeries.exp ℚ).subst (ltLogQ p)
def DworkLemma : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (f : PowerSeries ℚ_[p]), constantCoeff f = 1 →
    ((∀ n, ‖coeff n f‖ ≤ 1) ↔
      ∃ g : PowerSeries ℚ_[p], (∀ n, ‖coeff n g‖ ≤ 1) ∧
        f.subst ((PowerSeries.X : PowerSeries ℚ_[p]) ^ p) =
          f ^ p * (1 + (p : ℚ_[p]) • (PowerSeries.X * g)))
def ArtinHasseIntegral : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n : ℕ), ¬ p ∣ (coeff n (artinHasse p)).den
def carries (p : ℕ) [Fact p.Prime] (y : ℤ_[p]) (i : ℕ) : Set ℕ :=
  {e : ℕ | 1 ≤ e ∧ p ^ e ≤ i % p ^ e + y.appr e}
def KummerZp : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (y : ℤ_[p]) (i : ℕ), Ring.choose (y + i) i ≠ 0 →
    (carries p y i).Finite ∧
      ‖Ring.choose (y + i) i‖ = (p : ℝ) ^ (-((carries p y i).ncard : ℤ))
end Formalism.FT


