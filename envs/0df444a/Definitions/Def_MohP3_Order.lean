-- Prove2me | Definitions.Def_MohP3_Order
-- name    : MohP3_Order
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T21:49:15.239801+00:00
-- url     : https://prove2.me/theorems/4632ff94-3572-5b94-94d6-184098235707
-- title:
--   Order
-- statement:
--   Definitions and structural lemmas for Order, from GrgAakash (GrgAakash/moh-p3-set-theoretic-complete-intersection; see pinned Apache-2.0 LICENSE and README.md)'s pinned Moh P3 curve is a global and formal-local set-theoretic complete intersection development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Order.lean

module
public import Mathlib
set_option autoImplicit true
@[expose] public section
@[expose] public section
noncomputable section
open MvPowerSeries
namespace MohP3.Wt
variable {k : Type*} [CommRing k]
def wt (d : Fin 3 →₀ ℕ) : ℕ := 6 * d 0 + 8 * d 1 + 10 * d 2
def WOrd (F : MvPowerSeries (Fin 3) k) (n : ℕ) : Prop :=
  ∀ d, wt d < n → coeff d F = 0
def YOrd (p : PowerSeries k) (n : ℕ) : Prop :=
  ∀ m, 8 * m < n → PowerSeries.coeff m p = 0
def dd (a b c : ℕ) : Fin 3 →₀ ℕ :=
  Finsupp.single 0 a + Finsupp.single 1 b + Finsupp.single 2 c
def En (n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.range (n + 1)) ×ˢ (Finset.range (n + 1)) ×ˢ (Finset.range (n + 1))).filter
    (fun p => 6 * p.1 + 8 * p.2.1 + 10 * p.2.2 = n)
end MohP3.Wt


