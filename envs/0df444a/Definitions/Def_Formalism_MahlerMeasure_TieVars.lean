-- Prove2me | Definitions.Def_Formalism_MahlerMeasure_TieVars
-- name    : Formalism_MahlerMeasure_TieVars
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:11:48.102796+00:00
-- url     : https://prove2.me/theorems/085ec494-8534-4f37-9dce-224dcd2b9fac
-- title:
--   Tie Vars
-- statement:
--   Definitions and structural lemmas for Tie Vars, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/TieVars.lean

import Definitions.Def_Formalism_MahlerMeasure_GoodCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.GM.M
open MvPolynomial Finset
noncomputable def fockK {k σ : Type} [Field k] (F G : MvPolynomial σ k) : k :=
  ∑ m ∈ F.support, F.coeff m * G.coeff m * (m.prod fun _ j => (j.factorial : k))
noncomputable def tieEh {k σ : Type} [Field k] {r : ℕ} (w e : Fin r → σ) (zv sv : σ) :
    MvPolynomial σ k →ₗ[k] MvPolynomial σ k :=
  LinearMap.mulLeft k (X zv * X sv + ∑ c, X (w c) * X (e c))
noncomputable def tieFh {k σ : Type} [Field k] {r : ℕ} (w e : Fin r → σ) (zv sv : σ) :
    MvPolynomial σ k →ₗ[k] MvPolynomial σ k :=
  (pderiv zv).toLinearMap ∘ₗ (pderiv sv).toLinearMap + Formalism.GM.tieF w e
noncomputable def tieP {k σ : Type} [Field k] {r : ℕ} (w e : Fin r → σ) (zv sv : σ) (o n z : ℕ)
    (y : MvPolynomial σ k) : MvPolynomial σ k :=
  ∑ l ∈ range (o + 1),
    (((-1 : k) ^ l) / (((l.factorial : k) ^ 2) * ((o + n + r + z - 1).choose l : k))) •
      ((tieEh w e zv sv) ^ l) (((Formalism.GM.tieF w e) ^ l) (X zv ^ z * y))
def TieVars {σ : Type} {r : ℕ} (w e : Fin r → σ) (zv sv : σ) : Prop :=
  Function.Injective w ∧ Function.Injective e ∧ (∀ c d, w c ≠ e d) ∧ (∀ c, w c ≠ zv ∧ w c ≠ sv ∧ e c ≠ zv ∧
    e c ≠ sv) ∧ zv ≠ sv
def ZSFree {k σ : Type} [Field k] (zv sv : σ) (y : MvPolynomial σ k) : Prop :=
  ∀ m ∈ y.support, m zv = 0 ∧ m sv = 0
def RemoveS : Prop :=
  ∀ (k σ : Type) [Field k] [CharZero k] (r : ℕ) (w e : Fin r → σ) (zv sv : σ), TieVars w e zv sv → 1 ≤ r →
    ∀ (o n z : ℕ) (y y' : MvPolynomial σ k),
      Formalism.GM.BiHom w e o n y → Formalism.GM.BiHom w e o n y' → ZSFree zv sv y → ZSFree zv sv y' →
      tieFh w e zv sv (tieP w e zv sv o n z y) = 0 ∧
      fockK (tieP w e zv sv o n z y) (tieP w e zv sv o n z y') =
        (z.factorial : k) * fockK y (Formalism.GM.tiePhi w e o n z y') ∧
      ∀ j j' : ℕ,
        fockK ((((j.factorial : k))⁻¹) • ((tieEh w e zv sv) ^ j) (tieP w e zv sv o n z y))
              ((((j'.factorial : k))⁻¹) • ((tieEh w e zv sv) ^ j') (tieP w e zv sv o n z y')) =
          if j = j' then (((o + n + r + z + 1 + j - 1).choose j : ℕ) : k) * (z.factorial : k) *
            fockK y (Formalism.GM.tiePhi w e o n z y') else 0
end Formalism.GM.M


