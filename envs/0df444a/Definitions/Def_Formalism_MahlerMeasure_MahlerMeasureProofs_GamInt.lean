-- Prove2me | Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
-- name    : Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:25:20.27317+00:00
-- url     : https://prove2.me/theorems/93dcd803-df85-4877-a0e5-7e86ea883bdf
-- title:
--   Gam Int
-- statement:
--   Definitions and structural lemmas for Gam Int, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean

import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.GM.gammaIntegralityLemmas
open Finset Polynomial
variable {p : ℕ} [Fact p.Prime]
def IVP (p : ℕ) [Fact p.Prime] (D : ℕ) (g : ℕ → ℚ_[p]) : Prop :=
  (∃ P : Polynomial ℚ_[p], P.natDegree ≤ D ∧ ∀ m : ℕ, g m = P.eval (m : ℚ_[p])) ∧ ∀ m, ‖g m‖ ≤ 1
end Formalism.GM.gammaIntegralityLemmas
namespace Formalism.GM.gammaIntegralityLemmas
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
end Formalism.GM.gammaIntegralityLemmas
namespace Formalism.GM.gammaIntegralityLemmas
open MvPolynomial Finset
variable {p : ℕ} [hp : Fact p.Prime]
section fockS
variable {σ : Type} [Fintype σ] [DecidableEq σ]
noncomputable def wf (m : σ →₀ ℕ) : ℚ_[p] := ∏ x, ((m x).factorial : ℚ_[p])
end fockS
section tie
variable {σ : Type} [Fintype σ] [DecidableEq σ] {r : ℕ} (w e : Fin r → σ)
end tie
section dop
variable {σ : Type} [DecidableEq σ]
noncomputable def Dop (u v : σ) : Module.End ℚ_[p] (MvPolynomial σ ℚ_[p]) :=
  (pderiv u).toLinearMap ∘ₗ (pderiv v).toLinearMap
end dop
end Formalism.GM.gammaIntegralityLemmas
namespace Formalism.GM.gammaIntegralityLemmas
open MvPolynomial Finset
variable {p : ℕ} [hp : Fact p.Prime]
section dop2
variable {σ : Type} [DecidableEq σ]
end dop2
section FT
variable {σ : Type} [DecidableEq σ] {r : ℕ} (w e : Fin r → σ)
noncomputable def FT (T : Finset (Fin r)) : Module.End ℚ_[p] (MvPolynomial σ ℚ_[p]) :=
  ∑ c ∈ T, Dop (w c) (e c)
end FT
end Formalism.GM.gammaIntegralityLemmas
namespace Formalism.GM.gammaIntegralityLemmas
open MvPolynomial Finset
variable {p : ℕ} [hp : Fact p.Prime]
section good
variable {σ : Type} [DecidableEq σ] {M : Type} [AddCommMonoid M]
def AllMono (Q : M → (σ →₀ ℕ) → Prop) (d : M) (P : MvPolynomial σ ℚ_[p]) : Prop :=
  ∀ β ∈ P.support, Q d β
variable (Q : M → (σ →₀ ℕ) → Prop)
end good
section intP
variable {σ : Type} [DecidableEq σ]
def IsIntP (P : MvPolynomial σ ℚ_[p]) : Prop := ∀ β, ‖coeff β P‖ ≤ 1
theorem IsIntP.C {a : ℚ_[p]} (ha : ‖a‖ ≤ 1) : IsIntP (MvPolynomial.C a : MvPolynomial σ ℚ_[p]) := by
  intro β; rw [coeff_C]; split_ifs <;> simp [ha]
theorem IsIntP.X (u : σ) : IsIntP (X u : MvPolynomial σ ℚ_[p]) := by
  intro β; rw [coeff_X']; split_ifs <;> simp
end intP
end Formalism.GM.gammaIntegralityLemmas
namespace Formalism.GM.gammaIntegralityLemmas
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [hp : Fact p.Prime]
section frz
variable {N r : ℕ}
def δv (β : Fin (N + 1 + 1) × Fin r →₀ ℕ) : Fin (N + 1 + 1) → ℕ := fun i => ∑ c, β (i, c)
def GoodQ (ρ : Fin r) (D : Fin (N + 1 + 1) → ℕ) (β : Fin (N + 1 + 1) × Fin r →₀ ℕ) : Prop :=
  δv β = D ∧ β (Fin.castSucc (Fin.last N), ρ) ≤ β (Fin.last (N + 1), ρ)
def dv (i : Fin (N + 1)) : Fin (N + 1 + 1) → ℕ := Pi.single (Fin.castSucc i) 1 + Pi.single (Fin.last (N + 1)) 1
end frz
end Formalism.GM.gammaIntegralityLemmas
namespace Formalism.GM.gammaIntegralityLemmas
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [hp : Fact p.Prime]
section frz3
variable {N r : ℕ}
end frz3
end Formalism.GM.gammaIntegralityLemmas
namespace Formalism.GM.gammaIntegralityLemmas
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [hp : Fact p.Prime]
section alg
variable {σ : Type} [Fintype σ] [DecidableEq σ]
end alg
end Formalism.GM.gammaIntegralityLemmas
namespace Formalism.GM.gammaIntegralityLemmas
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [hp : Fact p.Prime]
section grp
variable {N r : ℕ}
end grp
end Formalism.GM.gammaIntegralityLemmas
namespace Formalism.GM.gammaIntegralityLemmas
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [hp : Fact p.Prime]
section term
variable {N r : ℕ}
abbrev xW (ρ : Fin r) : Fin (N + 1 + 1) × Fin r := (Fin.castSucc (Fin.last N), ρ)
abbrev yE (ρ : Fin r) : Fin (N + 1 + 1) × Fin r := (Fin.last (N + 1), ρ)
def eWY : Fin (N + 1 + 1) → ℕ := Pi.single (Fin.castSucc (Fin.last N)) 1 + Pi.single (Fin.last (N + 1)) 1
def kap (N r B : ℕ) : ℕ := 10 * (N + 3) * r ^ 2 * (B + 1)
noncomputable def termF (LL : Letters (N + 1)) (ρ : Fin r) (z j a a' : ℕ) (β γ : Fin (N + 1 + 1) × Fin r →₀ ℕ)
    (h h' : ℚ_[p]) (m : ℕ) : ℚ_[p] :=
  ((((LL.deg (Fin.last N) + (m + LL.total) + r + z - 1).choose (LL.deg (Fin.last N)) : ℕ) : ℚ_[p]) *
    (((-1 : ℚ_[p]) ^ j / (((j.factorial : ℚ_[p]) ^ 2) *
      (((LL.deg (Fin.last N) + (m + LL.total) + r + z - 1).choose j : ℕ) : ℚ_[p]))) *
    (((j.choose a : ℕ) : ℚ_[p]) * ((j.choose a' : ℕ) : ℚ_[p]) *
      Formalism.GM.M.fock p ((Dop (xW ρ) (yE ρ) ^ a) (X (yE ρ) ^ m * monomial β h))
        ((Dop (xW ρ) (yE ρ) ^ a') (X (yE ρ) ^ m * monomial γ h')))) /
    ((((m + LL.total - LL.total).factorial * LL.total.factorial : ℕ) : ℚ_[p]) * ∏ i, ((LL.deg i).factorial : ℚ_[p])))
end term
end Formalism.GM.gammaIntegralityLemmas
namespace Formalism.GM.gammaIntegralityLemmas
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [hp : Fact p.Prime]
section term2
variable {N r : ℕ}
end term2
end Formalism.GM.gammaIntegralityLemmas
namespace Formalism.GM.gammaIntegralityLemmas
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [hp : Fact p.Prime]
section term3
variable {N r : ℕ}
end term3
end Formalism.GM.gammaIntegralityLemmas
namespace Formalism.GM.gammaIntegralityLemmas
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [hp : Fact p.Prime]
section expand
variable {σ : Type} [Fintype σ] [DecidableEq σ] {r : ℕ} (w e : Fin r → σ) (ρ : Fin r)
end expand
end Formalism.GM.gammaIntegralityLemmas
namespace Formalism.GM.gammaIntegralityLemmas
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [hp : Fact p.Prime]
section final
variable {N r : ℕ}
abbrev wv : Fin r → Fin (N + 1 + 1) × Fin r := fun c => (Fin.castSucc (Fin.last N), c)
abbrev ev : Fin r → Fin (N + 1 + 1) × Fin r := fun c => (Fin.last (N + 1), c)
end final
end Formalism.GM.gammaIntegralityLemmas
namespace Formalism.GM.gammaIntegralityLemmas
open MvPolynomial Finset Formalism.GM.M
end Formalism.GM.gammaIntegralityLemmas
namespace Formalism.GM
end Formalism.GM


