-- Prove2me | Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
-- name    : Formalism_PolynomialDimension_MultinomialDepth_PartnerM
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:21:00.77904+00:00
-- url     : https://prove2.me/theorems/a179bec2-a841-457e-95e1-9f692f530e5e
-- title:
--   Partner M
-- statement:
--   Definitions and structural lemmas for Partner M, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.CountingSumsFrames
open Formalism.GM Formalism.GM.TM
open M MvPolynomial Finset
def TieOps : Prop :=
  ∃ C₂ : ℝ, 0 ≤ C₂ ∧ ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero N] [NeZero r]
    (LL : Letters N) (T : TieData) (a : ℕ) (E κ : ℝ) (n : Fin T.t → ℕ) (ρ : Fin r),
    p ≠ 2 → 2 ≤ r → (ρ : ℕ) = r - 1 → T.Admissible LL → 1 ≤ E →
    (∀ i, T.S (LL.setTies T n) i ≤ n i) → (∀ x, (LL.setTies T n).deg x ≤ 2 * a) → (∀ i, T.z i ≤ 2 * a) →
    ((N + 2) * r ^ 2 : ℝ) * lgV2 p a r ≤ κ →
    HypP p (LL.setTies T n) ρ ⌈κ / (N + 2)⌉₊ → HypW p (r := r) (LL.setTies T n) ⌈κ / (N + 2)⌉₊ →
    (∀ i, GramDeterminantGradedHypothesis p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ κ) →
    ∀ (nb : Fin T.t → (Fin r → ℤ) → ℕ)
      (f : ∀ i w, Fin (nb i w) → MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p])
      (U V : ∀ i w, Matrix (Fin (nb i w)) (Fin (nb i w)) ℚ_[p]) (dg : ∀ i w, Fin (nb i w) → ℚ_[p])
      (fw : ∀ i : Fin T.t, (Fin r → ℤ) → MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p]),
      (∀ i w, LinearIndependent ℤ_[p] (f i w) ∧
        Submodule.span ℤ_[p] (Set.range (f i w)) =
          MMwZ p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w) →
      (∀ i w, (∀ x y, ‖U i w x y‖ ≤ 1) ∧ (∀ x y, ‖V i w x y‖ ≤ 1) ∧ ‖(U i w).det‖ = 1 ∧ ‖(V i w).det‖ = 1 ∧
        (Matrix.of fun x y => (p : ℚ_[p]) ^ (⌈κ⌉₊) *
          tieGam p ((LL.setTies T n).takeD (T.pos i + 1)) ρ (T.z i) (n i) (f i w x) (f i w y)) =
          U i w * Matrix.diagonal (dg i w) * V i w) →
      (∀ i w, fw i w ∈ MMw p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w ∧
        (MMw p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w ≠ ⊥ → fw i w ≠ 0)) →
      ∀ i : Fin T.t, ∃ (Tm πm : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
        (K : ℕ), (K : ℝ) ≤ C₂ * κ ∧
        (∀ y ∈ Y p (r := r) (LL.setTies T n) T.J T.thr, Tm y ∈ Y p (r := r) (LL.setTies T n) T.J T.thr) ∧
        (∀ y ∈ YZ p (r := r) (LL.setTies T n) T.J T.thr,
          ((p : ℚ_[p]) ^ K) • Tm y ∈ IntPol p (Fin N × Fin r)) ∧
        (∀ u ∈ Y p (r := r) (LL.setTies T n) T.J (T.thrUpTo i), ∀ u' ∈ Y p (r := r) (LL.setTies T n) T.J T.thr,
          fockN p (LL.setTies T n) (T.phi p (LL.setTies T n) i u) (Tm u') =
            (p : ℚ_[p]) ^ ⌊E⌋₊ * fockN p (LL.setTies T n) (πm u) u') ∧
        (∀ j : Fin T.t, i < j → ∀ u ∈ Y p (r := r) (LL.setTies T n) T.J (T.thrUpTo i),
          πm (T.phi p (LL.setTies T n) j u) = T.phi p (LL.setTies T n) j (πm u)) ∧
        ((Module.finrank ℚ_[p] (Y p (r := r) (LL.setTies T n) T.J T.thr) -
            Module.finrank ℚ_[p] ((Y p (r := r) (LL.setTies T n) T.J T.thr ⊓
              LinearMap.ker (πm - LinearMap.id) : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]))) : ℕ) : ℝ) ≤
          ∑ᶠ w, ((univ.filter (fun b => ‖dg i w b‖ < (p : ℝ) ^ (-E))).card : ℝ) *
            (Module.finrank ℚ_[p] (T.YYsp p LL i ρ n (fw i w)) : ℝ)
def YPartner : Prop :=
  ∃ C₃ : ℝ, 0 ≤ C₃ ∧ ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero N] [NeZero r] (LL : Letters N) {q : ℕ}
    (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (ρ : Fin r) (a : ℕ) (κ : ℝ),
    2 ≤ r → ((N + 2) * r ^ 2 : ℝ) * lgV2 p a r ≤ κ → HypP p LL ρ ⌈κ / (N + 2)⌉₊ →
    ∀ z ∈ YZ p (r := r) LL J M,
      (∀ (c : ℤ_[p]) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]), x ∈ YZ p (r := r) LL J M → z = c • x → IsUnit c) →
      ∃ z'' ∈ YZ p (r := r) LL J M, ∃ K₀ : ℕ, (K₀ : ℝ) ≤ C₃ * κ ∧
        (p : ℝ) ^ (-(K₀ : ℤ)) ≤ ‖fockN p LL z z''‖
section Peel
variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [LinearOrder ι]
def lcomp (φ : ι → V →ₗ[K] V) (l : List ι) : V →ₗ[K] V :=
  l.foldr (fun i acc => φ i ∘ₗ acc) LinearMap.id
end Peel
section Lat
variable {p : ℕ} [Fact p.Prime]
end Lat
section Codim
variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
end Codim
end Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
open Formalism.GM Formalism.GM.TM M MvPolynomial Finset
section Stab
variable {k σ : Type} [Field k]
def stabAlg (W : Submodule k (MvPolynomial σ k)) : Subalgebra k (Module.End k (MvPolynomial σ k)) where
  carrier := {T | ∀ x ∈ W, T x ∈ W}
  mul_mem' := by intro a b ha hb x hx; exact ha _ (hb x hx)
  add_mem' := by intro a b ha hb x hx; exact W.add_mem (ha x hx) (hb x hx)
  algebraMap_mem' := by intro c x hx; rw [Module.algebraMap_end_apply]; exact W.smul_mem c hx
end Stab
section Keep
variable {p : ℕ} [Fact p.Prime]
end Keep
section Keep2
variable {p : ℕ} [Fact p.Prime]
end Keep2
end Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
open Formalism.GM Formalism.GM.TM M MvPolynomial Finset
end Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
open Formalism.GM Formalism.GM.TM M MvPolynomial Finset
section XD
variable {k σ : Type} [Field k]
end XD
section Gl
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
end Gl
end Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
open Formalism.GM Formalism.GM.TM M MvPolynomial Finset
section Wt
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
def shiftW {r : ℕ} (μ : Fin r → ℤ) (c d : Fin r) : Fin r → ℤ :=
  fun c' => μ c' + (if c = c' then 1 else 0) - (if d = c' then 1 else 0)
end Wt
end Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
open Formalism.GM Formalism.GM.TM M MvPolynomial Finset
section Comm
variable {k σ : Type} [Field k]
end Comm
section Terms
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
noncomputable def tm (LL : Letters N) (j : ℕ) (i : Fin N) (c d : Fin r) :
    Module.End ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) :=
  if (i : ℕ) < j then
    (if LL.vec i then (LinearMap.mulLeft ℚ_[p] (X (i, c))) ∘ₗ (pderiv (i, d)).toLinearMap
     else -((LinearMap.mulLeft ℚ_[p] (X (i, d))) ∘ₗ (pderiv (i, c)).toLinearMap))
  else 0
end Terms
end Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
open Formalism.GM Formalism.GM.TM M MvPolynomial Finset
section Gen
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
end Gen
section Rep
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
end Rep
end Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
open Formalism.GM Formalism.GM.TM M MvPolynomial Finset
section Proj
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
end Proj
end Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
open Formalism.GM Formalism.GM.TM M MvPolynomial Finset
section Comp
variable {K σ : Type} [Field K]
open Classical in

noncomputable def compP (Pr : (σ →₀ ℕ) → Prop) (x : MvPolynomial σ K) : MvPolynomial σ K :=
  ∑ m ∈ x.support, if Pr m then monomial m (coeff m x) else 0
end Comp
end Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
open Formalism.GM Formalism.GM.TM M MvPolynomial Finset
section HW
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
end HW
end Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
open Formalism.GM Formalism.GM.TM M MvPolynomial Finset
section E1
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
end E1
end Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
open Formalism.GM Formalism.GM.TM M MvPolynomial Finset
section E2
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
end E2
end Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
open Formalism.GM Formalism.GM.TM M MvPolynomial Finset
section E3
end E3
end Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
open Formalism.GM Formalism.GM.TM
end Formalism.CountingSumsFrames


