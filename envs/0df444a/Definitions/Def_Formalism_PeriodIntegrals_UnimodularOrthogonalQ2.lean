-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnimodularOrthogonalQ2
-- name    : Formalism_PeriodIntegrals_UnimodularOrthogonalQ2
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:50:49.08684+00:00
-- url     : https://prove2.me/theorems/5f63cf95-18c0-4a34-bc0a-41ea74a92d31
-- title:
--   Unimodular Orthogonal Q2
-- statement:
--   Definitions and structural lemmas for Unimodular Orthogonal Q2, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnimodularOrthogonalQ2.lean

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
namespace PI.UnimodularOrthogonalQ2
open NumberField
def OKpair (K : Type) [Field K] [NumberField K] (c : K →+* K) (p : ℕ) [Fact p.Prime] (τ : K →+* ℂ_[p]) :
    Set (ℂ_[p] × ℂ_[p]) :=
  closure (Set.range fun a : 𝓞 K => (τ (a : K), τ (c (a : K))))
def hP {p : ℕ} [Fact p.Prime] {κ : Type} [Fintype κ] (x y : κ → ℂ_[p] × ℂ_[p]) : ℂ_[p] × ℂ_[p] :=
  ∑ k, x k * (y k).swap
def IsBasisOver {p : ℕ} [Fact p.Prime] (O : Set (ℂ_[p] × ℂ_[p])) {κ ι : Type} [Fintype ι]
    (Y : Set (κ → ℂ_[p] × ℂ_[p])) (b : ι → κ → ℂ_[p] × ℂ_[p]) : Prop :=
  (∀ e, b e ∈ Y) ∧ ∀ y ∈ Y, ∃! a : ι → ℂ_[p] × ℂ_[p], (∀ e, a e ∈ O) ∧ y = fun k => ∑ e, a e * b e k
def Stmt : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (c : K →+* K) (p : ℕ) [Fact p.Prime] (τ : K →+* ℂ_[p]) (d : ℕ) (b0 : K),
    Module.finrank ℚ K = 2 → (∃ x, c x ≠ x) → d.Prime → b0 ^ 2 = -(d : K) → p ≠ d → (p = 2 → d % 8 = 7) →
    ∀ (κ : Type) [Fintype κ] (r : ℕ) (Y : Set (κ → ℂ_[p] × ℂ_[p])) (b : Fin r → κ → ℂ_[p] × ℂ_[p]),
      IsBasisOver (OKpair K c p τ) Y b →
      (∀ a : Fin r → ℂ_[p] × ℂ_[p], (∀ e, a e ∈ OKpair K c p τ) → (fun k => ∑ e, a e * b e k) ∈ Y) →
      (∀ i j, hP (b i) (b j) ∈ OKpair K c p τ) →
      (∃ G : Fin r → Fin r → ℂ_[p] × ℂ_[p], (∀ i j, G i j ∈ OKpair K c p τ) ∧
        ∀ i k, ∑ j, hP (b i) (b j) * G j k = if i = k then 1 else 0) →
      ∃ b' : Fin r → κ → ℂ_[p] × ℂ_[p], IsBasisOver (OKpair K c p τ) Y b' ∧
        ∀ i j, hP (b' i) (b' j) = if i = j then 1 else 0
end PI.UnimodularOrthogonalQ2


