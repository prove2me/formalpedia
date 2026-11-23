-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularOrthogonal_MatOrthoLocal
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularOrthogonal_MatOrthoLocal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:52:38.186125+00:00
-- url     : https://prove2.me/theorems/9696cd9b-5378-41cb-8e48-0eda590d369a
-- title:
--   Mat Ortho Local
-- statement:
--   Definitions and structural lemmas for Mat Ortho Local, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularOrthogonal/MatOrthoLocal.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnimodularOrthogonalQ2
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.UnimodularOrthogonalQuadratic
open NumberField PI.UnimodularOrthogonalQ2
def FHyp (K : Type) [Field K] [NumberField K] (c : K →+* K) (p : ℕ) [Fact p.Prime] (τ : K →+* ℂ_[p]) (d : ℕ)
    (b0 : K) : Prop :=
  Module.finrank ℚ K = 2 ∧ (∃ x, c x ≠ x) ∧ d.Prime ∧ b0 ^ 2 = -(d : K) ∧ p ≠ d ∧ (p = 2 → d % 8 = 7)
def zc {p : ℕ} [Fact p.Prime] (a : ℤ_[p]) : ℂ_[p] := algebraMap ℚ_[p] ℂ_[p] (a : ℚ_[p])
def RingSwap {p : ℕ} [Fact p.Prime] (O : Set (ℂ_[p] × ℂ_[p])) : Prop :=
  (0 : ℂ_[p] × ℂ_[p]) ∈ O ∧ (1 : ℂ_[p] × ℂ_[p]) ∈ O ∧ (∀ x ∈ O, ∀ y ∈ O, x + y ∈ O) ∧ (∀ x ∈ O, -x ∈ O) ∧
    (∀ x ∈ O, ∀ y ∈ O, x * y ∈ O) ∧ ∀ x ∈ O, x.swap ∈ O
def MatOrthoFor {p : ℕ} [Fact p.Prime] (O : Set (ℂ_[p] × ℂ_[p])) : Prop :=
  ∀ (r : ℕ) (H : Matrix (Fin r) (Fin r) (ℂ_[p] × ℂ_[p])), (∀ i j, H i j ∈ O) → (∀ i j, H j i = (H i j).swap) →
    (∃ G : Matrix (Fin r) (Fin r) (ℂ_[p] × ℂ_[p]), (∀ i j, G i j ∈ O) ∧ H * G = 1) →
    ∃ P Q : Matrix (Fin r) (Fin r) (ℂ_[p] × ℂ_[p]), (∀ i j, P i j ∈ O) ∧ (∀ i j, Q i j ∈ O) ∧ Q * P = 1 ∧
      P * H * (P.map Prod.swap).transpose = 1
def Reduce : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (O : Set (ℂ_[p] × ℂ_[p])), RingSwap O → MatOrthoFor O →
    ∀ (κ : Type) [Fintype κ] (r : ℕ) (Y : Set (κ → ℂ_[p] × ℂ_[p])) (b : Fin r → κ → ℂ_[p] × ℂ_[p]),
      IsBasisOver O Y b →
      (∀ a : Fin r → ℂ_[p] × ℂ_[p], (∀ e, a e ∈ O) → (fun k => ∑ e, a e * b e k) ∈ Y) →
      (∀ i j, hP (b i) (b j) ∈ O) →
      (∃ G : Fin r → Fin r → ℂ_[p] × ℂ_[p], (∀ i j, G i j ∈ O) ∧
        ∀ i k, ∑ j, hP (b i) (b j) * G j k = if i = k then 1 else 0) →
      ∃ b' : Fin r → κ → ℂ_[p] × ℂ_[p], IsBasisOver O Y b' ∧ ∀ i j, hP (b' i) (b' j) = if i = j then 1 else 0
def OkGood : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (c : K →+* K) (p : ℕ) [Fact p.Prime] (τ : K →+* ℂ_[p]) (d : ℕ) (b0 : K),
    FHyp K c p τ d b0 → RingSwap (OKpair K c p τ) ∧ MatOrthoFor (OKpair K c p τ)
def OrthoOver (S : Type) [CommRing S] (σ : S →+* S) : Prop :=
  ∀ (r : ℕ) (H : Matrix (Fin r) (Fin r) S), (∀ i j, H j i = σ (H i j)) → (∃ G, H * G = 1) →
    ∃ P Q : Matrix (Fin r) (Fin r) S, Q * P = 1 ∧ P * H * (P.map σ).transpose = 1
def MatOrthoLocal : Prop :=
  ∀ (S : Type) [CommRing S] (σ : S →+* S), (∀ x, σ (σ x) = x) → IsUnit (2 : S) →
    (∀ x y : S, σ x = x → σ y = y → ¬IsUnit x → ¬IsUnit y → ¬IsUnit (x + y)) →
    (∀ x : S, σ x = x → IsUnit x → ∃ u, u * σ u = x) → OrthoOver S σ
def MatOrthoSplit : Prop :=
  ∀ (S : Type) [CommRing S] (σ : S →+* S), (∀ x, σ (σ x) = x) → (∃ e : S, e * e = e ∧ σ e = 1 - e) →
    OrthoOver S σ
def sw {p : ℕ} [Fact p.Prime] (S : Subring (ℂ_[p] × ℂ_[p])) (h : ∀ x ∈ S, x.swap ∈ S) : S →+* S :=
  (RingEquiv.prodComm : ℂ_[p] × ℂ_[p] ≃+* ℂ_[p] × ℂ_[p]).toRingHom.restrict S S h
def Transfer : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (S : Subring (ℂ_[p] × ℂ_[p])) (h : ∀ x ∈ S, x.swap ∈ S),
    OrthoOver S (sw S h) → MatOrthoFor (S : Set (ℂ_[p] × ℂ_[p]))
def F0 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (c : K →+* K) (p : ℕ) [Fact p.Prime] (τ : K →+* ℂ_[p]) (d : ℕ) (b0 : K),
    FHyp K c p τ d b0 → ∃ S : Subring (ℂ_[p] × ℂ_[p]), (S : Set _) = OKpair K c p τ ∧ ∀ x ∈ S, x.swap ∈ S
def F1 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (c : K →+* K) (p : ℕ) [Fact p.Prime] (τ : K →+* ℂ_[p]) (d : ℕ) (b0 : K),
    FHyp K c p τ d b0 → ∀ z : ℤ_[p], (zc z, zc z) ∈ OKpair K c p τ
def F2 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (c : K →+* K) (p : ℕ) [Fact p.Prime] (τ : K →+* ℂ_[p]) (d : ℕ) (b0 : K),
    FHyp K c p τ d b0 → ∀ x ∈ OKpair K c p τ, ‖x.1‖ ≤ 1 ∧ ‖x.2‖ ≤ 1
def F3 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (c : K →+* K) (p : ℕ) [Fact p.Prime] (τ : K →+* ℂ_[p]) (d : ℕ) (b0 : K),
    FHyp K c p τ d b0 → p ≠ 2 → ∀ x ∈ OKpair K c p τ, x.swap = x → ∃ z : ℤ_[p], x = (zc z, zc z)
def F4 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (c : K →+* K) (p : ℕ) [Fact p.Prime] (τ : K →+* ℂ_[p]) (d : ℕ) (b0 : K),
    FHyp K c p τ d b0 → p ≠ 2 → ∀ z : ℤ_[p], IsUnit z → ∃ u ∈ OKpair K c p τ, u * u.swap = (zc z, zc z)
def F5 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (c : K →+* K) (p : ℕ) [Fact p.Prime] (τ : K →+* ℂ_[p]) (d : ℕ) (b0 : K),
    FHyp K c p τ d b0 → p = 2 → ∃ α ∈ OKpair K c p τ, ∃ x y : ℤ_[p], α = (zc x, zc y) ∧ IsUnit (x - y)
def Glue : Prop := F0 → F1 → F2 → F3 → F4 → F5 → MatOrthoLocal → MatOrthoSplit → Transfer → OkGood
end PI.UnimodularOrthogonalQuadratic


