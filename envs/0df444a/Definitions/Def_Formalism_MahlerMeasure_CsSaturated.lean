-- Prove2me | Definitions.Def_Formalism_MahlerMeasure_CsSaturated
-- name    : Formalism_MahlerMeasure_CsSaturated
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:06:42.543038+00:00
-- url     : https://prove2.me/theorems/c09ed98c-9875-4e09-bcf1-a3b12c824b39
-- title:
--   Cs Saturated
-- statement:
--   Definitions and structural lemmas for Cs Saturated, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/CsSaturated.lean

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_QuotientUpperBoundsOfPowerBounds
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
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
noncomputable def WtSpC (p : ℕ) [Fact p.Prime] (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (la : Fin r → ℤ) :
    Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) :=
  MvPolynomial.restrictSupport ℚ_[p] {m | ∀ c ∈ Cs, wt LL j c m = la c}
def GlStableC (p : ℕ) [Fact p.Prime] (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r))
    (S : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p])) : Prop :=
  ∀ c ∈ Cs, ∀ d ∈ Cs, ∀ x ∈ S, glAct p LL j c d x ∈ S
noncomputable def HWC (p : ℕ) [Fact p.Prime] (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (la : Fin r → ℤ) :
    Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) :=
  WtSpC p LL j Cs la ⊓ ⨅ (c : Fin r) (d : Fin r) (_ : c ∈ Cs ∧ d ∈ Cs ∧ c < d), LinearMap.ker (glAct p LL j c d)
noncomputable def IsoC (p : ℕ) [Fact p.Prime] (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (la : Fin r → ℤ) :
    Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) :=
  sInf {S | HWC p LL j Cs la ≤ S ∧ GlStableC p LL j Cs S}
def CsSaturated {r : ℕ} (Cs : Finset (Fin r)) (T : Set (Fin r → ℤ)) : Prop :=
  ∀ la la', (∀ c ∈ Cs, la c = la' c) → (la ∈ T ↔ la' ∈ T)
def IsTypeProj (p : ℕ) [Fact p.Prime] (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (T : Set (Fin r → ℤ))
    (P : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p]) : Prop :=
  P ∘ₗ P = P ∧ LinearMap.range P = ⨆ (la : Fin r → ℤ) (_ : la ∈ T), IsoC p LL j Cs la ∧
    LinearMap.ker P = ⨆ (la : Fin r → ℤ) (_ : la ∉ T), IsoC p LL j Cs la
noncomputable def WeylLat (p : ℕ) [Fact p.Prime] (LL : Letters N) (j : ℕ)
    (h : MvPolynomial (Fin N × Fin r) ℚ_[p]) : Submodule ℤ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) :=
  sInf {L | h ∈ L ∧ ∀ c d : Fin r, c ≠ d → ∀ k : ℕ, ∀ x ∈ L,
    (((k.factorial : ℚ_[p]))⁻¹) • ((glAct p LL j c d) ^ k) x ∈ L}
def Primitive' (p : ℕ) [Fact p.Prime] {σ : Type} (h : MvPolynomial σ ℚ_[p]) : Prop :=
  h ∈ IntPol p σ ∧ ∃ m, ‖h.coeff m‖ = 1
def Letters.take (LL : Letters N) (k : ℕ) (hk : k ≤ N) : Letters k where
  vec := fun i => LL.vec (Fin.castLE hk i)
  deg := fun i => LL.deg (Fin.castLE hk i)
noncomputable def MMw (p : ℕ) [Fact p.Prime] {K : ℕ} [NeZero r] (LLw : Letters K) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) (w : Fin r → ℤ) : Submodule ℚ_[p] (MvPolynomial (Fin K × Fin r) ℚ_[p]) :=
  Y p LLw J M ⊓ HWC p LLw K (univ.erase ρ) w ⊓ WtSpC p LLw K univ w
noncomputable def MMwZ (p : ℕ) [Fact p.Prime] {K : ℕ} [NeZero r] (LLw : Letters K) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) (w : Fin r → ℤ) : Submodule ℤ_[p] (MvPolynomial (Fin K × Fin r) ℚ_[p]) :=
  (MMw p LLw J M ρ w).restrictScalars ℤ_[p] ⊓ IntPol p (Fin K × Fin r)
noncomputable def FilE (p : ℕ) [Fact p.Prime] {K : ℕ} [NeZero r] (LLw : Letters K) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) (w : Fin r → ℤ) (v : Fin K × Fin r) (e : ℕ) :
    Submodule ℤ_[p] (MvPolynomial (Fin K × Fin r) ℚ_[p]) :=
  MMwZ p LLw J M ρ w ⊓ (MvPolynomial.restrictSupport ℚ_[p] {m | e ≤ m v}).restrictScalars ℤ_[p]
noncomputable def grLat (p : ℕ) [Fact p.Prime] {K : ℕ} [NeZero r] (LLw : Letters K) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) (w : Fin r → ℤ) (v : Fin K × Fin r) (e : ℕ) :
    Submodule ℤ_[p] (MvPolynomial (Fin K × Fin r) ℚ_[p]) :=
  Submodule.span ℤ_[p] (initPart v e '' (FilE p LLw J M ρ w v e : Set (MvPolynomial (Fin K × Fin r) ℚ_[p])))
end Formalism.GM.M


