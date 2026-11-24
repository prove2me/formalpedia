-- Prove2me | Definitions.Def_ReciprocityTheory_Chebotarev_CasimirPowerSurjectiveSymmetric
-- name    : ReciprocityTheory_Chebotarev_CasimirPowerSurjectiveSymmetric
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:53:26.554087+00:00
-- url     : https://prove2.me/theorems/ebe8b56d-ec1d-453b-90ac-c7f8796927eb
-- title:
--   Casimir Power Surjective Symmetric
-- statement:
--   Definitions and structural lemmas for Casimir Power Surjective Symmetric, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/CasimirPowerSurjectiveSymmetric.lean

import Definitions.Def_ReciprocityTheory_Chebotarev_NZIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Filter Topology
namespace ReciprocityTheory.Cheb
def E1 : Prop :=
  (∀ (E : Type) [Field E] [NumberField E] (f : NZIdeal E → ℂ), (∀ a, ‖f a‖ ≤ 1) → ∀ s : ℝ, 1 < s →
      Summable (fun a : NZIdeal E => f a * ((Ideal.absNorm a.1 : ℕ) : ℂ) ^ (-(s : ℂ)))) ∧
  (∀ (E : Type) [Field E] [NumberField E] (s : ℝ), 1 < s →
      dedekindZeta E s = ∑' a : NZIdeal E, ((Ideal.absNorm a.1 : ℕ) : ℂ) ^ (-(s : ℂ))) ∧
  (∀ (E : Type) [Field E] [NumberField E] (s : ℝ), 1 < s →
      Summable (fun q : Prm E => ((Nrm q : ℕ) : ℝ) ^ (-s)))
def E2 : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime] (χ : DirichletCharacter ℂ l) (s : ℝ), 1 < s →
    Complex.exp (abelian₂ E χ s) = Lser E χ s
def CasimirPowerSurjectiveSymmetric : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime] (χ : DirichletCharacter ℂ l),
    ∃ C : ℝ, ∀ s : ℝ, 1 < s → ‖abelian₂ E χ s - Psum E χ s‖ ≤ C
def faceMap_castSucc_comp_eq_succ : Prop :=
  ∀ (E : Type) [Field E] [NumberField E],
    ∃ C : ℝ, ∀ s : ℝ, s ∈ Set.Ioc 1 2 → |PE E s - Real.log (1 / (s - 1))| ≤ C
def SmoothMapSeminormBound : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime] (χ : DirichletCharacter ℂ l),
    ContinuousOn (fun s : ℝ => abelian₂ E χ s) (Set.Ioi 1)
def KProp : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime], Irreducible (Polynomial.cyclotomic l E) →
    ∀ χ : DirichletCharacter ℂ l, χ ≠ 1 → ∃ L1 : ℂ, Tendsto (fun s : ℝ => Lser E χ s) (𝓝[>] 1) (𝓝 L1)
def S1 : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime], Irreducible (Polynomial.cyclotomic l E) →
    ∃ C : ℝ, ∀ᶠ s in 𝓝[>] (1 : ℝ), PE E s - C ≤ ((l - 1 : ℕ) : ℝ) * Pcl E l 1 s
def S2 : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime], Irreducible (Polynomial.cyclotomic l E) →
    ∀ χ : DirichletCharacter ℂ l, χ ≠ 1 → ∀ m : ℕ, m ≠ 0 →
      ∃ q : Prm E, Nat.Coprime (Nrm q) (m * l) ∧ χ ((Nrm q : ℕ) : ZMod l) ≠ 1
end ReciprocityTheory.Cheb


