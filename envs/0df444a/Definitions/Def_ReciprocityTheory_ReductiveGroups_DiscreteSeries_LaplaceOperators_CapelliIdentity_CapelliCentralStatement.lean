-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_CapelliCentralStatement
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_CapelliCentralStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:38:49.704804+00:00
-- url     : https://prove2.me/theorems/f7a943f2-d3d5-421b-ae42-24e3a4b1d05c
-- title:
--   Capelli Central Statement
-- statement:
--   Definitions and structural lemmas for Capelli Central Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/CapelliIdentity/CapelliCentralStatement.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_IsInfUnitary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
namespace ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
open ReciprocityTheory.ChartRestriction.DS
universe u v w
section Ring
variable {𝒰 : Type*} [Ring 𝒰] [Algebra ℂ 𝒰] {n : ℕ}
def GlRelR (E : Fin n → Fin n → 𝒰) : Prop :=
  ∀ a b c d : Fin n, E a b * E c d - E c d * E a b =
    (if b = c then E a d else 0) - (if d = a then E c b else 0)
def capEntry (E : Fin n → Fin n → 𝒰) (x : ℂ) (a b : Fin n) : 𝒰 :=
  E a b + if a = b then algebraMap ℂ 𝒰 x else 0
def cminor {p : ℕ} (E : Fin n → Fin n → 𝒰) (R C : Fin p → Fin n) (x : ℂ) : 𝒰 :=
  ∑ σ : Equiv.Perm (Fin p), ((Equiv.Perm.sign σ : ℤˣ) : ℤ) •
    (List.ofFn fun j : Fin p => capEntry E (x - ((j : ℕ) : ℂ)) (R (σ j)) (C j)).prod
def rminor {p : ℕ} (E : Fin n → Fin n → 𝒰) (R C : Fin p → Fin n) (x : ℂ) : 𝒰 :=
  ∑ σ : Equiv.Perm (Fin p), ((Equiv.Perm.sign σ : ℤˣ) : ℤ) •
    (List.ofFn fun i : Fin p => capEntry E (x - ((p : ℕ) : ℂ) + 1 + ((i : ℕ) : ℂ)) (R i) (C (σ i))).prod
def capelliC (E : Fin n → Fin n → 𝒰) (x : ℂ) : 𝒰 :=
  cminor E id id x
end Ring
section Tensor
variable {M : Type*} [AddCommGroup M] [Module ℂ M] {n : ℕ}
def tensV (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) : Module.End ℂ (Fin n → M) :=
  LinearMap.pi fun d =>
    (E a b).comp (LinearMap.proj d) + if d = a then (LinearMap.proj b : (Fin n → M) →ₗ[ℂ] M) else 0
def tensVd (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) : Module.End ℂ (Fin n → M) :=
  LinearMap.pi fun d =>
    (E a b).comp (LinearMap.proj d) - if d = b then (LinearMap.proj a : (Fin n → M) →ₗ[ℂ] M) else 0
def eeV (E : Fin n → Fin n → Module.End ℂ M) : Module.End ℂ (Fin n → M) :=
  LinearMap.pi fun b => ∑ a, (E a b).comp (LinearMap.proj a)
def eeVd (E : Fin n → Fin n → Module.End ℂ M) : Module.End ℂ (Fin n → M) :=
  LinearMap.pi fun a => -∑ c, (E a c).comp (LinearMap.proj c)
def nnPlus {m : ℕ} (E : Fin (m + 1) → Fin (m + 1) → Module.End ℂ M) (y : Fin (m + 1) → ℂ) (om : ℂ)
    (v : M) : Fin (m + 1) → M :=
  fun d => ∑ c, (y c * (-1) ^ ((d : ℕ) + (c : ℕ))) • cminor E d.succAbove c.succAbove (om - 1) v
def nnMinus {m : ℕ} (E : Fin (m + 1) → Fin (m + 1) → Module.End ℂ M) (β : Fin (m + 1) → ℂ) (om : ℂ)
    (v : M) : Fin (m + 1) → M :=
  fun d => ∑ c, (β c * (-1) ^ ((d : ℕ) + (c : ℕ))) • cminor E c.succAbove d.succAbove om v
end Tensor
section Bessel
def blk (k r : ℕ) (i : Fin (k + 2 * r + 1)) : ℕ :=
  if (i : ℕ) < r then i else if (i : ℕ) ≤ r + k then r else (i : ℕ) - k
def inW (k r : ℕ) (i : Fin (k + 2 * r + 1)) : Prop :=
  r ≤ (i : ℕ) ∧ (i : ℕ) < r + k
instance (k r : ℕ) : DecidablePred (inW k r) := fun i => by unfold inW; infer_instance
def IsSimplePair (k r : ℕ) (a b : Fin (k + 2 * r + 1)) : Prop :=
  blk k r b = blk k r a + 1 ∧ ¬ inW k r a ∧ ¬ inW k r b
instance (k r : ℕ) : DecidableRel (IsSimplePair k r) := fun a b => by
  unfold IsSimplePair; infer_instance
def wIdx (k r : ℕ) (j : Fin k) : Fin (k + 2 * r + 1) :=
  ⟨r + (j : ℕ), by omega⟩
def kappa (k r : ℕ) (ψ : Fin (k + 2 * r + 1) → Fin (k + 2 * r + 1) → ℂ) : ℂ :=
  ∏ a, ∏ b, if IsSimplePair k r a b then ψ a b else 1
end Bessel
def CapelliCentralStatement : Prop :=
  ∀ (𝒰 : Type u) [Ring 𝒰] [Algebra ℂ 𝒰] (n : ℕ) (E : Fin n → Fin n → 𝒰) (x : ℂ),
    GlRelR E → ∀ a b, Commute (E a b) (capelliC E x)
def CapelliHWStatement : Prop :=
  ∀ (M : Type u) [AddCommGroup M] [Module ℂ M] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ M)
    (μ : Fin n → ℝ) (v : M) (x : ℂ), IsGlRep E → IsHWVec E μ v →
    ∀ y ∈ genSub E (Submodule.span ℂ {v}),
      capelliC E x y = (∏ a : Fin n, (x + (μ a : ℂ) - ((a : ℕ) : ℂ))) • y
def CapelliExpandStatement : Prop :=
  ∀ (𝒰 : Type u) [Ring 𝒰] [Algebra ℂ 𝒰] (m : ℕ) (E : Fin (m + 1) → Fin (m + 1) → 𝒰) (om : ℂ),
    GlRelR E →
    (∀ b c : Fin (m + 1), ∑ d : Fin (m + 1), ((-1 : ℂ) ^ ((d : ℕ) + (c : ℕ))) •
        (capEntry E om d b * cminor E d.succAbove c.succAbove (om - 1)) =
      if b = c then capelliC E om else 0) ∧
    (∀ a c : Fin (m + 1), ∑ d : Fin (m + 1), ((-1 : ℂ) ^ ((d : ℕ) + (c : ℕ))) •
        (capEntry E (om - (m : ℂ)) a d * cminor E c.succAbove d.succAbove om) =
      if a = c then capelliC E om else 0)
def CapelliTensorStatement : Prop :=
  ∀ (M : Type u) [AddCommGroup M] [Module ℂ M] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ M),
    IsGlRep E → IsGlRep (tensV E) ∧ IsGlRep (tensVd E) ∧
    (∀ f : Fin n → M, casimir (tensV E) f =
      (fun d => casimir E (f d)) + ((n : ℂ) • f + (2 : ℂ) • eeV E f)) ∧
    (∀ f : Fin n → M, casimir (tensVd E) f =
      (fun d => casimir E (f d)) + ((n : ℂ) • f + (2 : ℂ) • eeVd E f))
def CapelliAPlusStatement : Prop :=
  ∀ (M : Type u) [AddCommGroup M] [Module ℂ M] (m : ℕ) (E : Fin (m + 1) → Fin (m + 1) → Module.End ℂ M)
    (y : Fin (m + 1) → ℂ) (om : ℂ) (v : M), IsGlRep E → capelliC E om v = 0 →
    eeV E (nnPlus E y om v) = (-om) • nnPlus E y om v
def CapelliAMinusStatement : Prop :=
  ∀ (M : Type u) [AddCommGroup M] [Module ℂ M] (m : ℕ) (E : Fin (m + 1) → Fin (m + 1) → Module.End ℂ M)
    (β : Fin (m + 1) → ℂ) (om : ℂ) (v : M), IsGlRep E → capelliC E om v = 0 →
    eeVd E (nnMinus E β om v) = (om - (m : ℂ)) • nnMinus E β om v
def CapelliBStatement : Prop :=
  ∀ (M : Type u) (R : Type v) [AddCommGroup M] [Module ℂ M] [AddCommGroup R] [Module ℂ R] (k r : ℕ)
    (E : Fin (k + 2 * r + 1) → Fin (k + 2 * r + 1) → Module.End ℂ M)
    (D : Fin k → Fin k → Module.End ℂ R) (ψ : Fin (k + 2 * r + 1) → Fin (k + 2 * r + 1) → ℂ)
    (l : M →ₗ[ℂ] R) (x : ℂ), IsGlRep E → 0 < r →
    (∀ a b, blk k r a < blk k r b → l ∘ₗ E a b = ψ a b • l) →
    (∀ a b, blk k r a < blk k r b → ¬ IsSimplePair k r a b → ψ a b = 0) →
    (∀ i j, l ∘ₗ E (wIdx k r i) (wIdx k r j) = D i j ∘ₗ l) →
    l ∘ₗ cminor E Fin.castSucc Fin.succ x = ((-1) ^ k * kappa k r ψ) • (capelliC D (x - (r : ℂ)) ∘ₗ l)
def WhittakerZeroStatement : Prop :=
  ∀ (M : Type u) (R : Type v) [AddCommGroup M] [Module ℂ M] [AddCommGroup R] [Module ℂ R] (k : ℕ)
    (E : Fin (k + 1) → Fin (k + 1) → Module.End ℂ M) (D : Fin k → Fin k → Module.End ℂ R)
    (l : M →ₗ[ℂ] R) (x : ℂ),
    (∀ i j, l ∘ₗ E (Fin.castSucc i) (Fin.castSucc j) = D i j ∘ₗ l) →
    l ∘ₗ cminor E Fin.castSucc Fin.castSucc x = capelliC D x ∘ₗ l
end ReciprocityTheory.ChartRestriction.DS.Lap.Capelli


