-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Permute
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Permute
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:33:10.972858+00:00
-- url     : https://prove2.me/theorems/c886eab4-7c14-495d-8088-e2f49a5148ae
-- title:
--   Permute
-- statement:
--   Definitions and structural lemmas for Permute, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/Permute.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasValK
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
namespace ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
section Defs
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M]
abbrev Big (n k : ℕ) (M : Type*) := PiLp 2 (fun _ : Fin k → Fin n × Fin n => M)
def coord (k : ℕ) (κ : Fin k → Fin n × Fin n) : Big n k M →ₗ[ℂ] M :=
  LinearMap.proj (R := ℂ) (φ := fun _ : Fin k → Fin n × Fin n => M) κ ∘ₗ
    (WithLp.linearEquiv 2 ℂ ((Fin k → Fin n × Fin n) → M)).toLinearMap
def ofCoords {X : Type*} [AddCommGroup X] [Module ℂ X] (k : ℕ)
    (f : (Fin k → Fin n × Fin n) → (X →ₗ[ℂ] M)) : X →ₗ[ℂ] Big n k M :=
  (WithLp.linearEquiv 2 ℂ ((Fin k → Fin n × Fin n) → M)).symm.toLinearMap ∘ₗ LinearMap.pi f
def mAct (E : Fin n → Fin n → Module.End ℂ M) (k : ℕ) (a b : Fin n) : Module.End ℂ (Big n k M) :=
  ofCoords k fun κ => E a b ∘ₗ coord k κ
def factorAd (k : ℕ) (i : Fin k) (a b : Fin n) : Module.End ℂ (Big n k M) :=
  ofCoords k fun κ =>
    (if (κ i).1 = a then coord k (Function.update κ i (b, (κ i).2)) else 0) -
      (if (κ i).2 = b then coord k (Function.update κ i ((κ i).1, a)) else 0)
def bAct (E : Fin n → Fin n → Module.End ℂ M) (k : ℕ) (a b : Fin n) : Module.End ℂ (Big n k M) :=
  mAct E k a b + ∑ i, factorAd k i a b
def factorCasimir (ε : Fin n → Bool) (k : ℕ) : Module.End ℂ (Big n k M) :=
  casimirK ε (fun a b => ∑ i, factorAd (M := M) k i a b)
def crossOp (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (k : ℕ) (i : Fin k) :
    Module.End ℂ (Big n k M) :=
  ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a), factorAd k i a b * mAct E k b a
def ncV (ε : Fin n → Bool) (V : Submodule ℂ M) (k : ℕ) : Submodule ℂ (Big n k M) :=
  ⨅ κ : Fin k → Fin n × Fin n,
    (if ∀ i, ε (κ i).1 ≠ ε (κ i).2 then V else ⊥).comap (coord k κ)
def word (E : Fin n → Fin n → Module.End ℂ M) {k : ℕ} (κ : Fin k → Fin n × Fin n) :
    Module.End ℂ M :=
  (List.ofFn fun i => E (κ i).1 (κ i).2).prod
def phi (E : Fin n → Fin n → Module.End ℂ M) (k : ℕ) : Big n k M →ₗ[ℂ] M :=
  ∑ κ, word E κ ∘ₗ coord k κ
def slice {k : ℕ} (i : Fin k) (κ : Fin k → Fin n × Fin n) (F : Big n k M) : Big n 1 M :=
  WithLp.toLp 2 (fun ι : Fin 1 → Fin n × Fin n => F (Function.update κ i (ι 0)))
def permute {k : ℕ} (σ : Equiv.Perm (Fin k)) (F : Big n k M) : Big n k M :=
  WithLp.toLp 2 (fun κ => F (κ ∘ σ))
def Wm (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (V : Submodule ℂ M) :
    Submodule ℂ (Big n 1 M) :=
  ⨆ (θ : ℝ) (_ : θ < 0), Module.End.eigenspace (crossOp ε E 1 0) (θ : ℂ) ⊓ ncV ε V 1
def Wp (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (V : Submodule ℂ M) :
    Submodule ℂ (Big n 1 M) :=
  ⨆ (θ : ℝ) (_ : 0 < θ), Module.End.eigenspace (crossOp ε E 1 0) (θ : ℂ) ⊓ ncV ε V 1
end Defs
end ReciprocityTheory.ChartRestriction.DS


