-- Prove2me | Definitions.Def_OAI_Combinatorics_SphericalRamsey_AlgebraicExtension
-- name    : OAI_Combinatorics_SphericalRamsey_AlgebraicExtension
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T10:08:40.101599+00:00
-- url     : https://prove2.me/theorems/a7d224f6-120c-4b8b-8cb3-76725c202c00
-- title:
--   Extending a derivation to an algebraic extension in characteristic zero
-- statement:
--   Let $F\subseteq K$ be fields with $F$ of characteristic $0$ and $K/F$ algebraic, and let $F$ carry a derivation $\delta$. Every $x\in K$ generates a finite simple extension $F(x)$, which carries a unique derivation extending $\delta$.
--
--   1. **Value.** $\widetilde\delta(x)\in K$ is the derivative of $x$ computed in $F(x)$.
--   2. **Independence.** In every finite intermediate field $L\ni x$, the derivative of $x$ equals $\widetilde\delta(x)$.
--   3. **Derivation laws.**
--   $$
--   \widetilde\delta(0)=0,\qquad\widetilde\delta(x+y)=\widetilde\delta(x)+\widetilde\delta(y),\qquad\widetilde\delta(xy)=x\,\widetilde\delta(y)+y\,\widetilde\delta(x),
--   $$
--      checked inside $F(x)\vee F(y)$.
--   4. **Differential structure.** $\widetilde\delta$ is a derivation of $K$, so $K$ becomes a differential field extending $F$.
--
--   Derivations extend uniquely through separable algebraic extensions. Combined with a transcendence basis, this produces derivations of $\mathbb{R}$ with prescribed values.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SphericalRamsey/AlgebraicExtension.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SphericalRamsey/AlgebraicExtension.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the GrahamSpherical mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.FieldTheory.Differential.Basic
import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleNumber
import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Localization.Integral
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Definitions.Def_GrahamSpherical
import Definitions.Def_OAI_Combinatorics_SphericalRamsey_Model
import Definitions.Def_OAI_Combinatorics_SphericalRamsey_MonochromaticObstruction
import Definitions.Def_OAI_Combinatorics_SphericalRamsey_BasisDerivation

namespace OAI

namespace GrahamSpherical.AlgebraicExtension

open IntermediateField
open scoped Differential

variable {F K : Type*} [Field F] [Field K] [CharZero F]
  [Algebra F K] [Algebra.IsAlgebraic F K] [Differential F]

local instance finiteSimple (x : K) : FiniteDimensional F F⟮x⟯ :=
  IntermediateField.adjoin.finiteDimensional
    (Algebra.IsIntegral.isIntegral (R := F) x)

/-- The value forced by the native derivation on a finite simple subextension. -/
noncomputable def value (x : K) : K :=
  ((Differential.deriv (⟨x, mem_adjoin_simple_self F x⟩ : F⟮x⟯) : F⟮x⟯) : K)

/-- All finite subextensions compute the same derivative of a given element. -/
theorem value_eq (L : IntermediateField F K) [FiniteDimensional F L]
    (x : K) (hx : x ∈ L) :
    value (F := F) x = ((Differential.deriv (⟨x, hx⟩ : L) : L) : K) := by
  have hle : F⟮x⟯ ≤ L := adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hx)
  have h := Differential.algHom_deriv' (inclusion hle) (inclusion_injective hle)
    (⟨x, mem_adjoin_simple_self F x⟩ : F⟮x⟯)
  exact congrArg (fun z : L => (z : K)) h

theorem value_zero : value (F := F) (0 : K) = 0 := by
  rw [value_eq (F⟮(0 : K)⟯) 0 (zero_mem _)]
  change ((Differential.deriv (0 : F⟮(0 : K)⟯) : F⟮(0 : K)⟯) : K) = 0
  simp

theorem value_add (x y : K) :
    value (F := F) (x + y) = value (F := F) x + value (F := F) y := by
  let L : IntermediateField F K := F⟮x⟯ ⊔ F⟮y⟯
  have hx : x ∈ L := (show F⟮x⟯ ≤ L from le_sup_left) (mem_adjoin_simple_self F x)
  have hy : y ∈ L := (show F⟮y⟯ ≤ L from le_sup_right) (mem_adjoin_simple_self F y)
  rw [value_eq L (x + y) (L.add_mem hx hy), value_eq L x hx, value_eq L y hy]
  exact congrArg (fun z : L => (z : K))
    (map_add Differential.deriv (⟨x, hx⟩ : L) (⟨y, hy⟩ : L))

theorem value_mul (x y : K) :
    value (F := F) (x * y) = x * value (F := F) y + y * value (F := F) x := by
  let L : IntermediateField F K := F⟮x⟯ ⊔ F⟮y⟯
  have hx : x ∈ L := (show F⟮x⟯ ≤ L from le_sup_left) (mem_adjoin_simple_self F x)
  have hy : y ∈ L := (show F⟮y⟯ ≤ L from le_sup_right) (mem_adjoin_simple_self F y)
  rw [value_eq L (x * y) (L.mul_mem hx hy), value_eq L x hx, value_eq L y hy]
  have hm : (⟨x, hx⟩ : L) * (⟨y, hy⟩ : L) = ⟨x * y, L.mul_mem hx hy⟩ := by
    apply Subtype.ext
    exact L.coe_mul _ _
  have hd := Derivation.leibniz Differential.deriv (⟨x, hx⟩ : L) (⟨y, hy⟩ : L)
  rw [hm] at hd
  simpa only [smul_eq_mul, IntermediateField.coe_add, IntermediateField.coe_mul,
    Subtype.coe_mk] using congrArg (fun z : L => (z : K)) hd

/-- Extension to an arbitrary algebraic field extension in characteristic zero. -/
@[instance_reducible]
noncomputable def differentialAlgebraic : Differential K where
  deriv := Derivation.mk'
    (AddMonoidHom.toIntLinearMap
      { toFun := value (F := F), map_zero' := value_zero, map_add' := value_add })
    (by intro x y; exact value_mul x y)

end GrahamSpherical.AlgebraicExtension

end OAI


