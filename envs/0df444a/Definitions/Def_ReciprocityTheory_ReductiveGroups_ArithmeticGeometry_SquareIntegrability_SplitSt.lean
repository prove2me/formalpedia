-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:14:09.90357+00:00
-- url     : https://prove2.me/theorems/d5ca3bcb-93ab-4d64-83d4-64414bf7955e
-- title:
--   Split St
-- statement:
--   Definitions and structural lemmas for Split St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SplitSt.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
noncomputable section
variable {E : Type} [Field E] [NumberField E]
abbrev IR {dim : (E →+* ℂ) → ℕ} (I : Submodule ℤ (Vsp dim)) : Submodule ℝ (Vsp dim) :=
  Submodule.span ℝ (I : Set (Vsp dim))
def IsU {dim : (E →+* ℂ) → ℕ} (I : Submodule ℤ (Vsp dim)) (x u : Vsp dim) : Prop :=
  u ∈ IR I ∧ ∀ a ∈ IR I, inner ℝ u a = (Hf x a).im
def InPart {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) (v : Vsp dim) : Prop := ∀ j : Idx dim, j.1 ≠ σ → v j = 0
def d1 {dim : (E →+* ℂ) → ℕ} (F : (Fin 1 → Vsp dim) → ℂ) (c : ℕ) (x : Fin c → Vsp dim) : ℂ :=
  iteratedFDeriv ℂ c F 0 (fun k _ => x k)
section
variable {DF : ℕ} {X : PT E}
def Par.th (P : Par X DF) : ℝ := ReciprocityTheory.ChartRestriction.G.I2.th (E := E) P.q P.R0
def Par.eps1 (P : Par X DF) : ℝ :=
  7 * 2 ^ X.gA * (4.3 : ℝ) ^ dstar (E := E) P.m * Real.exp (-t0 (E := E) P.q P.R0)
def Par.K6 (P : Par X DF) : ℝ :=
  6 * (2 * (dstar (E := E) P.m : ℝ)) ^ ((dstar (E := E) P.m : ℝ) / 2)
structure IsSplit (P : Par X DF) (I : Submodule ℤ (Vsp X.dim)) : Prop where
  le : I ≤ X.L
  sat : ∀ x ∈ X.L, ∀ k : ℤ, k ≠ 0 → k • x ∈ I → x ∈ I
  stable : ∀ (α : 𝓞 E) x, x ∈ I → act α x ∈ I
  iso : ∀ x ∈ I, ∀ y ∈ I, (Hf x y).im = 0
  eps : ∀ x ∈ I, X.eps x = 1
  rank : ∃ ρ ≤ P.m, Module.finrank ℝ (IR I) = 2 * PT.f E * ρ
  ne_bot : I ≠ ⊥ ↔ X.la1 < P.th

  thick : ∀ x ∈ X.L, (∀ a ∈ I, (Hf x a).im = 0) → x ∉ I → P.th ≤ Metric.infDist x (IR I)

  sep : ∀ x ∈ X.L, ∀ u, IsU I x u → u ≠ 0 → b0 (E := E) P.q P.R0 ≤ ‖u‖ ^ 2

  u1 : ∃ x : Fin (Module.finrank ℝ (IR I)) → Vsp X.dim, ∃ u : Fin (Module.finrank ℝ (IR I)) → Vsp X.dim,
    (∀ j, x j ∈ X.L ∧ IsU I (x j) (u j)) ∧ LinearIndependent ℝ u ∧
      ∀ j, ‖u j‖ ^ 2 ≤ PT.rd E ^ 2 * (dstar (E := E) P.m : ℝ) ^ 4 * P.ph / (2 * PT.f E)

  u2 : ∀ (k : ℕ) (x u : Fin k → Vsp X.dim), (∀ j, x j ∈ X.L ∧ IsU I (x j) (u j)) →
    Submodule.span ℝ {w | ∃ j, ∃ α : 𝓞 E, IsU I (act α (x j)) w} = IR I →
      P.ph ≤ ∑ j, ‖u j‖ ^ 2 / 2
end
def SplitStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (X : PT E) (DF : ℕ) (P : Par X DF),
    ∃ I, IsSplit P I
def CharStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (X : PT E) (DF : ℕ) (P : Par X DF)
    (I : Submodule ℤ (Vsp X.dim)), IsSplit P I → ∀ σ : E →+* ℂ, ∀ ρ : ℕ,
    Module.finrank ℂ ((Submodule.span ℂ (I : Set (Vsp X.dim))) ⊓
      {carrier := {v | InPart σ v}, add_mem' := fun {a b} ha hb j hj => by
          simp [ha j hj, hb j hj], zero_mem' := fun j _ => rfl,
        smul_mem' := fun c v hv j hj => by simp [hv j hj]} : Submodule ℂ (Vsp X.dim)) = ρ →
    ∃ (w : Fin ρ → Vsp X.dim) (x u : Fin ρ → Vsp X.dim) (R : Fin ρ → ℝ) (ε : Fin ρ → Fin ρ → ℂ),
      (∀ s, InPart σ (w s) ∧ w s ∈ Submodule.span ℂ (I : Set (Vsp X.dim))) ∧
      (∀ s s', Hf (w s) (w s') = if s = s' then 1 else 0) ∧
      (∀ s, x s ∈ X.L ∧ IsU I (x s) (u s)) ∧
      (∀ s s', s < s' → ε s s' = 0) ∧
      (∀ s, Real.sqrt (∑ s', ‖ε s s'‖ ^ 2) ≤ 1 / (30 * ρ ^ 2) ∧
        ∑ s', ‖ε s s'‖ ≤ Real.sqrt ρ / (30 * ρ ^ 2)) ∧
      (∀ s v, InPart σ v → Hf v (u s) / R s = Hf v (w s) + ∑ s', ε s s' * Hf v (w s')) ∧
      (∀ s, ‖u s‖ ≤ 1.5 * R s ∧ 1 ≤ 2 * Real.pi * R s) ∧
      (∀ s, ∀ y ∈ X.L, ∀ uy, IsU I y uy → |2 * inner ℝ (u s) uy| ≤ M1 (E := E) P.m * ‖uy‖ ^ 2) ∧
      (∀ s, ‖u s‖ ^ 2 ≤ Cchi (E := E) P.m * P.ph)
def ColTorusStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (X : PT E) (DF : ℕ) (P : Par X DF)
    (I : Submodule ℤ (Vsp X.dim)), IsSplit P I → ∀ (c : ℕ), c ≤ DF → ∀ (σ : E →+* ℂ)
    (x0 u : Vsp X.dim), x0 ∈ X.L → IsU I x0 u → ∀ n : ℝ, 1 ≤ n → 2 * Real.pi * ‖u‖ ≤ 1.5 * n →
    (∀ y ∈ X.L, ∀ uy, IsU I y uy → |2 * inner ℝ u uy| ≤ M1 (E := E) P.m * ‖uy‖ ^ 2) →
    ∃ s' ∈ X.Sec P.q 1, ∃ ζ : ℂ, ‖ζ‖ = 1 ∧
      (∀ xs : Fin c → Vsp X.dim, (∀ k, InPart σ (xs k) ∧ ‖xs k‖ = 1) →
        ‖d1 s' c xs - ζ * (2 * Real.pi) ^ c * ∏ k, Hf (xs k) u‖ ≤ P.eps1 * n ^ c) ∧
      P.K6⁻¹ * Real.exp (-(2 * Real.pi * ‖u‖ ^ 2 / P.q)) * X.l2 P.q s' ≤ n ^ (2 * c)
def ColAbelStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (X : PT E) (DF : ℕ) (P : Par X DF)
    (I : Submodule ℤ (Vsp X.dim)), IsSplit P I → ∀ (c : ℕ), c ≤ DF → ∀ (σ : E →+* ℂ)
    (ξ : Vsp X.dim), InPart σ ξ → ‖ξ‖ = 1 → (∀ a ∈ I, Hf ξ a = 0) →
    ∃ s' ∈ X.Sec P.q 1,
      (∀ xs : Fin c → Vsp X.dim, (∀ k, InPart σ (xs k) ∧ ‖xs k‖ = 1) →
        ‖d1 s' c xs - (c.factorial : ℂ) * ∏ k, Hf (xs k) ξ‖ ≤ P.eps1 * c.factorial) ∧
      P.K6⁻¹ * X.l2 P.q s' ≤ (c.factorial : ℝ) ^ 2
def ColEmptyStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (X : PT E) (DF : ℕ) (P : Par X DF)
    (I : Submodule ℤ (Vsp X.dim)), IsSplit P I →
    ∃ s' ∈ X.Sec P.q 1, 1 / 2 ≤ ‖s' 0‖ ∧ P.K6⁻¹ * X.l2 P.q s' ≤ 1
end
end ReciprocityTheory.ChartRestriction.G.I2


