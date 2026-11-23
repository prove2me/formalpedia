-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_ExistsArBaseAway
-- name    : Development_AbelianVarietyTheory_Definitions_ModuliSpaces_ExistsArBaseAway
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:55:01.656461+00:00
-- url     : https://prove2.me/theorems/64bdef66-b9dd-44f8-90a5-a358310a3611
-- title:
--   Exists Ar Base Away
-- statement:
--   Definitions and structural lemmas for Exists Ar Base Away, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ModuliSpaces/ExistsArBaseAway.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_GoodClass
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_W8AddTransposeEqE8
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
namespace GlobalTheory.ZM
variable {o : Type} [CommRing o] {S : Scheme.{0}} {g k : ℕ} {J : Type} {b : TBase o k} {s : S ⟶ Sp o}
section PEL
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
def IsSympBasis (D : Datum H) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) : Prop :=
  ∀ i j, D.EF (bas (Pi.single i 1)) (bas (Pi.single j 1)) = Out.stdSymp g i j
def IsPEL (D : Datum H) (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (ρ : o) (t : TObj g k J b s) (τ : SAB H S) : Prop :=
  ∃ φ : τ.G ≅ t.A, IsMonHom φ.hom ∧ LBIso τ.PP.L (t.L.pull φ.hom.left) ∧ (∀ j, τ.act.act (a j) ≫ φ.hom = φ.hom ≫ t.act j) ∧
    ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (x : Sp K ⟶ S) (β : o →+* K), x ≫ s = spMap β →
      DetCond D τ.act x (β ρ) ∧ ∃ I : TateIso D K (Over.mk x ⟶ τ.G) (fun c y => y ≫ τ.act.act c)
          (fun n y y' c => Out.WeilIs τ.G τ.PP.L n y y' (unitOn c)),
        (I.ζ k : K) = β b.ζ ∧ ∀ i, I.ev k (bas (Pi.single i 1)) ≫ φ.hom =
          (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver S) ≫ t.pt i
def PELClass (D : Datum H) (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (ρ : o) (em : o →+* ℂ)
    (t : TObj g k J b (spMap em)) : Prop := ∃ τ, IsPEL D a bas ρ t τ
end PEL
section Siegel
variable {h : ℕ}
def IsE8 (W : Matrix (Fin 8) (Fin 8) ℤ) : Prop := ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef ∧ (W + W.transpose).det = 1
def IsSharpBasis (W : Matrix (Fin 8) (Fin 8) ℤ) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))) : Prop :=
  ∀ i j, ∑ u, ∑ v, (W + W.transpose) u v * omegaStd (bas (Pi.single i 1) u) (bas (Pi.single j 1) v) = Out.stdSymp g i j
def IsSharp (W : Matrix (Fin 8) (Fin 8) ℤ) (a : J → Matrix (Fin 8) (Fin 8) ℤ)
    (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))) (t : TObj g k J b s) (c : SiegPre h k (b.ζ : o) s) : Prop :=
  ∃ pr : Fin 8 → (t.A ⟶ c.A), (∀ u, IsMonHom (pr u)) ∧
    (∀ (T : Over S) (y : Fin 8 → (T ⟶ c.A)), ∃! x : T ⟶ t.A, ∀ u, x ≫ pr u = y u) ∧
    LBIso t.L (LB.LinComb c.P (K := Fin 8 × Fin 8) (fun uv => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2)) ∧
    (∀ j u, t.act j ≫ pr u = (List.ofFn fun v => pr v ^ a j u v).prod) ∧
    ∀ i u, (t.pt i ≫ pr u).left = (c.lev (bas (Pi.single i 1) u)).left
def SharpClass (W : Matrix (Fin 8) (Fin 8) ℤ) (a : J → Matrix (Fin 8) (Fin 8) ℤ)
    (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))) (em : o →+* ℂ) (t : TObj g k J b (spMap em)) : Prop :=
  ∃ c : SiegPre h k (b.ζ : o) (spMap em), c.Principal ∧ IsSharp W a bas t c
end Siegel
def ArBase (em : o →+* ℂ) : Prop := IsDedekindDomain o ∧ Algebra.FiniteType ℤ o ∧ Function.Injective em
section Inhabitants
end Inhabitants
end GlobalTheory.ZM
end


