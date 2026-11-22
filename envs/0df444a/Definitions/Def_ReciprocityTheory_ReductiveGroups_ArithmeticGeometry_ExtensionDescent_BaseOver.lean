-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_BaseOver
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_BaseOver
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:27:33.75873+00:00
-- url     : https://prove2.me/theorems/3e2273ac-7b44-4f77-b628-4d333ac6055e
-- title:
--   Base Over
-- statement:
--   Definitions and structural lemmas for Base Over, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/BaseOver.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ConstGen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
attribute [local instance] Over.cartesianMonoidalCategory
namespace ReciprocityTheory.ChartRestriction.G.Out
open Semi
def stdSymp (g : ℕ) (i j : Fin (2 * g)) : ℤ :=
  if (i : ℕ) < g ∧ (j : ℕ) = (i : ℕ) + g then 1
  else if (j : ℕ) < g ∧ (i : ℕ) = (j : ℕ) + g then -1 else 0
variable {S : Scheme.{0}}
abbrev baseOver (S : Scheme.{0}) : Over S := Over.mk (𝟙 S)
def linComb {A : Over S} [GrpObj A] {T : Over S} {n : ℕ} (y : Fin n → (T ⟶ A)) (a : Fin n → ℕ) :
    T ⟶ A :=
  (List.ofFn fun i => y i ^ a i).prod
structure Level (P : PolAV S) (k : ℕ) (ze : Γ(S, ⊤)ˣ) where

  pt : Fin (2 * P.g) → (baseOver S ⟶ P.A)

  prim : IsPrimitiveRoot ze k

  torsion : ∀ i, pt i ^ k = 1

  indep : ∀ (K : Type) [Field K] [IsAlgClosed K] (s : Spec (CommRingCat.of K) ⟶ S)
    (c c' : Fin (2 * P.g) → Fin k),
    linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver S) ≫ pt i) (fun i => (c i : ℕ)) =
      linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver S) ≫ pt i) (fun i => (c' i : ℕ)) →
    c = c'

  span : ∀ (K : Type) [Field K] [IsAlgClosed K] (s : Spec (CommRingCat.of K) ⟶ S)
    (y : Over.mk s ⟶ P.A), y ^ k = 1 →
    ∃ c : Fin (2 * P.g) → Fin k,
      linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver S) ≫ pt i) (fun i => (c i : ℕ)) = y

  pairing : ∀ i j, WeilIs P.A P.L k (pt i) (pt j) (ze ^ stdSymp P.g i j)
def Level.toPt {P : PolAV S} {k : ℕ} {ze : Γ(S, ⊤)ˣ} (lev : Level P k ze)
    (a : Fin (2 * P.g) → ZMod k) : baseOver S ⟶ P.A :=
  linComb lev.pt (fun i => (a i).val)
end ReciprocityTheory.ChartRestriction.G.Out


