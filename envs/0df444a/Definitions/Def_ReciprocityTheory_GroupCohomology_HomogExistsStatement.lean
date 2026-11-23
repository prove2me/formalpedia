-- Prove2me | Definitions.Def_ReciprocityTheory_GroupCohomology_HomogExistsStatement
-- name    : ReciprocityTheory_GroupCohomology_HomogExistsStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:05:41.550973+00:00
-- url     : https://prove2.me/theorems/32d460cb-bdf3-4a75-ae83-141876ece0d7
-- title:
--   Homog Exists Statement
-- statement:
--   Definitions and structural lemmas for Homog Exists Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/HomogExistsStatement.lean

import Definitions.Def_ReciprocityTheory_GroupCohomology_ContinuousContractNth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.Coh
open ReciprocityTheory.Gal Cx Function
noncomputable section
universe u
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
def hcoch (M : TRep R G) (X : Type u) [TopologicalSpace X] [MulAction G X] (n : ℕ) :
    Submodule R ((Fin (n + 1) → X) → M.V) where
  carrier := {F | Continuous F ∧ ∀ (g : G) x, F (fun i => g • x i) = M.rho g (F x)}
  zero_mem' := ⟨continuous_const, fun g x => by simp⟩
  add_mem' := fun {a b} ha hb => ⟨ha.1.add hb.1, fun g x => by simp [ha.2, hb.2]⟩
  smul_mem' c a ha := ⟨ha.1.const_smul c, fun g x => by simp [ha.2]⟩
def hd {V X : Type u} [AddCommGroup V] (n : ℕ) (F : (Fin (n + 1) → X) → V) (x : Fin (n + 2) → X) : V :=
  ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • F fun j => x (i.succAbove j)
def IsHomog (M : TRep R G) (X : Type u) [TopologicalSpace X] [MulAction G X] (A : Cx R)
    (e : ∀ n, A.X n ≃ₗ[R] hcoch M X n) : Prop :=
  ∀ n a, (e (n + 1) (A.d n a)).1 = hd n (e n a).1
def HomogExistsStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (M : TRep R G) (X : Type u) [TopologicalSpace X] [MulAction G X],
  ∃ A e, IsHomog M X A e
def HomogIsoStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (M : TRep R G), ∃ e, IsHomog M G M.coch e ∧
    (∀ n f x, (e n f).1 x = M.rho (x 0) (f.1 fun i => (x i.castSucc)⁻¹ * x i.succ)) ∧
    ∀ n f g, f.1 g = (e n f).1 (Fin.partialProd g)
def PrismStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (M : TRep R G) (X Y : Type u) [TopologicalSpace X] [MulAction G X]
  [TopologicalSpace Y] [MulAction G Y] (A B : Cx R) eA eB, IsHomog M X A eA → IsHomog M Y B eB →
  (∀ a : X → Y, Continuous a → (∀ (g : G) x, a (g • x) = g • a x) →
    ∃ φ : Hom B A, ∀ n F x, (eA n (φ.f n F)).1 x = (eB n F).1 fun i => a (x i)) ∧
  ∀ (a b : X → Y) (φ ψ : Hom B A), Continuous a → Continuous b → (∀ (g : G) x, a (g • x) = g • a x) →
    (∀ (g : G) x, b (g • x) = g • b x) → (∀ n F x, (eA n (φ.f n F)).1 x = (eB n F).1 fun i => a (x i)) →
    (∀ n F x, (eA n (ψ.f n F)).1 x = (eB n F).1 fun i => b (x i)) → ∀ n, φ.H n = ψ.H n
def ReverseStatement : Prop := ∀ (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (M : TRep R G) (X : Type u) [TopologicalSpace X] [MulAction G X] (A : Cx R) e,
  IsHomog M X A e → ∀ n (a b : A.X n) ha hb,
  (∀ x, (e n b).1 x = (-1 : ℤ) ^ (n * (n + 1) / 2) • (e n a).1 fun i => x i.rev) → A.cls n a ha = A.cls n b hb
end
end ReciprocityTheory.Coh


