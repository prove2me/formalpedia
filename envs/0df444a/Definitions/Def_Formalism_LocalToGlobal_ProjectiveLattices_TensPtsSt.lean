-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_TensPtsSt
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_TensPtsSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:38:24.627925+00:00
-- url     : https://prove2.me/theorems/63ebcf17-0148-4371-902a-a1895a902f23
-- title:
--   Tens Pts St
-- statement:
--   Definitions and structural lemmas for Tens Pts St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/TensPtsSt.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
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
namespace Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
variable {X : Scheme.{0}} (A : Over X)
def powO : ℕ → Over X
  | 0 => 𝟙_ (Over X)
  | k + 1 => A ⊗ powO k
def prj : (k : ℕ) → Fin k → (powO A k ⟶ A)
  | 0, j => j.elim0
  | k + 1, j => Fin.cases (fst A (powO A k)) (fun j' => snd A (powO A k) ≫ prj k j') j
def tup {T : Over X} : (k : ℕ) → (Fin k → (T ⟶ A)) → (T ⟶ powO A k)
  | 0, _ => toUnit T
  | k + 1, a => lift (a 0) (tup k fun j => a j.succ)
variable [GrpObj A] [IsCommMonObj A] {O : Type} [CommRing O] (act : OAct O A)
structure DualPres (O : Type) [CommRing O] (La : Type) [AddCommGroup La] [Module O La] where

  k : ℕ

  gen : Fin k → La

  coord : Fin k → Module.Dual O La

  recon : ∀ x, (∑ j, coord j x • gen j) = x
def DualPres.e {La : Type} [AddCommGroup La] [Module O La] (D : DualPres O La) (i j : Fin D.k) : O :=
  D.coord i (D.gen j)
def matMap {k : ℕ} (e : Fin k → Fin k → O) : powO A k ⟶ powO A k :=
  tup A k fun i => psum A (fun j => prj A k j ≫ act.act (e i j)) Finset.univ
abbrev tensSch {k : ℕ} (e : Fin k → Fin k → O) : Scheme.{0} :=
  pullback (lift (matMap A act e) (𝟙 (powO A k))).left (lift (𝟙 (powO A k)) (𝟙 (powO A k))).left
def tensO {k : ℕ} (e : Fin k → Fin k → O) : Over X :=
  Over.mk (pullback.fst _ _ ≫ (powO A k).hom : tensSch A act e ⟶ X)
def tensIncl {k : ℕ} (e : Fin k → Fin k → O) : tensO A act e ⟶ powO A k :=
  Over.homMk (pullback.fst _ _) rfl
def tcoord {k : ℕ} (e : Fin k → Fin k → O) (j : Fin k) : tensO A act e ⟶ A :=
  tensIncl A act e ≫ prj A k j
def IsTensPt {k : ℕ} (e : Fin k → Fin k → O) {T : Over X} (a : Fin k → (T ⟶ A)) : Prop :=
  ∀ i, psum A (fun j => a j ≫ act.act (e i j)) Finset.univ = a i
def TensPtsSt {k : ℕ} (e : Fin k → Fin k → O) : Prop :=
  ∀ (T : Over X),
    (∀ b : T ⟶ tensO A act e, IsTensPt A act e fun j => b ≫ tcoord A act e j) ∧
    ∀ a : Fin k → (T ⟶ A), IsTensPt A act e a → ∃! b : T ⟶ tensO A act e, ∀ j, b ≫ tcoord A act e j = a j
abbrev tensIx {k : ℕ} (h : Fin k → Fin k → O) : Type :=
  {p : Fin k × Fin k // h p.1 p.2 ≠ 0} × ULift.{0} (Finset (Fin 2))
open Classical in
instance {k : ℕ} (h : Fin k → Fin k → O) : Fintype (tensIx h) :=
  inferInstanceAs (Fintype ({p : Fin k × Fin k // h p.1 p.2 ≠ 0} × ULift.{0} (Finset (Fin 2))))
def tensφ {k : ℕ} (e : Fin k → Fin k → O) (h : Fin k → Fin k → O) (w0 : O) :
    tensIx h → ((tensO A act e).left ⟶ A.left) :=
  fun q => (psum A ![tcoord A act e q.1.1.1, tcoord A act e q.1.1.2 ≫ act.act (h q.1.1.1 q.1.1.2 * w0)]
    q.2.down).left
def tensε {k : ℕ} (h : Fin k → Fin k → O) : tensIx h → ℤ := fun q => (-1) ^ (2 - q.2.down.card)
def tensLB (PP : RigLB A) {k : ℕ} (e : Fin k → Fin k → O) (h : Fin k → Fin k → O) (w0 : O) :
    LB (tensO A act e).left :=
  LB.LinComb PP.L (tensφ A act e h w0) (tensε h)
def tensOf {La : Type} [AddCommGroup La] [Module O La] (D : DualPres O La) : Over X :=
  tensO A act D.e
def tensLBOf (PP : RigLB A) {La : Type} [AddCommGroup La] [Module O La] (D : DualPres O La)
    (hf : La → La → O) (w0 : O) : LB (tensOf A act D).left :=
  tensLB A act PP D.e (fun j j' => hf (D.gen j) (D.gen j')) w0
end Formalism.L2.Pj


