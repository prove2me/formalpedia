-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsThRule
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_IsThRule
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:51:16.509441+00:00
-- url     : https://prove2.me/theorems/d70fafe4-09dc-4f91-af46-bba5f1ac1153
-- title:
--   Is Th Rule
-- statement:
--   Definitions and structural lemmas for Is Th Rule, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/IsThRule.lean

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsCombAt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RowDeg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Mathlib.RingTheory.RingHom.FaithfullyFlat
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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)
abbrev Lt1 (Dw : Datum H) : Type := Σ τ : E →+* ℂ, Fin (Dw.mult τ)
abbrev ptO {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) : Over Xo.X := Over.mk x
abbrev NabV : Type 1 :=
  ∀ {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (k : ℤ),
    LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x)) → (Lt1 Dw →₀ ℕ) → S
section Vt
variable {X : Scheme.{0}} (A : Over X) [GrpObj A] [IsCommMonObj A] (L : RigLB A)
def IsVtOver (N : ℕ) {T : Over X} (ok : (T ⟶ A) → Prop) (s : LB.Sec (LPow A L.L 1 T)) (t : T ⟶ A)
    (F : LB.Sec (LPow A L.L ((N : ℤ) ^ 2) T)) : Prop :=
  ∃ (t' : T ⟶ A)
    (α₀ : LB.Gen (LB.LinComb L.L (K := Fin 2) ![𝟙 A.left, (mulA A N).left] ![(N : ℤ) ^ 2, -1]))
    (α : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(snd T A).left, (snd T A ^ N).left] ![(N : ℤ) ^ 2, -1]))
    (s₁ : LB.Sec (LPow A L.L ((N : ℤ) ^ 2) T)) (U : ThetaGrp A L.L ((N : ℤ) ^ 2) T),
    t' ^ N = t ∧ ok t' ∧ α₀.IsGen ∧ IsNormMul A L.L L.rig N α₀ ∧
    LB.Gen.Corr L.L _ _ _ _ α (LB.pullGen L.L _ _ α₀ (snd T A).left) ∧
    IsTwistPull A L.L (mulT A T N) (snd T A ^ N) (lift_snd _ _) ((N : ℤ) ^ 2) 1 α s s₁ ∧
    SymLift A L.L ((N : ℤ) ^ 2) (N ^ 2) t' U ∧ IsActOf A L.L ((N : ℤ) ^ 2) U s₁ F
def IsTFrame (N : ℕ) {T : Over X} (t' : T ⟶ A)
    (e : LB.Gen (LB.LinComb L.L (Y := T.left) (K := Fin 1) (fun _ => (t' ^ N).left) (fun _ => 1))) : Prop :=
  e.IsGen ∧ ∃ (α₀ : LB.Gen (LB.LinComb L.L (K := Fin 2) ![𝟙 A.left, (mulA A N).left] ![(N : ℤ) ^ 2, -1]))
    (U : ThetaGrp A L.L ((N : ℤ) ^ 2) T)
    (τ : LB.Gen (LB.LinComb L.L (Y := T.left) (K := Fin 1) (fun _ => U.pt.left) (fun _ => (N : ℤ) ^ 2))),
    α₀.IsGen ∧ IsNormMul A L.L L.rig N α₀ ∧ SymLift A L.L ((N : ℤ) ^ 2) (N ^ 2) t' U ∧
    LB.Gen.Corr L.L _ _ _ _ τ (LB.mulGen L.L _ _ _ _ (LB.pullGen L.L _ _ α₀ t'.left) e) ∧
    LB.Gen.Corr L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (LB.pullGen L.L _ _ U.φ (ptSecT A 1).left) τ)
      (rigT A L.L L.rig T ((N : ℤ) ^ 2))
end Vt
abbrev LtN (Dw : Datum H) (n : ℕ) : Type := Letter (E →+* ℂ) Dw.mult n
def colOf {n : ℕ} (m : LtN Dw n →₀ ℕ) (b : Fin n) : Lt1 Dw →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun ℓ => m ⟨ℓ.1, ℓ.2, b⟩
def levPt {S : Type} [CommRing S] (x0 : Sp S ⟶ Xo.X) (x : Dw.La) : ptO Xo x0 ⟶ Xo.univ.t.G :=
  toUnit _ ≫ Xo.univ.eta x
def KilledBy (I : Ideal (𝓞 E)) {T : Over Xo.X} (t' : T ⟶ Xo.univ.t.G) : Prop :=
  ∀ a ∈ I, t' ≫ Xo.univ.t.act.act a = 1
def thExpr (nab : NabV Xo c) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) {n : ℕ}
    (P : MvPolynomial (LtN Dw n) c.F)
    (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2) (ptO Xo y.x))) : S :=
  algebraMap c.F S (((l.M : c.F) ^ P.totalDegree)⁻¹) *
    ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, nab y ((l.M : ℤ) ^ 2) (F b) (colOf m b)
def ThValAt (nab : NabV Xo c) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) {n : ℕ}
    (x : Fin n → Dw.La) (P : MvPolynomial (LtN Dw n) c.F) (v : S) : Prop :=
  ∃ (S' : Type) (_ : CommRing S') (_ : Algebra c.F S') (φ : S →ₐ[c.F] S') (y' : FrPt Xo c S')
    (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2) (ptO Xo y'.x))),
    φ.toRingHom.FaithfullyFlat ∧ FrMap φ y y' ∧
    (∀ b, IsVtOver Xo.univ.t.G Xo.univ.t.PP l.M (KilledBy Xo (l.Mb ^ 2)) y'.s (levPt Xo y'.x (x b)) (F b)) ∧
    φ v = thExpr Xo c nab y' P F
def IsThRule (nab : NabV Xo c) {n : ℕ} (x : Fin n → Dw.La) (P : MvPolynomial (LtN Dw n) c.F)
    (f : Rul Xo c) : Prop :=
  ∀ (p : TRing c.F) (y : FrPt Xo c p.R), ThValAt Xo c nab y x P (f p y)
def InPsi (H : Host E) (τ : E →+* ℂ) : Prop := τ (H.rt : E) = H.rt0
def harmA (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Set (MvPolynomial (LtN Dw n) c.F) :=
  HaO Dw.mult n c.F (integralClosure ℤ c.F).toSubring ComplexEmbedding.conjugate (InPsi H) fun τ i => a (τ, i)
def thGen (nab : NabV Xo c) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Set (Rul Xo c) :=
  {f | ∃ (x : Fin n → Dw.La) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n ∧
    IsThRule Xo c nab x P f}
end Formalism.L2.Pj


