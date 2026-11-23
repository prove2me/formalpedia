-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntAllProofFree
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_IntAllProofFree
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:42:16.40084+00:00
-- url     : https://prove2.me/theorems/9d246073-3fcc-4456-8112-93dcd204a9f4
-- title:
--   Int All Proof Free
-- statement:
--   Definitions and structural lemmas for Int All Proof Free, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/IntAllProofFree.lean

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CoreProofs
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntAllFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ExistsOfValILeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.PjFree
open Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open scoped WithZero
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
section Dvr
variable {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K'] [Algebra V K']
  [IsFractionRing V K']
end Dvr
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
section Open
variable (Xo : Moduli Dw l) (c : Coeff l)
def FrBaseChg : Prop :=
  ∀ (S S' : Type) [Field S] [Field S'] [Algebra c.F S] [Algebra c.F S'] (φ : S →ₐ[c.F] S') (y : FrPt Xo c S),
    ∃ z : FrPt Xo c S', FrMap φ y z
def ReFrame : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr), letI := io.toAlgebra
    ∀ (y0 : IntFr Xo c T io) (z : FrPt Xo c T.Fr), z.x = y0.1.x →
      ∃ (t : Ix Dw → T.Frˣ) (y' : IntFr Xo c T io), FrBor t z y'.1
def XoNumPt : Prop :=
  ∃ (L : Type) (_ : Field L) (_ : NumberField L) (j : c.F →+* L) (x : Sp L ⟶ Xo.X),
    (letI := j.toAlgebra; x ≫ Xo.s = sOf c L)
end Open
def LocFld : Prop :=
  ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] (j : K →+* L) (la : HeightOneSpectrum (𝓞 K)),
    ∃ (T : CDVR) (k : L →+* T.Fr) (e : ℕ), OverLa la T.V (k.comp j) e ∧ T.FinRes
section Proofs
variable {Xo : Moduli Dw l} {c : Coeff l}
end Proofs
section Frames
theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl
theorem epsMul_comp_alg {S : Type} [CommRing S] (a : S) :
    (epsMul a).comp (algebraMap S (DualNumber S)) = algebraMap S (DualNumber S) := by
  ext x <;> simp [epsMul]
def epsPt {S : Type} [CommRing S] {Xo : Moduli Dw l} {x : Sp S ⟶ Xo.X}
    {v : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (hv : IsTanAt x v) (a : S) : tEps x ⟶ Xo.univ.t.G :=
  Over.homMk (spMap (epsMul a) ≫ v) (by
    rw [Category.assoc, hv.1, ← Category.assoc, spMap_comp', epsMul_comp_alg]
    rfl)
variable (Xo : Moduli Dw l) (c : Coeff l)
def TanLin : Prop :=
  ∀ (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) {m : ℕ} (v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)),
    (∀ j, IsTanAt x (v j)) →
      ∀ {m' : ℕ} (w : Fin m' → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)) (A : Matrix (Fin m) (Fin m') S)
        (N : Fin m' → S) (w' : Sp (DualNumber S) ⟶ Xo.univ.t.G.left),
        (∀ i, IsCombAt x v (fun j => A j i) (w i)) → IsCombAt x w N w' → IsCombAt x v (A.mulVec N) w'
variable {Xo c} in

def SClause {S : Type} [CommRing S] [Algebra c.F S] (a : S) (y y' : FrPt Xo c S) : Prop :=
  ∃ pm : Gx y'.x ⟶ Gx y.x, pm ≫ (snd (Over.mk y.x) Xo.univ.t.G).left = (snd (Over.mk y'.x) Xo.univ.t.G).left ∧
    pm ≫ (fst (Over.mk y.x) Xo.univ.t.G).left = (fst (Over.mk y'.x) Xo.univ.t.G).left ∧
    ∀ (i : Fin 1 → Xo.univ.t.PP.L.ι) (h : (PPx y'.x).U i ≤ pm ⁻¹ᵁ (PPx y.x).U i),
      (pm.appLE _ _ h).hom (scal y.x a i * y.s.f i) = y'.s.f i
def IntRebase : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr), letI := io.toAlgebra
    ∀ (y0 : IntFr Xo c T io) (z : FrPt Xo c T.Fr), z.x = y0.1.x →
      ∀ k : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) T.V, (∀ τ, IsUnit (k τ).det) →
        ∃ (y'' : IntFr Xo c T io) (t0 : T.Frˣ), y''.1.x = z.x ∧
          (∀ τ i, IsCombAt y0.1.x (y0.1.u τ) (fun j => algebraMap T.V T.Fr (k τ j i)) (y''.1.u τ i)) ∧
          SClause (t0 : T.Fr) z y''.1
variable {Xo c}
end Frames
end Formalism.L2.PjFree


