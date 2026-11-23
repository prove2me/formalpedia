-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameProofs
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_FrameProofs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T09:54:30.635124+00:00
-- url     : https://prove2.me/theorems/9f1a09e9-b464-4d1a-8c16-22c6de7ed398
-- title:
--   Frame Proofs
-- statement:
--   Definitions and structural lemmas for Frame Proofs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/FrameProofs.lean

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CoreProofs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
section Open
variable (Xo : Moduli Dw l) (c : Coeff l)
def BorDesc : Prop :=
  ∀ (S : Type) [Field S] [Algebra c.F S] (t : Ix Dw → Sˣ) (y y' : FrPt Xo c S), FrBor t y y' →
    ∀ (p q : TRing c.F) (φ : p.R →ₐ[c.F] S) (ψ : q.R →ₐ[c.F] S) (yp : FrPt Xo c p.R) (yq : FrPt Xo c q.R),
      FrMap φ yp y → FrMap ψ yq y' →
      ∃ (r : TRing c.F) (α : p.R →ₐ[c.F] r.R) (β : q.R →ₐ[c.F] r.R) (χ : r.R →ₐ[c.F] S)
        (z z' : FrPt Xo c r.R) (t₀ : Ix Dw → (r.R)ˣ),
        χ.comp α = φ ∧ χ.comp β = ψ ∧ FrMap α yp z ∧ FrMap β yq z' ∧ FrBor t₀ z z' ∧
          ∀ i, χ (t₀ i : r.R) = (t i : S)
def IntLatU : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y y' : IntFr Xo c T io), letI := io.toAlgebra; y'.1.x = y.1.x →
    (∀ τ : E →+* ℂ, ∃ A : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) T.V, IsUnit A.det ∧
      ∀ i, IsCombAt y.1.x (y.1.u τ) (fun j => algebraMap T.V T.Fr (A i j)) (y'.1.u τ i)) ∧
    ∀ (a : T.Frˣ) (pm : Gx y'.1.x ⟶ Gx y.1.x),
      pm ≫ (CartesianMonoidalCategory.snd (Over.mk y.1.x) Xo.univ.t.G).left =
          (CartesianMonoidalCategory.snd (Over.mk y'.1.x) Xo.univ.t.G).left →
      pm ≫ (CartesianMonoidalCategory.fst (Over.mk y.1.x) Xo.univ.t.G).left =
          (CartesianMonoidalCategory.fst (Over.mk y'.1.x) Xo.univ.t.G).left →
      (∀ (i : Fin 1 → Xo.univ.t.PP.L.ι) (h : (PPx y'.1.x).U i ≤ pm ⁻¹ᵁ (PPx y.1.x).U i),
        (pm.appLE _ _ h).hom (scal y.1.x (a : T.Fr) i * y.1.s.f i) = y'.1.s.f i) →
      valV T.V (a : T.Fr) = 1
end Open
section Proofs
variable {Xo : Moduli Dw l} {c : Coeff l}
end Proofs
end Formalism.L2.Pj


