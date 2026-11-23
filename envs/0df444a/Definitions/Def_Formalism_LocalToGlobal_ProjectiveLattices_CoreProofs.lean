-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CoreProofs
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_CoreProofs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T09:52:09.017395+00:00
-- url     : https://prove2.me/theorems/b63ed637-069f-4ea9-a41a-570d585ee016
-- title:
--   Core Proofs
-- statement:
--   Definitions and structural lemmas for Core Proofs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CoreProofs.lean

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_VAtVNeBot
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
def WtField : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), f ∈ sec Xo c a n →
    ∀ (S : Type) [Field S] [Algebra c.F S] (t : Ix Dw → Sˣ) (y y' : FrPt Xo c S),
      FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y →
      FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y' →
      FrBor t y y' → evR Xo c f y' = wchar (ex Dw a n) t * evR Xo c f y
def IntDiagUnit : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y y' : IntFr Xo c T io) (t : Ix Dw → T.Frˣ),
    (letI := io.toAlgebra; FrBor t y.1 y'.1) → ∀ i, valV T.V ((t i : T.Frˣ) : T.Fr) = 1
def AlgPtLa : Prop :=
  ∀ la : HeightOneSpectrum (𝓞 c.F), ∃ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (_ : OverLa la T.V io e),
    T.FinRes ∧ ∃ x : Sp T.Fr ⟶ Xo.X, (letI := io.toAlgebra; x ≫ Xo.s = sOf c T.Fr)
def IntFrExt : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr), T.FinRes → ∀ x : Sp T.Fr ⟶ Xo.X, (letI := io.toAlgebra; x ≫ Xo.s = sOf c T.Fr) →
    ∃ (T' : CDVR) (i : T.Fr →+* T'.Fr) (r : ℕ), 0 < r ∧ (∀ z, vV T'.V (i z) = (r : ℤ) * vV T.V z) ∧ T'.FinRes ∧
      ∃ y : IntFr Xo c T' (i.comp io), (letI := (i.comp io).toAlgebra; y.1.x = spMap i ≫ x)
end Open
section Proofs
variable {Xo : Moduli Dw l} {c : Coeff l}
end Proofs
end Formalism.L2.Pj


