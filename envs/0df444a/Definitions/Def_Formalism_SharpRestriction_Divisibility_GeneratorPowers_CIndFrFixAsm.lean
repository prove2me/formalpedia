-- Prove2me | Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndFrFixAsm
-- name    : Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndFrFixAsm
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T15:12:13.057954+00:00
-- url     : https://prove2.me/theorems/8a1edb3f-2873-4b14-affc-59bb125aebbb
-- title:
--   CInd Fr Fix Asm
-- statement:
--   Definitions and structural lemmas for CInd Fr Fix Asm, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/CIndFrFixAsm.lean

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_IsUnitCoeffZero
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ConstantCoeffAddFirstSecond
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndFrFix
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
namespace Formalism.MainNotions.ModuliIntegralCharts.H1
open AlgebraicGeometry CategoryTheory Limits NumberField MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
  Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix
open ReciprocityTheory.ChartRestriction.G.TB (dLin)
def FrRatioSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
    ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S) (C : ChartAt Xo c y) (m : ℕ),
    ∃ U : (Jet S (Fin 2 × Fin C.d) m)ˣ,
      LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
        (LB.pullGen Xo.univ.t.PP.L _ _ (C.e (m + 1))
          (homAt y.x (jetTrunc : Jet S (Fin 2 × Fin C.d) (m + 1) →ₐ[S] Jet S (Fin 2 × Fin C.d) m)).left)
        (scaleGen (Xo := Xo) _ _ (unitΓ U) (C.e m)) ∧
      jetSubstP m (fun p : Fin 2 × Fin C.d =>
          (![fun j => psIn C.d m (![0, 1] : Fin 2 → Fin 3) (C.B.G.F j), fun j => X ((2 : Fin 3), j)] :
            Fin 2 → Fin C.d → MvPolynomial (Fin 3 × Fin C.d) S) p.1 p.2) (U : Jet S (Fin 2 × Fin C.d) m) =
        jetSubstP m (fun p : Fin 2 × Fin C.d => (![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)] :
            Fin 2 → Fin C.d → MvPolynomial (Fin 3 × Fin C.d) S) p.1 p.2) (U : Jet S (Fin 2 × Fin C.d) m) *
        jetSubstP m (fun p : Fin 2 × Fin C.d => (![fun j => X ((1 : Fin 3), j), fun j => X ((2 : Fin 3), j)] :
            Fin 2 → Fin C.d → MvPolynomial (Fin 3 × Fin C.d) S) p.1 p.2) (U : Jet S (Fin 2 × Fin C.d) m) ∧
      jetSubstP m (fun p : Fin 2 × Fin C.d => (![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)] :
          Fin 2 → Fin C.d → MvPolynomial (Fin 2 × Fin C.d) S) p.1 p.2) (U : Jet S (Fin 2 × Fin C.d) m) = U ∧
      ∀ a : 𝓞 E, jetSubstP m (fun p : Fin 2 × Fin C.d =>
          (![fun j => psIn C.d m ![0] (C.B.A.act a j), fun j => X ((1 : Fin 2), j)] :
            Fin 2 → Fin C.d → MvPolynomial (Fin 2 × Fin C.d) S) p.1 p.2) (U : Jet S (Fin 2 × Fin C.d) m) =
        jetSubstP m (fun p : Fin 2 × Fin C.d =>
          (![fun j => X ((0 : Fin 2), j), fun j => psIn C.d m ![1] (C.B.A.act (H.bar a) j)] :
            Fin 2 → Fin C.d → MvPolynomial (Fin 2 × Fin C.d) S) p.1 p.2) (U : Jet S (Fin 2 × Fin C.d) m)
def ccOf {S : Type} [CommRing S] {d : ℕ} (cm : ℕ → Fin d → Fin d → S) : ℕ → Fin d → Fin d → S
  | 0 => 0
  | m + 1 => ccOf cm m - cm m
end Formalism.MainNotions.ModuliIntegralCharts.H1


