-- Prove2me | Definitions.Def_RPLib_S4T_TateProof
-- name    : RPLib_S4T_TateProof
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-16T07:28:13.807991+00:00
-- url     : https://prove2.me/theorems/da24b006-5f10-4e61-94a6-a3629266fd46
-- title:
--   Tate's isogeny theorem over finite fields, prime-to-$p$ form, from Proved FLT-project theorems
-- statement:
--   Tate's isogeny theorem, prime-to-`p` form, from the Proved FLT-project theorems.
--
--   **`tateIsogenyPrimeToP_of_FLT`**: `RPLib.DWS.TateIsogenyPrimeToP.{0}`, conditional only on fifteen Proved
--   prove2.me theorems of the FLT project, each taken as an explicit hypothesis `h_<id8> : FLT.S_<id8>` whose type is
--   the byte-exact platform statement (`scratch/rp/lib/S4T/FLTStmts.lean`; locally those theorems are sorry stubs, so
--   they are never used as lemmas). The chain is `Glue.tate_of_FLT` fed with the five route units:
--   `LiftSetup.l0` (L0), `CMGlue.l2` (L1-L2), `PrimeToP.l5` (L4-L5), `ReduceDescend.l7` (L6-L7), `FFB.l9` (L9).
--
--   **`tate_isogeny_theorem_prime_to_char_of_FLT`**: the same, in the exact shape of the platform leaf 9b26707e
--   (`WeierstrassCurve.tate_isogeny_theorem_prime_to_char`, `F : Type`).
--
--   **Formalization note.** Library module of a formalization of Tate's isogeny theorem over finite fields in prime-to-$p$ form (ordinary elliptic curves with the same number of points are linked by $F$-isogenies $u, w$ with $w \circ u = [N]$, $p \nmid N$, stated through $F$-algebra maps of function fields), via Deuring lifting to characteristic $0$. It is conditional only on fifteen Proved prove2.me theorems of the FLT project, which enter as explicit hypotheses whose types are their exact statements (never as lemmas). Part of a formalization of the Ramanujan-Petersson conjecture in weight two. It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   J. Tate, Endomorphisms of abelian varieties over finite fields, Invent. Math. 2 (1966), 134-144, Theorem 1; M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560, Chapter 4; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Sections III.6-III.7

import Mathlib
import Definitions.Def_RPLib_S4T_LiftSetup
import Definitions.Def_RPLib_S4T_CMGlue
import Definitions.Def_RPLib_S4T_PrimeToP
import Definitions.Def_RPLib_S4T_ReduceDescend
import Definitions.Def_RPLib_S4T_FFBridge

/-!
# S4T-Assembly (route L10): Tate's isogeny theorem, prime-to-`p` form, from the Proved FLT-project theorems

**`tateIsogenyPrimeToP_of_FLT`**: `RPLib.DWS.TateIsogenyPrimeToP.{0}`, conditional only on fifteen Proved
prove2.me theorems of the FLT project, each taken as an explicit hypothesis `h_<id8> : FLT.S_<id8>` whose type is
the byte-exact platform statement (`scratch/rp/lib/S4T/FLTStmts.lean`; locally those theorems are sorry stubs, so
they are never used as lemmas). The chain is `Glue.tate_of_FLT` fed with the five route units:
`LiftSetup.l0` (L0), `CMGlue.l2` (L1-L2), `PrimeToP.l5` (L4-L5), `ReduceDescend.l7` (L6-L7), `FFB.l9` (L9).

**`tate_isogeny_theorem_prime_to_char_of_FLT`**: the same, in the exact shape of the platform leaf 9b26707e
(`WeierstrassCurve.tate_isogeny_theorem_prime_to_char`, `F : Type`).
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace RPLib.S4T.TateProof

/-- **Tate's isogeny theorem, prime-to-`p` form** (`RPLib.DWS.TateIsogenyPrimeToP.{0}`), from the Proved FLT
theorems 0cf211ae (Deuring lifting), 0b434d80 (char-0 CM isogeny), cd49331c (reduction of homs), 7b2524b2
(Frobenius descent), 2bb50ff6 (ordinary ⇒ nonzero `p`-torsion), a78cfa46 (nonzero maps are onto), 0e002459
(lifting prime-to-`p` torsion), bf2cb471 (variable change is additive), 0e8f5714 (dual pair), fe3c6240 /
195173b3 / 580839d4 (composition, sum, negation of rational maps), 094b1237 (commutative End, ordinary),
6256914e (a map killing `X[N]` is divisible by `N`), 97650530 (finitely many rational automorphisms). -/
theorem tateIsogenyPrimeToP_of_FLT
    (h_0cf211ae : FLT.S_0cf211ae) (h_0b434d80 : FLT.S_0b434d80.{0}) (h_cd49331c : FLT.S_cd49331c.{0})
    (h_7b2524b2 : FLT.S_7b2524b2.{0, 0}) (h_2bb50ff6 : FLT.S_2bb50ff6.{0})
    (h_a78cfa46 : FLT.S_a78cfa46.{0, 0}) (h_0e002459 : FLT.S_0e002459.{0})
    (h_bf2cb471 : FLT.S_bf2cb471.{0}) (h_0e8f5714 : FLT.S_0e8f5714.{0, 0})
    (h_fe3c6240 : FLT.S_fe3c6240.{0, 0}) (h_195173b3 : FLT.S_195173b3.{0, 0})
    (h_580839d4 : FLT.S_580839d4.{0, 0}) (h_094b1237 : FLT.S_094b1237.{0})
    (h_6256914e : FLT.S_6256914e.{0, 0}) (h_97650530 : FLT.S_97650530.{0, 0}) :
    RPLib.DWS.TateIsogenyPrimeToP.{0} :=
  Glue.tate_of_FLT h_0cf211ae h_0b434d80 h_cd49331c h_7b2524b2 h_2bb50ff6
    LiftSetup.l0
    (CMGlue.l2 h_a78cfa46 h_0e002459 h_bf2cb471 h_0e8f5714 h_fe3c6240 h_195173b3 h_580839d4)
    (PrimeToP.l5 h_6256914e h_0e8f5714 h_a78cfa46 h_97650530 h_fe3c6240 h_195173b3 h_580839d4)
    (ReduceDescend.l7 h_a78cfa46 h_0e002459 h_bf2cb471 h_0e8f5714 h_fe3c6240 h_195173b3 h_580839d4
      h_094b1237)
    FFB.l9

/-- **Tate's isogeny theorem, prime-to-`p` form, platform shape** (the conclusion of 9b26707e
`WeierstrassCurve.tate_isogeny_theorem_prime_to_char` verbatim), from the same fifteen FLT statements. -/
theorem tate_isogeny_theorem_prime_to_char_of_FLT
    (h_0cf211ae : FLT.S_0cf211ae) (h_0b434d80 : FLT.S_0b434d80.{0}) (h_cd49331c : FLT.S_cd49331c.{0})
    (h_7b2524b2 : FLT.S_7b2524b2.{0, 0}) (h_2bb50ff6 : FLT.S_2bb50ff6.{0})
    (h_a78cfa46 : FLT.S_a78cfa46.{0, 0}) (h_0e002459 : FLT.S_0e002459.{0})
    (h_bf2cb471 : FLT.S_bf2cb471.{0}) (h_0e8f5714 : FLT.S_0e8f5714.{0, 0})
    (h_fe3c6240 : FLT.S_fe3c6240.{0, 0}) (h_195173b3 : FLT.S_195173b3.{0, 0})
    (h_580839d4 : FLT.S_580839d4.{0, 0}) (h_094b1237 : FLT.S_094b1237.{0})
    (h_6256914e : FLT.S_6256914e.{0, 0}) (h_97650530 : FLT.S_97650530.{0, 0})
    (F : Type) [Field F] [Fintype F]
    (W W' : WeierstrassCurve F) [W.IsElliptic] [W'.IsElliptic]
    (hcard : Nat.card W.toAffine.Point = Nat.card W'.toAffine.Point)
    (hord : ¬ ((ringChar F : ℤ) ∣ ((Fintype.card F : ℤ) + 1 - (Nat.card W.toAffine.Point : ℤ)))) :
    ∃ (f : W'.toAffine.FunctionField →ₐ[F] W.toAffine.FunctionField)
      (g : W.toAffine.FunctionField →ₐ[F] W'.toAffine.FunctionField) (N : ℕ), (N : F) ≠ 0 ∧
      ∃ h : (W.baseChange W.toAffine.FunctionField).toAffine.Nonsingular
          (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
            (WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine (Polynomial.C Polynomial.X)))
          (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
            (WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine Polynomial.X)),
        WeierstrassCurve.Affine.Point.map (W' := W.toAffine) (f.comp g)
            (WeierstrassCurve.Affine.Point.some _ _ h) =
          N • WeierstrassCurve.Affine.Point.some _ _ h :=
  tateIsogenyPrimeToP_of_FLT h_0cf211ae h_0b434d80 h_cd49331c h_7b2524b2 h_2bb50ff6 h_a78cfa46 h_0e002459
    h_bf2cb471 h_0e8f5714 h_fe3c6240 h_195173b3 h_580839d4 h_094b1237 h_6256914e h_97650530 F W W' hcard hord

end RPLib.S4T.TateProof


