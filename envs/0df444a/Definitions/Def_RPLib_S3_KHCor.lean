-- Prove2me | Definitions.Def_RPLib_S3_KHCor
-- name    : RPLib_S3_KHCor
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T19:17:56.829528+00:00
-- url     : https://prove2.me/theorems/6d14c4c3-25f2-491a-af09-34d8e9327e95
-- title:
--   Ramanujan-Petersson in weight two for every level and character, conditional on Tate's isogeny theorem
-- statement:
--   S3-KH corollaries: the weight-2 results without `hKH`.
--
--   `kroneckerHurwitz` (KroneckerHurwitz.lean) discharges the hypothesis `hKH : KroneckerHurwitz` of
--   `DWSO.dwsOrdinary`, `Match.identityI'`, `Match.identityI'_j`, `Wt2.phiEigenBound_two` and
--   `Wt2.deligne_hecke_root_bound_wt2`; the primed versions below take only `hT : TateIsogenyPrimeToP`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   Y. Ihara, Hecke polynomials as congruence zeta functions in elliptic modular case, Ann. of Math. 85 (1967), 267-295; M. Eichler, Quaternäre quadratische Formen und die Riemannsche Vermutung für die Kongruenzzetafunktion, Arch. Math. 5 (1954), 355-366; G. Shimura, Introduction to the Arithmetic Theory of Automorphic Functions, Princeton 1971, Chapter 7; M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211

import Mathlib
import Definitions.Def_RPLib_S3_KroneckerHurwitz
import Definitions.Def_RPLib_S3_Wt2RP

/-!
# S3-KH corollaries: the weight-2 results without `hKH`

`kroneckerHurwitz` (KroneckerHurwitz.lean) discharges the hypothesis `hKH : KroneckerHurwitz` of
`DWSO.dwsOrdinary`, `Match.identityI'`, `Match.identityI'_j`, `Wt2.phiEigenBound_two` and
`Wt2.deligne_hecke_root_bound_wt2`; the primed versions below take only `hT : TateIsogenyPrimeToP`.
-/

set_option autoImplicit false

open UpperHalfPlane ModularForm CongruenceSubgroup MatrixGroups

namespace RamanujanPetersson.S3.KH

open RamanujanPetersson.S3

/-- **DWSOrdinary**, conditional on `TateIsogenyPrimeToP` only. -/
theorem dwsOrdinary' (hT : RPLib.DWS.TateIsogenyPrimeToP.{0}) : DWSOrdinary :=
  DWSO.dwsOrdinary hT kroneckerHurwitz

/-- **Identity (I')**, conditional on `TateIsogenyPrimeToP` only. -/
theorem identityI'' (hT : RPLib.DWS.TateIsogenyPrimeToP.{0}) : IdentityI' :=
  Match.identityI' hT kroneckerHurwitz

/-- **Identity (I') over `j ∉ {0, 1728}`**, conditional on `TateIsogenyPrimeToP` only. -/
theorem identityI'_j' (hT : RPLib.DWS.TateIsogenyPrimeToP.{0}) : IdentityI'_j :=
  Match.identityI'_j hT kroneckerHurwitz

/-- **Weight-2 eigenvalue bound for `Φ`**, conditional on `TateIsogenyPrimeToP` only. -/
theorem phiEigenBound_two' (hT : RPLib.DWS.TateIsogenyPrimeToP.{0}) : PhiEigenBound 2 :=
  Wt2.phiEigenBound_two hT kroneckerHurwitz

/-- **Ramanujan-Petersson in weight 2**, conditional on `TateIsogenyPrimeToP` only: every root of the Hecke
polynomial `X² - b(p) X + χ(p) p` of a normalized eigenform `F ∈ S_2(Γ₁(L), χ)` at `p ∤ L` has `|α| ≤ √p`. -/
theorem deligne_hecke_root_bound_wt2' (hT : RPLib.DWS.TateIsogenyPrimeToP.{0})
    (L : ℕ) (hL : 0 < L)
    (χ : DirichletCharacter ℂ L)
    (F : CuspForm ((CongruenceSubgroup.Gamma1 L : Subgroup SL(2, ℤ)) :
      Subgroup (GL (Fin 2) ℝ)) 2)
    (hχ : ∀ γ ∈ CongruenceSubgroup.Gamma0 L, (⇑F ∣[(2 : ℤ)] γ) = χ ((γ 1 1 : ℤ) : ZMod L) • ⇑F)
    (h1 : (qExpansion 1 F).coeff 1 = 1)
    (hrec : ∀ q n : ℕ, q.Prime → ¬ q ∣ L →
      (qExpansion 1 F).coeff (q * n) =
        (qExpansion 1 F).coeff q * (qExpansion 1 F).coeff n -
          χ (q : ZMod L) * (q : ℂ) ^ ((2 : ℤ) - 1) *
            (if q ∣ n then (qExpansion 1 F).coeff (n / q) else 0))
    (p : ℕ) (hp : p.Prime) (hpL : ¬ p ∣ L) (α : ℂ)
    (hα : α ^ 2 - (qExpansion 1 F).coeff p * α + χ (p : ZMod L) * (p : ℂ) ^ ((2 : ℤ) - 1) = 0) :
    ‖α‖ ≤ (p : ℝ) ^ ((((2 : ℤ) : ℝ) - 1) / 2) :=
  Wt2.deligne_hecke_root_bound_wt2 hT kroneckerHurwitz L hL χ F hχ h1 hrec p hp hpL α hα

end RamanujanPetersson.S3.KH


