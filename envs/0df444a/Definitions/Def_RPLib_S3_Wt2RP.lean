-- Prove2me | Definitions.Def_RPLib_S3_Wt2RP
-- name    : RPLib_S3_Wt2RP
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T18:37:45.697835+00:00
-- url     : https://prove2.me/theorems/acdbe36c-5ef0-4fa1-b7b4-a77843df0dc4
-- title:
--   Weight-two Ramanujan-Petersson library: Ramanujan-Petersson for weight 2 on `Γ₁(L)`, all characters
-- statement:
--   Ramanujan-Petersson for weight 2 on `Γ₁(L)`, all characters.
--
--   Conditional on the two hypotheses of S3-Matching: `hT : TateIsogenyPrimeToP` (Tate's isogeny theorem for prime-to-`p`
--   torsion, see `units/S3-DWS-Tate/NOTES.md`) and `hKH : KroneckerHurwitz`.
--
--   * **`phiEigenBound_two`**: every eigenvalue of `Φ = [[T_p, -p⟨p⟩], [1, 0]]` on `S_2(Γ₁(M))² ` (`M ≥ 4`, `p ∤ M`)
--     has modulus at most `√p`. Proof: Identity (I') at `k = 2`, the point count of `Y₁(M)`,
--     Hasse-Weil for an arbitrary constant field (`hw_general`, from S3-ZetaSB), and the power-sum growth lemma; see `Wt2RP_C`.
--   * **`deligne_hecke_root_bound_wt2`**: N4 (`scratch/decomp/3c5fc8a7/spec_N4.json`) at `k = 2`, for every level `L > 0`
--     (`Wt2RP_A`, level raising).
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   Y. Ihara, Hecke polynomials as congruence zeta functions in elliptic modular case, Ann. of Math. 85 (1967), 267-295; M. Eichler, Quaternäre quadratische Formen und die Riemannsche Vermutung für die Kongruenzzetafunktion, Arch. Math. 5 (1954), 355-366; G. Shimura, Introduction to the Arithmetic Theory of Automorphic Functions, Princeton 1971, Chapter 7; M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211

import Mathlib
import Definitions.Def_RPLib_S3_Wt2RPA
import Definitions.Def_RPLib_S3_Wt2RPC
import Definitions.Def_RPLib_S3_Matching

/-!
# Ramanujan-Petersson for weight 2 on `Γ₁(L)`, all characters (unit S3-Wt2RP, goal file)

Conditional on the two hypotheses of S3-Matching: `hT : TateIsogenyPrimeToP` (Tate's isogeny theorem for prime-to-`p`
torsion, see `units/S3-DWS-Tate/NOTES.md`) and `hKH : KroneckerHurwitz`.

* **`phiEigenBound_two`**: every eigenvalue of `Φ = [[T_p, -p⟨p⟩], [1, 0]]` on `S_2(Γ₁(M))² ` (`M ≥ 4`, `p ∤ M`)
  has modulus at most `√p`. Proof: Identity (I') at `k = 2` (S3-Matching), the point count of `Y₁(M)` (S3-X1Count),
  Hasse-Weil for an arbitrary constant field (`hw_general`, from S3-ZetaSB), and the power-sum growth lemma
  (S3-ExpSum); see `Wt2RP_C`.
* **`deligne_hecke_root_bound_wt2`**: N4 (`scratch/decomp/3c5fc8a7/spec_N4.json`) at `k = 2`, for every level `L > 0`
  (`Wt2RP_A`, level raising).
-/

set_option autoImplicit false

open UpperHalfPlane ModularForm CongruenceSubgroup MatrixGroups

namespace RamanujanPetersson.S3.Wt2

/-- **Weight-2 eigenvalue bound for `Φ`** (conditional on `hT`, `hKH`). -/
theorem phiEigenBound_two (hT : RPLib.DWS.TateIsogenyPrimeToP.{0}) (hKH : KroneckerHurwitz) : PhiEigenBound 2 :=
  phiEigenBound_two_of (Match.identityI' hT hKH)

/-- **Ramanujan-Petersson in weight 2** (N4 at `k = 2`; conditional on `hT`, `hKH`): every root of the Hecke
polynomial `X² - b(p) X + χ(p) p` of a normalized eigenform `F ∈ S_2(Γ₁(L), χ)` at `p ∤ L` has `|α| ≤ √p`. -/
theorem deligne_hecke_root_bound_wt2 (hT : RPLib.DWS.TateIsogenyPrimeToP.{0}) (hKH : KroneckerHurwitz)
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
  n4_of_phiEigenBound 2 (by norm_num) (phiEigenBound_two hT hKH) L hL χ F hχ h1 hrec p hp hpL α hα

end RamanujanPetersson.S3.Wt2


