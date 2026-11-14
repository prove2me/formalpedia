-- Prove2me | Definitions.Def_RPLib_S4_JacDivisorsE
-- name    : RPLib_S4_JacDivisorsE
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-13T19:20:11.091947+00:00
-- url     : https://prove2.me/theorems/bd2a631c-4ab3-4dff-b4a1-2e22844aabb0
-- title:
--   Localizations of regular local rings at primes are regular local
-- statement:
--   Let $R$ be a regular local ring and $\mathfrak p \subset R$ a prime ideal. The file constructs the isomorphism of $R_{\mathfrak p}$-modules $$(R/\mathfrak p)_{\mathfrak p} \cong R_{\mathfrak p}/\mathfrak p R_{\mathfrak p}$$ and proves that the localization $R_{\mathfrak p}$ is again a regular local ring. This is the step that makes regularity a local property on $\operatorname{Spec} R$ (Serre).
--
--   **Formalization note.** This file is a library module (namespace `RamanujanPetersson.JacDivisors`) of a formalization of the Ramanujan-Petersson conjecture; it is the regular-local-ring part of that library. It contains definitions together with proved lemmas (no `sorry`), stated with Mathlib's `IsRegularLocalRing`, `Ideal.spanFinrank` and the categorical `HasProjectiveDimensionLT` on `ModuleCat`, so that later solution files can import them.
-- source:
--   H. Matsumura, Commutative Ring Theory, Cambridge Stud. Adv. Math. 8, Cambridge University Press 1986, doi:10.1017/CBO9781139171762, Theorem 19.3; J.-P. Serre, Sur la dimension homologique des anneaux et des modules noethériens, Proc. Int. Symp. Algebraic Number Theory, Tokyo-Nikko 1955, Sci. Council Japan (1956), 175-189

import Mathlib
import Definitions.Def_RPLib_S4_JacDivisorsD

/-!
# S4-JacDivisors E (O6: localizations of regular local rings)
* `localizedModule_quotient_iso`: `(R ⧸ Q)_Q ≅ R_Q ⧸ m_{R_Q}` as `R_Q`-modules.
* `isRegularLocalRing_localization` (O6): `R` regular local, `Q` prime ⟹ `R_Q` regular local
  (Serre: `pd_R (R ⧸ Q) < ∞` localizes to `pd_{R_Q} k(Q) < ∞`).
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacDivisors

open CategoryTheory IsLocalRing Ideal

universe u

variable {R : Type u} [CommRing R]

/-- `(R ⧸ Q)_Q ≅ R_Q ⧸ m` as `R_Q`-modules. -/
noncomputable def localizedModule_quotient_iso (Q : Ideal R) [Q.IsPrime] :
    (ModuleCat.of R (R ⧸ Q)).localizedModule Q.primeCompl ≅
      ModuleCat.of (Localization.AtPrime Q)
        (Localization.AtPrime Q ⧸ maximalIdeal (Localization.AtPrime Q)) :=
  let e1 := Shrink.linearEquiv.{u} (Localization.AtPrime Q)
    (LocalizedModule Q.primeCompl (R ⧸ Q))
  let e2 := (IsLocalizedModule.iso Q.primeCompl
    (Q.toLocalizedQuotient' (Localization.AtPrime Q) Q.primeCompl
      (Algebra.linearMap R (Localization.AtPrime Q)))).extendScalarsOfIsLocalization
        Q.primeCompl (Localization.AtPrime Q)
  let e3 := Submodule.quotEquivOfEq _ _ (by
    rw [Ideal.localized'_eq_map, Localization.AtPrime.map_eq_maximalIdeal])
  (e1.trans (e2.trans e3)).toModuleIso

/-- O6: the localization of a regular local ring at a prime is regular local. -/
theorem isRegularLocalRing_localization [IsRegularLocalRing R] (Q : Ideal R) [Q.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime Q) := by
  obtain ⟨n, hn⟩ := exists_hasPDLT_of_isRegularLocalRing (ModuleCat.of R (R ⧸ Q))
  have : HasProjectiveDimensionLE (ModuleCat.of R (R ⧸ Q)) n :=
    hasProjectiveDimensionLT_of_ge _ n (n + 1) (by omega)
  have h1 := (ModuleCat.of R (R ⧸ Q)).localizedModule_hasProjectiveDimensionLE n Q.primeCompl
  have h2 := hasProjectiveDimensionLT_of_iso (localizedModule_quotient_iso Q) (n + 1)
  exact isRegularLocalRing_of_hasPDLT (n + 1) h2

end RamanujanPetersson.JacDivisors


