-- Prove2me | Definitions.Def_RPLib_S3_TateStmtP
-- name    : RPLib_S3_TateStmtP
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T16:19:52.799098+00:00
-- url     : https://prove2.me/theorems/6c987414-cfe3-4a38-8eaf-ff817186a691
-- title:
--   Weight-two Ramanujan-Petersson library: Tate's isogeny theorem, PRIME-TO-`p` form: the hypothesis actually consumed by the S3 DWS chain
-- statement:
--   Tate's isogeny theorem, PRIME-TO-`p` form: the hypothesis actually consumed by the S3 DWS chain.
--
--   Pure Mathlib (imports `Mathlib` only). This is the form proposed for the platform leaf (option A), replacing the plain
--   `TateIsogenyStatement` of `TateStmt.lean` (which it implies, see `TateIsogenyPrimeToP.plain`).
--
--   For ORDINARY elliptic curves `E, E'` over a finite field `F` (`p = char F` does not divide the trace
--   `q + 1 - #E(F)`) with the same number of points (Tate) there is an `F`-isogeny `u : E → E'` of degree `N` prime to
--   `p` (Deuring: `Hom(E, E')` is an invertible module over the endomorphism orders, whose conductors are prime to `p`).
--   With its dual `w = û` one has `w ∘ u = [N]`. On function fields `f = u^* : K(E') → K(E)`, `g = w^* : K(E) → K(E')`
--   and `f ∘ g = (w ∘ u)^* = [N]^*`, i.e. `f ∘ g` sends the generic point `(x, y)` of `E` to `N • (x, y)` in
--   `E(K(E))`. The statement says exactly this.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211; J. Tate, Endomorphisms of abelian varieties over finite fields, Invent. Math. 2 (1966), 134-144; J. Vélu, Isogénies entre courbes elliptiques, C. R. Acad. Sci. Paris Sér. A 273 (1971), 238-241; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Chapters III and V

import Mathlib

/-!
# Tate's isogeny theorem, PRIME-TO-`p` form: the hypothesis actually consumed by the S3 DWS chain

Pure Mathlib (imports `Mathlib` only). This is the form proposed for the platform leaf (option A), replacing the plain
`TateIsogenyStatement` of `TateStmt.lean` (which it implies, see `TateIsogenyPrimeToP.plain`).

For ORDINARY elliptic curves `E, E'` over a finite field `F` (`p = char F` does not divide the trace
`q + 1 - #E(F)`) with the same number of points (Tate) there is an `F`-isogeny `u : E → E'` of degree `N` prime to
`p` (Deuring: `Hom(E, E')` is an invertible module over the endomorphism orders, whose conductors are prime to `p`).
With its dual `w = û` one has `w ∘ u = [N]`. On function fields `f = u^* : K(E') → K(E)`, `g = w^* : K(E) → K(E')`
and `f ∘ g = (w ∘ u)^* = [N]^*`, i.e. `f ∘ g` sends the generic point `(x, y)` of `E` to `N • (x, y)` in
`E(K(E))`. The statement says exactly this.
-/

set_option autoImplicit false

universe u

namespace RPLib.DWS

open WeierstrassCurve WeierstrassCurve.Affine

/-- **Tate's isogeny theorem, prime-to-`p` form** (statement only; never assumed as an axiom). Two ordinary elliptic
curves over a finite field `F` with the same number of `F`-points are linked by `F`-morphisms `u : E → E'`,
`w : E' → E` with `w ∘ u = [N]`, `N` prime to the characteristic: the pullbacks `f = u^*`, `g = w^*` of function
fields satisfy `(f ∘ g) (x, y) = N • (x, y)` for the generic point `(x, y)` of `W` over its function field. -/
def TateIsogenyPrimeToP : Prop :=
  ∀ (F : Type u) [Field F] [Fintype F] (W W' : WeierstrassCurve F) [W.IsElliptic] [W'.IsElliptic],
    Nat.card W.toAffine.Point = Nat.card W'.toAffine.Point →
    ¬ ((ringChar F : ℤ) ∣ ((Fintype.card F : ℤ) + 1 - (Nat.card W.toAffine.Point : ℤ))) →
    ∃ (f : W'.toAffine.FunctionField →ₐ[F] W.toAffine.FunctionField)
      (g : W.toAffine.FunctionField →ₐ[F] W'.toAffine.FunctionField) (N : ℕ), (N : F) ≠ 0 ∧
      ∃ h : (W.baseChange W.toAffine.FunctionField).toAffine.Nonsingular
          (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
            (CoordinateRing.mk W.toAffine (Polynomial.C Polynomial.X)))
          (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
            (CoordinateRing.mk W.toAffine Polynomial.X)),
        Point.map (W' := W.toAffine) (f.comp g) (Point.some _ _ h) = N • Point.some _ _ h

/-- The prime-to-`p` form gives the plain conclusion (an `F`-algebra map `K(E') → K(E)`) for ordinary curves. -/
theorem TateIsogenyPrimeToP.plain (hT : TateIsogenyPrimeToP.{u}) (F : Type u) [Field F] [Fintype F]
    (W W' : WeierstrassCurve F) [W.IsElliptic] [W'.IsElliptic]
    (hN : Nat.card W.toAffine.Point = Nat.card W'.toAffine.Point)
    (hord : ¬ ((ringChar F : ℤ) ∣ ((Fintype.card F : ℤ) + 1 - (Nat.card W.toAffine.Point : ℤ)))) :
    Nonempty (W'.toAffine.FunctionField →ₐ[F] W.toAffine.FunctionField) := by
  obtain ⟨f, -, -, -, -⟩ := hT F W W' hN hord
  exact ⟨f⟩

end RPLib.DWS


