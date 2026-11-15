-- Prove2me | Definitions.Def_RPLib_S3_DWSIsog
-- name    : RPLib_S3_DWSIsog
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T17:03:31.90083+00:00
-- url     : https://prove2.me/theorems/dd62effb-0bda-40d6-957e-24c5334a6e28
-- title:
--   Weight-two Ramanujan-Petersson library: isogenies and endomorphism rings of elliptic curves over `F_q` (headline file)
-- statement:
--   Isogenies and endomorphism rings of elliptic curves over `F_q` (headline file).
--
--   `W` is an elliptic curve over a finite field `F` (`q = #F`), `L ⊇ F` algebraically closed. Morphisms are additive maps
--   on `L`-points with a generic-point representative (`IsEndo`, `IsIsog`, files A, C); everything is pure Mathlib
--   `WeierstrassCurve` language. The parts:
--
--   * A: `endRing W L` (`End(E)`) and `endFq W L` (`End_{F_q}(E)`, commuting with the `q`-Frobenius `π`) as subrings of
--     `AddMonoid.End E(L)`; `ℤ[π] ⊆ End_{F_q}(E)`; degree, trace, Cayley–Hamilton, no zero divisors.
--   * B: for ordinary `E` (`p ∤ a`): `a² < 4q`, `End_{F_q}(E)` commutative and an order `ℤ + ℤω`, `f ω = π - b`,
--     `ω` imaginary quadratic, `a² - 4q = f² disc(ω)`.
--   * C, D: isogenies `E → E'`, `F_q`-isogenous curves have the same number of points and the same trace.
--   * E–L: the Vélu quotient `E → E/G` over `F_q` for a finite Frobenius-stable `G` with `p ∤ #G`, kernel exactly `G`.
--   * M–O: surjectivity, the universal property of `E → E/G`, the dual isogeny.
--
--   Headline results of this file: `endFq_contains_Zpi`, `endFq_ordinary`, `isogenous_same_trace`,
--   `velu_quotient_dual`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211; J. Tate, Endomorphisms of abelian varieties over finite fields, Invent. Math. 2 (1966), 134-144; J. Vélu, Isogénies entre courbes elliptiques, C. R. Acad. Sci. Paris Sér. A 273 (1971), 238-241; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Chapters III and V

import Mathlib
import Definitions.Def_RPLib_S3_DWSIsogO

/-!
# S3-DWS-Isog: isogenies and endomorphism rings of elliptic curves over `F_q` (headline file)

`W` is an elliptic curve over a finite field `F` (`q = #F`), `L ⊇ F` algebraically closed. Morphisms are additive maps
on `L`-points with a generic-point representative (`IsEndo`, `IsIsog`, files A, C); everything is pure Mathlib
`WeierstrassCurve` language. The parts:

* A: `endRing W L` (`End(E)`) and `endFq W L` (`End_{F_q}(E)`, commuting with the `q`-Frobenius `π`) as subrings of
  `AddMonoid.End E(L)`; `ℤ[π] ⊆ End_{F_q}(E)`; degree, trace, Cayley–Hamilton, no zero divisors.
* B: for ordinary `E` (`p ∤ a`): `a² < 4q`, `End_{F_q}(E)` commutative and an order `ℤ + ℤω`, `f ω = π - b`,
  `ω` imaginary quadratic, `a² - 4q = f² disc(ω)`.
* C, D: isogenies `E → E'`, `F_q`-isogenous curves have the same number of points and the same trace.
* E–L: the Vélu quotient `E → E/G` over `F_q` for a finite Frobenius-stable `G` with `p ∤ #G`, kernel exactly `G`.
* M–O: surjectivity, the universal property of `E → E/G`, the dual isogeny.

Headline results of this file: `endFq_contains_Zpi`, `endFq_ordinary`, `isogenous_same_trace`,
`velu_quotient_dual`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open WeierstrassCurve WeierstrassCurve.Affine

namespace RPLib.DWS

open RPLib.Weil RPLib.Isog RPLib.Hasse

section Headline

variable {F : Type*} [Field F] [Fintype F] {W : WeierstrassCurve F} [W.IsElliptic]
  {L : Type*} [Field L] [Algebra F L] [IsAlgClosed L] [DecidableEq L]

attribute [local instance] finite_coordinateRing decEqFF torsModule

/-- **`ℤ[π] ⊆ End_{F_q}(E) ⊆ End(E)`**, and `π² - a π + q = 0`. -/
theorem endFq_contains_Zpi :
    piE W L ∈ endFq W L ∧ (∀ r s : ℤ, rsE W L r s ∈ endFq W L) ∧ endFq W L ≤ endRing W L ∧
      piE W L * piE W L - (RPLib.EllFq.trace W : AddMonoid.End (Pt W L)) * piE W L +
        ((Fintype.card F : ℤ) : AddMonoid.End (Pt W L)) = 0 :=
  ⟨frob_mem_endFq, rsHom_mem_endFq, endFq_le, frob_ch⟩

/-- **`End_{F_q}(E)` of an ordinary curve is an order in the imaginary quadratic field `ℚ(π)`.** If `p ∤ a` then
`a² < 4q`, `End_{F_q}(E)` is commutative, `End_{F_q}(E) = ℤ + ℤω` with `f ω = π - b` (`f > 0`), so
`f · End_{F_q}(E) ⊆ ℤ[π] ⊆ End_{F_q}(E)` (`End_{F_q}(E) ⊗ ℚ = ℚ(π)`), `ω² - tr ω ω + deg ω = 0` with
`tr ω² < 4 deg ω`, and `a² - 4q = f² (tr ω² - 4 deg ω)`. -/
theorem endFq_ordinary (h : ¬ ((ringChar F : ℤ) ∣ RPLib.EllFq.trace W)) :
    RPLib.EllFq.trace W ^ 2 < 4 * (Fintype.card F : ℤ) ∧
    (∀ φ ∈ endFq W L, ∀ ψ ∈ endFq W L, φ * ψ = ψ * φ) ∧
    ∃ (f b : ℤ) (ω : AddMonoid.End (Pt W L)), 0 < f ∧ ω ∈ endFq W L ∧
      (f : AddMonoid.End (Pt W L)) * ω = piE W L - (b : AddMonoid.End (Pt W L)) ∧
      (∀ φ ∈ endFq W L, ∃ i j : ℤ,
        φ = (i : AddMonoid.End (Pt W L)) + (j : AddMonoid.End (Pt W L)) * ω) ∧
      (∀ i j : ℤ, (i : AddMonoid.End (Pt W L)) + (j : AddMonoid.End (Pt W L)) * ω = 0 →
        i = 0 ∧ j = 0) ∧
      (∀ φ ∈ endFq W L, ∃ i j : ℤ,
        (f : AddMonoid.End (Pt W L)) * φ = (i : AddMonoid.End (Pt W L)) + (j : AddMonoid.End (Pt W L)) * piE W L) ∧
      ω * ω - (tr ω : AddMonoid.End (Pt W L)) * ω + ((deg ω : ℤ) : AddMonoid.End (Pt W L)) = 0 ∧
      tr ω ^ 2 < 4 * (deg ω : ℤ) ∧
      RPLib.EllFq.trace W = 2 * b + f * tr ω ∧
      (Fintype.card F : ℤ) = b ^ 2 + f * tr ω * b + f ^ 2 * (deg ω : ℤ) ∧
      RPLib.EllFq.trace W ^ 2 - 4 * (Fintype.card F : ℤ) = f ^ 2 * (tr ω ^ 2 - 4 * (deg ω : ℤ)) := by
  have ht := trace_sq_lt_of_not_dvd h
  obtain ⟨f, b, ω, hf, hω, hfω, hbasis, hindep, htr, hq, hdisc, hneg⟩ := endFq_order_basis (L := L) ht
  refine ⟨ht, fun φ hφ ψ hψ => endFq_comm ht hφ hψ, f, b, ω, hf, hω, hfω, hbasis, hindep, fun φ hφ => ?_,
    ch (endFq_le hω), hneg, htr, hq, hdisc⟩
  obtain ⟨i, j, rfl⟩ := hbasis φ hφ
  refine ⟨f * i - j * b, j, ?_⟩
  rw [mul_add, ← mul_assoc, (Int.cast_commute f (j : AddMonoid.End (Pt W L))).eq, mul_assoc, hfω, mul_sub]
  push_cast
  abel

/-- **`F_q`-isogenous curves have the same number of points and the same trace**, and `F_q`-isogeny is transitive. -/
theorem isogenous_same_trace {W' W'' : WeierstrassCurve F} [W'.IsElliptic] [W''.IsElliptic]
    (h : IsIsogenous W W' L) :
    RPLib.EllFq.trace W = RPLib.EllFq.trace W' ∧ RPLib.EllFq.numPoints W = RPLib.EllFq.numPoints W' ∧
      (IsIsogenous W' W'' L → IsIsogenous W W'' L) :=
  ⟨h.trace_eq, h.numPoints_eq, fun h' => h.trans h'⟩

/-- **Vélu quotient `E → E/G` over `F_q` with its dual.** For a finite Frobenius-stable subgroup `G ⊆ E(L)` with
`p ∤ #G` there is an elliptic curve `W'` over `F_q` and isogenies `φ : E → E'`, `ψ : E' → E` commuting with
Frobenius such that `ker φ = G` (so `#ker φ = #G`, the degree of the separable isogeny `φ`), `φ` is surjective,
`ψ ∘ φ = [#G]` (of degree `#G²`) and `φ ∘ ψ = [#G]`, every isogeny `α : E → E₁` killing `G` factors uniquely
through `φ`, and the two curves are `F_q`-isogenous both ways with the same trace and number of points. -/
theorem velu_quotient_dual (G : AddSubgroup (Pt W L)) [Fintype G] (hG : (Fintype.card G : L) ≠ 0)
    (hFr : ∀ T ∈ G, RPLib.EllFq.frob W L T ∈ G) :
    ∃ W' : WeierstrassCurve F, ∃ _ : W'.IsElliptic, ∃ φ : Pt W L →+ Pt W' L, ∃ ψ : Pt W' L →+ Pt W L,
      IsIsog φ ∧ IsIsog ψ ∧ (∀ S, φ S = 0 ↔ S ∈ G) ∧ {S | φ S = 0}.ncard = Fintype.card G ∧
      Function.Surjective φ ∧
      (∀ P, ψ (φ P) = Fintype.card G • P) ∧ (∀ Q, φ (ψ Q) = Fintype.card G • Q) ∧
      (deg (ψ.comp φ) : ℤ) = (Fintype.card G : ℤ) ^ 2 ∧
      (∀ P, φ (RPLib.EllFq.frob W L P) = RPLib.EllFq.frob W' L (φ P)) ∧
      (∀ Q, ψ (RPLib.EllFq.frob W' L Q) = RPLib.EllFq.frob W L (ψ Q)) ∧
      (∀ (W₁ : WeierstrassCurve F) [W₁.IsElliptic] (α : Pt W L →+ Pt W₁ L), IsIsog α →
        (∀ T ∈ G, α T = 0) → ∃! β : Pt W' L →+ Pt W₁ L, IsIsog β ∧ β.comp φ = α) ∧
      IsIsogenous W W' L ∧ IsIsogenous W' W L ∧ RPLib.EllFq.trace W' = RPLib.EllFq.trace W ∧
      RPLib.EllFq.numPoints W' = RPLib.EllFq.numPoints W := by
  obtain ⟨W', hE, hW'⟩ := exists_quotient hG hFr
  have := hE
  obtain ⟨ψ, hψ, -, h1, h2, h3⟩ := exists_dual hG hW' hFr
  have hsurj := qmap_surjective hG hW'
  have hset : {S | qmap hG hW' S = 0} = (G : Set (Pt W L)) := Set.ext fun S => qmap_eq_zero_iff hG hW'
  have hdeg : ψ.comp (qmap hG hW') = (((Fintype.card G : ℕ) : ℤ) : AddMonoid.End (Pt W L)) := by
    refine AddMonoidHom.ext fun P => ?_
    show ψ (qmap hG hW' P) = ((Fintype.card G : ℤ) : AddMonoid.End (Pt W L)) P
    rw [h1]
    show _ = (Fintype.card G : ℤ) • P
    exact (natCast_zsmul P _).symm
  have hiso := isIsogenous_quot hG hW' hFr
  refine ⟨W', hE, qmap hG hW', ψ, ⟨qPt hW', hasGenI_qmap hG hW'⟩, hψ,
    fun S => qmap_eq_zero_iff hG hW', ?_, hsurj, h1, h2, ?_, qmap_frob hG hW' hFr, h3, ?_,
    hiso, isIsogenous_dual hG hW' hFr, hiso.trace_eq.symm, hiso.numPoints_eq.symm⟩
  · rw [hset, ← Nat.card_coe_set_eq, SetLike.coe_sort_coe, Nat.card_eq_fintype_card]
  · rw [hdeg]; exact endo_deg_intCast _
  · intro W₁ _ α hα hker
    obtain ⟨A, hA⟩ := hα
    obtain ⟨β, hβ, hcomp⟩ := exists_factor hG hW' hA hker
    refine ⟨β, ⟨hβ, hcomp⟩, fun β' hβ' => ?_⟩
    refine AddMonoidHom.ext fun Q => ?_
    obtain ⟨P, rfl⟩ := hsurj Q
    have e1 := congrArg (fun χ : Pt W L →+ Pt W₁ L => χ P) hβ'.2
    have e2 := congrArg (fun χ : Pt W L →+ Pt W₁ L => χ P) hcomp
    exact e1.trans e2.symm

end Headline

end RPLib.DWS


