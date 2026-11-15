-- Prove2me | Definitions.Def_RPLib_S3_DWSTateY
-- name    : RPLib_S3_DWSTateY
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T17:59:34.651496+00:00
-- url     : https://prove2.me/theorems/11344439-ef78-47e7-8969-aeb8afc22702
-- title:
--   Weight-two Ramanujan-Petersson library: parts (a) and (b7) conditional on Tate
-- statement:
--   Parts (a) and (b7) conditional on Tate.
--
--   Tate's isogeny theorem enters ONLY as the explicit hypothesis `hT : TateIsogenyPrimeToP` (`lib/S3/TateStmtP.lean`,
--   pure Mathlib, never an axiom). For ORDINARY curves (`p ∤ trace`):
--   * `exists_isog_of_tate`: equal point counts give a prime-to-`p` Frobenius-equivariant isogeny pair `u, w` with
--     `w ∘ u = [n]`, `u ∘ w = [n]` (Tate pullbacks + `exists_isog_data`, file X).
--   * `exists_nsmul_ne_zero`: `[n] ≠ 0` on `E(L)` when `p ∤ n`.
--   * **`isIsogenous_of_tate`** (part (a), ordinary case): equal trace ⇒ `F_q`-isogenous.
--   * **`exists_quotClass_of_tate`** (b7 under Tate): Frobenius-normalised `R`-structures on `E, E₁` with the same
--     number of points put `E₁` in the `Pic(R)`-orbit of `E` (`exists_quotClass_of_isog`, file L).
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211; J. Tate, Endomorphisms of abelian varieties over finite fields, Invent. Math. 2 (1966), 134-144; J. Vélu, Isogénies entre courbes elliptiques, C. R. Acad. Sci. Paris Sér. A 273 (1971), 238-241; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Chapters III and V

import Mathlib
import Definitions.Def_RPLib_S3_DWSTateX
import Definitions.Def_RPLib_S3_DWSTateL
import Definitions.Def_RPLib_S3_TateStmtP

/-!
# S3-DWS-Tate, part Y (FINAL of the bridge BR): parts (a) and (b7) conditional on Tate

Tate's isogeny theorem enters ONLY as the explicit hypothesis `hT : TateIsogenyPrimeToP` (`lib/S3/TateStmtP.lean`,
pure Mathlib, never an axiom). For ORDINARY curves (`p ∤ trace`):
* `exists_isog_of_tate`: equal point counts give a prime-to-`p` Frobenius-equivariant isogeny pair `u, w` with
  `w ∘ u = [n]`, `u ∘ w = [n]` (Tate pullbacks + `exists_isog_data`, file X).
* `exists_nsmul_ne_zero`: `[n] ≠ 0` on `E(L)` when `p ∤ n`.
* **`isIsogenous_of_tate`** (part (a), ordinary case): equal trace ⇒ `F_q`-isogenous.
* **`exists_quotClass_of_tate`** (b7 under Tate): Frobenius-normalised `R`-structures on `E, E₁` with the same
  number of points put `E₁` in the `Pic(R)`-orbit of `E` (`exists_quotClass_of_isog`, file L).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u v

open WeierstrassCurve WeierstrassCurve.Affine

namespace RPLib.DWS

open RPLib.Weil RPLib.Isog RPLib.Hasse QuadraticAlgebra RamanujanPetersson.Hurwitz

section Y

variable {F : Type u} [Field F] [Fintype F] {L : Type v} [Field L] [Algebra F L] [IsAlgClosed L]
  [DecidableEq L]

attribute [local instance] finite_coordinateRing decEqFF

variable {W W₁ : WeierstrassCurve F} [W.IsElliptic] [W₁.IsElliptic]

/-- Under Tate (prime-to-`p` form), ordinary curves with the same number of points carry a prime-to-`p`
Frobenius-equivariant isogeny pair. -/
theorem exists_isog_of_tate (hT : TateIsogenyPrimeToP.{u}) [Algebra.IsAlgebraic F L]
    (hcard : Nat.card W.toAffine.Point = Nat.card W₁.toAffine.Point)
    (hord : ¬ ((ringChar F : ℤ) ∣ RPLib.EllFq.trace W)) :
    ∃ n : ℕ, (n : F) ≠ 0 ∧ ∃ u : Pt W L →+ Pt W₁ L, ∃ w : Pt W₁ L →+ Pt W L,
      IsIsog u ∧ IsIsog w ∧ (∀ P, w (u P) = n • P) ∧ (∀ Q, u (w Q) = n • Q) ∧
      (∀ P, u (RPLib.EllFq.frob W L P) = RPLib.EllFq.frob W₁ L (u P)) := by
  have hord' : ¬ ((ringChar F : ℤ) ∣ ((Fintype.card F : ℤ) + 1 - (Nat.card W.toAffine.Point : ℤ))) := by
    intro h
    apply hord
    unfold RPLib.EllFq.trace RPLib.EllFq.numPoints
    rwa [Nat.card_eq_fintype_card (α := F)]
  obtain ⟨f, g, N, hNF, _h, hfg⟩ := hT F W W₁ hcard hord'
  have hfg' : Point.map (W' := W.toAffine) (f.comp g) (P0 W) = N • P0 W := hfg
  have := finite_HT (L := L) hNF f
  let _ : Fintype (HT L N f) := Fintype.ofFinite _
  exact exists_isog_data (L := L) hNF f g hfg'

/-- `[n]` is nonzero on `E(L)` when `p ∤ n` (a point of prime order `ℓ > n` survives). -/
theorem exists_nsmul_ne_zero {n : ℕ} (hn : (n : F) ≠ 0) : ∃ P : Pt W L, n • P ≠ 0 := by
  have hnL : (n : L) ≠ 0 := by
    rw [← map_natCast (algebraMap F L)]; exact (map_ne_zero _).mpr hn
  have hn0 : n ≠ 0 := by rintro rfl; exact hn Nat.cast_zero
  obtain ⟨ℓ, hℓ1, hℓ⟩ := Nat.exists_infinite_primes (n + ringChar L + 2)
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hL : (ℓ : L) ≠ 0 := natCast_ne_zero_of_prime hℓ (by omega)
  have hc := RPLib.Torsion.card_tors (W := W.baseChange L) ℓ hL
  have hex : ∃ P : Pt W L, P ∈ RPLib.Torsion.tors (W.baseChange L) ℓ ∧ P ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    haveI : Subsingleton (RPLib.Torsion.tors (W.baseChange L) ℓ) :=
      ⟨fun x y => Subtype.ext ((hcon x x.2).trans (hcon y y.2).symm)⟩
    have h1 := Nat.card_of_subsingleton (0 : RPLib.Torsion.tors (W.baseChange L) ℓ)
    rw [hc] at h1
    have h2 := hℓ.two_le
    nlinarith
  obtain ⟨P, hP, hP0⟩ := hex
  refine ⟨P, fun hnP => ?_⟩
  have hord : addOrderOf P = ℓ := addOrderOf_eq_prime (RPLib.Torsion.mem_tors.mp hP) hP0
  have hd : ℓ ∣ n := hord ▸ addOrderOf_dvd_of_nsmul_eq_zero hnP
  have := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hd
  omega

/-- **Part (a) under Tate, ordinary case**: ordinary elliptic curves over `F_q` with the same trace are
`F_q`-isogenous (`IsIsogenous`, file DWSIsog_D). -/
theorem isIsogenous_of_tate (hT : TateIsogenyPrimeToP.{u}) [Algebra.IsAlgebraic F L]
    (htr : RPLib.EllFq.trace W = RPLib.EllFq.trace W₁)
    (hord : ¬ ((ringChar F : ℤ) ∣ RPLib.EllFq.trace W)) : IsIsogenous W W₁ L := by
  have hcard : Nat.card W.toAffine.Point = Nat.card W₁.toAffine.Point :=
    (numPoints_eq_iff_trace_eq W W₁).mpr htr
  obtain ⟨n, hn, u, w, hu, -, hwu, -, hfu⟩ := exists_isog_of_tate (L := L) hT hcard hord
  refine ⟨u, hu, fun hu0 => ?_, hfu⟩
  obtain ⟨P, hP⟩ := exists_nsmul_ne_zero (W := W) (L := L) hn
  apply hP
  rw [← hwu P, hu0, AddMonoidHom.zero_apply, map_zero]

variable {a b : ℤ} {s : OAct (QuadraticAlgebra ℤ a b) W L} {s₁ : OAct (QuadraticAlgebra ℤ a b) W₁ L}

/-- **(b7) under Tate.** Given the prime-to-`p` Tate hypothesis `hT`, two ordinary elliptic curves over `F_q`
with the same number of points and Frobenius-normalised `R`-structures lie in one `Pic(R)`-orbit. -/
theorem exists_quotClass_of_tate (hT : TateIsogenyPrimeToP.{u}) [Algebra.IsAlgebraic F L]
    (hcard : Nat.card W.toAffine.Point = Nat.card W₁.toAffine.Point)
    (hord : ¬ ((ringChar F : ℤ) ∣ RPLib.EllFq.trace W))
    (hD : b ^ 2 + 4 * a < 0) {π : QuadraticAlgebra ℤ a b}
    (hπ : s.ι π = piE W L) (hπ₁ : s₁.ι π = piE W₁ L) (hπF : (π.im.natAbs : F) ≠ 0) :
    ∃ c : QA.PicQ hD, QuotClass W₁ hD s c := by
  obtain ⟨n, hn, u, w, hu, hw, hwu, huw, hfu⟩ := exists_isog_of_tate (L := L) hT hcard hord
  exact exists_quotClass_of_isog hD hπ hπ₁ hπF hn hu hw hwu huw hfu

end Y

end RPLib.DWS


