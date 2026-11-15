-- Prove2me | Definitions.Def_RPLib_S3_DWSOCA
-- name    : RPLib_S3_DWSOCA
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T17:46:49.739211+00:00
-- url     : https://prove2.me/theorems/f350dfbf-220a-4e51-acae-0c2dba11a369
-- title:
--   Weight-two Ramanujan-Petersson library: automorphisms and the per-curve bound (O3, part 1)
-- statement:
--   Automorphisms and the per-curve bound (O3, part 1).
--
--   * `finite_variableChange` : over a finite field there are finitely many changes of variables.
--   * `autOf` / `autOf_injective` / **`card_units_le_autVC`** : `#(End_{F_q} E)ˣ ≤ #Aut_VC(E)` (VC2-F applied to
--     each unit of the Frobenius-commuting endomorphism ring).
--   * `shiftEquiv` : `ℤ[ω'] ≃ ℤ[ω]`, `ω' = ω - k`, between two presentations of one quadratic order;
--     `oactComap` pulls an order structure back along a ring isomorphism.
--   * **`card_ycl_mul_sD_le`** : `#yclSet E M · s(D') ≤ L_f(t, D')` for an ordinary `E` with order data `d`
--     (`D' = disc ℤ[w]`, `f = d.f`, `t = a_E`).
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Chapters III and V; Y. Ihara, Hecke polynomials as congruence zeta functions in elliptic modular case, Ann. of Math. 85 (1967), 267-295; M. Eichler, Quaternäre quadratische Formen und die Riemannsche Vermutung für die Kongruenzzetafunktion, Arch. Math. 5 (1954), 355-366; G. Shimura, Introduction to the Arithmetic Theory of Automorphic Functions, Princeton 1971, Chapter 7

import Mathlib
import Definitions.Def_RPLib_S3_DWSOVE
import Definitions.Def_RPLib_S3_DWSOR
import Definitions.Def_RPLib_S3_DWSTateH

/-!
# S3-DWS-Ordinary, part CA: automorphisms and the per-curve bound (O3, part 1)

* `finite_variableChange` : over a finite field there are finitely many changes of variables.
* `autOf` / `autOf_injective` / **`card_units_le_autVC`** : `#(End_{F_q} E)ˣ ≤ #Aut_VC(E)` (VC2-F applied to
  each unit of the Frobenius-commuting endomorphism ring).
* `shiftEquiv` : `ℤ[ω'] ≃ ℤ[ω]`, `ω' = ω - k`, between two presentations of one quadratic order;
  `oactComap` pulls an order structure back along a ring isomorphism.
* **`card_ycl_mul_sD_le`** : `#yclSet E M · s(D') ≤ L_f(t, D')` for an ordinary `E` with order data `d`
  (`D' = disc ℤ[w]`, `f = d.f`, `t = a_E`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open WeierstrassCurve WeierstrassCurve.Affine RPLib.TateNF

namespace RamanujanPetersson.S3.DWSO

open RPLib.Weil RPLib.Isog RPLib.Hasse RPLib.DWS

section Fin

variable {F : Type*} [Field F] [Finite F]

instance finite_variableChange : Finite (VariableChange F) :=
  Finite.of_injective (fun C : VariableChange F => (C.u, C.r, C.s, C.t)) (by
    rintro ⟨u, r, s, t⟩ ⟨u', r', s', t'⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    rfl)

end Fin

section Shift

/-- The shift `x + y ω' ↦ (x - k y) + y ω` between two presentations of one quadratic order
(`ω' = ω - k`, `b = b' + 2k`, `a = a' - k² - b'k`). -/
def shiftEquiv {a b a' b' : ℤ} (k : ℤ) (hb : b = b' + 2 * k) (ha : a = a' - k ^ 2 - b' * k) :
    QuadraticAlgebra ℤ a' b' ≃+* QuadraticAlgebra ℤ a b where
  toFun z := ⟨z.re - k * z.im, z.im⟩
  invFun z := ⟨z.re + k * z.im, z.im⟩
  left_inv z := by ext <;> simp
  right_inv z := by ext <;> simp
  map_mul' z w := by
    subst hb ha
    ext <;> simp <;> ring
  map_add' z w := by ext <;> simp <;> ring

lemma shiftEquiv_mk {a b a' b' : ℤ} (k : ℤ) (hb : b = b' + 2 * k) (ha : a = a' - k ^ 2 - b' * k) (x y : ℤ) :
    shiftEquiv k hb ha (⟨x, y⟩ : QuadraticAlgebra ℤ a' b') = ⟨x - k * y, y⟩ := rfl

end Shift

section Comap

variable {F : Type*} [Field F] [Fintype F] {L : Type*} [Field L] [Algebra F L] [IsAlgClosed L] [DecidableEq L]
  {W : WeierstrassCurve F} [W.IsElliptic]

/-- Pull an order structure back along a ring isomorphism. -/
def oactComap {R R' : Type*} [CommRing R] [CommRing R'] (s : OAct R W L) (e : R' ≃+* R) : OAct R' W L :=
  ⟨s.ι.comp e.toRingHom, s.inj.comp e.injective, fun _ => s.mem _, fun γ hγ => by
    obtain ⟨r, hr⟩ := s.surj γ hγ
    exact ⟨e.symm r, by simp [hr]⟩⟩

lemma oactComap_ι {R R' : Type*} [CommRing R] [CommRing R'] (s : OAct R W L) (e : R' ≃+* R) (r : R') :
    (oactComap s e).ι r = s.ι (e r) := rfl

end Comap

section Aut

variable {F : Type*} [Field F] [Fintype F] {W : WeierstrassCurve F} [W.IsElliptic]
  {L : Type*} [Field L] [Algebra F L] [IsAlgClosed L] [DecidableEq L]

attribute [local instance] finite_coordinateRing decEqFF

lemma units_inv_apply (γ : (endFq W L)ˣ) (P : Pt W L) :
    (((γ⁻¹ : (endFq W L)ˣ) : endFq W L) : AddMonoid.End (Pt W L))
      (((γ : endFq W L) : AddMonoid.End (Pt W L)) P) = P := by
  have h : (((γ⁻¹ * γ : (endFq W L)ˣ) : endFq W L) : AddMonoid.End (Pt W L)) P = P := by
    rw [inv_mul_cancel]; rfl
  exact h

lemma exists_autVC (γ : (endFq W L)ˣ) : ∃ (C : VariableChange F) (h : C • W = W),
    (((γ : endFq W L) : AddMonoid.End (Pt W L)) : Pt W L →+ Pt W L) =
      ptHom (C.map (algebraMap F L)) (vc_bcF h) :=
  exists_vcF (isIsog_of_mem γ.1.2) (isIsog_of_mem (γ⁻¹).1.2) (units_inv_apply γ) (endFq_frob γ.1.2)

/-- The change of variables realising a unit of `End_{F_q}(E)`. -/
noncomputable def autOf (γ : (endFq W L)ˣ) : AutVC W :=
  ⟨Classical.choose (exists_autVC γ),
    MulAction.mem_stabilizer_iff.mpr (Classical.choose_spec (exists_autVC γ)).fst⟩

lemma ptHom_congr {C C' : VariableChange F} (e : C = C') (h : C • W = W) (h' : C' • W = W) :
    ptHom (C.map (algebraMap F L)) (vc_bcF h) = ptHom (C'.map (algebraMap F L)) (vc_bcF h') := by
  subst e; rfl

lemma autOf_injective : Function.Injective (autOf (W := W) (L := L)) := by
  intro γ γ' h
  have e : Classical.choose (exists_autVC γ) = Classical.choose (exists_autVC γ') :=
    congrArg Subtype.val h
  obtain ⟨h₁, h₁'⟩ := Classical.choose_spec (exists_autVC γ)
  obtain ⟨h₂, h₂'⟩ := Classical.choose_spec (exists_autVC γ')
  apply Units.ext
  apply Subtype.ext
  exact h₁'.trans ((ptHom_congr e h₁ h₂).trans h₂'.symm)

/-- **`#(End_{F_q} E)ˣ ≤ #Aut_VC(E)`.** -/
theorem card_units_le_autVC : Nat.card (endFq W L)ˣ ≤ Nat.card (AutVC W) :=
  Nat.card_le_card_of_injective _ autOf_injective

end Aut

section Bound

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {L : Type*} [Field L] [Algebra F L] [IsAlgClosed L]
  [DecidableEq L] {W : WeierstrassCurve F} [W.IsElliptic] {M : ℕ} [NeZero M]

attribute [local instance] finite_coordinateRing decEqFF

/-- **Per-curve bound.** `#yclSet E M · s(D') ≤ L_f(a_E, D')`. -/
theorem card_ycl_mul_sD_le (d : OrdData W L) (hM4 : 4 ≤ M) (hM : (M : F) ≠ 0) :
    Nat.card (yclSet W M) * QA.sD (tr d.w ^ 2 + 4 * -(deg d.w : ℤ)) ≤
      Lval M (RPLib.EllFq.trace W) d.f (tr d.w ^ 2 + 4 * -(deg d.w : ℤ)) := by
  have hπ : d.toOAct.ι (⟨d.b, d.f⟩ : Ord d) = piE W L := by
    rw [OrdData.toOAct_ι]; exact θ_pi d
  rw [← QA.card_units_eq_sD d.disc_neg, ← card_units_endFq d.toOAct,
    ← Lval_eq M (a := -(deg d.w : ℤ)) (x := d.b) d.htr.symm,
    ← card_ptOrd_eq_levelCount d.toOAct hM hπ, card_ptOrd W.isUnit_Δ.ne_zero hM4]
  exact Nat.mul_le_mul_left _ card_units_le_autVC

end Bound

end RamanujanPetersson.S3.DWSO


