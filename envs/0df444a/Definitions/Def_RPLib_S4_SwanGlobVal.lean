-- Prove2me | Definitions.Def_RPLib_S4_SwanGlobVal
-- name    : RPLib_S4_SwanGlobVal
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T10:32:26.444649+00:00
-- url     : https://prove2.me/theorems/10a963e9-d885-4412-a35f-6b76bf5349d3
-- title:
--   The valuation condition for subgroups of an inertia group
-- statement:
--   For a finite group acting on a Dedekind domain $B$ and a height-one prime $\mathfrak{P}$ with inertia group $I$, the file shows that every subgroup $H \le I$ yields quotient local data: the $\mathfrak{P}$-adic valuation restricted to the $H$-fixed field is $|H|$ times a normalised valuation with a uniformiser fixed by $H$. This is the valuation hypothesis required to apply the quotient formula to inertia groups of Galois extensions of Dedekind domains.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (Swan conductors and wild ramification at infinity, used for Weil-type bounds of exponential sums). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   J.-P. Serre, Local Fields, GTM 67, Springer (1979), doi:10.1007/978-1-4757-5673-9, Chapter IV; J. Neukirch, Algebraic Number Theory, Grundlehren 322, Springer (1999), Chapter I, Section 9 (Hilbert's ramification theory)

import Mathlib
import Definitions.Def_RPLib_S4_SwanGlobE
import Definitions.Def_RPLib_S4_SwanGlobF
import Definitions.Def_RPLib_S4_SwanGlobT

/-!
# S4-Swan (K2), part 16: the valuation condition for subgroups of an inertia group

For `S / R` finite Dedekind with Galois group `G`, `Q` a height-one prime of `S` with finite residue field, and
`H ≤ Q.inertia G`, every nonzero `H`-fixed `x ∈ L = Frac S` has `v_Q(x) ∈ |H| ℤ`
(`exists_adicAdd_fixed_eq`): write `x = c1 / c2` with `c_i ∈ S^H` (`exists_fixed_mul_eq`), and use that
`S^H` is Dedekind (`isDedekindDomain_fixed`) with `e(Q | Q ∩ S^H) = |Q.inertia H| = |H|` (`GlobE`).
For the local data `inertiaLocData` this is the `val` condition of `QData` and of `Tower`
(`inertiaLocData_val`), and the norm of the uniformizer is quotient data (`inertiaQData`).
-/

set_option autoImplicit false

noncomputable section

open IsDedekindDomain

namespace RamanujanPetersson.Swan

namespace LocData

variable {G L : Type*} [Group G] [Field L] [MulSemiringAction G L] (D : LocData G L)

/-- Given the valuation condition, the norm `∏_{h ∈ H} h • ϖ` of the uniformizer is quotient data. -/
theorem qdata_prod (H : Subgroup G) [Fintype H]
    (hval : ∀ x : L, (∀ h ∈ H, h • x = x) → x ≠ 0 →
      ∃ k : ℤ, D.v x = (((Fintype.card H : ℤ) * k : ℤ) : WithTop ℤ)) :
    D.QData H (∏ h : H, (h : G) • D.ϖ) where
  fix g hg := by
    rw [Finset.smul_prod']
    exact Fintype.prod_equiv (Equiv.mulLeft (⟨g, hg⟩ : H)) _ _ (fun h => by
      rw [Equiv.coe_mulLeft, Subgroup.coe_mul, Subgroup.coe_mk, mul_smul])
  v_eq := by
    rw [D.v_prod]
    simp only [D.v_smul, D.v_ϖ]
    rw [Finset.sum_const, Finset.card_univ, nsmul_one]
  val := hval

end LocData

section Val

variable {R S : Type*} [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]
  [Algebra R S] [Module.Finite R S]
  {G : Type*} [Group G] [MulSemiringAction G S] [IsGaloisGroup G R S] [Finite G]
  {L : Type*} [Field L] [Algebra S L] [IsFractionRing S L] [MulSemiringAction G L]
  (hc : ∀ (σ : G) (s : S), σ • algebraMap S L s = algebraMap S L (σ • s))
  (Q : HeightOneSpectrum S) [Finite (S ⧸ Q.asIdeal)]

include R hc in
/-- For `H ≤ Q.inertia G`, `v_Q(x) ∈ |H| ℤ` for every nonzero `H`-fixed `x ∈ L`. -/
theorem exists_adicAdd_fixed_eq (H : Subgroup G) (hH : H ≤ Q.asIdeal.inertia G) (x : L)
    (hx : ∀ h ∈ H, h • x = x) (hx0 : x ≠ 0) :
    ∃ k : ℤ, adicAdd Q x = (((Nat.card H : ℤ) * k : ℤ) : WithTop ℤ) := by
  obtain ⟨c1, c2, h1, h2, hc2, hx12⟩ := exists_fixed_mul_eq hc H x hx
  let A := FixedPoints.subalgebra R S H
  haveI : IsDedekindDomain A := isDedekindDomain_fixed H
  haveI : Module.Finite A S := finite_fixed H
  have hI : Nat.card (Q.asIdeal.inertia H) = Nat.card H := by
    have : Q.asIdeal.inertia H = ⊤ := by
      ext σ
      simp only [Subgroup.mem_top, iff_true]
      exact hH σ.2
    rw [this, Subgroup.card_top]
  have hinj := IsFractionRing.injective S L
  have hc1 : c1 ≠ 0 := by
    rintro rfl
    rw [map_zero] at hx12
    exact hx0 ((mul_eq_zero.1 hx12).resolve_right ((map_ne_zero_iff _ hinj).2 hc2))
  let a1 : A := ⟨c1, (mem_fixedSubalgebra_iff H c1).2 fun h => h1 h h.2⟩
  let a2 : A := ⟨c2, (mem_fixedSubalgebra_iff H c2).2 fun h => h2 h h.2⟩
  obtain ⟨k1, hk1⟩ := exists_adicAdd_algebraMap_eq (L := L) H Q a1
    (fun h => hc1 (congrArg Subtype.val h))
  obtain ⟨k2, hk2⟩ := exists_adicAdd_algebraMap_eq (L := L) H Q a2
    (fun h => hc2 (congrArg Subtype.val h))
  rw [hI] at hk1 hk2
  change adicAdd Q (algebraMap S L c1) = _ at hk1
  change adicAdd Q (algebraMap S L c2) = _ at hk2
  have hv := congrArg (adicAdd Q) hx12
  rw [AddValuation.map_mul, hk1, hk2] at hv
  obtain ⟨t, ht⟩ : ∃ t : ℤ, adicAdd Q x = t := by
    induction h : adicAdd Q x with
    | top => exact absurd ((AddValuation.top_iff _).1 h) hx0
    | coe t => exact ⟨t, rfl⟩
  rw [ht, ← WithTop.coe_add, WithTop.coe_inj] at hv
  refine ⟨k1 - k2, ?_⟩
  rw [ht, WithTop.coe_inj]
  linarith [mul_sub (Nat.card H : ℤ) k1 k2]

include R hc in
/-- The `val` condition of `QData`/`Tower` for the inertia local data and any subgroup `H` of the inertia. -/
theorem inertiaLocData_val (H : Subgroup (Q.asIdeal.inertia G)) [Fintype H] (x : L)
    (hx : ∀ h ∈ H, h • x = x) (hx0 : x ≠ 0) :
    ∃ k : ℤ, (inertiaLocData (R := R) hc Q).v x = (((Fintype.card H : ℤ) * k : ℤ) : WithTop ℤ) := by
  obtain ⟨k, hk⟩ := exists_adicAdd_fixed_eq (R := R) hc Q (H.map (Q.asIdeal.inertia G).subtype)
    (Subgroup.map_subtype_le H) x (by
      rintro _ ⟨h, hh, rfl⟩
      exact hx h hh) hx0
  refine ⟨k, ?_⟩
  rw [inertiaLocData_v, hk, Subgroup.card_map_of_injective (Subgroup.subtype_injective _),
    Nat.card_eq_fintype_card]

/-- The norm of the uniformizer is quotient data for any subgroup of the inertia group. -/
theorem inertiaQData (H : Subgroup (Q.asIdeal.inertia G)) [Fintype H] :
    (inertiaLocData (R := R) hc Q).QData H
      (∏ h : H, (h : Q.asIdeal.inertia G) • (inertiaLocData (R := R) hc Q).ϖ) :=
  LocData.qdata_prod _ H (inertiaLocData_val (R := R) hc Q H)

end Val

end RamanujanPetersson.Swan


