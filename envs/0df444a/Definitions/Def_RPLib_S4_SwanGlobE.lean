-- Prove2me | Definitions.Def_RPLib_S4_SwanGlobE
-- name    : RPLib_S4_SwanGlobE
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T10:22:49.995291+00:00
-- url     : https://prove2.me/theorems/4f90e9b5-f6e5-4988-86ae-7da50bd26201
-- title:
--   Ramification index equals the order of the inertia group, for adic valuations
-- statement:
--   Let a finite group $G$ act on a Dedekind domain $B$ as a Galois group over a Dedekind domain $A \subseteq B$, and let $\mathfrak{P}$ be a height-one prime of $B$ over $\mathfrak{p} = \mathfrak{P} \cap A$ with finite residue field. The file proves that the ramification index $e(\mathfrak{P}/\mathfrak{p})$ equals the order of the inertia group, $$e(\mathfrak{P}/\mathfrak{p}) = |I_\mathfrak{P}|,$$ and the resulting relation $v_\mathfrak{P}(a) = e \cdot v_\mathfrak{p}(a)$ between the additive valuations on the fraction field of $A$.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (Swan conductors and wild ramification at infinity, used for Weil-type bounds of exponential sums). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   J. Neukirch, Algebraic Number Theory, Grundlehren 322, Springer (1999), Chapter I, Section 9 (Hilbert's ramification theory); J.-P. Serre, Local Fields, GTM 67, Springer (1979), doi:10.1007/978-1-4757-5673-9, Chapter I, Section 7

import Mathlib
import Definitions.Def_RPLib_S4_SwanGlobV

/-!
# S4-Swan (K2), part 14: ramification index = order of the inertia group, for adic valuations

Let `S / A` be a finite torsion-free extension of Dedekind domains with Galois group `H` (`IsGaloisGroup H A S`),
`Q` a height-one prime of `S` with finite residue field and `p = Q ∩ A`. Then the ramification index of `Q`
over `p` is `|Q.inertia H|` (`card_inertia_eq_ramificationIdxIn`), so the `Q`-adic valuation restricts to
`|Q.inertia H|` times the `p`-adic one (`intValuation_liesOver`, `valuation_liesOver`). We record this for the
additive valuations `adicAdd` of `GlobV`.
-/

set_option autoImplicit false

noncomputable section

open IsDedekindDomain WithZero

namespace RamanujanPetersson.Swan

section Core

variable {A S : Type*} [CommRing A] [IsDedekindDomain A] [CommRing S] [IsDedekindDomain S]
  [Algebra A S] [Module.Finite A S] [Module.IsTorsionFree A S]
  (H : Type*) [Group H] [Finite H] [MulSemiringAction H S] [IsGaloisGroup H A S]
  (Q : HeightOneSpectrum S) [Finite (S ⧸ Q.asIdeal)]

omit [Module.IsTorsionFree A S] [Finite (S ⧸ Q.asIdeal)] in
theorem liesOver_under : Q.asIdeal.LiesOver (Q.under A).asIdeal := ⟨rfl⟩

attribute [local instance] Ideal.Quotient.field in
/-- The ramification index of `Q` over `Q ∩ A` is the order of the inertia group of `Q` in `H`. -/
theorem ramificationIdx'_under_eq_card :
    (Q.under A).asIdeal.ramificationIdx' Q.asIdeal = Nat.card (Q.asIdeal.inertia H) := by
  have := liesOver_under (A := A) Q
  have : (Q.under A).asIdeal.IsMaximal := (Q.under A).isMaximal
  have : Finite (A ⧸ (Q.under A).asIdeal) :=
    Finite.of_injective (algebraMap (A ⧸ (Q.under A).asIdeal) (S ⧸ Q.asIdeal)) (RingHom.injective _)
  have : Finite (Q.under A).asIdeal.ResidueField :=
    Finite.of_surjective _ (Ideal.bijective_algebraMap_quotient_residueField (Q.under A).asIdeal).2
  rw [Ideal.card_inertia_eq_ramificationIdxIn (G := H) (Q.under A).asIdeal Q.asIdeal,
    Ideal.ramificationIdxIn_eq_ramificationIdx (Q.under A).asIdeal Q.asIdeal H,
    Ideal.ramificationIdx'_eq_ramificationIdx (Q.under A).asIdeal Q.asIdeal (Q.under A).ne_bot]

theorem intValuation_algebraMap_eq_pow (c : A) :
    Q.intValuation (algebraMap A S c) =
      (Q.under A).intValuation c ^ Nat.card (Q.asIdeal.inertia H) := by
  have := liesOver_under (A := A) Q
  rw [← ramificationIdx'_under_eq_card (A := A) H Q]
  exact (HeightOneSpectrum.intValuation_liesOver (Q.under A) Q c).symm

variable {L : Type*} [Field L] [Algebra S L] [IsFractionRing S L]

/-- Additive form on `A`: `v_Q(c) = |I| · k` for a nonzero `c ∈ A`. -/
theorem exists_adicAdd_algebraMap_eq (c : A) (hc : c ≠ 0) :
    ∃ k : ℤ, adicAdd Q (algebraMap S L (algebraMap A S c)) =
      (((Nat.card (Q.asIdeal.inertia H) : ℤ) * k : ℤ) : WithTop ℤ) := by
  have hc' : algebraMap S L (algebraMap A S c) ≠ 0 := by
    rw [map_ne_zero_iff _ (IsFractionRing.injective S L)]
    exact (FaithfulSMul.algebraMap_injective A S).ne_iff' (map_zero _) |>.2 hc
  refine ⟨-log ((Q.under A).intValuation c), ?_⟩
  rw [adicAdd_apply, negLogV_of_ne Q hc', HeightOneSpectrum.valuation_of_algebraMap,
    intValuation_algebraMap_eq_pow H Q c, log_pow, nsmul_eq_mul]
  congr 1
  ring

variable {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [IsScalarTower A S L]

/-- Additive form on `K = Frac A`: `v_Q(x) = |I| · v_p(x)`. -/
theorem adicAdd_algebraMap_eq (x : K) (m : ℤ) (hm : adicAdd (Q.under A) x = m) :
    adicAdd Q (algebraMap K L x) =
      (((Nat.card (Q.asIdeal.inertia H) : ℤ) * m : ℤ) : WithTop ℤ) := by
  have hx : x ≠ 0 := by
    rintro rfl
    rw [AddValuation.map_zero] at hm
    exact WithTop.top_ne_coe hm
  have hx' : algebraMap K L x ≠ 0 := (map_ne_zero _).2 hx
  have := liesOver_under (A := A) Q
  rw [adicAdd_apply, negLogV_of_ne (L := K) _ hx] at hm
  have hm' : -log ((Q.under A).valuation K x) = m := WithTop.coe_inj.1 hm
  rw [adicAdd_apply, negLogV_of_ne Q hx', ← HeightOneSpectrum.valuation_liesOver L (Q.under A) Q x,
    ramificationIdx'_under_eq_card (A := A) H Q, log_pow, nsmul_eq_mul, ← hm']
  congr 1
  ring

end Core

end RamanujanPetersson.Swan


