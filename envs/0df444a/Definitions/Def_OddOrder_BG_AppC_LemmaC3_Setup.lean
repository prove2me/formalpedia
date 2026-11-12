-- Prove2me | Definitions.Def_OddOrder_BG_AppC_LemmaC3_Setup
-- name    : OddOrder_BG_AppC_LemmaC3_Setup
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:50:26.294221+00:00
-- url     : https://prove2.me/theorems/fd27e497-3202-4d9e-a7ce-8f8ad35b251c
-- title:
--   Bender–Glauberman Appendix C, Lemma C.3: the transported configuration
-- statement:
--   Sets up the configuration in Bender–Glauberman Appendix C, Lemma C.3 (§3, pp. 148–152). Under hypothesis (B) the monomorphism $\sigma:H=P\rtimes U\to G$ transports the concrete Frobenius group into $G$. The file develops the resulting configuration: the element $s=\sigma(1)\in\sigma(P_0)$, the isomorphism $U\cong\sigma(U)$, the decomposition $\sigma(H)=PU$ with $P\cap U=1$, that $P$ is characteristic in $PU$, and the irreducibility bridge.
--
--   Main definitions: `normSetGeneratorRelation` (the norm relation from the generator relation), `normSetTwistedNormOneStep` (Step 4 narrowed to the norm-one units), `s` (the BG element $s\in P_0^\#$ transported to $G$), and finiteness of the transported prime line $W_2=\sigma(P_0)$ of order $p$ and of $Q$ (`finite_W2`, `finite_Q`, `finite_W2_sup_Q`).
--
--   The bundle also proves 10 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/AppC_LemmaC3_Setup.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/AppC_LemmaC3_Setup.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_AppC_FrobeniusBasics

namespace OddOrder.BG.AppC

open scoped Pointwise

/-- **BG Appendix C, Lemma C.3**: the norm relation produced by the generator-relation argument.
For every `a` in the norm set `E`, `N(2a − 1) = 1`; BG then converts this finite-field statement
into `a⁻¹ ∈ E`. -/
def normSetGeneratorRelation (p q : ℕ) [Fact p.Prime] : Prop :=
  ∀ a : GaloisField p q, a ∈ NormSet.normSetE p q →
    NormSet.normN p q ((2 : GaloisField p q) * a - 1) = 1

/-- **BG Appendix C, Lemma C.3, Step 4**, narrowed to the norm-one unit group `U`.  This matches
the actual BG Step 4 action by conjugation with `t`; no extension to all of `𝔽_{p^q}ˣ` is
required. -/
def normSetTwistedNormOneStep (p q : ℕ) [Fact p.Prime] : Prop :=
  ∃ φ : MulAut (NormSet.normOneUnits p q),
    φ ^ p = 1 ∧ NormSet.normSetETwistedNormOneStep p q φ

variable {p q : ℕ} [Fact p.Prime] {G : Type*} [Group G]

namespace FieldNormalizerData

/-- The BG element `s ∈ P₀#`, transported to `G` through the concrete
field-normalizer monomorphism. -/
noncomputable def s (data : FieldNormalizerData p q G) : G :=
  data.sigma (primeLineGenerator p q)

/-- The transported element `s` lies in Peterfalvi's subgroup `W₂ = σ(P₀)`. -/
theorem s_mem_W2 (data : FieldNormalizerData p q G) :
    data.s ∈ data.W2 := by
  rw [← data.sigma_P0_eq_W2]
  exact ⟨primeLineGenerator p q,
    primeLineGenerator_mem p q, rfl⟩

/-- The transported element `s` is nontrivial. -/
theorem s_ne_one (data : FieldNormalizerData p q G) :
    data.s ≠ 1 := by
  intro hs
  exact primeLineGenerator_ne_one p q
    (data.sigma_injective (by simpa [s] using hs))

/-- The transported prime-line generator has `p`-th power equal to `1`. -/
theorem s_pow_p_eq_one (data : FieldNormalizerData p q G) :
    data.s ^ p = 1 := by
  simpa [s] using congrArg data.sigma (primeLineGenerator_pow_p p q)

/-- The transported generator `s` has exact order `p`. -/
theorem s_orderOf_eq_p (data : FieldNormalizerData p q G) :
    orderOf data.s = p := by
  have hdiv : orderOf data.s ∣ p :=
    orderOf_dvd_of_pow_eq_one data.s_pow_p_eq_one
  rcases (Fact.out : Nat.Prime p).eq_one_or_self_of_dvd (orderOf data.s) hdiv with h | h
  · exact False.elim (data.s_ne_one (orderOf_eq_one_iff.mp h))
  · exact h

/-- The transported prime line `W₂ = σ(P₀)` is finite, of order `p`.  Together with the
hypothesis (B) field `Q_finite` this is all the finiteness the Lemma C.3 development needs --
in particular the ambient group `G` is never assumed finite. -/
instance finite_W2 (data : FieldNormalizerData p q G) : Finite data.W2 :=
  Nat.finite_of_card_ne_zero (by rw [data.card_W2]; exact (Fact.out : Nat.Prime p).ne_zero)

/-- Hypothesis (B)'s `Q` is finite, as an instance. -/
instance finite_Q (data : FieldNormalizerData p q G) : Finite data.Q := data.Q_finite

/-- The underlying set of `W₂` is finite. -/
theorem setFinite_W2 (data : FieldNormalizerData p q G) : (↑data.W2 : Set G).Finite :=
  Set.finite_coe_iff.mp (finite_W2 data)

/-- The underlying set of `Q` is finite (hypothesis (B)). -/
theorem setFinite_Q (data : FieldNormalizerData p q G) : (↑data.Q : Set G).Finite :=
  Set.finite_coe_iff.mp (finite_Q data)

/-- `W₂Q` is finite: `W₂` normalizes `Q` by (B), so the join is the product set `W₂ · Q` of two
finite sets.  This is what lets the Step 3 Sylow argument run without assuming `G` finite. -/
theorem setFinite_W2_sup_Q (data : FieldNormalizerData p q G) :
    ((data.W2 ⊔ data.Q : Subgroup G) : Set G).Finite := by
  rw [Subgroup.coe_mul_of_left_le_normalizer_right data.W2 data.Q data.W2_normalizes_Q]
  exact data.setFinite_W2.mul data.setFinite_Q

instance finite_W2_sup_Q (data : FieldNormalizerData p q G) :
    Finite ↥(data.W2 ⊔ data.Q) := data.setFinite_W2_sup_Q.to_subtype

/-- The transported prime line `W₂ = σ(P₀)` is generated by the distinguished
nonidentity element `s`.  This is the `P₀ = ⟨s⟩` input in BG Appendix C. -/
theorem W2_eq_zpowers_s (data : FieldNormalizerData p q G) :
    data.W2 = Subgroup.zpowers data.s := by
  have hsle : Subgroup.zpowers data.s ≤ data.W2 :=
    Subgroup.zpowers_le.mpr data.s_mem_W2
  have hcard : Nat.card ↥data.W2 ≤ Nat.card ↥(Subgroup.zpowers data.s) := by
    rw [Nat.card_zpowers, data.s_orderOf_eq_p, data.card_W2]
  exact (Subgroup.eq_of_le_of_card_ge hsle hcard).symm

/-- The concrete norm-one complement transported through `σ` onto Peterfalvi's
subgroup `U`. -/
noncomputable def normOneUnitsToU (data : FieldNormalizerData p q G) :
    NormSet.normOneUnits p q →* data.U :=
  { toFun := fun u =>
      ⟨data.sigma (SemidirectProduct.inr u), by
        rw [← data.sigma_U_eq_U]
        exact ⟨SemidirectProduct.inr u, ⟨u, rfl⟩, rfl⟩⟩
    map_one' := by
      ext
      simp
    map_mul' := by
      intro u v
      ext
      simp }

/-- The transported norm-one complement map is injective. -/
theorem normOneUnitsToU_injective (data : FieldNormalizerData p q G) :
    Function.Injective data.normOneUnitsToU := by
  intro u v h
  have hsig : data.sigma (SemidirectProduct.inr u) = data.sigma (SemidirectProduct.inr v) :=
    congrArg Subtype.val h
  exact SemidirectProduct.inr_injective (data.sigma_injective hsig)

/-- The transported norm-one complement map is onto Peterfalvi's `U`. -/
theorem normOneUnitsToU_surjective (data : FieldNormalizerData p q G) :
    Function.Surjective data.normOneUnitsToU := by
  intro u
  have hu : (u : G) ∈ (NormSet.normOneFrobeniusComplement p q).map data.sigma := by
    rw [data.sigma_U_eq_U]
    exact u.property
  rcases hu with ⟨x, hxU, hx⟩
  rcases hxU with ⟨u0, rfl⟩
  refine ⟨u0, ?_⟩
  ext
  exact hx

/-- The concrete norm-one unit group is isomorphic to Peterfalvi's subgroup `U`
through the field-normalizer embedding. -/
noncomputable def normOneUnitsEquivU (data : FieldNormalizerData p q G) :
    NormSet.normOneUnits p q ≃* data.U :=
  MulEquiv.ofBijective data.normOneUnitsToU
    ⟨data.normOneUnitsToU_injective, data.normOneUnitsToU_surjective⟩

end FieldNormalizerData

end OddOrder.BG.AppC


