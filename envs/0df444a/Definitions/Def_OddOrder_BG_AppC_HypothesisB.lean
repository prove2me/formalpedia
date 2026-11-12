-- Prove2me | Definitions.Def_OddOrder_BG_AppC_HypothesisB
-- name    : OddOrder_BG_AppC_HypothesisB
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:47:07.913084+00:00
-- url     : https://prove2.me/theorems/a417f0a2-b6b7-4464-92d8-5441626ca9ce
-- title:
--   Bender–Glauberman Appendix C: hypotheses (A) and (B) of Theorem C
-- statement:
--   Formalizes the hypotheses of Theorem C in Bender–Glauberman Appendix C, §1 (p. 145). Let $p,q$ be primes satisfying condition (A), $\gcd((p^q-1)/(p-1),p-1)=1$; let $P$ be the additive group of $\mathbb{F}_{p^q}$ and $U$ the norm-one subgroup of $\mathbb{F}_{p^q}^\times$, acting on $P$ by multiplication, giving the semidirect product $H=PU$ with prime-field line $P_0$.
--
--   Main definitions: `conditionA` (the cyclotomic condition), `primeLine` ($P_0\le P$), `primeLineElement` and `primeLineGenerator` (the elements of $P_0$ for a scalar and its distinguished generator), `HypothesisBAbstract` (Hypothesis (B), in the book's abstract form) and `FieldNormalizerData` (Hypothesis (B) together with condition (A)).
--
--   The bundle also proves 5 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/AppC_HypothesisB.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/AppC_HypothesisB.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_AppC_NormSet

namespace OddOrder.BG.AppC

open scoped Pointwise

/-- **BG Appendix C, Condition (A)**: the cyclotomic factor attached to
`F_{p^q}` is coprime to `p - 1`.

By Remark (I) this is equivalent to `q ∤ p - 1` (`NormSet.conditionA_iff_not_dvd`). -/
def conditionA (p q : ℕ) : Prop :=
  Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1)

/-- **BG Appendix C**, the prime-field line `P₀ ≤ P`: the image in `P = 𝔽_{p^q}` of the additive
group of `𝔽_p`, i.e. the `𝔽_p`-span of `1`, viewed inside `H = P ⋊ U`. -/
noncomputable def primeLine (p q : ℕ) [Fact p.Prime] :
    Subgroup (NormSet.normOneFrobeniusGroup p q) :=
  NormSet.normOneFrobeniusSubspaceKernel p q
    (Submodule.span (ZMod p) ({(1 : GaloisField p q)} : Set (GaloisField p q)))

/-- The `𝔽_p`-span of `1` in `𝔽_{p^q}` is the prime field, of cardinality `p`. -/
theorem card_span_singleton_one (p q : ℕ) [Fact p.Prime] :
    Nat.card (Submodule.span (ZMod p) ({(1 : GaloisField p q)} : Set (GaloisField p q))) = p := by
  have hinj : Function.Injective
      (LinearMap.toSpanSingleton (ZMod p) (GaloisField p q) 1) := by
    intro a b hab
    have : (algebraMap (ZMod p) (GaloisField p q)) a =
        (algebraMap (ZMod p) (GaloisField p q)) b := by
      simpa [LinearMap.toSpanSingleton_apply, Algebra.smul_def] using hab
    exact FaithfulSMul.algebraMap_injective (ZMod p) (GaloisField p q) this
  rw [LinearMap.span_singleton_eq_range]
  have : Nat.card (LinearMap.range (LinearMap.toSpanSingleton (ZMod p) (GaloisField p q) 1)) =
      Nat.card (ZMod p) := (Nat.card_congr (Equiv.ofInjective _ hinj)).symm
  rw [this, Nat.card_eq_fintype_card, ZMod.card]

/-- **`|P₀| = p`**: the prime-field line has order `p`.  This is what the Section 16 development
used to take from its own hypothesis (`p = |W₂|`); it is in fact a consequence of the setup, since
`P₀` is the image of the prime field `𝔽_p` inside `P = 𝔽_{p^q}`. -/
theorem card_primeLine (p q : ℕ) [Fact p.Prime] : Nat.card (primeLine p q) = p := by
  rw [primeLine, NormSet.normOneFrobeniusSubspaceKernel,
    Subgroup.card_map_of_injective SemidirectProduct.inl_injective]
  exact card_span_singleton_one p q

/-- The element of the prime-field line `P₀ ≤ P ≤ H` corresponding to a scalar `c : ZMod p`,
i.e. `algebraMap c ∈ 𝔽_p ⊆ 𝔽_{p^q}` read inside the additive kernel. -/
noncomputable def primeLineElement (p q : ℕ) [Fact p.Prime] (c : ZMod p) :
    NormSet.normOneFrobeniusGroup p q :=
  SemidirectProduct.inl (Multiplicative.ofAdd (algebraMap (ZMod p) (GaloisField p q) c))

/-- The distinguished nonidentity element of the prime-field line `P₀`, corresponding to
`1 : 𝔽_{p^q}` in BG Appendix C. -/
noncomputable def primeLineGenerator (p q : ℕ) [Fact p.Prime] :
    NormSet.normOneFrobeniusGroup p q :=
  SemidirectProduct.inl (Multiplicative.ofAdd (1 : GaloisField p q))

/-- **BG Appendix C, Hypothesis (B)** (p. 145), in the book's `p, q, G`-abstract form: no
Peterfalvi Section 16 configuration anywhere in the statement.

Verbatim: *"There is a monomorphism `σ : H → G`, a finite abelian `p'`-subgroup `Q` of `G`, and an
element `y ∈ Q` such that `σ(P₀)` normalizes `Q` and `σ(P₀)^y` normalizes `U`."*  Here
`H = P ⋊ U` is `NormSet.normOneFrobeniusGroup p q`, `P₀` is `primeLine p q`, and `U` is
identified with its image `σ(U)` inside `G` (Remark (VI)).

The conjugation is written `MulAut.conj y • σ(P₀) = y σ(P₀) y⁻¹`; since `Q` is a subgroup,
feeding it `y⁻¹` recovers the book's `σ(P₀)^y = y⁻¹ σ(P₀) y` verbatim, so the two readings define
the same hypothesis.

The concrete Peterfalvi Section 16 instance of (B) along the Feit--Thompson spine is
`OddOrder.Peterfalvi.S16.FieldNormalizerData`.  What is still missing to run Theorem C off the
abstract form is the implication *(B) ⟹ `hrel`* (BG Lemma C.3), currently available only through
Section 16; see issue 0151.

`hypothesisBAbstract_sl2` (in `OddOrder.BG.AppC_SL2Example`) is the book's Remark (II) witness,
showing this hypothesis is satisfiable (`p = 2`, `G = SL(2, 2^q)`). -/
structure HypothesisBAbstract (p q : ℕ) [Fact p.Prime] (G : Type*) [Group G] where
  /-- The monomorphism `σ : H = P ⋊ U → G`. -/
  sigma : NormSet.normOneFrobeniusGroup p q →* G
  /-- `σ` is a monomorphism. -/
  sigma_injective : Function.Injective sigma
  /-- The finite abelian `p'`-subgroup `Q ≤ G`. -/
  Q : Subgroup G
  /-- `Q` is finite. -/
  Q_finite : Finite Q
  /-- `Q` is abelian. -/
  Q_commutative : IsMulCommutative Q
  /-- `Q` is a `p'`-group. -/
  Q_pPrime : ¬ p ∣ Nat.card Q
  /-- The distinguished element `y ∈ Q`. -/
  y : G
  /-- `y` lies in `Q`. -/
  y_mem_Q : y ∈ Q
  /-- `σ(P₀)` normalizes `Q`. -/
  primeLine_normalizes_Q :
    (primeLine p q).map sigma ≤ Subgroup.normalizer (Q : Set G)
  /-- `σ(P₀)^y` normalizes `σ(U)`. -/
  primeLine_conj_normalizes_U :
    MulAut.conj y • ((primeLine p q).map sigma) ≤
      Subgroup.normalizer
        (((NormSet.normOneFrobeniusComplement p q).map sigma : Subgroup G) : Set G)

section Data

variable {p q : ℕ} [Fact p.Prime] {G : Type*} [Group G]

/-- **Field-normalizer data**: hypothesis (B) together with condition (A), with the three
subgroups `σ(P)`, `σ(U)`, `σ(P₀)` given names.

This is the shape in which the Lemma C.1--C.3 development consumes Theorem C's hypotheses: the
proofs constantly refer to the ambient subgroups `P = σ(P)`, `U = σ(U)` and `W₂ = σ(P₀)` of `G`,
so it is convenient to carry them as fields with their defining equations rather than to unfold
`Subgroup.map` everywhere.

The packaging adds **nothing**: `HypothesisBAbstract.toFieldNormalizerData` builds it from (B)
and (A) alone, taking the three subgroups to be literally the images (all three equations are
`rfl`).  So a `FieldNormalizerData` is exactly "(A) and (B)". -/
structure FieldNormalizerData (p q : ℕ) [Fact p.Prime] (G : Type*) [Group G]
    extends HypothesisBAbstract p q G where
  /-- The image `P = σ(P)` of the additive kernel. -/
  P : Subgroup G
  /-- The image `U = σ(U)` of the norm-one complement. -/
  U : Subgroup G
  /-- The image `W₂ = σ(P₀)` of the prime-field line. -/
  W2 : Subgroup G
  /-- `P` is the image of the additive kernel. -/
  sigma_P_eq_P : (NormSet.normOneFrobeniusKernel p q).map sigma = P
  /-- `U` is the image of the norm-one complement. -/
  sigma_U_eq_U : (NormSet.normOneFrobeniusComplement p q).map sigma = U
  /-- `W₂` is the image of the prime-field line. -/
  sigma_P0_eq_W2 : (primeLine p q).map sigma = W2
  /-- `q` is prime (the standing hypothesis of Theorem C). -/
  q_prime : q.Prime
  /-- `p` is odd.  By **Remark (V)** ("by (A), we can assume `p` and `q` are odd") this costs
  nothing: `le_of_conditionA_of_not_odd` disposes of the even case outright. -/
  p_odd : Odd p
  /-- Condition (A). -/
  cyclotomic_coprime : conditionA p q

namespace FieldNormalizerData

/-- `W₂ = σ(P₀)` normalizes `Q`: clause (B) read through `sigma_P0_eq_W2`. -/
theorem W2_normalizes_Q (data : FieldNormalizerData p q G) :
    data.W2 ≤ Subgroup.normalizer (data.Q : Set G) := by
  rw [← data.sigma_P0_eq_W2]
  exact data.primeLine_normalizes_Q

/-- **`|W₂| = p`**: the transported prime line has order `p`, because `W₂ = σ(P₀)`, `σ` is
injective and `|P₀| = p` (`card_primeLine`).  The Section 16 development previously took this
from its own hypothesis field `p = |W₂|`; it is a consequence of (B). -/
theorem card_W2 (data : FieldNormalizerData p q G) : Nat.card data.W2 = p := by
  rw [← data.sigma_P0_eq_W2, Subgroup.card_map_of_injective data.sigma_injective]
  exact card_primeLine p q

/-- `W₂^y` normalizes `U`: clause (B) read through `sigma_P0_eq_W2` and `sigma_U_eq_U`. -/
theorem W2_conj_y_normalizes_U (data : FieldNormalizerData p q G) :
    MulAut.conj data.y • data.W2 ≤ Subgroup.normalizer (data.U : Set G) := by
  rw [← data.sigma_P0_eq_W2, ← data.sigma_U_eq_U]
  exact data.primeLine_conj_normalizes_U

end FieldNormalizerData

end Data

end OddOrder.BG.AppC


