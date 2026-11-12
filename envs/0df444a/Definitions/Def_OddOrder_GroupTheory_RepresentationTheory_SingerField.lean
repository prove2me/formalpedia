-- Prove2me | Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_SingerField
-- name    : OddOrder_GroupTheory_RepresentationTheory_SingerField
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:40:33.640182+00:00
-- url     : https://prove2.me/theorems/170ed4b3-5797-419e-b513-aded6af9dac5
-- title:
--   The Singer mechanism: irreducible abelian linear actions realize fields
-- statement:
--   If a finite abelian group $C$ acts $\mathbb{F}_p$-linearly and irreducibly on a finite $\mathbb{F}_p$-vector space $M$, formalized as $M$ being a simple module over the group algebra $\mathbb{F}_p[C]$, then $M$ carries the structure of a finite field with $C$ acting by multiplication.
--
--   The main structure is `SingerFieldData`, the witness that such an irreducible action realizes $M$ as a finite field.
--
--   The bundle also proves 5 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/RepresentationTheory/SingerField.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/SingerField.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.RepresentationTheory.Maschke
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.NumberTheory.Multiplicity
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.Order.Ring.GeomSum
import Mathlib.Algebra.Ring.GeomSum

namespace OddOrder.RepresentationTheory

universe u

variable {p : ℕ} {C M : Type u} [CommGroup C] [AddCommGroup M]
  [Module (MonoidAlgebra (ZMod p) C) M]

/-- Witness that an irreducible `𝔽_p`-linear action of an abelian group `C` on `M`
realizes `M` as a finite field with `C` acting by multiplication.

The field `K`, the additive isomorphism `e : M ≃+ K`, and the multiplicative
realization `μ : C →* Kˣ` package Peterfalvi (14.2)(a) in abstract form: `M` *is* the
additive group of a field, and the group action *is* multiplication. -/
structure SingerFieldData where
  /-- The field structure carried by `M`. -/
  K : Type u
  [field : Field K]
  [fintype : Fintype K]
  /-- `M` is additively the field `K`. -/
  e : M ≃+ K
  /-- `C` is realized inside `Kˣ` by the action. -/
  μ : C →* Kˣ
  /-- The action of `c` on `M` is multiplication by `μ c` in the field `K`. -/
  compat : ∀ (c : C) (m : M),
    e (MonoidAlgebra.of (ZMod p) C c • m) = (μ c : K) * e m

attribute [instance] SingerFieldData.field SingerFieldData.fintype

/-- In a finite cyclic group, two subgroups with trivial intersection have coprime orders.

Valid because a cyclic group has a *unique* subgroup of each order dividing the group order:
with `g = gcd(|H|, |K|)`, the `g`-torsion subgroup `ker(x ↦ x^g)` has order `gcd(|Z|, g) = g`
and lies in both `H` and `K` (each subgroup is its own `|·|`-torsion), hence in `H ⊓ K = ⊥`,
forcing `g = 1`. -/
theorem coprime_card_of_inf_eq_bot_isCyclic {Z : Type*} [CommGroup Z] [Finite Z] [IsCyclic Z]
    {H K : Subgroup Z} (hdisj : H ⊓ K = ⊥) :
    Nat.Coprime (Nat.card H) (Nat.card K) := by
  classical
  -- Each subgroup `J` is the kernel of `x ↦ x ^ |J|` (its `|J|`-torsion).
  have htorsion : ∀ J : Subgroup Z, (powMonoidHom (Nat.card J) : Z →* Z).ker = J := by
    intro J
    have hsub : J ≤ (powMonoidHom (Nat.card J) : Z →* Z).ker := by
      intro x hx
      rw [MonoidHom.mem_ker, powMonoidHom_apply]
      have hpow : ((⟨x, hx⟩ : J) ^ Nat.card J : J) = (1 : J) := pow_card_eq_one'
      have := congrArg (Subgroup.subtype J) hpow
      rw [map_pow, map_one] at this
      exact this
    have hcard : Nat.card (powMonoidHom (Nat.card J) : Z →* Z).ker = Nat.card J := by
      rw [IsCyclic.card_powMonoidHom_ker, Nat.gcd_eq_right (Subgroup.card_subgroup_dvd_card J)]
    exact (Subgroup.eq_of_le_of_card_ge hsub hcard.le).symm
  -- `ker(x ↦ x^g)` is contained in both `H` and `K`, where `g = gcd(|H|,|K|)`.
  set g := Nat.gcd (Nat.card H) (Nat.card K) with hg
  have hgH : g ∣ Nat.card H := Nat.gcd_dvd_left _ _
  have hgK : g ∣ Nat.card K := Nat.gcd_dvd_right _ _
  have hkerle : ∀ (J : Subgroup Z), g ∣ Nat.card J →
      (powMonoidHom g : Z →* Z).ker ≤ J := by
    intro J hJ
    rw [← htorsion J]
    intro x hx
    simp only [MonoidHom.mem_ker, powMonoidHom_apply] at hx ⊢
    obtain ⟨k, hk⟩ := hJ
    rw [hk, pow_mul, hx, one_pow]
  have hbot : (powMonoidHom g : Z →* Z).ker ≤ ⊥ := by
    rw [← hdisj]; exact le_inf (hkerle H hgH) (hkerle K hgK)
  -- Its order is `gcd(|Z|, g) = g` (since `g ∣ |H| ∣ |Z|`), so `g = 1`.
  have hgZ : g ∣ Nat.card Z := hgH.trans (Subgroup.card_subgroup_dvd_card H)
  have : Nat.card (powMonoidHom g : Z →* Z).ker = 1 := by
    rw [le_bot_iff.mp hbot, Subgroup.card_bot]
  rw [IsCyclic.card_powMonoidHom_ker, Nat.gcd_eq_right hgZ] at this
  exact this

section CommGroupFreeSinger

variable {p : ℕ} {E M : Type*} [Group E] [AddCommGroup M]
  [Module (MonoidAlgebra (ZMod p) E) M]

/-- For an abelian group `E`, the group algebra `𝔽_p[E]` is commutative. -/
theorem mul_comm_monoidAlgebra_of_comm (hcomm : ∀ a b : E, a * b = b * a)
    (x y : MonoidAlgebra (ZMod p) E) : x * y = y * x := by
  have hsingle : ∀ (a : E) (c : ZMod p) (z : MonoidAlgebra (ZMod p) E),
      MonoidAlgebra.single a c * z = z * MonoidAlgebra.single a c := by
    intro a c z
    induction z using MonoidAlgebra.induction_linear with
    | zero => simp
    | add f g hf hg => rw [mul_add, add_mul, hf, hg]
    | single b d =>
        rw [MonoidAlgebra.single_mul_single, MonoidAlgebra.single_mul_single,
          hcomm a b, mul_comm c d]
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg => rw [add_mul, mul_add, hf, hg]
  | single a c => exact hsingle a c y

/-- **Singer mechanism, commutativity as a hypothesis.**  If a finite group `E` acts
faithfully (`hfaith`), commutatively (`hcomm`), and irreducibly
(`IsSimpleModule (𝔽_p[E]) M`) on a finite module `M`, then `E` is cyclic and `|E| ∣ |M| - 1`.

Unlike `isCyclic_and_card_dvd_card_sub_one_of_faithful_irreducible`, this requires only a
*proof* of commutativity, not a `CommGroup` instance: the commutative `CommRing (𝔽_p[E])` is
supplied locally on top of the existing `Ring` and the Singer field is `𝔽_p[E] ⧸ I`. -/
theorem isCyclic_and_card_dvd_of_faithful_irreducible_comm [Finite E] [Finite M]
    [IsSimpleModule (MonoidAlgebra (ZMod p) E) M]
    (hcomm : ∀ a b : E, a * b = b * a)
    (hfaith : ∀ e : E, (∀ x : M, MonoidAlgebra.of (ZMod p) E e • x = x) → e = 1) :
    IsCyclic E ∧ Nat.card E ∣ Nat.card M - 1 := by
  classical
  -- `𝔽_p[E]` is commutative; equip it with a `CommRing` built on its existing `Ring` (no diamond).
  let : CommRing (MonoidAlgebra (ZMod p) E) :=
    { (inferInstance : Ring (MonoidAlgebra (ZMod p) E)) with
      mul_comm := mul_comm_monoidAlgebra_of_comm hcomm }
  -- `M` simple over `𝔽_p[E]` ⟹ `M ≅ 𝔽_p[E] ⧸ I` for a maximal ideal `I`; the quotient is a field.
  obtain ⟨I, hImax, ⟨lequiv⟩⟩ :=
    (isSimpleModule_iff_quot_maximal (R := MonoidAlgebra (ZMod p) E) (M := M)).mp ‹_›
  have : I.IsMaximal := hImax
  let : Field (MonoidAlgebra (ZMod p) E ⧸ I) := Ideal.Quotient.field I
  have : Finite (MonoidAlgebra (ZMod p) E ⧸ I) := Finite.of_equiv _ lequiv.toEquiv
  -- `μ : E ↪ Kˣ` realizes `E` inside the units of the field `K = 𝔽_p[E] ⧸ I`.
  let μ : E →* (MonoidAlgebra (ZMod p) E ⧸ I)ˣ :=
    (Units.map (Ideal.Quotient.mk I : MonoidAlgebra (ZMod p) E →+* _).toMonoidHom).comp
      (MonoidAlgebra.of (ZMod p) E).toHomUnits
  have hμinj : Function.Injective μ := by
    rw [injective_iff_map_eq_one]
    intro e he
    apply hfaith e
    intro x
    apply lequiv.injective
    have hcompat : lequiv (MonoidAlgebra.of (ZMod p) E e • x)
        = (↑(μ e) : MonoidAlgebra (ZMod p) E ⧸ I) * lequiv x := by
      rw [map_smul, Algebra.smul_def, Ideal.Quotient.algebraMap_eq]; rfl
    rw [hcompat, he, Units.val_one, one_mul]
  have : IsCyclic (MonoidAlgebra (ZMod p) E ⧸ I)ˣ := inferInstance
  have : IsCyclic μ.range := inferInstance
  refine ⟨isCyclic_of_surjective (MonoidHom.ofInjective hμinj).symm.toMonoidHom
      (MonoidHom.ofInjective hμinj).symm.surjective, ?_⟩
  -- `|E| = |μ.range| ∣ |Kˣ| = |K| - 1 = |M| - 1`.
  have hKM : Nat.card (MonoidAlgebra (ZMod p) E ⧸ I) = Nat.card M :=
    (Nat.card_congr lequiv.toEquiv).symm
  calc Nat.card E = Nat.card μ.range := Nat.card_congr (MonoidHom.ofInjective hμinj).toEquiv
    _ ∣ Nat.card (MonoidAlgebra (ZMod p) E ⧸ I)ˣ := Subgroup.card_subgroup_dvd_card _
    _ = Nat.card (MonoidAlgebra (ZMod p) E ⧸ I) - 1 :=
        Nat.card_units (α := MonoidAlgebra (ZMod p) E ⧸ I)
    _ = Nat.card M - 1 := by rw [hKM]

/-- **Singer coprimality core, `𝔽ₚ`-scalar form.**  Adds to the Singer hypotheses (`E` finite
acting faithfully, commutatively, and irreducibly on the finite `𝔽ₚ[E]`-module `M`) the condition
that only `e = 1` acts on `M` as an `𝔽ₚ`-scalar (`x ↦ n • x`).  Then `|E|` is coprime to `p - 1`.

The realization `μ : E ↪ Kˣ` (`K = 𝔽ₚ[E] ⧸ I` the Singer field) meets the prime-subfield units
`ν : 𝔽ₚ* ↪ Kˣ` only in `1`: a common unit `μ e = ν c` makes `e` act as the scalar `(c).val`, so
`hnonscalar` forces `e = 1`.  Hence `μ.range ⊓ ν.range = ⊥` in the cyclic group `Kˣ`, and
`coprime_card_of_inf_eq_bot_isCyclic` yields `Coprime |E| (p - 1)`.  The fixed-point-free bridge
`coprime_card_sub_one_of_faithful_irreducible_comm_fpf` and the `p + 1` refinement of Peterfalvi
(12.12) both specialize this by supplying the non-scalar condition from their own structure. -/
theorem coprime_card_sub_one_of_faithful_irreducible_comm_nonscalar
    [Fact p.Prime] [Finite E] [Finite M]
    [IsSimpleModule (MonoidAlgebra (ZMod p) E) M]
    (hcomm : ∀ a b : E, a * b = b * a)
    (hfaith : ∀ e : E, (∀ x : M, MonoidAlgebra.of (ZMod p) E e • x = x) → e = 1)
    (hnonscalar : ∀ e : E,
        (∃ n : ℕ, ∀ x : M, MonoidAlgebra.of (ZMod p) E e • x = n • x) → e = 1) :
    Nat.Coprime (Nat.card E) (p - 1) := by
  classical
  let : CommRing (MonoidAlgebra (ZMod p) E) :=
    { (inferInstance : Ring (MonoidAlgebra (ZMod p) E)) with
      mul_comm := mul_comm_monoidAlgebra_of_comm hcomm }
  obtain ⟨I, hImax, ⟨lequiv⟩⟩ :=
    (isSimpleModule_iff_quot_maximal (R := MonoidAlgebra (ZMod p) E) (M := M)).mp ‹_›
  have : I.IsMaximal := hImax
  let : Field (MonoidAlgebra (ZMod p) E ⧸ I) := Ideal.Quotient.field I
  have : Finite (MonoidAlgebra (ZMod p) E ⧸ I) := Finite.of_equiv _ lequiv.toEquiv
  let μ : E →* (MonoidAlgebra (ZMod p) E ⧸ I)ˣ :=
    (Units.map (Ideal.Quotient.mk I : MonoidAlgebra (ZMod p) E →+* _).toMonoidHom).comp
      (MonoidAlgebra.of (ZMod p) E).toHomUnits
  let ν : (ZMod p)ˣ →* (MonoidAlgebra (ZMod p) E ⧸ I)ˣ :=
    Units.map (algebraMap (ZMod p) (MonoidAlgebra (ZMod p) E ⧸ I)).toMonoidHom
  have hcompat : ∀ (a : E) (x : M),
      lequiv (MonoidAlgebra.of (ZMod p) E a • x)
        = (↑(μ a) : MonoidAlgebra (ZMod p) E ⧸ I) * lequiv x := by
    intro a x
    rw [map_smul, Algebra.smul_def, Ideal.Quotient.algebraMap_eq]; rfl
  have hμinj : Function.Injective μ := by
    rw [injective_iff_map_eq_one]
    intro e he
    apply hfaith e
    intro x
    apply lequiv.injective
    rw [hcompat e x, he, Units.val_one, one_mul]
  have hνinj : Function.Injective ν :=
    Units.map_injective (algebraMap (ZMod p) (MonoidAlgebra (ZMod p) E ⧸ I)).injective
  have : IsCyclic (MonoidAlgebra (ZMod p) E ⧸ I)ˣ := inferInstance
  have hdisj : μ.range ⊓ ν.range = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    rw [Subgroup.mem_inf] at hz
    obtain ⟨⟨e, he⟩, ⟨c, hc⟩⟩ := hz
    have hμν : (↑(μ e) : MonoidAlgebra (ZMod p) E ⧸ I)
        = algebraMap (ZMod p) (MonoidAlgebra (ZMod p) E ⧸ I) (c : ZMod p) := by
      have heν : μ e = ν c := he.trans hc.symm
      rw [heν, Units.coe_map]; rfl
    have hscalar : ∀ x : M, MonoidAlgebra.of (ZMod p) E e • x = (c : ZMod p).val • x := by
      intro x
      apply lequiv.injective
      rw [hcompat e x, hμν, map_nsmul, nsmul_eq_mul]
      congr 1
      conv_lhs => rw [← ZMod.natCast_zmod_val (c : ZMod p)]
      rw [map_natCast]
    have he1 : e = 1 := hnonscalar e ⟨(c : ZMod p).val, hscalar⟩
    rw [← he, he1, map_one]
  have hcop := coprime_card_of_inf_eq_bot_isCyclic hdisj
  have hcardμ : Nat.card μ.range = Nat.card E :=
    (Nat.card_congr (MonoidHom.ofInjective hμinj).toEquiv).symm
  have hcardν : Nat.card ν.range = p - 1 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hνinj).toEquiv, Nat.card_eq_fintype_card,
      ZMod.card_units_eq_totient, Nat.totient_prime (Fact.out)]
  rwa [hcardμ, hcardν] at hcop

/-- **Peterfalvi (9.7)(b), the coprimality `Coprime |E| (p-1)`.**  Adds to the Singer hypotheses
(`E` finite abelian acting faithfully, commutatively, and irreducibly on the finite `𝔽ₚ[E]`-module
`M`) a fixed-point-free additive automorphism `σ` of `M`: the only `e` whose `𝔽ₚ[E]`-action
commutes with `σ` is `e = 1`.  Then `|E|` is coprime to `p - 1`.

This is the fixed-point-free input of (9.7)(b).  An `e ∈ E` whose realization `μ e ∈ Kˣ` lands in
the prime subfield `𝔽ₚ* = algebraMap '' (ZMod p)ˣ` acts on `M` as an `𝔽ₚ`-scalar (an `nsmul`),
hence commutes with the *additive* `σ`; fixed-point-freeness then forces `e = 1`.  So `E ↪ Kˣ` and
`𝔽ₚ* ↪ Kˣ` intersect trivially in the cyclic group `Kˣ` of the Singer field `K`, and
`coprime_card_of_inf_eq_bot_isCyclic` yields `Coprime |E| (p-1)`.

In Peterfalvi's application `σ = φ(w)` is the action of a nontrivial `w ∈ W₁`: an `𝔽ₚ`-scalar is
central in `Aut(H̄)`, so it is `W₁`-fixed, and `Ū ⋊ W₁` is Frobenius, so it is trivial. -/
theorem coprime_card_sub_one_of_faithful_irreducible_comm_fpf [Fact p.Prime] [Finite E] [Finite M]
    [IsSimpleModule (MonoidAlgebra (ZMod p) E) M]
    (hcomm : ∀ a b : E, a * b = b * a)
    (hfaith : ∀ e : E, (∀ x : M, MonoidAlgebra.of (ZMod p) E e • x = x) → e = 1)
    (σ : M ≃+ M)
    (hfpf : ∀ e : E, (∀ x : M, σ (MonoidAlgebra.of (ZMod p) E e • x)
                              = MonoidAlgebra.of (ZMod p) E e • σ x) → e = 1) :
    Nat.Coprime (Nat.card E) (p - 1) :=
  -- An `𝔽ₚ`-scalar action `x ↦ n • x` commutes with the additive `σ`, so the non-scalar core
  -- applies with its scalar hypothesis discharged by fixed-point-freeness.
  coprime_card_sub_one_of_faithful_irreducible_comm_nonscalar hcomm hfaith
    (fun e ⟨n, hn⟩ => hfpf e (fun x => by rw [hn, hn, map_nsmul]))

end CommGroupFreeSinger

end OddOrder.RepresentationTheory


