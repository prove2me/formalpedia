-- Prove2me | Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CyclotomicGaloisAction
-- name    : OddOrder_GroupTheory_RepresentationTheory_CyclotomicGaloisAction
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:00:58.114345+00:00
-- url     : https://prove2.me/theorems/4135ea0c-c47e-40d6-8215-9a80e901727d
-- title:
--   Peterfalvi (1.9): cyclotomic Galois automorphisms acting on character values
-- statement:
--   Formalizes Peterfalvi (1.9) (§1, p. 6). Suppose $|G|=n=ab$ with $a,b$ coprime. (a) Every automorphism of $\mathbb{Q}_a$ extends to an automorphism of $\mathbb{Q}_n$ fixing $\mathbb{Q}_b$; (b) for a character $\chi$ of $G$ and $k$ coprime to $a$, there is an automorphism $v$ of $\mathbb{Q}_n$ with $\chi^v(g)=\chi(g^k)$ when the order of $g$ divides $a$, and $\chi^v(g)=\chi(g)$ when the order of $g$ is prime to $a$.
--
--   The bundle introduces one declaration, `exists_complexRingEquiv_extends` (every automorphism of a subfield of $\mathbb{C}$ extends to a ring automorphism of $\mathbb{C}$), with the rest being lemmas such as eigenvalues of finite-order endomorphisms being roots of unity and traces of finite-order endomorphisms under ring homomorphisms.
--
--   The bundle also proves 8 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/RepresentationTheory/CyclotomicGaloisAction.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/CyclotomicGaloisAction.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_GaloisCharacter
import Mathlib.Algebra.DirectSum.LinearMap
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.FieldTheory.IsAlgClosed.Classification
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.LinearAlgebra.Semisimple
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.RootsOfUnity.Complex

namespace OddOrder.RepresentationTheory

open Polynomial

section FiniteOrderTrace

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

private theorem pow_apply_of_mem_eigenspace {f : Module.End ℂ V} {μ : ℂ} {x : V}
    (hx : x ∈ f.eigenspace μ) (j : ℕ) : (f ^ j) x = μ ^ j • x := by
  induction j with
  | zero => simp
  | succ j ih =>
      have hfx : f x = μ • x := Module.End.mem_eigenspace_iff.mp hx
      calc (f ^ (j + 1)) x = (f ^ j) (f x) := by rw [pow_succ, Module.End.mul_apply]
        _ = μ • (f ^ j) x := by rw [hfx, map_smul]
        _ = μ ^ (j + 1) • x := by rw [ih, smul_smul, pow_succ, mul_comm]

/-- Eigenvalues of a finite-order endomorphism are roots of unity. -/
theorem pow_eq_one_of_eigenspace_ne_bot {f : Module.End ℂ V} {m : ℕ}
    (hf : f ^ m = 1) {μ : ℂ} (hμ : f.eigenspace μ ≠ ⊥) : μ ^ m = 1 := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hμ
  have h1 : (f ^ m) x = x := by rw [hf, Module.End.one_apply]
  have h2 : (f ^ m) x = μ ^ m • x := pow_apply_of_mem_eigenspace hx m
  have hsub : (μ ^ m - 1) • x = 0 := by
    rw [sub_smul, one_smul, ← h2, h1, sub_self]
  rcases smul_eq_zero.mp hsub with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hx0

variable [FiniteDimensional ℂ V]

/-- **Trace of a finite-order endomorphism under a ring homomorphism.**  If `f ^ m = 1`
and `σ : ℂ →+* ℂ` acts as `(· ^ k)` on `m`-th roots of unity, then
`σ (trace f) = trace (f ^ k)`. -/
theorem map_trace_of_pow_eq_one (σ : ℂ →+* ℂ) {f : Module.End ℂ V} {m k : ℕ}
    (hm : m ≠ 0) (hf : f ^ m = 1)
    (hσ : ∀ ζ : ℂ, ζ ^ m = 1 → σ ζ = ζ ^ k) :
    σ (LinearMap.trace ℂ V f) = LinearMap.trace ℂ V (f ^ k) := by
  classical
  -- `f` is semisimple: it is annihilated by the squarefree polynomial `X ^ m - 1`
  have hmC : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  have hsq : Squarefree (X ^ m - 1 : ℂ[X]) := by
    have hsep : (X ^ m - C (1 : ℂ)).Separable := separable_X_pow_sub_C 1 hmC one_ne_zero
    simpa using hsep.squarefree
  have haev : aeval f (X ^ m - 1 : ℂ[X]) = 0 := by
    simp [map_sub, map_pow, hf]
  have hss : f.IsSemisimple :=
    Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsq haev
  -- the eigenspace decomposition is an internal direct sum with finite support
  have hint : DirectSum.IsInternal (f.eigenspace ·) :=
    (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr
      ⟨f.independent_genEigenspace 1, hss.iSup_eigenspace_eq_top⟩
  have hXne : (X ^ m - 1 : ℂ[X]) ≠ 0 := (monic_X_pow_sub_C (1 : ℂ) hm).ne_zero
  have hfin : {μ : ℂ | f.eigenspace μ ≠ ⊥}.Finite := by
    refine (Polynomial.finite_setOfPred_isRoot hXne).subset fun μ hμ => ?_
    have := pow_eq_one_of_eigenspace_ne_bot hf hμ
    simp [Polynomial.IsRoot, this]
  -- `f` and `f ^ k` preserve each eigenspace, acting as `μ • 1` and `μ ^ k • 1`
  have hmaps : ∀ j : ℕ, ∀ μ : ℂ,
      Set.MapsTo (f ^ j) (f.eigenspace μ) (f.eigenspace μ) := by
    intro j μ x hx
    refine Module.End.mem_eigenspace_iff.mpr ?_
    have hfx : f x = μ • x := Module.End.mem_eigenspace_iff.mp hx
    rw [pow_apply_of_mem_eigenspace hx j, map_smul, hfx, smul_smul, smul_smul, mul_comm]
  have htr : ∀ j : ℕ, ∀ μ : ℂ,
      LinearMap.trace ℂ (f.eigenspace μ) ((f ^ j).restrict (hmaps j μ)) =
        μ ^ j * (Module.finrank ℂ (f.eigenspace μ) : ℂ) := by
    intro j μ
    have hres : (f ^ j).restrict (hmaps j μ) = μ ^ j • (1 : Module.End ℂ (f.eigenspace μ)) := by
      ext x
      have : ((f ^ j).restrict (hmaps j μ) x : V) = (f ^ j) (x : V) := rfl
      have hx : (x : V) ∈ f.eigenspace μ := x.2
      simp [this, pow_apply_of_mem_eigenspace hx j]
    rw [hres, map_smul, LinearMap.trace_one, smul_eq_mul]
  -- assemble: trace over the eigenspace decomposition
  have key : ∀ j : ℕ, LinearMap.trace ℂ V (f ^ j) =
      ∑ μ ∈ hfin.toFinset, μ ^ j * (Module.finrank ℂ (f.eigenspace μ) : ℂ) := by
    intro j
    rw [LinearMap.trace_eq_sum_trace_restrict' hint hfin (hmaps j ·)]
    exact Finset.sum_congr rfl fun μ _ => htr j μ
  have h1 : LinearMap.trace ℂ V f =
      ∑ μ ∈ hfin.toFinset, μ * (Module.finrank ℂ (f.eigenspace μ) : ℂ) := by
    simpa [pow_one] using key 1
  rw [h1, key k, map_sum]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  rw [map_mul, map_natCast,
    hσ μ (pow_eq_one_of_eigenspace_ne_bot hf (hfin.mem_toFinset.mp hμ))]

end FiniteOrderTrace

section CharacterPower

variable {G : Type*} [Group G]

/-- If `σ : ℂ →+* ℂ` acts as `(· ^ k)` on `orderOf g`-th roots of unity then
`σ (χ_ρ(g)) = χ_ρ(g ^ k)`: the eigenvalues of `ρ g` are `orderOf g`-th roots of unity. -/
theorem map_character_eq_character_pow {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (σ : ℂ →+* ℂ) (ρ : Representation ℂ G V) {g : G}
    (hg : IsOfFinOrder g) {k : ℕ}
    (hσ : ∀ ζ : ℂ, ζ ^ orderOf g = 1 → σ ζ = ζ ^ k) :
    σ (ρ.character g) = ρ.character (g ^ k) := by
  have hm : orderOf g ≠ 0 := hg.orderOf_pos.ne'
  have hf : ρ g ^ orderOf g = 1 := by rw [← map_pow, pow_orderOf_eq_one, map_one]
  have h := map_trace_of_pow_eq_one σ hm hf hσ
  change σ (LinearMap.trace ℂ V (ρ g)) = LinearMap.trace ℂ V (ρ (g ^ k))
  rw [map_pow]
  exact h

/-- The `ClassFunction`-level power formula for genuine characters. -/
theorem IsCharacter.mapRingEquiv_apply_eq_apply_pow {φ : ClassFunction G ℂ}
    (hφ : IsCharacter φ) (σ : ℂ ≃+* ℂ) {g : G} (hg : IsOfFinOrder g) {k : ℕ}
    (hσ : ∀ ζ : ℂ, ζ ^ orderOf g = 1 → σ ζ = ζ ^ k) :
    ClassFunction.mapRingEquiv σ φ g = φ (g ^ k) := by
  obtain ⟨W, _, _, _, ρ, hchar⟩ := hφ
  have h1 : φ g = ρ.character g := congrFun hchar g
  have h2 : φ (g ^ k) = ρ.character (g ^ k) := congrFun hchar (g ^ k)
  rw [ClassFunction.mapRingEquiv_apply, h1, h2]
  exact map_character_eq_character_pow (σ : ℂ →+* ℂ) ρ hg hσ

/-- The power formula for virtual characters `φ ∈ ℤ[Irr G]`, by `ℤ`-linearity. -/
theorem mapRingEquiv_apply_eq_apply_pow_of_mem_ZIrr {φ : ClassFunction G ℂ}
    (hφ : φ ∈ ZIrr G) (σ : ℂ ≃+* ℂ) {g : G} (hg : IsOfFinOrder g) {k : ℕ}
    (hσ : ∀ ζ : ℂ, ζ ^ orderOf g = 1 → σ ζ = ζ ^ k) :
    ClassFunction.mapRingEquiv σ φ g = φ (g ^ k) := by
  induction hφ using Submodule.span_induction with
  | mem x hx =>
      exact (IsIrreducibleCharacter.isCharacter hx).mapRingEquiv_apply_eq_apply_pow σ hg hσ
  | zero => simp
  | add x y _ _ hx hy =>
      rw [ClassFunction.mapRingEquiv_add]
      change ClassFunction.mapRingEquiv σ x g + ClassFunction.mapRingEquiv σ y g =
        x (g ^ k) + y (g ^ k)
      rw [hx, hy]
  | smul n x _ hx =>
      rw [ClassFunction.mapRingEquiv_zsmul]
      change n • ClassFunction.mapRingEquiv σ x g = n • x (g ^ k)
      rw [hx]

end CharacterPower

section ComplexExtension

set_option backward.isDefEq.respectTransparency.types false in
/-- **Every automorphism of a subfield of `ℂ` extends to a ring automorphism of `ℂ`.** -/
theorem exists_complexRingEquiv_extends (K : IntermediateField ℚ ℂ) (v : K ≃+* K) :
    ∃ σ : ℂ ≃+* ℂ, ∀ x : K, σ x = (v x : ℂ) := by
  classical
  have : FaithfulSMul K ℂ :=
    (faithfulSMul_iff_algebraMap_injective K ℂ).mpr (algebraMap K ℂ).injective
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis K ℂ
  let := IsAlgClosed.isAlgClosure_of_transcendence_basis _ hs
  -- the coefficient-twist automorphism of the adjoined subalgebra `K[s]`
  set A := Algebra.adjoin K (Set.range ((↑) : s → ℂ)) with hA
  set e : A ≃+* A :=
    (hs.1.aevalEquiv.symm.toRingEquiv.trans (MvPolynomial.mapEquiv s v)).trans
      hs.1.aevalEquiv.toRingEquiv with he_def
  have he : ∀ x : K, e (algebraMap K A x) = algebraMap K A (v x) := by
    intro x
    have h1 : hs.1.aevalEquiv.symm (algebraMap K A x) = MvPolynomial.C x := by
      apply hs.1.aevalEquiv.injective
      rw [AlgEquiv.apply_symm_apply, ← MvPolynomial.algebraMap_eq, AlgEquiv.commutes]
    have h2 : MvPolynomial.map (v : K →+* K) (MvPolynomial.C x : MvPolynomial s K) =
        MvPolynomial.C (v x) :=
      MvPolynomial.map_C _ x
    have h3 : hs.1.aevalEquiv (MvPolynomial.C (v x)) = algebraMap K A (v x) := by
      rw [← MvPolynomial.algebraMap_eq, AlgEquiv.commutes]
    rw [he_def]
    simp only [RingEquiv.trans_apply, AlgEquiv.coe_ringEquiv, MvPolynomial.mapEquiv_apply]
    rw [h1, h2, h3]
  refine ⟨IsAlgClosure.equivOfEquiv ℂ ℂ e, fun x => ?_⟩
  have hx : (x : ℂ) = algebraMap A ℂ (algebraMap K A x) := by
    rw [← IsScalarTower.algebraMap_apply K A ℂ x]
    rfl
  rw [hx, IsAlgClosure.equivOfEquiv_algebraMap, he, ← IsScalarTower.algebraMap_apply]
  rfl

end ComplexExtension

section CyclotomicAutomorphism

open IntermediateField

/-- For `k` coprime to `n` there is a ring automorphism of `ℂ` acting as `(· ^ k)` on all
`n`-th roots of unity: the automorphism `μ ↦ μ ^ k` of the cyclotomic subfield `ℚ⟮μ⟯`,
extended to `ℂ` by `exists_complexRingEquiv_extends`. -/
theorem exists_complexRingEquiv_pow_of_rootsOfUnity {n k : ℕ} (hn : n ≠ 0)
    (hk : k.Coprime n) :
    ∃ σ : ℂ ≃+* ℂ, ∀ ζ : ℂ, ζ ^ n = 1 → σ ζ = ζ ^ k := by
  classical
  have : NeZero n := ⟨hn⟩
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  obtain ⟨μ, hμ⟩ : ∃ μ : ℂ, IsPrimitiveRoot μ n := ⟨_, Complex.isPrimitiveRoot_exp n hn⟩
  -- the cyclotomic subfield `K = ℚ(μ)` with power basis generated by `μ`
  have hint : IsIntegral ℚ μ :=
    ⟨X ^ n - 1, monic_X_pow_sub_C 1 hn, by simp [hμ.pow_eq_one]⟩
  let pb := IntermediateField.adjoin.powerBasis hint
  -- `μ ^ k` is a root of `minpoly ℚ μ = cyclotomic n ℚ` lying in `K`
  have hμk : IsPrimitiveRoot (μ ^ k) n := hμ.pow_of_coprime k hk
  have hmem : μ ^ k ∈ ℚ⟮μ⟯ := pow_mem (IntermediateField.mem_adjoin_simple_self ℚ μ) k
  have hcoe_gen : algebraMap ℚ⟮μ⟯ ℂ (IntermediateField.AdjoinSimple.gen ℚ μ) = μ :=
    IntermediateField.AdjoinSimple.algebraMap_gen ℚ μ
  have hgen : minpoly ℚ pb.gen = cyclotomic n ℚ := by
    rw [IntermediateField.adjoin.powerBasis_gen,
      ← minpoly.algebraMap_eq (algebraMap ℚ⟮μ⟯ ℂ).injective, hcoe_gen,
      ← cyclotomic_eq_minpoly_rat hμ hnpos]
  have hroot : aeval (⟨μ ^ k, hmem⟩ : ℚ⟮μ⟯) (minpoly ℚ pb.gen) = 0 := by
    apply (algebraMap ℚ⟮μ⟯ ℂ).injective
    rw [map_zero, ← Polynomial.aeval_algebraMap_apply, hgen]
    have : algebraMap ℚ⟮μ⟯ ℂ ⟨μ ^ k, hmem⟩ = μ ^ k := rfl
    rw [this, Polynomial.aeval_def, ← Polynomial.eval_map, Polynomial.map_cyclotomic]
    exact (hμk.isRoot_cyclotomic hnpos)
  -- the automorphism `μ ↦ μ ^ k` of `K`
  have : FiniteDimensional ℚ ℚ⟮μ⟯ := IntermediateField.adjoin.finiteDimensional hint
  let v₀ : ℚ⟮μ⟯ →ₐ[ℚ] ℚ⟮μ⟯ := pb.lift ⟨μ ^ k, hmem⟩ hroot
  have hv₀ : Function.Bijective v₀ :=
    ⟨v₀.toRingHom.injective,
      LinearMap.injective_iff_surjective.mp v₀.toRingHom.injective⟩
  let v : ℚ⟮μ⟯ ≃ₐ[ℚ] ℚ⟮μ⟯ := AlgEquiv.ofBijective v₀ hv₀
  obtain ⟨σ, hσ⟩ := exists_complexRingEquiv_extends ℚ⟮μ⟯ v.toRingEquiv
  -- `σ μ = μ ^ k`
  have hσμ : σ μ = μ ^ k := by
    have h1 := hσ (IntermediateField.AdjoinSimple.gen ℚ μ)
    have h2 : v.toRingEquiv (IntermediateField.AdjoinSimple.gen ℚ μ) = ⟨μ ^ k, hmem⟩ := by
      change v₀ (IntermediateField.AdjoinSimple.gen ℚ μ) = _
      rw [← IntermediateField.adjoin.powerBasis_gen hint]
      exact pb.lift_gen _ hroot
    rw [h2] at h1
    rw [show ((IntermediateField.AdjoinSimple.gen ℚ μ : ℚ⟮μ⟯) : ℂ) = μ from hcoe_gen] at h1
    exact h1
  -- hence `σ` is `(· ^ k)` on every `n`-th root of unity
  refine ⟨σ, fun ζ hζ => ?_⟩
  obtain ⟨i, _, hi⟩ := hμ.eq_pow_of_pow_eq_one hζ
  rw [← hi, map_pow, hσμ, ← pow_mul, mul_comm k i, pow_mul]

/-- **Peterfalvi (1.9)(a)** (CRT form).  For coprime `a, b` and `k` coprime to `a` there is
a ring automorphism of `ℂ` acting as `(· ^ k)` on `a`-th roots of unity and as the
identity on `b`-th roots of unity. -/
theorem exists_complexRingEquiv_pow_and_fixed {a b k : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a.Coprime b) (hk : k.Coprime a) :
    ∃ σ : ℂ ≃+* ℂ,
      (∀ ζ : ℂ, ζ ^ a = 1 → σ ζ = ζ ^ k) ∧ (∀ ζ : ℂ, ζ ^ b = 1 → σ ζ = ζ) := by
  -- CRT: pick `k'` with `k' ≡ k [MOD a]`, `k' ≡ 1 [MOD b]`; then `k'` is coprime to `a*b`
  obtain ⟨k', hk'a, hk'b⟩ := Nat.chineseRemainder hab k 1
  have hk'n : k'.Coprime (a * b) := by
    have h1 : k'.Coprime a := by
      have := hk'a.gcd_eq
      unfold Nat.Coprime
      rw [this]
      exact hk
    have h2 : k'.Coprime b := by
      have := hk'b.gcd_eq
      unfold Nat.Coprime
      rw [this]
      exact Nat.coprime_one_left b
    exact Nat.Coprime.mul_right h1 h2
  obtain ⟨σ, hσ⟩ :=
    exists_complexRingEquiv_pow_of_rootsOfUnity (mul_ne_zero ha hb) hk'n
  have key : ∀ (ζ : ℂ) (d : ℕ), d ≠ 0 → d ∣ a * b → ζ ^ d = 1 → ∀ j : ℕ,
      k' ≡ j [MOD d] → σ ζ = ζ ^ j := by
    intro ζ d hd hdvd hζ j hmod
    have hζn : ζ ^ (a * b) = 1 := by
      obtain ⟨c, hc⟩ := hdvd
      rw [hc, pow_mul, hζ, one_pow]
    rw [hσ ζ hζn]
    have hfo : IsOfFinOrder ζ :=
      isOfFinOrder_iff_pow_eq_one.mpr ⟨d, Nat.pos_of_ne_zero hd, hζ⟩
    exact hfo.pow_eq_pow_iff_modEq.mpr
      (hmod.of_dvd (orderOf_dvd_of_pow_eq_one hζ))
  exact ⟨σ, fun ζ hζ => key ζ a ha (dvd_mul_right a b) hζ k hk'a,
    fun ζ hζ => by
      simpa using key ζ b hb (dvd_mul_left b a) hζ 1 hk'b⟩

end CyclotomicAutomorphism

end OddOrder.RepresentationTheory


