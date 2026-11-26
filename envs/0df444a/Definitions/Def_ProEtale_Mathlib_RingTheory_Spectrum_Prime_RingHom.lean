-- Prove2me | Definitions.Def_ProEtale_Mathlib_RingTheory_Spectrum_Prime_RingHom
-- name    : ProEtale_Mathlib_RingTheory_Spectrum_Prime_RingHom
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T17:00:32.263804+00:00
-- url     : https://prove2.me/theorems/186d7d90-d009-5af8-bee3-54946b80e3bb
-- title:
--   Injectivity, flatness and surjectivity of ring maps tested at maximal ideals; primes of finite products of fields
-- statement:
--   Let $f\colon R \to S$ be a homomorphism of commutative rings. For a prime $\mathfrak p \subset S$, write $f_{\mathfrak p}\colon R_{f^{-1}\mathfrak p} \to S_{\mathfrak p}$ for the induced map of local rings.
--
--   Principal results:
--
--   1. If $(A_i)_{i \in \iota}$ is a finite family of fields, every prime ideal of $\prod_i A_i$ is the kernel of one of the projections $\prod_i A_i \to A_j$.
--   2. **Injectivity.** Suppose $f_{\mathfrak m}$ is injective for every maximal ideal $\mathfrak m$ of $S$, and $\operatorname{Spec} f\colon \operatorname{Spec} S \to \operatorname{Spec} R$ is surjective. Then $f$ is injective.
--   3. **Flatness.** If $f_{\mathfrak m}$ is flat for every maximal ideal $\mathfrak m$ of $S$, then $f$ is flat.
--   4. **Surjectivity.** Suppose that for every $s \in S$ and every maximal ideal $\mathfrak m$ of $R$ there is $r \in R \setminus \mathfrak m$ with $f(r)\,s \in f(R)$. Then $f$ is surjective.
--
--   These local criteria are used to check properties of ring maps (bijectivity, flatness) stalk by stalk, for instance for maps that identify local rings.
--
--   **Formalization Note** The declarations are `Ideal.exists_eq_ker_evalRingHom`, `RingHom.injective_of_localRingHom_injective`, `RingHom.flat_of_flat_localRingHom` and `RingHom.surjective_of_forall_isMaximal_exists`. The local maps are `Localization.localRingHom (p.comap f) p f rfl`. The module docstring announces an "if and only if" for surjectivity, but the Lean lemma proves only the implication stated in item 4.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/RingTheory/Spectrum/Prime/RingHom.lean (declarations needed by the transplanted proofs, unused ones removed).

/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Spectrum.Maximal.Localization
import Mathlib.RingTheory.Spectrum.Prime.RingHom

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
/-!
# General results on ring homomorphisms and localization

In this file we show:

- A ring homomorphism is injective if all stalk maps are injective and for every maximal
  ideal of `R`, there exists a prime of `S` mapping to it.
- A ring homomorphism is flat if the induced maps on localizations at each maximal ideal
  are flat.
- A ring homomorphism is surjective if and only if for every element and every maximal ideal,
  there exists an element outside the maximal ideal whose product with the given element
  is in the range.
-/

variable {R S : Type*} [CommRing R] [CommRing S]

/-- A prime ideal of a finite product of fields is the kernel of one of the evaluation maps. -/
lemma Ideal.exists_eq_ker_evalRingHom {ι : Type*} [Finite ι] {A : ι → Type*}
    [∀ i, Field (A i)] (p : Ideal (∀ i, A i)) [p.IsPrime] :
    ∃ j, p = RingHom.ker (Pi.evalRingHom A j) := by
  obtain ⟨j, q, hq⟩ := PrimeSpectrum.exists_comap_evalRingHom_eq ⟨p, ‹p.IsPrime›⟩
  refine ⟨j, ?_⟩
  have hq' : (PrimeSpectrum.comap (Pi.evalRingHom A j) q).asIdeal = p :=
    congrArg PrimeSpectrum.asIdeal hq
  rwa [PrimeSpectrum.comap_asIdeal, Subsingleton.elim q ⊥, PrimeSpectrum.asIdeal_bot,
    ← RingHom.ker_eq_comap_bot, eq_comm] at hq'

/-- A ring homomorphism is injective if all stalk maps at maximal ideals are injective and
`PrimeSpectrum.comap f` is surjective. -/
lemma RingHom.injective_of_localRingHom_injective {f : R →+* S}
    (hf : ∀ (p : Ideal S) [p.IsMaximal],
        Function.Injective (Localization.localRingHom (p.comap f) p f rfl))
    (hb : Function.Surjective (PrimeSpectrum.comap f)) : Function.Injective f := by
  intro r₁ r₂ hr
  apply MaximalSpectrum.toPiLocalization_injective R
  ext ⟨q, hq⟩
  obtain ⟨⟨p, hp⟩, hpq⟩ := hb ⟨q, hq.isPrime⟩
  have hpq' : p.comap f = q := congr_arg PrimeSpectrum.asIdeal hpq
  obtain ⟨m, hm, hpm⟩ := p.exists_le_maximal hp.ne_top
  have hmcomap : m.comap f = q :=
    (hq.eq_of_le (Ideal.comap_ne_top f hm.ne_top)
      (hpq' ▸ Ideal.comap_mono hpm)).symm
  subst hmcomap
  haveI := hm
  apply hf m
  simp only [MaximalSpectrum.toPiLocalization_apply_apply,
    Localization.localRingHom_to_map, hr]

/-- A ring homomorphism `f : R →+* S` is flat if the induced maps on localizations at each
maximal ideal are flat. -/
lemma RingHom.flat_of_flat_localRingHom {f : R →+* S}
    (h : ∀ (p : Ideal S) [p.IsMaximal],
        (Localization.localRingHom (p.comap f) p f rfl).Flat) :
    f.Flat := by
  algebraize [f]
  rw [RingHom.Flat]
  apply Module.flat_of_isLocalized_maximal S S (fun P ↦ Localization.AtPrime P)
    (fun P ↦ Algebra.linearMap S _)
  intro P _
  algebraize [Localization.localRingHom (Ideal.comap f P) P f rfl]
  have : IsScalarTower R (Localization.AtPrime (Ideal.comap f P)) (Localization.AtPrime P) :=
    .of_algebraMap_eq fun x ↦ (Localization.localRingHom_to_map _ _ _ rfl x).symm
  have : Module.Flat (Localization.AtPrime (Ideal.comap f P))
      (Localization.AtPrime P) := h P
  exact Module.Flat.trans R (Localization.AtPrime <| Ideal.comap f P) (Localization.AtPrime P)

/-- A ring homomorphism `f : R →+* S` is surjective if for every `s : S` and every maximal
ideal `m` of `R`, there exists `r ∉ m` such that `f r * s ∈ f.range`. -/
lemma RingHom.surjective_of_forall_isMaximal_exists {f : R →+* S}
    (h : ∀ (s : S) (m : Ideal R), m.IsMaximal → ∃ r : R, r ∉ m ∧ f r * s ∈ f.range) :
    Function.Surjective f := by
  intro s
  by_contra hs
  have h1 : ¬(f 1 * s ∈ f.range) := by simpa only [map_one, one_mul]
  set J_s : Ideal R := {
    carrier := {r : R | f r * s ∈ f.range}
    add_mem' := fun ⟨x, hx⟩ ⟨y, hy⟩ ↦ ⟨x + y, by rw [map_add, map_add, add_mul, hx, hy]⟩
    zero_mem' := ⟨0, by simp⟩
    smul_mem' := fun c _ ⟨x, hx⟩ ↦
      ⟨c * x, by rw [smul_eq_mul, map_mul, map_mul, mul_assoc, hx]⟩
  }
  have hJ_ne_top : J_s ≠ ⊤ := fun heq ↦ h1 ((heq ▸ Submodule.mem_top : (1 : R) ∈ J_s))
  obtain ⟨m, hm, hJm⟩ := Ideal.exists_le_maximal J_s hJ_ne_top
  obtain ⟨r, hrm, hr_range⟩ := h s m hm
  exact hrm (hJm hr_range)


