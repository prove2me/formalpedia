-- Prove2me | Definitions.Def_AutomorphicForm_CyclicBaseChangeLifting
-- name    : AutomorphicForm_CyclicBaseChangeLifting
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/107ec17f-49ea-5dc9-a439-5c4fd1779282
-- title:
--   Cyclic base change lifting properties for Hecke eigensystems
-- statement:
--   For number fields $F$ and $E$ with $E$ an $F$-algebra, and for a parameter `notion : CuspidalityNotion ℂ` (a structure whose single field assigns to every number field $K$ a predicate `IsCusp` on complex Hecke eigensystems over $K$), this module defines the Prop-valued structure `LanglandsLiftingProperties`, a four-field package of the lifting and descent properties of cyclic base change, formulated entirely in terms of Satake data. Here a Hecke eigensystem over $K$ consists of a nonzero level ideal of $\mathcal O_K$ together with two functions $a, b$ from the height-one spectrum of $\mathcal O_K$ to the coefficient ring; $\pi$ base changes to $\Psi$ (`IsBaseChangeOf`) when, outside some finite set of primes $\mathfrak P$ of $\mathcal O_E$, one has $\Psi.a(\mathfrak P) = \mathrm{satakePow}_f(\pi.a(v), \pi.b(v))$ and $\Psi.b(\mathfrak P) = \pi.b(v)^f$, where $v$ is the prime of $\mathcal O_F$ under $\mathfrak P$, $f$ is its residue degree, and $\mathrm{satakePow}_n(s,e)$ is the recursion $2, s, s\,\mathrm{satakePow}_{n+1} - e\,\mathrm{satakePow}_n$ computing the trace of the $n$-th power of a matrix of trace $s$ and determinant $e$.
--
--   The fields are: `propertyA`, every cuspidal $\pi$ over $F$ admits some $\Psi$ over $E$ with $\pi$ base changing to $\Psi$ (no cuspidality demanded of $\Psi$); `propertyB`, every cuspidal $\Psi$ over $E$ which is constant on fibres over $F$ (that is, outside a finite set of primes, $a$ and $b$ agree at any two primes of $\mathcal O_E$ lying over the same prime of $\mathcal O_F$ with the same residue degree) is the base change of some cuspidal $\pi$ over $F$; `propertyC`, if cuspidal $\pi, \pi'$ over $F$ both base change to the same $\Psi$, then there are a modulus $\mathfrak f$ admissible for $E/F$ (nonzero, and divisible by $v^{4e_2+2e_3+1}$, with $e_2, e_3$ the ramification indices of $(2)$ and $(3)$ at $v$, for every prime $v$ whose chosen prime above in $E$ has nontrivial inertia) and a character $\omega$ of the narrow ray class group modulo $\mathfrak f$ with values in $\mathbb C^\times$, trivial on the $f(w/v)$-th power of the class of $v$ for every prime $w$ of $\mathcal O_E$ over a prime $v \nmid \mathfrak f$, such that outside a finite set of primes $v \nmid \mathfrak f$ one has $\pi'.a(v) = \omega([v])\,\pi.a(v)$ and $\pi'.b(v) = \omega([v])^2\,\pi.b(v)$, i.e. $\pi'$ is the twist of $\pi$ by $\omega$ away from finitely many primes; `propertyG`, which spells out the existential in `IsBaseChangeOf` and therefore asks nothing beyond its hypothesis. The structure has no field asserting the classical pointwise strong multiplicity one property.
--
--   **Relation to Mathlib.** Mathlib has no automorphic forms, cuspidality or base change; the Hecke eigensystem, base-change and cuspidality notions used here are the project's own, formulated on top of Mathlib's rings of integers, height-one spectra, residue degrees and adele rings.
--
--   **Where it is used.** The structure is the interface through which cyclic base change for $\mathrm{GL}(2)$, in the Satake-data form used by the Langlands–Tunnell theorem, enters the argument: it is what supplies modularity of the mod $3$ representation attached to a Frey curve, the starting point of the modularity-lifting route to Fermat's Last Theorem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_CyclicBaseChangeLifting.lean

import Definitions.Def_AutomorphicForm_HeckeEigensystem
import Definitions.Def_LanglandsTunnell_ArtinCoreCTM

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open IsDedekindDomain NumberField
open Deep.NTSupply LanglandsTunnell.P2.Artin

noncomputable section

namespace AutomorphicForm.CyclicBaseChangeLifting

section GlobalLifting

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E]

structure LanglandsLiftingProperties (notion : CuspidalityNotion ℂ) : Prop where

  propertyA : ∀ π : HeckeEigensystem F ℂ, notion.IsCusp F π →
    ∃ Ψ : HeckeEigensystem E ℂ, IsBaseChangeOf π Ψ

  propertyB : ∀ Ψ : HeckeEigensystem E ℂ, notion.IsCusp E Ψ →
    Ψ.IsConstantOnFibers F →
    ∃ π : HeckeEigensystem F ℂ, notion.IsCusp F π ∧ IsBaseChangeOf π Ψ

  propertyC : ∀ π π' : HeckeEigensystem F ℂ, notion.IsCusp F π → notion.IsCusp F π' →
    ∀ Ψ : HeckeEigensystem E ℂ, IsBaseChangeOf π Ψ → IsBaseChangeOf π' Ψ →
    ∃ 𝔣 : Ideal (𝓞 F), IsAdmissibleModulus F E 𝔣 ∧
      ∃ ω : NarrowRayClassGroup F 𝔣 →* ℂˣ,
        (∀ (w : HeightOneSpectrum (𝓞 E)) (hw : ¬ ((w.under (𝓞 F)).asIdeal ∣ 𝔣)),
          ω (primeClass F 𝔣 (w.under (𝓞 F)) hw ^
            ((w.under (𝓞 F)).asIdeal.inertiaDeg' w.asIdeal)) = 1) ∧
        ∃ S : Finset (HeightOneSpectrum (𝓞 F)),
          ∀ v ∉ S, ∀ (hv : ¬ v.asIdeal ∣ 𝔣),
            π'.a v = (ω (primeClass F 𝔣 v hv) : ℂ) * π.a v ∧
            π'.b v = (ω (primeClass F 𝔣 v hv) : ℂ) ^ 2 * π.b v

  propertyG : ∀ (π : HeckeEigensystem F ℂ) (Ψ : HeckeEigensystem E ℂ),
    IsBaseChangeOf π Ψ →
    ∃ S : Finset (HeightOneSpectrum (𝓞 E)),
      ∀ w ∉ S, IsBaseChangeAt π Ψ w

end GlobalLifting

end AutomorphicForm.CyclicBaseChangeLifting


