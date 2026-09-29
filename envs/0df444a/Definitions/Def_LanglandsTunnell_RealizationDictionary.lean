-- Prove2me | Definitions.Def_LanglandsTunnell_RealizationDictionary
-- name    : LanglandsTunnell_RealizationDictionary
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/5b95a06d-9ca7-509d-992f-b3dc12350339
-- title:
--   Realization dictionary for cuspidal Hecke eigensystems over Q
-- statement:
--   Two declarations. The helper [`AutomorphicForm.ratPrime`](../def/LanglandsTunnell_RealizationDictionary.html#L17) transports a rational prime $p$ to a height-one prime of $\mathcal{O}_{\mathbb{Q}}$, using the inverse of Mathlib's equivalence `Rat.HeightOneSpectrum.primesEquiv`.
--
--   The main definition is a predicate on an abstract cuspidality notion. Here `notion : CuspidalityNotion (ℤ√(-2))` is a structure whose single field assigns, to every number field $F$, a predicate `IsCusp` on Hecke eigensystems over $F$ with values in $\mathbb{Z}[\sqrt{-2}]$, a Hecke eigensystem being a record consisting of a nonzero level ideal of $\mathcal{O}_F$ together with two functions $a, b$ on the height-one primes (Satake data). `RealizationDictionary notion` asserts: for every $\pi_0$ over $\mathbb{Q}$ with `notion.IsCusp ℚ π₀` and every finite set $T \subseteq \mathbb{N}$, there are a level $M \neq 0$ and a sequence $b : \mathbb{N} \to \mathbb{Z}[\sqrt{-2}]$ such that (i) every nonzero $\ell \in T$ divides $M$; (ii) $b$ satisfies the formal Hecke recursion [`FormalHecke.IsEigensystem`](../def/FormalHecke_Eigensystem.html#L10) for the eigenvalue system $\ell \mapsto \chi_{-3}(\ell)$ away from $M$ and $0$ at $\ell \mid M$, i.e. $b_1 = 1$ and $b_{\ell n} + \chi_{-3}(\ell)\,[\ell \mid n]\,b_{n/\ell} = b_\ell b_n$ for all primes $\ell$, with $\chi_{-3}$ the character $n \bmod 3 \mapsto 1, -1, 0$; (iii) `HasIntegralBasis M`, i.e. the weight-two cusp forms on $\Gamma_0(M)$ with all $q$-coefficients in the prime subring of $\mathbb{C}$ span the whole space over $\mathbb{C}$; (iv) and (v) two integral sequences $a : \mathbb{N} \to \mathbb{Z}$, each a formal Hecke eigensystem for the same eigenvalue system and each `IsLatticeRealized M`, i.e. realized by a weight-two cusp form on $\Gamma_0(M)$ with integral $q$-coefficients congruent mod $3$ to the coefficients of $(\sum a_n q^n)\cdot E_{1,\chi_{-3}}$, with $a_n \equiv \mathrm{red}(b_n)$ respectively $a_n \equiv \chi_{-3}(n)\,\mathrm{red}(b_n)$ in $\mathbb{Z}/3$, where $\mathrm{red} : \mathbb{Z}[\sqrt{-2}] \to \mathbb{Z}/3$ sends $\sqrt{-2} \mapsto -1$; and (vi) $b_p = \pi_0.a(\mathrm{ratPrime}\,p)$ for all primes $p \nmid 3M$. Everything on the holomorphic side is thus a mod-$3$ congruence of $q$-expansion coefficient sequences, not an identification of forms, and $b$ itself is only a formal eigensystem.
--
--   **Relation to Mathlib.** Mathlib supplies `CuspForm`, `Gamma0`, `qExpansion` and `Zsqrtd`, and the equivalence `Rat.HeightOneSpectrum.primesEquiv` repackaged as `ratPrime`; the notions of Hecke eigensystem, abstract cuspidality notion, formal Hecke eigensystem, integral $q$-expansion basis and lattice realization are the project's own.
--
--   **Where it is used.** This predicate is one of the two conditions imposed on the abstract cuspidality notion in the Langlands–Tunnell input: it pins the opaque notion to holomorphic data, so that a cuspidal eigensystem over $\mathbb{Q}$ produces weight-one Hecke data congruent mod $3$ to integral weight-two cusp forms of controllable level. It is used as a hypothesis by the base-change citation statements and by the bridge to the existence of a weight-one newform, which is what makes the mod-$3$ representation of the Frey curve modular.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LanglandsTunnell_RealizationDictionary.lean

import Mathlib
import Definitions.Def_AutomorphicForm_HeckeEigensystem
import Definitions.Def_FormalHecke_Eigensystem
import Definitions.Def_LanglandsTunnell_ExplicitLift
import Definitions.Def_ModularForm_EisensteinChiNegThree
import Definitions.Def_CuspForm_IntegralLattice

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open FLT.ExplicitLift EisensteinWeightOne CuspForm Zsqrtd

noncomputable section

namespace AutomorphicForm

def ratPrime (p : Nat.Primes) : HeightOneSpectrum (𝓞 ℚ) :=
  (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm p

def RealizationDictionary (notion : CuspidalityNotion (ℤ√(-2))) : Prop :=
  ∀ π₀ : HeckeEigensystem ℚ (ℤ√(-2)), notion.IsCusp ℚ π₀ →
    ∀ T : Finset ℕ,
      ∃ (M : ℕ) (_ : NeZero M) (b : ℕ → ℤ√(-2)),
        (∀ ℓ ∈ T, ℓ ≠ 0 → ℓ ∣ M) ∧
        FormalHecke.IsEigensystem
          (fun ℓ => if ℓ ∣ M then 0 else ((chiNegThree ℓ : ℤ) : ℤ√(-2))) b ∧
        HasIntegralBasis M ∧
        (∃ a : ℕ → ℤ,
          FormalHecke.IsEigensystem
            (fun ℓ => if ℓ ∣ M then 0 else ((chiNegThree ℓ : ℤ) : ℤ)) a ∧
          IsLatticeRealized M a ∧
          ∀ n : ℕ, ((a n : ℤ) : ZMod 3) = red (b n)) ∧
        (∃ a : ℕ → ℤ,
          FormalHecke.IsEigensystem
            (fun ℓ => if ℓ ∣ M then 0 else ((chiNegThree ℓ : ℤ) : ℤ)) a ∧
          IsLatticeRealized M a ∧
          ∀ n : ℕ, ((a n : ℤ) : ZMod 3) = ((chiNegThree n : ℤ) : ZMod 3) * red (b n)) ∧
        (∀ p : Nat.Primes, ¬ (p : ℕ) ∣ 3 * M → b (p : ℕ) = π₀.a (ratPrime p))

end AutomorphicForm

end


