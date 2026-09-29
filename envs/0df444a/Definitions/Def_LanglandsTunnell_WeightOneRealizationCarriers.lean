-- Prove2me | Definitions.Def_LanglandsTunnell_WeightOneRealizationCarriers
-- name    : LanglandsTunnell_WeightOneRealizationCarriers
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/fb594014-3057-5146-ab2d-e12c0647da55
-- title:
--   Weight-one realization and mod-3 congruence-lift carriers
-- statement:
--   Three `Prop`-valued carriers that split the project's Langlands–Tunnell dictionary [`AutomorphicForm.RealizationDictionary`](../def/LanglandsTunnell_RealizationDictionary.html#L20) at the weight-one/weight-two boundary, together with two bookkeeping lemmas.
--
--   [`CuspForm.IsWeightOneChiNegThreeRealized M b`](../def/LanglandsTunnell_WeightOneRealizationCarriers.html#L15), for $M : \mathbb{N}$ and $b : \mathbb{N} \to \mathbb{Z}[\sqrt{-2}]$, asserts the existence of a ring homomorphism $\iota : \mathbb{Z}[\sqrt{-2}] \to \mathbb{C}$ and a cusp form $f$ of weight $1$ on $\Gamma_1(M)$ whose $q$-expansion coefficients satisfy $\mathrm{qCoeff}(f,n) = \iota(b_n)$ for all $n$; note the predicate is about the sequence $b$, not about $f$, and no nondegeneracy of $\iota$ or normalisation of $f$ is imposed.
--
--   [`AutomorphicForm.WeightOneHolomorphicRealization notion`](../def/LanglandsTunnell_WeightOneRealizationCarriers.html#L23), for a project notion of cuspidality `notion` over $\mathbb{Z}[\sqrt{-2}]$, says: for every Hecke eigensystem $\pi_0$ over $\mathbb{Q}$ with coefficients in $\mathbb{Z}[\sqrt{-2}]$ that is `notion`-cuspidal, and every finite set $T$ of naturals, there are a level $M$ (nonzero), and $b : \mathbb{N} \to \mathbb{Z}[\sqrt{-2}]$ such that every nonzero $\ell \in T$ divides $M$; $b$ is a formal Hecke eigensystem for the nebentypus $\ell \mapsto \chi_{-3}(\ell)$ truncated to $0$ at $\ell \mid M$; `HasIntegralBasis M` holds; $b$ is weight-one realized in the above sense; and $b_p = \pi_0.a(p)$ for all primes $p \nmid 3M$.
--
--   [`CuspForm.WeightTwoModThreeCongruenceLift`](../def/LanglandsTunnell_WeightOneRealizationCarriers.html#L38) says: for every such $M$, $b$ which is a $\chi_{-3}$-eigensystem, has integral basis and is weight-one realized, there exist integral eigensystems $a$ for the same truncated $\chi_{-3}$ system, lattice-realized at level $M$, with $a_n \equiv \mathrm{red}(b_n)$ and (for a second such $a$) $a_n \equiv \chi_{-3}(n)\,\mathrm{red}(b_n)$ in $\mathbb{Z}/3$ — congruences of coefficient sequences only.
--
--   The lemma `realizationDictionary_of_weightOne_of_congruenceLift` merely reassembles the two carriers into `RealizationDictionary`; `notionCompatForAttachedOctahedralData_self` proves compatibility of a notion with itself by returning one of the hypotheses.
--
--   **Relation to Mathlib.** The weight-one cusp forms and $\Gamma_1(M)$ are Mathlib's (`CuspForm (Gamma1 M) 1`, `CongruenceSubgroup`); the predicates `HeckeEigensystem`, `CuspidalityNotion`, [`FormalHecke.IsEigensystem`](../def/FormalHecke_Eigensystem.html#L10), `HasIntegralBasis`, `IsLatticeRealized`, `red`, `chiNegThree` and `RealizationDictionary` are the project's own, defined in the imported definition modules.
--
--   **Where it is used.** These carriers isolate the two classical inputs to the Langlands–Tunnell step of the mod-3 modularity argument: realization of a cuspidal Hecke eigensystem with nebentypus $\chi_{-3}$ by a holomorphic weight-one form, and passage from weight one to weight two by a mod-3 congruence. The combined statement `RealizationDictionary` is what the octahedral-representation part of the Frey-curve argument consumes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LanglandsTunnell_WeightOneRealizationCarriers.lean

import Mathlib
import Definitions.Def_LanglandsTunnell_RealizationDictionary
import Definitions.Def_LanglandsTunnell_TunnellExistenceCarriers

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open FLT.ExplicitLift EisensteinWeightOne CuspForm Zsqrtd
open CongruenceSubgroup

noncomputable section

namespace CuspForm

def IsWeightOneChiNegThreeRealized (M : ℕ) (b : ℕ → ℤ√(-2)) : Prop :=
  ∃ (ι : ℤ√(-2) →+* ℂ) (f : CuspForm (Gamma1 M) 1),
    ∀ n : ℕ, ModularFormClass.qCoeff f n = ι (b n)

end CuspForm

namespace AutomorphicForm

def WeightOneHolomorphicRealization (notion : CuspidalityNotion (ℤ√(-2))) : Prop :=
  ∀ π₀ : HeckeEigensystem ℚ (ℤ√(-2)), notion.IsCusp ℚ π₀ →
    ∀ T : Finset ℕ,
      ∃ (M : ℕ) (_ : NeZero M) (b : ℕ → ℤ√(-2)),
        (∀ ℓ ∈ T, ℓ ≠ 0 → ℓ ∣ M) ∧
        FormalHecke.IsEigensystem
          (fun ℓ => if ℓ ∣ M then 0 else ((chiNegThree ℓ : ℤ) : ℤ√(-2))) b ∧
        HasIntegralBasis M ∧
        CuspForm.IsWeightOneChiNegThreeRealized M b ∧
        (∀ p : Nat.Primes, ¬ (p : ℕ) ∣ 3 * M → b (p : ℕ) = π₀.a (ratPrime p))

end AutomorphicForm

namespace CuspForm

def WeightTwoModThreeCongruenceLift : Prop :=
  ∀ (M : ℕ) (_ : NeZero M) (b : ℕ → ℤ√(-2)),
    FormalHecke.IsEigensystem
      (fun ℓ => if ℓ ∣ M then 0 else ((chiNegThree ℓ : ℤ) : ℤ√(-2))) b →
    HasIntegralBasis M →
    IsWeightOneChiNegThreeRealized M b →
    (∃ a : ℕ → ℤ,
      FormalHecke.IsEigensystem
        (fun ℓ => if ℓ ∣ M then 0 else ((chiNegThree ℓ : ℤ) : ℤ)) a ∧
      IsLatticeRealized M a ∧
      ∀ n : ℕ, ((a n : ℤ) : ZMod 3) = red (b n)) ∧
    (∃ a : ℕ → ℤ,
      FormalHecke.IsEigensystem
        (fun ℓ => if ℓ ∣ M then 0 else ((chiNegThree ℓ : ℤ) : ℤ)) a ∧
      IsLatticeRealized M a ∧
      ∀ n : ℕ, ((a n : ℤ) : ZMod 3) = ((chiNegThree n : ℤ) : ZMod 3) * red (b n))

end CuspForm

namespace AutomorphicForm

theorem realizationDictionary_of_weightOne_of_congruenceLift
    {notion : CuspidalityNotion (ℤ√(-2))}
    (hW1 : WeightOneHolomorphicRealization notion)
    (hW2 : CuspForm.WeightTwoModThreeCongruenceLift) :
    RealizationDictionary notion := by
  intro π₀ hcusp T
  obtain ⟨M, hM, b, c1, c2, c3, cW1, c6⟩ := hW1 π₀ hcusp T
  obtain ⟨c4, c5⟩ := hW2 M hM b c2 c3 cW1
  exact ⟨M, hM, b, c1, c2, c3, c4, c5, c6⟩

end AutomorphicForm

namespace LanglandsTunnell

theorem notionCompatForAttachedOctahedralData_self
    (notion : AutomorphicForm.CuspidalityNotion (ℤ√(-2))) :
    NotionCompatForAttachedOctahedralData notion notion :=
  fun _ _ _ _ _ _ _ _ h _ => h

end LanglandsTunnell

end


