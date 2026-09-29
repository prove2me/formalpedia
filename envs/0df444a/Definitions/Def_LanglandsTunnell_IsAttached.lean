-- Prove2me | Definitions.Def_LanglandsTunnell_IsAttached
-- name    : LanglandsTunnell_IsAttached
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/d7a3a7f7-e52e-5eb1-826e-ccd1d0b9d74b
-- title:
--   Mod-3 Frobenius-trace attachment predicates, up to quadratic twist
-- statement:
--   Working with the Galois group written as the group of $\mathbb{Q}$-algebra automorphisms of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`, this module defines three predicates comparing a homomorphism $\rho$ of that group into $\mathrm{GL}_2(\mathbb{Z}/3)$ with a Hecke eigensystem $\pi_0$ of type `HeckeEigensystem ℚ (ℤ√(-2))` — that is, a nonzero ideal `level` of $\mathcal{O}_{\mathbb{Q}}$ together with two functions $a, b$ from the height-one spectrum of $\mathcal{O}_{\mathbb{Q}}$ to $\mathbb{Z}[\sqrt{-2}]$ — away from a finite set $T$ of natural numbers. `IsAttachedExact ρ π₀ T` asserts: for every prime $p$ with $p \notin T$, every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $p$ a nonunit of $A$, and every $\sigma$ lying in the decomposition subgroup of $A$ over $\mathbb{Q}$ and inducing $x \mapsto x^p$ on the residue field of $A$, one has $\mathrm{red}(\pi_0.a(v_p)) = \mathrm{tr}\,\rho(\sigma)$ in $\mathbb{Z}/3$, where $v_p$ is the place of $\mathcal{O}_{\mathbb{Q}}$ corresponding to $p$ under `Rat.HeightOneSpectrum.primesEquiv`, $\mathrm{red} : \mathbb{Z}[\sqrt{-2}] \to \mathbb{Z}/3$ is the ring homomorphism sending $\sqrt{-2}$ to $-1$, and the trace is that of the underlying $2 \times 2$ matrix. `IsAttachedTwisted` has the same shape with the right-hand side multiplied by the image in $\mathbb{Z}/3$ of `chiNegThree p`, i.e. of $1$, $-1$ or $0$ according as $p \equiv 1, 2, 0 \pmod 3$. `IsAttachedUpToTwist` is the disjunction of the two, the choice of branch being made once and for all, outside the quantifier over places. These are congruences of traces in characteristic $3$ at unramified-type data only: no continuity, irreducibility or automorphy is asserted, and no characteristic-zero identity. The accompanying lemma `isAttachedUpToTwist_one` exhibits one instance of the untwisted branch, for trivial $\rho$, empty $T$ and the eigensystem with unit level and constant data $a \equiv 2$, $b \equiv 0$, where both sides equal $2$.
--
--   **Relation to Mathlib.** Mathlib has no notion of a Galois representation being attached to a Hecke eigensystem; these predicates are the project's own, built on the project's `HeckeEigensystem` structure and on the project's valuation-theoretic predicates [`ValuationSubring.LiesOverPrime`](../def/FLTPrelim_Ramification.html#L16) and [`ValuationSubring.IsFrobeniusAt`](../def/EllipticCurve_FrobeniusTrace.html#L51).
--
--   **Where it is used.** These predicates package the conclusion needed from the Langlands–Tunnell step: the residual representation on $3$-torsion has, away from finitely many primes, Frobenius traces matching the reduction of the Satake data of a Hecke eigensystem, possibly after twisting by the quadratic character of conductor $3$. The twisted branch is what permits the subsequent correction of the weight-one form by the Eisenstein series attached to `chiNegThree`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LanglandsTunnell_IsAttached.lean

import Definitions.Def_AutomorphicForm_HeckeEigensystem
import Definitions.Def_LanglandsTunnell_ExplicitLift
import Definitions.Def_ModularForm_EisensteinChiNegThree
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_FrobeniusTrace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace LanglandsTunnell

open NumberField AutomorphicForm IsDedekindDomain EisensteinWeightOne FLT.ExplicitLift

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

def IsAttachedExact (ρ : Γℚ →* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (π₀ : HeckeEigensystem ℚ (ℤ√(-2))) (T : Finset ℕ) : Prop :=
  ∀ p : Nat.Primes, (p : ℕ) ∉ T →
    ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime (p : ℕ) →
      ∀ σ : Γℚ, A.IsFrobeniusAt σ (p : ℕ) →
        red (π₀.a ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm p))
          = ((ρ σ : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
              Matrix (Fin 2) (Fin 2) (ZMod 3)).trace

def IsAttachedTwisted (ρ : Γℚ →* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (π₀ : HeckeEigensystem ℚ (ℤ√(-2))) (T : Finset ℕ) : Prop :=
  ∀ p : Nat.Primes, (p : ℕ) ∉ T →
    ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime (p : ℕ) →
      ∀ σ : Γℚ, A.IsFrobeniusAt σ (p : ℕ) →
        red (π₀.a ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm p))
          = ((chiNegThree (p : ℕ) : ℤ) : ZMod 3)
            * ((ρ σ : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
                Matrix (Fin 2) (Fin 2) (ZMod 3)).trace

def IsAttachedUpToTwist (ρ : Γℚ →* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (π₀ : HeckeEigensystem ℚ (ℤ√(-2))) (T : Finset ℕ) : Prop :=
  IsAttachedExact ρ π₀ T ∨ IsAttachedTwisted ρ π₀ T

theorem isAttachedUpToTwist_one :
    IsAttachedUpToTwist 1 ⟨⊤, by simp, fun _ => 2, fun _ => 0⟩ ∅ :=
  Or.inl fun _ _ _ _ _ _ => by
    simp [Matrix.trace]
    exact map_ofNat red 2

end LanglandsTunnell


