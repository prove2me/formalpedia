-- Prove2me | Definitions.Def_ModularCurve_JZeroNeronAtPData
-- name    : ModularCurve_JZeroNeronAtPData
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/39049c14-1818-5f42-aaf5-f4c5557a6802
-- title:
--   Néron data at q with ranks and level-lowering detection
-- statement:
--   Fix $N\ge 1$, a prime $q$ with $q\nmid N$, a valuation subring $A$ of $\overline{\mathbb Q}$ with $q$ a non-unit of $A$ (the predicate [`ValuationSubring.LiesOverPrime`](../def/FLTPrelim_Ramification.html#L16)), and recall the structure `JZeroNeronData`, which equips $J =$ `JZero (N*q)` with three $m$-indexed chains of subgroups $\mathrm{toric}(m)\le \mathrm{fin}(m)\le \mathrm{finPart}(m)\le J[m]$, a finite Hecke-module $\Phi$ of components, and the Galois- and Hecke-compatibilities recorded there. The structure `JZeroNeronAtPData` extends that datum by two natural numbers `toricRank` $t$ and `abelianRank` $a$ together with two cardinality assertions, carried as fields: for every $m>0$, $\#\,\mathrm{toric}(m) = m^{t}$ and $\#\,\mathrm{fin}(m) = m^{t+2a}$. The remaining field is a support-transport clause at $q$-torsion: assuming `HeckeInputsAll` and `HeckeOperatorsCommuteBar` at both levels $Nq$ and $N$, for every maximal ideal $\mathfrak m$ of the Hecke polynomial ring $\mathbb T = \mathbb Z[T_\ell : \ell \text{ prime}]$ with the image of $q$ in $\mathfrak m$, and every $x \in \mathrm{fin}(q)$ which is annihilated by $\mathfrak m$ for the module structure `heckeModuleBar (N*q)` and does not lie in $\mathrm{toric}(q)$, one has `HasLowerLevelTorsion (primesOf (N*q)) 𝔪 (JZero N)`, i.e. there exists a nonzero $y \in J_0(N)$ killed by every integer lying in $\mathfrak m$ and by every $T_\ell - b \in \mathfrak m$ with $\ell \nmid Nq$. Thus the conclusion is the nonvanishing of an $\mathfrak m$-type eigenspace at level $N$, not a map of modules. The predicate `HasJZeroNeronAtPData N q hqN` asserts that such a datum exists for every choice of $A$ lying over $q$. The auxiliary `primesOf M` is the prime divisors of $M$ viewed as a finite set of `Nat.Primes`, and `mem_primesOf` identifies membership with divisibility of $M$ for $M \neq 0$.
--
--   **Relation to Mathlib.** Mathlib has no Néron model, toric part or component group for Jacobians of modular curves; these are the project's own structures. `primesOf` is Mathlib's `Nat.primeFactors` transported to the subtype `Nat.Primes`.
--
--   **Where it is used.** These data package what is needed at the prime $q$ of exact level $q$ in Mazur's principle: the ranks pin down the $q$-power toric and finite filtration steps, and the detection clause converts a non-toric $\mathfrak m$-torsion point of the finite part at level $Nq$ into an $\mathfrak m$-eigenvector at level $N$, which is the level-lowering step for the Frey curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_JZeroNeronAtPData.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronData
import Definitions.Def_ModularCurve_MazurPrincipleCore

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace ModularCurve

def primesOf (M : ℕ) : Finset Nat.Primes := (M.primeFactors).subtype Nat.Prime

theorem mem_primesOf {M : ℕ} [NeZero M] (ℓ : Nat.Primes) : ℓ ∈ primesOf M ↔ (ℓ : ℕ) ∣ M := by
  have h1 := Finset.mem_subtype (s := M.primeFactors) (a := ℓ)
  refine h1.trans ?_
  rw [Nat.mem_primeFactors]
  exact ⟨fun h => h.2.1, fun h => ⟨ℓ.2, h, NeZero.ne _⟩⟩

structure JZeroNeronAtPData (N q : ℕ) [NeZero N] [Fact q.Prime] (hqN : ¬ q ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    extends JZeroNeronData N q hqN A hA where

  toricRank : ℕ

  abelianRank : ℕ

  card_toric : ∀ m : ℕ, 0 < m → Nat.card ↥(toric m) = m ^ toricRank

  card_fin : ∀ m : ℕ, 0 < m → Nat.card ↥(fin m) = m ^ (toricRank + 2 * abelianRank)

  fin_heckeTorsion_detects_lowerLevel :
    HeckeInputsAll (N * q) → HeckeOperatorsCommuteBar (N * q) →
    HeckeInputsAll N → HeckeOperatorsCommuteBar N →
      ∀ 𝔪 : Ideal HeckeAlg, 𝔪.IsMaximal → ((q : ℕ) : HeckeAlg) ∈ 𝔪 →
        ∀ x ∈ fin q, (letI := heckeModuleBar (N * q); x ∈ heckeTorsion (JZero (N * q)) 𝔪) →
          x ∉ toric q →
            (letI := heckeModuleBar N; HasLowerLevelTorsion (primesOf (N * q)) 𝔪 (JZero N))

def HasJZeroNeronAtPData (N q : ℕ) [NeZero N] [Fact q.Prime] (hqN : ¬ q ∣ N) : Prop :=
  ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q), Nonempty (JZeroNeronAtPData N q hqN A hA)

end ModularCurve

end


