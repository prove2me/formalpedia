-- Prove2me | Definitions.Def_OAI_NumberTheory_ShortEgyptian_ListConstruction
-- name    : OAI_NumberTheory_ShortEgyptian_ListConstruction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T22:51:07.61128+00:00
-- url     : https://prove2.me/theorems/b6434b4a-827f-44ba-8b67-485493dac45b
-- title:
--   Deterministic prime products and the auxiliary common denominator
-- statement:
--   This file defines two products of natural numbers attached to finite families of primes; they provide the divisors and the common modulus in the construction of residue systems for short Egyptian fraction expansions. Throughout, $J$ and $R$ are finite index sets, $A$ is an arbitrary index set, and $\{0,1\}$ stands for the two Boolean values false and true.
--
--   1. **Deterministic product.** For $p:J\to\mathbb{N}$ and a selection vector $I\in\{0,1\}^J$,
--
--      $$\Pi_p(I)=\prod_{j\in J}\begin{cases}p_j,& I_j=1,\\ 1,& I_j=0,\end{cases}\qquad\text{that is,}\qquad \Pi_p(I)=\prod_{j\in J:\ I_j=1}p_j .$$
--
--   2. **Auxiliary denominator.** For $a\in\mathbb{N}$, $p_0:J\to\mathbb{N}$, $p:A\to\mathbb{N}$ and a family $f=(f_i)_{i\in R}$ of maps $f_i:J\times\{0,1\}\to A$,
--
--      $$D(a,p_0,p,f)=2^{a}\,\prod_{j\in J}p_0(j)\,\prod_{i\in R}\prod_{j\in J}p\big(f_i(j,0)\big)\,p\big(f_i(j,1)\big).$$
--
--   When the $p_j$ are distinct primes, the map $I\mapsto\Pi_p(I)$ is injective, so the $2^{|J|}$ deterministic products are distinct squarefree numbers. The auxiliary denominator is built so that it is divisible by $2^a$, by every deterministic product $\Pi_{p_0}(I)$, and by every *sample product* $\prod_{j\in J}p\big(f_i(j,I_j)\big)$ with $i\in R$ and $I\in\{0,1\}^J$; here each map $f_i$ chooses, for every coordinate $j$ and each of the two values of $I_j$, a prime from the pool $p(A)$. With $a$ the binary exponent of the scale, it serves as the common modulus $M$ whose divisors are used to descend from a numerator to a small residue.
--
--   **Formalization Note** The Booleans are Lean's `Bool`, written $0,1$ above for `false`, `true`. The definitions are `deterministicProduct p I` and `auxiliaryDenominator a p0 p f` (with `p0` written $p_0$ above); the sample products are `sampleProduct` from an earlier module.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/ListConstruction.lean

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/ListConstruction.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ShortEgyptianFractions mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FirstDerivative
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ReciprocalDifferences
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IntervalDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IteratedDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ParameterBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FourierDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowSpectrum
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_EmpiricalDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorWeights
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_TruncatedDivisors
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_SmoothBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorMoments
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_PrimeLists
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_PrimeProducts
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_HammingDistance
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_SamplePartitions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ProductCorrelations
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ListSelection
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_LevelSelection

namespace OAI

universe uJ uA uR

namespace ShortEgyptian

open scoped BigOperators
open Finset Classical

noncomputable def deterministicProduct {J : Type uJ} [Fintype J]
    (p : J → ℕ) (I : J → Bool) : ℕ := ∏ j, if I j then p j else 1

noncomputable def auxiliaryDenominator {J : Type uJ} {A : Type uA} {R : Type uR} [Fintype J] [Fintype R]
    (a : ℕ) (p₀ : J → ℕ) (p : A → ℕ) (f : R → (J × Bool) → A) : ℕ :=
  2^a*(∏ j,p₀ j)*(∏ i,∏ j,p (f i (j,false))*p (f i (j,true)))

end ShortEgyptian

end OAI


