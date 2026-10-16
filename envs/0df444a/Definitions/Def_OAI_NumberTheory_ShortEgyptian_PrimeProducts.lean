-- Prove2me | Definitions.Def_OAI_NumberTheory_ShortEgyptian_PrimeProducts
-- name    : OAI_NumberTheory_ShortEgyptian_PrimeProducts
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T22:36:37.485204+00:00
-- url     : https://prove2.me/theorems/79d32d5a-0e36-4fc0-aff0-175d296830aa
-- title:
--   Point masses of the push-forward of the uniform distribution on a finite set
-- statement:
--   Let $A$ be a finite set with $|A|$ elements, $B$ any set, and $f:A\to B$ a map. For $b\in B$ the file defines
--
--   $$\mu_f(b)=\frac{\#\{a\in A:\ f(a)=b\}}{|A|}.$$
--
--   When $A$ is nonempty, $\mu_f$ is the distribution of $f(a)$ for $a$ drawn uniformly at random from $A$: it is nonnegative, its values sum to $1$ (only the finitely many values on the image of $f$ are nonzero), and the average of $g(f(a))$ over $a\in A$ equals $\sum_b\mu_f(b)\,g(b)$ for every function $g$ on $B$.
--
--   The definition lets averages over random choices be rewritten as weighted sums over the values they produce. In the surrounding development it is applied to maps $f$ sending a tuple of uniformly chosen primes to the residue of their product modulo $q$, so that bilinear character sums over two independent random products become bilinear forms in two probability distributions on $\mathbb{Z}/q\mathbb{Z}$, whose point masses are small by unique factorization.
--
--   **Formalization Note** The Lean name is `finiteMass`; the numerator is `Nat.card` of the fibre, and classical decidability is used. If A is empty the value is 0, because Lean's division by zero gives 0.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/PrimeProducts.lean

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/PrimeProducts.lean by skeleton subtraction
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

namespace OAI

universe uJ uA uB uE uK

namespace ShortEgyptian

open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable

noncomputable def finiteMass {A : Type uA} {B : Type uB} [Fintype A] (f : A → B) (b : B) : ℝ :=
  (Nat.card {a : A // f a = b} : ℝ) / Fintype.card A

end ShortEgyptian

end OAI


