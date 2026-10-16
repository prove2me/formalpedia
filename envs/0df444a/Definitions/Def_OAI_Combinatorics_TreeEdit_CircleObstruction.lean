-- Prove2me | Definitions.Def_OAI_Combinatorics_TreeEdit_CircleObstruction
-- name    : OAI_Combinatorics_TreeEdit_CircleObstruction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T01:33:05.767478+00:00
-- url     : https://prove2.me/theorems/a3059771-c5fa-489b-bdc8-286e794173fa
-- title:
--   Parameters, prime pool and moduli of the circle-tree obstruction
-- statement:
--   This file fixes the numerical data of the circle-tree lower bound as functions of a natural number $k$. Here $\operatorname{Sym}(X)$ is the group of permutations of a finite set $X$.
--
--   1. **Branching** $m(k)=16k\cdot k^2=16k^3$: the number of children of each node, arranged in $g=16k$ groups of $s=k^2$.
--   2. **Resolution** $R(k)=k^{8k}$: the number of bins quantizing each leaf phase.
--   3. **Cutoff** $Q(k)=k^{12k}$: the threshold separating high from low centered frequencies.
--   4. **Repetitions** $T(k)=k^{52k}$: the number of rows in each internal node's word.
--   5. **Prime pool** $\mathcal{P}_k$: the primes $p$ with $k^2<p\le k^3$, each identified with its value; every pool element is a prime in this range.
--   6. **Residue modulus** $L(k)=\prod_{p\in\mathcal{P}_k}p$, which is positive.
--   7. **All periods.** For an injective list $j:\{0,\dots,16k-1\}\to\mathcal{P}_k$ and $\sigma\in\operatorname{Sym}(\mathcal{P}_k)$, let $P_\sigma=\prod_{q<16k}\sigma(j(q))$ be the period selected by $\sigma$, and
--
--      $$\Pi(j)=\prod_{\sigma\in\operatorname{Sym}(\mathcal{P}_k)}P_\sigma.$$
--
--   8. **Fine modulus**
--
--      $$M(j)=R(k)\cdot\Bigl(2\,Q(k)\,\bigl((m(k)+1)\,Q(k)+1\bigr)\cdot\Pi(j)\Bigr).$$
--
--   The residue modulus is divisible by every pool prime, so a uniform residue modulo $L(k)$ reduces to a uniform residue modulo each selected prime. The fine modulus is a common multiple of $R(k)$, $Q(k)$, $2$ and every possible period $P_\sigma$, and it exceeds $(m(k)+1)Q(k)$; sampling leaf phases on the grid $\mathbb{Z}/M(j)\mathbb{Z}$ therefore represents the bins, the row drifts, the frequency cutoff and the half-turn $M(j)/2$ exactly. Every period satisfies $P_\sigma\le k^{48k}$, so $P_\sigma/T(k)\le k^{-4k}$ and $R(k)/Q(k)=k^{-4k}$: these are the two small ratios that drive the obstruction.
--
--   **Formalization Note** The Lean names are `branching`, `resolution`, `cutoff`, `repetitions`, `Pool k` (the subtype of `PrimeSupply.band k 2`, with the instance `poolFintype` and the value map `poolPrime`), `residueModulus` (with `pool_properties`, `residueModulus_pos` and the instance `residueModulus_neZero`), `allPeriods j` and `fineModulus j`, where `j : Fin (16*k) ↪ Pool k`. Branching is written `16 * k * k ^ 2`, literally $g\cdot s$ with $g=16k$ and $s=k^2$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TreeEdit/CircleObstruction.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TreeEdit/CircleObstruction.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TreeEdit mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_TreeEdit
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model
import Definitions.Def_OAI_Combinatorics_TreeEdit_FiniteProbability
import Definitions.Def_OAI_Combinatorics_TreeEdit_EditMetric
import Definitions.Def_OAI_Combinatorics_TreeEdit_Alignments
import Definitions.Def_OAI_Combinatorics_TreeEdit_SegmentComparison
import Definitions.Def_OAI_Combinatorics_TreeEdit_CyclicWords
import Definitions.Def_OAI_Combinatorics_TreeEdit_TreeArithmetic
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleTree
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleSeparation
import Definitions.Def_OAI_Combinatorics_TreeEdit_RandomCircle
import Definitions.Def_OAI_Combinatorics_TreeEdit_FiniteFourier
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleFourier
import Definitions.Def_OAI_Combinatorics_TreeEdit_SampledSpectrum
import Definitions.Def_OAI_Combinatorics_TreeEdit_PrimeSupply

namespace OAI

namespace TreeEdit.TorusTree
open scoped BigOperators
open Classical Filter FiniteProbability

def branching (k : ℕ) : ℕ := 16 * k * k ^ 2
def resolution (k : ℕ) : ℕ := k ^ (8 * k)
def cutoff (k : ℕ) : ℕ := k ^ (12 * k)
def repetitions (k : ℕ) : ℕ := k ^ (52 * k)
noncomputable def Pool (k : ℕ) := {p // p ∈ PrimeSupply.band k 2}
noncomputable instance poolFintype (k : ℕ) : Fintype (Pool k) := inferInstanceAs (Fintype {p // p ∈ PrimeSupply.band k 2})
noncomputable def poolPrime {k : ℕ} (p : Pool k) : ℕ := p.val
noncomputable def residueModulus (k : ℕ) : ℕ := ∏ p : Pool k, poolPrime p

lemma pool_properties {k : ℕ} (p : Pool k) : Nat.Prime (poolPrime p) ∧ k ^ 2 < poolPrime p ∧ poolPrime p ≤ k ^ 3 :=
  PrimeSupply.mem_band p.property

lemma residueModulus_pos (k : ℕ) : 0 < residueModulus k :=
  product_positive _ (fun p => (pool_properties p).1.pos)

noncomputable instance residueModulus_neZero (k : ℕ) : NeZero (residueModulus k) := ⟨(residueModulus_pos k).ne'⟩

end TreeEdit.TorusTree

namespace TreeEdit.TorusTree
open scoped BigOperators
open Classical Filter

noncomputable def allPeriods {k : ℕ} (j : Fin (16*k) ↪ Pool k) : ℕ :=
  ∏ σ : Equiv.Perm (Pool k), period poolPrime j σ

noncomputable def fineModulus {k : ℕ} (j : Fin (16*k) ↪ Pool k) : ℕ :=
  resolution k * (2 * cutoff k * ((branching k+1)*cutoff k+1) * allPeriods j)

end TreeEdit.TorusTree

end OAI


