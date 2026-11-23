-- Prove2me | Definitions.Def_NonmonotoneSubmod_RandomSet_Supplement_Succinct
-- name    : NonmonotoneSubmod_RandomSet_Supplement_Succinct
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T09:10:52.505933+00:00
-- url     : https://prove2.me/theorems/853794ec-9461-4469-ac2c-8023078c24e5
-- title:
--   §4 — succinct instances and polynomial approximation
-- statement:
--   A succinct instance consists of a finite ground set and an explicit list of nonnegative submodular building blocks. Each block has an injective list of element labels and a complete rational table. Its value on a set is the table value on the elements of that set lying in the block. The objective is
--   $$f(S)=\sum_{B}g_B(S\cap B).$$
--
--   For every fixed arity bound $K$, a polynomial approximation algorithm is one deterministic Turing machine, polynomial in the full encoded input length, returning a subset $S$ on every valid instance and satisfying
--   $$r\operatorname{OPT}\le f(S).$$
--
--   The symmetric version promises complement symmetry of the entire objective, without requiring each block to be symmetric. Arity is fixed before the input; the machine and its polynomial may depend on $K$ and the fixed ratio. No normalization or monotonicity is imposed. The maximum is the published finite maximum over all subsets, including the empty subset. This supplies the algorithmic domain for both companion theorems.
--
--   **Formalization Note** All ground sets are labelled by $\{0,\ldots,n-1\}$. The published binary numeral codes double each bit and end with 01; integers add a sign bit and reduced rationals encode numerator and denominator. Tables are encoded in increasing binary-mask order. Rational tables give a stronger hardness claim already on this subclass of the source's finite representations; every algorithm for the whole source class must work on these inputs. The input contains the full table of each constant-size block, rather than the exponential table of the whole function. Time is actual Turing-machine bit time, not a bound on output length. Sparse outputs avoid an artificial complexity obstruction from isolated elements.
-- source:
--   Feige, Mirrokni, Vondrák, Maximizing Non-Monotone Submodular Functions, SIAM J. Comput. 40(4):1133–1153, 2011, DOI 10.1137/090779346; p. 1144, succinct representation paragraph

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_Shared_SymmetricSetFun
import Definitions.Def_NonmonotoneSubmod_Shared_OPT
import Definitions.Def_OptimalQueuingComplexity_Restless_encNat

open OptimalQueuingComplexity.Restless

namespace NonmonotoneSubmod.RandomSet.Supplement

/-- Sparse output: cardinality followed by increasing binary element labels. -/
def encSubset {n : ℕ} (S : Finset (Fin n)) : List Bool :=
  encNat S.card ++ (S.sort (· ≤ ·)).flatMap (fun i => encNat i.val)

/-- One explicit rational-valued table on k labelled elements of a ground set Fin n. -/
structure Block (n : ℕ) where
  arity : ℕ
  label : Fin arity → Fin n
  table : Finset (Fin arity) → ℚ

/-- A finite list of building blocks; no normalization or monotonicity is imposed. -/
structure SuccinctInstance where
  n : ℕ
  blocks : List (Block n)

/-- The order of subset tables is fixed by the increasing binary mask. -/
def Block.encodeTable {n : ℕ} (b : Block n) : List Bool :=
  (List.finRange (2 ^ b.arity)).flatMap fun mask =>
    encRat (b.table (Finset.univ.filter (fun i => (Nat.testBit mask.val i.val))))

/-- Table entries in binary-mask order, all labels and dimensions in binary. -/
def SuccinctInstance.encode (I : SuccinctInstance) : List Bool :=
  encNat I.n ++ encNat I.blocks.length ++ I.blocks.flatMap (fun b =>
    encNat b.arity ++ (List.finRange b.arity).flatMap (fun i => encNat (b.label i).val) ++
      b.encodeTable)

def Block.value {n : ℕ} (b : Block n) (S : Finset (Fin n)) : ℝ :=
  b.table (Finset.univ.filter (fun i => b.label i ∈ S))

def SuccinctInstance.value (I : SuccinctInstance) (S : Finset (Fin I.n)) : ℝ :=
  (I.blocks.map (fun b => b.value S)).sum

/-- Each block has constant arity, is nonnegative and satisfies Definition 1.1.
K is fixed before the input, not an instance-dependent asymptotic constant. -/
def SuccinctInstance.Valid (I : SuccinctInstance) (K : ℕ) : Prop :=
  ∀ b ∈ I.blocks, b.arity ≤ K ∧ Function.Injective b.label ∧
    (∀ S, 0 ≤ b.table S) ∧
    NonmonotoneSubmod.Shared.Submodular (fun S => (b.table S : ℝ))

/-- On every fixed arity class, one deterministic bit-time polynomial algorithm outputs
an actual subset whose objective is at least r times the finite maximum. The algorithm
may depend on K and r, while its exponent is independent of the input. -/
def HasPolyApprox (r : ℝ) (symmetric : Bool) : Prop :=
  ∀ K : ℕ, ∃ A : List Bool → List Bool,
    CookPvsNP.PolyTimeComputable A ∧
    ∀ I : SuccinctInstance, I.Valid K →
      (symmetric = true → NonmonotoneSubmod.Shared.SymmetricSetFun I.value) →
      ∃ S : Finset (Fin I.n), A I.encode = encSubset S ∧
        r * NonmonotoneSubmod.Shared.OPT I.value ≤ I.value S

end NonmonotoneSubmod.RandomSet.Supplement


