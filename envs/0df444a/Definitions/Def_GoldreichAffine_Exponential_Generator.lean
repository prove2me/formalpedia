-- Prove2me | Definitions.Def_GoldreichAffine_Exponential_Generator
-- name    : GoldreichAffine_Exponential_Generator
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:11:38.772869+00:00
-- url     : https://prove2.me/theorems/4f2358d2-4a5a-408f-aeb4-bd63e17a4770
-- title:
--   Goldreich generator and the XOR–predicate family
-- statement:
--   Let $n,d,m$ be positive integers with $d\le n$. A public index tuple is an ordered list of $d$ distinct seed positions. Given a sequence $\Sigma=(\sigma_i)_{i<m}$ and a predicate $P$, the generator is
--   $$G_{P,\Sigma}(x)_i=P(x[\sigma_i]).$$
--   The public tuples are sampled independently and uniformly and the hidden seed is uniform and independent of them. The joint mass on each public-sequence/seed pair is $|\operatorname{IndexTuple}(n,d)|^{-m}2^{-n}$. For positive $a,b$, the combined predicate is
--   $$P(x)=\left(\bigoplus_{i<a}x_i\right)\oplus M(x_a,\ldots,x_{a+b-1}).$$
--   Verification accepts any $x$ whose generator output equals the observed $y$. This layer supplies the cryptographic setting; it does not assert pseudorandomness, rank or independence of approximation errors. The later analytical cost counts success through the planted seed.
--
--   **Formalization Note** Distinct ordered tuples are embeddings between finite types. The evaluation maps have natural total extensions to zero dimensions; probabilistic interpretations here use the source domain $d\le n$.
-- source:
--   Ximing Fu, Mo Li, Shihan Lyu, STOC 2027 submission #579 (October 2026), p. 3 (PDF p. 4), §2, XOR–M definition; §2.1 on p. 4 (PDF p. 5); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/579.pdf

import Definitions.Def_GoldreichAffine_Exponential_BooleanCore
open scoped BigOperators NNReal ENNReal
open MatousekLP.Codes (Word weight)
set_option autoImplicit false

namespace GoldreichAffine.Exponential

/-- Public ordered tuples have no repeated positions. -/
abbrev IndexTuple (n d : ℕ) := Fin d ↪ Fin n

def generator {n d m : ℕ} (P : Predicate d)
    (σ : Fin m → IndexTuple n d) (x : Word n) : Word m :=
  fun i => P (fun j => x (σ i j))

def xorPredicate {a b : ℕ} (M : Predicate b) : Predicate (a + b) :=
  fun x => Bool.xor (decide (Odd (weight (fun i : Fin a => x (Fin.castAdd b i)))))
    (M (fun i => x (Fin.natAdd a i)))

/-- Independent uniform sampling of each public tuple and of the hidden seed. -/
noncomputable def publicSeedMass (n d m : ℕ)
    (_ : (Fin m → IndexTuple n d) × Word n) : ℝ≥0 :=
  1 / ((Fintype.card (IndexTuple n d) : ℝ≥0) ^ m * (2 : ℝ≥0) ^ n)

def verifies {n d m : ℕ} (P : Predicate d)
    (σ : Fin m → IndexTuple n d) (y : Word m) (x : Word n) : Prop :=
  generator P σ x = y

end GoldreichAffine.Exponential


