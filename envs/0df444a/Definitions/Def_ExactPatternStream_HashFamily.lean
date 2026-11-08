-- Prove2me | Definitions.Def_ExactPatternStream_HashFamily
-- name    : ExactPatternStream_HashFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:03:13.540408+00:00
-- url     : https://prove2.me/theorems/d9684978-0d33-4265-8850-b79fe3f78174
-- title:
--   Proof of Lemma 7.4 — the family $\mathcal H_{L,b}$, evaluators, uniform probability
-- statement:
--   The explicit family $\mathcal H_{L,b}$ of maps $\{0,1\}^L\to\{0,1\}^b$. If $L\le b$ it holds the injection $h(x)=x\circ0^{b-L}$. If $L>b$ and $b\le3$ it holds a constant map. Otherwise, with $q=\lfloor b/2\rfloor$ and $p$ the smallest prime in $[2^{q-1},2^q]$: $\phi$ splits the input into blocks of $q-1$ bits, padding the last with zeros, giving $d=\lceil L/(q-1)\rceil$ elements of $\mathbb F_p$; $\psi$ writes both coordinates with $q$ bits and appends $b-2q$ zeros; and $h=\psi\circ R_s\circ\phi$ for a seed $s\in(\mathbb F_p^2)^D$.
--
--   An `Evaluator` has a fixed number of state bits, an initial state given a parameter, one update per input symbol, and a final output. A uniform probability is the fraction of a finite sample space.
--
--   **Formalization Note** The smallest prime $\ge2^{q-1}$ is the prime of the proof, by Bertrand's postulate. The constant map is $0^b$. The seed space has one point in the two singleton cases. The paper samples field elements by rejection, and the seed law here is the uniform one it produces.
-- source:
--   Gawrychowski, Janczewski, Jin, Nelson, An Improved Streaming Algorithm for Exact Pattern Matching (preprint, STOC 2027 submission, sha256 351218cb…), proof of Lemma 7.4, p.19 (PDF 20)

import Mathlib
import Definitions.Def_ExactPatternStream_Strings
import Definitions.Def_ExactPatternStream_LinearMaps

namespace ExactPatternStream

/-! # The explicit family `H_{L,b}`

Gawrychowski, Janczewski, Jin, Nelson (preprint, sha256 351218cb…), proof of Lemma 7.4, p.19 (PDF 20).

**Formalization Note.** The family is defined in the proof of Lemma 7.4. If `L ≤ b` it is the zero-padding
injection; if `L > b` and `b ≤ 3` it is the constant map to `0^b` (the paper says "a constant map"); then
the seed space has one point, because `hashRounds L b = 0`. Otherwise `q = ⌊b/2⌋`, `p` is the smallest prime
in `[2^{q-1}, 2^q]`, which by Bertrand's postulate is the smallest prime `≥ 2^{q-1}` (the form used here, as
it needs no hypothesis on `q`), `d = ⌈L/(q-1)⌉`, and `h = ψ ∘ R_s ∘ ϕ`. Bit strings are `List Bool`,
most significant bit first. The input is any list; the family's claims are for length `L`. The paper
samples field elements by rejection; the seed law here is the uniform law it produces. -/

/-- The `q` of the proof of Lemma 7.4. -/
def hashQ (b : ℕ) : ℕ := b / 2

/-- The smallest prime `≥ 2^{q-1}`, i.e. the smallest prime in `[2^{q-1}, 2^q]`. -/
def hashPrime (b : ℕ) : ℕ := Nat.find (Nat.exists_infinite_primes (2 ^ (hashQ b - 1)))

theorem hashPrime_prime (b : ℕ) : (hashPrime b).Prime :=
  (Nat.find_spec (Nat.exists_infinite_primes (2 ^ (hashQ b - 1)))).2

instance (b : ℕ) : Fact (hashPrime b).Prime := ⟨hashPrime_prime b⟩

/-- `d = ⌈L/(q-1)⌉`. -/
def hashBlocks (L b : ℕ) : ℕ := (L + (hashQ b - 1) - 1) / (hashQ b - 1)

open Classical in
/-- The number `D` of seed pairs: none in the two singleton cases. -/
noncomputable def hashRounds (L b : ℕ) : ℕ :=
  if L ≤ b ∨ b ≤ 3 then 0 else roundsD (hashBlocks L b)

/-- The seed space of `H_{L,b}`: `(F_p²)^D`, with `p = hashPrime b`. -/
abbrev HSeed (L b : ℕ) := Fin (hashRounds L b) → ZMod (hashPrime b) × ZMod (hashPrime b)

/-- The `q` lowest bits of `x`, most significant first. -/
def natBits (q x : ℕ) : List Bool := (List.range q).reverse.map fun j => x.testBit j

/-- The value of a bit string, most significant bit first. -/
def bitsVal (x : List Bool) : ℕ := x.foldl (fun a t => 2 * a + (if t then 1 else 0)) 0

/-- The injection `ϕ`: blocks of `q - 1` bits, the last one padded with zeros, as elements of `F_p`. -/
def hashPhi (L b : ℕ) (x : List Bool) : List (ZMod (hashPrime b)) :=
  (List.range (hashBlocks L b)).map fun r =>
    ((bitsVal ((slice (x ++ List.replicate (hashQ b - 1) false)
      (r * (hashQ b - 1)) ((r + 1) * (hashQ b - 1)))) : ℕ) : ZMod (hashPrime b))

/-- The injection `ψ`: both coordinates with `q` bits, followed by `b - 2q` zeros. -/
def hashPsi (b : ℕ) (y : List (ZMod (hashPrime b))) : List Bool :=
  (y.flatMap fun a => natBits (hashQ b) a.val) ++ List.replicate (b - 2 * hashQ b) false

open Classical in
/-- The map `h ∈ H_{L,b}` of seed `s`, `h = ψ ∘ R_s ∘ ϕ` in the main case. -/
noncomputable def hashEval (L b : ℕ) (s : HSeed L b) (x : List Bool) : List Bool :=
  if L ≤ b then x ++ List.replicate (b - L) false
  else if b ≤ 3 then List.replicate b false
  else hashPsi b (applyRounds (List.ofFn s) (hashPhi L b x))

/-- A finite-state one-pass evaluator with an explicit state size: `bits` bits of state, started from an
initial state that may depend on a parameter (a seed), updated once per input symbol, and read at the
end. The state is everything kept between symbols, so a seed the evaluator needs is in the state. -/
structure Evaluator (I A B : Type*) where
  /-- The number of working bits. -/
  bits : ℕ
  /-- The initial state. -/
  init : I → Fin bits → Bool
  /-- The update on one input symbol. -/
  step : (Fin bits → Bool) → A → Fin bits → Bool
  /-- The final output. -/
  out : (Fin bits → Bool) → B

/-- The output of an evaluator on a stream. -/
def Evaluator.run {I A B : Type*} (ev : Evaluator I A B) (i : I) (xs : List A) : B :=
  ev.out (xs.foldl ev.step (ev.init i))

/-- A uniform probability: the fraction of the finite sample space on which `E` holds. Independent uniform
coordinates are the uniform law on the product. -/
noncomputable def unifProb {Ω : Type*} [Fintype Ω] (E : Ω → Prop) : ℝ :=
  open Classical in ((Finset.univ.filter E).card : ℝ) / (Fintype.card Ω : ℝ)

end ExactPatternStream


