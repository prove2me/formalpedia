-- Prove2me | Definitions.Def_HILL_PRG_Model
-- name    : HILL_PRG_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:09:33.214488+00:00
-- url     : https://prove2.me/theorems/fd67e56c-b9cc-4f86-987d-d1c6d884b1f1
-- title:
--   §§2–4 — computational and entropy model
-- statement:
--   A **function ensemble** $F$ maps a bit string of length $t_n$ to one of length $\ell_n$, with an optional integer advice value. Its evaluator and length parameters are polynomial-time, while the advice is polynomially bounded. A probabilistic adversary has one polynomial-time bit-string evaluator and polynomially many independent random coins. It sees the unary security parameter $1^n$ followed by separators, the optional unary advice, its input, and the coins. It accepts exactly when its output is the one-bit string $[1]$.
--
--   A probability is a fraction of a finite Boolean cube. The one-way condition is
--
--   $$
--   \forall A\;\forall k\;\exists N\;\forall n\ge N:\quad
--   \Pr_{x,r}[F_n(A(F_n(x),r))=F_n(x)]<n^{-k}.
--   $$
--
--   The adversary must output a string of the prescribed input length, but may return any preimage. A pseudorandom generator is polynomial-time, stretches every positive-parameter seed, and has negligible distinguishing advantage against every such adversary. Shannon and order-two Rényi entropies use base-two logarithms; statistical distance is half the $L^1$ distance. Computational, pseudo-, and false-entropy use a same-output-length polynomial-time witness law. Universal hashing means exact pairwise independence for every pair of distinct inputs and every pair of target outputs.
--
--   These definitions provide the reusable interface for the paper's chain of reductions.
--
--   **Formalization Note** The security notion is qualitative negligible success rather than the paper's time–success ratio $R$ and reduction-preservation classes. Machines are Mathlib TM2 machines. Computation with advice and hash output lengths uses unary advice. Entropy lower bounds are required for all sufficiently large $n$ to accommodate the paper's finite-parameter defects; the printed Definition 3.7 says all $n$. Expected-time adversaries are represented by worst-case polynomial-time machines, as asymptotically negligible success is preserved by truncation. A hash family's key and input lengths are computable from its output-length advice.
-- source:
--   Håstad, Impagliazzo, Levin and Luby, A pseudorandom generator from any one-way function, SIAM J. Comput. 28(4), 1999, pp. 1367–1377, Definitions 2.1, 2.3, 2.4, 2.8–2.14 and 3.1–3.9, Definition 4.6

import Mathlib
import Definitions.Def_Levin2003_owf_model

namespace HILL.PRG

abbrev Bits := Levin2003.Bits
abbrev cube := Levin2003.cube
abbrev PolyTimeComputable := Levin2003.PolyTimeComputable

/-- A polynomial bound, including the constant-size cases. -/
def IsPoly (p : ℕ → ℕ) : Prop :=
  ∃ c : ℕ, ∀ n, p n ≤ c * n ^ c + c

/-- Asymptotic negligibility; the threshold may depend on the exponent. -/
def Negligible (μ : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, ∃ N : ℕ, ∀ n ≥ N, μ n < 1 / (n : ℝ) ^ k

/-- The paper's polynomial parameter, restricted to positive security parameters. -/
def PolyParam (p : ℕ → ℝ) : Prop :=
  ∃ c : ℕ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
    1 / ((c : ℝ) * (n : ℝ) ^ c) ≤ p n ∧ p n ≤ (c : ℝ) * (n : ℝ) ^ c

/-- An integer parameter that can also be computed from unary n in polynomial time. -/
def PTimeParam (p : ℕ → ℕ) : Prop :=
  PolyParam (fun n => (p n : ℝ)) ∧
    PolyTimeComputable (fun w => List.replicate (p w.length) true)

/-- The machine receives the security parameter in unary and a separated payload. -/
def enc (n : ℕ) (w : Bits) : Bits :=
  List.replicate n true ++ false :: w

/-- Advice is a unary integer in a second separated block. -/
def encAdvice (n a : ℕ) (w : Bits) : Bits :=
  enc n (List.replicate a true ++ false :: w)

/-- A function ensemble, with advice value, security parameter, input length and output length. -/
structure FunEns where
  t : ℕ → ℕ
  ℓ : ℕ → ℕ
  f : ℕ → ℕ → Bits → Bits

/-- Uniform polynomial-time evaluation, or mildly nonuniform evaluation with integer advice. -/
def FunEns.PTime (F : FunEns) (a : ℕ → ℕ) : Prop :=
  PTimeParam F.t ∧ PTimeParam F.ℓ ∧ IsPoly a ∧
  ∃ M : Bits → Bits, PolyTimeComputable M ∧
    ∀ n x, x ∈ cube (F.t n) →
      M (encAdvice n (a n) x) = F.f (a n) n x ∧
      (F.f (a n) n x).length = F.ℓ n

/-- A uniform PPT adversary with a polynomial bound on its independent random coins. -/
structure Adv where
  run : Bits → Bits
  polyTime : PolyTimeComputable run
  coins : ℕ → ℕ
  coinsPoly : IsPoly coins

/-- Probability of an event under the uniform law on a nonempty finite sample set. -/
noncomputable def uniformProb {α : Type*} [DecidableEq α] (s : Finset α) (P : α → Prop)
    [DecidablePred P] : ℝ :=
  ((s.filter P).card : ℝ) / (s.card : ℝ)

/-- A probability weight of the image of a finite uniform source. -/
noncomputable def lawOn {α β : Type*} [DecidableEq β] (s : Finset α) (g : α → β)
    (y : β) : ℝ :=
  ((s.filter (fun x => g x = y)).card : ℝ) / (s.card : ℝ)

/-- The finite support law of a function ensemble at parameter n. -/
noncomputable def FunEns.law (F : FunEns) (a : ℕ → ℕ) (n : ℕ) (y : Bits) : ℝ :=
  lawOn (cube (F.t n)) (F.f (a n) n) y

/-- The uniform distribution on all bit strings of a fixed length. -/
noncomputable def uniformBits (n : ℕ) (y : Bits) : ℝ :=
  lawOn (cube n) id y

/-- Coin-averaged acceptance probability; only the singleton string [true] accepts. -/
noncomputable def acceptProb (A : Adv) (n : ℕ) (a : ℕ → ℕ) (y : Bits) : ℝ :=
  uniformProb (cube (A.coins n))
    (fun r => A.run (encAdvice n (a n) (y ++ r)) = [true])

/-- Inversion succeeds when the adversary returns any preimage of the sampled image. -/
noncomputable def invSucc (F : FunEns) (A : Adv) (n : ℕ) : ℝ :=
  uniformProb (cube (F.t n) ×ˢ cube (A.coins n))
    (fun z => let out := A.run (enc n (F.f 0 n z.1 ++ z.2));
      out ∈ cube (F.t n) ∧ F.f 0 n out = F.f 0 n z.1)

/-- Qualitative one-wayness of Definition 3.2. -/
def IsOWF (F : FunEns) : Prop :=
  F.PTime (fun _ => 0) ∧ ∀ A : Adv, Negligible (invSucc F A)

/-- Advantage between two laws on the same length-n output space. -/
noncomputable def advantage (A : Adv) (n : ℕ) (a : ℕ → ℕ) (ℓ : ℕ)
    (D E : Bits → ℝ) : ℝ :=
  |∑ y ∈ cube ℓ, (D y - E y) * acceptProb A n a y|

/-- Computational indistinguishability against PPT distinguishers. -/
def CompIndist (a : ℕ → ℕ) (ℓ : ℕ → ℕ)
    (D E : ℕ → Bits → ℝ) : Prop :=
  ∀ A : Adv, Negligible (fun n => advantage A n a (ℓ n) (D n) (E n))

/-- A stretching polynomial-time generator with pseudorandom output. -/
def IsPRG (G : FunEns) (a : ℕ → ℕ) : Prop :=
  G.PTime a ∧ (∀ n, 1 ≤ n → G.t n < G.ℓ n) ∧
    CompIndist a G.ℓ (G.law a) (fun n => uniformBits (G.ℓ n))

/-- Probability weights on a finite support. -/
def IsProbOn {α : Type*} [DecidableEq α] (s : Finset α) (D : α → ℝ) : Prop :=
  (∀ x ∈ s, 0 ≤ D x) ∧ (∑ x ∈ s, D x) = 1

/-- Shannon entropy of a finite weight function, in bits. -/
noncomputable def shannonOn {α : Type*} (s : Finset α) (D : α → ℝ) : ℝ :=
  ∑ x ∈ s, -(D x * Real.logb 2 (D x))

/-- Rényi entropy of order two, in bits. -/
noncomputable def renyiOn {α : Type*} (s : Finset α) (D : α → ℝ) : ℝ :=
  -Real.logb 2 (∑ x ∈ s, (D x) ^ 2)

/-- Statistical distance on a finite support. -/
noncomputable def statDistOn {α : Type*} (s : Finset α) (D E : α → ℝ) : ℝ :=
  (∑ x ∈ s, |D x - E x|) / 2

/-- Push a finite weighted law forward through a deterministic map. -/
noncomputable def weightedLaw {α β : Type*} [DecidableEq β]
    (s : Finset α) (D : α → ℝ) (g : α → β) (y : β) : ℝ :=
  ∑ x ∈ s, if g x = y then D x else 0

/-- Shannon entropy of a finite uniform seed's output law. -/
noncomputable def entropyOf {α β : Type*} [DecidableEq β] (s : Finset α) (g : α → β) : ℝ :=
  shannonOn (s.image g) (lawOn s g)

/-- Computational entropy: a same-output-length P-time witness with larger Shannon entropy. -/
def HasCompEntropy (F : FunEns) (a : ℕ → ℕ) (s : ℕ → ℝ) : Prop :=
  F.PTime a ∧ PolyParam s ∧
  ∃ W : FunEns, W.PTime a ∧ W.ℓ = F.ℓ ∧
    CompIndist a F.ℓ (F.law a) (W.law a) ∧
    ∃ N : ℕ, ∀ n ≥ N, 1 ≤ n →
      s n ≤ shannonOn (cube (F.ℓ n)) (W.law a n)

/-- Pseudoentropy exceeds the input seed length by s. -/
def IsPseudoentropyGen (F : FunEns) (a : ℕ → ℕ) (s : ℕ → ℝ) : Prop :=
  HasCompEntropy F a (fun n => (F.t n : ℝ) + s n)

/-- False entropy exceeds the actual output entropy by s. -/
def IsFalseEntropyGen (F : FunEns) (a : ℕ → ℕ) (s : ℕ → ℝ) : Prop :=
  HasCompEntropy F a
    (fun n => shannonOn (cube (F.ℓ n)) (F.law a n) + s n)

/-- A family of keyed hash functions, with lengths indexed by the security parameter. -/
structure HashFamily where
  keyLen : ℕ → ℕ
  inLen : ℕ → ℕ
  outLen : ℕ → ℕ
  eval : ℕ → Bits → Bits → Bits

/-- Polynomial-time evaluation and exact lengths of a keyed family. -/
def HashFamily.PTime (h : HashFamily) : Prop :=
  IsPoly h.keyLen ∧ IsPoly h.inLen ∧ IsPoly h.outLen ∧
  (∃ K I : Bits → Bits, PolyTimeComputable K ∧ PolyTimeComputable I ∧
    ∀ n, K (encAdvice n (h.outLen n) []) = List.replicate (h.keyLen n) true ∧
      I (encAdvice n (h.outLen n) []) = List.replicate (h.inLen n) true) ∧
  ∃ M : Bits → Bits, PolyTimeComputable M ∧
    ∀ n key x, key ∈ cube (h.keyLen n) → x ∈ cube (h.inLen n) →
      M (encAdvice n (h.outLen n) (key ++ x)) = h.eval n key x ∧
      (h.eval n key x).length = h.outLen n

/-- Definition 4.6: exact pairwise independence, including every output pair. -/
def HashFamily.IsUniversal (h : HashFamily) : Prop :=
  h.PTime ∧
  ∀ n x x' a a', x ∈ cube (h.inLen n) → x' ∈ cube (h.inLen n) →
    x ≠ x' → a ∈ cube (h.outLen n) → a' ∈ cube (h.outLen n) →
    ((cube (h.keyLen n)).filter
      (fun key => h.eval n key x = a ∧ h.eval n key x' = a')).card *
      2 ^ (2 * h.outLen n) = 2 ^ (h.keyLen n)

/-- The parity inner product on binary strings; inputs are used at their common prefix. -/
def ip (x y : Bits) : Bool :=
  ((x.zip y).filter (fun z => z.1 && z.2)).length % 2 == 1

/-- Approximate degeneracy: ceiling log base two of the number of preimages. -/
def Dtilde {α β : Type*} [DecidableEq β] (s : Finset α) (f : α → β) (z : β) : ℕ :=
  Nat.clog 2 ((s.filter (fun x => f x = z)).card)

end HILL.PRG


