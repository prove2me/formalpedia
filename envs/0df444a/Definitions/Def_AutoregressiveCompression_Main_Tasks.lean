-- Prove2me | Definitions.Def_AutoregressiveCompression_Main_Tasks
-- name    : AutoregressiveCompression_Main_Tasks
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:12:53.323481+00:00
-- url     : https://prove2.me/theorems/42b98639-f3ee-4262-b46e-84812df0d778
-- title:
--   The seven computational tasks of Theorem 5.1
-- statement:
--   Definitions of the seven properties of a class of distributions, each witnessed by finite Turing machines with polynomial time bounds fixed before n and the distribution: autoregressive distribution learning (Definition 4.5, in KL divergence or in statistical distance), public-coin, deterministic and inefficient-decoder universal compression (Definition 4.7), randomized universal compression at the Shannon rate with a negligible decoding error (Definitions 4.9–4.10), entropy estimation with completeness on the class and soundness on every distribution (Definition 4.12), and entropy gap testing (Definition 4.13). Here every algorithm is one finite Turing machine with one polynomial time bound, fixed before the size parameter n, the distribution and the inputs; randomized algorithms read a uniformly random coin string of polynomial length. Autoregressive learning (Definition 4.5) means: on 1ⁿ, 1^{1/ε}, 1^{1/δ} and m = ρ(n,1/ε,1/δ) independent samples, the learner outputs on every input a circuit P with rational P(u,a) ∈ (0,1) and Σₐ P(u,a) = 1 for |u| < N, and with probability ≥ 1−δ the represented law Q_P(z) = ∏ᵢ P(z_{<i}, zᵢ) satisfies KL₂(D‖Q_P) ≤ ε (or, in a learner of the other kind, Δ_tv(D,Q_P) ≤ ε). Public-coin universal compression (Definition 4.7): efficient Enc and Dec sharing a public coin string of length r(n,m) with exact decoding of every block for every coin string and expected codeword length ≤ mH(D) + m^{1−γ} for m ≥ ρ(n), with γ ∈ (0,1); deterministic means r ≡ 0; "without an efficient decoder" means Dec is an arbitrary function. Randomized universal compression (Definitions 4.9–4.10, h = H): independent coins for Enc and Dec, every block decoded with probability ≥ 1 − η(m) for a negligible η, and the same rate. Entropy estimation (Definition 4.12): an estimate E with Pr[E ≤ H(D)+ε] ≥ 1−δ for D in the class and Pr[E ≥ H(Q)−ε] ≥ 1−δ for every Q on Σ^{ℓ(D)}. Entropy gap testing (Definition 4.13): a [0,1]-valued tester and constants a, b > 0 with E_{Q^{⊗m}}[T] − E_{D^{⊗m}}[T] ≥ m^{−b} whenever m ≥ ρ(n) and H(Q) ≥ H(D) + m^{−a}.
-- source:
--   Shuichi Hirahara, Mikito Nanashima, Autoregressive Distribution Learning and Universal Compression, STOC 2027 submission #793 (October 2026), Definitions 4.5, 4.7, 4.9, 4.10, 4.12, 4.13 and footnote 7, printed pp.17–21 / PDF pp.19–23; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/793.pdf

import Mathlib
import Definitions.Def_AutoregressiveCompression_Main_Machine

/-!
The seven tasks of Theorem 5.1 of Hirahara–Nanashima, STOC 2027 submission #793
(October 2026): Definitions 4.5 (autoregressive case), 4.7, 4.9–4.10, 4.12 and
4.13, printed pp.17–21 / PDF pp.19–23.

Every algorithm is one `Program` (a finite Turing machine) with one polynomial time
bound, chosen before the size parameter `n`, the distribution and the inputs.
A randomized algorithm reads a uniform coin string of polynomial length. The
mathematical function next to each program is the output the program actually
produces on the relevant inputs (it is pinned by the `OutputsWithin` clause).
Accuracy and confidence `ε = 1/a`, `δ = 1/b` with `a, b ≥ 2` are the source's
`ε, δ ∈ (0,1)` with `ε⁻¹, δ⁻¹ ∈ ℕ`; they are given in unary.
-/

open scoped Classical

noncomputable section

namespace AutoregressiveCompression.Main

/-- Evaluate a polynomial in `(n, m)`. -/
def eval2 (p : MvPolynomial (Fin 2) ℕ) (n m : ℕ) : ℕ := MvPolynomial.eval ![n, m] p

/-- Evaluate a polynomial in `(n, ε⁻¹, δ⁻¹)`. -/
def eval3 (p : MvPolynomial (Fin 3) ℕ) (n a b : ℕ) : ℕ := MvPolynomial.eval ![n, a, b] p

/-- Footnote 7: `η` is negligible if for every constant `c > 0`, `η(m) ≤ m^{-c}` for
all sufficiently large `m`. -/
def Negligible (η : ℕ → ℝ) : Prop :=
  ∀ c : ℝ, 0 < c → ∀ᶠ m in Filter.atTop, η m ≤ (m : ℝ) ^ (-c)

/-- Law of two independent coin strings. -/
def coinPairLaw (r₁ r₂ : ℕ) : PMF ((Fin r₁ → Bool) × (Fin r₂ → Bool)) :=
  (coinLaw r₁).bind fun ω₁ => (coinLaw r₂).map fun ω₂ => (ω₁, ω₂)

variable {Sym Γ : Type} [Fintype Sym] [Fintype Γ]

/-- Definition 4.5, autoregressive hypotheses: `D` admits polynomial-time
autoregressive distribution learning. One program `L` with time polynomial `time`,
sample bound `ρ` and coin length `r`; on `1ⁿ, 1^{ε⁻¹}, 1^{δ⁻¹}`, `m = ρ(n,ε⁻¹,δ⁻¹)`
samples and its coins it outputs (the description of) a circuit, which on every
input is an autoregressive model on `Σ^{ℓ(D)}`; and the learner learns in KL
divergence or in statistical distance. -/
def AutoregressiveLearnable (𝒟 : DistributionClass Sym) : Prop :=
  ∃ (L : Program) (time : Polynomial ℕ) (ρ r : MvPolynomial (Fin 3) ℕ)
    (hyp : ℕ → ℕ → ℕ → List (List Sym) → Bits → Circuit),
    (∀ n, ∀ D ∈ 𝒟.members n, ∀ a b : ℕ, 2 ≤ a → 2 ≤ b →
      ∀ (xs : Fin (eval3 ρ n a b) → Word Sym D.length) (ω : Fin (eval3 r n a b) → Bool),
        L.OutputsWithin
            (frame [unary n, unary a, unary b, blockBits (blockList xs), coinBits ω])
            (hyp n a b (blockList xs) (coinBits ω)).bits (time.eval (n + a + b)) ∧
          (hyp n a b (blockList xs) (coinBits ω)).IsAutoregressive (Sym := Sym) D.length) ∧
    ((∀ n, ∀ D ∈ 𝒟.members n, ∀ a b : ℕ, 2 ≤ a → 2 ≤ b →
        1 - 1 / (b : ℝ) ≤ eventProbability (samplesAndCoins D.law (eval3 ρ n a b) (eval3 r n a b))
          (fun p => klBitsWeights D.law
            ((hyp n a b (blockList p.1) (coinBits p.2)).modelMass D.length) ≤
              ((1 / (a : ℝ) : ℝ) : EReal))) ∨
     (∀ n, ∀ D ∈ 𝒟.members n, ∀ a b : ℕ, 2 ≤ a → 2 ≤ b →
        1 - 1 / (b : ℝ) ≤ eventProbability (samplesAndCoins D.law (eval3 ρ n a b) (eval3 r n a b))
          (fun p => tvWeights D.law
            ((hyp n a b (blockList p.1) (coinBits p.2)).modelMass D.length) ≤ 1 / (a : ℝ))))

/-- Definition 4.7(b): the rate condition, for an encoder output function `enc`
with public coin length `r(n,m)`: for `m ≥ ρ(n)`,
`E_{X̄∼D^{⊗m}, ω}|Enc(1ⁿ, X̄; ω)| ≤ m H(D) + m^{1-γ}`. -/
def RateBound (𝒞 : DistributionClass Γ) (r : MvPolynomial (Fin 2) ℕ) (ρ : Polynomial ℕ)
    (γ : ℝ) (enc : ℕ → List (List Γ) → Bits → Bits) : Prop :=
  ∀ n, ∀ D ∈ 𝒞.members n, ∀ m : ℕ, ρ.eval n ≤ m →
    expectation (samplesAndCoins D.law m (eval2 r n m))
        (fun p => ((enc n (blockList p.1) (coinBits p.2)).length : ℝ)) ≤
      m * entropy D.law + (m : ℝ) ^ (1 - γ)

/-- Definition 4.7(c) for the encoder: on input `1ⁿ`, a block and the public coins,
the program `Enc` outputs `enc(…)` within `tE(n+m)` steps. -/
def EncoderRuns (𝒞 : DistributionClass Γ) (Enc : Program) (tE : Polynomial ℕ)
    (r : MvPolynomial (Fin 2) ℕ) (enc : ℕ → List (List Γ) → Bits → Bits) : Prop :=
  ∀ n, ∀ D ∈ 𝒞.members n, ∀ (m : ℕ) (xs : Fin m → Word Γ D.length)
    (ω : Fin (eval2 r n m) → Bool),
    Enc.OutputsWithin (frame [unary n, blockBits (blockList xs), coinBits ω])
      (enc n (blockList xs) (coinBits ω)) (tE.eval (n + m))

/-- Definition 4.7 with an efficient decoder: exact decoding of every block for
every public coin string, by a program `Dec` running in time `tD(n+m)`. -/
def IsPublicCoinCompressor (𝒞 : DistributionClass Γ) (Enc Dec : Program)
    (tE tD : Polynomial ℕ) (r : MvPolynomial (Fin 2) ℕ) (ρ : Polynomial ℕ) (γ : ℝ)
    (enc : ℕ → List (List Γ) → Bits → Bits) : Prop :=
  0 < γ ∧ γ < 1 ∧ EncoderRuns 𝒞 Enc tE r enc ∧
  (∀ n, ∀ D ∈ 𝒞.members n, ∀ (m : ℕ) (xs : Fin m → Word Γ D.length)
    (ω : Fin (eval2 r n m) → Bool),
    Dec.OutputsWithin (frame [unary n, enc n (blockList xs) (coinBits ω), coinBits ω])
      (blockBits (blockList xs)) (tD.eval (n + m))) ∧
  RateBound 𝒞 r ρ γ enc

/-- Definition 4.7: polynomial-time public-coin universal compression. -/
def PublicCoinCompressible (𝒞 : DistributionClass Γ) : Prop :=
  ∃ (Enc Dec : Program) (tE tD : Polynomial ℕ) (r : MvPolynomial (Fin 2) ℕ)
    (ρ : Polynomial ℕ) (γ : ℝ) (enc : ℕ → List (List Γ) → Bits → Bits),
    IsPublicCoinCompressor 𝒞 Enc Dec tE tD r ρ γ enc

/-- Definition 4.7, `r ≡ 0`: polynomial-time deterministic universal compression. -/
def DeterministicCompressible (𝒞 : DistributionClass Γ) : Prop :=
  ∃ (Enc Dec : Program) (tE tD : Polynomial ℕ) (ρ : Polynomial ℕ) (γ : ℝ)
    (enc : ℕ → List (List Γ) → Bits → Bits),
    IsPublicCoinCompressor 𝒞 Enc Dec tE tD 0 ρ γ enc

/-- Definition 4.7 without an efficient decoder: the encoder is efficient, and `Dec`
is any function satisfying exact decoding (a). -/
def PublicCoinCompressibleInefficientDecoder (𝒞 : DistributionClass Γ) : Prop :=
  ∃ (Enc : Program) (tE : Polynomial ℕ) (r : MvPolynomial (Fin 2) ℕ) (ρ : Polynomial ℕ)
    (γ : ℝ) (enc : ℕ → List (List Γ) → Bits → Bits)
    (dec : ℕ → Bits → Bits → List (List Γ)),
    0 < γ ∧ γ < 1 ∧ EncoderRuns 𝒞 Enc tE r enc ∧
    (∀ n, ∀ D ∈ 𝒞.members n, ∀ (m : ℕ) (xs : Fin m → Word Γ D.length)
      (ω : Fin (eval2 r n m) → Bool),
      dec n (enc n (blockList xs) (coinBits ω)) (coinBits ω) = blockList xs) ∧
    RateBound 𝒞 r ρ γ enc

/-- Definitions 4.9–4.10 with `h = H`: polynomial-time randomized universal
compression (Yao's effective entropy coincides with Shannon entropy). `Enc` and
`Dec` use independent coin strings of lengths `rE(n,m)`, `rD(n,m)`; every block is
decoded with probability `≥ 1 - η(m)` for a negligible `η : ℕ → [0,1]`. -/
def RandomizedCompressible (𝒞 : DistributionClass Γ) : Prop :=
  ∃ (Enc Dec : Program) (tE tD : Polynomial ℕ) (rE rD : MvPolynomial (Fin 2) ℕ)
    (ρ : Polynomial ℕ) (γ : ℝ) (η : ℕ → ℝ)
    (enc : ℕ → List (List Γ) → Bits → Bits) (dec : ℕ → Bits → Bits → Bits),
    0 < γ ∧ γ < 1 ∧ (∀ m, 0 ≤ η m ∧ η m ≤ 1) ∧ Negligible η ∧
    EncoderRuns 𝒞 Enc tE rE enc ∧
    (∀ n, ∀ D ∈ 𝒞.members n, ∀ (m : ℕ) (xs : Fin m → Word Γ D.length)
      (ωE : Fin (eval2 rE n m) → Bool) (ωD : Fin (eval2 rD n m) → Bool),
      Dec.OutputsWithin (frame [unary n, enc n (blockList xs) (coinBits ωE), coinBits ωD])
        (dec n (enc n (blockList xs) (coinBits ωE)) (coinBits ωD)) (tD.eval (n + m))) ∧
    (∀ n, ∀ D ∈ 𝒞.members n, ∀ (m : ℕ) (xs : Fin m → Word Γ D.length),
      1 - η m ≤ eventProbability (coinPairLaw (eval2 rE n m) (eval2 rD n m))
        (fun ω => dec n (enc n (blockList xs) (coinBits ω.1)) (coinBits ω.2) =
          blockBits (blockList xs))) ∧
    RateBound 𝒞 rE ρ γ enc

/-- Definition 4.12: polynomial-time entropy estimation. One program `E` with coin
length `r` and sample bound `ρ`, outputting a rational estimate; completeness on
every `D ∈ 𝒞ₙ` and soundness for every distribution `Q` on `Γ^{ℓ(D)}`. -/
def EntropyEstimable (𝒞 : DistributionClass Γ) : Prop :=
  ∃ (E : Program) (time : Polynomial ℕ) (ρ r : MvPolynomial (Fin 3) ℕ)
    (est : ℕ → ℕ → ℕ → List (List Γ) → Bits → ℚ),
    (∀ n, ∀ D ∈ 𝒞.members n, ∀ a b : ℕ, 2 ≤ a → 2 ≤ b →
      ∀ (xs : Fin (eval3 ρ n a b) → Word Γ D.length) (ω : Fin (eval3 r n a b) → Bool),
        E.OutputsWithin
          (frame [unary n, unary a, unary b, blockBits (blockList xs), coinBits ω])
          (ratBits (est n a b (blockList xs) (coinBits ω))) (time.eval (n + a + b))) ∧
    (∀ n, ∀ D ∈ 𝒞.members n, ∀ a b : ℕ, 2 ≤ a → 2 ≤ b →
      1 - 1 / (b : ℝ) ≤ eventProbability (samplesAndCoins D.law (eval3 ρ n a b) (eval3 r n a b))
        (fun p => ((est n a b (blockList p.1) (coinBits p.2) : ℚ) : ℝ) ≤
          entropy D.law + 1 / (a : ℝ))) ∧
    (∀ n, ∀ D ∈ 𝒞.members n, ∀ a b : ℕ, 2 ≤ a → 2 ≤ b →
      ∀ Q : PMF (Word Γ D.length),
      1 - 1 / (b : ℝ) ≤ eventProbability (samplesAndCoins Q (eval3 ρ n a b) (eval3 r n a b))
        (fun p => entropy Q - 1 / (a : ℝ) ≤
          ((est n a b (blockList p.1) (coinBits p.2) : ℚ) : ℝ)))

/-- Definition 4.13: polynomial-time entropy gap testing. One program `T` with
coin length `r(n,m)`, rational output in `[0,1]`, constants `a, b > 0` and a
polynomial `ρ`: for `m ≥ ρ(n)` and every `Q` on `Γ^{ℓ(D)}` with
`H(Q) ≥ H(D) + m^{-a}`, `E_{Q^{⊗m}}[T] - E_{D^{⊗m}}[T] ≥ m^{-b}` (expectations
also over the coins of `T`). -/
def EntropyGapTestable (𝒞 : DistributionClass Γ) : Prop :=
  ∃ (T : Program) (time : Polynomial ℕ) (r : MvPolynomial (Fin 2) ℕ) (ρ : Polynomial ℕ)
    (a b : ℝ) (test : ℕ → List (List Γ) → Bits → ℚ),
    0 < a ∧ 0 < b ∧
    (∀ n, ∀ D ∈ 𝒞.members n, ∀ (m : ℕ) (xs : Fin m → Word Γ D.length)
      (ω : Fin (eval2 r n m) → Bool),
      T.OutputsWithin (frame [unary n, blockBits (blockList xs), coinBits ω])
          (ratBits (test n (blockList xs) (coinBits ω))) (time.eval (n + m)) ∧
        0 ≤ test n (blockList xs) (coinBits ω) ∧ test n (blockList xs) (coinBits ω) ≤ 1) ∧
    (∀ n, ∀ D ∈ 𝒞.members n, ∀ m : ℕ, ρ.eval n ≤ m →
      ∀ Q : PMF (Word Γ D.length), entropy D.law + (m : ℝ) ^ (-a) ≤ entropy Q →
        (m : ℝ) ^ (-b) ≤
          expectation (samplesAndCoins Q m (eval2 r n m))
              (fun p => ((test n (blockList p.1) (coinBits p.2) : ℚ) : ℝ)) -
            expectation (samplesAndCoins D.law m (eval2 r n m))
              (fun p => ((test n (blockList p.1) (coinBits p.2) : ℚ) : ℝ)))

end AutoregressiveCompression.Main


