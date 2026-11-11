-- Prove2me | Definitions.Def_EditPRC_Boost_PRC
-- name    : EditPRC_Boost_PRC
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T05:08:47.588721+00:00
-- url     : https://prove2.me/theorems/b178b6b0-2e41-4a42-9b83-6d8dd0641160
-- title:
--   Secret-key pseudorandom codes: syntax, rate, pseudorandomness, soundness and edit robustness (Definition 2.1)
-- statement:
--   Let $M$ (the message alphabet, written $\Gamma$ in Definition 2.1) and $S$ (the codeword alphabet, written $\Sigma$) be finite alphabets. A **secret-key pseudorandom code** (PRC) $P$ consists of, for every security parameter $\lambda$, a key length $\kappa(\lambda)$, message length $k(\lambda)$, blocklength $n(\lambda)$, and three algorithms:
--   1. $\mathrm{KeyGen}(1^\lambda)$, randomized, outputs a secret key $\mathrm{sk}\in\{0,1\}^{\kappa(\lambda)}$;
--   2. $\mathrm{Enc}_{\mathrm{sk}}(m)$, randomized, maps a message $m \in M^{k(\lambda)}$ to a codeword in $S^{n(\lambda)}$;
--   3. $\mathrm{Dec}_{\mathrm{sk}}(y)$, deterministic, maps **every** string $y \in S^\star$ to a message or to $\bot$.
--
--   The **relative rate** is $\dfrac{k(\lambda)\log|M|}{n(\lambda)\log|S|}$. $P$ is **efficient** if the three algorithms are computed in polynomial time (on the encodings of their inputs, which include $1^\lambda$; KeyGen and Enc read polynomially many coins).
--
--   **Pseudorandomness.** For an oracle distinguisher $D$, let $\Pr[D^{\mathrm{Enc}_{\mathrm{sk}}(\cdot)}(1^\lambda)=1]$ be taken over $\mathrm{sk}\leftarrow\mathrm{KeyGen}(1^\lambda)$, the coins of $D$ and fresh coins of Enc for every oracle call (the query is read as a message chosen by $D$), and let $\Pr[D^{\mathcal U}(1^\lambda)=1]$ be taken over the coins of $D$ and a fresh uniformly random string of $S^{n(\lambda)}$ answered on every call. $P$ is pseudorandom if for every polynomial-time $D$ the advantage
--   $$\mathrm{adv}_D(\lambda)=\Bigl|\Pr[D^{\mathrm{Enc}_{\mathrm{sk}}(\cdot)}(1^\lambda)=1]-\Pr[D^{\mathcal U}(1^\lambda)=1]\Bigr|$$
--   is negligible. With **sub-exponential security** $s(\lambda)=\lambda^c$ ($c>0$): every distinguisher running in time $2^{C\lambda^c}$ (for some $C$) has, for every $K$, advantage at most $2^{-K\lambda^c}$ for all large $\lambda$.
--
--   **Soundness.** There is one negligible $\nu$ with $\Pr_{\mathrm{sk}}[\mathrm{Dec}_{\mathrm{sk}}(y)=\bot]\ge 1-\nu(\lambda)$ for every $\lambda$ and every fixed $y\in S^\star$.
--
--   **Edit robustness.** With the unit-cost edit distance $D_E$ (insertions, deletions and substitutions each cost $1$) and the ball $B_E(x,\varepsilon)=\{x'\in S^\star : D_E(x,x')\le\varepsilon|x|\}$, $P$ is strongly-adaptively robust to an $\varepsilon$ fraction of edits if there is one negligible $\nu$ with
--   $$\Pr_{\mathrm{sk}\leftarrow\mathrm{KeyGen}(1^\lambda),\ x\leftarrow\mathrm{Enc}_{\mathrm{sk}}(m)}\bigl[\forall x'\in B_E(x,\varepsilon):\ \mathrm{Dec}_{\mathrm{sk}}(x')=m\bigr]\ \ge\ 1-\nu(\lambda)$$
--   for every $\lambda$ and every $m\in M^{k(\lambda)}$. The universal quantifier sits inside the probability: the corruption may be chosen after seeing the key and the codeword.
--
--   A PRC in the sense of Definition 2.1 is an efficient, pseudorandom and sound code; its robustness is stated separately, with the radius $\varepsilon$ as a parameter. These are the objects in both the hypothesis and the conclusion of Theorem 3.12.
--
--   **Formalization Note.** Negligible functions are `QuantumPRC.Negligible` ($|\nu(\lambda)|<\lambda^{-c}$ for all large $\lambda$, for every $c>0$); the edit distance is the published `OAI.EditDistortion.edit`. Keys and coins are `Fin _ → Bool`, codewords `Fin n → S`, and $\mathrm{Dec}$ takes a `List S`. The probability of an event is its uniform probability over all coin strings, with one independent coin string per oracle call.
-- source:
--   Gozon, Edit-Robust Pseudorandom Codes, Watermarks, and Steganography, STOC 2027 submission (manuscript sha256 73170029…6b60), p. 8 (notation: s(λ), negl, B_E, D_E), p. 9, Definition 2.1, p. 10 (strongly-adaptive robustness; λ = n)

import Mathlib
import Definitions.Def_EditPRC_Boost_Machine
import Definitions.Def_EditDistance
import Definitions.Def_QuantumPRC_Negligible

set_option autoImplicit false

namespace EditPRC.Boost

/-!
# Secret-key pseudorandom codes (Definition 2.1) with edit robustness

Gozon, *Edit-Robust Pseudorandom Codes, Watermarks, and Steganography*, STOC 2027 submission
(manuscript sha256 73170029…6b60), p. 8 (edit distance `D_E`, ball `B_E(x, ε)`, notation
`s(λ)`), p. 9, Definition 2.1, p. 10 (strongly-adaptive robustness; `λ = n`).

* `M` is the message alphabet (the paper's `Γ` in Definition 2.1), `S` the codeword alphabet
  (`Σ`). A secret key is a bit string of length `keyLen λ`, a message a string in
  `M^{msgLen λ}`, a codeword a string in `S^{blockLen λ}`.
* `keyGen` and `enc` are randomized: they read `keyCoins λ` resp. `encCoins λ` fair coins. `dec`
  is deterministic and accepts every string of `S★`; `none` is `⊥`.
* Pseudorandomness: the oracle `Enc_sk(·)` reads its query as a message and encodes it with
  fresh coins on every call; the oracle `𝒰` answers every call with a fresh uniform string of
  `S^{blockLen λ}`.
* Negligible functions are `QuantumPRC.Negligible`: `|ν λ| < λ^{-c}` eventually, for every
  `c > 0`.
-/

open Filter

/-- The syntax of a secret-key pseudorandom code with message alphabet `M` and codeword
alphabet `S` (Definition 2.1, "Syntax"). -/
structure PRC (M S : Type) [Fintype M] [Fintype S] where
  /-- Secret key length `κ(λ)`. -/
  keyLen : ℕ → ℕ
  /-- Message length `k(λ)`. -/
  msgLen : ℕ → ℕ
  /-- Blocklength `n(λ)`. -/
  blockLen : ℕ → ℕ
  /-- Number of coins read by `KeyGen(1^λ)`. -/
  keyCoins : ℕ → ℕ
  /-- Number of coins read by one call of `Enc`. -/
  encCoins : ℕ → ℕ
  /-- `KeyGen(1^λ)` on its coins. -/
  keyGen : (lam : ℕ) → (Fin (keyCoins lam) → Bool) → Fin (keyLen lam) → Bool
  /-- `Enc_sk(m)` on its coins. -/
  enc : (lam : ℕ) → (Fin (keyLen lam) → Bool) → (Fin (msgLen lam) → M) →
    (Fin (encCoins lam) → Bool) → Fin (blockLen lam) → S
  /-- `Dec_sk(y)` for every `y ∈ S★`; `none` is `⊥`. -/
  dec : (lam : ℕ) → (Fin (keyLen lam) → Bool) → List S → Option (Fin (msgLen lam) → M)

variable {M S : Type} [Fintype M] [Fintype S]

/-- The bit encoding of an output of `Dec`: `⊥` is `[false]`, a message `m` is
`true :: strCode m`. -/
noncomputable def decCode {k : ℕ} : Option (Fin k → M) → List Bool
  | none => [false]
  | some m => true :: strCode (List.ofFn m)

/-- `KeyGen`, `Enc` and `Dec` are polynomial-time randomized algorithms: polynomially many coins,
and each is computed on the bit encoding of its inputs (which include `1^λ`) by one machine in
polynomial time. -/
def PRC.Efficient (P : PRC M S) : Prop :=
  PolyBounded P.keyCoins ∧ PolyBounded P.encCoins ∧
  (∃ F : List Bool → List Bool, PolyTimeFn F ∧
    ∀ (lam : ℕ) (r : Fin (P.keyCoins lam) → Bool),
      F (tup [unary lam, List.ofFn r]) = List.ofFn (P.keyGen lam r)) ∧
  (∃ F : List Bool → List Bool, PolyTimeFn F ∧
    ∀ (lam : ℕ) (sk : Fin (P.keyLen lam) → Bool) (m : Fin (P.msgLen lam) → M)
      (ρ : Fin (P.encCoins lam) → Bool),
      F (tup [unary lam, List.ofFn sk, strCode (List.ofFn m), List.ofFn ρ]) =
        strCode (List.ofFn (P.enc lam sk m ρ))) ∧
  (∃ F : List Bool → List Bool, PolyTimeFn F ∧
    ∀ (lam : ℕ) (sk : Fin (P.keyLen lam) → Bool) (y : List S),
      F (tup [unary lam, List.ofFn sk, strCode y]) = decCode (P.dec lam sk y))

/-- The number of bits of one oracle answer (an encoded codeword) at security parameter `λ`. -/
noncomputable def PRC.ansLen (P : PRC M S) (lam : ℕ) : ℕ := P.blockLen lam * symWidth S

/-- `Pr_{sk ← KeyGen(1^λ)}[Dist^{Enc_sk(·)}(1^λ) = 1]`: over the coins of `KeyGen`, of `Dist`,
and one independent coin string of `Enc` for each oracle call. -/
noncomputable def PRC.realAccept [Nonempty M] (P : PRC M S) (D : OracleAlg) (lam : ℕ) : ℝ :=
  unifProb (fun ω : (Fin (P.keyCoins lam) → Bool) × (Fin (D.coins lam) → Bool) ×
      (Fin (D.rounds lam) → Fin (P.encCoins lam) → Bool) =>
    D.output lam ω.2.1 (fun i q =>
      if h : i < D.rounds lam then
        strCode (List.ofFn (P.enc lam (P.keyGen lam ω.1) (msgParse (P.msgLen lam) q)
          (ω.2.2 ⟨i, h⟩)))
      else []) = true)

/-- `Pr_𝒰[Dist^𝒰(1^λ) = 1]`: over the coins of `Dist` and one independent uniform string of
`S^{n(λ)}` for each oracle call. -/
noncomputable def PRC.idealAccept (P : PRC M S) (D : OracleAlg) (lam : ℕ) : ℝ :=
  unifProb (fun ω : (Fin (D.coins lam) → Bool) × (Fin (D.rounds lam) → Fin (P.blockLen lam) → S) =>
    D.output lam ω.1 (fun i _ =>
      if h : i < D.rounds lam then strCode (List.ofFn (ω.2 ⟨i, h⟩)) else []) = true)

/-- The distinguishing advantage of `D` at security parameter `λ`. -/
noncomputable def PRC.advantage [Nonempty M] (P : PRC M S) (D : OracleAlg) (lam : ℕ) : ℝ :=
  |P.realAccept D lam - P.idealAccept D lam|

/-- Undetectability / pseudorandomness: every polynomial-time oracle distinguisher has negligible
advantage. -/
def PRC.Pseudorandom [Nonempty M] (P : PRC M S) : Prop :=
  ∀ D : OracleAlg, D.PolyTime P.ansLen → QuantumPRC.Negligible (P.advantage D)

/-- Pseudorandomness with **sub-exponential security** `s(λ) = λ^c` (p. 8): every distinguisher
running in time `2^{O(λ^c)}` has advantage `2^{-ω(λ^c)}`. -/
def PRC.SubexpPseudorandom [Nonempty M] (P : PRC M S) (c : ℝ) : Prop :=
  ∀ (D : OracleAlg) (C : ℝ),
    D.RunsWithin P.ansLen (fun lam => (2 : ℝ) ^ (C * (lam : ℝ) ^ c)) →
    ∀ K : ℝ, ∀ᶠ lam in atTop, P.advantage D lam ≤ (2 : ℝ) ^ (-(K * (lam : ℝ) ^ c))

/-- Soundness: one negligible `ν` such that for every `λ` and every fixed `y ∈ S★`,
`Pr_{sk ← KeyGen(1^λ)}[Dec_sk(y) = ⊥] ≥ 1 − ν(λ)`. -/
def PRC.Sound (P : PRC M S) : Prop :=
  ∃ ν : ℕ → ℝ, QuantumPRC.Negligible ν ∧ ∀ (lam : ℕ) (y : List S),
    1 - ν lam ≤ unifProb (fun r : Fin (P.keyCoins lam) → Bool => P.dec lam (P.keyGen lam r) y = none)

/-- The edit ball `B_E(x, ε) = {x' ∈ S★ : D_E(x, x') ≤ ε|x|}`, with `D_E` the unit-cost
insertion/deletion/substitution distance `OAI.EditDistortion.edit`. -/
def editBall (x : List S) (ε : ℝ) : Set (List S) :=
  {x' | (OAI.EditDistortion.edit x x' : ℝ) ≤ ε * x.length}

/-- Strongly-adaptive robustness to an `ε` fraction of edits: one negligible `ν` such that for
every `λ` and every message `m`,
`Pr_{sk ← KeyGen(1^λ), x ← Enc_sk(m)}[∀ x' ∈ B_E(x, ε), Dec_sk(x') = m] ≥ 1 − ν(λ)`. -/
def PRC.EditRobust (P : PRC M S) (ε : ℝ) : Prop :=
  ∃ ν : ℕ → ℝ, QuantumPRC.Negligible ν ∧ ∀ (lam : ℕ) (m : Fin (P.msgLen lam) → M),
    1 - ν lam ≤ unifProb (fun ω : (Fin (P.keyCoins lam) → Bool) × (Fin (P.encCoins lam) → Bool) =>
      ∀ x' ∈ editBall (List.ofFn (P.enc lam (P.keyGen lam ω.1) m ω.2)) ε,
        P.dec lam (P.keyGen lam ω.1) x' = some m)

/-- A pseudorandom code in the sense of Definition 2.1 (its robustness is stated separately):
polynomial-time algorithms, pseudorandomness, soundness. -/
def PRC.IsPRC [Nonempty M] (P : PRC M S) : Prop :=
  P.Efficient ∧ P.Pseudorandom ∧ P.Sound

/-- The relative rate `k(λ) log|M| / (n(λ) log|S|)`. -/
noncomputable def PRC.relRate (P : PRC M S) (lam : ℕ) : ℝ :=
  ((P.msgLen lam : ℝ) * Real.log (Fintype.card M)) /
    ((P.blockLen lam : ℝ) * Real.log (Fintype.card S))

end EditPRC.Boost


