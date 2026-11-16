-- Prove2me | Definitions.Def_FourMsgQMA_Supplement_HashFamily
-- name    : FourMsgQMA_Supplement_HashFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:16:55.805709+00:00
-- url     : https://prove2.me/theorems/7e782118-7960-4395-a186-003c803904f8
-- title:
--   Keyed hash families: efficiency, collision resistance (Def 3.11) and collapsing (Def 3.12)
-- statement:
--   A **keyed hash family** $H=(\mathrm{Gen},\mathrm{Hash})$ for a prescribed input length $\ell$ consists of a randomized key generator $hk\leftarrow\mathrm{Gen}(1^\lambda,\ell)$ (with explicit coins) and a deterministic, total map $\alpha:=\mathrm{Hash}(hk,x)$ sending $x\in\{0,1\}^\ell$ to a digest of prescribed length $d_H(\lambda,\ell)$.
--
--   1. **Efficiency** (§3.7): key and digest lengths and key-generation time are $\mathrm{poly}(\lambda,\log(\ell+1))$, and evaluation is polynomial time.
--   2. **Collision resistance** (Definition 3.11): for every polynomial $\ell(\lambda)$ and every QPT adversary that receives $hk$ and outputs $(x_0,x_1)$, the probability that both messages have length $\ell$, $x_0\ne x_1$ and $\mathrm{Hash}(hk,x_0)=\mathrm{Hash}(hk,x_1)$ is negligible.
--   3. **Collapsing** (Definition 3.12): the first stage receives $hk$ and outputs a classical $\alpha$, leaving a state on its message register $X$ and its other registers $R$. The challenger samples $b\leftarrow\{0,1\}$, applies the coherent test $\mathrm{Check}_{hk,\alpha}$ of $\mathrm{Hash}(hk,x)=\alpha$ on $X$ with outcome $v$, and if $b=1$ measures $X$ in the computational basis (outcome discarded). If $v=1$ the second stage guesses $\hat b$; if $v=0$ the guess is an independent uniform bit. Collapsing requires
--   $$
--   \Pr[\hat b=b]\le \tfrac12+\nu(\lambda)
--   $$
--   for a negligible $\nu$, for every polynomial $\ell$ and every QPT two-stage adversary.
--
--   These are the hash properties used by the Merkle commitments of §3.8, by Kilian's argument (Theorem 3.26) and by the six-message construction (Theorem 7.5).
--
--   **Formalization Note** Adversaries are the published `IsQPT` strategies; the two stages are rounds 0 and 1 of one strategy with one quantum advice state, and the message register is any list of $\ell(\lambda)$ distinct core wires (security is required for every choice). The coherent test is the two-outcome projective measurement it implements.
-- source:
--   Goyal, Koppula, Four-Message Arguments for NP ∘ batchQMA and Six-Message Arguments for QMA from LWE, STOC 2027 submission (sha256 6c523d45…), §3.7 and Definitions 3.11–3.12, pp.15–16 (PDF 17–18)

import Mathlib
import Definitions.Def_FourMsgQMA_IndexBARG

namespace FourMsgQMA

/-!
Goyal, Koppula, *Four-Message Arguments for NP ∘ batchQMA and Six-Message Arguments for QMA from
LWE*, STOC 2027 submission (sha256 6c523d45…), §3.7 (p.15, PDF 17) and Definitions 3.11–3.12
(pp.15–16, PDF 17–18): keyed hash families, their efficiency, collision resistance and collapsing.

Pinned-down version (operator request): "PPT"/"time" are polynomial-time computability
(`QAlgorithms.Complexity.PolyTimeComputable`) on packed inputs together with polynomial length
bounds; adversaries are the published `TightPQRepetition.Main.IsQPT` strategies.
-/

namespace Supplement

open QAlgorithms QAlgorithms.Complexity TightPQRepetition.Main

/-- A keyed hash family `H = (Gen, Hash)` (§3.7, p.15). -/
structure HashFamily where
  /-- The number of coins of `Gen(1^λ, ℓ)` at `(λ, ℓ)`. -/
  genCoins : ℕ → ℕ → ℕ
  /-- `hk ← Gen(1^λ, ℓ)`, with explicit coins. -/
  gen : ℕ → ℕ → Bits → Bits
  /-- The prescribed digest length `d_H(λ, ℓ)`. -/
  digestLen : ℕ → ℕ → ℕ
  /-- `α := Hash(hk, x)`, deterministic and total. -/
  hash : Bits → Bits → Bits

/-- The binary representation of `ℓ` in `⌈log₂(ℓ + 1)⌉` bits, least significant bit first. -/
def binNat (l : ℕ) : Bits := idxBits (clog2 (l + 1)) l

/-- The efficiency requirements of §3.7 (p.15): "key and digest lengths `poly(λ, log(ℓ + 1))`,
key-generation time `poly(λ, log(ℓ + 1))`, and evaluation time `poly(λ, ℓ)`", and digests of the
prescribed length `d_H(λ, ℓ)` on inputs `x ∈ {0,1}^ℓ`. Key generation is polynomial time in
`(1^λ, ℓ in binary, coins)`, evaluation in `(hk, x)`. -/
def HashFamily.Efficient (H : HashFamily) : Prop :=
  (∃ p : MvPolynomial (Fin 4) ℕ, ∀ lam l : ℕ,
    H.genCoins lam l ≤ eval4 p lam (clog2 (l + 1)) 0 0 ∧
    H.digestLen lam l ≤ eval4 p lam (clog2 (l + 1)) 0 0 ∧
    ∀ r : Bits, r.length = H.genCoins lam l → (H.gen lam l r).length ≤ eval4 p lam (clog2 (l + 1)) 0 0) ∧
  (∀ lam l (r x : Bits), r.length = H.genCoins lam l → x.length = l →
    (H.hash (H.gen lam l r) x).length = H.digestLen lam l) ∧
  (∃ g : Str → Str, PolyTimeComputable g ∧ ∀ lam l,
    g (pack [unary lam, binNat l]) = pack [unary (H.genCoins lam l), unary (H.digestLen lam l)]) ∧
  (∃ g : Str → Str, PolyTimeComputable g ∧ ∀ lam l r,
    g (pack [unary lam, binNat l, r]) = H.gen lam l r) ∧
  (∃ g : Str → Str, PolyTimeComputable g ∧ ∀ hk x, g (pack [hk, x]) = H.hash hk x)

/-- The collision-resistance experiment of Definition 3.11 (p.15) at input length `ℓ(λ)`, as a
published `TightPQRepetition.Main.Verifier` (semantic carrier): the adversary receives
`hk ← Gen(1^λ, ℓ)` and answers `pack [x₀, x₁]`; it wins when both messages have the admissible
length `ℓ`, `x₀ ≠ x₁` and `Hash(hk, x₀) = Hash(hk, x₁)`. -/
def HashFamily.crVerifier (H : HashFamily) (l : ℕ → ℕ) : Verifier where
  rounds := fun _ => 1
  coins := fun lam => H.genCoins lam (l lam)
  qLen := fun _ _ => 0
  query := fun lam r _ _ => H.gen lam (l lam) r
  verdict := fun lam r τ =>
    let hk := H.gen lam (l lam) r
    let ans := unpack (τ.getD 0 ([], [])).2
    let x0 := ans.getD 0 []
    let x1 := ans.getD 1 []
    decide (x0.length = l lam ∧ x1.length = l lam ∧ x0 ≠ x1 ∧ H.hash hk x0 = H.hash hk x1)

/-- Collision resistance, Definition 3.11 (p.15): for every polynomial `ℓ` and every QPT
adversary there is a negligible `ν` bounding its winning probability. -/
def HashFamily.CollisionResistant (H : HashFamily) : Prop :=
  ∀ l : ℕ → ℕ, PolyBound l → ∀ Adv : ℕ → Strategy, IsQPT Adv →
    ∃ ν : ℕ → ℝ, Negligible ν ∧ ∀ lam, (Adv lam).acceptProb (H.crVerifier l) lam ≤ ν lam

/-- The operator of round `j` of a strategy with incoming core string `x` and measured outcome `c`:
apply the round's unitary and project the measured wires onto `c`. -/
noncomputable def roundOp (S : Strategy) (j : ℕ) (x c : Bits) : Matrix (Qubits S.n) (Qubits S.n) ℂ :=
  outcomeProj (S.stepAt j).outW c * (S.stepAt j).op x

/-- The projector of the coherent test `Check_{hk,α}` of Definition 3.12 with outcome `v`, on the
message register `X` (the wires `Xw`): `v = true` on the basis states whose `X` content `x`
satisfies `Hash(hk, x) = α`, `v = false` on the others. Computing the bit into a fresh register,
measuring it and uncomputing the workspace is this two-outcome projective measurement. -/
noncomputable def checkProj {n : ℕ} (H : HashFamily) (hk α : Bits) (Xw : List (Fin n)) (v : Bool) :
    Matrix (Qubits n) (Qubits n) ℂ :=
  Matrix.diagonal fun y => if decide (H.hash hk (Xw.map y) = α) = v then 1 else 0

/-- The probability `Pr[b̂ = b]` in the collapsing experiment of Definition 3.12 (pp.15–16) at input
length `ℓ`, for the strategy `S` whose message register `X` is the list of wires `Xw`:
`hk ← Gen(1^λ, ℓ)` and `b ← {0,1}`; the first stage receives `hk` (round 0) and outputs the
classical `α` (its round-0 answer), leaving the state `ρ_XR` on its core; the challenger applies
`Check_{hk,α}` with outcome `v`, then, if `b = 1`, measures `X` in the computational basis and
discards the outcome (`M⁰_X` is the identity); if `v = 1` the second stage (round 1, empty incoming
message) outputs `b̂` as the first bit of its answer, and if `v = 0` the guess is an independent
uniform bit. The register `R` is every other wire of the core. -/
noncomputable def HashFamily.collapseWin (H : HashFamily) (l lam : ℕ) (S : Strategy)
    (Xw : List (Fin S.n)) : ℝ :=
  avgCoins (H.genCoins lam l) fun r => avgCoins S.tape fun u =>
    let hk := H.gen lam l r
    let x0 := S.toCore 0 (pack (controllerView u [] ++ [hk]))
    ∑ c0 : Qubits (S.outLen 0),
      let h1 : List (Bits × Bits) := [(hk, toBits c0)]
      let α := S.toVerifier 0 (pack (controllerView u h1))
      let ψ := act (roundOp S 0 x0 (toBits c0)) S.init
      let x1 := S.toCore 1 (pack (controllerView u h1 ++ [[]]))
      let cont : EuclideanSpace ℂ (Qubits S.n) → Bool → ℝ := fun φ b =>
        ∑ c1 : Qubits (S.outLen 1),
          if (S.toVerifier 1 (pack (controllerView u (h1 ++ [([], toBits c1)])))).getD 0 false = b
          then ‖act (roundOp S 1 x1 (toBits c1)) φ‖ ^ 2 else 0
      let ψ1 := act (checkProj H hk α Xw true) ψ
      (1 / 2) * ‖act (checkProj H hk α Xw false) ψ‖ ^ 2 +
        (1 / 2) * (cont ψ1 false +
          ∑ x : Qubits l, cont (act (outcomeProj Xw (toBits x)) ψ1) true)

/-- Collapsing, Definition 3.12 (pp.15–16): for every polynomial `ℓ`, every QPT two-stage adversary
(one `IsQPT` strategy whose rounds 0 and 1 are `A₁`, `A₂`, with one quantum advice state and the
residual state carried forward) and every choice of its message register (`ℓ(λ)` distinct core
wires), `Pr[b̂ = b] ≤ 1/2 + ν(λ)` for a negligible `ν`. -/
def HashFamily.Collapsing (H : HashFamily) : Prop :=
  ∀ l : ℕ → ℕ, PolyBound l → ∀ Adv : ℕ → Strategy, IsQPT Adv →
    ∀ Xw : (lam : ℕ) → List (Fin (Adv lam).n), (∀ lam, (Xw lam).length = l lam ∧ (Xw lam).Nodup) →
    ∃ ν : ℕ → ℝ, Negligible ν ∧ ∀ lam, H.collapseWin (l lam) lam (Adv lam) (Xw lam) ≤ 1 / 2 + ν lam

end Supplement

end FourMsgQMA


