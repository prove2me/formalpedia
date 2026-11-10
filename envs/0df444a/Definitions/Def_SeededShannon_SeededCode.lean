-- Prove2me | Definitions.Def_SeededShannon_SeededCode
-- name    : SeededShannon_SeededCode
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:45:09.321629+00:00
-- url     : https://prove2.me/theorems/7311c76e-312e-42aa-b57f-7131b097cf4d
-- title:
--   Seeded code $(\mathrm{Setup},\mathrm{Encode},\mathrm{Decode})$ and its properties (Definition 3.15)
-- statement:
--   A **seeded code** $\Pi=(\mathrm{Setup},\mathrm{Encode},\mathrm{Decode})$ consists of a randomized $\mathrm{Setup}(1^\lambda,1^k)\to crs$ producing a public seed, a deterministic encoder $\mathrm{Encode}_{crs}:\{0,1\}^k\to\{0,1\}^{N(\lambda,k)}$ and a deterministic decoder $\mathrm{Decode}_{crs}$ mapping $y\in\{0,1\}^{N(\lambda,k)}$ to a list $T\subseteq\{0,1\}^k$. For a set of supported lengths $(\lambda,k)$ the module defines:
--
--   1. **efficiency**: fixed machines compute $\mathrm{Setup}$, $\mathrm{Encode}$ and $\mathrm{Decode}$, and for every polynomially bounded message length $k(\lambda)$ they run in time polynomial in $\lambda$ at supported lengths;
--   2. **codeword length**: $|\mathrm{Encode}_{crs}(x)|=N(\lambda,k)$ for $x\in\{0,1\}^k$;
--   3. **list size $L$**: $|\mathrm{Decode}_{crs}(y)|\le L(\lambda,k)$ for every seed and every $y$, and every listed message has length $k$;
--   4. **$p$-soundness**: $\Delta(\mathrm{Encode}_{crs}(x),y)\le p\cdot N$ for every seed, every $y$ and every $x\in\mathrm{Decode}_{crs}(y)$;
--   5. **selective computational $p$-correction**: for every adversary $A=(A_1,A_2)$ there is a negligible $\nu$ with $\Pr[\mathsf{ExpCorrect}^{(p)}(A,\lambda)=1]\le\nu(\lambda)$, where $A_1$ fixes $x^*$ of a supported length $k$, the challenger samples $crs\leftarrow\mathrm{Setup}(1^\lambda,1^k)$, $A_2(st,crs)$ outputs $y\in\{0,1\}^N$, and the experiment outputs $1$ iff
--   $$\Delta(\mathrm{Encode}_{crs}(x^*),y)\le p\cdot N\quad\text{and}\quad x^*\notin\mathrm{Decode}_{crs}(y).$$
--
--   The module also fixes the Hamming distance of bit strings and two-argument polynomial boundedness. These are the conclusion predicates of the goal theorem.
--
--   **Formalization Note** Seeds, messages and words are bit strings. Adversaries are nonuniform polynomial-size circuit families and deterministic, so $A_1$ is a fixed message sequence of polynomial length and its state is hard-wired into $A_2$ (the published `CircFamily`), which receives $(1^\lambda,crs)$. An unsupported length or a $y$ of the wrong length makes the experiment output $0$ (p.22). The decoder's set is a list, so a bound on its length bounds $|T|$.
-- source:
--   Dujmovic, Lu, Silbak, Wichs, Shannon Rate Seeded Codes from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 52f4b606…a769709), Definition 3.15, p.22 (PDF p.25), with the malformed-input convention directly above it

import Mathlib
import Definitions.Def_NoisyOWMPC_KeyedFamily
import Definitions.Def_NoisyOWMPC_wprob

set_option autoImplicit false

namespace SeededShannon

open LaconicBarrier NoisyOWMPC

/-- A **seeded code** `Π = (Setup, Encode, Decode)` (Dujmovic, Lu, Silbak, Wichs, STOC 2027
submission (manuscript sha256 52f4b606…a769709), Definition 3.15, p.22):
`Setup(1^λ, 1^k) → crs`; a deterministic `Encode_crs : {0,1}^k → {0,1}^{N(λ,k)}`; a deterministic
`Decode_crs : {0,1}^{N(λ,k)} →` list of messages in `{0,1}^k`.

**Formalization Note** `setup λ k r` is the seed under setup coins `r ∈ {0,1}^{setupCoins λ k}`.
Seeds, messages, codewords and received words are bit strings (`List Bool`); the lengths the paper
fixes are separate predicates (`EncodeLength`, `ListBound`). The decoder's output set `T` is a
list, so a bound on the list length bounds `|T|`. -/
structure SeededCode where
  /-- the codeword length `N(λ, k)` -/
  N : ℕ → ℕ → ℕ
  /-- the number of coins of `Setup(1^λ, 1^k)` -/
  setupCoins : ℕ → ℕ → ℕ
  /-- `Setup(1^λ, 1^k; r) = crs` -/
  setup : (lam k : ℕ) → (Fin (setupCoins lam k) → Bool) → List Bool
  /-- `Encode(crs, x)` -/
  encode : List Bool → List Bool → List Bool
  /-- `Decode(crs, y)` -/
  decode : List Bool → List Bool → List (List Bool)

/-- Absolute Hamming distance `Δ(a, b)` of two bit strings: the number of positions, among the
first `min(|a|, |b|)`, where they differ (§3, p.16: "Let `Δ` denote absolute Hamming distance"). It
is only applied to strings of equal length. -/
def ldist (a b : List Bool) : ℕ := (List.zipWith (fun u v => u != v) a b).count true

/-- A two-argument function is **polynomially bounded**: `L(λ, k) ≤ (λ + k + 2)^c` for one `c`. -/
def PolyBounded₂ (L : ℕ → ℕ → ℕ) : Prop := ∃ c : ℕ, ∀ lam k, L lam k ≤ (lam + k + 2) ^ c

/-- The algorithms **run in time `poly(λ, k)`** at the supported lengths `supp` (Definition 3.15,
p.22: "three efficient algorithms"; Theorem 6.13, p.47: "has algorithms running in time
`poly(λ, k)`" for every polynomially bounded message length `k`): there are three fixed machines
computing `Setup` from `(1^λ, 1^k, r)`, `Encode` from `(crs, x)` and `Decode` from `(crs, y)` (honest
seeds `crs`, messages of length `k`, words of length `N(λ, k)`) such that for every polynomially
bounded length function `k(λ)` there is one exponent `c` with: `Setup` uses at most `(λ + 2)^c`
coins, and each machine halts within `(λ + 2)^c` steps, at every supported `(λ, k(λ))`.

**Formalization Note** The machines are uniform, in the published model of
`LaconicBarrier.RunsWithin`, and are fixed before the length function; only the time exponent
depends on the length function ("for every polynomially bounded message length `k` … time
`poly(λ, k)`"; for polynomially bounded `k`, `poly(λ, k)` is `poly(λ)`). Every supported pair
`(λ, k)` lies on some polynomially bounded length function, so the machines compute the algorithms
at every supported length. The output list of `Decode` is written in the tuple encoding. -/
def SeededCode.IsEfficient (C : SeededCode) (supp : ℕ → ℕ → Prop) : Prop :=
  ∃ Ms Me Md : KarpLiptonOM.OracleTM, ∀ kf : ℕ → ℕ, PolyBounded kf → ∃ c : ℕ,
    ∀ lam, supp lam (kf lam) →
      C.setupCoins lam (kf lam) ≤ (lam + 2) ^ c ∧
      ∀ r : Fin (C.setupCoins lam (kf lam)) → Bool,
        RunsWithin Ms [unary lam, unary (kf lam), bits r] (C.setup lam (kf lam) r)
            ((lam + 2) ^ c) ∧
        (∀ x : Fin (kf lam) → Bool,
          RunsWithin Me [C.setup lam (kf lam) r, bits x]
            (C.encode (C.setup lam (kf lam) r) (bits x)) ((lam + 2) ^ c)) ∧
        (∀ y : Fin (C.N lam (kf lam)) → Bool,
          RunsWithin Md [C.setup lam (kf lam) r, bits y]
            (QAdvFew.PoQOracle.tup (C.decode (C.setup lam (kf lam) r) (bits y))) ((lam + 2) ^ c))

/-- **Codeword length** (Definition 3.15, p.22: `Encode_crs(x) ∈ {0,1}^{N(λ,k)}`): on every seed
`Setup` outputs at a supported `(λ, k)`, every message of length `k` encodes to a word of length
exactly `N(λ, k)`. -/
def SeededCode.EncodeLength (C : SeededCode) (supp : ℕ → ℕ → Prop) : Prop :=
  ∀ (lam k : ℕ), supp lam k → ∀ (r : Fin (C.setupCoins lam k) → Bool) (x : List Bool),
    x.length = k → (C.encode (C.setup lam k r) x).length = C.N lam k

/-- **List size `L`** (Definition 3.15, p.22: "For every crs and y, the list has size
`|Decode_crs(y)| ≤ L`"; `Decode` outputs `T ⊆ {0,1}^k`): on every seed at a supported `(λ, k)` and
every `y ∈ {0,1}^{N(λ,k)}`, the decoder lists at most `L(λ, k)` messages, each of length `k`. -/
def SeededCode.ListBound (C : SeededCode) (supp : ℕ → ℕ → Prop) (L : ℕ → ℕ → ℕ) : Prop :=
  ∀ (lam k : ℕ), supp lam k → ∀ (r : Fin (C.setupCoins lam k) → Bool) (y : List Bool),
    y.length = C.N lam k →
      (C.decode (C.setup lam k r) y).length ≤ L lam k ∧
      ∀ x ∈ C.decode (C.setup lam k r) y, x.length = k

/-- **`p`-soundness** (Definition 3.15, p.22: "For every crs, every y, and every
`x ∈ Decode_crs(y)`, we have `Δ(Encode_crs(x), y) ≤ p · N`"), on every seed at a supported
`(λ, k)` and every `y ∈ {0,1}^{N(λ,k)}`. -/
def SeededCode.Sound (C : SeededCode) (supp : ℕ → ℕ → Prop) (p : ℝ) : Prop :=
  ∀ (lam k : ℕ), supp lam k → ∀ (r : Fin (C.setupCoins lam k) → Bool) (y : List Bool),
    y.length = C.N lam k → ∀ x ∈ C.decode (C.setup lam k r) y,
      (ldist (C.encode (C.setup lam k r) x) y : ℝ) ≤ p * C.N lam k

/-- **Selective computational `p`-correction** (Definition 3.15, p.22, experiment
`ExpCorrect^{(p)}(A, λ)`): for every adversary `A = (A₁, A₂)` there is a negligible `ν` such that for
every `λ`, `Pr[ExpCorrect^{(p)}(A, λ) = 1] ≤ ν(λ)`, where `A₁(1^λ)` sends `x* ∈ {0,1}^k` of a
supported length `k`, the challenger samples `crs ← Setup(1^λ, 1^k)`, `A₂(st, crs)` sends
`y ∈ {0,1}^N`, and the experiment outputs `1` iff `Δ(Encode_crs(x*), y) ≤ p · N` and
`x* ∉ Decode_crs(y)`.

**Formalization Note** Adversaries are nonuniform polynomial-size circuit families and
deterministic (a randomized one is matched by its best coins). Then `A₁(1^λ)` is a fixed message
`x*_λ` (a sequence `xs` of polynomially bounded length) and its state is hard-wired into `A₂`, a
published `CircFamily` run on `(1^λ, crs)`. An unsupported length `|x*_λ|` or an output `y` of the
wrong length makes the experiment output `0` (p.22, "Malformed inputs"). `ν` is chosen after the
adversary and before `λ`. -/
def SeededCode.SelectivelyCorrect (C : SeededCode) (supp : ℕ → ℕ → Prop) (p : ℝ) : Prop :=
  ∀ xs : ℕ → List Bool, PolyBounded (fun lam => (xs lam).length) →
  ∀ A : CircFamily, A.IsPoly → ∃ ν : ℕ → ℝ, Negligible ν ∧ ∀ lam, supp lam (xs lam).length →
    wprob (unifW (Fin (C.setupCoins lam (xs lam).length) → Bool)) (fun r =>
      let crs := C.setup lam (xs lam).length r
      let y := (A.circ lam).eval (padIn (A.inLen lam) (QAdvFew.PoQOracle.tup [unary lam, crs]))
      y.length = C.N lam (xs lam).length ∧
        (ldist (C.encode crs (xs lam)) y : ℝ) ≤ p * C.N lam (xs lam).length ∧
        xs lam ∉ C.decode crs y) ≤ ν lam

end SeededShannon


