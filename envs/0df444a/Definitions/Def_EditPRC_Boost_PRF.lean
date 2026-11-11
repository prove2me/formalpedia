-- Prove2me | Definitions.Def_EditPRC_Boost_PRF
-- name    : EditPRC_Boost_PRF
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T05:08:39.20647+00:00
-- url     : https://prove2.me/theorems/02a924a5-c151-44a9-a0f8-ace992741d3b
-- title:
--   Pseudorandom functions with sub-exponential security and running time $O(n^{1+\theta})$ (§2.6)
-- statement:
--   A **keyed function family** $\mathrm{PRF}:\{0,1\}^{\kappa(n)}\times\{0,1\}^n\to\{0,1\}^{m(n)}$ is, for every input length $n$, a function of a key $k$ and an input $x$. It is **well-formed** if $\kappa$ and $m$ are polynomially bounded and $m(n)\ge 1$.
--
--   For an oracle distinguisher $D$ let $\Pr_k[D^{\mathrm{PRF}_k}(1^n)=1]$ be taken over a uniform key and the coins of $D$, and $\Pr_R[D^{R}(1^n)=1]$ over a uniformly random function $R:\{0,1\}^n\to\{0,1\}^{m(n)}$ and the coins of $D$; queries are read as $n$-bit inputs. The family is **sub-exponentially secure** if for some constant $c>0$, every $D$ running in time $2^{Cn^c}$ (for some $C$) has advantage
--   $$\Bigl|\Pr_k[D^{\mathrm{PRF}_k}(1^n)=1]-\Pr_R[D^{R}(1^n)=1]\Bigr|\ \le\ 2^{-Kn^c}$$
--   for every $K$ and all large $n$, i.e. advantage $2^{-\omega(n^c)}$ against time $2^{O(n^c)}$.
--
--   It **runs in time $O(n^{1+\theta})$** if one Turing machine computes $\mathrm{PRF}(k,x)$ from the encoding of $(1^n,k,x)$ within $C n^{1+\theta}+C$ steps, for a constant $C$.
--
--   These are the PRFs that Theorem 2.27 obtains from PRCs and that the proof of Theorem 3.12 uses as one-time pads and to seed synchronization strings.
--
--   **Formalization Note.** The machine model and the running-time accounting of distinguishers are those of `EditPRC.Boost.Machine`. The condition $m(n)\ge1$ only excludes the degenerate empty-output family.
-- source:
--   Gozon, Edit-Robust Pseudorandom Codes, Watermarks, and Steganography, STOC 2027 submission (manuscript sha256 73170029…6b60), p. 8 (sub-exponential security s(λ) = n^c), p. 18, §2.6 (PRF : {0,1}^{κ(n)} × {0,1}^n → {0,1}^{m(n)}, m = poly(n); running time O(n^{1+θ}))

import Mathlib
import Definitions.Def_EditPRC_Boost_Machine

set_option autoImplicit false

namespace EditPRC.Boost

/-!
# Pseudorandom functions with sub-exponential security and a running-time bound

Gozon, *Edit-Robust Pseudorandom Codes, Watermarks, and Steganography*, STOC 2027 submission
(manuscript sha256 73170029…6b60), p. 8 (notation: security `s(λ)`, sub-exponential security
`s = n^c`), p. 18, §2.6 (`PRF : {0,1}^{κ(n)} × {0,1}^n → {0,1}^{m(n)}` with `m = poly(n)`;
running time `O(n^{1+θ})`).

* A keyed family `PRF_k : {0,1}^n → {0,1}^{m(n)}` with uniformly random key `k ∈ {0,1}^{κ(n)}`.
* Security is oracle indistinguishability from a uniformly random function
  `{0,1}^n → {0,1}^{m(n)}`; the oracle reads its query as an `n`-bit input (bit `i` of the query,
  missing bits `0`), so the caller may query any input.
-/

open Filter

/-- A keyed function family with input length `n`, key length `κ(n)` and output length
`m(n)`. -/
structure PRF where
  /-- Key length `κ(n)`. -/
  keyLen : ℕ → ℕ
  /-- Output length `m(n)`. -/
  outLen : ℕ → ℕ
  /-- `PRF(k, x)`. -/
  eval : (n : ℕ) → (Fin (keyLen n) → Bool) → (Fin n → Bool) → Fin (outLen n) → Bool

/-- Read a bit string as an `n`-bit input: bit `i` of the query, `false` where it is missing. -/
def bitsParse (n : ℕ) (q : List Bool) : Fin n → Bool := fun i => q.getD i.val false

/-- `Pr_k[Dist^{PRF_k}(1^n) = 1]`, over the uniform key and the coins of `Dist`. -/
noncomputable def PRF.realAccept (F : PRF) (D : OracleAlg) (n : ℕ) : ℝ :=
  unifProb (fun ω : (Fin (F.keyLen n) → Bool) × (Fin (D.coins n) → Bool) =>
    D.output n ω.2 (fun _ q => List.ofFn (F.eval n ω.1 (bitsParse n q))) = true)

/-- `Pr_R[Dist^R(1^n) = 1]` for a uniformly random function `R : {0,1}^n → {0,1}^{m(n)}`. -/
noncomputable def PRF.idealAccept (F : PRF) (D : OracleAlg) (n : ℕ) : ℝ :=
  unifProb (fun ω : (Fin (D.coins n) → Bool) × ((Fin n → Bool) → Fin (F.outLen n) → Bool) =>
    D.output n ω.1 (fun _ q => List.ofFn (ω.2 (bitsParse n q))) = true)

/-- The distinguishing advantage of `D` at input length `n`. -/
noncomputable def PRF.advantage (F : PRF) (D : OracleAlg) (n : ℕ) : ℝ :=
  |F.realAccept D n - F.idealAccept D n|

/-- Well-formedness: polynomial key and output lengths, and at least one output bit. -/
def PRF.WellFormed (F : PRF) : Prop :=
  PolyBounded F.keyLen ∧ PolyBounded F.outLen ∧ ∀ n, 1 ≤ F.outLen n

/-- **Sub-exponential security**: for some constant `c > 0`, every distinguisher running in time
`2^{O(n^c)}` has advantage `2^{-ω(n^c)}`. -/
def PRF.SubexpSecure (F : PRF) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (D : OracleAlg) (C : ℝ),
    D.RunsWithin F.outLen (fun n => (2 : ℝ) ^ (C * (n : ℝ) ^ c)) →
    ∀ K : ℝ, ∀ᶠ n in atTop, F.advantage D n ≤ (2 : ℝ) ^ (-(K * (n : ℝ) ^ c))

/-- **Running time `O(n^{1+θ})`**: one machine computes `PRF(k, x)` from the encoding of
`(1^n, k, x)` within `C · n^{1+θ} + C` steps, for a constant `C`. -/
def PRF.RunsInTime (F : PRF) (θ : ℝ) : Prop :=
  ∃ G : List Bool → List Bool,
    (∀ (n : ℕ) (k : Fin (F.keyLen n) → Bool) (x : Fin n → Bool),
      G (tup [unary n, List.ofFn k, List.ofFn x]) = List.ofFn (F.eval n k x)) ∧
    ∃ (Mach : Turing.TM2ComputableInTime (id : List Bool → List Bool)
        (id : List Bool → List Bool) G) (C : ℝ),
      ∀ (n : ℕ) (k : Fin (F.keyLen n) → Bool) (x : Fin n → Bool),
        (Mach.time (tup [unary n, List.ofFn k, List.ofFn x]).length : ℝ) ≤
          C * (n : ℝ) ^ (1 + θ) + C

end EditPRC.Boost


