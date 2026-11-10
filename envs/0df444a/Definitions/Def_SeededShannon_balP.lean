-- Prove2me | Definitions.Def_SeededShannon_balP
-- name    : SeededShannon_balP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:45:53.579792+00:00
-- url     : https://prove2.me/theorems/3ff1ba1b-7261-4b22-ae57-adccc26bbaa0
-- title:
--   Balanced errors: $\mathrm{Ball}_p(c)$, $\mathrm{Bal}_P(c;\tau,\gamma)$, balanced-error codes, partition predicates (Definition 3.13)
-- statement:
--   Let $b\mid n$ and let $P$ be a partition of $[n]$ into sets of size $b$; $P_b$ is the partition into consecutive blocks of length $b$. For a center $c\in\{0,1\}^n$,
--   $$\mathrm{Ball}_p(c)=\{y:\delta(y,c)\le p\},\qquad \mathrm{Bal}_P(c;\tau,\gamma)=\{y:|\{S\in P:\delta(y_S,c_S)>\tau\}|\le\gamma\cdot n/b\}.$$
--   A binary code $(\mathrm{Encode},\mathrm{ListDec})$ is **$L$-list decodable against $(b,\tau,\gamma)$-balanced errors** if for every $y$ the list $T=\mathrm{ListDec}(y)$ has $|T|\le L$ and, for every message $m$, $m\in T\iff y\in\mathrm{Bal}_{P_b}(\mathrm{Encode}(m);\tau,\gamma)$.
--
--   The module also defines the two **partition agreement predicates**: the expanded form of Theorem 5.6, $f_P(y)=1\iff \mathrm{wt}(y)\le p\cdot n$ and $|\{S\in P:\mathrm{wt}(y_S)>\tau b\}|>\gamma n/b$, and the form of Theorem 5.3, $f_P(x)=1\iff x\in\mathrm{Ball}_p(0^n)\setminus\mathrm{Bal}_P(0^n;\tau,\gamma)$, with their families over partitions $P$ into $b$-blocks, and a bit-string code of a partition.
--
--   These are the error classes of the balanced-error code (Theorem 3.14) and of the partition evasive obfuscator (Theorems 5.3, 5.6).
--
--   **Formalization Note** A partition is a block labelling $P:[n]\to\{0,\dots,n/b-1\}$ with every label used $b$ times; consecutive blocks label position $i$ (from $0$) by $\lfloor i/b\rfloor$. $\delta(y_S,c_S)>\tau$ on a block of size $b$ is $\Delta(y_S,c_S)>\tau b$, and $\delta(y,c)\le p$ is $\Delta(y,c)\le pn$.
-- source:
--   Dujmovic, Lu, Silbak, Wichs, Shannon Rate Seeded Codes from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 52f4b606…a769709), Definition 3.13, p.21 (PDF p.24); Theorems 5.3, 5.6, pp.32–33 (PDF pp.35–36)

import Mathlib
import Definitions.Def_SeededShannon_setFamily
import Definitions.Def_QAdvFew_PoQOracle_tup

set_option autoImplicit false

namespace SeededShannon

/-- A **partition of `[n]` into blocks of size `b`** (Dujmovic, Lu, Silbak, Wichs, STOC 2027
submission (manuscript sha256 52f4b606…a769709), Definition 3.13, p.21: "let `P` be a partition of
`[n]` into sets of size `b`"), given by a block label `P(i) < n/b` for every position, every label
used by exactly `b` positions. -/
def IsBlockPartition (b n : ℕ) (P : Fin n → ℕ) : Prop :=
  (∀ i, P i < n / b) ∧ ∀ j < n / b, (Finset.univ.filter (fun i => P i = j)).card = b

/-- The partition `P_b` of `[n]` into **consecutive blocks** of length `b` (Definition 3.13, p.21):
position `i` (from `0`) lies in block `⌊i/b⌋`. -/
def consecBlocks (b n : ℕ) : Fin n → ℕ := fun i => i.val / b

/-- The Hamming distance `Δ(y_S, c_S)` on the block with label `j`. -/
def blockDist {n : ℕ} (P : Fin n → ℕ) (j : ℕ) (y c : Fin n → Bool) : ℕ :=
  (Finset.univ.filter (fun i => P i = j ∧ y i ≠ c i)).card

/-- The **Hamming ball** `Ball_p(c) = {y : δ(y, c) ≤ p}` (Definition 3.13, p.21), as the predicate
`y ∈ Ball_p(c)`.

**Formalization Note** `δ(y, c) ≤ p` is written `Δ(y, c) ≤ p · n`. -/
def ballP (p : ℝ) {n : ℕ} (c y : Fin n → Bool) : Prop := (hammingDist y c : ℝ) ≤ p * n

/-- The **balanced-error ball** `Bal_P(c; τ, γ) = {y : |{S ∈ P : δ(y_S, c_S) > τ}| ≤ γ · n/b}`
(Definition 3.13, p.21), as the predicate `y ∈ Bal_P(c; τ, γ)`, for a partition `P` of `[n]` into
blocks of size `b` given by block labels `0, …, n/b − 1`.

**Formalization Note** `δ(y_S, c_S) > τ` on a block of size `b` is written `Δ(y_S, c_S) > τ · b`. -/
def balP (b : ℕ) (τ γ : ℝ) {n : ℕ} (P : Fin n → ℕ) (c y : Fin n → Bool) : Prop :=
  ((((Finset.range (n / b)).filter (fun j => τ * b < blockDist P j y c)).card : ℕ) : ℝ) ≤
    γ * n / b

/-- A binary code `(Encode, ListDec)` with `Encode : {0,1}^k → {0,1}^n` is **`L`-list decodable
against `(b, τ, γ)`-balanced errors** (Definition 3.13, p.21): for every `y ∈ {0,1}^n` the list
`T = ListDec(y)` has `|T| ≤ L` and, for every message `m`, `m ∈ T ⟺ y ∈ Bal_{P_b}(Encode(m); τ, γ)`. -/
def BalancedListDecodable (b : ℕ) (τ γ : ℝ) {k n : ℕ} (enc : (Fin k → Bool) → Fin n → Bool)
    (dec : (Fin n → Bool) → List (Fin k → Bool)) (L : ℕ) : Prop :=
  ∀ y : Fin n → Bool, (dec y).length ≤ L ∧
    ∀ m : Fin k → Bool, m ∈ dec y ↔ balP b τ γ (consecBlocks b n) (enc m) y

/-- The **sparse partition agreement predicate** in the expanded form of Theorem 5.6 (p.33):
`f_P(y) = 1 ⟺ wt(y) ≤ p · n` and `|{S ∈ P : wt(y_S) > τ · b}| > γ · n/b`. -/
def partAgree (p τ γ : ℝ) (b : ℕ) {n : ℕ} (P : Fin n → ℕ) (y : Fin n → Bool) : Prop :=
  (wt y : ℝ) ≤ p * n ∧
    γ * n / b < ((((Finset.range (n / b)).filter (fun j =>
      τ * b < (Finset.univ.filter (fun i => P i = j ∧ y i = true)).card)).card : ℕ) : ℝ)

/-- The family of Theorem 5.6 (p.33): `f_P` for partitions `P` of `[n]` into blocks of size `b`,
with `f_P` the expanded predicate `partAgree`. -/
def partFamily56 (p τ γ : ℝ) (b : ℕ) (_lam n : ℕ) : Set ((Fin n → Bool) → Bool) :=
  {f | ∃ P : Fin n → ℕ, IsBlockPartition b n P ∧ ∀ y, f y = true ↔ partAgree p τ γ b P y}

/-- The family of Theorem 5.3 (p.32): `f_P` for partitions `P` of `[n]` into `b`-element blocks,
`f_P(x) = 1 ⟺ x ∈ Ball_p(0^n) \ Bal_P(0^n; τ, γ)`. -/
def partFamily53 (p τ γ : ℝ) (b : ℕ) (_lam n : ℕ) : Set ((Fin n → Bool) → Bool) :=
  {f | ∃ P : Fin n → ℕ, IsBlockPartition b n P ∧
    ∀ x, f x = true ↔ (ballP p (fun _ => false) x ∧ ¬ balP b τ γ P (fun _ => false) x)}

/-- The bit-string code of a block labelling `P : [n] → ℕ`: the labels in binary with
`⌈log₂(n + 1)⌉` digits each, in the tuple encoding. -/
def partCode {n : ℕ} (P : Fin n → ℕ) : List Bool :=
  QAdvFew.PoQOracle.tup (List.ofFn fun i => KarpLiptonOM.binW (Nat.size n) (P i))

end SeededShannon


