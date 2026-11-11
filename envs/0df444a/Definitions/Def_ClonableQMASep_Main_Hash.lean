-- Prove2me | Definitions.Def_ClonableQMASep_Main_Hash
-- name    : ClonableQMASep_Main_Hash
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:23:44.983597+00:00
-- url     : https://prove2.me/theorems/f5b17638-3770-4e23-8909-1f785d069996
-- title:
--   Hash families, biased hashes, code intersection, guessers and self-encrypted CISS oracles
-- statement:
--   Fix a finite alphabet $\Sigma$ and a length $n$ (in the paper $\Sigma=\mathbb F_q^s$).
--
--   1. A **hash family** is $H=(H_i:\Sigma\to\{0,1\})_{i\in[n]}$, and $H(c)=H_1(c_1)\|\cdots\|H_n(c_n)$. For $z\in\{0,1\}^\ell$, $z\|0^{n-\ell}$ is the padded target.
--   2. Under $\mathrm{Bias}_{n,p,\Sigma}$ all values $H_i(x)$ are independent with $\Pr[H_i(x)=1]=p$; the weight of $H$ is $\prod_{i,x}p^{H_i(x)}(1-p)^{1-H_i(x)}$, and $\mathbb E_H$, $\Pr_H$ are the corresponding finite sums.
--   3. The **code intersection relation** of a code $C\subseteq\Sigma^n$ is $R_{C,H}=\{(b,c):c\in C,\ H(c)=b\}$ (Definition 4). $\mathsf{Valid}_H(T)$ for a tuple $T$ of $L$ pairs means the pairs are distinct and each lies in $R_{C,H}$; the variant with $\ell$-bit targets requires $H(c^{(j)})=z_j\|0^{n-\ell}$.
--   4. A **guesser** with a $t$-bit classical input is a kernel sending each $w\in\{0,1\}^t$ to a sub-probability distribution on output tuples (missing mass is a failure output).
--   5. **List recovery** and **coordinate-symbol diversity** (Definition 3, items 2–3): if $\frac1n\sum_i|S_i|\le L$ then at most $2L$ codewords have $c_i\in S_i$ for all $i$; and every $L$ distinct codewords satisfy $\sum_i|\{c^{(j)}_i:j\in[L]\}|\ge nL/2$. Symbol weight counts nonzero symbols; $\Pr_{X\leftarrow\mathrm{Bin}(N,p)}[X>a]$ is the binomial tail.
--   6. The **self-encrypted oracle** (Definition 6): for an injective $\mathsf{BinEnc}:[n]\times\Sigma\to\{0,1\}^\ell$ and $E\subseteq\{0,1\}^\ell\times\Sigma^n$,
--   $$M[H,E](i,x,c)=\begin{cases}H_i(x)&\text{if } c\in C,\ H(c)=\mathsf{BinEnc}(i,x)\|0^{n-\ell},\ (\mathsf{BinEnc}(i,x),c)\in E,\\ \bot&\text{otherwise.}\end{cases}$$
--   For a set $G$ of hash families, the YES oracles are $M[H,\{0,1\}^\ell\times\Sigma^n]$ with $H\in G$, and the NO oracles are $M[H,E]$ with $H\in G$ and $E\subseteq F\times\Sigma^n$, $|F|\le n|\Sigma|/3$.
--   7. In the query model the answers $\bot,0,1$ are encoded as $00,01,10$ and accessed by XOR.
--
--   **Formalization Note** $\bot$ is `none` in `Option Bool`.
-- source:
--   Alper Cakan, Kai-Min Chung, Wei-Hsiang Hung, Tzu-Yi Yang, Separating ClonableQMA and QCMA Relative to a Classical Oracle, STOC 2027 submission #844 (October 2026), §3 p. 14 (Definition 3 items 2–3, symbol weight); §4 p. 16 (Bias, Definition 4, Valid); §6 p. 24 (Definition 6, CISS); footnote 6 p. 27 (distinct encodings of 0, 1, ⊥)

import Mathlib

set_option autoImplicit false

namespace ClonableQMASep.Main

/-! Hash families, biased hashes, code intersection, guessers and the self-encrypted CISS oracle,
over an arbitrary finite alphabet `A` (in the paper `A = Σ = F_q^s`). -/

/-- A **hash family** `H = (H_i : A → {0,1})_{i ∈ [n]}`. -/
abbrev HashFam (n : ℕ) (A : Type) := Fin n → A → Bool

/-- `H(c) = H_1(c_1) ‖ ⋯ ‖ H_n(c_n)`. -/
def hashWord {n : ℕ} {A : Type} (H : HashFam n A) (c : Fin n → A) : Fin n → Bool :=
  fun i => H i (c i)

/-- The padded target `z ‖ 0^{n−ℓ}` of `z ∈ {0,1}^ℓ` (for `ℓ ≤ n`). -/
def padTarget {n ℓ : ℕ} (z : Fin ℓ → Bool) : Fin n → Bool :=
  fun i => if h : i.val < ℓ then z ⟨i.val, h⟩ else false

/-- The weight `∏_{(i,x)} p^{H_i(x)} (1−p)^{1−H_i(x)}` of `H` under `Bias_{n,p,A}`: all values
`H_i(x)` independent with `Pr[H_i(x) = 1] = p`. -/
noncomputable def biasWeight {n : ℕ} {A : Type} [Fintype A] (p : ℝ) (H : HashFam n A) : ℝ :=
  ∏ i, ∏ x, (if H i x then p else 1 - p)

/-- The expectation `E_{H ← Bias_{n,p,A}}[g(H)]`. -/
noncomputable def biasExp {n : ℕ} {A : Type} [Fintype A] [DecidableEq A] (p : ℝ)
    (g : HashFam n A → ℝ) : ℝ :=
  ∑ H : HashFam n A, biasWeight p H * g H

/-- The probability `Pr_{H ← Bias_{n,p,A}}[H ∈ G]`. -/
noncomputable def biasProb {n : ℕ} {A : Type} [Fintype A] [DecidableEq A] (p : ℝ)
    (G : Set (HashFam n A)) : ℝ := by
  classical exact biasExp p (fun H => if H ∈ G then 1 else 0)

/-- The number `|H_i^{-1}(b)|` of preimages of `b` under `H_i`. -/
def preCard {n : ℕ} {A : Type} [Fintype A] (H : HashFam n A) (i : Fin n) (b : Bool) : ℕ :=
  (Finset.univ.filter fun x => H i x = b).card

/-- The **code intersection relation** `R_{C,H} = {(b, c) ∈ {0,1}^n × A^n : c ∈ C, H(c) = b}`
(Definition 4). -/
def CIRel {n : ℕ} {A : Type} (C : Set (Fin n → A)) (H : HashFam n A) :
    Set ((Fin n → Bool) × (Fin n → A)) :=
  {bc | bc.2 ∈ C ∧ hashWord H bc.2 = bc.1}

/-- `Valid_H(T)` (Lemma 3): the `L` pairs of `T` are pairwise distinct and each lies in
`R_{C,H}`. -/
def Valid {n L : ℕ} {A : Type} (C : Set (Fin n → A)) (H : HashFam n A)
    (T : Fin L → (Fin n → Bool) × (Fin n → A)) : Prop :=
  Function.Injective T ∧ ∀ j, T j ∈ CIRel C H

/-- `Valid_H(T)` for tuples with `ℓ`-bit targets (§6.2, p. 26): the pairs `(z_j, c^{(j)})` are
pairwise distinct, `c^{(j)} ∈ C` and `H(c^{(j)}) = z_j ‖ 0^{n−ℓ}`. -/
def ValidPad {n ℓ L : ℕ} {A : Type} (C : Set (Fin n → A)) (H : HashFam n A)
    (T : Fin L → (Fin ℓ → Bool) × (Fin n → A)) : Prop :=
  Function.Injective T ∧ ∀ j, (T j).2 ∈ C ∧ hashWord H (T j).2 = padTarget (T j).1

/-- A **query-free guesser with a `t`-bit classical input**, fixed independently of the hash: a
kernel sending each `w ∈ {0,1}^t` to a sub-probability distribution on output tuples (mass
missing from `1` is a failure output). -/
def IsGuesser {t : ℕ} {Out : Type} [Fintype Out] (G : (Fin t → Bool) → Out → ℝ) : Prop :=
  ∀ w, (∀ o, 0 ≤ G w o) ∧ ∑ o, G w o ≤ 1

/-- The probability `Pr_{T ← G(w)}[P(T)]` of an event under a guesser's output. -/
noncomputable def guessProb {t : ℕ} {Out : Type} [Fintype Out] (G : (Fin t → Bool) → Out → ℝ)
    (w : Fin t → Bool) (P : Out → Prop) : ℝ := by
  classical exact ∑ o, if P o then G w o else 0

/-- **List recovery** (Definition 3, item 2): if `S_1, …, S_n ⊆ A` have
`(1/n) ∑_i |S_i| ≤ L`, at most `2L` codewords `c ∈ C` have `c_i ∈ S_i` for every `i`. -/
def ListRecoverable {n : ℕ} {A : Type} (C : Set (Fin n → A)) (L : ℕ) : Prop :=
  ∀ S : Fin n → Finset A, (1 / (n : ℝ)) * ∑ i, ((S i).card : ℝ) ≤ L →
    {c | c ∈ C ∧ ∀ i, c i ∈ S i}.ncard ≤ 2 * L

/-- **Coordinate-symbol diversity** (Definition 3, item 3, inequality (1)): every `L` distinct
codewords `c^{(1)}, …, c^{(L)} ∈ C` satisfy `∑_i |{c_i^{(j)} : j ∈ [L]}| ≥ nL/2`. -/
def Diverse {n : ℕ} {A : Type} [DecidableEq A] (C : Set (Fin n → A)) (L : ℕ) : Prop :=
  ∀ c : Fin L → (Fin n → A), Function.Injective c → (∀ j, c j ∈ C) →
    (n : ℝ) * L / 2 ≤ ∑ i, ((Finset.univ.image fun j => c j i).card : ℝ)

/-- The Hamming weight of `e ∈ A^n` in symbols: the number of nonzero coordinates. -/
def symWt {n : ℕ} {A : Type} [Zero A] [DecidableEq A] (e : Fin n → A) : ℕ :=
  (Finset.univ.filter fun i => e i ≠ 0).card

/-- The binomial tail `Pr_{X ← Bin(N, p)}[X > a] = ∑_{k > a} C(N,k) p^k (1−p)^{N−k}`. -/
noncomputable def binomTailGT (N : ℕ) (p : ℝ) (a : ℤ) : ℝ :=
  ∑ k ∈ Finset.range (N + 1), if a < (k : ℤ) then (N.choose k : ℝ) * p ^ k * (1 - p) ^ (N - k) else 0

/-- The **self-encrypted oracle** `M[H, E] : [n] × A × A^n → {0, 1, ⊥}` (Definition 6), with `⊥`
written `none`: `M[H,E](i, x, c) = H_i(x)` if `c ∈ C`, `H(c) = BinEnc(i,x) ‖ 0^{n−ℓ}` and
`(BinEnc(i,x), c) ∈ E`, and `⊥` otherwise. -/
noncomputable def cissOracle {n ℓ : ℕ} {A : Type} (C : Set (Fin n → A))
    (BinEnc : Fin n → A → (Fin ℓ → Bool)) (H : HashFam n A)
    (E : Set ((Fin ℓ → Bool) × (Fin n → A))) : Fin n → A → (Fin n → A) → Option Bool := by
  classical exact fun i x c =>
    if c ∈ C ∧ hashWord H c = padTarget (BinEnc i x) ∧ (BinEnc i x, c) ∈ E then some (H i x)
    else none

/-- The YES oracle family of the self-encrypted CISS problem (Definition 6):
`{M[H, {0,1}^ℓ × A^n] : H ∈ G}`. -/
def cissYes {n ℓ : ℕ} {A : Type} (C : Set (Fin n → A)) (BinEnc : Fin n → A → (Fin ℓ → Bool))
    (G : Set (HashFam n A)) : Set (Fin n → A → (Fin n → A) → Option Bool) :=
  {M | ∃ H ∈ G, M = cissOracle C BinEnc H Set.univ}

/-- The NO oracle family of the self-encrypted CISS problem (Definition 6):
`{M[H, E] : H ∈ G, E ⊆ F × A^n, F ⊆ {0,1}^ℓ, |F| ≤ n|A|/3}`. -/
def cissNo {n ℓ : ℕ} {A : Type} [Fintype A] (C : Set (Fin n → A))
    (BinEnc : Fin n → A → (Fin ℓ → Bool)) (G : Set (HashFam n A)) :
    Set (Fin n → A → (Fin n → A) → Option Bool) :=
  {M | ∃ H ∈ G, ∃ (E : Set ((Fin ℓ → Bool) × (Fin n → A))) (F : Finset (Fin ℓ → Bool)),
    E ⊆ (↑F : Set (Fin ℓ → Bool)) ×ˢ Set.univ ∧
    (F.card : ℝ) ≤ (n : ℝ) * (Fintype.card A : ℝ) / 3 ∧ M = cissOracle C BinEnc H E}

/-- The two-bit answer code with distinct encodings of `⊥, 0, 1`: `⊥ ↦ 00`, `0 ↦ 01`,
`1 ↦ 10`. -/
def ansVec : Option Bool → (Fin 2 → ZMod 2)
  | none => ![0, 0]
  | some false => ![0, 1]
  | some true => ![1, 0]

/-- The oracle `M : [n] × A × A^n → {0,1,⊥}` as a query-model function
`(i, x, c) ↦ code(M(i,x,c)) ∈ (ℤ/2)^2`, accessed by XOR. -/
def queryFn {n : ℕ} {A : Type} (M : Fin n → A → (Fin n → A) → Option Bool) :
    Fin n × A × (Fin n → A) → (Fin 2 → ZMod 2) :=
  fun q => ansVec (M q.1 q.2.1 q.2.2)

end ClonableQMASep.Main


