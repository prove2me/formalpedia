-- Prove2me | Definitions.Def_TurnstileCutSparsify_Main_Randomness
-- name    : TurnstileCutSparsify_Main_Randomness
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T18:40:23.194491+00:00
-- url     : https://prove2.me/theorems/021da83d-96e5-4885-92e5-f28cad21e671
-- title:
--   Four-wise independent families (App. A.4), read-once space-bounded algorithms, generators and local bit computation (§2.4), Freedman's quadratic variation, and the quadratic sign forms of Lemma 5.1
-- statement:
--   **Four-wise independence.** A seeded family $F:\mathrm{Seed}\times\alpha\to\beta$ with a uniformly random seed is $k$-wise independent with uniform marginals if for every $j\le k$ distinct points $a_1,\dots,a_j$ the values $(F(a_1),\dots,F(a_j))$ are uniform on $\beta^j$. Four-wise hashes into $[B]$ and four-wise unbiased signs are the cases $k=4$, $\beta=[B]$ and $\beta=\{\pm1\}$.
--
--   **Appendix A.4.** Let $m$ be the smallest integer $2\cdot3^a$ with $2^m\ge\max\{N,B_S\}$ and $\mathbb F_{2^m}=\mathbb F_2[z]/(z^m+z^{m/2}+1)$. Each pair $e$ is identified with the field element whose binary representation is $\mathrm{id}(e)$, $\mathrm{id}(\{u,v\})=(v-1)(v-2)/2+u-1$ (§7.1). A seed is a uniformly random polynomial of degree at most three; for a table of width $B=2^b$, $b$ fixed bits of its value give the hash and one fixed bit gives the sign.
--
--   **Space-bounded computation (§2.4).** An algorithm runs in space $S$ if it has $S$ bits of working memory and read-only access to its input, and reads its random bits once, in a fixed order; for a fixed input it is a read-once branching program of width $2^S$ over its random bits, with a set of failing final states. A generator $G$ from $s$ seed bits to $L_{out}$ bits fools such algorithms with error $\eta$ if, for every such program reading at most $L_{out}$ bits, its failure probability on the first output bits of $G$ for a uniform seed exceeds its failure probability on uniform bits by at most $\eta$. A word-RAM program computes the output bits locally within $T$ steps if, given an index $i$ and the seed packed $w$ bits per word, it halts within $T$ steps with bit $i$ of $G(\text{seed})$.
--
--   **Freedman's quadratic variation (Lemma 2.5).** For a process $Y$ and filtration $(\mathcal H_i)$, $V_i=\sum_{j=1}^i\mathbb E[d_j^2\mid\mathcal H_{j-1}]$ with $d_j=Y_j-Y_{j-1}$, valued in $[0,\infty]$.
--
--   **Lemma 5.1's quantities.** For signs $\sigma^{\pi,l}_f$, targets $T$ decoded at labels $\pi_e$ and collision vectors $u_e$: $c_{e,l}=\sum_f u_e(f)\sigma^{\pi_e,l}_f$ and $Q_F=\frac1R\sum_{e\in F\cap T}\sum_{l=1}^R\sigma^{\pi_e,l}_e c_{e,l}$.
--
--   **Formalization Note** `KWiseUniform k F` counts seeds; `a4m`, `bitsPoly`, `polyBits`, `gfMul` (product of the bit polynomials reduced modulo `z^m + z^{m/2} + 1`), `cubicEval` (Horner, addition = xor); `a4Hash m b c e` takes the `b` lowest bits and `a4Sign m c e` the lowest bit of the value at `pairId e = v(v − 1)/2 + u` (0-based). `ROBP W L` (start state, transitions per position and bit, failing set), `FoolsSpace S G η` (width `2^S`), `packBits`, `BitLocal`. `predQV μ ℱ Y i ω = ⨆ K, Σ_{j=1}^{i} μ[min(d_j², K) | ℱ (j−1)] ω`, the conditional expectation of the nonnegative `d_j²` as an increasing limit (so it is the textbook value whether or not `d_j²` is integrable). `collNoise`, `errQ`; a sign is a bit (`true` = −1).
-- source:
--   Lin, Mirrokni, Woodruff (2026), Near-Optimal Space and Time Cut Sparsification in Turnstile Streams, arXiv:2611.03604 (version of November 3, 2026, SHA-256 7beb32bf…), §2.4 p. 12, Lemma 2.5 p. 10, Lemma 5.1 p. 19, §7.1 p. 26, Appendix A.4 pp. 42–43

import Mathlib
import Definitions.Def_TurnstileCutSparsify_Main_Graph
import Definitions.Def_TurnstileCutSparsify_Main_Streaming

open scoped BigOperators Classical
open Polynomial

noncomputable section

namespace TurnstileCutSparsify.Main

open TurnstileRank.TightBounds.RAM

/-!
# Randomness: four-wise independent families, read-once space-bounded computation, generators

Lin, Mirrokni, Woodruff, arXiv:2611.03604 (version of November 3, 2026, SHA-256 7beb32bf…),
§2.4 p. 12, §7.1 p. 26 (pair identifiers), Appendix A.4 pp. 42–43.

* `pairId e = v(v − 1)/2 + u` for `e = {u, v}`, `u < v` (0-based): the bijection
  `id({u, v}) = (v − 1)(v − 2)/2 + u − 1` of §7.1 for 1-based vertices, onto `{0, …, N − 1}`.
* `KWiseUniform k F`: a family `F : Seed → α → β` with a uniformly random seed is `k`-wise
  independent with uniform marginals: for every `j ≤ k` distinct points the values are uniform on
  `β^j`. Four-wise independent hashes into `[B]` are `KWiseUniform 4` with `β = Fin B`;
  four-wise independent unbiased signs are `KWiseUniform 4` with `β = Bool` (`true` is the sign
  `−1`).
* Appendix A.4: `a4m N BS` is the smallest `m = 2 · 3^a` with `2^m ≥ max {N, BS}`; field elements
  of `F_{2^m} = F_2[z]/(z^m + z^{m/2} + 1)` are the naturals `< 2^m` (bit `i` = coefficient of
  `z^i`); a seed is four field elements (a uniformly random polynomial of degree at most three),
  evaluated at the field element `pairId e`; the hash into `[2^b]` takes the `b` lowest bits of the
  value and the sign takes its lowest bit.
* A read-once branching program of width `W` and length `L` (`ROBP W L`): a start state, a
  transition for each position and bit, and a set of failing final states. It is the model of
  §2.4: "an algorithm runs in space `S` if it has `S` bits of working memory and read-only access to
  its input, and it reads its random bits once, in a fixed order" — for a fixed input, such an
  algorithm is an `ROBP (2^S) L` over its random bits (its states are the contents of its working
  memory).
* `FoolsSpace S G err`: replacing the random bits of every such program reading at most `Lout`
  bits by the output of `G` on a uniform seed increases the failure probability by at most `err`.
* `BitLocal P w cells T G`: the word-RAM program `P` (word size `w`, `cells` cells), started with
  the index `i` in cell `0` followed by the seed packed `w` bits per word, halts within `T` steps
  with output bit `i` of `G(seed)` in cell `0`.
* `predQV μ ℱ Y i` is the predictable quadratic variation `V_i = Σ_{j=1}^{i} E[d_j² | H_{j−1}]` of
  Lemma 2.5 (p. 10), `d_j = Y_j − Y_{j−1}`, with values in `[0, ∞]`: the increasing limit over `K`
  of `Σ_j E[min (d_j², K) | H_{j−1}]`, which is the conditional expectation of the nonnegative
  `d_j²` whether or not `d_j²` is integrable.
* Lemma 5.1 (p. 19): for signs `σ^{π,l}_f` (a sign is a bit, `true` is `−1`), targets `T` decoded at
  labels `π_e`, and collision vectors `u_e`, `collNoise` is `c_{e,l} = Σ_f u_e(f) σ^{π_e,l}_f` and
  `errQ` is `Q_F = (1/R) Σ_{e ∈ F ∩ T} Σ_l σ^{π_e,l}_e c_{e,l}`.
-/

variable {n : ℕ}

/-- The identifier of a pair (§7.1), 0-based. -/
def pairId (e : Pair n) : ℕ := e.hi.val * (e.hi.val - 1) / 2 + e.lo.val

/-- A Rademacher sign from a bit: `false ↦ 1`, `true ↦ −1`. -/
def sgnB (b : Bool) : ℤ := if b then -1 else 1

/-- `k`-wise independence with uniform marginals of a seeded family: for every `j ≤ k` distinct
points the values are uniform on `β^j`. -/
def KWiseUniform {Seed α β : Type*} [Fintype Seed] [Fintype β] (k : ℕ) (F : Seed → α → β) :
    Prop :=
  ∀ j ≤ k, ∀ a : Fin j → α, Function.Injective a → ∀ b : Fin j → β,
    ((Finset.univ.filter fun s => ∀ i, F s (a i) = b i).card : ℝ) * (Fintype.card β : ℝ) ^ j =
      (Fintype.card Seed : ℝ)

/-- The field size exponent of Appendix A.4: the smallest `m = 2 · 3^a` with `2^m ≥ max {N, BS}`. -/
def a4m (N BS : ℕ) : ℕ :=
  if h : ∃ a : ℕ, max N BS ≤ 2 ^ (2 * 3 ^ a) then 2 * 3 ^ Nat.find h else 0

/-- The polynomial over `F_2` whose coefficients are the bits of `a`. -/
def bitsPoly (a : ℕ) : (ZMod 2)[X] :=
  ∑ i ∈ Finset.range a.size, if a.testBit i then (X : (ZMod 2)[X]) ^ i else 0

/-- The natural whose bits are the coefficients of a polynomial over `F_2`. -/
def polyBits (p : (ZMod 2)[X]) : ℕ :=
  ∑ i ∈ Finset.range (p.natDegree + 1), (p.coeff i).val * 2 ^ i

/-- The modulus `z^m + z^{m/2} + 1`. -/
def a4Modulus (m : ℕ) : (ZMod 2)[X] := X ^ m + X ^ (m / 2) + 1

/-- Multiplication in `F_2[z]/(z^m + z^{m/2} + 1)`. -/
def gfMul (m a b : ℕ) : ℕ := polyBits ((bitsPoly a * bitsPoly b) %ₘ a4Modulus m)

/-- The value at `z` of the polynomial `c 0 + c 1 z + c 2 z² + c 3 z³` over `F_{2^m}` (addition is
bitwise exclusive or). -/
def cubicEval (m : ℕ) (c : Fin 4 → ℕ) (z : ℕ) : ℕ :=
  gfMul m (gfMul m (gfMul m (c 3) z ^^^ c 2) z ^^^ c 1) z ^^^ c 0

/-- The Appendix A.4 hash into `[2^b]`: the `b` lowest bits of the polynomial's value at the pair. -/
def a4Hash (m b : ℕ) (c : Fin 4 → Fin (2 ^ m)) (e : Pair n) : Fin (2 ^ b) :=
  Fin.ofNat (2 ^ b) (cubicEval m (fun i => (c i).val) (pairId e))

/-- The Appendix A.4 sign: the lowest bit of the polynomial's value at the pair. -/
def a4Sign (m : ℕ) (c : Fin 4 → Fin (2 ^ m)) (e : Pair n) : Bool :=
  (cubicEval m (fun i => (c i).val) (pairId e)).testBit 0

/-- A read-once branching program of width `W` and length `L` over random bits. -/
structure ROBP (W L : ℕ) where
  start : Fin W
  next : Fin L → Fin W → Bool → Fin W
  fail : Finset (Fin W)

/-- The final state of an `ROBP` on a bit string, reading the bits once, in order. -/
def ROBP.final {W L : ℕ} (P : ROBP W L) (bits : Fin L → Bool) : Fin W :=
  (List.finRange L).foldl (fun st i => P.next i st (bits i)) P.start

/-- The program fails on the bit string. -/
def ROBP.Fails {W L : ℕ} (P : ROBP W L) (bits : Fin L → Bool) : Prop := P.final bits ∈ P.fail

/-- `G` fools every space-`S` read-once algorithm reading at most `Lout` bits, with additive error
`err` on its failure probability. -/
def FoolsSpace (S : ℕ) {s Lout : ℕ} (G : (Fin s → Bool) → Fin Lout → Bool) (err : ℝ) : Prop :=
  ∀ (L : ℕ) (hL : L ≤ Lout) (P : ROBP (2 ^ S) L),
    prob (fun seed : Fin s → Bool => P.Fails fun i => G seed ⟨i.val, lt_of_lt_of_le i.2 hL⟩) ≤
      prob (fun bits : Fin L → Bool => P.Fails bits) + err

/-- A bit string packed `w` bits per word (bit `t` of word `j` is bit `j w + t`). -/
def packBits (w s : ℕ) (seed : Fin s → Bool) : List ℕ :=
  (List.range ((s + w - 1) / w)).map fun j =>
    ∑ t ∈ Finset.range w, if h : j * w + t < s then (if seed ⟨j * w + t, h⟩ then 2 ^ t else 0)
      else 0

/-- The program `P` computes every output bit of `G` from the seed within `T` steps. -/
def BitLocal (P : Program) (w cells T : ℕ) {s Lout : ℕ} (G : (Fin s → Bool) → Fin Lout → Bool) :
    Prop :=
  ∀ (seed : Fin s → Bool) (i : Fin Lout), ∃ m,
    runWithin w cells P T (setInputs w (fun _ => 0) (i.val :: packBits w s seed)) = some m ∧
      rd m 0 = some (if G seed i then 1 else 0)

/-- The predictable quadratic variation `V_i = Σ_{j=1}^{i} E[d_j² | H_{j−1}] ∈ [0, ∞]`. -/
def predQV {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : MeasureTheory.Measure Ω)
    (ℱ : MeasureTheory.Filtration ℕ m0) (Y : ℕ → Ω → ℝ) (i : ℕ) (ω : Ω) : ENNReal :=
  ⨆ K : ℕ, ENNReal.ofReal (∑ j ∈ Finset.Icc 1 i,
    (MeasureTheory.condExp (ℱ (j - 1)) μ
      (fun ω' => min ((Y j ω' - Y (j - 1) ω') ^ 2) (K : ℝ))) ω)

/-- The collision noise `c_{e,l} = Σ_f u_e(f) σ^{π_e,l}_f` of Lemma 5.1. -/
def collNoise {N R : ℕ} {Λ : Type*} (π : Fin N → Λ) (u : Fin N → Fin N → ℝ)
    (σ : Λ → Fin R → Fin N → Bool) (e : Fin N) (l : Fin R) : ℝ :=
  ∑ f, u e f * (sgnB (σ (π e) l f) : ℝ)

/-- The error `Q_F = (1/R) Σ_{e ∈ F ∩ T} Σ_l σ^{π_e,l}_e c_{e,l}` of Lemma 5.1. -/
def errQ {N R : ℕ} {Λ : Type*} (π : Fin N → Λ) (u : Fin N → Fin N → ℝ)
    (σ : Λ → Fin R → Fin N → Bool) (T F : Finset (Fin N)) : ℝ :=
  (1 / (R : ℝ)) * ∑ e ∈ F ∩ T, ∑ l : Fin R, (sgnB (σ (π e) l e) : ℝ) * collNoise π u σ e l

end TurnstileCutSparsify.Main


