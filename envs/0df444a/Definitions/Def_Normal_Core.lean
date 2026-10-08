-- Prove2me | Definitions.Def_Normal_Core
-- name    : Normal_Core
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-06T15:24:53.488975+00:00
-- url     : https://prove2.me/theorems/ef41cdf5-131b-4144-b399-321486d55de3
-- title:
--   Normal numbers: words, occurrence counts, Borel normality, Champernowne and Copeland–Erdős sequences
-- statement:
--   This bundle fixes the vocabulary for the formalization of Champernowne (1933) and Copeland–Erdős (1946). All declarations live in the namespace `Normal`.
--
--   **Words and counts.** A digit sequence is a function $s:\mathbb N\to\mathbb N$ ($s_0$ is the first digit after the point); a word is a finite list of naturals. `occ w u` is the number of (overlapping) occurrences of the word $w$ in the finite word $u$; `count s w N` is the number of positions $i<N$ with $s_{i+j}=w_j$ for all $j<|w|$; `strs b n` is the finite set of all $b^n$ words of length $n$ over $\{0,\dots,b-1\}$.
--
--   **Normality.** `IsNormalSeq b s` holds if every word $w$ over $\{0,\dots,b-1\}$ satisfies
--   $$\lim_{N\to\infty}\frac{\mathrm{count}(s,w,N)}{N}=b^{-|w|}.$$
--   `digit b x n` $=\lfloor x\,b^{n+1}\rfloor\bmod b$ is the $n$-th base-$b$ digit of a real $x$ after the point, and `IsNormalReal b x` means that $n\mapsto$ `digit b x n` is normal in base $b$. `ofDigits b s` $=\sum_n s_n b^{-(n+1)}$ is the real number $0.s_0s_1s_2\ldots$.
--
--   **Concatenation.** `flatten d L` is the infinite sequence $L_0L_1L_2\cdots$ (the default $d$ is never used when all $L_i$ are nonempty); `digitsBE b m` is the usual base-$b$ expansion of $m$, most significant digit first; `concatDigits b a` is the digit sequence of $0.(a_0)_b(a_1)_b(a_2)_b\cdots$.
--
--   **The constants.** `champernowneConstant b` $=$ `ofDigits b (concatDigits b (· + 1))` $=0.(1)_b(2)_b(3)_b\cdots$ and `copelandErdosConstant b` $=0.(2)_b(3)_b(5)_b(7)_b\cdots$ (the primes, via `Nat.nth Nat.Prime`). `champernowneFin`, `copelandErdosFin` are the same digit sequences valued in `Fin b`.
--
--   **Champernowne's sequences.** `padDigits b r m` is the $r$-digit expansion of $m$ with leading zeros; `level b r` is Champernowne's $s_r$, all $b^r$ strings of $r$ digits in ascending order; `champI b`, `champII b μ`, `champIV b` are the digit sequences $s_1s_2s_3\cdots$, ${}_\mu s_1\,{}_\mu s_2\cdots$ and ${}_1s_1\,{}_2s_2\cdots$ of Theorems I, II, IV; `champGen b m` is the general schedule $({}_{m(0)}s_1)({}_{m(1)}s_2)\cdots$, with auxiliary `memb`, `grp`, `nBlk`, `lev`.
--
--   **Auxiliary.** `totalLen B J` $=\sum_{i<J}|B_i|$; `alc w m v` counts aligned occurrences of $w$ in $v$ at positions $0,|w|,2|w|,\dots$ below $m|w|$. `Agafonov.prefixList`, `Agafonov.blockCount`, `Agafonov.IsNormal` reproduce verbatim the integer-arithmetic definition of normality from `xiangyazi24/agafonov`. A few structural lemmas required by definition bodies (`flatten_mem`, `digitsBE_lt`, `concatDigits_lt`, `exists_lev`, ...) are proved inside the bundle.
-- source:
--   D. G. Champernowne, The construction of decimals normal in the scale of ten, J. London Math. Soc. 8 (1933), 254–260, p. 254 (definition of normality), p. 255 (the sequences s_r); A. H. Copeland and P. Erdős, Note on normal numbers, Bull. Amer. Math. Soc. 52 (1946), 857–860, p. 857. Lean source: https://github.com/xiangyazi24/normal/tree/ccb5977dc827e12f5f1b7266aec48a9b039370af/Normal

import Init
import Mathlib
set_option autoImplicit false


/- Original source header (imports hoisted):
import Mathlib
-/
/- Source module: Normal.Basic -/
section
set_option autoImplicit false


/-!
# Normal sequences and normal numbers: basic definitions

This file fixes the vocabulary shared by the formalizations of

* D. G. Champernowne, *The construction of decimals normal in the scale of ten*,
  J. London Math. Soc. 8 (1933), 254–260 (`papers/champernowne-1933.pdf`), and
* A. H. Copeland, P. Erdős, *Note on normal numbers*,
  Bull. Amer. Math. Soc. 52 (1946), 857–860 (`papers/copeland-erdos-1946.pdf`).

## Conventions

* A *digit sequence* is a function `s : ℕ → ℕ`; `s 0` is the first digit after the point.
* A *word* is a `List ℕ`; a word over base `b` has all entries `< b`.
* `count s w N` is the number of positions `i < N` at which the word `w` occurs in `s`
  (overlapping occurrences are counted). Champernowne's `G(x)` counts occurrences lying
  inside the first `x` digits; the two differ by at most `w.length`, so the limits agree.
* `IsNormalSeq b s` is Borel normality in base `b` exactly as defined on p. 254 of
  Champernowne and on p. 857 of Copeland–Erdős: every word of length `k` over base `b`
  occurs with limiting relative frequency `b⁻ᵏ`.
-/

open Filter Topology

namespace Normal

/-! ## Words and occurrences -/

/-- Number of (possibly overlapping) occurrences of the word `w` in the finite list `u`:
the number of positions `i < u.length` such that `w` is a prefix of `u.drop i`.
For `w ≠ []` this is the number of `i` with `i + w.length ≤ u.length` and
`u[i], …, u[i + w.length - 1] = w`. -/
def occ (w u : List ℕ) : ℕ :=
  ∑ i ∈ Finset.range u.length, if w <+: u.drop i then 1 else 0

/-- `count s w N` is the number of positions `i < N` at which the word `w` occurs in the
infinite digit sequence `s`, i.e. `s (i + j) = w[j]` for all `j < w.length`. -/
def count (s : ℕ → ℕ) (w : List ℕ) (N : ℕ) : ℕ :=
  ((Finset.range N).filter (fun i => ∀ j : Fin w.length, s (i + j) = w.get j)).card

/-- **Normality in base `b`** (Borel; Champernowne p. 254, Copeland–Erdős p. 857).
The digit sequence `s` is normal in base `b` if every word `w` over the alphabet
`{0, …, b-1}` occurs in `s` with limiting relative frequency `b ^ (-w.length)`. -/
def IsNormalSeq (b : ℕ) (s : ℕ → ℕ) : Prop :=
  ∀ w : List ℕ, (∀ d ∈ w, d < b) →
    Tendsto (fun N : ℕ => (count s w N : ℝ) / N) atTop (𝓝 ((b : ℝ) ^ w.length)⁻¹)

/-! ## Base-`b` digits of real numbers -/

/-- The `n`-th digit after the point of the real number `x` in base `b`
(`n = 0` is the first digit after the point): `⌊x · bⁿ⁺¹⌋ mod b`. -/
noncomputable def digit (b : ℕ) (x : ℝ) (n : ℕ) : ℕ :=
  (⌊x * (b : ℝ) ^ (n + 1)⌋ % (b : ℤ)).toNat

/-- A real number is **normal in base `b`** if its sequence of base-`b` digits after the
point is normal in base `b`. -/
def IsNormalReal (b : ℕ) (x : ℝ) : Prop :=
  IsNormalSeq b (digit b x)

/-- The real number `0.s₀s₁s₂…` in base `b`, i.e. `∑ₙ sₙ b⁻⁽ⁿ⁺¹⁾`. -/
noncomputable def ofDigits (b : ℕ) (s : ℕ → ℕ) : ℝ :=
  ∑' n, (s n : ℝ) / (b : ℝ) ^ (n + 1)

/-! ## Finite strings over base `b` -/

/-- `strs b n` is the finite set of all words of length `n` over `{0, …, b-1}`. -/
def strs (b : ℕ) : ℕ → Finset (List ℕ)
  | 0 => {[]}
  | n + 1 => ((Finset.range b) ×ˢ strs b n).image (fun p => p.1 :: p.2)

/-! ## Concatenating a sequence of words -/

/-- `flatten d L` is the infinite sequence `L 0 ++ L 1 ++ L 2 ++ ⋯`.
Its `n`-th entry is read off from the concatenation of the first `n + 1` lists, which
already has more than `n` entries when every `L i` is nonempty. (The default `d` is only
used when that fails, i.e. never in our applications.) -/
def flatten {α : Type*} (d : α) (L : ℕ → List α) (n : ℕ) : α :=
  ((List.range (n + 1)).flatMap L).getD n d

/-- The usual written base-`b` expansion of `m`, most significant digit first
(`Nat.digits` is least significant first). E.g. `digitsBE 10 123 = [1, 2, 3]`. -/
def digitsBE (b m : ℕ) : List ℕ := (Nat.digits b m).reverse

/-- The digit sequence of `0.a₀a₁a₂…` in base `b`: the base-`b` expansions of the terms of
the sequence `a`, written one after another. -/
def concatDigits (b : ℕ) (a : ℕ → ℕ) : ℕ → ℕ :=
  flatten 0 (fun i => digitsBE b (a i))

end Normal

end

/- Original source header (imports hoisted):
import Normal.Basic
-/
/- Source module: Normal.Agafonov -/
section
set_option autoImplicit false


/-!
# Compatibility with the `agafonov` repository's definition of normality

The repository `xiangyazi24/agafonov` (branch `research-dot/agafonov-formalization-20261002`,
file `Agafonov/Target.lean`, commit `cb08d11`) defines normality of a sequence `x : ℕ → Fin b`
with integer arithmetic, in a form that avoids reals and truncated subtraction. That
repository is pinned to a different Lean toolchain (`v4.31.0-rc2`), so it is not a Lake
dependency here. Instead its three definitions are copied **verbatim** into the namespace
`Normal.Agafonov`, and we prove that they agree with `Normal.IsNormalSeq`:

* `count_eq_blockCount`: the two occurrence counters agree on corresponding words;
* `isNormalSeq_iff_isNormal`: `IsNormalSeq b (fun n => (x n : ℕ)) ↔ Agafonov.IsNormal x`.

Hence every normality theorem of this repository can be restated in the `agafonov` form.
-/

open Filter Topology

namespace Normal

namespace Agafonov

/-! ### Verbatim copies of the `agafonov` definitions -/

/-- Positions are zero-based. (Copied from `agafonov`.) -/
def prefixList {α : Type*} (x : Nat → α) (n : Nat) : List α :=
  List.ofFn (fun i : Fin n => x i)

/-- Sliding occurrences starting at the positions `0, ..., n-1`. (Copied from `agafonov`.) -/
def blockCount {b : Nat} (x : Nat → Fin b) (w : List (Fin b)) (n : Nat) : Nat :=
  (List.range n).countP (fun i => prefixList (fun j => x (i + j)) w.length == w)

/-- Borel normality expressed with integer arithmetic: for every positive integer `e`,
the discrepancy between `b^|w| * count(w,n)` and `n` is eventually at most `n/e`.
(Copied from `agafonov`.) -/
def IsNormal {b : Nat} (x : Nat → Fin b) : Prop :=
  ∀ w : List (Fin b), ∀ e : Nat, 0 < e → ∃ N : Nat, ∀ n : Nat, N ≤ n →
    e * (b ^ w.length * blockCount x w n) ≤ e * n + n ∧
    e * n ≤ e * (b ^ w.length * blockCount x w n) + n

end Agafonov

/-! ### The occurrence counters agree -/





/-! ### Real-limit form versus integer `e`-form -/



/-! ### The two definitions of normality agree -/



end Normal

end

/- Original source header (imports hoisted):
import Normal.Basic
-/
/- Source module: Normal.Flatten -/
section
set_option autoImplicit false


/-!
# Basic facts about `Normal.flatten`

`flatten d L` is the infinite concatenation `L 0 ++ L 1 ++ ⋯`. When every `L i` is
nonempty its first `|L 0| + ⋯ + |L (J-1)|` entries are exactly
`(List.range J).flatMap L`, every entry lies in some `L i`, and flattening is associative.
-/

namespace Normal

variable {α : Type*}

/-! ### The finite concatenations `L 0 ++ ⋯ ++ L (J-1)` form a prefix chain -/

/-- `L 0 ++ ⋯ ++ L J = (L 0 ++ ⋯ ++ L (J-1)) ++ L J`. -/
theorem flatMap_range_succ (L : ℕ → List α) (J : ℕ) :
    (List.range (J + 1)).flatMap L = (List.range J).flatMap L ++ L J := by
  simp [List.range_succ, List.flatMap_append]



/-- With nonempty blocks, the first `J` blocks have at least `J` entries. -/
theorem le_length_flatMap_range {L : ℕ → List α} (hne : ∀ i, L i ≠ []) (J : ℕ) :
    J ≤ ((List.range J).flatMap L).length := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [flatMap_range_succ, List.length_append]
    have := List.length_pos_iff.mpr (hne J)
    omega







/-- Every entry of `flatten d L` is an entry of some `L i`. -/
theorem flatten_mem {d : α} {L : ℕ → List α} (hne : ∀ i, L i ≠ []) (n : ℕ) :
    ∃ i, flatten d L n ∈ L i := by
  have h1 : n < ((List.range (n + 1)).flatMap L).length :=
    lt_of_lt_of_le (Nat.lt_succ_self n) (le_length_flatMap_range hne _)
  have hmem : flatten d L n ∈ (List.range (n + 1)).flatMap L := by
    unfold flatten
    rw [List.getD_eq_getElem _ _ h1]
    exact List.getElem_mem h1
  obtain ⟨i, -, hi⟩ := List.mem_flatMap.mp hmem
  exact ⟨i, hi⟩



end Normal

end

/- Original source header (imports hoisted):
import Normal.Basic
-/
/- Source module: Normal.Strs -/
section
set_option autoImplicit false


/-!
# The finite set `strs b n` of words of length `n` over base `b`
-/

namespace Normal





end Normal

end

/- Original source header (imports hoisted):
import Normal.Flatten
import Normal.Strs
-/
/- Source module: Normal.LargeDeviation -/
section
set_option autoImplicit false


/-!
# The Copeland–Erdős counting lemma (large deviations for word counts)

Copeland–Erdős, p. 858, **Lemma**: *the number of integers up to `N` which are not
`(ε, k)` normal with respect to a given base `β` is less than `N^δ`, where
`δ = δ(ε, k, β) < 1`.*

We prove the form that is actually used (only the upper deviation is needed, see
`Normal.Blocks`): among the `bⁿ` words of length `n` over base `b`, those in which a fixed
word `w` occurs more than `(b^{-|w|} + ε) · n` times number at most `C · βⁿ` for some
`β < b`. Since a number below `bⁿ` is a word of length `n`, `C βⁿ = C N^{log_b β}`
recovers the lemma.

Proof (a Chernoff bound, replacing the paper's explicit binomial-tail estimate and its
Borel grouping step): split the occurrence positions by residue mod `k = |w|`; within one
residue class the windows are disjoint, so the exponential moment `∑ λ^{count}` over all
words factorises as `(bᵏ - 1 + λ)^m · b^{rest}`; Markov's inequality with a suitable
`λ > 1` gives the geometric saving.
-/

open Filter Topology

namespace Normal

/-- Aligned occurrence count: the number of `j < m` such that `w` is a prefix of
`v.drop (|w| * j)`, i.e. occurrences of `w` starting at positions `≡ 0 mod |w|`. -/
def alc (w : List ℕ) (m : ℕ) (v : List ℕ) : ℕ :=
  ∑ j ∈ Finset.range m, if w <+: v.drop (w.length * j) then 1 else 0



























end Normal

end

/- Original source header (imports hoisted):
import Normal.LargeDeviation
-/
/- Source module: Normal.Blocks -/
section
set_option autoImplicit false


/-!
# Normality of a concatenation of blocks

A general criterion, abstracted from the proof of the theorem of Copeland–Erdős
(pp. 858–860), for the sequence `B 0 ++ B 1 ++ B 2 ++ ⋯` of digit blocks to be normal:

1. the average block length tends to infinity (`J / T J → 0`, where `T J` is the total
   length of the first `J` blocks), so occurrences straddling block boundaries are
   negligible;
2. the current block is negligible against what came before (`|B J| / T J → 0`), so a
   prefix ending inside a block behaves like one ending at a block boundary;
3. every family of words that is *exponentially thin* (at most `C βⁿ` of length `n`, with
   `β < b`) carries an asymptotically negligible share of the total length.

Condition 3 is fed by `Normal.large_deviation`: the blocks in which a given word is
over-represented form an exponentially thin family, so they do not matter, and in all the
remaining blocks the word has frequency at most `b^{-k} + ε`. This gives the upper bound
`limsup count / N ≤ b^{-k}` for every word; since the counts of the `bᵏ` words of length
`k` add up to `N`, the matching lower bound follows (the paper's closing remark on p. 860).
-/

open Filter Topology

namespace Normal

/-- Total length of the first `J` blocks. -/
def totalLen (B : ℕ → List ℕ) (J : ℕ) : ℕ := ∑ i ∈ Finset.range J, (B i).length































variable {b : ℕ} {B : ℕ → List ℕ}







end Normal

end

/- Original source header (imports hoisted):
import Normal.Flatten
-/
/- Source module: Normal.Real -/
section
set_option autoImplicit false


/-!
# From normal digit sequences to normal real numbers

Champernowne and Copeland–Erdős speak of the *decimal* `0.a₁a₂a₃…`. We record the bridge
from a digit sequence `s` to the real number `ofDigits b s = ∑ sₙ b^{-(n+1)}`: when `s` is a
genuine base-`b` digit sequence that is not eventually `b - 1`, the base-`b` digits of
`ofDigits b s` are exactly `s`. A normal sequence is never eventually `b - 1` (the digit `0`
must have frequency `1/b`), so normality transfers to the real number.
-/

open Filter Topology

namespace Normal









end Normal

end

/- Original source header (imports hoisted):
import Normal.Blocks
-/
/- Source module: Normal.CopelandErdos -/
section
set_option autoImplicit false


/-!
# The theorem of Copeland and Erdős

A. H. Copeland, P. Erdős, *Note on normal numbers*, Bull. Amer. Math. Soc. 52 (1946),
857–860, p. 857:

> **THEOREM.** *If `a₁, a₂, ⋯` is an increasing sequence of integers such that for every
> `θ < 1` the number of `a`'s up to `N` exceeds `N^θ` provided `N` is sufficiently large,
> then the infinite decimal `0.a₁a₂a₃⋯` is normal with respect to the base `β` in which
> these integers are expressed.*

Formal reading: the sequence is `a : ℕ → ℕ`, strictly increasing ("increasing sequence of
integers", whose terms are written out in base `b`, hence positive); "the number of `a`'s
up to `N`" is `#{i | a i ≤ N}`, which we write as a filter over `range (N + 1)` (this loses
nothing: `a i ≥ i` for a strictly increasing sequence of naturals, so `a i ≤ N` forces
`i ≤ N`).

Corollaries on the same page: the conjecture of Champernowne that `0.235711131719⋯`
(the primes) is normal, and Champernowne's own Theorem III, `0.123456789101112⋯`.
-/

open Filter Topology

namespace Normal

/-- The base-`b` expansion of a positive number is a nonempty word. -/
theorem digitsBE_ne_nil {b m : ℕ} (hm : 0 < m) : digitsBE b m ≠ [] := by
  simp [digitsBE, Nat.digits_ne_nil_iff_ne_zero, hm.ne']

/-- The entries of a base-`b` expansion are digits `< b`. -/
theorem digitsBE_lt {b m : ℕ} (hb : 2 ≤ b) {d : ℕ} (hd : d ∈ digitsBE b m) : d < b :=
  Nat.digits_lt_base (by omega) (List.mem_reverse.1 hd)

/-- The digits of `0.a₀a₁a₂⋯` are digits in base `b`. -/
theorem concatDigits_lt {b : ℕ} (hb : 2 ≤ b) {a : ℕ → ℕ} (ha : ∀ i, 0 < a i) (n : ℕ) :
    concatDigits b a n < b := by
  obtain ⟨i, hi⟩ := flatten_mem (d := 0) (fun i => digitsBE_ne_nil (b := b) (ha i)) n
  exact digitsBE_lt hb hi













section CopelandErdosProof

variable {b : ℕ} {a : ℕ → ℕ}































end CopelandErdosProof







end Normal

end

/- Original source header (imports hoisted):
import Normal.Blocks
-/
/- Source module: Normal.Champernowne -/
section
set_option autoImplicit false


/-!
# Champernowne's Theorems I, II and IV

D. G. Champernowne, *The construction of decimals normal in the scale of ten*,
J. London Math. Soc. 8 (1933), 254–260, p. 255. Let `s_r` denote the sequence
`00..0, 00..1, 00..2, ⋯, 99..9` of all `10^r` arrangements of `r` digits in ascending
order, and `_μs_r` the sequence `s_r` repeated `μ` times.

* **Theorem I.** `0.s₁s₂s₃⋯` is normal in the scale of ten.
* **Theorem II.** For every fixed positive integer `μ`, `0._μs₁ _μs₂ ⋯ _μs_r ⋯` is normal.
* **Theorem III.** `0.123456789101112⋯` is normal (see `Normal.champernowne_concat`).
* **Theorem IV.** `0.₁s₁ ₂s₂ ⋯ _rs_r ⋯` is normal.

We state and prove them in every base `b ≥ 2`; base ten is the specialisation in
`Normal.Main`. Champernowne's proofs count occurrences exactly; ours go through the block
criterion `Normal.isNormalSeq_flatten`, with the members of `s_r` as the blocks.
-/

open Filter Topology

namespace Normal

/-- The `r`-digit base-`b` string of `m` with leading zeros (most significant first);
for `m < b ^ r` this is the member of `s_r` that represents `m`. -/
def padDigits (b r m : ℕ) : List ℕ := List.ofFn (fun i : Fin r => m / b ^ (r - 1 - i) % b)

/-- Champernowne's `s_r` in base `b`, written out as one list of digits: the `b ^ r`
strings of `r` digits in ascending order. -/
def level (b r : ℕ) : List ℕ := (List.range (b ^ r)).flatMap (padDigits b r)

/-- Digit sequence of Theorem I: `s₁ s₂ s₃ ⋯`. -/
def champI (b : ℕ) : ℕ → ℕ := flatten 0 (fun r => level b (r + 1))

/-- Digit sequence of Theorem II: `_μs₁ _μs₂ _μs₃ ⋯`, each `s_r` repeated `μ` times. -/
def champII (b μ : ℕ) : ℕ → ℕ :=
  flatten 0 (fun r => (List.replicate μ (level b (r + 1))).flatten)

/-- Digit sequence of Theorem IV: `₁s₁ ₂s₂ ₃s₃ ⋯`, with `s_r` repeated `r` times. -/
def champIV (b : ℕ) : ℕ → ℕ :=
  flatten 0 (fun r => (List.replicate (r + 1) (level b (r + 1))).flatten)


/-! ## The strings `padDigits b r m` -/











/-! ## Abstract block sequences `flatten [] M` -/

section Abstract

variable (M : ℕ → List (List ℕ))

/-- Number of blocks in the first `R` groups `M 0, …, M (R-1)`. -/
def nBlk (R : ℕ) : ℕ := ((List.range R).flatMap M).length

theorem nBlk_succ (R : ℕ) : nBlk M (R + 1) = nBlk M R + (M R).length := by
  simp [nBlk, List.range_succ, List.flatMap_append]



variable {M}

theorem le_nBlk (hM : ∀ r, M r ≠ []) (R : ℕ) : R ≤ nBlk M R := by
  induction R with
  | zero => simp
  | succ R ih => rw [nBlk_succ]; have := List.length_pos_iff.2 (hM R); omega









theorem exists_lev (hM : ∀ r, M r ≠ []) (J : ℕ) : ∃ R, J < nBlk M (R + 1) :=
  ⟨J, by have := le_nBlk hM (J + 1); omega⟩

/-- The group index of the block number `J`: the least `R` with `J < nBlk M (R + 1)`. -/
def lev (hM : ∀ r, M r ≠ []) (J : ℕ) : ℕ := Nat.find (exists_lev hM J)







end Abstract




/-! ## Champernowne's block sequences -/

/-- The members of `s_{r+1}`, as a list of blocks. -/
def memb (b r : ℕ) : List (List ℕ) := (List.range (b ^ (r + 1))).map (padDigits b (r + 1))

/-- The `r`-th group of blocks: `mult r` copies of the members of `s_{r+1}`. -/
def grp (b : ℕ) (mult : ℕ → ℕ) (r : ℕ) : List (List ℕ) := (List.replicate (mult r) (memb b r)).flatten

/-- `s_1` repeated `mult 0` times, then `s_2` repeated `mult 1` times, and so on. -/
def champGen (b : ℕ) (mult : ℕ → ℕ) : ℕ → ℕ :=
  flatten 0 (fun r => (List.replicate (mult r) (level b (r + 1))).flatten)
































end Normal

end

/- Original source header (imports hoisted):
import Normal.CopelandErdos
import Normal.Champernowne
import Normal.Real
import Normal.Agafonov
-/
/- Source module: Normal.Main -/
section
set_option autoImplicit false


/-!
# Headline theorems: the Champernowne and Copeland–Erdős constants are normal

Real-number forms, in base ten exactly as in the papers, and in every base `b ≥ 2`.
The `example`s at the end check, by evaluation, that the digit sequences are the intended
ones (`0.123456789101112…`, `0.0123456789000102…`).
-/

open Filter Topology

namespace Normal

/-- The Champernowne constant in base `b`: `0.123456789101112⋯` (base `b` expansions of
`1, 2, 3, …` concatenated). -/
noncomputable def champernowneConstant (b : ℕ) : ℝ := ofDigits b (concatDigits b (· + 1))

/-- The Copeland–Erdős constant in base `b`: `0.235711131719⋯` (the primes in base `b`). -/
noncomputable def copelandErdosConstant (b : ℕ) : ℝ :=
  ofDigits b (concatDigits b (Nat.nth Nat.Prime))















/-! ## The same results in the `agafonov` repository's form

Via `isNormalSeq_iff_isNormal`, the digit sequences, viewed as `ℕ → Fin b`, satisfy
`Agafonov.IsNormal` (the integer-arithmetic definition of `xiangyazi24/agafonov`). -/

/-- The Champernowne digit sequence, as a `Fin b`-valued sequence. -/
def champernowneFin {b : ℕ} (hb : 2 ≤ b) (n : ℕ) : Fin b :=
  ⟨concatDigits b (· + 1) n, concatDigits_lt hb (fun _ => Nat.succ_pos _) n⟩

/-- The Copeland–Erdős digit sequence, as a `Fin b`-valued sequence. -/
noncomputable def copelandErdosFin {b : ℕ} (hb : 2 ≤ b) (n : ℕ) : Fin b :=
  ⟨concatDigits b (Nat.nth Nat.Prime) n,
    concatDigits_lt hb (fun i => (Nat.prime_nth_prime i).pos) n⟩





/-! ## Sanity checks on the digit sequences -/





end Normal

end

/- Original source header (imports hoisted):
import Normal.Basic
import Normal.Agafonov
import Normal.Flatten
import Normal.Strs
import Normal.LargeDeviation
import Normal.Blocks
import Normal.Real
import Normal.CopelandErdos
import Normal.Champernowne
import Normal.Main
-/
/- Source module: Normal -/
section
set_option autoImplicit false


end


