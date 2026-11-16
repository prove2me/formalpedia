-- Prove2me | Definitions.Def_EliasGlobalClock_LowerBound_Supplement_codes
-- name    : EliasGlobalClock_LowerBound_Supplement_codes
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T07:33:07.440303+00:00
-- url     : https://prove2.me/theorems/135fee25-6c21-4bae-ae86-72df95cef919
-- title:
--   Prefix-free codes, the sequence Int(t), Elias, MonoElias, SmoothCode and SmoothMonoCode
-- statement:
--   A **code** is a map $\mathrm{Code}:\mathbb Z_+\to\{0,1\}^*$; it is **prefix-free** when for $M\ne N$ the word $\mathrm{Code}(M)$ is not a prefix of $\mathrm{Code}(N)$ (in particular distinct integers get distinct words). $\mathrm{Bin}(N)$ is the base-2 representation, most significant bit first, with $\mathrm{Bin}(0)=\varepsilon$; $\mathrm{Bin}_{\mathrm{lsb}}(N)$ is its reversal, and $\mathrm{Bin}_q(N)=0^{q-|\mathrm{Bin}(N)|}\,\|\,\mathrm{Bin}(N)$.
--
--   For a code, $\mathrm{Int}(t)$ is the unique positive $N$ such that $\mathrm{Code}(N)$ is a prefix of the infinite string $\mathrm{Bin}_{\mathrm{lsb}}(t)\,\|\,0^\infty$ (the bits of $t$, least significant first), and $\mathrm{Int}(t)=0$ if there is none. A code has the **prefix property** if $\mathrm{Int}(t)\ge1$ for every $t\ge1$, and the **monotonicity property** if for every $N\ge1$ and every $j\ge0$ the aligned interval
--   $$J=[\,j\cdot 2P,\ (j+1)\cdot 2P\,),\qquad P=2^{|\mathrm{Code}(N)|},$$
--   contains positive times $\tau_1<\dots<\tau_N$ with $\mathrm{Int}(\tau_i)=i$.
--
--   The concrete codes are those of the paper.
--   1. **Elias $\omega$-code**: $N_1=N$, $N_i=\lfloor\log_2 N_{i-1}\rfloor$, $k$ minimal with $N_k\in\{2,3\}$; $\mathrm{Elias}(1)=0$ and $\mathrm{Elias}(N)=\mathrm{Bin}(N_k)\|\cdots\|\mathrm{Bin}(N_1)\|0$.
--   2. **MonoElias**: the same with each $\mathrm{Bin}(N_i)$ replaced by $\mathrm{RBin}(N_i)=1\|\mathrm{Reverse}(s)$ where $\mathrm{Bin}(N_i)=1\|s$.
--   3. **SmoothCode**: groups $G_0=\{1,2\}$, $G_1=\{3\}$, $G_r=[2^r-2^{r-2}+1,\,2^r+2^{r-1}]$ ($r\ge2$), $\mathrm{gr}(N)$ the group index; $\mathrm{SmoothCode}(1)=00$, $\mathrm{SmoothCode}(2)=01$, $\mathrm{SmoothCode}(N)=1\|\mathrm{SmoothCode}(\mathrm{gr}(N))\|\mathrm{Enc}(N)$, where $\mathrm{Enc}(3)=\varepsilon$ and for $N\in G_r$, $r\ge2$, $\mathrm{Enc}(N)=0\|\mathrm{Bin}_{r-2}(N-[2^r-2^{r-2}+1])$ if $N\le 2^r$ and $1\|\mathrm{Bin}_{r-1}(N-[2^r+1])$ otherwise. $\mathrm{SmoothCode}_{\mathrm{lsb}}$ replaces each padded offset by its reversal.
--   4. **SmoothMonoCode**: with $d_N=|\mathrm{SmoothCode}(N)|$ and $H_r=\{2^r+1,\dots,2^{r+1}\}$ ($r\ge2$), it equals $\mathrm{SmoothCode}_{\mathrm{lsb}}(N)$ when $N\le4$ or $N\in H_r$ with $d_r<d_{r+1}$; otherwise $2^r+1+2x\mapsto 1\|\mathrm{SmoothCode}_{\mathrm{lsb}}(r+1)\|0\|\mathrm{Bin}^{r-1}_{\mathrm{lsb}}(x)$ and $2^r+2+2x\mapsto 1\|\mathrm{SmoothCode}_{\mathrm{lsb}}(r)\|1\|\mathrm{Bin}^{r-1}_{\mathrm{lsb}}(x)$.
--
--   Finally $\log^*N=\min\{\ell:\log_2^{(\ell)}N<2\}$, the product $\log n\cdot\log\log n\cdots$ is $\prod_{h=1}^{\log^* n}\log_2^{(h)}n$ (empty product $1$), and $\lceil\log_2(n+1)\rceil$ is a positive integer for $n\ge1$.
--
--   These objects are the coding layer of Theorems 2.1–2.3, 3.1 and B.2 and of the schedule of Algorithm 2.
--
--   **Formalization Note** Bit strings are `List Bool`. The codes are defined on $\mathbb N$ (the value at $0$ is unused) and wrapped as functions on $\mathbb N^+$. $\mathrm{Int}$ returns $0$ also if two codewords matched, which cannot happen for a prefix-free code. The group index is computed by the closed form $\mathrm{gr}(N)=\lfloor\log_2\lfloor(N-1)/3\rfloor\rfloor+2$ for $N\ge4$, equivalent to membership in $G_r$; $\log^*$ is computed with integer floors, which gives the same count.
-- source:
--   Kuowen Chen, Shengquan Du, Tsvi Kopelowitz, Seth Pettie, Ben Plosk, STOC 2027 submission #1311 (October 2026), The Necessity of Elias Codes in the Global Clock Model, printed pp.5–7, 22–28 / PDF pp.6–8, 23–29: §2 (Elias codes, Int(t)), Appendix A.1 (MonoElias), Appendix A.2 (Int for an arbitrary code, footnote 9), Appendix B (SmoothCode, SmoothCode_lsb, SmoothMonoCode); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1311.pdf

import Mathlib

namespace EliasGlobalClock.LowerBound.Supplement

/-! Binary codes for the positive integers and the integer sequence `Int(t)` of §2.
Printed pp.5–7 / PDF pp.6–8 (§2), Appendix A (printed pp.22–23), Appendix B
(printed pp.24–28). Bit strings are `List Bool`, `false` = 0 and `true` = 1. -/

/-- `Bin(N)`: the usual base-2 representation, most significant bit first.
`Bin(0)` is the empty string, as in the padding formulas of Appendix B. -/
def bin (N : ℕ) : List Bool := (Nat.bits N).reverse

/-- `Bin_q(N)`: `Bin(N)` padded on the left with zeros to exactly `q` bits. -/
def binPad (q N : ℕ) : List Bool := List.replicate (q - (bin N).length) false ++ bin N

/-- `Bin^q_lsb(N) = Reverse(Bin_q(N))`. -/
def binPadLsb (q N : ℕ) : List Bool := (binPad q N).reverse

/-- A code `Code : ℤ₊ → {0,1}*` is prefix-free: for distinct `M ≠ N`, `Code(M)` is not a
prefix of `Code(N)`. Taking `M ≠ N` with equal codewords is also excluded. -/
def IsPrefixFree (c : ℕ+ → List Bool) : Prop :=
  ∀ M N : ℕ+, M ≠ N → ¬ (c M <+: c N)

/-- `w` is a prefix of `Bin_lsb(t) ∥ 0^∞`: the `i`-th bit of `w` is the `i`-th least
significant bit of `t` (bits beyond the top bit of `t` are `0`). -/
def IsPrefixOfLsb (w : List Bool) (t : ℕ) : Prop :=
  ∀ i (hi : i < w.length), w[i] = t.testBit i

/-- `Int(t)` (§2.2): the unique positive `N` whose codeword is a prefix of
`Bin_lsb(t) ∥ 0^∞`, or `0` if there is no such integer. -/
noncomputable def decode (c : ℕ+ → List Bool) (t : ℕ) : ℕ := by
  classical
  exact if h : ∃! N : ℕ+, IsPrefixOfLsb (c N) t then ((h.exists.choose : ℕ+) : ℕ) else 0

/-- `(seq t)_{t ∈ J, t ≥ 1}` contains `1, 2, …, N` as a subsequence: there are strictly
increasing positive times `τ₁ < ⋯ < τ_N` in `J` with `seq τᵢ = i`. -/
def ContainsInitialSegment (seq : ℕ → ℕ) (J : Set ℕ) (N : ℕ) : Prop :=
  ∃ τ : Fin N → ℕ, StrictMono τ ∧ ∀ i, τ i ∈ J ∧ 1 ≤ τ i ∧ seq (τ i) = (i : ℕ) + 1

/-- The aligned interval `[j(2P), (j+1)(2P))`. -/
def alignedInterval (P j : ℕ) : Set ℕ := Set.Ico (j * (2 * P)) ((j + 1) * (2 * P))

/-- Monotonicity (Theorems 2.1, 2.2, B.2): for every `N` and every aligned interval `J` of
length `2P`, `P = 2^{|Code(N)|}`, the sequence `(Int(t))_{t ∈ J ∩ ℤ₊}` contains
`1, …, N` as a subsequence. -/
def HasMonotonicity (c : ℕ+ → List Bool) : Prop :=
  ∀ (N : ℕ+) (j : ℕ),
    ContainsInitialSegment (decode c) (alignedInterval (2 ^ (c N).length) j) N

/-- Prefix property: `Int(t) ≥ 1` for every positive `t`. -/
def HasPrefixProperty (c : ℕ+ → List Bool) : Prop :=
  ∀ t : ℕ, 1 ≤ t → 1 ≤ decode c t

/-! ### Elias ω-code and MonoElias (§2.1, Appendix A.1) -/

/-- Blocks `Bin(N_k) ∥ ⋯ ∥ Bin(N_1)` of the Elias ω-code, `N_1 = N`, `N_i = ⌊log₂ N_{i-1}⌋`,
stopping at the first `N_k ∈ {2,3}`. Used for `N ≥ 2`. -/
def eliasBlocks (N : ℕ) : List Bool :=
  if _h : N ≤ 3 then bin N else eliasBlocks (Nat.log 2 N) ++ bin N
decreasing_by exact Nat.log_lt_self 2 (by omega)

/-- `Elias(1) = 0`, `Elias(N) = Bin(N_k) ∥ ⋯ ∥ Bin(N_1) ∥ 0`. -/
def elias (N : ℕ+) : List Bool :=
  if (N : ℕ) = 1 then [false] else eliasBlocks N ++ [false]

/-- `RBin(N) = 1 ∥ Reverse(s)` where `Bin(N) = 1 ∥ s` (`N ≥ 1`). -/
def rbin (N : ℕ) : List Bool := true :: (bin N).tail.reverse

/-- The blocks `RBin(N_k) ∥ ⋯ ∥ RBin(N_1)` of MonoElias. -/
def monoEliasBlocks (N : ℕ) : List Bool :=
  if _h : N ≤ 3 then rbin N else monoEliasBlocks (Nat.log 2 N) ++ rbin N
decreasing_by exact Nat.log_lt_self 2 (by omega)

/-- `MonoElias(1) = 0`, `MonoElias(N) = RBin(N_k) ∥ ⋯ ∥ RBin(N_1) ∥ 0` (Appendix A.1). -/
def monoElias (N : ℕ+) : List Bool :=
  if (N : ℕ) = 1 then [false] else monoEliasBlocks N ++ [false]

/-! ### SmoothCode, SmoothCode_lsb and SmoothMonoCode (Appendix B) -/

/-- The group index `gr(N)`: `G₀ = {1,2}`, `G₁ = {3}` and, for `r ≥ 2`,
`G_r = [2^r − 2^{r−2} + 1, 2^r + 2^{r−1}] = (3·2^{r−2}, 3·2^{r−1}]`; for `N ≥ 4` this is
`r = ⌊log₂ ⌊(N−1)/3⌋⌋ + 2`. -/
def groupIndex (N : ℕ) : ℕ :=
  if N ≤ 2 then 0 else if N = 3 then 1 else Nat.log 2 ((N - 1) / 3) + 2

/-- `Enc(N)` for `N ≥ 4`, `r = gr(N)`: `0 ∥ Bin_{r−2}(N − [2^r − 2^{r−2} + 1])` on
`G⁰_r = [2^r − 2^{r−2} + 1, 2^r]` and `1 ∥ Bin_{r−1}(N − [2^r + 1])` on
`G¹_r = [2^r + 1, 2^r + 2^{r−1}]`; `Enc(3) = ε`. With `lsb = true` the padded offset is
replaced by its reversal `Bin^q_lsb` (the code `SmoothCode_lsb`). -/
def enc (lsb : Bool) (N : ℕ) : List Bool :=
  let r := groupIndex N
  let pad : ℕ → ℕ → List Bool := if lsb then binPadLsb else binPad
  if N ≤ 3 then []
  else if N ≤ 2 ^ r then false :: pad (r - 2) (N - (2 ^ r - 2 ^ (r - 2) + 1))
  else true :: pad (r - 1) (N - (2 ^ r + 1))

/-- `SmoothCode(1) = 00`, `SmoothCode(2) = 01`,
`SmoothCode(N) = 1 ∥ SmoothCode(gr(N)) ∥ Enc(N)` for `N ≥ 3` (with `lsb = false`);
`lsb = true` gives `SmoothCode_lsb`. The value at `0` is unused. -/
def smoothCodeWith (lsb : Bool) (N : ℕ) : List Bool :=
  if _h0 : N = 0 then []
  else if _h1 : N = 1 then [false, false]
  else if _h2 : N = 2 then [false, true]
  else true :: (smoothCodeWith lsb (groupIndex N) ++ enc lsb N)
decreasing_by
  unfold groupIndex
  split_ifs with ha hb
  · omega
  · omega
  · have hx : (N - 1) / 3 ≠ 0 := by omega
    have := Nat.log_lt_self 2 hx
    omega

/-- `SmoothCode` on `ℕ` (meaningful for `N ≥ 1`). -/
def smoothCodeNat (N : ℕ) : List Bool := smoothCodeWith false N

/-- `SmoothCode_lsb` on `ℕ` (meaningful for `N ≥ 1`). -/
def smoothCodeLsbNat (N : ℕ) : List Bool := smoothCodeWith true N

/-- `SmoothCode : ℤ₊ → {0,1}*` (Appendix B). -/
def smoothCode (N : ℕ+) : List Bool := smoothCodeNat N

/-- `SmoothMonoCode` (Appendix B.0.1). `H₁ = {1,2,3,4}`, `H_r = {2^r+1, …, 2^{r+1}}` for
`r ≥ 2`, `d_N = |SmoothCode(N)|`. It equals `SmoothCode_lsb(N)` when `N ≤ 4` or when
`N ∈ H_r` with `d_r < d_{r+1}`. Otherwise, writing `N = 2^r + 1 + (2x + b)`,
`SmoothMonoCode(2^r+1+2x) = 1 ∥ SmoothCode_lsb(r+1) ∥ 0 ∥ Bin^{r−1}_lsb(x)` and
`SmoothMonoCode(2^r+2+2x) = 1 ∥ SmoothCode_lsb(r) ∥ 1 ∥ Bin^{r−1}_lsb(x)`. -/
def smoothMonoCodeNat (N : ℕ) : List Bool :=
  if N ≤ 4 then smoothCodeLsbNat N
  else
    let r := Nat.log 2 (N - 1)
    if (smoothCodeNat r).length < (smoothCodeNat (r + 1)).length then smoothCodeLsbNat N
    else
      let o := N - (2 ^ r + 1)
      if o % 2 = 0 then
        true :: (smoothCodeLsbNat (r + 1) ++ false :: binPadLsb (r - 1) (o / 2))
      else
        true :: (smoothCodeLsbNat r ++ true :: binPadLsb (r - 1) (o / 2))

/-- `SmoothMonoCode : ℤ₊ → {0,1}*`. -/
def smoothMonoCode (N : ℕ+) : List Bool := smoothMonoCodeNat N

/-! ### Iterated logarithms (Theorem 3.1) -/

/-- `log* N = min{ℓ : log^{(ℓ)} N < 2}` (log base 2). Computed with integer floors, which
does not change the count since `⌊log₂ ⌊x⌋⌋ = ⌊log₂ x⌋` for `x ≥ 1`. -/
def logStar (N : ℕ) : ℕ :=
  if _h : N < 2 then 0 else logStar (Nat.log 2 N) + 1
decreasing_by exact Nat.log_lt_self 2 (by omega)

/-- `log^{(h)} x`, the `h`-fold iterate of `log₂` on the reals. -/
noncomputable def iterLog (h : ℕ) (x : ℝ) : ℝ := (Real.logb 2)^[h] x

/-- `log n · log log n · log log log n ⋯`: the product of `log^{(h)} n` over
`1 ≤ h ≤ log* n` (an empty product is `1`). -/
noncomputable def iterLogProduct (n : ℕ) : ℝ :=
  ∏ h ∈ Finset.Icc 1 (logStar n), iterLog h n

/-- `⌈log₂(n+1)⌉` as a positive integer. -/
def ceilLog (n : ℕ+) : ℕ+ :=
  ⟨Nat.clog 2 ((n : ℕ) + 1), Nat.clog_pos one_lt_two (by have := n.pos; omega)⟩

end EliasGlobalClock.LowerBound.Supplement


