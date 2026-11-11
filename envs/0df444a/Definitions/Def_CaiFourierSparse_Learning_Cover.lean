-- Prove2me | Definitions.Def_CaiFourierSparse_Learning_Cover
-- name    : CaiFourierSparse_Learning_Cover
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T15:15:21.405911+00:00
-- url     : https://prove2.me/theorems/5bb149b7-3b46-4dad-971d-fe7ca47231c8
-- title:
--   Output formats and the post-processing of Algorithm 3 (FrequenciesCover)
-- statement:
--   A Haar–Fourier expansion $\tilde x=\sum_H\beta_H\varphi_H$ is output as the exponents $b,a$ of $N=2^b$, $K=2^a$, the number of terms, and for each term the index of $H$ and $\beta_H$ (`encHF`, `levCode`); intervals and frequency lists have their own encodings (`encIv`, `encFreqs`). `hfSum` is the function $\tilde x$, and `ValidHF k F b a terms` says the expansion is in the basis $\mathcal B$ of Definition 4.1 for $k$ and $F$ ($K\ge k$, $N\ge2F$, $K\mid2N$, indices in $\mathcal H_{2N}$, each at most once).
--
--   **Algorithm 3** turns each $H$ with $\beta_H\ne0$, whose Haar vector has support $\{a,\dots,b\}$ (`haarStart`), into the region $[a/2-1/4,\,b/2+1/4]$ with energy $m=|\beta_H|^2$ (`regions`); merges regions with nonempty intersection until they are disjoint, adding energies, and sorts them, $\ell_1\le r_1<\ell_2\le\dots$ (`mergeInto`, `mergedRegions`); sets $\tau=c\varepsilon^2\sum_im_i/(k^2\log^{5/2}(k/\varepsilon)\log^2N)$ (`alg3Tau`); and runs the forward scan $R_1=r_1+m_1/\tau$, $R_i=\max\{R_{i-1},r_i\}+m_i/\tau$ and the backward scan $L_{n'}=\ell_{n'}-m_{n'}/\tau$, $L_i=\min\{L_{i+1},\ell_i\}-m_i/\tau$ (`fwdScan`, `bwdScan`), returning $I'=\bigcup_i[L_i,R_i]$ (`coverWithTau` for any $\tau$, `alg3Cover` with the printed $\tau$; `ivUnion` is the union as a set). The printed procedure has no instruction for an empty list of regions; there `coverWithTau` returns no output (`none`).
-- source:
--   Cai, Chen, Shao, Wang (2026), Learning Fourier-Sparse Signals and Multiband Signals, arXiv:2609.02977 (supplied manuscript, SHA-256 0ce139ab…), Theorem 5.1, Algorithm 1 line 17, Algorithm 3, Claim 8.3, Theorem 8.1, printed pp. 24–25, 40–41 (PDF pp. 26–27, 42–43)

import Mathlib
import Definitions.Def_CaiFourierSparse_Learning_HaarFourier

namespace CaiFourierSparse.Learning

open MeasureTheory

/-! # Output formats and the post-processing of Algorithm 3 (`FrequenciesCover`)
(Cai–Chen–Shao–Wang, Theorem 5.1, Algorithm 1 line 17, Algorithm 3, Claim 8.3, Theorem 8.1)

A Haar–Fourier expansion `x̃ = ∑_H β_H φ_H` is output as the exponents `b, a` of `N = 2^b`,
`K = 2^a`, the number of terms, and for each term the index of `H` (block, type code, position)
and the coefficient `β_H`. Algorithm 3 turns the nonzero coefficients into regions
`[a_i/2 - 1/4, b_i/2 + 1/4]` (`{a_i, …, b_i}` the support of the Haar vector) with energies
`m_i = |β_H|²`, merges intersecting regions (adding energies), sorts them, sets
`τ = c ε² ∑_i m_i / (k² log^{5/2}(k/ε) log² N)` and extends them by the forward scan
`R_1 = r_1 + m_1/τ`, `R_i = max{R_{i-1}, r_i} + m_i/τ` and the backward scan
`L_{n'} = ℓ_{n'} - m_{n'}/τ`, `L_i = min{L_{i+1}, ℓ_i} - m_i/τ`, returning
`I' = ⋃_i [L_i, R_i]`. The printed procedure has no instruction for an empty list of regions;
there the cover is `none` (no output). -/

/-- Code of a Haar type in the output: `0` for the scaling type, `m` for the wavelet of
support `2^m`. -/
def levCode : Option ℕ → ℕ
  | none => 0
  | some m => m

/-- Output encoding of a Haar–Fourier expansion with `N = 2^b`, `K = 2^a`. -/
def encHF (b a : ℕ) (terms : List (HaarIdx × ℂ)) : List ℂ :=
  [(b : ℂ), (a : ℂ), (terms.length : ℂ)] ++
    terms.flatMap fun p => [(p.1.blk : ℂ), (levCode p.1.lev : ℂ), (p.1.pos : ℂ), p.2]

/-- Output encoding of a finite list of intervals `[L_i, R_i]`. -/
def encIv (I : List (ℝ × ℝ)) : List ℂ :=
  [(I.length : ℂ)] ++ I.flatMap fun p => [(p.1 : ℂ), (p.2 : ℂ)]

/-- Output encoding of a finite list of frequencies. -/
def encFreqs (L : List ℝ) : List ℂ := [(L.length : ℂ)] ++ L.map fun f => (f : ℂ)

/-- The expansion `x̃(t) = ∑_{(H, β_H)} β_H φ_H(t)`. -/
noncomputable def hfSum (b a : ℕ) (terms : List (HaarIdx × ℂ)) (t : ℝ) : ℂ :=
  (terms.map fun p => p.2 * phiH b a p.1 t).sum

/-- The expansion is in the Haar–Fourier basis `B` of Definition 4.1 for the sparsity `k` and
bandlimit `F`: `K = 2^a ≥ k`, `N = 2^b ≥ 2F`, `K ∣ 2N`, every index is a vector of `H_{2N}`, and
each basis vector appears at most once. -/
def ValidHF (k : ℕ) (F : ℝ) (b a : ℕ) (terms : List (HaarIdx × ℂ)) : Prop :=
  k ≤ 2 ^ a ∧ 2 * F ≤ 2 ^ b ∧ a ≤ b + 1 ∧ (∀ p ∈ terms, p.1 ∈ haarIdxSet b a) ∧
    (terms.map Prod.fst).Nodup

/-- First index of the support of the Haar vector `H` (`N = 2^b`, `K = 2^a`). -/
def haarStart (b a : ℕ) (H : HaarIdx) : ℤ :=
  -(2 ^ b : ℤ) + (2 ^ a : ℤ) * H.blk + (haarSupp a H : ℤ) * H.pos

/-- Algorithm 3, line 3: for each `H` with `β_H ≠ 0`, the region
`[a/2 - 1/4, b/2 + 1/4]` (`{a, …, b}` the support of `H`) with energy `|β_H|²`. -/
noncomputable def regions (b a : ℕ) (terms : List (HaarIdx × ℂ)) : List (ℝ × ℝ × ℝ) :=
  (terms.filter fun p => p.2 ≠ 0).map fun p =>
    ((haarStart b a p.1 : ℝ) / 2 - 1 / 4,
     ((haarStart b a p.1 + haarSupp a p.1 - 1 : ℤ) : ℝ) / 2 + 1 / 4,
     ‖p.2‖ ^ 2)

/-- Merge step on a list of regions sorted by left endpoint: a region meeting the last merged
region is absorbed into it (its right end is the maximum, its energy the sum). -/
noncomputable def mergeInto (acc : List (ℝ × ℝ × ℝ)) (z : ℝ × ℝ × ℝ) : List (ℝ × ℝ × ℝ) :=
  match acc with
  | [] => [z]
  | top :: rest =>
    if z.1 ≤ top.2.1 then (top.1, max top.2.1 z.2.1, top.2.2 + z.2.2) :: rest else z :: acc

/-- Algorithm 3, lines 4–5: merge regions with nonempty intersections until they are disjoint
(energies add) and sort them, `ℓ_1 ≤ r_1 < ℓ_2 ≤ r_2 < ⋯`. -/
noncomputable def mergedRegions (b a : ℕ) (terms : List (HaarIdx × ℂ)) : List (ℝ × ℝ × ℝ) :=
  (((regions b a terms).mergeSort fun u v => decide (u.1 ≤ v.1)).foldl mergeInto []).reverse

/-- Forward scan: `R_1 = r_1 + m_1/τ`, `R_i = max{R_{i-1}, r_i} + m_i/τ`. -/
noncomputable def fwdScan (τ : ℝ) : Option ℝ → List (ℝ × ℝ × ℝ) → List ℝ
  | _, [] => []
  | prev, z :: zs =>
    let R := (match prev with
      | none => z.2.1
      | some p => max p z.2.1) + z.2.2 / τ
    R :: fwdScan τ (some R) zs

/-- Backward scan, run on the reversed list: `L_{n'} = ℓ_{n'} - m_{n'}/τ`,
`L_i = min{L_{i+1}, ℓ_i} - m_i/τ`. -/
noncomputable def bwdScan (τ : ℝ) : Option ℝ → List (ℝ × ℝ × ℝ) → List ℝ
  | _, [] => []
  | prev, z :: zs =>
    let L := (match prev with
      | none => z.1
      | some p => min p z.1) - z.2.2 / τ
    L :: bwdScan τ (some L) zs

/-- The intervals `[L_i, R_i]` produced by the two scans with threshold `τ` from the merged,
sorted regions; `none` if there is no region (the printed procedure does not cover that case). -/
noncomputable def coverWithTau (b a : ℕ) (terms : List (HaarIdx × ℂ)) (τ : ℝ) :
    Option (List (ℝ × ℝ)) :=
  let R := mergedRegions b a terms
  if R = [] then none
  else some (List.zip (bwdScan τ none R.reverse).reverse (fwdScan τ none R))

/-- Algorithm 3's threshold `τ = c ε² ∑_i m_i / (k² log^{5/2}(k/ε) log² N)`, `N = 2^b`. -/
noncomputable def alg3Tau (c ε : ℝ) (k b : ℕ) (Rg : List (ℝ × ℝ × ℝ)) : ℝ :=
  c * ε ^ 2 * (Rg.map fun z => z.2.2).sum /
    ((k : ℝ) ^ 2 * Real.log ((k : ℝ) / ε) ^ (5 / 2 : ℝ) * Real.log ((2 : ℝ) ^ b) ^ 2)

/-- The output `I'` of Algorithm 3 (`FrequenciesCover`) with constant `c` applied to the
Haar–Fourier expansion returned by `ImproperLearning`. -/
noncomputable def alg3Cover (c ε : ℝ) (k b a : ℕ) (terms : List (HaarIdx × ℂ)) :
    Option (List (ℝ × ℝ)) :=
  coverWithTau b a terms (alg3Tau c ε k b (mergedRegions b a terms))

/-- The set `⋃_i [L_i, R_i]` of a list of intervals. -/
def ivUnion (I : List (ℝ × ℝ)) : Set ℝ := {ξ | ∃ p ∈ I, p.1 ≤ ξ ∧ ξ ≤ p.2}

end CaiFourierSparse.Learning


