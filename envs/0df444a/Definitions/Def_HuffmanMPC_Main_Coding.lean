-- Prove2me | Definitions.Def_HuffmanMPC_Main_Coding
-- name    : HuffmanMPC_Main_Coding
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:23:25.228834+00:00
-- url     : https://prove2.me/theorems/a31a7216-faba-4a05-84d8-ad09292e507c
-- title:
--   §2 and §§3.1, 4 — prefix codes, the optimum $\mu$, depths, bounded-ratio inputs and the threshold stopping state
-- statement:
--   A frequency list $A=(f_1,\dots,f_m)$ is a finite list of natural numbers; equal frequencies are kept as distinct occurrences. A binary code assigns to each index $i$ a finite Boolean word $C(i)$; it is prefix-free when $C(i)$ is not a prefix of $C(j)$ for $i\neq j$ (the published predicate `FuchsThesis.Coding.IsInstantaneous`, which admits the empty word for a single symbol). Its cost is $\sum_i f_i|C(i)|$, and
--   $$\mu(A)=\min_{C\ \text{prefix-free}}\sum_{i=1}^m f_i\,|C(i)|.$$
--   For a text $T$, the frequency list lists, for each distinct symbol, its number of occurrences, and $\mu(T)$ is $\mu$ of that list.
--
--   A depth vector $h$ is optimal for $A$ when some prefix-free code has lengths exactly $h$ and $\sum_i f_ih_i=\mu(A)$. With $\varphi=(1+\sqrt5)/2$, $\alpha=\log_\varphi 2$, $\Delta_\lambda=\lceil\log_\varphi\lambda\rceil+1$,
--   $$\ell=\max\{1,\lceil\log_2 m\rceil-\Delta_\lambda\},\qquad u=\lfloor\log_2 m\rfloor+\Delta_\lambda .$$
--   A bounded-ratio input is a sorted list of $m\ge2$ positive frequencies with $f_m\le\lambda f_2$ (largest over second-smallest).
--
--   The threshold stopping state for a threshold $\tau$ runs Huffman's algorithm (repeatedly merge the two smallest entries, adding their sum to the cost) and stops just before the first merge whose larger operand exceeds $\tau$, or at the final state; it returns the accumulated merge cost and the remaining multiset. It specifies outputs only; it is never used to measure parallel resources.
--
--   **Formalization Note** $\mu$ is the natural-number infimum of the costs of all prefix-free codes; that it is attained and equals the published real infimum `FuchsThesis.Coding.minLength` is the theorem `optimum_attained`. The stopping state is computed with fuel equal to the list length, which suffices since each merge shortens the list.
-- source:
--   Masoud Seddighin, Saeed Seddighin, Massively Parallel Algorithms for Huffman Coding, STOC 2027 submission #377 (October 2026), SHA-256 f63f78c8ea11dfeb34be181f681ce85dc9fd1fa2def1da4a30b231073a8166ba, §2, p. 2 (PDF 3); Eq. (1), p. 3 (PDF 4); §3.1 and §4, pp. 5, 13 (PDF 6, 14); §6, p. 25 (PDF 26)

import Mathlib
import Definitions.Def_FuchsThesis_Coding_IsInstantaneous
import Definitions.Def_FuchsThesis_Coding_expLength
import Definitions.Def_FuchsThesis_Coding_minLength

set_option autoImplicit false

namespace HuffmanMPC.Main

/-- Occurrences are indexed even when their numerical weights coincide. -/
abbrev Frequencies := List ℕ

/-- Integer weighted length, with no normalization of the frequencies. -/
def codeCost (a : Frequencies) (c : Fin a.length → List Bool) : ℕ :=
  ∑ i, a[i] * (c i).length

/-- The independently defined minimum over all prefix-free codes.  The set is
nonempty for every list: distinct fixed-length binary words suffice.  Attainment
and agreement with the real infimum are separate theorem obligations. -/
noncomputable def optimum (a : Frequencies) : ℕ :=
  sInf {v | ∃ c : Fin a.length → List Bool,
    FuchsThesis.Coding.IsInstantaneous c ∧ codeCost a c = v}

/-- Distinct symbols of a finite text, with multiplicities retained in the counts. -/
def textFrequencies (t : List ℕ) : Frequencies :=
  t.dedup.map fun x => t.count x

noncomputable def textOptimum (t : List ℕ) : ℕ := optimum (textFrequencies t)

def Positive (a : Frequencies) : Prop := ∀ x ∈ a, 0 < x

def depthCost (a : Frequencies) (h : Fin a.length → ℕ) : ℕ :=
  ∑ i, a[i] * h i

def Realizes {a : Frequencies} (h : Fin a.length → ℕ) (c : Fin a.length → List Bool) : Prop :=
  FuchsThesis.Coding.IsInstantaneous c ∧ ∀ i, (c i).length = h i

def OptimalDepths (a : Frequencies) (h : Fin a.length → ℕ) : Prop :=
  (∃ c, Realizes h c) ∧ depthCost a h = optimum a

noncomputable def phi : ℝ := (1 + Real.sqrt 5) / 2
noncomputable def alpha : ℝ := Real.logb phi 2
noncomputable def delta (lam : ℝ) : ℕ := ⌈Real.logb phi lam⌉₊ + 1
noncomputable def lowerDepth (m : ℕ) (lam : ℝ) : ℕ :=
  max 1 (⌈Real.logb 2 (m : ℝ)⌉₊ - delta lam)
noncomputable def upperDepth (m : ℕ) (lam : ℝ) : ℕ :=
  ⌊Real.logb 2 (m : ℝ)⌋₊ + delta lam

/-- Sorted positive input and the ratio to the second-smallest occurrence. -/
def BoundedRatio (a : Frequencies) (lam : ℝ) : Prop :=
  2 ≤ a.length ∧ Positive a ∧ a.Pairwise (· ≤ ·) ∧
    (a.getLast! : ℝ) ≤ lam * (a.getD 1 0 : ℝ)

/-- A deterministic sequential specification of threshold stopping, used only to
specify the required output, never to define the MPC resources. -/
def thresholdRun : ℕ → ℕ → Frequencies → ℕ × Frequencies
  | 0, _, a => (0, a.mergeSort (· ≤ ·))
  | fuel + 1, tau, a =>
    match a.mergeSort (· ≤ ·) with
    | x :: y :: xs =>
      if y ≤ tau then
        let r := thresholdRun fuel tau ((x + y) :: xs)
        (x + y + r.1, r.2)
      else (0, x :: y :: xs)
    | xs => (0, xs)

def stoppingState (a : Frequencies) (tau : ℕ) : ℕ × Frequencies :=
  thresholdRun a.length tau a

end HuffmanMPC.Main


