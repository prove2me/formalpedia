-- Prove2me | Definitions.Def_ThreshRankBIS_countInput
-- name    : ThreshRankBIS_countInput
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T06:00:29.969004+00:00
-- url     : https://prove2.me/theorems/ba671f92-3b06-49ac-a86c-62b9d116dd7b
-- title:
--   Encodings: input $(G,\lambda,\epsilon)$, bit length $B$, success event and probability
-- statement:
--   The input of the counting and sampling problems is the triple $(G,\lambda,\epsilon)$: the graph as $n$ in binary followed by the $n^2$ biadjacency bits in row-major order, and the rationals $\lambda,\epsilon$ in the platform's binary encoding (sign, numerator, denominator), combined by the platform's self-delimiting tuple code. $B$ is the combined length of the codes of $\lambda$ and $\epsilon$.
--
--   A machine output $s$ is a **relative $\epsilon$-approximation** to $Z>0$ if $s$ is the code of a rational $\hat Z$ with
--
--   $$
--   e^{-\epsilon}Z\le\hat Z\le e^{\epsilon}Z .
--   $$
--
--   The **success probability** of a randomized machine on input $x$ is the fraction of coin strings $\omega\in\{0,1\}^{\mathrm{coins}(x)}$ on which the output satisfies the success event. The module also fixes the $2n$-bit indicator encoding of a vertex set, its decoder for sampler outputs (strings of the wrong length decode to "no valid output"), the encoding of a list of vertex sets, and the input $(G,D_0,b,R)$ of the recovery procedure of Lemma 7.
--
--   **Formalization Note** The rational code is injective, so the success event has no decoder slack. $B$ is within a constant factor of any other binary encoding length of $\lambda,\epsilon$, which the polynomial factor of every running time absorbs.
-- source:
--   Carlson–Kolla, Efficient Algorithms for Approximately Counting Bipartite Independent Sets in Low Threshold Rank Graphs, STOC 2027 submission (manuscript sha256 9b315e04…), §1.1, p.3; Lemma 7, p.10

import Mathlib
import Definitions.Def_CritWinSpin_RandMachine
import Definitions.Def_QAlgorithms_ClassicalRationalEncoding
import Definitions.Def_ThreshRankBIS_IsRegular
set_option autoImplicit false

namespace ThreshRankBIS

open Finset QAlgorithms.Complexity QAlgorithms.LocalHamiltonian QuantumPRC

/-- The encoding of the graph: `n` in self-delimiting binary, then the `n × n` biadjacency bits
`E x y` in row-major order (`x` the row). -/
def encGraph (n : ℕ) (E : Fin n → Fin n → Bool) : Str :=
  encBin n ++ List.ofFn (fun i : Fin (n * n) => E (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2)

/-- The `2n`-bit indicator string of a vertex set `S ⊆ V(G)`, in the order `x_1, …, x_n,
y_1, …, y_n` (`finSumFinEquiv`). -/
def encSet (n : ℕ) (S : Finset (V n)) : Str :=
  List.ofFn (fun i : Fin (n + n) => decide (finSumFinEquiv.symm i ∈ S))

/-- Decoding a sampler output: a string of length `2n` is read as the indicator string of a
vertex set; any other string decodes to `none`. -/
def decSet (n : ℕ) (s : Str) : Option (Finset (V n)) :=
  if s.length = n + n then
    some (univ.filter (fun v => s[(finSumFinEquiv v : ℕ)]? = some true))
  else none

/-- A list of vertex sets: its length in binary, then each set's indicator string. -/
def encSetList (n : ℕ) (L : List (Finset (V n))) : Str :=
  encBin L.length ++ (L.map (encSet n)).flatten

/-- **The input string of the counting and sampling problems** (§1.1, p.3): the code of the
triple (graph `G`, fugacity `λ`, accuracy `ε`), `tupleCode [encGraph n E, encRat λ, encRat ε]`.

Source: Carlson–Kolla, STOC 2027 submission (manuscript sha256 9b315e04…), §1.1, p.3 ("The
numerical inputs λ and ϵ are rational, and B denotes their combined binary encoding length");
Lemma 7, p.10 (the recovery input).

The module also defines the graph and vertex-set encodings, the recovery input
`(G, D_0, b, R)` of Lemma 7, `B = bitLen λ ε`, the success event of a relative
`ε`-approximation, and the success probability of a randomized machine.

**Formalization Note.** `λ` and `ε` are encoded with the platform's `encRat` (sign, numerator
and denominator in self-delimiting binary) and `B` is the sum of the two code lengths, which is
the paper's "combined binary encoding length" up to a constant factor. A count output must be
exactly the string `encRat Ẑ` of a rational `Ẑ`; `encRat` is injective, so there is no decoder
slack. -/
def countInput (n : ℕ) (E : Fin n → Fin n → Bool) (lam ε : ℚ) : Str :=
  tupleCode [encGraph n E, encRat lam, encRat ε]

/-- The input `(G, D_0, b, R)` of the recovery procedure of Lemma 7 (p.10). -/
def recoveryInput (n : ℕ) (E : Fin n → Fin n → Bool) (D0 : Finset (V n)) (b R : ℕ) : Str :=
  tupleCode [encGraph n E, encSet n D0, encBin b, encBin R]

/-- `B`, the combined binary encoding length of `λ` and `ε` (p.3). -/
def bitLen (lam ε : ℚ) : ℕ := (encRat lam).length + (encRat ε).length

/-- The output string `s` is a relative `ε`-approximation to `Z > 0` (p.3): `s = encRat Ẑ` for a
rational `Ẑ` with `e^{−ε} Z ≤ Ẑ ≤ e^{ε} Z`. -/
def goodCount (Z ε : ℝ) (s : Str) : Prop :=
  ∃ Zh : ℚ, s = encRat Zh ∧ Real.exp (-ε) * Z ≤ (Zh : ℝ) ∧ (Zh : ℝ) ≤ Real.exp ε * Z

/-- The probability, over the uniform coin string `ω ∈ {0,1}^{coins x}`, that the output of the
randomized machine `M` on input `x` satisfies `good`. -/
noncomputable def successProb (M : CritWinSpin.RandMachine) (x : Str) (good : Str → Prop) : ℝ := by
  classical
  exact (1 / (2 : ℝ) ^ M.coins x) *
    ∑ ω : Fin (M.coins x) → Bool, if good (M.run (tupleCode [List.ofFn ω, x])) then (1 : ℝ) else 0

end ThreshRankBIS


