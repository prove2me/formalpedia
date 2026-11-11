-- Prove2me | Definitions.Def_SoSPlantedCSP_Reduction_IO
-- name    : SoSPlantedCSP_Reduction_IO
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:39:19.57269+00:00
-- url     : https://prove2.me/theorems/fe468462-1b4b-4400-b196-9d3d6b232fe8
-- title:
--   Input layouts, output decoding, joint probabilities and the success event
-- statement:
--   This module fixes how the algorithms of the mission receive their inputs and return their outputs.
--
--   1. **Inputs.** A list of reals $L$ is the memory with $L_z$ in cell $z$ for $0\le z<|L|$ and $0$ elsewhere. A k-XOR instance $(\mathcal H,b)$ is written hyperedge by hyperedge: the elements of $H_j$ in increasing order (as reals $0,\dots,n-1$), then $b_j\in\{-1,1\}$. The algorithm of Theorem 3.1 receives $n,m,k,\ell,\hat\varepsilon,\gamma$ followed by the instance; Predict receives $n,m,k,\ell,\hat\varepsilon$ and the instance; Prune receives $n,m,k,\ell,\hat\varepsilon,\gamma$ and the hypergraph only; the sample splitter receives $b,\hat\varepsilon,t$. No input contains the planted vector, the true bias or the noise bits.
--   2. **Outputs.** Outputs are read from the negative cells $-1,-2,\dots$ of the final memory, which start at $0$. For Theorem 3.1, position $j$ is in $\mathcal H_+$, $\mathcal H_-$ or $\mathcal H_0$ according as cell $-(j+1)$ is positive, negative or zero, so the output is always a partition $\mathcal H_+\sqcup\mathcal H_-\sqcup\mathcal H_0$ of the positions. Predict's prediction for position $j$ is $1$ if cell $-(j+1)$ is positive and $-1$ otherwise. Prune's output $\mathcal H'$ is the set of positions whose cell is positive. The splitter's bit $b_i$ is $1$ if cell $-(i+1)$ is positive and $-1$ otherwise.
--   3. **Joint probability.** If $a$ has mass function $\mu$ on a finite set and, independently, $\omega$ is the tape, the probability of $E(a,\omega)$ is $\sum_a\mu(a)\,\mathbb P_{\mathrm{tape}}[E(a,\cdot)]$.
--   4. **Success event of Theorem 3.1.** For an instance $(\mathcal H,b)$ with plant $x^*$, the output succeeds if (1) $b_C=x^*_C$ for every $C\in\mathcal H_+$, (2) $b_C=-x^*_C$ for every $C\in\mathcal H_-$, and (3) $|\mathcal H_0|\le\gamma m$.
--
--   **Formalization Note** Every memory content decodes to an output of the promised shape (total decoding). Tape probabilities of possibly non-measurable events are outer measures; all probability claims of the mission are upper bounds on failure probabilities, which outer measures never make easier.
-- source:
--   Arpon Basu, Andrew D. Lin, Peter Manohar, STOC 2027 submission #544 (October 2026), inputs and outputs of Theorem 3.1, p. 10 (PDF p. 12), and Lemmas 3.5, 3.6, p. 11 (PDF p. 13); success clauses (1)–(3) of Theorem 3.1

import Mathlib
import Definitions.Def_SoSPlantedCSP_Reduction_Machine
import Definitions.Def_SoSPlantedCSP_Reduction_KXOR

open MeasureTheory

namespace SoSPlantedCSP.Reduction

/-!
# Input layouts, output decoding and joint probabilities

Basu–Lin–Manohar, STOC 2027 submission #544 (October 2026): the inputs and outputs of the
algorithms of Theorem 3.1 (printed p. 10, PDF p. 12), Lemma 3.5 and Lemma 3.6 (printed p. 11,
PDF p. 13).

* A list of reals `L` is the memory `z ↦ L[z]` for `0 ≤ z < |L|`, and `0` elsewhere.
* An instance `(ℋ, b)` is written hyperedge by hyperedge: for each position `j` the elements of
  `H j` in increasing order (as the reals `0, …, n − 1`), followed by `b_j ∈ {−1, 1}`
  (`xorBlocks`); a hypergraph alone omits the `b_j` (`hgBlocks`).
* Outputs are read from the negative memory cells `−1, −2, …` of the final memory (initially
  `0`, so an output is only what the program writes), and every memory content is decoded
  (total decoding), so a decoded output always has the promised shape.
* The probability of an event over an independent pair (a finite random object with mass
  function `μ`, the tape) is `∑_a μ(a) · Pr_tape[E a]`. For a non-measurable section the tape
  measure is the outer measure, so upper bounds on such probabilities are never easier.
-/

/-- The memory holding the list `L` in cells `0, …, |L| − 1`, and `0` elsewhere. -/
noncomputable def listMem (L : List ℝ) : ℤ → ℝ :=
  fun z => if 0 ≤ z then L.getD z.toNat 0 else 0

/-- The elements of a set of variables in increasing order, as reals. -/
noncomputable def edgeList {n : ℕ} (C : Finset (Fin n)) : List ℝ :=
  (C.sort (· ≤ ·)).map fun i => ((i : ℕ) : ℝ)

/-- The k-XOR instance `(ℋ, b)`: for each position `j`, the elements of `H j`, then `b_j`. -/
noncomputable def xorBlocks {n m : ℕ} (H : Fin m → Finset (Fin n)) (b : Fin m → ℤˣ) : List ℝ :=
  (List.finRange m).flatMap fun j => edgeList (H j) ++ [((b j : ℤ) : ℝ)]

/-- The hypergraph `ℋ`: for each position `j`, the elements of `H j`. -/
noncomputable def hgBlocks {n m : ℕ} (H : Fin m → Finset (Fin n)) : List ℝ :=
  (List.finRange m).flatMap fun j => edgeList (H j)

/-- Input of the algorithm `𝒜` of Theorem 3.1: `n, m, k, ℓ, ε̂, γ`, then the instance. -/
noncomputable def encMain {n m : ℕ} (k ℓ : ℕ) (εhat γ : ℝ) (H : Fin m → Finset (Fin n))
    (b : Fin m → ℤˣ) : ℤ → ℝ :=
  listMem ([(n : ℝ), (m : ℝ), (k : ℝ), (ℓ : ℝ), εhat, γ] ++ xorBlocks H b)

/-- Input of `Predict` (Lemma 3.5): `n, m, k, ℓ, ε̂`, then the instance. -/
noncomputable def encPredict {n m : ℕ} (k ℓ : ℕ) (εhat : ℝ) (H : Fin m → Finset (Fin n))
    (b : Fin m → ℤˣ) : ℤ → ℝ :=
  listMem ([(n : ℝ), (m : ℝ), (k : ℝ), (ℓ : ℝ), εhat] ++ xorBlocks H b)

/-- Input of `Prune` (Lemma 3.5): `n, m, k, ℓ, ε̂, γ`, then the hypergraph (no right-hand
sides). -/
noncomputable def encPrune {n m : ℕ} (k ℓ : ℕ) (εhat γ : ℝ) (H : Fin m → Finset (Fin n)) :
    ℤ → ℝ :=
  listMem ([(n : ℝ), (m : ℝ), (k : ℝ), (ℓ : ℝ), εhat, γ] ++ hgBlocks H)

/-- Input of the sample-splitting algorithm (Lemma 3.6): the bit `b`, then `ε̂`, then `t`. -/
noncomputable def encSplit (b : ℤˣ) (εhat : ℝ) (t : ℕ) : ℤ → ℝ :=
  listMem [((b : ℤ) : ℝ), εhat, (t : ℝ)]

/-- A sign read from a memory cell: `1` if the cell is positive, `−1` otherwise. -/
noncomputable def signOut (v : ℝ) : ℤˣ :=
  if 0 < v then 1 else -1

open Classical in
/-- Output of `𝒜` (Theorem 3.1), part `ℋ₊`: the positions `j` whose cell `−(j + 1)` is positive. -/
noncomputable def outPlus {m : ℕ} (M : ℤ → ℝ) : Finset (Fin m) :=
  Finset.univ.filter fun j => 0 < M (-((j : ℕ) + 1 : ℤ))

open Classical in
/-- Output of `𝒜`, part `ℋ₋`: the positions `j` whose cell `−(j + 1)` is negative. -/
noncomputable def outMinus {m : ℕ} (M : ℤ → ℝ) : Finset (Fin m) :=
  Finset.univ.filter fun j => M (-((j : ℕ) + 1 : ℤ)) < 0

open Classical in
/-- Output of `𝒜`, part `ℋ₀`: the positions `j` whose cell `−(j + 1)` is zero. Together with
`outPlus` and `outMinus` this is a partition of `Fin m` for every memory. -/
noncomputable def outZero {m : ℕ} (M : ℤ → ℝ) : Finset (Fin m) :=
  Finset.univ.filter fun j => M (-((j : ℕ) + 1 : ℤ)) = 0

/-- Output of `Predict` (Lemma 3.5): the prediction `pred(Ψ, j) ∈ {−1, 1}`, read from cell
`−(j + 1)`. -/
noncomputable def predOut {m : ℕ} (M : ℤ → ℝ) (j : Fin m) : ℤˣ :=
  signOut (M (-((j : ℕ) + 1 : ℤ)))

open Classical in
/-- Output of `Prune` (Lemma 3.5): `ℋ′`, the positions `j` whose cell `−(j + 1)` is positive. -/
noncomputable def pruneOut {m : ℕ} (M : ℤ → ℝ) : Finset (Fin m) :=
  Finset.univ.filter fun j => 0 < M (-((j : ℕ) + 1 : ℤ))

/-- Output of the sample-splitting algorithm (Lemma 3.6): `(b_1, …, b_t)`, bit `i` read from
cell `−(i + 1)`. -/
noncomputable def splitOut (t : ℕ) (M : ℤ → ℝ) : Fin t → ℤˣ :=
  fun i => signOut (M (-((i : ℕ) + 1 : ℤ)))

/-- The probability that `E a ω` holds when `a` has mass function `μ` and, independently, `ω`
is the tape: `∑_a μ(a) · Pr_ω[E a ω]`. -/
noncomputable def jointProb {α : Type*} [Fintype α] (μ : α → ℝ) (E : α → Tape → Prop) : ℝ :=
  ∑ a, μ a * (tapeLaw {ω | E a ω}).toReal

/-- The success event of Theorem 3.1 for the output memory `M` on the instance `(ℋ, b)` with
plant `x*`: (1) `b_C = x*_C` for every `C ∈ ℋ₊`, (2) `b_C = −x*_C` for every `C ∈ ℋ₋`,
(3) `|ℋ₀| ≤ γ m`. -/
def MainSuccess {n m : ℕ} (H : Fin m → Finset (Fin n)) (γ : ℝ) (xstar : Fin n → ℤˣ)
    (b : Fin m → ℤˣ) (M : ℤ → ℝ) : Prop :=
  (∀ j ∈ outPlus (m := m) M, b j = monoSign xstar (H j)) ∧
  (∀ j ∈ outMinus (m := m) M, b j = -monoSign xstar (H j)) ∧
  ((outZero (m := m) M).card : ℝ) ≤ γ * m

end SoSPlantedCSP.Reduction


