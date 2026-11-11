-- Prove2me | Definitions.Def_DQIShattered_Ensemble
-- name    : DQIShattered_Ensemble
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:27:41.646124+00:00
-- url     : https://prove2.me/theorems/09120782-9966-4dff-a298-e88d3f358c51
-- title:
--   The Erdős–Rényi ensemble $\mathbb G_{\mathrm{ER}}(N,k,D)$
-- statement:
--   Fix integers $N\ge k\ge 2$ and a real $D>0$, and let $V=\{1,\dots,N\}$. The ensemble $\mathbb G_{\mathrm{ER}}(N,k,D)$ is built as follows.
--
--   1. Set $M=\lfloor ND/k\rfloor$.
--   2. Draw hyperedges $e_1,\dots,e_M$ independently and uniformly from the $k$-element subsets of $V$, with replacement.
--   3. The **incidence matrix** $B\in\mathbb F_2^{M\times N}$ has row $i$ equal to the indicator of $e_i$.
--   4. Draw couplings $J\in\{+1,-1\}^M$ i.i.d. uniform (Rademacher), independent of the hyperedges. They are written $J_i=(-1)^{v_i}$ with $v\in\mathbb F_2^M$ uniform.
--
--   The definition provides the probability of an event of $B$, and of an event of $(B,J)$, under this law. For example,
--
--   $$\mathbb P[(B,J)\in\mathcal E]=\frac{\#\{(e,v)\in\binom{V}{k}^M\times\mathbb F_2^M:\ (B(e),v)\in\mathcal E\}}{\binom Nk^M\,2^M}.$$
--
--   This is the random instance of every probabilistic statement of the mission.
--
--   **Formalization Note** The probabilities are finite uniform averages. For $N<k$ no $k$-subset exists and the value is $0$, so every statement of the mission assumes $N\ge k$. The bijection $v_i=(1-J_i)/2$ is (3.5).
-- source:
--   Zhou, Shutty, Sellke, Jordan, Gibbs Sampling in the Shattered Phase by Decoded Quantum Interferometry, arXiv:2609.40345 (held version sha256 0c7f6fdf…), Definition 2.5, p.6; (3.5), p.10

import Mathlib

namespace DQIShattered

open Finset

/-- A `k`-element subset of the vertex set `V = {1, …, N}` (here `Fin N`): one hyperedge. -/
abbrev KSet (N k : ℕ) := {s : Finset (Fin N) // s.card = k}

/-- **The number of hyperedges** `M = ⌊ND/k⌋` of the Erdős–Rényi ensemble `𝔾_ER(N, k, D)` (Zhou, Shutty,
Sellke, Jordan, arXiv:2609.40345, held version sha256 0c7f6fdf…, Definition 2.5, p.6). -/
noncomputable def Mrows (N k : ℕ) (D : ℝ) : ℕ := ⌊(N : ℝ) * D / k⌋₊

/-- **The incidence matrix** `B ∈ 𝔽₂^{M×N}` of a hyperedge list `E = (e₁, …, e_M)`: row `i` has ones exactly
at the `k` positions of `eᵢ` (Definition 2.5, p.6). -/
def incidence {N k M : ℕ} (E : Fin M → KSet N k) : Matrix (Fin M) (Fin N) (ZMod 2) :=
  fun i j => if j ∈ (E i).1 then 1 else 0

open Classical in
/-- **The probability, under `𝔾_ER(N, k, D)`, that the incidence matrix `B` has property `P`**
(Definition 2.5, p.6): the `M = ⌊ND/k⌋` hyperedges are i.i.d. uniform among the `k`-subsets of `V`
(with replacement), so every hyperedge list `E ∈ (V choose k)^M` has probability `C(N,k)^{−M}`.

**Formalization Note** A finite uniform average; no measure theory is involved. For `N < k` there is no
`k`-subset and the value is `0` (the paper assumes `N ≥ k`; every statement of the mission does). -/
noncomputable def erProbB (N k : ℕ) (D : ℝ)
    (P : Matrix (Fin (Mrows N k D)) (Fin N) (ZMod 2) → Prop) : ℝ :=
  (∑ E : Fin (Mrows N k D) → KSet N k, if P (incidence E) then (1 : ℝ) else 0) /
    (Fintype.card (Fin (Mrows N k D) → KSet N k) : ℝ)

open Classical in
/-- **The probability, under `(B, J) ∼ 𝔾_ER(N, k, D)`, of an event of `(B, J)`** (Definition 2.5, p.6). The
couplings `J = (J₁, …, J_M)` are i.i.d. uniform Rademacher, independent of the hyperedges; they are written
`Jᵢ = (−1)^{vᵢ}` with `v ∈ 𝔽₂^M` uniform, which is the bijection `vᵢ = (1 − Jᵢ)/2` of (3.5), p.10.

**Formalization Note** `P B v` is the event at incidence matrix `B` and sign vector `v`. The value is
`(C(N,k)^M 2^M)^{−1}` times the number of `(E, v)` in the event. -/
noncomputable def erProb (N k : ℕ) (D : ℝ)
    (P : Matrix (Fin (Mrows N k D)) (Fin N) (ZMod 2) → (Fin (Mrows N k D) → ZMod 2) → Prop) : ℝ :=
  (∑ E : Fin (Mrows N k D) → KSet N k, ∑ v : Fin (Mrows N k D) → ZMod 2,
      if P (incidence E) v then (1 : ℝ) else 0) /
    ((Fintype.card (Fin (Mrows N k D) → KSet N k) : ℝ) * 2 ^ Mrows N k D)

end DQIShattered


