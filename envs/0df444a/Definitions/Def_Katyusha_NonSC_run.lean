-- Prove2me | Definitions.Def_Katyusha_NonSC_run
-- name    : Katyusha_NonSC_run
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T06:34:43.80298+00:00
-- url     : https://prove2.me/theorems/3d153437-a576-4678-836d-8badba501bb6
-- title:
--   The Katyusha$^{\mathrm{ns}}$ run: epochs, snapshots $\widetilde x^s$ and the output $\widetilde x^S$ (Algorithm 2)
-- statement:
--   This file defines the iterates of Allen-Zhu's Algorithm 2, $\mathtt{Katyusha}^{\mathrm{ns}}(x_0,S,L)$ with Option I, for an epoch length $m$, as deterministic functions of the random indices drawn. Notation and the inner iteration are those of the companion definition file (composite objective $F$, parameters $\tau_{1,s}=2/(s+4)$, $\tau_2=1/2$, $\alpha_s=1/(3\tau_{1,s}L)$).
--
--   1. **Epoch iterates.** In epoch $s$, from a start pair $(y_{sm},z_{sm})$ and a snapshot $\widetilde x^s$, with indices $i_{sm},\dots,i_{sm+m-1}\in\{1,\dots,n\}$, iteration $k=sm+j$ ($0\le j<m$) applies one inner iteration with weight $\tau_{1,s}$, step $\alpha_s$ and index $i_k$, producing $(y_{sm+j+1},z_{sm+j+1})$.
--   2. **Snapshot.** At the end of epoch $s$,
--   $$\widetilde x^{s+1}=\frac1m\sum_{j=1}^m y_{sm+j}.$$
--   3. **Run.** Initially $y_0=z_0=\widetilde x^0=x_0$; epochs $s=0,1,\dots,S-1$ are applied in order, and the run returns $\widetilde x^S$.
--   4. **Index blocks.** A sequence of $Sm$ indices $(i_0,\dots,i_{Sm-1})$ is split into $S$ blocks of $m$, the index of iteration $k=sm+j$ being $i_{sm+j}$.
--
--   Choosing the $Sm$ indices independently and uniformly from $\{1,\dots,n\}$ gives the randomness of Algorithm 2; the expected value of a quantity of the run is its average over all $n^{Sm}$ index sequences.
--
--   **Formalization Note** Indices are `Fin n`. An epoch is indexed by `s : ℕ` and its indices by `Fin m → Fin n`; `epochIter … j` is $(y_{sm+j},z_{sm+j})$ for $0\le j\le m$, `epochStart … s B` is $(\widetilde x^s,y_{sm},z_{sm})$ given the first $s$ index blocks, `iterYZ` gives the inner iterates of any epoch of a run, and `output` is $\widetilde x^S$. The splitting of `Fin (S*m) → Fin n` into blocks uses Mathlib's `finProdFinEquiv`, a bijection, so the uniform average over `Fin (S*m) → Fin n` (`SAGA.Convex.expectIdx`) is the expectation over i.i.d. uniform indices. The epoch length $m$ is a parameter (the algorithm sets $m=2n$); Option II and the unused input $\sigma$ are not modelled.
-- source:
--   Allen-Zhu, Katyusha: The First Direct Acceleration of Stochastic Gradient Methods, arXiv:1603.05953v6, p. 15, Algorithm 2 (lines 1–17, Option I)

import Mathlib
import Definitions.Def_Katyusha_NonSC_step

namespace Katyusha.NonSC

/-- The inner iterates of epoch `s` of Algorithm 2 (lines 7–14, Option I, p. 15), started from
`yz = (y_{sm}, z_{sm})` with snapshot `x̃ = x̃^s` and the epoch's indices `is j` (`j < m`):
`epochIter … j = (y_{sm+j}, z_{sm+j})` for `j ≤ m` (constant after `j = m`). The epoch uses
`τ_{1,s} = tau1 s` and `α_s = alpha L s`. -/
noncomputable def epochIter {d n m : ℕ}
    (f' : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (P : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (L : ℝ) (s : ℕ)
    (xt : EuclideanSpace ℝ (Fin d))
    (yz : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) (is : Fin m → Fin n) :
    ℕ → EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)
  | 0 => yz
  | j + 1 =>
    if h : j < m then
      innerStep f' P L (tau1 s) (alpha L s) xt (epochIter f' P L s xt yz is j) (is ⟨j, h⟩)
    else epochIter f' P L s xt yz is j

/-- The end of epoch `s`, from the start state `st = (x̃^s, y_{sm}, z_{sm})`: the new state
`(x̃^{s+1}, y_{(s+1)m}, z_{(s+1)m})`, where `x̃^{s+1} = (1/m) ∑_{j=1}^m y_{sm+j}`
(Algorithm 2, line 15, p. 15). -/
noncomputable def epochEnd {d n m : ℕ}
    (f' : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (P : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (L : ℝ) (s : ℕ)
    (st : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))
    (is : Fin m → Fin n) :
    EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) :=
  ((1 / (m : ℝ)) • ∑ j ∈ Finset.range m, (epochIter f' P L s st.1 st.2 is (j + 1)).1,
    epochIter f' P L s st.1 st.2 is m)

/-- The state `(x̃^s, y_{sm}, z_{sm})` of `Katyusha^ns(x₀, S, L)` (Algorithm 2, p. 15) at the start
of epoch `s`, when the indices drawn in epochs `0, …, s-1` are `B 0, …, B (s-1)` (`B t j` is the
index of iteration `k = tm + j`). Initially `y₀ = z₀ = x̃⁰ = x₀` (line 3). -/
noncomputable def epochStart {d n m : ℕ}
    (f' : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (P : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (L : ℝ)
    (x0 : EuclideanSpace ℝ (Fin d)) :
    (s : ℕ) → (Fin s → Fin m → Fin n) →
      EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)
  | 0, _ => (x0, x0, x0)
  | s + 1, B =>
    epochEnd f' P L s (epochStart f' P L x0 s (fun t => B (Fin.castSucc t))) (B (Fin.last s))

/-- The iterates `(y_{sm+j}, z_{sm+j})` (`j ≤ m`) of epoch `s < S` of `Katyusha^ns(x₀, S, L)`, for
the index blocks `B : Fin S → Fin m → Fin n` of the whole run. -/
noncomputable def iterYZ {d n m S : ℕ}
    (f' : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (P : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (L : ℝ)
    (x0 : EuclideanSpace ℝ (Fin d)) (B : Fin S → Fin m → Fin n) (s : Fin S) (j : ℕ) :
    EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) :=
  let st := epochStart f' P L x0 s (fun t => B (Fin.castLE s.2.le t))
  epochIter f' P L s st.1 st.2 (B s) j

/-- The output `x̃^S` of `Katyusha^ns(x₀, S, L)` (Algorithm 2, line 17, p. 15). -/
noncomputable def output {d n m S : ℕ}
    (f' : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (P : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (L : ℝ)
    (x0 : EuclideanSpace ℝ (Fin d)) (B : Fin S → Fin m → Fin n) : EuclideanSpace ℝ (Fin d) :=
  (epochStart f' P L x0 S B).1

/-- Splits a sequence of `S m` indices into `S` blocks of `m`: block `s`, position `j` is the
index of iteration `k = sm + j` (`finProdFinEquiv (s, j) = j + m s`). -/
def blocks {n m S : ℕ} (js : Fin (S * m) → Fin n) : Fin S → Fin m → Fin n :=
  fun s j => js (finProdFinEquiv (s, j))

end Katyusha.NonSC


