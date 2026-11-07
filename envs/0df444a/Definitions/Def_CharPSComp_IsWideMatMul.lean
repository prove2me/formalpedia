-- Prove2me | Definitions.Def_CharPSComp_IsWideMatMul
-- name    : CharPSComp_IsWideMatMul
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:08:19.110241+00:00
-- url     : https://prove2.me/theorems/62992b61-86de-423c-88a8-6d8fa2d27cbf
-- title:
--   The conclusion of Lemma 5 as a predicate: construction and execution of the wide matrix product
-- statement:
--   `IsWideMatMul Rmat Build Exec C κ` states the machine part of Lemma 5 for a width threshold $R_{\mathrm{mat}}$, a construction program, an execution program, a constant $C$ and a word exponent $\kappa$. For every admissible $M$, every commutative ring $\mathcal A$ and every $k\ge k_0=2^9$:
--
--   1. **Construction.** `Build`, started with $W[0]=k$, halts within cost $C\,R_{\mathrm{mat}}(k)$, writes at most $C\,R_{\mathrm{mat}}(k)$ cells, keeps every word below $(R_{\mathrm{mat}}(k)+2)^\kappa$ in absolute value, and writes neither cell $0$ nor cell $1$. Its final word memory is the program $S$ of the paper.
--   2. **Execution.** For every $w\ge R_{\mathrm{mat}}(k)$ and all $A\in\mathcal A^{k\times k}$, $B\in\mathcal A^{k\times w}$ (row-major in ring cells $0,\dots,k^2+kw-1$), `Exec`, started on $S$ with $W[1]=w$, halts with $(AB)_{ij}$ in ring cell $k^2+kw+iw+j$, at cost at most $C\,kw\,2^{4\sqrt{\log k}}$, writing at most $Cw$ ring cells outside the $kw$ output cells and at most $Cw$ word cells, never writing an input ring cell, the program $S$ or word cells $0,1$, with every word below $(w+2)^\kappa$.
--
--   Cost counts ring and word operations together, as in the lemma; $\log$ is $\max\{1,\log_2\}$. Lemma 6 takes any data satisfying this predicate as its matrix-product subroutine.
-- source:
--   Zhu, Faster Power Series Composition in Fixed Positive Characteristic, STOC 2027 submission (manuscript sha256 e63e0527228218d0d0b04691cbfb8b92cc1c9c7abddec6972d71bbab231c6361), Lemma 5 and the paragraph before it, p.10 (PDF p.11)

import Mathlib
import Definitions.Def_CharPSComp_run
import Definitions.Def_CharPSComp_Admissible

namespace CharPSComp

universe u

/-- Ring memory holding a `k × k` matrix `A` (row-major, cells `0, …, k² − 1`) followed by a
`k × w` matrix `B` (row-major, cells `k², …, k² + kw − 1`); all other cells are `0`. -/
def matRmem {A : Type*} [Zero A] (k w : ℕ) (Am Bm : ℕ → ℕ → A) (i : ℕ) : A :=
  if i < k * k then Am (i / k) (i % k)
  else if i < k * k + k * w then Bm ((i - k * k) / w) ((i - k * k) % w)
  else 0

/-- The conclusion of Lemma 5 for a width threshold `Rmat`, a construction program `Build`, an
execution program `Exec`, a constant `C` and a word exponent `κ` (Zhu, *Faster Power Series
Composition in Fixed Positive Characteristic*, STOC 2027 submission (manuscript sha256 e63e0527…),
§3.4, p.10, PDF p.11). For every admissible `M`, every commutative ring `A` and every `k ≥ k₀ = 2⁹`:

1. `Build`, started with `W[0] = k`, halts within `C · Rmat(k)` steps, writes at most `C · Rmat(k)`
   cells, keeps every word below `(Rmat(k) + 2)^κ` in absolute value (words of `O(log Rmat(k))`
   bits) and writes neither its input cell `0` nor cell `1` (reserved for the width `w`);
2. for every `w ≥ Rmat(k)` and all `A ∈ A^{k×k}`, `B ∈ A^{k×w}`, `Exec`, started on `Build`'s final
   word memory with `W[1] := w` and with `A, B` in ring memory (`matRmem`), halts with `(AB)_{ij}` in
   ring cell `k² + kw + iw + j`, within `C · k · w · 2^{4√log k}` steps (`log` the paper's
   `max{1, log₂}`), writes at most `C · w` ring cells outside the `kw` output cells and at most
   `C · w` word cells, leaves the program `S` and word cells `0`, `1` unwritten, keeps every word
   below `(w + 2)^κ` (words of `O(log w)` bits) and does not overwrite the ring input.

**Formalization Note** The program `S` of the paper is `Build`'s final word memory; `MatMul` is
`Exec`. Cost counts ring and word operations together, as in the lemma. The page counts only ring
elements for the execution; the two word clauses come from §2.2 (working space counts machine
words) and Appendix A.3 ("reuses the same instructions for the next batch"), and they are what lets
Lemma 6 re-run `Exec` at every evaluation point inside `O(N)` working space. -/
def IsWideMatMul (Rmat : ℕ → ℕ) (Build Exec : Program) (C : ℝ) (κ : ℕ) : Prop :=
  ∀ M : ℕ → ℕ, Admissible M → ∀ (A : Type u) [CommRing A], ∀ k : ℕ, 2 ^ 9 ≤ k →
    ∃ kB : ℕ,
      (run M Build (initState [(k : ℤ)] ([] : List A)) kB).halted = true ∧
      ((run M Build (initState [(k : ℤ)] ([] : List A)) kB).cost : ℝ) ≤ C * Rmat k ∧
      ((run M Build (initState [(k : ℤ)] ([] : List A)) kB).space : ℝ) ≤ C * Rmat k ∧
      (run M Build (initState [(k : ℤ)] ([] : List A)) kB).maxWord < (Rmat k + 2) ^ κ ∧
      (run M Build (initState [(k : ℤ)] ([] : List A)) kB).ReadOnly 2 0 ∧
      ∀ w : ℕ, Rmat k ≤ w → ∀ Am Bm : ℕ → ℕ → A,
        ∃ kE : ℕ,
          let sB := run M Build (initState [(k : ℤ)] ([] : List A)) kB
          let s := run M Exec
            (mkState (Function.update sB.wmem 1 (w : ℤ)) (matRmem k w Am Bm)
              (max sB.maxWord w)) kE
          s.halted = true ∧
          (∀ i < k, ∀ j < w,
            s.rmem (k * k + k * w + i * w + j) = ∑ l ∈ Finset.range k, Am i l * Bm l j) ∧
          (s.cost : ℝ) ≤ C * k * w * 2 ^ (4 * Real.sqrt (lg k)) ∧
          ((s.rWritten.filter
              (fun a => ¬ (k * k + k * w ≤ a ∧ a < k * k + 2 * (k * w)))).card : ℝ) ≤ C * w ∧
          (s.wWritten.card : ℝ) ≤ C * w ∧
          (∀ a ∈ s.wWritten, a ≠ 0 ∧ a ≠ 1 ∧ a ∉ sB.wWritten) ∧
          s.maxWord < (w + 2) ^ κ ∧
          (∀ a ∈ s.rWritten, k * k + k * w ≤ a)

end CharPSComp


