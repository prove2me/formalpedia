-- Prove2me | Definitions.Def_ModFormPIR_Layouts
-- name    : ModFormPIR_Layouts
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:00:20.497205+00:00
-- url     : https://prove2.me/theorems/e15ba1c6-7413-48a1-abaa-f793e6bc5eae
-- title:
--   Memory layouts of Part I and PIR schemes over $\mathbb F_p$
-- statement:
--   This file fixes how the sub-algorithms of Part I receive their inputs on the machine: the dictionary of Theorem 9.4, the prime search of Lemma 9.5 and the coefficient solver of Lemma 9.3. Numbers that may exceed a word are one bit per cell.
--
--   It also defines the hypothesis of Lemma 9.6: a **family of $s$-server schemes over $\mathbb F_p$** on $b^j$ records. For large $n$, every accepting run of the sampler yields $B,p$ with $p$ prime, $p\ge n^4$, $2^B\le p\le2^B(1+\frac1{4n})$, $B,\log p\le\mathrm{polylog}(n)$; and for each $j$ with $1\le j$, $b^j\le n$ there is a private scheme in which each server stores $b^j$ elements of $\mathbb F_p$, computed in $b^j\,\mathrm{polylog}(n)$ time, the user uploads $O(\log n)$ bits, and each server reads and sends back at most $k$ elements in $k\,\mathrm{polylog}(n)$ time.
--
--   **Formalization Note** An element of $\mathbb F_p$ occupies $\mathrm{size}(p)$ bits of the table. Reading $k$ elements is reading at most $k\,\mathrm{size}(p)$ bits.
-- source:
--   Henzinger, Ragavan, Doubly-Efficient Private Information Retrieval from Modular Forms, STOC 2027 submission (manuscript sha256 2442f3db…), Lemma 9.3, p.34; Theorem 9.4, p.35; Lemma 9.5, p.35; Lemma 9.6, p.36

import Mathlib
import Definitions.Def_ModFormPIR_Machine
import Definitions.Def_ModFormPIR_Expansion
import Definitions.Def_ModFormPIR_Scheme

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace ModFormPIR

/-!
# Memory layouts of the sub-algorithms of Part I, and PIR schemes over `𝔽_p`

Henzinger, Ragavan, *Doubly-Efficient Private Information Retrieval from Modular Forms*, STOC 2027
submission (manuscript sha256 2442f3db…), Lemma 9.3, p.34; Theorem 9.4, p.35; Lemma 9.5, p.35; Lemma 9.6, p.36.

**Formalization Note.** Field elements and alphabet symbols exceed a word, so they are one bit per cell. An
element of `𝔽_p` takes `size p` bits, least significant first. A field-valued table is read through `probe`
as these bits, so "reads `k` elements" is "reads at most `k·size p` bits".
-/

/-- The dictionary's encoder input (Theorem 9.4): `N`, `size K`, the bits of `K`, then the `N` symbols. -/
def dictEncInput {N : ℕ} (K : ℕ) (v : Fin N → ℕ) : List ℤ :=
  (N : ℤ) :: (K.size : ℤ) :: bitCells K.size K ++
    (List.ofFn fun i => bitCells K.size (v i)).flatten

/-- The dictionary's decoder input (Theorem 9.4): `N`, `size K`, the bits of `K`, then the position `i`. -/
def dictDecInput (N K i : ℕ) : List ℤ :=
  (N : ℤ) :: (K.size : ℤ) :: bitCells K.size K ++ [(i : ℤ)]

/-- The prime search's input (Lemma 9.5): `n`, `size M`, then the bits of `M`. -/
def primeInput (n M : ℕ) : List ℤ :=
  (n : ℤ) :: (M.size : ℤ) :: bitCells M.size M

/-- The coefficient solver's input (Lemma 9.3): `d`, `size p`, the bits of `p`, the bits of `γ`, the number of
types, the `q` counts of each type, and the membership mask of `𝒜`. -/
def coeffInput (q d p : ℕ) (g : ℕ) (tys : List (ZMod q → ℕ)) (𝒜 : Finset (ZMod q)) : List ℤ :=
  (d : ℤ) :: (p.size : ℤ) :: bitCells p.size p ++ bitCells p.size g ++
    (tys.length : ℤ) ::
      (tys.flatMap fun τ => (List.range q).map fun j => ((τ (j : ZMod q) : ℕ) : ℤ)) ++
      (List.range q).map fun j => if (j : ZMod q) ∈ 𝒜 then 1 else 0

/-- The coefficients the solver leaves in memory (Lemma 9.3): the value for `(w, t)` with `w ∈ 𝒲`, `t ∈ 𝒜` is the
`size p`-bit number at position `(index of the type of w)·q + t`; all other coefficients are `0`. -/
def decodedCoeff {q d : ℕ} [NeZero q] {W : ℕ} (p : ℕ) (st : State W) (tys : List (ZMod q → ℕ))
    (𝒲 : Finset (Fin d → ZMod q)) (𝒜 : Finset (ZMod q)) (w : Fin d → ZMod q) (t : ZMod q) : ZMod p :=
  if w ∈ 𝒲 ∧ t ∈ 𝒜 then
    ((readNat st (-1 - (((tys.idxOf (typeOf w) * q + t.val) * p.size : ℕ) : ℤ)) p.size : ℕ) : ZMod p)
  else 0

/-- A family of `s`-server PIR schemes over `𝔽_p` on databases of `b^j` records (Lemma 9.6): for each `n`, the
public parameters fix `B, p`; `k n` is the bound on the elements a server reads. -/
structure FieldScheme (s b : ℕ) where
  sampler : Program
  prep : Program
  ans : Program
  field : ℕ → List ℕ → ℕ × ℕ
  k : ℕ → ℕ
  query : (n lvl : ℕ) → List ℕ → Fin (b ^ lvl) → PMF (List ℕ × (Fin s → List Bool))
  reconstruct : (n lvl : ℕ) → List ℕ → List ℕ → (Fin s → List Bool) → ℕ
  sampler_noProbe : NoProbe sampler
  prep_noProbe : NoProbe prep
  prep_noCoin : NoCoin prep
  ans_noCoin : NoCoin ans

/-- A database of elements as cells, `w` bits per element. -/
def eltCells {N : ℕ} (w : ℕ) (e : Fin N → ℕ) : List ℤ :=
  (List.ofFn fun i => bitCells w (e i)).flatten

/-- A table of elements as a list of bits, `w` bits per element. -/
def eltTable {N : ℕ} (w : ℕ) (e : Fin N → ℕ) : List Bool :=
  (List.ofFn fun i => (List.range w).map (e i).testBit).flatten

/-- The field preprocessor's input: `n`, level, server, `ℓ`, the parameters, then the database. -/
def fieldPrepInput {N : ℕ} (n lvl j w : ℕ) (params : List ℕ) (DB : Fin N → ℕ) : List ℤ :=
  (n : ℤ) :: (lvl : ℤ) :: (j : ℤ) :: (params.length : ℤ) :: params.map (fun x => (x : ℤ)) ++
    eltCells w DB

/-- The field answerer's input: `n`, level, server, `ℓ`, the parameters, the message length, the message. -/
def fieldAnsInput (n lvl j : ℕ) (params : List ℕ) (msg : List Bool) : List ℤ :=
  (n : ℤ) :: (lvl : ℤ) :: (j : ℤ) :: (params.length : ℤ) :: params.map (fun x => (x : ℤ)) ++
    (msg.length : ℤ) :: msg.map (fun b => if b then 1 else 0)

/-- The hypotheses of Lemma 9.6 at size `n` and width `W`, with constants `C, K` for each `polylog(n)` and
`O(·)`. Every accepting run of the sampler yields `B, p` with `p` prime, `p ≥ n⁴`, `2^B ≤ p ≤ 2^B(1 + 1/(4n))`,
`B, log p ≤ polylog(n)`; and for each level `lvl ∈ [d]` (that is `1 ≤ lvl`, `b^lvl ≤ n`) there is a private
scheme over `b^lvl` records in `𝔽_p`: each server stores `b^lvl` elements of `𝔽_p` computed in
`b^lvl · polylog(n)` time, the user uploads `O(log n)` bits, and each server reads and sends back at most
`k` elements of `𝔽_p`, in `k · polylog(n)` time. -/
def FieldScheme.Realizes {s b : ℕ} (F : FieldScheme s b) (n C K W : ℕ) : Prop :=
  Measurable (acceptCost F.sampler W (samplerInput n)) ∧
  ∫⁻ τ, acceptCost F.sampler W (samplerInput n) τ ∂coinMeasure ≤ ((C * polyL n ^ K : ℕ) : ℝ≥0∞) ∧
  ∀ params : List ℕ, IsSamplerOutput F.sampler W n params →
    let B := (F.field n params).1
    let p := (F.field n params).2
    p.Prime ∧ n ^ 4 ≤ p ∧ 2 ^ B ≤ p ∧ (p : ℝ) ≤ 2 ^ B * (1 + 1 / (4 * (n : ℝ))) ∧
    B ≤ C * polyL n ^ K ∧ Nat.log2 p ≤ C * polyL n ^ K ∧
    ∀ lvl : ℕ, 1 ≤ lvl → b ^ lvl ≤ n →
      (∀ (k : Fin s) (i i' : Fin (b ^ lvl)),
        (F.query n lvl params i).map (fun x => x.2 k) =
          (F.query n lvl params i').map (fun x => x.2 k)) ∧
      ∀ DB : Fin (b ^ lvl) → ℕ, (∀ i, DB i < p) →
        ∃ tables : Fin s → Fin (b ^ lvl) → ℕ,
          (∀ j : Fin s, (∀ i, tables j i < p) ∧
            ∃ (t : ℕ) (st : State W), t ≤ C * b ^ lvl * polyL n ^ K ∧
              Accepts F.prep [] zeroTape (fieldPrepInput n lvl (j : ℕ) p.size params DB) t st ∧
              BitCellsOK st (-1) (b ^ lvl * p.size) ∧
              ∀ i : Fin (b ^ lvl),
                readNat st (-1 - (((i : ℕ) * p.size : ℕ) : ℤ)) p.size = tables j i) ∧
          ∀ i : Fin (b ^ lvl), ∀ x ∈ (F.query n lvl params i).support,
            (∀ j : Fin s, (x.2 j).length ≤ C * polyL n) ∧
            ∃ tr : Fin s → List Bool,
              (∀ j : Fin s, ∃ (t : ℕ) (st : State W), t ≤ C * F.k n * polyL n ^ K ∧
                Accepts F.ans (eltTable p.size (tables j)) zeroTape
                  (fieldAnsInput n lvl (j : ℕ) params (x.2 j)) t st ∧
                tr j = st.trace ∧ (tr j).length ≤ F.k n * p.size) ∧
              F.reconstruct n lvl params x.1 tr = DB i

end ModFormPIR


