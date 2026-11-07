-- Prove2me | Definitions.Def_GaussPart_decode
-- name    : GaussPart_decode
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:28:08.851127+00:00
-- url     : https://prove2.me/theorems/24cdbade-c357-4d0e-bbea-921dfe544edb
-- title:
--   The output format of the partitioning program
-- statement:
--   From an address $a$ of the memory of a halted run, the output is read as: a natural number $N$; then, for each of $N$ cells, a flag $g\in\{0,1\}$ ($g=1$ means the cell is certified, i.e. in $\mathcal G$), a natural number $m$, and $m$ constraint records $(s,w_1,\dots,w_d,b)$ with $s\in\{0,1\}$, meaning $w\cdot x\le b$ ($s=0$) or $w\cdot x<b$ ($s=1$). A count that is not a natural number or a flag outside $\{0,1\}$ makes the output malformed, and a malformed output counts as failure. The program receives $k,q,\sigma,\eta,\delta,\Delta$ in memory from cell $0$ (`goalInput`) and $d$ in pointer $0$; the output starts at the address held in pointer $1$.
--
--   **Formalization Note** The page fixes no output format. Decoding is a specification only: it may test whether a real is a natural number, which the machine itself cannot do.
-- source:
--   Diakonikolas, Iakovidis, Kane, Ma, Gaussian Partitioning for Reliable Learning of Multi-Index Models, arXiv:2611.05264 (sha256 7e0ca6d4…), Theorem 3.1, p.14 (PDF p.16); Algorithm 1, p.19

import Mathlib
import Definitions.Def_GaussMixHH_Machine
import Definitions.Def_GaussPart_Cell

namespace GaussPart

open Classical in
/-- A memory cell read as a natural number; `none` if it does not hold one. -/
noncomputable def readNat (x : ℝ) : Option ℕ :=
  if ∃ n : ℕ, x = n then some ⌊x⌋₊ else none

open Classical in
/-- A memory cell read as a flag: `0` is `false`, `1` is `true`, anything else is `none`. -/
noncomputable def readFlag (x : ℝ) : Option Bool :=
  if x = 0 then some false else if x = 1 then some true else none

/-- The record `(s, w₁, …, w_d, b)` at address `a`, of `d + 2` cells. -/
noncomputable def readConstraint (d : ℕ) (mem : ℤ → ℝ) (a : ℤ) : Option (Constraint d) :=
  (readFlag (mem a)).map fun s =>
    ⟨WithLp.toLp 2 fun i : Fin d => mem (a + 1 + (i : ℕ)), mem (a + 1 + (d : ℤ)), s⟩

/-- `m` consecutive constraint records from address `a`. -/
noncomputable def readConstraints (d : ℕ) (mem : ℤ → ℝ) : ℕ → ℤ → Option (Cell d)
  | 0, _ => some []
  | m + 1, a => do
    let c ← readConstraint d mem a
    let cs ← readConstraints d mem m (a + (d : ℤ) + 2)
    pure (c :: cs)

/-- `N` consecutive flagged cells from address `a`: each is `g, m`, then `m` constraint records. -/
noncomputable def readCells (d : ℕ) (mem : ℤ → ℝ) : ℕ → ℤ → Option (List (Cell d × Bool))
  | 0, _ => some []
  | N + 1, a => do
    let g ← readFlag (mem a)
    let m ← readNat (mem (a + 1))
    let R ← readConstraints d mem m (a + 2)
    let rest ← readCells d mem N (a + 2 + (m : ℤ) * ((d : ℤ) + 2))
    pure ((R, g) :: rest)

/-- The output layout of the program of **Theorem 3.1** (arXiv:2611.05264, sha256 7e0ca6d4…, p.14,
PDF p.16): from address `base` the memory holds `N`, then for each of the `N` cells the flag `g`
(`1` means `R ∈ G`), the count `m`, and `m` records `(s, w₁, …, w_d, b)` meaning `w · x ≤ b`
(`s = 0`) or `w · x < b` (`s = 1`). A malformed count or flag decodes to `none`, which counts as
failure.

**Formalization Note.** This is a specification only: it may use `⌊·⌋₊` and equality on reals,
while the machine has neither. The page does not fix an output format. -/
noncomputable def decode (d : ℕ) (mem : ℤ → ℝ) (base : ℤ) : Option (List (Cell d × Bool)) := do
  let N ← readNat (mem base)
  readCells d mem N (base + 1)

/-- The output of a halted state of the partitioning program: `decode` from pointer `p[1]`. -/
noncomputable def decodeOutput (d : ℕ) (s : GaussMixHH.State) : Option (List (Cell d × Bool)) :=
  decode d s.core.mem (s.core.ptrs 1)

/-- The input of the partitioning program, in memory from cell `0`: `k, q, σ, η, δ, Δ`. The
dimension `d` is in pointer `0` (`GaussMixHH.initState`). -/
noncomputable def goalInput (k : ℕ) (q σ η δ Δ : ℝ) : List ℝ := [(k : ℝ), q, σ, η, δ, Δ]

end GaussPart


