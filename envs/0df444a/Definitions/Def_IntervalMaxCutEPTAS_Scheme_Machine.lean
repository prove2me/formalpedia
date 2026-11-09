-- Prove2me | Definitions.Def_IntervalMaxCutEPTAS_Scheme_Machine
-- name    : IntervalMaxCutEPTAS_Scheme_Machine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:19:01.875375+00:00
-- url     : https://prove2.me/theorems/21439a07-9616-43a5-874b-6d50c2ef015a
-- title:
--   Inputs, outputs and output layouts of the costed programs
-- statement:
--   The algorithms are programs of the published costed language `Light` (finite syntax, every executed operation costs one step, runs that exceed the word, space or depth limits do not exist, and two loaded values are compared in constant time).
--
--   1. **Inputs.** Memory cells $0,1,2,\dots$ hold $n$, the numbers $p,q$ with $\varepsilon=p/q$ (Theorem 1.1), or $b$ (Proposition 4.10), followed by the $n$ left and the $n$ right endpoints of an integer representation $J$. Lemma 5.3 instead receives $n,b,p,q$ with $\gamma=p/q$, followed by the fixed structure in the Proposition 4.10 layout; it computes the tables of that supplied structure. The program starts with `call 0 [] 0`.
--   2. **Outputs.** The returned value $a$ (local variable $0$) is a base address. A vertex set $X$ is written as the $0/1$ array $\mathrm{mem}(a+v)=[v\in X]$, below the space limit. The Max-Cut output must satisfy $\mathrm{cut}_G(X)\ge(1-\varepsilon)\mathrm{mc}(G)$ and the Max-Bisection output $|X|=\lfloor n/2\rfloor$, $\mathrm{cut}_G(X)\ge(1-\varepsilon)\mathrm{mb}(G)$, for the **original** representation.
--   3. **Proposition 4.10 layout.** $M$; per vertex the rejected flag, $A_v$, $B_v$, the anchor, the group id; per cell $W(C)$ and bitmaps of $A(C)$, $R(C)$, $O(2C)\setminus O(C)$, $O(2C+1)\setminus O(C)$, for a ranking of the input and a shift with Lemma 4.2's bound.
--   4. **Lemma 5.3 layout.** A directory in heap order contains the absolute base address of each cell's table, determined by the returned address and prefix lengths. It is followed by, for every cell, every boundary vector (mixed-radix index over $R(C)$ sorted by id, digits the positions in $D_g$ sorted ascending) and every $t\le W(C)$, the entry $F_C(x,t)$ as a pair (finite flag, value); then, for every finite root entry, the bitmap of an allowed set attaining it.
--   5. $2^{c\varepsilon^{-2}\log^3(2/\varepsilon)}$ (binary logarithm), $\omega=\lfloor2/\gamma\rfloor+2$ and $\Lambda=\tau(b+1)(2/\sigma+1)^2=2b(b+1)(2^{b+1}+1)^2$.
-- source:
--   Morteza Alimi, Hani Ahmadzadeh, STOC 2027 submission #636 (October 2026), Theorem 1.1, PDF p. 3 (printed p. 2); §3 machine model, PDF p. 14 (printed p. 13); Proposition 4.10, PDF p. 18 (printed p. 17); Lemma 5.3, PDF p. 21 (printed p. 20)

import Mathlib
import Definitions.Def_IntervalMaxCutEPTAS_Scheme_Tables
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntervalMaxCutEPTAS.Scheme

open Classical

/-! # Inputs, outputs and output layouts for the costed `Light` programs

A program receives an integer representation `J` with the endpoint comparisons of the original
representation (`SameComparisons`), written into memory cells `0, 1, 2, …`; it is started by the
statement `call 0 [] 0`, and the result of procedure 0 (local variable 0 of the final state) is the
base address of its output.  Every output layout is a fixed function of the defined objects. -/

/-- The input list for Theorem 1.1: `n, p, q` (with `ε = p/q`), the left endpoints, the right
endpoints. -/
def encode {n : ℕ} (J : Rep ℤ n) (p q : ℕ) : List ℤ :=
  [(n : ℤ), (p : ℤ), (q : ℤ)] ++ List.ofFn J.l ++ List.ofFn J.r

/-- The input list for Proposition 4.10: `n, b`, the left endpoints, the right endpoints. -/
def encodeStruct {n : ℕ} (J : Rep ℤ n) (b : ℕ) : List ℤ :=
  [(n : ℤ), (b : ℤ)] ++ List.ofFn J.l ++ List.ofFn J.r

/-- The start state: empty local frame, the input list in memory cells `0, 1, 2, …`. -/
def start (ws : List ℤ) : Light.State := ⟨Light.frame [], Light.memOf ws⟩

/-- The entry statement: call procedure 0, put its result in local variable 0. -/
def entry : Light.Stmt := .call 0 [] 0

/-- `1` if the proposition holds, `0` otherwise. -/
noncomputable def bit (p : Prop) : ℤ := if p then 1 else 0

/-- The final state writes the vertex set `X` as a 0/1 array of `n` cells starting at the
address `σ.loc 0`, all below the space limit `S`. -/
def Writes (n S : ℕ) (σ : Light.State) (X : Finset (Fin n)) : Prop :=
  0 ≤ σ.loc 0 ∧ (σ.loc 0).toNat + n ≤ S ∧
    ∀ v : Fin n, σ.mem ((σ.loc 0).toNat + v.val) = if v ∈ X then 1 else 0

/-- The final state writes the list `L` in consecutive cells from address `σ.loc 0`, all below the
space limit `S`. -/
def WritesList (S : ℕ) (σ : Light.State) (L : List ℤ) : Prop :=
  0 ≤ σ.loc 0 ∧ (σ.loc 0).toNat + L.length ≤ S ∧
    ∀ i (h : i < L.length), σ.mem ((σ.loc 0).toNat + i) = L[i]

/-- Max-Cut output: a set `X` with `cut_G(X) ≥ (1 − ε) mc(G)`, judged on the original `I`. -/
def ReportsCut {R : Type} [LinearOrder R] {n : ℕ} (I : Rep R n) (ε : ℝ) (S : ℕ)
    (σ : Light.State) : Prop :=
  ∃ X, Writes n S σ X ∧ (1 - ε) * (mc I.graph : ℝ) ≤ (cutCount I.graph X : ℝ)

/-- Max-Bisection output: a set `X` with `|X| = ⌊n/2⌋` and `cut_G(X) ≥ (1 − ε) mb(G)`. -/
def ReportsBis {R : Type} [LinearOrder R] {n : ℕ} (I : Rep R n) (ε : ℝ) (S : ℕ)
    (σ : Light.State) : Prop :=
  ∃ X, Writes n S σ X ∧ X.card = n / 2 ∧ (1 - ε) * (mb I.graph : ℝ) ≤ (cutCount I.graph X : ℝ)

/-- The time function `2^{c ε^{-2} log³(2/ε)}` (binary logarithm). -/
noncomputable def timeF (c : ℕ) (ε : ℝ) : ℝ :=
  (2 : ℝ) ^ ((c : ℝ) * ε⁻¹ ^ 2 * (Real.logb 2 (2 / ε)) ^ 3)

/-! ## The output of Proposition 4.10 -/

variable {n : ℕ} (P : Setup n)

/-- A vertex set as a 0/1 array over `Fin n` (over group ids, for sets of groups). -/
noncomputable def bitmap (X : Finset (Fin n)) : List ℤ := List.ofFn fun v => bit (v ∈ X)

/-- Per vertex `v`, in five arrays of length `n`: the rejected flag; `A_v`; `B_v`; the anchor
(heap index); the group id (least vertex of the group).  The last four are `0` for rejected
vertices. -/
noncomputable def vertexBlock : List ℤ :=
  bitmap (Z P) ++
  List.ofFn (fun v => if Rejected P v then 0 else A P v) ++
  List.ofFn (fun v => if Rejected P v then 0 else B P v) ++
  List.ofFn (fun v => if Rejected P v then 0 else (anchor P v : ℤ)) ++
  List.ofFn (fun v => if Rejected P v then 0 else ((rep P v : ℕ) : ℤ))

/-- Per cell `C`: `W(C)`; the bitmaps (over group ids) of `A(C)` and `R(C)`; and of
`O(2C) \ O(C)` and `O(2C+1) \ O(C)` (two zero arrays if `C` is a leaf). -/
noncomputable def cellBlock (C : ℕ) : List ℤ :=
  [(W P C : ℤ)] ++ bitmap (own P C) ++ bitmap (recent P C) ++
  (if IsLeaf n C then List.replicate (2 * n) 0
   else bitmap (old P (2 * C) \ old P C) ++ bitmap (old P (2 * C + 1) \ old P C))

/-- The whole output of Proposition 4.10: `M`, the vertex arrays, then the blocks of the cells
`1, 2, …, 8M − 1` in heap order. -/
noncomputable def structList : List ℤ :=
  [(bigM n : ℤ)] ++ vertexBlock P ++
  (List.range (8 * bigM n - 1)).flatMap (fun i => cellBlock P (i + 1))

/-- Lemma 5.3 receives the structure fixed at the start of §5, in exactly the layout produced
by Proposition 4.10: `n, b, p, q` (with `γ = p/q`), followed by `structList P`.
The chosen rank representation and shift are input data, not existential output choices. -/
noncomputable def encodeTables (p q : ℕ) : List ℤ :=
  [(n : ℤ), (P.b : ℤ), (p : ℤ), (q : ℤ)] ++ structList P

/-- Proposition 4.10's output, judged on the original representation `I`: there are a rank
representation `ρ` of `I` (§4.1, any admissible tie-break) and a shift `θ < 2M` satisfying the
bound of Lemma 4.2 such that, for `P = (ρ, b, θ)`, `|E(G) \ E(H)| ≤ 28 · 2^{-b} m` and the memory
holds exactly `structList P`. -/
def ReportsStructure {R : Type} [LinearOrder R] (I : Rep R n) (b S : ℕ) (σ : Light.State) :
    Prop :=
  ∃ (ρ : RankRep n) (θ : ℕ), IsRankingOf I ρ ∧ θ < 2 * bigM n ∧ GoodShift ⟨ρ, b, θ⟩ ∧
    2 ^ b * (ρ.graph.edgeFinset \ (H ⟨ρ, b, θ⟩).edgeFinset).card ≤ 28 * ρ.graph.edgeFinset.card ∧
    WritesList S σ (structList ⟨ρ, b, θ⟩)

/-! ## The output of Lemma 5.3 -/

variable (γ : ℝ)

/-- A table entry as two cells: `(0, 0)` for `−∞`, `(1, v)` for a finite value `v`. -/
def entryCells (z : WithBot ℤ) : List ℤ := if z = ⊥ then [0, 0] else [1, z.unbotD 0]

/-- The number of boundary vectors of `C`: `Π_{g ∈ R(C)} |D_g|`. -/
noncomputable def nVec (C : ℕ) : ℕ := ∏ g ∈ recent P C, (Dset P γ g).card

/-- Mixed-radix decoding over the list `gs` of groups: the first group is the least significant
digit; digit `d` of group `g` stands for the `d`-th smallest element of `D_g`. -/
noncomputable def decodeAux : List (Fin n) → ℕ → (Fin n → ℕ)
  | [], _ => fun _ => 0
  | g :: gs, k =>
    fun g' => if g' = g then ((Dset P γ g).sort (· ≤ ·)).getD (k % (Dset P γ g).card) 0
      else decodeAux gs (k / (Dset P γ g).card) g'

/-- The boundary vector of `C` with index `k` (groups of `R(C)` sorted by id). -/
noncomputable def decode (C k : ℕ) : Fin n → ℕ := decodeAux P γ ((recent P C).sort (· ≤ ·)) k

/-- The table of `C`: for `k < nVec C` and `t ≤ W(C)`, the entry `F_C(decode C k, t)` occupies the
two cells at offset `2·(k·(W(C)+1) + t)`. -/
noncomputable def tableBlock (C : ℕ) : List ℤ :=
  (List.range (nVec P γ C)).flatMap fun k =>
    (List.range (W P C + 1)).flatMap fun t => entryCells (F P γ C (decode P γ C k) t)

/-- All tables, for the cells `1, 2, …, 8M − 1` in heap order. -/
noncomputable def tableList : List ℤ :=
  (List.range (8 * bigM n - 1)).flatMap (fun i => tableBlock P γ (i + 1))

/-- The offset of cell `C`'s table from the returned address: one directory cell for every cell
of the hierarchy, followed by the table blocks in heap order. Only valid cells are queried. -/
noncomputable def tableOffset (C : ℕ) : ℕ :=
  (8 * bigM n - 1) + ((List.range (C - 1)).map (fun i => (tableBlock P γ (i + 1)).length)).sum

/-- The directory gives the absolute base address of each table, for cells in heap order.
Its entries are determined by `P`, `γ` and the returned address `base`. -/
noncomputable def tableDirectory (base : ℕ) : List ℤ :=
  (List.range (8 * bigM n - 1)).map (fun i => ((base + tableOffset P γ (i + 1) : ℕ) : ℤ))

/-- The fixed output layout for all tables: their directory followed by the table blocks.
Entry `(x, t)` of `C` is at the directory address plus `2 * (idx(x) * (W(C) + 1) + t)`. -/
noncomputable def tableOutput (base : ℕ) : List ℤ :=
  tableDirectory P γ base ++ tableList P γ

/-- The witness region at address `base`: for every `t ≤ W(root)` with `F_root(t)` finite, the `n`
cells at `base + t·n` hold the 0/1 array of an allowed set `S ⊆ V_root` with `|S| = t` attaining
`F_root(t)` (the root has no recent groups, so its boundary vector is empty). -/
def WitnessesAt (σ : Light.State) (base : ℕ) : Prop :=
  ∀ t ≤ W P 1, F P γ 1 (fun _ => 0) t ≠ ⊥ →
    ∃ S : Finset (Fin n), S ⊆ VC P 1 ∧ Allowed P γ S ∧ S.card = t ∧
      ((val P 1 S (fun _ => 0) : ℤ) : WithBot ℤ) = F P γ 1 (fun _ => 0) t ∧
      ∀ v : Fin n, σ.mem (base + t * n + v.val) = bit (v ∈ S)

/-- Lemma 5.3 computes the tables of the supplied structure `P`, with a directory of their
addresses, followed by the fixed witness region. Neither the structure nor the address map can
be chosen by the output predicate. -/
def ReportsTables (S : ℕ) (σ : Light.State) : Prop :=
  WritesList S σ (tableOutput P γ (σ.loc 0).toNat) ∧
    (σ.loc 0).toNat + (tableOutput P γ (σ.loc 0).toNat).length + (W P 1 + 1) * n ≤ S ∧
    WitnessesAt P γ σ ((σ.loc 0).toNat + (tableOutput P γ (σ.loc 0).toNat).length)

/-- `Λ = τ (b + 1)(2/σ + 1)² = 2b (b + 1)(2^{b+1} + 1)²`. -/
def bigLam (b : ℕ) : ℕ := 2 * b * (b + 1) * (2 ^ (b + 1) + 1) ^ 2

/-- `ω = ⌊2/γ⌋ + 2`. -/
noncomputable def omegaOf (γ : ℝ) : ℕ := ⌊(2 : ℝ) / γ⌋₊ + 2

end IntervalMaxCutEPTAS.Scheme


