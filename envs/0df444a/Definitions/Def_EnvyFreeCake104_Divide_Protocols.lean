-- Prove2me | Definitions.Def_EnvyFreeCake104_Divide_Protocols
-- name    : EnvyFreeCake104_Divide_Protocols
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:05:49.848525+00:00
-- url     : https://prove2.me/theorems/cbcb0b41-5415-4b03-a0f3-15912214664a
-- title:
--   Algorithms 1–5: Divide, Dominate, Core, Repair and Permute
-- statement:
--   The five protocols of the paper, written as programs over the query model.
--
--   1. **Permute$(N,(P_i))$** (Algorithm 5). For every ordering $i_1,\dots,i_n$ of the agents and $P_{j_1},\dots,P_{j_n}$ of the pieces, in an order chosen by the choice oracle, build the **candidate**: for $r=1,\dots,n$, set $Y_{i_r}\leftarrow P_{j_r}$ and, for $s=1,\dots,r-1$, if $V_{i_s}(Y_{i_r})>V_{i_s}(Y_{i_s})$, remove from $Y_{i_r}$ its smallest prefix worth $V_{i_s}(Y_{i_r})-V_{i_s}(Y_{i_s})$ to $i_s$. Return the first envy-free candidate and its residue $\bigl(\bigcup P_i\bigr)\setminus\bigl(\bigcup Y_i\bigr)$; fail if none is envy-free.
--   2. **Core$(c,N,C)$** (Algorithm 3). Sort $C$'s intervals left to right; the cutter $c$ splits it into $P_1,\dots,P_n$, each worth $V_c(C)/n$ to her, by $n-1$ prefix cuts; return Permute$(N,(P_i))$.
--   3. **Repair$(N,D,R,\varepsilon)$** (Algorithm 4). Let $M=\lceil 1/(3n\varepsilon)\rceil$. Every agent marks, by prefix cuts in $R$'s interval order, the $M-1$ points splitting $R$ into $M$ parts of equal value to her; the **cells** are the parts of $R$ between consecutive marks. Run round robin for $n-1$ rounds in a fixed agent order (chosen once); each agent takes a favourite available cell $Q_{i,r}$. Set $P_i=Q_{i,1}\mathbin{++}\cdots\mathbin{++}Q_{i,n-1}\mathbin{++}D_i$, run $(W,U)\leftarrow$ Permute$(N,(P_i))$, and return $W$ and the residue $(R\cup\bigcup D_i)\setminus\bigcup W_i$.
--   4. **Dominate$(N,C)$** (Algorithm 2). Choose a cutter $c$; start with $X_i=\emptyset$, $R=C$. Repeat: $(Y,U)\leftarrow$ Core$(c,N,R)$; if $(X\oplus Y,U)$ has a dominated group $E$, return $(X\oplus Y,U,E)$. Otherwise choose $\alpha=(4n^2)^{-t}$ with $2\le t\le n+1$, $i^*\ne j^*$ and a permutation $\pi$ of $N$ with (S1) $i^*$ does not dominate $j^*$ in $(X,R)$; (S2) $V_i(Y_{\pi(i)})\ge V_i(Y_i)-\alpha V_i(U)$ for all $i$; (S3) $V_{i^*}(Y_{\pi(j^*)})\le V_{i^*}(Y_{i^*})-4n^2\alpha V_{i^*}(U)$ — failing if none exists. Then $(W,R')\leftarrow$ Repair$(N,(X_i\cup Y_{\pi(i)})_i,U,\alpha)$; while $V_{i^*}(R')>\alpha V_{i^*}(U)$, $(F,R')\leftarrow$ Core$(i^*,N,R')$ and $W\leftarrow W\oplus F$; finally $(X,R)\leftarrow(W,R')$.
--   5. **Divide$(N,C)$** (Algorithm 1). If $|N|=1$ the agent gets $C$. If $|N|=2$, Cut-and-Choose: the first agent prefix-cuts $C$ into two pieces of equal value to her, the second takes a favourite, the first gets the other. Otherwise $(X,R,E)\leftarrow$ Dominate$(N,C)$, $Y\leftarrow$ Divide$(E,R)$, and return $X\oplus Y$ with $Y_i=\emptyset$ for $i\notin E$.
--
--   All values these protocols compare are read from the recorded values and cost no query. Every free choice of the paper goes through the choice oracle.
--
--   **Formalization Note** The `while` loops and the recursion take a fuel argument and fail when fuel runs out; fuel is consumed only when another iteration starts, so a run that succeeds with some fuel is the protocol's unbounded run. $X\oplus Y$ concatenates interval lists ($X_i$ then $Y_i$); the bundle $X_i\cup Y_{\pi(i)}$ passed to Repair lists $X_i$'s intervals first; Repair's residue lists the unpicked cells, then Permute's residue. $(4n^2)^{-t}$ is `alphaOf n t`. `runDivide` runs Divide on the agents $\{0,\dots,n-1\}$ and the cake $[0,1]$ from the initial records.
-- source:
--   Alexandros Psomas, Cutting a Cake For Human Consumption: An Elementary n-agent Cake Cutting Protocol, STOC 2027 submission #104 preprint (arXiv:2610.30370, version not pinned), source.pdf SHA-256 7bef7efb85003ee7fad0a7305c0adb56e7aa074946a39d69e18fd9526572e39f, p.5–15, Algorithms 1 (p.5), 2 (p.6), 3 (p.10), 4 (p.11), 5 (p.13)

import Definitions.Def_EnvyFreeCake104_Divide_Query

set_option autoImplicit false

namespace EnvyFreeCake104.Divide

open scoped Classical

/-! # Algorithms 1–5 of Psomas, *Cutting a Cake For Human Consumption*

Every value a protocol uses (bundles, residues, the domination tests, the Line 7 search) is
read from the recorded values (§1.3) and costs no query. Every free choice of the paper
(Dominate's cutter `c`, the Line 7 tuple, a dominated group, the round-robin order and
tie-breaks, Cut-and-Choose's roles and tie-break, Permute's enumeration order) goes through
`chooseP`, i.e. through the choice oracle. `while` loops and the recursion of Divide take a
`fuel` argument and fail when it runs out; fuel is consumed only when another iteration is
about to start, so a run that succeeds with some fuel succeeds identically with more. -/

variable {ι : Type} [DecidableEq ι]

/-- `true` iff the recorded values make `Y` envy-free among `N`. -/
noncomputable def recEnvyFree (s : Rec ι) (N : Finset ι) (Y : ι → Piece) : Prop :=
  ∀ i ∈ N, ∀ j ∈ N, s.pieceVal i (Y j) ≤ s.pieceVal i (Y i)

/-! ## Permute (Algorithm 5, p.13) -/

/-- Lines 4–8 of Algorithm 5 for one piece: for each earlier agent `i_s` in order, if
`V_{i_s}(Y_{i_r}) > V_{i_s}(Y_{i_s})`, remove from `Y_{i_r}` its smallest prefix worth the
difference to `i_s`. Returns the trimmed piece and the removed parts. -/
noncomputable def trimAgainst (N : Finset ι) (Y : ι → Piece) :
    List ι → Piece → Piece → Proto ι (Piece × Piece)
  | [], piece, removed => return (piece, removed)
  | s :: rest, piece, removed => do
      let st ← get
      let d := st.pieceVal s piece - st.pieceVal s (Y s)
      if 0 < d then
        let p ← prefixCut N s piece d
        trimAgainst N Y rest (suffixList piece p) (removed ++ prefixList piece p)
      else
        trimAgainst N Y rest piece removed

/-- Lines 2–9 of Algorithm 5: processes the pairs `(i_r, j_r)` in order; agent `i_r` starts
with `P_{j_r}` and is trimmed against every earlier agent. Also accumulates the residue. -/
noncomputable def candidateLoop (N : Finset ι) (P : ι → Piece) :
    List (ι × ι) → List ι → (ι → Piece) → Piece → Proto ι ((ι → Piece) × Piece)
  | [], _, Y, R => return (Y, R)
  | (i, j) :: rest, earlier, Y, R => do
      let (piece, rem) ← trimAgainst N Y earlier (P j) []
      candidateLoop N P rest (earlier ++ [i]) (Function.update Y i piece) (R ++ rem)

/-- The *candidate* (p.13) for the agent order `ag = [i_1, …, i_n]` and the piece order
`pc = [j_1, …, j_n]` (pieces are indexed by the agents of `N`), with its residue: the removed
prefixes. Agents not in `ag` get the empty piece. -/
noncomputable def candidate (N : Finset ι) (P : ι → Piece) (ag pc : List ι) :
    Proto ι ((ι → Piece) × Piece) :=
  candidateLoop N P (ag.zip pc) [] (fun _ => []) []

/-- The guesses of Algorithm 5: every ordering of the agents paired with every ordering of the
pieces. -/
noncomputable def guesses (N : Finset ι) : List (List ι × List ι) :=
  N.toList.permutations.product N.toList.permutations

/-- The search loop of Algorithm 5 over the untried guesses, in an order chosen by the choice
oracle; returns the first envy-free candidate and its residue, and fails if none is. -/
noncomputable def permuteLoop (N : Finset ι) (P : ι → Piece) :
    ℕ → List (List ι × List ι) → Proto ι ((ι → Piece) × Piece)
  | 0, _ => failP
  | k + 1, gs => do
      let g ← chooseP gs
      let (Y, R) ← candidate N P g.1 g.2
      let st ← get
      if recEnvyFree st N Y then return (Y, R) else permuteLoop N P k (gs.erase g)

/-- Algorithm 5, `Permute(N, (P_i)_{i ∈ N})` (p.13): returns an allocation and its residue
`(⋃ P_i) \ (⋃ Y_i)`. -/
noncomputable def permute (N : Finset ι) (P : ι → Piece) : Proto ι ((ι → Piece) × Piece) :=
  permuteLoop N P (guesses N).length (guesses N)

/-! ## Core (Algorithm 3, p.10) -/

/-- Sorts the intervals of a piece left to right (§1.3: "in Core the order is left to right"). -/
noncomputable def sortLR (C : Piece) : Piece := C.mergeSort (fun I J => decide (I.a ≤ J.a))

/-- `m` successive prefix cuts of value `w` each, for agent `c`, then the remaining piece. -/
noncomputable def equalCuts (N : Finset ι) (c : ι) (w : ℝ) : ℕ → Piece → Proto ι (List Piece)
  | 0, rest => return [rest]
  | m + 1, rest => do
      let p ← prefixCut N c rest w
      let tail ← equalCuts N c w m (suffixList rest p)
      return prefixList rest p :: tail

/-- Assigns the `k`-th piece of a list to the `k`-th agent of `l`; others get `[]`. -/
def assign : List ι → List Piece → ι → Piece
  | i :: l, P :: ps, j => if j = i then P else assign l ps j
  | _, _, _ => []

/-- Algorithm 3, `Core(c, N, C)`: the cutter `c` splits `C`, left to right, into
`P_1, …, P_n` worth `V_c(C)/n` each to her (`n - 1` prefix cuts), then
`Permute(N, (P_i))`. -/
noncomputable def core (N : Finset ι) (c : ι) (C : Piece) : Proto ι ((ι → Piece) × Piece) := do
  let C' := sortLR C
  let st ← get
  let w := st.pieceVal c C' / (N.card : ℝ)
  let pieces ← equalCuts N c w (N.card - 1) C'
  permute N (assign N.toList pieces)

/-! ## Repair (Algorithm 4, p.11) -/

/-- Agent `i`'s marks: prefix cuts of `R` at the values `t·v/M`, `t = 1, …, M - 1`. -/
noncomputable def marksOf (N : Finset ι) (R : Piece) (i : ι) (v : ℝ) (M : ℕ) :
    List ℕ → Proto ι (List Pos)
  | [] => return []
  | t :: ts => do
      let p ← prefixCut N i R ((t : ℝ) * v / (M : ℝ))
      let ps ← marksOf N R i v M ts
      return p :: ps

/-- Every agent's marks, in the order of `l`. -/
noncomputable def allMarks (N : Finset ι) (R : Piece) (v : ι → ℝ) (M : ℕ) :
    List ι → Proto ι (List Pos)
  | [] => return []
  | i :: l => do
      let ps ← marksOf N R i (v i) M (List.range' 1 (M - 1))
      let qs ← allMarks N R v M l
      return ps ++ qs

/-- Lexicographic order on positions (the order along the piece). -/
noncomputable def posLE (p q : Pos) : Bool := decide (p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 ≤ q.2))

/-- The parts of `R` between consecutive sorted marks. -/
def cellsAux (R : Piece) : Pos → List Pos → List Piece
  | prev, [] => [suffixList R prev]
  | prev, p :: ps => suffixList (prefixList R p) prev :: cellsAux R p ps

/-- The cells of Algorithm 4, Line 1: `R` cut at all marks, in `R`'s interval order. -/
noncomputable def cellsOf (R : Piece) (marks : List Pos) : List Piece :=
  cellsAux R (0, (R.getD 0 default).a) (marks.mergeSort posLE)

/-- One pick of round robin: agent `i` takes one of her favourite available cells (any
tie-break), by recorded values. -/
noncomputable def rrPick (cells : List Piece) (avail : List ℕ) (i : ι) : Proto ι ℕ := do
  let st ← get
  chooseP (avail.filter fun c =>
    decide (∀ d ∈ avail, st.pieceVal i (cells.getD d []) ≤ st.pieceVal i (cells.getD c [])))

/-- One round of round robin in the order `order`. `Q i` lists `i`'s picks in pick order. -/
noncomputable def rrRound (cells : List Piece) :
    List ι → List ℕ → (ι → List ℕ) → Proto ι ((ι → List ℕ) × List ℕ)
  | [], avail, Q => return (Q, avail)
  | i :: is, avail, Q => do
      let c ← rrPick cells avail i
      rrRound cells is (avail.erase c) (Function.update Q i (Q i ++ [c]))

/-- `r` rounds of round robin. -/
noncomputable def roundRobin (cells : List Piece) (order : List ι) :
    ℕ → List ℕ → (ι → List ℕ) → Proto ι ((ι → List ℕ) × List ℕ)
  | 0, avail, Q => return (Q, avail)
  | r + 1, avail, Q => do
      let (Q', avail') ← rrRound cells order avail Q
      roundRobin cells order r avail' Q'

/-- Algorithm 4, `Repair(N, D, R, ε)` (p.11). `M = ⌈1/(3nε)⌉`; every agent marks the
`M - 1` points splitting `R` (in its interval order) into `M` parts of equal value to her;
round robin for `n - 1` rounds over the cells in a fixed agent order; `P_i = Q_{i,1} ++ ⋯ ++
Q_{i,n-1} ++ D_i`; `(W, U) ← Permute(N, (P_i))`; returns `W` and the residue
`(R ∪ ⋃ D_i) \ ⋃ W_i`, listed as the unpicked cells followed by Permute's residue. -/
noncomputable def repair (N : Finset ι) (D : ι → Piece) (R : Piece) (ε : ℝ) :
    Proto ι ((ι → Piece) × Piece) := do
  let n := N.card
  let M := ⌈1 / (3 * (n : ℝ) * ε)⌉₊
  let st ← get
  let marks ← allMarks N R (fun i => st.pieceVal i R) M N.toList
  let cells := cellsOf R marks
  let order ← chooseP N.toList.permutations
  let (Q, avail) ← roundRobin cells order (n - 1) (List.range cells.length) (fun _ => [])
  let P : ι → Piece := fun i => ((Q i).map fun c => cells.getD c []).flatten ++ D i
  let (W, U) ← permute N P
  return (W, (avail.map fun c => cells.getD c []).flatten ++ U)

/-! ## Dominate (Algorithm 2, p.6) -/

/-- Recorded-value domination: `V_i(X_i) ≥ V_i(X_j) + V_i(R)`. -/
noncomputable def recDominates (s : Rec ι) (X : ι → Piece) (R : Piece) (i j : ι) : Prop :=
  s.pieceVal i (X j) + s.pieceVal i R ≤ s.pieceVal i (X i)

/-- Recorded-value dominated group of `(X, R)`. -/
noncomputable def recDominatedGroup (s : Rec ι) (N : Finset ι) (X : ι → Piece) (R : Piece)
    (E : Finset ι) : Prop :=
  E.Nonempty ∧ E ≠ N ∧ ∀ i ∈ N, i ∉ E → ∀ j ∈ E, recDominates s X R i j

/-- The permutation of `N` sending the `k`-th element of `l` to the `k`-th element of `l'`
(identity off `l`). -/
def permOfLists : List ι → List ι → ι → ι
  | i :: l, j :: l', x => if x = i then j else permOfLists l l' x
  | _, _, x => x

/-- `(4n²)^{-t}`. -/
noncomputable def alphaOf (n t : ℕ) : ℝ := ((4 * (n : ℝ) ^ 2) ^ t)⁻¹

/-- The admissible Line 7 tuples `(t, i*, j*, π)`, `α = (4n²)^{-t}`, `2 ≤ t ≤ n + 1`,
`i* ≠ j*`, `π` a permutation of `N`, satisfying (S1)–(S3) by recorded values (p.6). -/
noncomputable def line7Options (s : Rec ι) (N : Finset ι) (X : ι → Piece) (R : Piece)
    (Y : ι → Piece) (U : Piece) : List (ℕ × ι × ι × List ι) :=
  let n := N.card
  ((List.range' 2 n).product (N.toList.product (N.toList.product N.toList.permutations))).filter
    fun ⟨t, is, js, l'⟩ =>
      let α := alphaOf n t
      let π := permOfLists N.toList l'
      decide (is ≠ js ∧
        ¬ recDominates s X R is js ∧
        (∀ i ∈ N, s.pieceVal i (Y i) - α * s.pieceVal i U ≤ s.pieceVal i (Y (π i))) ∧
        s.pieceVal is (Y (π js)) ≤ s.pieceVal is (Y is) - 4 * (n : ℝ) ^ 2 * α * s.pieceVal is U)

/-- Lines 9–11 of Algorithm 2: while `V_{i*}(R') > α V_{i*}(U)`, run `Core(i*, N, R')` and
add its allocation to `W`. -/
noncomputable def shrink (N : Finset ι) (istar : ι) (α : ℝ) (U : Piece) :
    ℕ → (ι → Piece) → Piece → Proto ι ((ι → Piece) × Piece)
  | fuel, W, R' => do
      let st ← get
      if α * st.pieceVal istar U < st.pieceVal istar R' then
        match fuel with
        | 0 => failP
        | f + 1 => do
            let (F, R'') ← core N istar R'
            shrink N istar α U f (fun i => W i ++ F i) R''
      else
        return (W, R')

/-- The `while true` loop of Algorithm 2 (Lines 2–13), with fuel. -/
noncomputable def dominateLoop (N : Finset ι) (c : ι) :
    ℕ → (ι → Piece) → Piece → Proto ι ((ι → Piece) × Piece × Finset ι)
  | 0, _, _ => failP
  | f + 1, X, R => do
      let (Y, U) ← core N c R
      let XY : ι → Piece := fun i => X i ++ Y i
      let st ← get
      let groups := N.powerset.toList.filter fun E => decide (recDominatedGroup st N XY U E)
      if groups ≠ [] then
        let E ← chooseP groups
        return (XY, U, E)
      else
        let (t, istar, _jstar, l') ← chooseP (line7Options st N X R Y U)
        let α := alphaOf N.card t
        let π := permOfLists N.toList l'
        let (W, R') ← repair N (fun i => X i ++ Y (π i)) U α
        let (W', R'') ← shrink N istar α U f W R'
        dominateLoop N c f W' R''

/-- Algorithm 2, `Dominate(N, C)`: returns `(X, R, E)` with `R` the residue. -/
noncomputable def dominate (fuel : ℕ) (N : Finset ι) (C : Piece) :
    Proto ι ((ι → Piece) × Piece × Finset ι) := do
  let c ← chooseP N.toList
  dominateLoop N c fuel (fun _ => []) C

/-! ## Divide (Algorithm 1, p.5) -/

/-- Algorithm 1, `Divide(N, C)`, with fuel bounding the recursion and the loops of Dominate.
Agents outside `N` receive the empty piece. -/
noncomputable def divide : ℕ → Finset ι → Piece → Proto ι (ι → Piece)
  | 0, _, _ => failP
  | f + 1, N, C => do
      if N.card = 1 then
        let i ← chooseP N.toList
        return fun j => if j = i then C else []
      else if N.card = 2 then
        -- Cut-and-Choose: the first agent cuts `C` into two pieces of equal value to her,
        -- the second takes her favourite (any tie-break), the first gets the other.
        let first ← chooseP N.toList
        let second ← chooseP (N.toList.erase first)
        let st ← get
        let p ← prefixCut N first C (st.pieceVal first C / 2)
        let halves : List Piece := [prefixList C p, suffixList C p]
        let st' ← get
        let k ← chooseP ([0, 1].filter fun k => decide
          (∀ k' ∈ [0, 1], st'.pieceVal second (halves.getD k' []) ≤
            st'.pieceVal second (halves.getD k [])))
        return fun j => if j = second then halves.getD k []
          else if j = first then halves.getD (1 - k) [] else []
      else if N.card = 0 then
        failP
      else
        let (X, R, E) ← dominate f N C
        let Y ← divide f E R
        return fun i => if i ∈ N then X i ++ (if i ∈ E then Y i else []) else []

/-- The top-level run: `Divide(N, [0,1])` for the agent set `Fin n`, from the initial records
(every agent's value of `[0,1]` is `1`). Returns the allocation and the transcript. -/
noncomputable def runDivide {n : ℕ} (V : Fin n → Valuation) (o : ChoiceOracle (Fin n))
    (fuel : ℕ) : Option ((Fin n → Piece) × List (Event (Fin n))) :=
  match exec V o (divide fuel Finset.univ [⟨0, 1⟩]) (initRec (Fin n)) with
  | some (A, _, tr) => some (A, tr)
  | none => none

end EnvyFreeCake104.Divide


