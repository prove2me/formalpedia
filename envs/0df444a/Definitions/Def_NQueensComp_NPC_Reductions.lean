-- Prove2me | Definitions.Def_NQueensComp_NPC_Reductions
-- name    : NQueensComp_NPC_Reductions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T09:31:26.618212+00:00
-- url     : https://prove2.me/theorems/7593020d-6219-4834-a9cb-319595a42282
-- title:
--   The four constructions of §4 (Definitions 10, 16, 20 corrected, 24, 26–28, 31) and the solution maps of their lemmas
-- statement:
--   This module transcribes the four reductions of the paper and the maps between solutions used in its lemmas.
--
--   1. **Definition 10 (Problem 3 → Problem 2).** For $M_3=\langle n_3,P_3,C,R\rangle$: if two queens of $P_3$ attack each other, $M_2=\langle n_3,P_3\rangle$. Otherwise $n'=2n_3+1$ if $n_3\bmod3=2$ and $n'=2n_3-1$ otherwise; $Q_2=(A_{n'}+n'(Q_{19}\setminus\{(17,0)\}))\cup(B_{n'}+n'(17,0))$; $C'=C\cup\mathrm{cols}(P_3)$, $R'=R\cup\mathrm{rows}(P_3)$; $Q_3$ keeps the queens of $Q_2$ outside the columns $C'$ and rows $R'$; with $\alpha_0<\alpha_1<\cdots$ the elements of $C'$ and $\beta_0<\beta_1<\cdots$ those of $R'$, $Q_C=\{(i,2\alpha_i)\}$ and $Q_R=\{(2\beta_i,i)\}$; finally
--   $$n_2=19n'+|C'|,\qquad P_2=Q_3\cup(Q_C+n'(19,8))\cup(Q_R+n'(17,19))\cup P_3.$$
--   2. **Definition 16 (Problem 4 → Problem 3).** For $M_4=\langle n,C,R,D^-,D^+\rangle$: $Q_{D^-}=\{(6n-3-d,\,3n-1-2d)\mid d\in D^-\}$, $Q_{D^+}=\{(2n-2-d,\,n+2d)\mid d\in D^+\}$ and $M_3=\langle 7n-3,\ Q_{D^-}\cup Q_{D^+},\ \{c+3n-2\mid c\in C\},\ R\rangle$. Lemma 17 maps $S_4$ to $(S_4+(3n-2,0))\cup Q_{D^-}\cup Q_{D^+}$, Lemma 18 maps $S_3$ to $\{q\mid q+(3n-2,0)\in S_3,\ \mathrm{row}(q)<n\}$.
--   3. **Definition 20 (Problem 5 → Problem 4), corrected.** For a family of $k\ge1$ gadgets $\langle n_a,C_a,R_a,D^-_a,\{\}\rangle$: $n'=\max_a n_a$, $\alpha_a=2n'a$, $\beta_a=2n'(k-1-a)$, $n=n'(2k-1)$, $C=\bigcup_a(C_a+\alpha_a)$, $R=\bigcup_a(R_a+\beta_a)$, $D^-=\bigcup_a\{d+\alpha_a-\beta_a\mid d\in D^-_a\}$ and
--   $$D^+=\{0,\dots,2n'(k-1)-1\}\cup\{2n'k,\dots,2n-2\}.$$
--   The printed upper end $4n'k-2$ of the second block exceeds $2n-2$ for every $k$, so the output would never be an instance of Problem 4; the dropped values are sum-diagonals no square of the board has. The empty family ($k=0$, where the printed definition is undefined) is sent to $\langle1,\{0\},\{0\},\{\},\{\}\rangle$, which, like the empty family, has exactly one solution. Lemma 21 maps $(S_{4,a})_a$ to $\bigcup_a(S_{4,a}+(\alpha_a,\beta_a))$; Lemma 22 maps $S_4$ to the family $S_{4,a}=\{(\alpha,\beta)\mid 0\le\alpha,\beta<n',\ (\alpha,\beta)+(\alpha_a,\beta_a)\in S_4\}$.
--   4. **Definitions 24, 26–28, 31 (Restricted 1-in-3-SAT → Problem 5).** $G\oplus\delta=\langle n+\delta,C+\delta,R,D^-+\delta,\{\}\rangle$; $G^0=\langle4,\{0,1,3\},\{0,2,3\},\{\},\{\}\rangle$ with red solution $\{(0,0),(1,3),(3,2)\}$ and blue solution $\{(0,2),(1,0),(3,3)\}$; for the variable $v_i$ (the $i$-th smallest variable) $\delta_{v_i}=21i$ and $G^0_i=G^0\oplus\delta_{v_i}$. If $v$ occurs in clauses $c_1<c_2<c_3$, then $d^r_{v,c_1}=0,d^b_{v,c_1}=1$, $d^r_{v,c_2}=4,d^b_{v,c_2}=2$, $d^r_{v,c_3}=5,d^b_{v,c_3}=6$, and $\mathrm{col}^x_v=\delta_v+d^x_{v,c}$. For a clause $c=\{v_i,v_j,v_k\}$, $i<j<k$:
--   $$G^1_c=\langle\mathrm{col}^b_k+1,\{\mathrm{col}^b_i,\mathrm{col}^b_j,\mathrm{col}^b_k\},\{0,7,14\},\{\mathrm{col}^b_k-7,\mathrm{col}^b_i-14\},\{\}\rangle,$$
--   $$G^2_c=\langle\mathrm{col}^r_j+1,\{\mathrm{col}^r_i,\mathrm{col}^r_j\},\{0,7\},\{\},\{\}\rangle,\qquad G^3_c=\langle\mathrm{col}^r_k+1,\{\mathrm{col}^r_j,\mathrm{col}^r_k\},\{0,14\},\{\},\{\}\rangle.$$
--   $M_{5,c}=[G^0_i,G^0_j,G^0_k,G^1_c,G^2_c,G^3_c]$, and $M_5$ lists every $G^0_v$ once, then $G^1_c,G^2_c,G^3_c$ for each clause in order. Lemma 34's map takes $S_4(G^0_i)$ red iff $v_i$ is true, and for the gadgets of a clause whose true variable is $v_i$, $v_j$ or $v_k$ uses (with $b_v=\mathrm{col}^b_v$, $r_v=\mathrm{col}^r_v$)
--
--   | true variable | $S_4(G^1_c)$ | $S_4(G^2_c)$ | $S_4(G^3_c)$ |
--   |---|---|---|---|
--   | $v_i$ | $(b_i,0),(b_j,7),(b_k,14)$ | $(r_j,0),(r_i,7)$ | $(r_k,0),(r_j,14)$ |
--   | $v_j$ | $(b_j,0),(b_i,7),(b_k,14)$ | $(r_i,0),(r_j,7)$ | $(r_k,0),(r_j,14)$ |
--   | $v_k$ | $(b_k,0),(b_i,7),(b_j,14)$ | $(r_i,0),(r_j,7)$ | $(r_j,0),(r_k,14)$ |
--
--   as derived in the proof of Lemma 33 (pp. 835–836; the proof writes out the first row and omits the other two). Lemma 35's map makes $v_i$ true iff $S_4(G^0_i)$ is the red solution.
--
--   **Formalization Note** Coordinates of Definition 16 are computed in `ℤ` and converted with `Int.toNat`, which is exact on valid instances. The sorted enumerations of $C'$, $R'$ use `Finset.orderEmbOfFin`. The rank of a clause among the clauses of a variable is counted in the clause order of the instance's list; `dRed`/`dBlue` return $5$/$6$ for every rank $\ge2$ (ranks above $2$ do not occur in valid instances).
-- source:
--   Gent, Jefferson & Nightingale, Complexity of n-Queens Completion, J. Artif. Intell. Res. 59 (2017), pp. 824–825, Definition 10; p. 827, Definition 16; pp. 828–829, Definition 20; pp. 831–834, Definitions 24, 26, 27, 28, 31; pp. 835–836, proofs of Lemmas 33–34

import Mathlib
import Definitions.Def_NQueensComp_NPC_Problems

namespace NQueensComp.NPC

/-! The four constructions of §4 (Definitions 10, 16, 20, 24, 26–28, 31) on instances, and the
solution maps of Lemmas 11, 12, 17, 18, 21, 22, 34, 35. -/

/-! ### Definition 10 (pp. 824–825): Problem 3 → Problem 2 -/

/-- Some two queens of `P` attack each other. -/
def SelfAttacking (P : Finset Queen) : Prop := ∃ q₁ ∈ P, ∃ q₂ ∈ P, Attacks q₁ q₂

/-- Step 1: `n′ = 2n₃ + 1` if `n₃ mod 3 = 2`, otherwise `n′ = 2n₃ − 1`. -/
def def10_nprime (n₃ : ℕ) : ℕ := if n₃ % 3 = 2 then 2 * n₃ + 1 else 2 * n₃ - 1

/-- Step 2: `Q₂ = (A_{n′} + n′(Q₁₉ \ {(17, 0)})) ∪ (B_{n′} + n′(17, 0))`. -/
def def10_Q2 (n' : ℕ) : Finset Queen :=
  sumSet (A n') (scaleSet n' (Q19.erase (17, 0))) ∪ shiftSet (B n') (n' • ((17, 0) : Queen))

/-- Step 3: `C′ = C ∪ {col(q) | q ∈ P₃}`. -/
def def10_C' (M : Inst3) : Finset ℕ := M.C ∪ M.P.image col

/-- Step 3: `R′ = R ∪ {row(q) | q ∈ P₃}`. -/
def def10_R' (M : Inst3) : Finset ℕ := M.R ∪ M.P.image row

/-- Step 3: `Q₃ = {q ∈ Q₂ | col(q) ∉ C′, row(q) ∉ R′}`. -/
def def10_Q3 (M : Inst3) : Finset Queen :=
  (def10_Q2 (def10_nprime M.n)).filter (fun q => col q ∉ def10_C' M ∧ row q ∉ def10_R' M)

/-- Step 4: `Q_C = {(i, 2αᵢ) | 0 ≤ i < |C′|}` with `α₀ < α₁ < ⋯` the elements of `C′`. -/
noncomputable def def10_QC (M : Inst3) : Finset Queen :=
  Finset.univ.image (fun i : Fin (def10_C' M).card =>
    ((i : ℕ), 2 * (def10_C' M).orderEmbOfFin rfl i))

/-- Step 4: `Q_R = {(2βᵢ, i) | 0 ≤ i < |R′|}` with `β₀ < β₁ < ⋯` the elements of `R′`. -/
noncomputable def def10_QR (M : Inst3) : Finset Queen :=
  Finset.univ.image (fun i : Fin (def10_R' M).card =>
    (2 * (def10_R' M).orderEmbOfFin rfl i, (i : ℕ)))

open Classical in
/-- Definition 10.  If two queens of `P₃` attack each other, `M₂ = ⟨n₃, P₃⟩`.  Otherwise
`n₂ = 19n′ + |C′|` and `P₂ = Q₃ ∪ (Q_C + n′(19, 8)) ∪ (Q_R + n′(17, 19)) ∪ P₃`. -/
noncomputable def def10 (M : Inst3) : Inst2 :=
  if SelfAttacking M.P then ⟨M.n, M.P⟩ else
    ⟨19 * def10_nprime M.n + (def10_C' M).card,
      def10_Q3 M ∪ shiftSet (def10_QC M) (def10_nprime M.n • ((19, 8) : Queen)) ∪
        shiftSet (def10_QR M) (def10_nprime M.n • ((17, 19) : Queen)) ∪ M.P⟩

/-! ### Definition 16 (p. 827): Problem 4 → Problem 3 -/

/-- `Q_{D⁻} = {(6n − 3 − d, 3n − 1 − 2d) | d ∈ D⁻}` (computed in `ℤ`; both coordinates are
`≥ 0` for `d ∈ {−(n−1), …, n−1}`). -/
def def16_QDm (M : Inst4) : Finset Queen :=
  M.Dm.image (fun d : ℤ => ((6 * (M.n : ℤ) - 3 - d).toNat, (3 * (M.n : ℤ) - 1 - 2 * d).toNat))

/-- `Q_{D⁺} = {(2n − 2 − d, n + 2d) | d ∈ D⁺}` (the column computed in `ℤ`; it is `≥ 0` for
`d ∈ {0, …, 2n−2}`). -/
def def16_QDp (M : Inst4) : Finset Queen :=
  M.Dp.image (fun d : ℕ => ((2 * (M.n : ℤ) - 2 - (d : ℤ)).toNat, M.n + 2 * d))

/-- Definition 16: `M₃ = ⟨7n − 3, Q_{D⁻} ∪ Q_{D⁺}, {c + 3n − 2 | c ∈ C}, R⟩`. -/
def def16 (M : Inst4) : Inst3 :=
  ⟨7 * M.n - 3, def16_QDm M ∪ def16_QDp M, M.C.image (fun c => c + (3 * M.n - 2)), M.R⟩

/-- Lemma 17's map: `S₃ = (S₄ + (3n − 2, 0)) ∪ Q_{D⁻} ∪ Q_{D⁺}`. -/
def lemma17_map (M : Inst4) (S₄ : Finset Queen) : Finset Queen :=
  shiftSet S₄ (3 * M.n - 2, 0) ∪ def16_QDm M ∪ def16_QDp M

/-- Lemma 18's map: `S₄ = {q | q + (3n − 2, 0) ∈ S₃, row(q) < n}`, i.e.
`{(α − 3n + 2, β) | (α, β) ∈ S₃, β < n}` restricted to `α ≥ 3n − 2`. -/
def lemma18_map (M : Inst4) (S₃ : Finset Queen) : Finset Queen :=
  (S₃.filter (fun q => 3 * M.n - 2 ≤ q.1 ∧ q.2 < M.n)).image (fun q => (q.1 - (3 * M.n - 2), q.2))

/-! ### Definition 20 (pp. 828–829): Problem 5 → Problem 4 -/

/-- `n′ = max{nₐ | 0 ≤ a < k}`. -/
def def20_nmax (Ms : Inst5) : ℕ := (Ms.map Inst4.n).foldr max 0

/-- `αₐ = 2n′a`. -/
def def20_alpha (Ms : Inst5) (a : ℕ) : ℕ := 2 * def20_nmax Ms * a

/-- `βₐ = 2n′(k − 1 − a)`. -/
def def20_beta (Ms : Inst5) (a : ℕ) : ℕ := 2 * def20_nmax Ms * (Ms.length - 1 - a)

/-- Definition 20, with `k = |M₅|`, `n = n′(2k − 1)`, `C = ⋃ₐ {c + αₐ | c ∈ Cₐ}`,
`R = ⋃ₐ {r + βₐ | r ∈ Rₐ}`, `D⁻ = ⋃ₐ {d + αₐ − βₐ | d ∈ D⁻ₐ}` and the corrected
`D⁺ = {0, …, 2n′(k−1) − 1} ∪ {2n′k, …, 2n − 2}`.  For the empty family (`k = 0`, where the printed
definition is undefined) the output is `⟨1, {0}, {0}, {}, {}⟩`, which has exactly one solution. -/
def def20 (Ms : Inst5) : Inst4 :=
  if Ms.length = 0 then ⟨1, {0}, {0}, ∅, ∅⟩ else
    ⟨def20_nmax Ms * (2 * Ms.length - 1),
      (Finset.univ : Finset (Fin Ms.length)).biUnion
        (fun a => (Ms.get a).C.image (fun c => c + def20_alpha Ms a)),
      (Finset.univ : Finset (Fin Ms.length)).biUnion
        (fun a => (Ms.get a).R.image (fun r => r + def20_beta Ms a)),
      (Finset.univ : Finset (Fin Ms.length)).biUnion
        (fun a => (Ms.get a).Dm.image
          (fun d => d + (def20_alpha Ms a : ℤ) - (def20_beta Ms a : ℤ))),
      Finset.range (2 * def20_nmax Ms * (Ms.length - 1)) ∪
        Finset.Icc (2 * def20_nmax Ms * Ms.length)
          (2 * (def20_nmax Ms * (2 * Ms.length - 1)) - 2)⟩

/-- Lemma 21's map: `S₄ = ⋃_{0 ≤ a < k} (S₄,ₐ + (αₐ, βₐ))`. -/
def lemma21_map (Ms : Inst5) (Ss : List (Finset Queen)) : Finset Queen :=
  (Finset.range Ms.length).biUnion
    (fun a => shiftSet (Ss.getD a ∅) (def20_alpha Ms a, def20_beta Ms a))

/-- Lemma 22's map: `S₄,ₐ = {(α, β) | 0 ≤ α, β < n′, (α, β) + (αₐ, βₐ) ∈ S₄}`. -/
def lemma22_map (Ms : Inst5) (S₄ : Finset Queen) : List (Finset Queen) :=
  (List.range Ms.length).map (fun a =>
    ((Finset.range (def20_nmax Ms)) ×ˢ (Finset.range (def20_nmax Ms))).filter
      (fun q => q + (def20_alpha Ms a, def20_beta Ms a) ∈ S₄))

/-! ### Definitions 24, 26–28, 31 (pp. 831–835): Problem 6 → Problem 5 -/

/-- Definition 24: `G ⊕ δ = ⟨n + δ, {c + δ | c ∈ C}, R, {d + δ | d ∈ D⁻}, {}⟩`. -/
def Inst4.shift (G : Inst4) (δ : ℕ) : Inst4 :=
  ⟨G.n + δ, G.C.image (fun c => c + δ), G.R, G.Dm.image (fun d => d + (δ : ℤ)), ∅⟩

/-- Definition 26: the variable gadget `G⁰ = ⟨4, {0, 1, 3}, {0, 2, 3}, {}, {}⟩`. -/
def G0 : Inst4 := ⟨4, {0, 1, 3}, {0, 2, 3}, ∅, ∅⟩

/-- The index `i` of the variable `v = vᵢ`: variables are ordered increasingly,
`V = {v₀ < v₁ < ⋯}`. -/
def varIdx (cs : Inst6) (v : ℕ) : ℕ := ((vars cs).filter (fun u => u < v)).card

/-- `δ_{vᵢ} = 21i` (Definition 26). -/
def delta (cs : Inst6) (v : ℕ) : ℕ := 21 * varIdx cs v

/-- `G⁰ᵢ = G⁰ ⊕ δ_{vᵢ}` (Definition 26). -/
def G0v (cs : Inst6) (v : ℕ) : Inst4 := G0.shift (delta cs v)

/-- The red solution `{(0,0), (1,3), (3,2)}` of `G⁰`, shifted by `(δ, 0)`. -/
def redSol (δ : ℕ) : Finset Queen := shiftSet {(0, 0), (1, 3), (3, 2)} (δ, 0)

/-- The blue solution `{(0,2), (1,0), (3,3)}` of `G⁰`, shifted by `(δ, 0)`. -/
def blueSol (δ : ℕ) : Finset Queen := shiftSet {(0, 2), (1, 0), (3, 3)} (δ, 0)

/-- The rank of clause `c_j` among the clauses containing `v` (`0` for the first, `1` for the
second, `2` for the third, in the clause order). -/
def occRank (cs : Inst6) (v j : ℕ) : ℕ := (cs.take j).countP (fun c => decide (v ∈ c))

/-- `dʳ` for the first, second, third clause of a variable: `0, 4, 5` (Definition 26). -/
def dRed : ℕ → ℕ
  | 0 => 0
  | 1 => 4
  | _ => 5

/-- `dᵇ` for the first, second, third clause of a variable: `1, 2, 6` (Definition 26). -/
def dBlue : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | _ => 6

/-- `colʳ_v = δ_v + dʳ_{v,c}` for the clause `c = c_j` (p. 832). -/
def colRed (cs : Inst6) (j v : ℕ) : ℕ := delta cs v + dRed (occRank cs v j)

/-- `colᵇ_v = δ_v + dᵇ_{v,c}` for the clause `c = c_j` (p. 832). -/
def colBlue (cs : Inst6) (j v : ℕ) : ℕ := delta cs v + dBlue (occRank cs v j)

/-- The `t`-th smallest variable of clause `c_j` (`t = 0, 1, 2` give `vᵢ, vⱼ, vₖ` with
`i < j < k`). -/
def clauseVar (cs : Inst6) (j t : ℕ) : ℕ := ((cs.getD j ∅).sort (· ≤ ·)).getD t 0

/-- Definition 27: `G¹_c = ⟨colᵇₖ + 1, {colᵇᵢ, colᵇⱼ, colᵇₖ}, {0, 7, 14},
{colᵇₖ − 7, colᵇᵢ − 14}, {}⟩` for `c = c_j = {vᵢ, vⱼ, vₖ}`, `i < j < k`. -/
def G1 (cs : Inst6) (j : ℕ) : Inst4 :=
  ⟨colBlue cs j (clauseVar cs j 2) + 1,
    {colBlue cs j (clauseVar cs j 0), colBlue cs j (clauseVar cs j 1),
      colBlue cs j (clauseVar cs j 2)},
    {0, 7, 14},
    {(colBlue cs j (clauseVar cs j 2) : ℤ) - 7, (colBlue cs j (clauseVar cs j 0) : ℤ) - 14},
    ∅⟩

/-- Definition 28: `G²_c = ⟨colʳⱼ + 1, {colʳᵢ, colʳⱼ}, {0, 7}, {}, {}⟩`. -/
def G2 (cs : Inst6) (j : ℕ) : Inst4 :=
  ⟨colRed cs j (clauseVar cs j 1) + 1,
    {colRed cs j (clauseVar cs j 0), colRed cs j (clauseVar cs j 1)}, {0, 7}, ∅, ∅⟩

/-- Definition 28: `G³_c = ⟨colʳₖ + 1, {colʳⱼ, colʳₖ}, {0, 14}, {}, {}⟩`. -/
def G3 (cs : Inst6) (j : ℕ) : Inst4 :=
  ⟨colRed cs j (clauseVar cs j 2) + 1,
    {colRed cs j (clauseVar cs j 1), colRed cs j (clauseVar cs j 2)}, {0, 14}, ∅, ∅⟩

/-- `M₅,c = {G⁰ᵢ, G⁰ⱼ, G⁰ₖ, G¹_c, G²_c, G³_c}` for `c = c_j` (Definition 31), in this order. -/
def M5c (cs : Inst6) (j : ℕ) : Inst5 :=
  [G0v cs (clauseVar cs j 0), G0v cs (clauseVar cs j 1), G0v cs (clauseVar cs j 2),
    G1 cs j, G2 cs j, G3 cs j]

/-- Definition 31: `M₅ = ⋃_{c ∈ C} M₅,c`, each `G⁰_v` once, as the family
`G⁰_{v₀}, …, G⁰_{v_{|V|−1}}, G¹_{c₀}, G²_{c₀}, G³_{c₀}, G¹_{c₁}, …`. -/
def def31 (cs : Inst6) : Inst5 :=
  ((vars cs).sort (· ≤ ·)).map (G0v cs) ++
    (List.range cs.length).flatMap (fun j => [G1 cs j, G2 cs j, G3 cs j])

/-- The solutions `S₄(G¹_c), S₄(G²_c), S₄(G³_c)` of the proof of Lemma 33 when the `t`-th variable
of `c = c_j` is the true one (`t = 0, 1, 2` for `vᵢ, vⱼ, vₖ`); writing `b_v = colᵇ_v`,
`r_v = colʳ_v`:
* `t = 0`: `{(bᵢ,0), (bⱼ,7), (bₖ,14)}`, `{(rⱼ,0), (rᵢ,7)}`, `{(rₖ,0), (rⱼ,14)}`;
* `t = 1`: `{(bⱼ,0), (bᵢ,7), (bₖ,14)}`, `{(rᵢ,0), (rⱼ,7)}`, `{(rₖ,0), (rⱼ,14)}`;
* `t = 2`: `{(bₖ,0), (bᵢ,7), (bⱼ,14)}`, `{(rᵢ,0), (rⱼ,7)}`, `{(rⱼ,0), (rₖ,14)}`. -/
def clauseSols (cs : Inst6) (j t : ℕ) : List (Finset Queen) :=
  let bi := colBlue cs j (clauseVar cs j 0)
  let bj := colBlue cs j (clauseVar cs j 1)
  let bk := colBlue cs j (clauseVar cs j 2)
  let ri := colRed cs j (clauseVar cs j 0)
  let rj := colRed cs j (clauseVar cs j 1)
  let rk := colRed cs j (clauseVar cs j 2)
  match t with
  | 0 => [{(bi, 0), (bj, 7), (bk, 14)}, {(rj, 0), (ri, 7)}, {(rk, 0), (rj, 14)}]
  | 1 => [{(bj, 0), (bi, 7), (bk, 14)}, {(ri, 0), (rj, 7)}, {(rk, 0), (rj, 14)}]
  | _ => [{(bk, 0), (bi, 7), (bj, 14)}, {(ri, 0), (rj, 7)}, {(rj, 0), (rk, 14)}]

/-- The position `t ∈ {0, 1, 2}` of the true variable of clause `c_j` under `T`. -/
def truePos (cs : Inst6) (j : ℕ) (T : Finset ℕ) : ℕ :=
  if clauseVar cs j 0 ∈ T then 0 else if clauseVar cs j 1 ∈ T then 1 else 2

/-- Lemma 34's map: `S₄(G⁰ᵢ)` is the red solution iff `vᵢ` is true and the blue one otherwise;
`S₄(G¹_c), S₄(G²_c), S₄(G³_c)` as in the proof of Lemma 33. -/
def lemma34_map (cs : Inst6) (T : Finset ℕ) : List (Finset Queen) :=
  ((vars cs).sort (· ≤ ·)).map
      (fun v => if v ∈ T then redSol (delta cs v) else blueSol (delta cs v)) ++
    (List.range cs.length).flatMap (fun j => clauseSols cs j (truePos cs j T))

/-- Lemma 35's map: `vᵢ` is true iff `S₄(G⁰ᵢ)` is the red solution (`G⁰ᵢ` sits at position `i`
of `def31 cs`). -/
def lemma35_map (cs : Inst6) (Ss : List (Finset Queen)) : Finset ℕ :=
  (vars cs).filter (fun v => Ss.getD (varIdx cs v) ∅ = redSol (delta cs v))

end NQueensComp.NPC


