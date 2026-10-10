-- Prove2me | Definitions.Def_GGHRSW_ColoredMatrix_Model
-- name    : GGHRSW_ColoredMatrix_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T20:07:08.854409+00:00
-- url     : https://prove2.me/theorems/a19cf6b0-ee45-4f3b-9446-9018183b684f
-- title:
--   Def. 9, Def. 10, §4.1 and App. C.1–C.2, pp. 12, 16–18, 37–38 — branching programs, RND_p(BP), the generic colored matrix model and adversaries
-- statement:
--   This file defines every object of Appendix C of Garg, Gentry, Halevi, Raykova, Sahai and Waters: oblivious branching programs, the randomized branching program $\mathcal{RND}_p(BP)$, the multilinear form $F_\chi$, and the generic colored matrix model with its representation oracle and adversaries.
--
--   **Branching programs.** A length-$n$ oblivious branching program over $\ell$ input bits is $BP = (n,\ell,\mathsf{inp},A)$ where $\mathsf{inp}(i)\in[\ell]$ is the input bit read in step $i$ and $A_{i,0},A_{i,1}$ are permutations of $\{1,\dots,5\}$, used through their $5\times5$ permutation matrices. On input $\chi\in\{0,1\}^\ell$ the program outputs $1$ iff
--   $$\prod_{i=1}^{n} A_{i,\chi_{\mathsf{inp}(i)}} = I,$$
--   the product taken in step order. The block of bit $j$ is $I_j=\{i:\mathsf{inp}(i)=j\}$. A partial assignment is a set $J$ of input positions with values $\sigma:J\to\{0,1\}$; the restricted function $F|_\sigma$ is $x\mapsto BP(x \text{ with the bits in } J \text{ set by } \sigma)$. Two partial assignments $(J,\sigma)$, $(J,\sigma')$ are **functionally equivalent** (Definition 10) if $F|_\sigma = F|_{\sigma'}$ as functions of all inputs.
--
--   **The randomized program** (§4.1, Eq. (1)). Let $p$ be prime, $m = 2n+5$, $N = 2m+5$. A sample consists of: full-rank $N\times N$ matrices $R_0,\dots,R_n$ and $R'_0,\dots,R'_n$ over $\mathbb Z_p$; random diagonal entries $1,\dots,2m$ for each $D_{i,b}$ and $D'_{i,b}$; random entries $m+1,\dots,2m$ of the row vectors $\mathbf s,\mathbf s'$ and $1,\dots,m$ of the column vectors $\mathbf t,\mathbf t'$ (the others zero); 5-vectors $(\mathbf s^*,\mathbf t^*,\mathbf s^{*\prime},\mathbf t^{*\prime})$ uniform subject to $\langle \mathbf s^*,\mathbf t^*\rangle = \langle \mathbf s^{*\prime},\mathbf t^{*\prime}\rangle$, placed in the last 5 entries; and scalars $\gamma_{j,b,1},\dots,\gamma_{j,b,2n}$. All components are independent and uniform. The bundling scalars follow the procedure of p. 42: if step $i$ is the $r$-th step of its block $I_j$ and $k=|I_j|$, then
--   $$\alpha_{i,b} = \gamma_{j,b,2r-1}\gamma_{j,b,2r},\qquad \alpha'_{i,b}=\gamma_{j,b,2r}\gamma_{j,b,2r+1}\ (\text{indices mod } 2k),$$
--   so that $\prod_{i\in I_j}\alpha_{i,b}=\prod_{i\in I_j}\alpha'_{i,b}$. The matrix $D_{i,b}$ is block diagonal, with the random diagonal on coordinates $1..2m$ and $\alpha_{i,b}A_{i,b}$ in the bottom-right $5\times5$ block; $D'_{i,b}$ is the same with $\alpha'_{i,b}I$. The garbled objects are
--   $$\tilde{\mathbf s} = \mathbf s R_0^{-1},\quad \tilde{\mathbf t} = R_n\mathbf t,\quad \tilde D_{i,b}=R_{i-1}D_{i,b}R_i^{-1},$$
--   and the primed versions with $R'$. The multilinear form of §4.2 is
--   $$F_\chi = \tilde{\mathbf s}\Big(\prod_i \tilde D_{i,\chi_{\mathsf{inp}(i)}}\Big)\tilde{\mathbf t} - \tilde{\mathbf s}'\Big(\prod_i \tilde D'_{i,\chi_{\mathsf{inp}(i)}}\Big)\tilde{\mathbf t}' \bmod p.$$
--
--   **The generic colored matrix model** (App. C.1–C.2). Matrices carry a left and a right colour: $\tilde{\mathbf s}$ goes from $0$ to $1$, $\tilde{\mathbf s}'$ from $0$ to $1'$, $\tilde D_{i,b}$ from $i$ to $i+1$, $\tilde D'_{i,b}$ from $i'$ to $(i+1)'$, $\tilde{\mathbf t}$ from $n+1$ to $n+2$, $\tilde{\mathbf t}'$ from $(n+1)'$ to $n+2$. The representation oracle's initial database $DB(p,BP,(J,\sigma))$ holds $\tilde{\mathbf s},\tilde{\mathbf s}',\tilde{\mathbf t},\tilde{\mathbf t}'$, the matrices $\tilde D_{i,\sigma(\mathsf{inp}(i))},\tilde D'_{i,\sigma(\mathsf{inp}(i))}$ for steps $i\in I_J$, and both $\tilde D_{i,0},\tilde D_{i,1}$ (and primed) for the other steps; its size is $|DB| = 4+\sum_i(2 \text{ if } i\in I_J \text{ else } 4)$. The adversary refers to matrices only by handles and may ask for $\mathsf{add}(h,h')$ (same dimensions and colours), $\mathsf{ConstMul}(h,a)$ and $\mathsf{mult}(h,h')$ (right dimension and colour of the first equal to the left ones of the second). The oracle computes the result mod $p$; if a record with the same dimensions, colours and matrix already exists it returns that handle, otherwise it stores the result under the next handle and returns it. An adversary has random coins, chooses each query adaptively from its coins and all previous replies, and finally outputs a bit; its acceptance probability is taken over its coins and the sample of $\mathcal{RND}_p(BP)$.
--
--   These are the objects of Theorem 6, the paper's evidence that its hardness assumption (Assumption 1) withstands all attacks that only add, scale and multiply the published matrices in a colour-respecting order.
--
--   **Formalization Note.** Steps, handles and $\gamma$-indices are 0-based: step $i$ uses $R_i$ and $R_{i+1}^{-1}$, a handle is an index in the database list, and $\alpha_{i,b}=\gamma_{2r}\gamma_{2r+1}$, $\alpha'_{i,b}=\gamma_{2r+1}\gamma_{(2r+2)\bmod 2k}$. Colours are `src` ($0$), `snk` ($n+2$), `prim i` ($i$) and `dum i` ($i'$). The output convention is "identity means 1" (§3, §4.2, App. C), not the $(A_0,A_1)$ outputs of Definition 9; the value is defined through the product of permutation *matrices* in step order. §4.1 step 1 says the $\alpha$'s are random "subject to the constraint"; the proof of Theorem 6 (p. 42) uses the $\gamma$-procedure, which is what is formalized (over $\mathbb Z_p$ the two distributions differ). The sample is a finite product type with the uniform (counting) distribution; vectors are $1\times N$ and $N\times1$ matrices. The database lists, in a fixed public order, $\tilde{\mathbf s},\tilde{\mathbf s}',\tilde{\mathbf t},\tilde{\mathbf t}'$, the primal step matrices (fixed steps in order, then free steps with $b=0,1$), then the dummy ones. A query with an unknown handle or mismatched dimensions/colours is answered $\bot$ (`none`) and leaves the database unchanged; the page leaves this case implicit. Adversary coins are uniform on `Fin K` with $K>0$; the adversary makes exactly $q$ queries.
-- source:
--   Garg, Gentry, Halevi, Raykova, Sahai and Waters, Candidate Indistinguishability Obfuscation and Functional Encryption for All Circuits, SIAM J. Comput. 45(3), 2016 (authors' version of July 21, 2013), pp. 12, 16–18, 37–38, 42, Definitions 9–10, Section 4.1 (Eq. (1)), Section 4.2, Appendix C.1–C.2, γ-procedure of §C.3.1

import Mathlib

namespace GGHRSW.ColoredMatrix

open Matrix

/-! ## Branching programs (Def. 9, p. 12; notation of §4, p. 16; Def. 10, p. 18) -/

/-- A length-`n` oblivious linear branching program over `ℓ` input bits (Def. 9, notation of §4):
step `i` reads input bit `inp i` and selects the permutation `A i b` of `Fin 5` according to the
bit value `b`. Steps are 0-based (paper step `i` is `i - 1` here). -/
structure BP where
  n : ℕ
  ℓ : ℕ
  inp : Fin n → Fin ℓ
  A : Fin n → Bool → Equiv.Perm (Fin 5)

namespace BP

/-- The value of the branching program on `χ`: `true` (output 1) iff the ordered product
`A_{0,χ(inp 0)} ⋯ A_{n-1,χ(inp (n-1))}` of the 5×5 permutation matrices is the identity
(the "identity means 1" convention of §3, §4.2 and App. C). -/
def eval (bp : BP) (χ : Fin bp.ℓ → Bool) : Bool :=
  decide ((List.ofFn fun i => (bp.A i (χ (bp.inp i))).permMatrix ℤ).prod = 1)

/-- The block `I_j = {i | inp i = j}` of steps reading input bit `j`. -/
def block (bp : BP) (j : Fin bp.ℓ) : Finset (Fin bp.n) :=
  Finset.univ.filter fun i => bp.inp i = j

end BP

/-- The input obtained from `x` by fixing the bits in `J` to the values of `σ`
(only `σ j` for `j ∈ J` is read). -/
def fix {ℓ : ℕ} (J : Finset (Fin ℓ)) (σ x : Fin ℓ → Bool) : Fin ℓ → Bool :=
  fun j => if j ∈ J then σ j else x j

/-- Def. 10: the partial assignments `(J, σ)` and `(J, σ')` are functionally equivalent relative to
the function computed by `bp`, i.e. `F|_σ = F|_σ'` on every input. -/
def FunctionallyEquivalent (bp : BP) (J : Finset (Fin bp.ℓ)) (σ σ' : Fin bp.ℓ → Bool) : Prop :=
  ∀ x : Fin bp.ℓ → Bool, bp.eval (fix J σ x) = bp.eval (fix J σ' x)

/-! ## The randomized branching program `RND_p(BP)` (§4.1, Eq. (1), pp. 16–17; γ-procedure p. 42) -/

/-- `m = 2n + 5`. -/
abbrev mDim (n : ℕ) : ℕ := 2 * n + 5

/-- `N = 2m + 5`, the dimension of the randomized matrices. -/
abbrev NDim (n : ℕ) : ℕ := 2 * mDim n + 5

/-- Quadruples `(s*, t*, s*′, t*′)` of 5-vectors with `⟨s*, t*⟩ = ⟨s*′, t*′⟩` (§4.1, step 3). -/
abbrev Bookends (p : ℕ) :=
  {v : (Fin 5 → ZMod p) × (Fin 5 → ZMod p) × (Fin 5 → ZMod p) × (Fin 5 → ZMod p) //
    v.1 ⬝ᵥ v.2.1 = v.2.2.1 ⬝ᵥ v.2.2.2}

/-- One sample `ω` of all the randomness of `RND_p(BP)`: the full-rank matrices `R_0..R_n`,
`R′_0..R′_n`; the random diagonal entries of `D_{i,b}` and `D′_{i,b}`; the random middle entries of
`s, s′` and low entries of `t, t′`; the constrained 5-vectors; and the scalars `γ_{j,b,·}` from
which the bundling scalars are built. Uniform sampling is uniform over this finite type. -/
abbrev Sample (p : ℕ) (bp : BP) :=
  (Fin (bp.n + 1) → GL (Fin (NDim bp.n)) (ZMod p)) ×
  (Fin (bp.n + 1) → GL (Fin (NDim bp.n)) (ZMod p)) ×
  (Fin bp.n → Bool → Fin (2 * mDim bp.n) → ZMod p) ×
  (Fin bp.n → Bool → Fin (2 * mDim bp.n) → ZMod p) ×
  (Fin (mDim bp.n) → ZMod p) × (Fin (mDim bp.n) → ZMod p) ×
  (Fin (mDim bp.n) → ZMod p) × (Fin (mDim bp.n) → ZMod p) ×
  Bookends p ×
  (Fin bp.ℓ → Bool → Fin (2 * bp.n) → ZMod p)

/-- The sample space is finite (the nested product is too deep for default instance search). -/
instance instFintypeSample (p : ℕ) [Fact p.Prime] (bp : BP) : Fintype (Sample p bp) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : Fintype (Fin (bp.n + 1) → GL (Fin (NDim bp.n)) (ZMod p)) := inferInstance
  haveI : Fintype (Fin bp.n → Bool → Fin (2 * mDim bp.n) → ZMod p) := inferInstance
  haveI : Fintype (Fin (mDim bp.n) → ZMod p) := inferInstance
  haveI : Fintype (Bookends p) := inferInstance
  haveI : Fintype (Fin bp.ℓ → Bool → Fin (2 * bp.n) → ZMod p) := inferInstance
  unfold Sample
  infer_instance

namespace Sample

variable {p : ℕ} {bp : BP} (ω : Sample p bp)

/-- `R_0, …, R_n`. -/
def R : Fin (bp.n + 1) → GL (Fin (NDim bp.n)) (ZMod p) := ω.1
/-- `R′_0, …, R′_n`. -/
def R' : Fin (bp.n + 1) → GL (Fin (NDim bp.n)) (ZMod p) := ω.2.1
/-- Random diagonal entries `1..2m` of `D_{i,b}`. -/
def d : Fin bp.n → Bool → Fin (2 * mDim bp.n) → ZMod p := ω.2.2.1
/-- Random diagonal entries `1..2m` of `D′_{i,b}`. -/
def d' : Fin bp.n → Bool → Fin (2 * mDim bp.n) → ZMod p := ω.2.2.2.1
/-- Entries `m+1..2m` of `s`. -/
def sMid : Fin (mDim bp.n) → ZMod p := ω.2.2.2.2.1
/-- Entries `m+1..2m` of `s′`. -/
def s'Mid : Fin (mDim bp.n) → ZMod p := ω.2.2.2.2.2.1
/-- Entries `1..m` of `t`. -/
def tLow : Fin (mDim bp.n) → ZMod p := ω.2.2.2.2.2.2.1
/-- Entries `1..m` of `t′`. -/
def t'Low : Fin (mDim bp.n) → ZMod p := ω.2.2.2.2.2.2.2.1
/-- `s*`. -/
def sStar : Fin 5 → ZMod p := ω.2.2.2.2.2.2.2.2.1.1.1
/-- `t*`. -/
def tStar : Fin 5 → ZMod p := ω.2.2.2.2.2.2.2.2.1.1.2.1
/-- `s*′`. -/
def s'Star : Fin 5 → ZMod p := ω.2.2.2.2.2.2.2.2.1.1.2.2.1
/-- `t*′`. -/
def t'Star : Fin 5 → ZMod p := ω.2.2.2.2.2.2.2.2.1.1.2.2.2
/-- The scalars `γ_{j,b,x}` (input bit `j`, bit value `b`, 0-based index `x`). -/
def γ : Fin bp.ℓ → Bool → Fin (2 * bp.n) → ZMod p := ω.2.2.2.2.2.2.2.2.2

end Sample

/-- Number of earlier steps reading the same input bit: step `i` is the `(pos i)`-th (0-based)
element of its block `I_{inp i}`. -/
def pos (bp : BP) (i : Fin bp.n) : ℕ :=
  (Finset.univ.filter fun i' : Fin bp.n => i' < i ∧ bp.inp i' = bp.inp i).card

/-- `k_j = |I_j|`. -/
def blockSize (bp : BP) (j : Fin bp.ℓ) : ℕ := (bp.block j).card

/-- `γ_{j,b}` at a natural-number index (indices `≥ 2n` never occur; they read as `0`). -/
def gam {p : ℕ} (bp : BP) (γ : Fin bp.ℓ → Bool → Fin (2 * bp.n) → ZMod p) (j : Fin bp.ℓ)
    (b : Bool) (x : ℕ) : ZMod p :=
  if h : x < 2 * bp.n then γ j b ⟨x, h⟩ else 0

/-- Bundling scalar `α_{i,b} = γ_{2r,b} γ_{2r+1,b}` for the `r`-th step of block `j = inp i`
(the γ-procedure of p. 42, 0-based). -/
def alpha {p : ℕ} (bp : BP) (γ : Fin bp.ℓ → Bool → Fin (2 * bp.n) → ZMod p) (i : Fin bp.n)
    (b : Bool) : ZMod p :=
  gam bp γ (bp.inp i) b (2 * pos bp i) * gam bp γ (bp.inp i) b (2 * pos bp i + 1)

/-- Bundling scalar `α′_{i,b} = γ_{2r+1,b} γ_{(2r+2) mod 2k_j,b}` (γ-procedure of p. 42, 0-based). -/
def alpha' {p : ℕ} (bp : BP) (γ : Fin bp.ℓ → Bool → Fin (2 * bp.n) → ZMod p) (i : Fin bp.n)
    (b : Bool) : ZMod p :=
  gam bp γ (bp.inp i) b (2 * pos bp i + 1) *
    gam bp γ (bp.inp i) b ((2 * pos bp i + 2) % (2 * blockSize bp (bp.inp i)))

/-- The block-diagonal `(r+5) × (r+5)` matrix with diagonal `d` on the first `r` coordinates and the
5×5 block `B` in the bottom-right corner. -/
def blockDiag {p r : ℕ} (d : Fin r → ZMod p) (B : Matrix (Fin 5) (Fin 5) (ZMod p)) :
    Matrix (Fin (r + 5)) (Fin (r + 5)) (ZMod p) :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks (Matrix.diagonal d) 0 0 B)

/-- A row vector of length `2m+5`: zero on positions `< m`, `mid` on `m..2m-1`, `star` on the last 5. -/
def bookendRow {p m : ℕ} (mid : Fin m → ZMod p) (star : Fin 5 → ZMod p) :
    Matrix (Fin 1) (Fin (2 * m + 5)) (ZMod p) :=
  Matrix.of fun _ => Fin.append
    (fun k : Fin (2 * m) => if h : k.val < m then 0 else mid ⟨k.val - m, by omega⟩) star

/-- A column vector of length `2m+5`: `low` on positions `< m`, zero on `m..2m-1`, `star` on the last 5. -/
def bookendCol {p m : ℕ} (low : Fin m → ZMod p) (star : Fin 5 → ZMod p) :
    Matrix (Fin (2 * m + 5)) (Fin 1) (ZMod p) :=
  Matrix.of fun k _ => Fin.append
    (fun k : Fin (2 * m) => if h : k.val < m then low ⟨k.val, h⟩ else 0) star k

section Garbled

variable {p : ℕ} {bp : BP} (ω : Sample p bp)

/-- `D_{i,b}`: random diagonal on the first `2m` coordinates, `α_{i,b} A_{i,b}` in the bottom-right. -/
def Dmat (i : Fin bp.n) (b : Bool) : Matrix (Fin (NDim bp.n)) (Fin (NDim bp.n)) (ZMod p) :=
  blockDiag (ω.d i b) (alpha bp ω.γ i b • (bp.A i b).permMatrix (ZMod p))

/-- `D′_{i,b}`: random diagonal on the first `2m` coordinates, `α′_{i,b} I` in the bottom-right. -/
def D'mat (i : Fin bp.n) (b : Bool) : Matrix (Fin (NDim bp.n)) (Fin (NDim bp.n)) (ZMod p) :=
  blockDiag (ω.d' i b) (alpha' bp ω.γ i b • (1 : Matrix (Fin 5) (Fin 5) (ZMod p)))

/-- `s̃ = s R_0⁻¹`. -/
def sTil : Matrix (Fin 1) (Fin (NDim bp.n)) (ZMod p) :=
  bookendRow ω.sMid ω.sStar * Units.val (ω.R 0)⁻¹

/-- `t̃ = R_n t`. -/
def tTil : Matrix (Fin (NDim bp.n)) (Fin 1) (ZMod p) :=
  Units.val (ω.R (Fin.last bp.n)) * bookendCol ω.tLow ω.tStar

/-- `s̃′ = s′ (R′_0)⁻¹`. -/
def s'Til : Matrix (Fin 1) (Fin (NDim bp.n)) (ZMod p) :=
  bookendRow ω.s'Mid ω.s'Star * Units.val (ω.R' 0)⁻¹

/-- `t̃′ = R′_n t′`. -/
def t'Til : Matrix (Fin (NDim bp.n)) (Fin 1) (ZMod p) :=
  Units.val (ω.R' (Fin.last bp.n)) * bookendCol ω.t'Low ω.t'Star

/-- `D̃_{i,b} = R_i D_{i,b} R_{i+1}⁻¹` (0-based step `i`; paper: `R_{i-1} D_{i,b} R_i⁻¹`). -/
def DTil (i : Fin bp.n) (b : Bool) : Matrix (Fin (NDim bp.n)) (Fin (NDim bp.n)) (ZMod p) :=
  Units.val (ω.R i.castSucc) * Dmat ω i b * Units.val (ω.R i.succ)⁻¹

/-- `D̃′_{i,b} = R′_i D′_{i,b} (R′_{i+1})⁻¹`. -/
def D'Til (i : Fin bp.n) (b : Bool) : Matrix (Fin (NDim bp.n)) (Fin (NDim bp.n)) (ZMod p) :=
  Units.val (ω.R' i.castSucc) * D'mat ω i b * Units.val (ω.R' i.succ)⁻¹

end Garbled

/-- The multilinear form `F_χ(RND_p(BP)) = s̃ (∏_i D̃_{i,χ_{inp(i)}}) t̃ − s̃′ (∏_i D̃′_{i,χ_{inp(i)}}) t̃′`
(§4.2, p. 17), products in step order. -/
def Fchi {p : ℕ} (bp : BP) (ω : Sample p bp) (χ : Fin bp.ℓ → Bool) : ZMod p :=
  (sTil ω * (List.ofFn fun i => DTil ω i (χ (bp.inp i))).prod * tTil ω) 0 0 -
    (s'Til ω * (List.ofFn fun i => D'Til ω i (χ (bp.inp i))).prod * t'Til ω) 0 0

/-! ## The generic colored matrix model (App. C.1–C.2, pp. 37–38) -/

/-- Colours: `src` is the paper's `0`, `snk` is `n+2`, `prim i` is `i` and `dum i` is `i′`. -/
inductive Color
  | src
  | snk
  | prim (i : ℕ)
  | dum (i : ℕ)
  deriving DecidableEq

/-- A database record `(M, (rows, LC), (cols, RC))`; its handle is its index in the database. -/
structure Record (p : ℕ) where
  rows : ℕ
  cols : ℕ
  lc : Color
  rc : Color
  mat : Matrix (Fin rows) (Fin cols) (ZMod p)

/-- The records `(D̃_{i,b}, (N, i+1), (N, i+2))` (primal) and `(D̃′_{i,b}, (N, (i+1)′), (N, (i+2)′))`
(dummy) for 0-based step `i`. -/
def stepRec {p : ℕ} {bp : BP} (ω : Sample p bp) (primal : Bool) (i : Fin bp.n) (b : Bool) :
    Record p :=
  if primal then ⟨NDim bp.n, NDim bp.n, .prim (i.val + 1), .prim (i.val + 2), DTil ω i b⟩
  else ⟨NDim bp.n, NDim bp.n, .dum (i.val + 1), .dum (i.val + 2), D'Til ω i b⟩

/-- The records of one program (primal or dummy) after input fixing: for fixed steps
(`inp i ∈ J`) only `b = σ(inp i)`; then for free steps both `b = 0, 1`. Steps in increasing order. -/
def programRecs {p : ℕ} (bp : BP) (J : Finset (Fin bp.ℓ)) (σ : Fin bp.ℓ → Bool)
    (ω : Sample p bp) (primal : Bool) : List (Record p) :=
  ((List.finRange bp.n).filter fun i => bp.inp i ∈ J).map
      (fun i => stepRec ω primal i (σ (bp.inp i))) ++
    ((List.finRange bp.n).filter fun i => bp.inp i ∉ J).flatMap
      (fun i => [stepRec ω primal i false, stepRec ω primal i true])

/-- The initial database `DB(p, BP, (J, σ))` (p. 38), in this public order:
`s̃, s̃′, t̃, t̃′`, then the primal step matrices, then the dummy step matrices. -/
def initDB {p : ℕ} (bp : BP) (J : Finset (Fin bp.ℓ)) (σ : Fin bp.ℓ → Bool) (ω : Sample p bp) :
    List (Record p) :=
  [⟨1, NDim bp.n, .src, .prim 1, sTil ω⟩,
   ⟨1, NDim bp.n, .src, .dum 1, s'Til ω⟩,
   ⟨NDim bp.n, 1, .prim (bp.n + 1), .snk, tTil ω⟩,
   ⟨NDim bp.n, 1, .dum (bp.n + 1), .snk, t'Til ω⟩] ++
  programRecs bp J σ ω true ++ programRecs bp J σ ω false

/-- `|DB| = 4 + Σ_i (2 if inp i ∈ J else 4)`. -/
def dbSize (bp : BP) (J : Finset (Fin bp.ℓ)) : ℕ :=
  4 + ∑ i : Fin bp.n, if bp.inp i ∈ J then 2 else 4

/-- Adversary queries: `add(h, h′)`, `ConstMul(h, a)`, `mult(h, h′)`. -/
inductive Query (p : ℕ)
  | add (h h' : ℕ)
  | constMul (h : ℕ) (a : ZMod p)
  | mult (h h' : ℕ)

/-- `A + A′`, defined when both records have the same dimensions and colours. -/
def addRec {p : ℕ} (r r' : Record p) : Option (Record p) :=
  if h : r.rows = r'.rows ∧ r.cols = r'.cols ∧ r.lc = r'.lc ∧ r.rc = r'.rc then
    some ⟨r.rows, r.cols, r.lc, r.rc, r.mat + r'.mat.submatrix (Fin.cast h.1) (Fin.cast h.2.1)⟩
  else none

/-- `a · A`. -/
def constMulRec {p : ℕ} (r : Record p) (a : ZMod p) : Record p :=
  ⟨r.rows, r.cols, r.lc, r.rc, a • r.mat⟩

/-- `A × A′`, defined when `(cols, RC)` of `A` equals `(rows, LC)` of `A′`. -/
def multRec {p : ℕ} (r r' : Record p) : Option (Record p) :=
  if h : r.cols = r'.rows ∧ r.rc = r'.lc then
    some ⟨r.rows, r'.cols, r.lc, r'.rc, r.mat * r'.mat.submatrix (Fin.cast h.1) id⟩
  else none

open Classical in
/-- Reply to a computed record: the handle of the first existing record with the same dimensions,
colours and matrix (compared entrywise mod `p`), otherwise append it and return the new handle;
`none` (⊥) leaves the database unchanged. -/
noncomputable def respond {p : ℕ} (db : List (Record p)) : Option (Record p) →
    List (Record p) × Option ℕ
  | none => (db, none)
  | some r =>
    match db.findIdx? (fun x => decide (x = r)) with
    | some h => (db, some h)
    | none => (db ++ [r], some db.length)

/-- One step of the representation oracle. A missing handle or a dimension/colour mismatch
gives `none` (⊥). -/
noncomputable def oracleStep {p : ℕ} (db : List (Record p)) : Query p → List (Record p) × Option ℕ
  | .add h h' => respond db (do let r ← db[h]?; let r' ← db[h']?; addRec r r')
  | .constMul h a => respond db (do let r ← db[h]?; pure (constMulRec r a))
  | .mult h h' => respond db (do let r ← db[h]?; let r' ← db[h']?; multRec r r')

/-- A generic-colored-matrix-model adversary: random coins uniform on `Fin K`, `q` adaptive
queries (`next` sees the coins and all previous replies), and a final decision `out`. -/
structure Adversary (p : ℕ) where
  K : ℕ
  K_pos : 0 < K
  q : ℕ
  next : Fin K → List (Option ℕ) → Query p
  out : Fin K → List (Option ℕ) → Bool

/-- Run `k` more oracle interactions from the state `(database, replies so far)`. -/
noncomputable def runFrom {p : ℕ} (A : Adversary p) (c : Fin A.K) :
    ℕ → List (Record p) × List (Option ℕ) → List (Record p) × List (Option ℕ)
  | 0, s => s
  | k + 1, s =>
    let r := oracleStep s.1 (A.next c s.2)
    runFrom A c k (r.1, s.2 ++ [r.2])

/-- The view of `A` (its replies, together with its coins `c`) against the oracle initialized
with `DB(p, BP, (J, σ))` built from the sample `ω`. -/
noncomputable def view {p : ℕ} (bp : BP) (J : Finset (Fin bp.ℓ)) (σ : Fin bp.ℓ → Bool)
    (A : Adversary p) (c : Fin A.K) (ω : Sample p bp) : List (Option ℕ) :=
  (runFrom A c A.q (initDB bp J σ ω, [])).2

open Classical in
/-- `Pr[A outputs 1]`, over uniform coins and a uniform sample of `RND_p(BP)`. -/
noncomputable def acceptProb (p : ℕ) [Fact p.Prime] (bp : BP) (J : Finset (Fin bp.ℓ))
    (σ : Fin bp.ℓ → Bool) (A : Adversary p) : ℝ :=
  ((Finset.univ.filter fun x : Fin A.K × Sample p bp =>
      A.out x.1 (view bp J σ A x.1 x.2) = true).card : ℝ) /
    Fintype.card (Fin A.K × Sample p bp)

end GGHRSW.ColoredMatrix


