-- Prove2me | Definitions.Def_SparseSDP_TwoSided_Supplement_solve62
-- name    : SparseSDP_TwoSided_Supplement_solve62
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:32:52.427203+00:00
-- url     : https://prove2.me/theorems/ef1ebe9f-3fb7-456f-b941-dec6154f0792
-- title:
--   Theorem 6.2's solver: Algorithm 6, the primal phase and certificate selection, as charged programs
-- statement:
--   The direct classical Gibbs–MMWU solver at a target $g$, accuracy $\varepsilon$ and failure probability $\delta$, reading the SDP instance through its sparse oracle.
--
--   1. **Algorithm 6 (first phase).** Set $A_0=-C$, $b_0=-g$, $\theta=\varepsilon/(6Rr)$, $T=\lceil\log(2n)/\theta^2\rceil$, $y^{(1)}=0$. In round $t$, with $H_t=\sum_{j=0}^m y^{(t)}_jA_j$, Algorithm 5 estimates $\operatorname{Tr}(A_j\Omega_{H_t})$, $0\le j\le m$, to accuracy $\theta/2$ with failure probability $\delta/(2T)$. The **θ-oracle** then returns a point $\tilde y$ of
--   $$
--   \hat P=\Big\{\tilde y\ge0:\ b^\top\tilde y\le0,\ \sum_{j=0}^m\tilde y_j\hat\mu_{t,j}\ge-\tfrac\theta2,\ \tilde y_0=\tfrac1{2r},\ \|\tilde y\|_1\le1\Big\}
--   $$
--   with at most two nonzeros among $1,\dots,m$, or certifies $\hat P=\emptyset$, which ends the phase with "OPT $>g$". Otherwise $y^{(t+1)}=y^{(t)}+\theta\tilde y$. After $T$ rounds it returns $y_{\mathrm{out}}=\frac{2r}{T\theta}y^{(T+1)}+\frac\varepsilon Re_1-e_0$ with coordinate $0$ dropped.
--   2. **Primal phase.** With $\hat A_j=\operatorname{diag}(A_j,0)$, thresholds $b_j/R$ ($0\le j\le m$), $P=\operatorname{diag}(I_n,0)$, $\alpha_P=\min\{1/4,\varepsilon/(4Rr)\}$, $\eta_P=\alpha_P/2$, $\beta=\min\{1/2,\varepsilon/(2Rr)\}$, it runs at most $T_P=\lceil4\log(2(n+1))/\alpha_P^2\rceil$ rounds from zero coefficients. Each round one Algorithm 5 call estimates $\operatorname{Tr}(\hat A_j\rho)$ and $q=\operatorname{Tr}(P\rho)$ to accuracy $\min\{\alpha_P/2,\beta\}$; if some $j$ has $\hat\mu_j>b_j/R+3\alpha_P/2$, the first such $j$ gets $y_j\leftarrow y_j+\eta_P$; otherwise the phase returns $y'=y$ and $z=R\max\{0,\min\{1,\hat q\}\}$.
--   3. **Certificate selection.** Run the first phase with internal accuracy $\varepsilon/2$; return its dual vector if it returns one, else run the primal phase.
--
--   The output is either a primal certificate $(y',z)$, defining
--   $$
--   X=z\cdot\frac{\exp\big(y_0'C-\sum_{j=1}^my_j'A_j\big)}{\operatorname{Tr}\exp\big(y_0'C-\sum_{j=1}^my_j'A_j\big)},
--   $$
--   or a dual vector $y$. A primal output is **valid** if $y'\ge0$, $z\in[0,R]$, $\langle C,X\rangle\ge g-\varepsilon$ and $\langle A_j,X\rangle\le b_j+\varepsilon/r$ for all $j$; a dual output is valid if $y\ge0$, $\sum_jy_jA_j-C\succeq-\varepsilon I$ and $b^\top y\le g+\varepsilon$. The **support** is the number of nonzero coefficients.
--
--   **Formalization Note** The θ-oracle's geometric step ([vAGGdW20, Lemma 16]) is not written out in the paper; it is one exact primitive with the specification of p. 43, charged $16(m+1)$ ("It uses $O(m)$ classical time"). The accumulated Hamiltonian is a list of coefficient increments, at most three per round in the first phase and one in the primal phase (Eq. (220)). If all $T_P$ primal rounds return an index (excluded on the success event), the phase returns $z=0$.
-- source:
--   Brandão, Dalzell, Gilyén, Vasconcelos, Solving Sparse SDPs in Sublinear Time, arXiv:2609.40302, Algorithm 6, p. 41; §6.2, Eqs. (215)–(221), pp. 41–42; proof of Theorem 6.2, p. 43; Corollary 6.1, p. 40

import Mathlib
import Definitions.Def_SparseSDP_TwoSided_SparseOracle
import Definitions.Def_SparseSDP_TwoSided_Supplement_alg5

open Matrix
open scoped ComplexOrder

namespace SparseSDP.TwoSided.Supplement

open SparseSDP.TwoSided

variable {n m : ℕ} {I : Instance ℂ n m}

/-- Row `i` of `A₀ := −C` (index `0`) or of `Aⱼ` (index `j ≥ 1`, the paper's `Aⱼ`, Lean's
`I.A (j − 1)`), read through the instance's sparse oracle (Algorithm 6, line 1, p. 41). The sign of
`−C` is applied to each entry read, one operation per entry. -/
noncomputable def objRead (orc : SparseOracle I) (j : Fin (m + 1)) (i : Fin n) :
    Prog (CRow n) :=
  if h : j.val = 0 then do
    let row ← readRow orc none i
    op row.length (row.map fun p => (p.1, -p.2))
  else readRow orc (some ⟨j.val - 1, by omega⟩) i

/-- The reader of `A₀ = −C, A₁, …, A_m`. -/
noncomputable def objAccess (orc : SparseOracle I) : CRowAccess (Fin (m + 1)) n := ⟨objRead orc⟩

/-- Row `i` of the lifted matrices of the primal phase (§6.2, p. 42), in dimension `n + 1`: index
`j ≤ m` is `Â_j = diag(A_j, 0)` (with `A₀ = −C`), index `m + 1` is `P = diag(I_n, 0)`. -/
noncomputable def liftRead (orc : SparseOracle I) (j : Fin (m + 2)) (i : Fin (n + 1)) :
    Prog (CRow (n + 1)) :=
  if hi : i.val < n then
    if hj : j.val < m + 1 then do
      let row ← objRead orc ⟨j.val, hj⟩ ⟨i.val, hi⟩
      op row.length (row.map fun p => (Fin.castSucc p.1, p.2))
    else op 1 [(i, 1)]
  else op 1 []

/-- The reader of `Â₀, …, Â_m, P`. -/
noncomputable def liftAccess (orc : SparseOracle I) : CRowAccess (Fin (m + 2)) (n + 1) :=
  ⟨liftRead orc⟩

/-- The set `P̂` of the proof of Theorem 6.2 (p. 43), with the estimates `μ̂` and the thresholds
`b̃ = (b₀, b₁, …, b_m)`, `b₀ = −g`: `ỹ ≥ 0`, `b̃⊤ỹ ≤ 0`, `∑ⱼ ỹⱼ μ̂ⱼ ≥ −θ/2`, `ỹ₀ = 1/(2r)` and
`‖ỹ‖₁ ≤ 1` (that is, `∑_{j≥1} ỹⱼ ≤ 1 − 1/(2r)`), the set `P_θ` of Eq. (216), p. 41, with its payoff
condition replaced as on p. 43. -/
def PHat (r θ : ℝ) (bt μ : Fin (m + 1) → ℝ) : Set (Fin (m + 1) → ℝ) :=
  {y | (∀ j, 0 ≤ y j) ∧ ∑ j, bt j * y j ≤ 0 ∧ -(θ / 2) ≤ ∑ j, y j * μ j ∧ y 0 = 1 / (2 * r) ∧
    ∑ j, y j ≤ 1}

/-- At most two nonzero coordinates among `1, …, m`. -/
def Sparse2 (y : Fin (m + 1) → ℝ) : Prop :=
  (Finset.univ.filter fun j : Fin (m + 1) => j ≠ 0 ∧ y j ≠ 0).card ≤ 2

open Classical in
/-- Primitive: the θ-oracle's geometric step ([vAGGdW20, Lemma 16], as used on p. 43). It returns a
point of `P̂` with at most two nonzero coordinates among `1, …, m`, or `none` exactly when no such
point exists, and is charged `16 (m + 1)` ("It uses `O(m)` classical time", p. 43).

**Formalization Note.** The routine is not written out in the paper; it is modelled as one exact
primitive with the specification of p. 43, like the tridiagonal primitives of the base mission. With
`ỹ₀` fixed, `P̂` is cut out of `ỹ ≥ 0` by the two remaining payoff inequalities and the mass bound;
maximizing the payoff under the other two leaves a basic solution with at most two nonzeros, so
`none` is returned exactly when `P̂ = ∅`. -/
noncomputable def thetaOracle (r θ : ℝ) (bt μ : Fin (m + 1) → ℝ) :
    Prog (Option (Fin (m + 1) → ℝ)) :=
  op (16 * (m + 1))
    (if h : ∃ y, y ∈ PHat r θ bt μ ∧ Sparse2 y then some (Classical.choose h) else none)

/-- `T = ⌈log(2n)/θ²⌉` (Algorithm 6, line 2). -/
noncomputable def rounds6 (n : ℕ) (θ : ℝ) : ℕ := ⌈Real.log (2 * n) / θ ^ 2⌉₊

/-- Read `b̃ = (−g, b₁, …, b_m)` through `qB` (Algorithm 6, line 1). -/
noncomputable def readThresholds (orc : SparseOracle I) (g : ℝ) : Prog (Fin (m + 1) → ℝ) := do
  let mut bt : Fin (m + 1) → ℝ ← op 1 (Function.update 0 0 (-g))
  for j in List.finRange m do
    tick 1
    let bj ← qB orc j
    bt ← op 1 (Function.update bt j.succ bj)
  pure bt

/-- **Algorithm 6** (Direct classical Gibbs–MMWU solver, p. 41), first phase, as a charged
program, at target `g`, accuracy `ε`, failure probability `δ`.

Brandão, Dalzell, Gilyén, Vasconcelos, *Solving Sparse SDPs in Sublinear Time*, arXiv:2609.40302,
Algorithm 6, p. 41; proof of Theorem 6.2, p. 43.

Lines 1–2: `A₀ = −C`, `b₀ = −g`, `θ = ε/(6Rr)`, `T = ⌈log(2n)/θ²⌉`, `y⁽¹⁾ = 0`. Each round: `H_t`
is kept as the list of the coefficient increments (at most three per round, Eq. (220)); Algorithm 5
estimates `Tr(AⱼΩ_{H_t})`, `0 ≤ j ≤ m`, with `ω = 1`, accuracy `cθ` for `c = 1/2` and failure
probability `δ/(2T)` (line 5); the θ-oracle returns `ỹ⁽ᵗ⁾ ∈ P̂` or certifies `P̂ = ∅` (line 6); on
`∅` the output is `none`, "OPT > g" (lines 7–8); else `y⁽ᵗ⁺¹⁾ = y⁽ᵗ⁾ + θỹ⁽ᵗ⁾` (line 9). Lines 10–12:
`y_out = (2r/(Tθ)) y⁽ᵀ⁺¹⁾ + (ε/R)e₁ − e₀`, coordinate `0` dropped.

**Formalization Note.** `c = 1/2` is the choice made explicit in the proof (p. 43: "take `c ≤ 1/2`").
The bound `B_H` passed to Algorithm 5 is the current coefficient mass `∑ y_j⁽ᵗ⁾` (the coefficients
are nonnegative). The paper's `e₁` is coordinate `1` of `Fin (m + 1)`, i.e. Lean's `I.A 0`. -/
noncomputable def alg6 [NeZero n] (P : Consts5) (orc : SparseOracle I) (R r ε g δ : ℝ) :
    Prog (Option (Fin m → ℝ)) := do
  -- line 1
  let bt ← readThresholds orc g
  -- line 2
  let θ ← op 3 (ε / (6 * R * r))
  let T ← op 8 (rounds6 n θ)
  let mut y : Fin (m + 1) → ℝ := 0
  let mut Hl : List (Fin (m + 1) × ℝ) := []
  let mut empty : Bool := false
  -- lines 3–9
  for _t in List.range T do
    tick 1
    let BH ← op (Hl.length + 1) (Hl.map Prod.snd).sum
    -- line 5
    let μ ← alg5 P (objAccess orc) Hl BH (m + 1) (objAccess orc) 1 (θ / 2) (δ / (2 * T))
    -- line 6
    let o ← thetaOracle r θ bt μ
    tick 1
    match o with
    | none =>
      -- lines 7–8
      empty := true
      break
    | some yt =>
      -- line 9
      let y' ← op (2 * (m + 1)) (y + θ • yt)
      y := y'
      for j in List.finRange (m + 1) do
        tick 2
        if yt j ≠ 0 then
          Hl := Hl ++ [(j, θ * yt j)]
  tick 1
  if empty then
    pure none
  else
    -- lines 10–12
    let yo ← op (4 * (m + 1) + 4) (fun j : Fin (m + 1) =>
      2 * r / (T * θ) * y j + (if j.val = 1 then ε / R else 0) - (if j.val = 0 then 1 else 0))
    let yd ← op m (fun j : Fin m => yo j.succ)
    pure (some yd)

/-- The primal phase of §6.2 (p. 42) as a charged program, at target `g`, accuracy `ε`, failure
probability `δ`: lifted matrices `Â_j = diag(A_j, 0)` with thresholds `b_j/R` (`0 ≤ j ≤ m`,
`A₀ = −C`, `b₀ = −g`); `α_P = min{1/4, ε/(4Rr)}`, `η_P = α_P/2`, `β = min{1/2, ε/(2Rr)}`; at most
`T_P = ⌈4 log(2(n + 1))/α_P²⌉` rounds from zero coefficients. Each round, one Algorithm 5 call
estimates `Tr(Â_jρ)` for all `j` and `q = Tr(Pρ)`, `P = diag(I_n, 0)`, at accuracy `min{α_P/2, β}`
with failure probability `δ/(2T_P)`; Corollary 6.1's threshold scan returns the first `j` with
`μ̂_j > b_j/R + 3α_P/2`, and then `y⁽ᵗ⁺¹⁾ = y⁽ᵗ⁾ + η_P e_j` (Eq. (219)); if no index is returned,
the output is the coefficients `y` and `z = R max{0, min{1, q̂}}`.

**Formalization Note.** If all `T_P` rounds return an index (excluded on the success event by
Eq. (223)), the output is the final coefficients with `z = 0`. -/
noncomputable def primalPhase [NeZero n] (P : Consts5) (orc : SparseOracle I) (R r ε g δ : ℝ) :
    Prog ((Fin (m + 1) → ℝ) × ℝ) := do
  let bt ← readThresholds orc g
  let αP ← op 4 (min (1 / 4) (ε / (4 * R * r)))
  let ηP ← op 1 (αP / 2)
  let β ← op 4 (min (1 / 2) (ε / (2 * R * r)))
  let TP ← op 10 ⌈4 * Real.log (2 * ((n : ℝ) + 1)) / αP ^ 2⌉₊
  let acc ← op 2 (min (αP / 2) β)
  let mut y : Fin (m + 1) → ℝ := 0
  let mut Hl : List (Fin (m + 2) × ℝ) := []
  let mut z : ℝ := 0
  for _t in List.range TP do
    tick 1
    let BH ← op (Hl.length + 1) (Hl.map Prod.snd).sum
    let μ ← alg5 P (liftAccess orc) Hl BH (m + 2) (liftAccess orc) 1 acc (δ / (2 * TP))
    -- Corollary 6.1: threshold scan
    let mut found : Option (Fin (m + 1)) := none
    for j in List.finRange (m + 1) do
      tick 4
      if found.isNone ∧ bt j / R + 3 * αP / 2 < μ j.castSucc then
        found := some j
    match found with
    | some j =>
      y ← op 2 (Function.update y j (y j + ηP))
      tick 1
      Hl := Hl ++ [(j.castSucc, ηP)]
    | none =>
      z ← op 6 (R * max 0 (min 1 (μ (Fin.last (m + 1)))))
      break
  pure (y, z)

/-- The output of Theorem 6.2's solver: a primal certificate `(y′, z)`, `y′ ∈ ℝ^{m+1}`, or a dual
vector `y ∈ ℝᵐ`. -/
inductive Cert62 (m : ℕ) where
  /-- Coefficients `y′ = (y′₀, …, y′_m)` and the scalar `z` of Eq. (221). -/
  | primal (y : Fin (m + 1) → ℝ) (z : ℝ)
  /-- A dual vector `y = (y₁, …, y_m)`. -/
  | dual (y : Fin m → ℝ)

/-- The output is a primal certificate. -/
def Cert62.IsPrimal : Cert62 m → Prop
  | .primal _ _ => True
  | .dual _ => False

/-- The support of the coefficient representation: the number of nonzero coefficients. -/
noncomputable def Cert62.support : Cert62 m → ℕ
  | .primal y _ => (Finset.univ.filter fun j => y j ≠ 0).card
  | .dual y => (Finset.univ.filter fun j => y j ≠ 0).card

/-- **Theorem 6.2's solver** (certificate-selection rule of the proof, p. 43): run Algorithm 6 at
target `g` with internal accuracy `ε/2`; return its dual certificate if it returns one; otherwise
(it certified `OPT > g`) run the primal phase at accuracy `ε`. Both phases receive failure
probability `δ`, so the per-call budgets `δ/(2T)` and `δ/(2T_P)` sum to at most `δ`. -/
noncomputable def solve62 [NeZero n] (P : Consts5) (orc : SparseOracle I) (R r ε g δ : ℝ) :
    Prog (Cert62 m) := do
  let e2 ← op 1 (ε / 2)
  let o ← alg6 P orc R r e2 g δ
  tick 1
  match o with
  | some y => pure (.dual y)
  | none => do
    let yz ← primalPhase P orc R r ε g δ
    pure (.primal yz.1 yz.2)

/-- The implicit primal matrix of Eq. (221), p. 43:
`X = z · exp(y′₀C − ∑_{j=1}^m y′ⱼAⱼ) / Tr exp(y′₀C − ∑_{j=1}^m y′ⱼAⱼ)`. -/
noncomputable def primalMat (I : Instance ℂ n m) (y : Fin (m + 1) → ℝ) (z : ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  let M := (y 0 : ℂ) • I.C - ∑ j : Fin m, (y j.succ : ℂ) • I.A j
  ((z : ℂ) / Matrix.trace (NormedSpace.exp M)) • NormedSpace.exp M

/-- Validity of a returned certificate (Theorem 6.2, items 1 and 2, p. 43): a primal output has
`y′ ≥ 0`, `z ∈ [0, R]`, `⟨C, X⟩ ≥ g − ε` and `⟨Aⱼ, X⟩ ≤ bⱼ + ε/r` for every `j`, with `X` of
Eq. (221); a dual output has `y ≥ 0`, `∑ⱼ yⱼAⱼ − C ⪰ −εI` and `b⊤y ≤ g + ε` (Eq. (222)). -/
def Cert62.Valid (I : Instance ℂ n m) (R r ε g : ℝ) : Cert62 m → Prop
  | .primal y z => (∀ j, 0 ≤ y j) ∧ 0 ≤ z ∧ z ≤ R ∧ g - ε ≤ hs I.C (primalMat I y z) ∧
      ∀ j, hs (I.A j) (primalMat I y z) ≤ I.b j + ε / r
  | .dual y => (∀ j, 0 ≤ y j) ∧ (adj I.A y - I.C + (ε : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosSemidef ∧
      ∑ j, I.b j * y j ≤ g + ε

end SparseSDP.TwoSided.Supplement


