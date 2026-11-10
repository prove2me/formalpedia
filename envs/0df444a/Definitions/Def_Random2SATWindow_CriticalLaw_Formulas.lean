-- Prove2me | Definitions.Def_Random2SATWindow_CriticalLaw_Formulas
-- name    : Random2SATWindow_CriticalLaw_Formulas
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T03:40:09.946815+00:00
-- url     : https://prove2.me/theorems/edf60c85-7400-42ed-b104-9d71698cb813
-- title:
--   Random 2-SAT formulas, the implication digraph, the physical excess $R(F)$ and the two random models
-- statement:
--   Variables are `Fin n`; a literal is $(i,s)\in\mathrm{Fin}\,n\times\mathrm{Bool}$ ($s=$ true for $x_i$, false for $\bar x_i$), with complement $\bar u$ (`Literal.compl`).
--
--   * **Legal clauses and formulas** (Notations, printed p. 3; §5.1, p. 20). A legal clause is an unordered pair of literals (`Sym2`) on two *distinct* variables, so there are $N_n=4\binom n2=2n(n-1)$ of them (`numClauses n`; tautologies, repeated literals, ordered or repeated clauses are excluded). A formula is a finite set of legal clauses (`Formula n`), $|F|$ = `F.card`; $F\in\mathrm{SAT}$ (`Satisfiable F`) iff some assignment $\sigma:\mathrm{Fin}\,n\to\mathrm{Bool}$ makes a literal of every clause true.
--   * **Implication digraph** (2). The clause $u\vee v$ contributes the arcs $\bar u\to v$ and $\bar v\to u$, so $a\to b$ is an arc iff $\bar a\vee b\in F$ (`ImplArc F a b`); $u\rightsquigarrow v$ is reflexive–transitive reachability (`Reach`). `scc F u` is the strongly connected component of $u$ and `sccs F` = $\mathrm{SCC}(D(F))$.
--   * (4): $v(C)=|C|$ (`sccVerts`), $e(C)$ = number of arcs of $D(F)$ with both ends in $C$ (`sccArcs`), $r(C)=(e(C)-v(C))_+$ (`sccExcess`).
--   * (6): $R(F)=\tfrac12\sum_{C\in\mathrm{SCC}(D(F))}r(C)$ (`physExcess`), used only for $F\in\mathrm{SAT}$; there the components come in mirror pairs $\{C,\bar C\}$ of equal excess, so the sum is even and the halving (in $\mathbb N$) is exact: each unordered mirror pair is counted once.
--   * **The binomial model** $F(n,p)$: each legal clause independently with probability $p$, so $P(F(n,p)\in E)=\sum_{F\in E}p^{|F|}(1-p)^{N_n-|F|}$ (`probBinom n p E`, a polynomial in $p$), and `satProbBinom n p` $=P(F(n,p)\in\mathrm{SAT})$.
--   * (1): $p_n(x)=(1+xn^{-1/3})/(2n)$ (`critP n x`); $p_{n,q}(x)=P(F(n,p_n(x))\in\mathrm{SAT},\,R(F)=q)$ (`stratumProb n q x`); `condMomentR n r x` $=E[R^r\mathbf 1_{\mathrm{SAT}}]/P(\mathrm{SAT})$ under $F(n,p_n(x))$, the $r$-th moment of $R$ conditional on satisfiability.
--   * **The fixed-size model** (§5.1.11): $g_n(m)=P(F(n,m)\in\mathrm{SAT})=\#\{F:|F|=m,\ F\in\mathrm{SAT}\}/\binom{N_n}{m}$ (`satProbUniform n m`), and `critM n x` $=\lfloor n+xn^{2/3}\rfloor$ as a natural number.
--
--   **Formalization Note.** The finite-$n$ probabilities are explicit finite sums defined for every $n$ and $x$. $p_n(x)\in(0,1)$ and $0\le\lfloor n+xn^{2/3}\rfloor\le N_n$ hold for all large $n$ uniformly on compact $x$-sets, which is all the (eventual) limit statements use; for the finitely many other $n$, `critM` truncates a negative value to $0$ (`Int.toNat`) and $\binom{N_n}{m}=0$ gives $g_n(m)=0$ for $m>N_n$.
-- source:
--   Ravelomanana, Inside the Critical Window of Random 2-SAT, STOC 2027 submission (manuscript sha256 eef2fa67…), Notations (1)–(6), printed pp. 3–4 (PDF 5–6); §5.1, printed pp. 20–21 (PDF 22–23); §5.1.11, printed p. 54 (PDF 56)

import Mathlib

set_option autoImplicit false

open scoped BigOperators

namespace Random2SATWindow.CriticalLaw

/-! # Random 2-SAT formulas, the implication digraph and the two random models

Ravelomanana, *Inside the Critical Window of Random 2-SAT*, STOC 2027 submission (manuscript
sha256 eef2fa67…), Notations (1)–(6), printed pp. 3–4 (PDF 5–6); §5.1, printed pp. 20–21
(PDF 22–23); §5.1.11, printed p. 54 (PDF 56).

Conventions. The variables `x_1, …, x_n` are `Fin n`. A literal is a pair `(i, s)`:
`(i, true)` is `x_i` and `(i, false)` is `x̄_i`. A legal clause is an unordered pair of literals
(`Sym2`) on two distinct variables, so tautologies `x ∨ x̄`, repeated literals `x ∨ x`, ordered
clauses and repeated clauses are all excluded; there are `N_n = 4·C(n,2) = 2n(n-1)` of them.
A formula is a finite set of legal clauses. -/

/-- A literal on `n` variables: `(i, true)` is `x_i`, `(i, false)` is `x̄_i`. -/
abbrev Literal (n : ℕ) := Fin n × Bool

/-- The complementary literal `ū`. -/
def Literal.compl {n : ℕ} (u : Literal n) : Literal n := (u.1, !u.2)

/-- A legal clause: an unordered pair of literals whose two underlying variables are distinct. -/
abbrev LegalClause (n : ℕ) := {c : Sym2 (Literal n) // ¬ (c.map Prod.fst).IsDiag}

/-- A 2-SAT formula on `n` variables: a set of distinct legal clauses. `|F|` is `F.card`. -/
abbrev Formula (n : ℕ) := Finset (LegalClause n)

/-- `N_n`, the number of legal clauses (`= 2n(n-1)`). -/
def numClauses (n : ℕ) : ℕ := Fintype.card (LegalClause n)

/-- `F ∈ SAT`: some assignment makes a literal of every clause true. -/
def Satisfiable {n : ℕ} (F : Formula n) : Prop :=
  ∃ σ : Fin n → Bool, ∀ c ∈ F, ∃ u ∈ c.val, σ u.1 = u.2

/-- The arcs of the implication digraph `D(F)` (2): the clause `u ∨ v` contributes `ū → v` and
`v̄ → u`. Hence `a → b` is an arc iff `ā ∨ b` is a clause of `F`. -/
def ImplArc {n : ℕ} (F : Formula n) (a b : Literal n) : Prop :=
  ∃ c ∈ F, c.val = s(a.compl, b)

/-- Directed reachability `u ⇝ v` in `D(F)` (reflexive). -/
def Reach {n : ℕ} (F : Formula n) (u v : Literal n) : Prop :=
  Relation.ReflTransGen (ImplArc F) u v

open Classical in
/-- The strongly connected component of `D(F)` containing the literal `u`. -/
noncomputable def scc {n : ℕ} (F : Formula n) (u : Literal n) : Finset (Literal n) :=
  Finset.univ.filter (fun v => Reach F u v ∧ Reach F v u)

open Classical in
/-- `SCC(D(F))`, the set of strongly connected components (vertex sets) of `D(F)`. -/
noncomputable def sccs {n : ℕ} (F : Formula n) : Finset (Finset (Literal n)) :=
  Finset.univ.image (scc F)

/-- `v(C) = |V(C)|` (4). -/
def sccVerts {n : ℕ} (C : Finset (Literal n)) : ℕ := C.card

open Classical in
/-- `e(C) = |E(C)|` (4): the number of arcs of `D(F)` with both ends in `C`. -/
noncomputable def sccArcs {n : ℕ} (F : Formula n) (C : Finset (Literal n)) : ℕ :=
  ((C ×ˢ C).filter (fun p => ImplArc F p.1 p.2)).card

/-- `r(C) = (e(C) - v(C))_+` (4). -/
noncomputable def sccExcess {n : ℕ} (F : Formula n) (C : Finset (Literal n)) : ℕ :=
  ((sccArcs F C : ℤ) - (sccVerts C : ℤ)).toNat

/-- The total physical excess (6), `R(F) = ½ Σ_{C ∈ SCC(D(F))} r(C)`, used only for `F ∈ SAT`
(where the components come in mirror pairs of equal excess, so the sum is even and the halving
is exact; it counts each unordered mirror pair once). -/
noncomputable def physExcess {n : ℕ} (F : Formula n) : ℕ :=
  (∑ C ∈ sccs F, sccExcess F C) / 2

/-- The probability weight `p^{|F|} (1-p)^{N_n - |F|}` of the formula `F` in `F(n, p)`. -/
noncomputable def binomWeight {n : ℕ} (p : ℝ) (F : Formula n) : ℝ :=
  p ^ F.card * (1 - p) ^ (numClauses n - F.card)

open Classical in
/-- `P(F(n, p) ∈ E)`: each of the `N_n` legal clauses is present independently with probability
`p`. (A finite sum, a polynomial in `p`; it is a probability when `0 ≤ p ≤ 1`.) -/
noncomputable def probBinom (n : ℕ) (p : ℝ) (E : Formula n → Prop) : ℝ :=
  ∑ F : Formula n, if E F then binomWeight p F else 0

/-- `P(F(n, p) ∈ SAT)`. -/
noncomputable def satProbBinom (n : ℕ) (p : ℝ) : ℝ :=
  probBinom n p Satisfiable

/-- The critical clause probability (1): `p_n(x) = (1 + x n^{-1/3}) / (2n)`. -/
noncomputable def critP (n : ℕ) (x : ℝ) : ℝ :=
  (1 + x * (n : ℝ) ^ (-(1 / 3 : ℝ))) / (2 * n)

/-- `p_{n,q}(x) = P(F(n, p_n(x)) ∈ SAT, R(F) = q)` (§5.1, printed p. 21). -/
noncomputable def stratumProb (n q : ℕ) (x : ℝ) : ℝ :=
  probBinom n (critP n x) (fun F => Satisfiable F ∧ physExcess F = q)

open Classical in
/-- The `r`-th moment of `R(F(n, p_n(x)))` conditional on satisfiability:
`E[R^r 1_SAT] / P(SAT)`. -/
noncomputable def condMomentR (n r : ℕ) (x : ℝ) : ℝ :=
  (∑ F : Formula n, if Satisfiable F then (physExcess F : ℝ) ^ r * binomWeight (critP n x) F
      else 0) / satProbBinom n (critP n x)

open Classical in
/-- `g_n(m) = P(F(n, m) ∈ SAT)` (§5.1.11): `F(n, m)` is uniform among the `m`-subsets of the
`N_n` legal clauses, so `g_n(m) = #{F : |F| = m, F ∈ SAT} / C(N_n, m)`. -/
noncomputable def satProbUniform (n m : ℕ) : ℝ :=
  ((Finset.univ.filter (fun F : Formula n => F.card = m ∧ Satisfiable F)).card : ℝ) /
    ((numClauses n).choose m : ℝ)

/-- The critical clause count of Theorem 3.1, `m = ⌊n + x n^{2/3}⌋` (as a natural number; it is
negative only for finitely many `n` on each compact `x`-interval, where `toNat` gives `0`). -/
noncomputable def critM (n : ℕ) (x : ℝ) : ℕ :=
  (⌊(n : ℝ) + x * (n : ℝ) ^ (2 / 3 : ℝ)⌋).toNat

end Random2SATWindow.CriticalLaw


