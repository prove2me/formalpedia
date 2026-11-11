-- Prove2me | Definitions.Def_RSBDDHardness_PolyGap_Algebra
-- name    : RSBDDHardness_PolyGap_Algebra
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:25:25.03445+00:00
-- url     : https://prove2.me/theorems/3740a0f9-6ddd-47f7-a94a-446423fa524d
-- title:
--   Moments subset sum, monotone Exact 1-in-3 vectors, the quotient construction of §6.1 and the gap ⌊n^α⌋
-- statement:
--   This module fixes the algebraic objects of the paper.
--
--   1. **Moments subset sum** (Definition 3.2). For a finite set $S$ in a commutative ring $F$ the $j$-th moment is $\sum_{x\in S}x^j$. Given a finite set $A\subseteq F$, an integer $k$ and targets $m_1,\dots,m_d$, the yes-condition of $\mathrm{MSS}(d)$ asks for $S\subseteq A$ with
--   $$|S|=k,\qquad \sum_{x\in S}x^j=m_j\quad(1\le j\le d).$$
--   2. **Moment fibers** (§5.1). For a prime $q$ and $c\in\mathbb F_q^d$, $X_{c,h}=\{x\in\mathbb F_q^h:\sum_i x_i^j=c_j,\ 1\le j\le d\}$, $Z_r=X_{c,h}\cap\{x_r=0\}$ and $Y_{r,s}=X_{c,h}\cap\{x_r=x_s\}$.
--   3. **Monotone Exact 1-in-3 formulas** (§3.4). A formula has variables $z_1,\dots,z_m$ and clauses $C_1,\dots,C_c$, each a triple of variables without negations. An assignment $b\in\{0,1\}^m$ satisfies it in the Exact 1-in-3 sense when every clause has exactly one true variable. A formula is *cubic* when it is nonempty, every clause has three distinct variables, every variable occurs in exactly three clauses, and hence $c=m$. With $\chi_r(i,b)=b\cdot\mathbf 1[z_i\in C_r]$ the vectors of (11) are
--   $$v_{i,b}=(e_i;\chi_1(i,b),\dots,\chi_c(i,b))\in\mathbb F_q^{m+c},\qquad T=(1^m;1^c).$$
--   4. **The extension field of §6.1.** For $P\in\mathbb F_q[Z]$ put $\mathbb K=\mathbb F_q[Z]/(P)$ and $\theta=Z \bmod P$. When $P$ is monic of degree $L$, every $x\in\mathbb K$ is uniquely $\sum_{r<L}x_r\theta^r$. Define $H=\operatorname{span}_{\mathbb F_q}\{1,\theta,\dots,\theta^t\}$, the quotient map $\pi(x)=(x_{t+1},\dots,x_{2t})$ of (25), the section $\sigma(u_1,\dots,u_t)=\sum_r u_r\theta^{t+r}$, the product spaces $U^{\langle 0\rangle}=\mathbb F_q\cdot1$ and $U^{\langle s\rangle}=\operatorname{span}\{u_1\cdots u_s:u_i\in U\}$, and $\operatorname{span}\{\beta^j:\beta\in B\}$.
--   5. **Direction sets and the pool** (§6.2, §7). A finite $B\subseteq\mathbb K$ is projectively distinct when no element is a nonzero $\mathbb F_q$-multiple of another. It is a direction set for cutoff $d$ when $B\subseteq H\setminus\{0\}$, it is projectively distinct, $\operatorname{span}B=H$ (31) and $\operatorname{span}\{\beta^j:\beta\in B\}=\mathbb K$ for $2\le j\le d$ (32). The pool is $D=\bigcup_{\beta\in B}\beta\,\mathbb F_q^\times$.
--   6. A linear functional $\lambda:\mathbb K\to\mathbb F_q$ is given by its values $\lambda(\theta^r)$ on the power basis.
--   7. **The gap.** For rational $\alpha$, $\operatorname{gap}_\alpha(n)=\lfloor n^\alpha\rfloor$, computed exactly from the real power.
--
--   These are the shared objects of every milestone.
--
--   **Formalization Note** $\mathbb K$ is `AdjoinRoot P`, a commutative ring for every $P$ and a field when $P$ is irreducible; field-ness is never assumed by the definitions, and the theorems state primality and irreducibility as hypotheses. The coordinate of $x$ is read from the remainder of a representative modulo the monic $P$ (and is $0$ for a non-monic $P$, which never occurs). Variables and clauses are indexed from $0$. $\mathbb F_q^\times$ is written as the multiples $c\beta$, $c=1,\dots,q-1$. Indexed targets are functions on $\mathbb N$ of which only the values at $1,\dots,d$ matter.
-- source:
--   Daqing Wan, Jun Zhang, NP-Hardness of Bounded Distance Decoding for Reed–Solomon Codes, STOC 2027 submission #449 (October 2026), Definitions 3.2 (PDF p. 11), §3.4 eq. (11) (PDF pp. 12–13), §5.1 (PDF pp. 14–15), §6.1 eqs. (6), (25), (27) (PDF pp. 18–20), (31)–(32) and §7 (PDF pp. 20–22); PDF SHA-256 d60d9a54b73aa972494f130439dc6e07f8c7b33556741f8324d22cf45218e22b

import Mathlib

set_option autoImplicit false

open scoped BigOperators
open Classical

noncomputable section

namespace RSBDDHardness.PolyGap

/-! ## Moments subset sum (Definition 3.2, PDF 11) -/

/-- The `j`-th moment (power sum) `∑_{x ∈ S} x ^ j` of a finite set `S`. -/
def moment {F : Type} [CommRing F] (S : Finset F) (j : ℕ) : F :=
  ∑ x ∈ S, x ^ j

/-- `S` realizes the moment targets `m 1, …, m d`: `∑_{x∈S} x^j = m j` for `1 ≤ j ≤ d`
(equation (10)). Only the values `m 1, …, m d` matter. -/
def RealizesMoments {F : Type} [CommRing F] (S : Finset F) (d : ℕ) (m : ℕ → F) : Prop :=
  ∀ j : ℕ, 1 ≤ j → j ≤ d → moment S j = m j

/-- The yes-condition of `MSS(d)` (Definition 3.2): some `S ⊆ A` with `|S| = k`
realizes the targets `m 1, …, m d`. -/
def MSS {F : Type} [CommRing F] (A : Finset F) (k d : ℕ) (m : ℕ → F) : Prop :=
  ∃ S : Finset F, S ⊆ A ∧ S.card = k ∧ RealizesMoments S d m

/-! ## Moment fibers of §5.1 (PDF 14–15) -/

/-- `X_{c,h} = {x ∈ 𝔽_q^h : ∑_i x_i^j = c_j, 1 ≤ j ≤ d}`. -/
def Xfib (q h d : ℕ) (c : ℕ → ZMod q) : Set (Fin h → ZMod q) :=
  {x | ∀ j : ℕ, 1 ≤ j → j ≤ d → ∑ i, x i ^ j = c j}

/-- `Z_r = X_{c,h} ∩ {x_r = 0}`. -/
def Zfib (q h d : ℕ) (c : ℕ → ZMod q) (r : Fin h) : Set (Fin h → ZMod q) :=
  {x | x ∈ Xfib q h d c ∧ x r = 0}

/-- `Y_{r,s} = X_{c,h} ∩ {x_r = x_s}` (used for `r ≠ s`). -/
def Yfib (q h d : ℕ) (c : ℕ → ZMod q) (r s : Fin h) : Set (Fin h → ZMod q) :=
  {x | x ∈ Xfib q h d c ∧ x r = x s}

/-! ## Monotone Exact 1-in-3 formulas and their vectors (§3.4, PDF 12–13) -/

/-- A monotone Exact 1-in-3 formula on the variables `z_0, …, z_{m-1}`: a list of clauses,
each clause a triple of variables (no negations). -/
structure OneInThree where
  /-- Number of variables. -/
  m : ℕ
  /-- The clauses `C_r`, each a triple `(z_{i(r,1)}, z_{i(r,2)}, z_{i(r,3)})`. -/
  clauses : List (Fin 3 → Fin m)

namespace OneInThree

/-- Number of clauses. -/
def c (φ : OneInThree) : ℕ := φ.clauses.length

/-- The `r`-th clause. -/
def clause (φ : OneInThree) (r : Fin φ.c) : Fin 3 → Fin φ.m := φ.clauses.get r

/-- Every clause contains three distinct variables. -/
def DistinctClauses (φ : OneInThree) : Prop :=
  ∀ r : Fin φ.c, Function.Injective (φ.clause r)

/-- Variable `i` occurs in clause `r`. -/
def Occurs (φ : OneInThree) (i : Fin φ.m) (r : Fin φ.c) : Prop :=
  ∃ k : Fin 3, φ.clause r k = i

/-- Cubic monotone instance (§3.4): nonempty, every clause has three distinct variables, and
every variable occurs in exactly three clauses. (Then the numbers of clauses and variables
agree; this is stated explicitly as well.) -/
def IsCubic (φ : OneInThree) : Prop :=
  1 ≤ φ.m ∧ φ.DistinctClauses ∧ φ.c = φ.m ∧
    ∀ i : Fin φ.m, (Finset.univ.filter fun r : Fin φ.c => φ.Occurs i r).card = 3

/-- The assignment `b` satisfies `φ` in the Exact 1-in-3 sense: exactly one variable of every
clause is true. -/
def ExactSat (φ : OneInThree) (b : Fin φ.m → Bool) : Prop :=
  ∀ r : Fin φ.c, (Finset.univ.filter fun k : Fin 3 => b (φ.clause r k) = true).card = 1

/-- `φ` is Exact 1-in-3 satisfiable. -/
def Satisfiable (φ : OneInThree) : Prop := ∃ b : Fin φ.m → Bool, φ.ExactSat b

/-- `χ_r(i, b) = b · 1[z_i ∈ C_r]`. -/
def chi (φ : OneInThree) (q : ℕ) (r : Fin φ.c) (i : Fin φ.m) (b : Bool) : ZMod q :=
  if b = true ∧ φ.Occurs i r then 1 else 0

/-- The vector `v_{i,b} = (e_i ; χ_1(i,b), …, χ_c(i,b)) ∈ 𝔽_q^{m+c}` of (11). -/
def vec (φ : OneInThree) (q : ℕ) (i : Fin φ.m) (b : Bool) : Fin (φ.m + φ.c) → ZMod q :=
  Fin.append (fun i' : Fin φ.m => if i' = i then 1 else 0) (fun r => φ.chi q r i b)

/-- The target vector `T = (1^m ; 1^c)`. -/
def target (φ : OneInThree) (q : ℕ) : Fin (φ.m + φ.c) → ZMod q := fun _ => 1

end OneInThree

/-! ## The extension field objects of §6.1 (PDF 18–20) -/

section Field

variable {q : ℕ}

/-- `θ = Z mod P`. -/
abbrev theta (P : Polynomial (ZMod q)) : AdjoinRoot P := AdjoinRoot.root P

/-- Coordinate `x_r` of `x` in the power basis `1, θ, …, θ^{L-1}` of `𝔽_q[Z]/(P)`, read off the
remainder of a representative modulo the monic `P`. (For non-monic `P`, which never occurs in
the source, the value is `0`.) -/
def coord (P : Polynomial (ZMod q)) (x : AdjoinRoot P) (r : ℕ) : ZMod q :=
  if h : P.Monic then (AdjoinRoot.modByMonicHom h x).coeff r else 0

/-- `H = span_{𝔽_q} {1, θ, …, θ^t}` (equation (6)). -/
def Hsp (P : Polynomial (ZMod q)) (t : ℕ) : Submodule (ZMod q) (AdjoinRoot P) :=
  Submodule.span (ZMod q) (Set.range fun i : Fin (t + 1) => theta P ^ (i : ℕ))

/-- The quotient map `π(x) = (x_{t+1}, …, x_{2t})` of (25). -/
def piMap (P : Polynomial (ZMod q)) (t : ℕ) (x : AdjoinRoot P) : Fin t → ZMod q :=
  fun r => coord P x (t + 1 + (r : ℕ))

/-- The linear section `σ(u_1, …, u_t) = ∑_r u_r θ^{t+r}`. -/
def sigma (P : Polynomial (ZMod q)) (t : ℕ) (u : Fin t → ZMod q) : AdjoinRoot P :=
  ∑ r : Fin t, u r • theta P ^ (t + 1 + (r : ℕ))

/-- `U^{⟨s⟩} = span_{𝔽_q} {u_1 ⋯ u_s : u_i ∈ U}`; for `s = 0` the empty product gives
`U^{⟨0⟩} = 𝔽_q · 1`. -/
def Upow (P : Polynomial (ZMod q)) (U : Submodule (ZMod q) (AdjoinRoot P)) (s : ℕ) :
    Submodule (ZMod q) (AdjoinRoot P) :=
  Submodule.span (ZMod q) {x | ∃ u : Fin s → AdjoinRoot P, (∀ i, u i ∈ U) ∧ x = ∏ i, u i}

/-- `span_{𝔽_q} {β^j : β ∈ B}`. -/
def powSpan (P : Polynomial (ZMod q)) (B : Set (AdjoinRoot P)) (j : ℕ) :
    Submodule (ZMod q) (AdjoinRoot P) :=
  Submodule.span (ZMod q) ((fun β => β ^ j) '' B)

/-- Projectively distinct: no element of `B` is a nonzero `𝔽_q`-multiple of another element. -/
def ProjDistinct (P : Polynomial (ZMod q)) (B : Finset (AdjoinRoot P)) : Prop :=
  ∀ β ∈ B, ∀ β' ∈ B, β ≠ β' → ∀ c : ZMod q, c ≠ 0 → β ≠ c • β'

/-- A direction set as in Lemma 6.3 / §7 for moment cutoff `d`: `B ⊆ H ∖ {0}`, projectively
distinct, `span B = H` (31), and `span {β^j : β ∈ B} = 𝕂` for `2 ≤ j ≤ d` (32). -/
def IsDirectionSet (P : Polynomial (ZMod q)) (t d : ℕ) (B : Finset (AdjoinRoot P)) : Prop :=
  (∀ β ∈ B, β ∈ Hsp P t ∧ β ≠ 0) ∧ ProjDistinct P B ∧
    Submodule.span (ZMod q) (B : Set (AdjoinRoot P)) = Hsp P t ∧
    ∀ j : ℕ, 2 ≤ j → j ≤ d → powSpan P (B : Set (AdjoinRoot P)) j = ⊤

/-- The auxiliary pool `D = ⨆_{β ∈ B} β 𝔽_q^×`, with `𝔽_q^× = {1, …, q-1}`. -/
def pool (P : Polynomial (ZMod q)) (B : Finset (AdjoinRoot P)) : Finset (AdjoinRoot P) :=
  B.biUnion fun β => (Finset.Ico 1 q).image fun c : ℕ => (c : ZMod q) • β

/-- The linear functional `λ : 𝕂 → 𝔽_q` with prescribed values `λ(θ^r) = vals[r]` on the
power basis, `0 ≤ r < L`: `λ(x) = ∑_{r<L} x_r · vals[r]`. -/
def lamOf (P : Polynomial (ZMod q)) (vals : List ℕ) (x : AdjoinRoot P) : ZMod q :=
  ∑ r ∈ Finset.range vals.length, coord P x r * (vals.getD r 0 : ZMod q)

end Field

/-! ## The exact gap `⌊n^α⌋` -/

/-- `⌊n^α⌋`, computed exactly with real powers (not floating point). -/
def gap (α : ℚ) (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (α : ℝ)⌋₊

end RSBDDHardness.PolyGap


