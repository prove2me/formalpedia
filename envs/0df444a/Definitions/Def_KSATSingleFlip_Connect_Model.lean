-- Prove2me | Definitions.Def_KSATSingleFlip_Connect_Model
-- name    : KSATSingleFlip_Connect_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T21:05:54.062451+00:00
-- url     : https://prove2.me/theorems/ba1cd852-5713-438d-8510-a4c5f2152462
-- title:
--   Random $k$-SAT model: clauses, formulas, solutions, paths, Poissonised laws and the solution-count constants
-- statement:
--   The random formula and the geometry of its solution space (model paragraph, p. 2; §2.1, p. 10; §2.3, p. 13).
--
--   * Variables are `Fin n` (the paper's variable $i+1$ is `i`); assignments are `V → Bool`. A clause on a variable type $V$ is a map $C : V \to \mathrm{Option\ Bool}$; $C(i) = \mathrm{some}\ s$ means $C$ has a literal on $i$, true under $\sigma$ iff $\sigma(i) = s$. The published `OAI.FixedClauseThreshold.ProperClause n k` is such a map with exactly $k$ signed variables, and `Formula n k m = Fin m → ProperClause n k` is the paper's indexed clause collection $\Phi(k,n,m)$ (repeats allowed).
--   * A formula of any length is a list of clauses (`GFormula V`): the position is the clause index, so identical copies stay distinct. `ofFormula`, `ofList` convert; `toMultiset` gives the clause multiset. A sub-formula $\Psi \subseteq \Phi$ is a set $I$ of positions, `subF Φ I`.
--   * `ClauseSat`, `FSat`; $\mathrm{vbl}(C)$ = `vbl C`; $\mathrm{sat}_x(C)$ = `satSet x C`; $\Omega_\Phi$ = `sols Φ`; $Z_\Phi$ = `numSols Φ`; the mass $\mu_\Phi(S) = |S\cap\Omega_\Phi|/Z_\Phi$ (zero when $Z_\Phi = 0$); $\Delta(x,y)$ = `disagree`; $d_H$ = `hamming`; $x\oplus v$ = `flip x v`.
--   * A path in a set $\Omega$ from $x$ to $y$ (`IsPathIn`) is a nonempty list of members of $\Omega$ starting at $x$, ending at $y$, consecutive members at Hamming distance $1$; its length (`pathLength`) is the number of flips. A satisfying path of $\Phi$ (`IsSatPath`) is a path in $\Omega_\Phi$.
--   * $\Psi[x]$ = `satBy Ψ x`, the clauses of $\Psi$ satisfied by $x$ (their positions: `satIdx`).
--   * Probabilities are real numbers: `uexp`/`uprob` average over a finite type; `poisW μ j` $= e^{-\mu}\mu^j/j!$; `poisExp S μ f` is the expectation of $f$ when the formula has $\mathrm{Pois}(\mu)$ clauses i.i.d. uniform on the finite set $S$ (listed in drawing order); `poisProb` the probability. With $S$ = `allClauses n k` (a uniform proper clause has a uniform $k$-set scope and fair signs) this is $\Pr_{\mathrm{Pois}(m)}$: $M\sim\mathrm{Pois}(m)$, $\Phi^+\sim\Phi(k,n,M)$. `clausesSatBy xs` is the conditional clause law of the planted model (clauses satisfied by every assignment of the tuple), `oneTrueClauses x` the clauses with exactly one $x$-true literal. `formulaProb n k m` is $\Pr$ under $\Phi(k,n,m)$.
--   * §2.3: $\varepsilon_0 = 2^{-k}$, $M = 2^n(1-\varepsilon_0)^m$ (`Mexp`), $\Gamma = \alpha k^3\varepsilon_0^2$ with $\alpha = m/n$ (`Gam`), $L_Z = 40ne^{\Gamma n}$ (`LZ`), and the event $\mathcal Z = \{Z_\Phi \ge M/L_Z\}$ (`ZEvent`).
--   * `densityBound k γ` $= \frac{2^k}{k}\big(\ln k + \ln\ln k + \gamma - (\ln\ln k)^{-1/16}\big)$, the right end of (1.2) as a function of $\gamma$; `loosenessLambda k` $= \ln k + \ln\ln k + 1 + \frac{\ln\ln k + 1/2}{\ln k} - \frac{6(\ln\ln k)^2}{(\ln k)^2}$ (Lemmas 3.3, 7.4, 7.11). Logarithms are natural (`Real.log`).
-- source:
--   Wang, Yin, Yu, Zhang (2026), Single-Variable Connectivity in Random k-SAT, arXiv:2611.05981 (held version, SHA-256 1821a501…58b80f5), model paragraph (printed p. 2, PDF 4), §2.1 (printed p. 10, PDF 12), §2.3 (printed p. 13, PDF 15)

import Mathlib
import Definitions.Def_SATComputability

noncomputable section

open scoped Classical BigOperators

namespace KSATSingleFlip.Connect

open OAI.FixedClauseThreshold

/-! # The random k-SAT model and the geometry of its solution space

Wang, Yin, Yu, Zhang (2026), *Single-Variable Connectivity in Random k-SAT*, arXiv:2611.05981,
model paragraph (printed p. 2), §2.1 (p. 10), §2.3 (p. 13), §7.1 (p. 53).

Conventions. The paper's variables `[n] = {1, …, n}` are `Fin n` (variable `i + 1` is `i`).
An assignment is `V → Bool` (`true` = 1). A clause on a variable type `V` is a map
`C : V → Option Bool`: `C i = some s` means that `C` has a literal on `i`, which is true under
`σ` exactly when `σ i = s`; `C i = none` means `i ∉ vbl(C)`. The published
`OAI.FixedClauseThreshold.ProperClause n k` is such a map with exactly `k` signed variables, and
`Formula n k m = Fin m → ProperClause n k` is the paper's indexed clause collection (repeats
allowed). A formula of arbitrary length (the Poissonised formulas `Φ⁺`, sub-formulas) is a list
of clauses: the list position is the clause index, so repeated clauses stay distinct, and a
sub-formula `Ψ ⊆ Φ` is a set of list positions. -/

/-- A clause on the variable type `V`: an optional literal sign on every variable. -/
abbrev GClause (V : Type) := V → Option Bool

/-- A formula on `V`: its indexed clause collection, as a list (position = clause index). -/
abbrev GFormula (V : Type) := List (GClause V)

variable {V : Type}

/-- `σ` satisfies the clause `C`: some literal of `C` is true under `σ`. -/
def ClauseSat (σ : V → Bool) (C : GClause V) : Prop := ∃ i, C i = some (σ i)

/-- `σ` satisfies every clause of `Φ`. -/
def FSat (σ : V → Bool) (Φ : GFormula V) : Prop := ∀ C ∈ Φ, ClauseSat σ C

/-- The clause list of an indexed formula `Φ ∈ Formula n k m`. -/
def ofFormula {n k m : ℕ} (F : Formula n k m) : GFormula (Fin n) :=
  List.ofFn fun j => (F j).val

/-- The clause list of a list of proper clauses. -/
def ofList {n k : ℕ} (l : List (ProperClause n k)) : GFormula (Fin n) := l.map Subtype.val

/-- The clause multiset of a list of proper clauses. -/
def toMultiset {n k : ℕ} (l : List (ProperClause n k)) : Multiset (ProperClause n k) := l

section Finite

variable [Fintype V] [DecidableEq V]

/-- `vbl(C)`: the variables on which `C` has a literal (its scope). -/
def vbl (C : GClause V) : Finset V := Finset.univ.filter fun i => (C i).isSome

/-- `sat_x(C)`: the variables whose literals in `C` are true under `x` (Definition 3.1). -/
def satSet (x : V → Bool) (C : GClause V) : Finset V :=
  Finset.univ.filter fun i => C i = some (x i)

/-- `Ω_Φ`: the satisfying assignments of `Φ`. -/
def sols (Φ : GFormula V) : Finset (V → Bool) := Finset.univ.filter fun σ => FSat σ Φ

/-- `Z_Φ = |Ω_Φ|`. -/
def numSols (Φ : GFormula V) : ℕ := (sols Φ).card

/-- The mass `µ_Φ(S) = |S ∩ Ω_Φ| / Z_Φ` of a set of assignments (`0` when `Z_Φ = 0`, the paper's
convention that `µ_Φ` is the zero measure on an unsatisfiable formula). -/
def mass (Φ : GFormula V) (S : Finset (V → Bool)) : ℝ :=
  ((S ∩ sols Φ).card : ℝ) / ((sols Φ).card : ℝ)

/-- The disagreement set `∆(x, y) = {v : x(v) ≠ y(v)}`. -/
def disagree (x y : V → Bool) : Finset V := Finset.univ.filter fun v => x v ≠ y v

/-- Hamming distance `d_H(x, y) = |∆(x, y)|`. -/
def hamming (x y : V → Bool) : ℕ := (disagree x y).card

/-- `x ⊕ v`: `x` with coordinate `v` flipped. -/
def flip (x : V → Bool) (v : V) : V → Bool := Function.update x v (!x v)

/-- `p` is a single-flip path inside the set `Ω` from `x` to `y`: a nonempty sequence of members
of `Ω`, starting at `x`, ending at `y`, consecutive members at Hamming distance one. -/
def IsPathIn (Ω : Finset (V → Bool)) (p : List (V → Bool)) (x y : V → Bool) : Prop :=
  p.head? = some x ∧ p.getLast? = some y ∧ (∀ z ∈ p, z ∈ Ω) ∧
    p.IsChain (fun a b => hamming a b = 1)

/-- The length of a path = its number of flips. -/
def pathLength (p : List (V → Bool)) : ℕ := p.length - 1

/-- A satisfying path of `Φ` from `x` to `y` (model paragraph, p. 2). -/
def IsSatPath (Φ : GFormula V) (p : List (V → Bool)) (x y : V → Bool) : Prop :=
  IsPathIn (sols Φ) p x y

/-- The sub-formula of `Φ` made of the clauses at the positions in `I`, in their order. -/
def subF (Φ : GFormula V) (I : Finset (Fin Φ.length)) : GFormula V :=
  (List.finRange Φ.length).filterMap fun j => if j ∈ I then some (Φ.get j) else none

/-- `Ψ[x] = {C ∈ Ψ : C(x) = 1}` (p. 51): the clauses of `Ψ` satisfied by `x`. -/
def satBy (Ψ : GFormula V) (x : V → Bool) : GFormula V := Ψ.filter fun C => decide (ClauseSat x C)

/-- The positions of the clauses of `Ψ` satisfied by `x` (so `subF Ψ (satIdx Ψ x) = Ψ[x]`). -/
def satIdx (Ψ : GFormula V) (x : V → Bool) : Finset (Fin Ψ.length) :=
  Finset.univ.filter fun j => ClauseSat x (Ψ.get j)

end Finite

/-! ## Probability over finite and Poissonised laws (all probabilities are real numbers) -/

/-- The expectation of `f` under the uniform law on a finite type. -/
def uexp {β : Type} [Fintype β] (f : β → ℝ) : ℝ := (∑ b, f b) / (Fintype.card β : ℝ)

/-- The probability of an event under the uniform law on a finite type. -/
def uprob {β : Type} [Fintype β] (P : β → Prop) : ℝ := uexp fun b => if P b then (1 : ℝ) else 0

/-- The Poisson weight `Pr(Pois(μ) = j) = e^{-μ} μ^j / j!`. -/
def poisW (μ : ℝ) (j : ℕ) : ℝ := Real.exp (-μ) * μ ^ j / (j.factorial : ℝ)

/-- The expectation of `f(Φ)` when `Φ` consists of `Pois(μ)` independent clauses, each uniform on
the finite set `S`: the clause count `M ∼ Pois(μ)`, then `M` i.i.d. uniform members of `S`, listed
in drawing order. Every `f` used below takes values in `[0, 1]`, so the series converges. -/
def poisExp {α : Type} (S : Finset α) (μ : ℝ) (f : List α → ℝ) : ℝ :=
  ∑' M : ℕ, poisW μ M * uexp fun F : Fin M → S => f (List.ofFn fun i => (F i).1)

/-- The probability of an event under the law of `poisExp`. -/
def poisProb {α : Type} (S : Finset α) (μ : ℝ) (P : List α → Prop) : ℝ :=
  poisExp S μ fun l => if P l then (1 : ℝ) else 0

/-- All proper `k`-clauses on `[n]`: a uniform member has a uniform `k`-element scope and
independent fair signs. `poisExp (allClauses n k) m` is the law `Pr_{Pois(m)}` of §7.1:
`M ∼ Pois(m)`, then `Φ⁺ ∼ Φ(k, n, M)`. -/
def allClauses (n k : ℕ) : Finset (ProperClause n k) := Finset.univ

/-- The proper `k`-clauses satisfied by every assignment of the tuple `xs` (the conditional clause
law of the planted model: a uniform member of this set is a clause conditioned to be satisfied by
all of `xs`). -/
def clausesSatBy {n k r : ℕ} (xs : Fin r → Fin n → Bool) : Finset (ProperClause n k) :=
  Finset.univ.filter fun C => ∀ i, ClauseSat (xs i) C.val

/-- The proper `k`-clauses with exactly one true literal under `x`. -/
def oneTrueClauses {n k : ℕ} (x : Fin n → Bool) : Finset (ProperClause n k) :=
  Finset.univ.filter fun C => (satSet x C.val).card = 1

/-- `Pr_{Φ ∼ Φ(k,n,m)}(P Φ)`: the uniform law on `Formula n k m`, which is the paper's
`Φ(k, n, m)` (m independent clauses, each a uniform k-set of variables with independent fair
signs; repeats allowed). -/
def formulaProb (n k m : ℕ) (P : Formula n k m → Prop) : ℝ := uprob P

/-! ## Solution counts (§2.3, printed p. 13) -/

/-- `ε₀ = 2^{-k}`. -/
def eps0 (k : ℕ) : ℝ := 1 / (2 : ℝ) ^ k

/-- `M = E[Z_Φ] = 2^n (1 − ε₀)^m`. -/
def Mexp (n k m : ℕ) : ℝ := (2 : ℝ) ^ n * (1 - eps0 k) ^ m

/-- `Γ = α k³ ε₀²` with `α = m/n`. -/
def Gam (n k m : ℕ) : ℝ := ((m : ℝ) / n) * (k : ℝ) ^ 3 * eps0 k ^ 2

/-- `L_Z = 40 n e^{Γ n}`. -/
def LZ (n k m : ℕ) : ℝ := 40 * (n : ℝ) * Real.exp (Gam n k m * n)

/-- The event `Z = {Z_Φ ≥ M / L_Z}`. -/
def ZEvent {n k m : ℕ} (F : Formula n k m) : Prop :=
  Mexp n k m / LZ n k m ≤ (numSols (ofFormula F) : ℝ)

/-- The upper end of the density range (1.2) of Theorem 1.1:
`(2^k/k)(ln k + ln ln k + γ − 1/(ln ln k)^{1/16})`, as a function of the constant `γ` (it is used
with `γ = γ*`). -/
def densityBound (k : ℕ) (γ : ℝ) : ℝ :=
  (2 : ℝ) ^ k / k *
    (Real.log k + Real.log (Real.log k) + γ - 1 / Real.rpow (Real.log (Real.log k)) (1 / 16))

/-- The looseness density bound of Lemmas 3.3, 7.4 and 7.11 (without the factor `2^k n/k`):
`ln k + ln ln k + 1 + (ln ln k + 1/2)/ln k − 6 (ln ln k)²/(ln k)²`. -/
def loosenessLambda (k : ℕ) : ℝ :=
  Real.log k + Real.log (Real.log k) + 1 + (Real.log (Real.log k) + 1 / 2) / Real.log k -
    6 * Real.log (Real.log k) ^ 2 / Real.log k ^ 2

end KSATSingleFlip.Connect


