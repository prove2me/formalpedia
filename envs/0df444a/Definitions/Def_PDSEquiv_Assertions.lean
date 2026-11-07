-- Prove2me | Definitions.Def_PDSEquiv_Assertions
-- name    : PDSEquiv_Assertions
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:02:51.066403+00:00
-- url     : https://prove2.me/theorems/66243e25-c6c2-4a41-9677-d3cc007f9190
-- title:
--   The eight assertions of Theorem 8.1, (AD), and the reductions clause
-- statement:
--   Fix densities $0<q<p\le1$, an exponent $\beta$ and a constant. For a randomized procedure, given by its acceptance probabilities $a(G)$ and recovery probabilities $s(G,C)$, the guarantee **at size $N$** of each assertion is, with $k=\lfloor N^\beta\rfloor$ and $x=N^\beta$:
--
--   1. (WS) $\Pr_{(G,C)\sim\mathrm{PDS}(N,k,p,q)}[S(G)=C]\ge N^{-a_0}$; (SS) the same probability $\ge 1-e^{-N^\xi}$.
--   2. (WD) $\mathrm{adv}(\mathrm{PDS}(N,k,p,q),\mathrm{ER}(N,q))\ge(1+\varepsilon)\Lambda_N(k)$; (SD) the advantage $\ge 2-e^{-N^\xi}$.
--   3. (W̃S), (S̃S), (W̃D), (S̃D): the same with $\widetilde{\mathrm{PDS}}(N,x,p,q)$, the benchmark in (W̃D) still being $\Lambda_N(\lfloor N^\beta\rfloor)$.
--   4. (AD) $\Pr_{\mathrm{ER}(N,q)}[D=1]\le N^{-1}$ and $\Pr_{\mathrm{PDS}(N,j,p,q)}[D=1]\ge\gamma$ for every $j\in\{\lfloor N^\beta\rfloor,\dots,N\}$, with $\gamma\in(0,1]$.
--
--   An assertion **holds on** $\mathcal N\subseteq\mathbb N$ if there are a polynomial-time program, a rational $\beta\in(0,1/2)$ and a positive constant (in $(0,1]$ for (AD)) such that its guarantee holds for all sufficiently large $N\in\mathcal N$.
--
--   A **reduction from $X$ to $Y$**: for every rational $\beta\in(0,1/2)$ and admissible constant of $X$ there are one oracle program $R$, a rational $\beta'\in(0,1/2)$, an admissible constant of $Y$, an exponent $c$ and a threshold $N_0$, all chosen before the oracle, such that for **every** oracle $O$ of $X$'s kind:
--
--   1. for every $N$ and every graph on $[N]$, $R^O$ halts within log-cost $(N+2)^c$ and $(N+2)^c$ queries on every branch, and every query is an $N$-vertex graph;
--   2. for every $N\ge N_0$, if $O$ meets $X$ at size $N$ (with $\beta$ and the constant), then $R^O$ meets $Y$ at size $N$ (with $\beta'$ and its constant).
--
--   This is the closing sentence of Theorem 8.1: the reductions preserve $(p,q)$, the number $N$ of vertices and the set $\mathcal N$, run in polynomial time, make $\mathrm{poly}(N)$ queries on $N$-vertex graphs and never check membership in $\mathcal N$ — no $\mathcal N$ occurs in the definition.
--
--   **Formalization Note** "For all sufficiently large $N\in\mathcal N$" is $\exists N_0,\ \forall N\in\mathcal N,\ N\ge N_0\to\dots$. A program's acceptance probability is the mass of output $[1]$; its recovery probability of $C$ the mass of the characteristic list of $C$.
-- source:
--   Hirahara, Shimizu, Planted Dense Subgraph Conjectures Are Equivalent, STOC 2027 submission (manuscript sha256 f849d438…), Theorem 8.1, pp.31–32 (the eight assertions and the closing sentence); (AD), p.33

import Mathlib
import Definitions.Def_PDSEquiv_Laws
import Definitions.Def_PDSEquiv_Machine

set_option autoImplicit false

namespace PDSEquiv

noncomputable section

/-!
# The assertions of Theorem 8.1, (AD), and the reductions clause

S. Hirahara, N. Shimizu, *Planted Dense Subgraph Conjectures Are Equivalent*, STOC 2027 submission
(manuscript sha256 f849d438…), §8, pp.31–33.

**Formalization Note.** `holdsAt` is an assertion's guarantee at one size `N` for one behaviour, and a
behaviour is what either a program or a typed oracle has: acceptance probabilities and recovery
probabilities. `Holds` is the printed assertion: a polynomial-time program, a rational `β ∈ (0, 1/2)`,
a positive constant (in `(0, 1]` for (AD)), and all sufficiently large `N ∈ 𝒩`. `Reduces` formalizes
the theorem's closing sentence: one oracle program per ordered pair and per input parameters, chosen
before the oracle, with a bound on time and queries for every `N`, every graph and every oracle, and
a guarantee pointwise in `N` with a threshold independent of the oracle. It has no `𝒩` in it, which
is how it preserves `𝒩` and does not check membership. A program's time bound is for all `N`, not
only for `N ∈ 𝒩`.
-/

/-- What a randomized procedure does on a graph: its acceptance and recovery probabilities. -/
structure Behaviour where
  /-- The probability of the value `1` on `G`. -/
  accept : ∀ N, Graph N → ℝ
  /-- The probability of the output `C` on `G`. -/
  recover : ∀ N, Graph N → Finset (Fin N) → ℝ

/-- The behaviour of a program with an oracle. -/
def Behaviour.ofProgram (P : Program) (Q : Oracle) : Behaviour where
  accept _ G := outMass P Q (enc G) acceptOut
  recover _ G C := outMass P Q (enc G) (charList C)

/-- The two kinds of algorithm in Theorem 8.1. -/
inductive Kind
  | search
  | dist

/-- A black-box algorithm of a kind. -/
abbrev Kind.Family : Kind → Type
  | .search => SearchFamily
  | .dist => DistFamily

/-- The typed oracle of a black-box algorithm. -/
def Kind.oracle : (K : Kind) → K.Family → Oracle
  | .search, s => searchOracle s
  | .dist, d => distOracle d

/-- The behaviour of a black-box algorithm. Only the field of its kind is read. -/
def Kind.behaviour : (K : Kind) → K.Family → Behaviour
  | .search, s => ⟨fun _ _ => 0, fun _ G C => searchRec s G C⟩
  | .dist, d => ⟨fun _ G => distAcc d G, fun _ _ _ => 0⟩

/-- The eight assertions of Theorem 8.1, pp.31–32, and (AD), p.33. The suffix `b` is the binomial-k
model (the tilde on the page). -/
inductive Assertion
  | WS | SS | WD | SD | WSb | SSb | WDb | SDb | AD
  deriving DecidableEq

/-- The kind of algorithm an assertion asks for. -/
def Assertion.kind : Assertion → Kind
  | .WS | .SS | .WSb | .SSb => .search
  | .WD | .SD | .WDb | .SDb | .AD => .dist

/-- The admissible constants: `a₀, ξ, ε > 0`, and `γ ∈ (0, 1]` for (AD). -/
def Assertion.ConstOK : Assertion → ℝ → Prop
  | .AD, c => 0 < c ∧ c ≤ 1
  | _, c => 0 < c

/-- `Pr_{(G,C)∼PDS(N,k,p,q)}[S(G) = C]`. -/
def recProb (N k : ℕ) (p q : ℝ) (b : Behaviour) : ℝ :=
  ∑ G : Graph N, ∑ C, pdsJoint N k p q G C * b.recover N G C

/-- `Pr_{(G,C)∼P̃DS(N,x,p,q)}[S(G) = C]`. -/
def recProbB (N : ℕ) (x p q : ℝ) (b : Behaviour) : ℝ :=
  ∑ G : Graph N, ∑ C, pdsbJoint N x p q G C * b.recover N G C

/-- `⌊N^β⌋`. -/
def floorPow (N : ℕ) (β : ℝ) : ℕ := ⌊(N : ℝ) ^ β⌋₊

/-- An assertion's guarantee at one size `N`, for a behaviour, with exponent `β` and constant
`const` (`a₀`, `ξ`, `ε` or `γ`), pp.31–33. -/
def holdsAt (A : Assertion) (p q β const : ℝ) (b : Behaviour) (N : ℕ) : Prop :=
  match A with
  | .WS => recProb N (floorPow N β) p q b ≥ (N : ℝ) ^ (-const)
  | .SS => recProb N (floorPow N β) p q b ≥ 1 - Real.exp (-(N : ℝ) ^ const)
  | .WD =>
    adv (pdsMass N (floorPow N β) p q) (erMass N q) (b.accept N)
      ≥ (1 + const) * Lam p q N (floorPow N β)
  | .SD =>
    adv (pdsMass N (floorPow N β) p q) (erMass N q) (b.accept N)
      ≥ 2 - Real.exp (-(N : ℝ) ^ const)
  | .WSb => recProbB N ((N : ℝ) ^ β) p q b ≥ (N : ℝ) ^ (-const)
  | .SSb => recProbB N ((N : ℝ) ^ β) p q b ≥ 1 - Real.exp (-(N : ℝ) ^ const)
  | .WDb =>
    adv (pdsbMass N ((N : ℝ) ^ β) p q) (erMass N q) (b.accept N)
      ≥ (1 + const) * Lam p q N (floorPow N β)
  | .SDb =>
    adv (pdsbMass N ((N : ℝ) ^ β) p q) (erMass N q) (b.accept N)
      ≥ 2 - Real.exp (-(N : ℝ) ^ const)
  | .AD =>
    expect (erMass N q) (b.accept N) ≤ (N : ℝ)⁻¹ ∧
      ∀ j : ℕ, floorPow N β ≤ j → j ≤ N → expect (pdsMass N j p q) (b.accept N) ≥ const

/-- The printed assertion: there are a randomized polynomial-time algorithm, a rational
`β ∈ (0, 1/2)` and a constant such that the guarantee holds for all sufficiently large `N ∈ 𝒩`. -/
def Holds (A : Assertion) (p q : ℝ) (𝒩 : Set ℕ) : Prop :=
  ∃ P : Program, PolyTimeAlg P ∧ ∃ β : ℚ, 0 < β ∧ β < 1 / 2 ∧ ∃ const : ℝ, A.ConstOK const ∧
    ∃ N₀ : ℕ, ∀ N ∈ 𝒩, N₀ ≤ N → holdsAt A p q β const (Behaviour.ofProgram P noOracle) N

/-- The closing sentence of Theorem 8.1, p.32: a reduction from `X` to `Y`. For all parameters of `X`
there are one oracle program `R`, parameters of `Y`, an exponent `c` and a threshold `N₀`, all chosen
before the oracle, such that for **every** oracle `O` of `X`'s kind: `R^O` runs within `(N + 2) ^ c`
log-cost and queries on every branch, for every `N` and every graph on `[N]`, querying only `N`-vertex
graphs; and for every `N ≥ N₀`, if `O` meets `X` at size `N` then `R^O` meets `Y` at size `N`. -/
def Reduces (p q : ℝ) (X Y : Assertion) : Prop :=
  ∀ β : ℚ, 0 < β → β < 1 / 2 → ∀ const : ℝ, X.ConstOK const →
    ∃ (R : Program) (β' : ℚ) (const' : ℝ) (c N₀ : ℕ),
      0 < β' ∧ β' < 1 / 2 ∧ Y.ConstOK const' ∧
      ∀ O : X.kind.Family,
        (∀ (N : ℕ) (G : Graph N),
          HaltsWithin R (X.kind.oracle O) (enc G) ((N + 2) ^ c) ((N + 2) ^ c) ∧
            QueriesSatisfy R (X.kind.oracle O) (enc G) (IsGraphQuery N)) ∧
        ∀ N : ℕ, N₀ ≤ N → holdsAt X p q β const (X.kind.behaviour O) N →
          holdsAt Y p q β' const' (Behaviour.ofProgram R (X.kind.oracle O)) N

/-- The fixed-k assertions of Lemma 8.5 with (AD). -/
def fixedFive : List Assertion := [.WS, .SS, .WD, .SD, .AD]

/-- The binomial-k assertions of Lemma 8.6 with (AD). -/
def binomialFive : List Assertion := [.WSb, .SSb, .WDb, .SDb, .AD]

/-- The eight assertions of Theorem 8.1. -/
def theEight : List Assertion := [.WS, .SS, .WD, .SD, .WSb, .SSb, .WDb, .SDb]

end

end PDSEquiv


