-- Prove2me | Definitions.Def_AvgWorstGap_Supplement_EasyOnAvg
-- name    : AvgWorstGap_Supplement_EasyOnAvg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:06:52.623211+00:00
-- url     : https://prove2.me/theorems/d91aa8af-6f67-4bb9-8242-d4b76fe18d4c
-- title:
--   Average-case easiness of meta-complexity problems: "$\in\mathsf{HeurBPP}$" and "$\in\mathsf{AvgBPP}$" for $\mathrm{Gap}\text{-}\mathrm{MINpKT}^{\mathsf{PH}}$ and $\mathrm{MINpKT}^{\mathsf{PH}}$
-- statement:
--   Let $\Pi=(\mathrm{YES},\mathrm{NO})$ be a promise problem on instances $z=(x,1^s,1^t,1^a,1^b)$. An algorithm $A$ **decides $\Pi$ on $z$** if it outputs $1$ when $z\in\mathrm{YES}$, $0$ when $z\in\mathrm{NO}$, and a bit otherwise (the output $\bot$ never decides).
--
--   1. **Two-sided error** (Def. 2.19). $\Pi$ is easy on average with two-sided error if for every polynomial-time samplable family $\{D_n\}$ with $D_n$ supported on $\{0,1\}^n$ there is a probabilistic polynomial-time algorithm $A$ such that for all $n,s,t,a,b$ and all $k\ge1$, $$\Pr_{x\sim D_n}\Big[\Pr_A\big[A(-;1^k)\text{ decides }\Pi\text{ on }(x,1^s,1^t,1^a,1^b)\big]>\tfrac35\Big]\ \ge\ 1-\frac1k.$$
--   2. **Zero error** (Def. 2.20). In addition, for every $x\in\operatorname{Support}(D_n)$, $$\Pr_A\big[A(-;1^k)\text{ decides }\Pi\text{ on }(x,1^s,1^t,1^a,1^b)\ \text{ or }\ A(x,1^s,1^t,1^a,1^b;1^k)=\bot\big]\ \ge\ \tfrac45.$$
--
--   "$\mathrm{Gap}\text{-}\mathrm{MINpKT}^{\mathsf{PH}}\in\mathsf{HeurBPP}$" means that for every $O\in\mathsf{PH}$ there is a polynomial $\rho$ with $\mathrm{Gap}_\rho\text{-}\mathrm{MINpKT}^O$ easy on average with two-sided error, and "$\in\mathsf{AvgBPP}$" the same with zero error. "$\mathrm{MINpKT}^{\mathsf{PH}}\in\mathsf{HeurBPP}$" (resp. "$\in\mathsf{AvgBPP}$") means that $\mathrm{MINpKT}^O$ is easy on average with two-sided (resp. zero) error for every $O\in\mathsf{PH}$.
--
--   These notions measure the average-case difficulty of estimating $\mathrm{pK}^t$ when the string $x$ comes from a samplable distribution and the other parameters are arbitrary.
--
--   **Formalization Note** One algorithm $A$ (with its polynomial running time, halting on every input and random string) is chosen per family $D$ and serves all $n,s,t,a,b,k$. $k\ge1$, since $1-1/k$ is undefined at $k=0$. The input $(z;1^k)$ is encoded by the published tuple encoding. $\rho$ ranges over polynomials with natural coefficients: NO shrinks as $\rho$ grows, and every polynomial $\mathbb N\to\mathbb N$ is dominated by such a one. The paper extends Defs. 2.19 and 2.20 to $\mathrm{MINpKT}^{\mathsf{PH}}$ by stating that this is "straightforward"; the extension here replaces the gap problem by $\mathrm{MINpKT}^O$ and leaves everything else unchanged.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, The Gap Between Average-Case and Worst-Case Complexity, arXiv:2610.19162 (Oct. 30, 2026), notion "A decides Π on z", p.18; Definition 2.19, p.18; Definition 2.20 and the extension to MINpKT^PH, p.19

import Mathlib
import Definitions.Def_AvgWorstGap_InPrBPP
import Definitions.Def_AvgWorstGap_InPSAMP
import Definitions.Def_AvgWorstGap_InSigmaPO
import Definitions.Def_AvgWorstGap_GapMINpKT
import Definitions.Def_AvgWorstGap_Supplement_MINpKT

namespace AvgWorstGap.Supplement

open NKtLB

/-- The input `(z; 1^k)` of an average-case algorithm for a meta-complexity problem, as one string:
the instance `z = (x, 1^s, 1^t, 1^a, 1^b)` and the accuracy parameter `1^k`. -/
def heurInput (z : List Bool) (k : ℕ) : List Bool := tupleEnc [z, unary k]

/-- **"`A` decides `Π` on `z`"** (Goldberg, Hu, Lu, Lyu, Oliveira, *The Gap Between Average-Case and
Worst-Case Complexity*, arXiv:2610.19162, version of October 30, 2026, §2.5, p.18): "`A(z) = 1` if
`z ∈ YES`, `0` if `z ∈ NO`, either `0` or `1` otherwise." Here the run of `A` on the read-only
contents `inp` halts within `T` steps with a one-bit output `β`, `β = 1` if `z ∈ YES` and `β = 0`
if `z ∈ NO` (an output `⊥` never decides). -/
def DecidesOn (P : PromiseProblem) (A : Machine) (inp : Inputs) (T : ℕ) (z : List Bool) : Prop :=
  ∃ β : Bool, A.HaltsWith ∅ inp T (bitOut β) ∧ (z ∈ P.yes → β = true) ∧ (z ∈ P.no → β = false)

/-- A **polynomial-time samplable family supported over `{0,1}^n`** (Defs. 2.19, 2.20, p.18–19):
`D ∈ PSAMP` (the published `InPSAMP`) and every string in the support of `D_n` has length `n`. -/
def IsSampLenFamily (D : ℕ → PMF (List Bool)) : Prop :=
  InPSAMP D ∧ ∀ n : ℕ, ∀ x ∈ (D n).support, x.length = n

/-- A **probabilistic polynomial-time machine**: on every input `u` and every random string
`r ∈ {0,1}^{p(|u|)}` (oracle `∅`, auxiliary and guess tapes empty) it halts within `p(|u|)` steps. -/
def IsPPT (A : Machine) (p : Polynomial ℕ) : Prop :=
  ∀ u r : List Bool, r.length = p.eval u.length →
    (A.run ∅ ⟨u, [], [], r⟩ (p.eval u.length)).state = A.halt

/-- The probability over `A`'s random string that `A(z; 1^k)` decides `P` on `z`
(`z = (x, 1^s, 1^t, 1^a, 1^b)`), where `A` runs `p(|(z; 1^k)|)` steps. -/
noncomputable def probDecides (P : PromiseProblem) (A : Machine) (p : Polynomial ℕ)
    (z : List Bool) (k : ℕ) : ℝ :=
  prob (p.eval (heurInput z k).length) (fun r =>
    DecidesOn P A ⟨heurInput z k, [], [], r⟩ (p.eval (heurInput z k).length) z)

/-- The probability over `A`'s random string that `A(z; 1^k)` decides `P` on `z` **or** outputs `⊥`. -/
noncomputable def probDecidesOrBot (P : PromiseProblem) (A : Machine) (p : Polynomial ℕ)
    (z : List Bool) (k : ℕ) : ℝ :=
  prob (p.eval (heurInput z k).length) (fun r =>
    DecidesOn P A ⟨heurInput z k, [], [], r⟩ (p.eval (heurInput z k).length) z ∨
      A.HaltsWith ∅ ⟨heurInput z k, [], [], r⟩ (p.eval (heurInput z k).length) [Sym.bot])

/-- **Easy on average with two-sided error** (Def. 2.19, p.18): "for every polynomial-time samplable
distribution family `{Dn}n` supported over `{0, 1}^n`, there exist a PPT algorithm `A` such that for
every `n, s, t, a, b, k ∈ ℕ`,
`Pr_{x∼Dn} [ Pr_A [ A(−; 1^k) decides Gapρ-MINpKT^O on (x, 1^s, 1^t, 1^a, 1^b) ] > 3/5 ] ≥ 1 − 1/k`."
Stated for an arbitrary promise problem `P` on the instances `(x, 1^s, 1^t, 1^a, 1^b)` (the base
`inst5`), so that it applies to `Gapρ-MINpKT^O` and to `MINpKT^O` ("It is straightforward to extend
the above definitions to … MINpKT^PH", p.19).

**Formalization Note.** `A` may depend on `D` only (not on `n, s, t, a, b, k`); `k ≥ 1` (at `k = 0`
the bound `1 − 1/k` is undefined). -/
def EasyOnAvgTwoSided (P : PromiseProblem) : Prop :=
  ∀ D : ℕ → PMF (List Bool), IsSampLenFamily D →
    ∃ (A : Machine) (p : Polynomial ℕ), IsPPT A p ∧
      ∀ n s t a b k : ℕ, 1 ≤ k →
        ENNReal.ofReal (1 - 1 / (k : ℝ)) ≤
          (D n).toOuterMeasure {x | 3 / 5 < probDecides P A p (inst5 x s t a b) k}

/-- **Easy on average with zero error** (Def. 2.20, p.19): the two-sided condition of Def. 2.19 and,
"for every `x ∈ Support(Dn)`, `Pr_A [ A(−; 1^k) decides Gapρ-MINpKT^O on (x, 1^s, 1^t, 1^a, 1^b) OR
A(x, 1^s, 1^t, 1^a, 1^b; 1^k) = ⊥ ] ≥ 4/5`", both for all `n, s, t, a, b` and `k ≥ 1`, with one PPT
algorithm `A` per family `D`. -/
def EasyOnAvgZeroError (P : PromiseProblem) : Prop :=
  ∀ D : ℕ → PMF (List Bool), IsSampLenFamily D →
    ∃ (A : Machine) (p : Polynomial ℕ), IsPPT A p ∧
      ∀ n s t a b k : ℕ, 1 ≤ k →
        ENNReal.ofReal (1 - 1 / (k : ℝ)) ≤
            (D n).toOuterMeasure {x | 3 / 5 < probDecides P A p (inst5 x s t a b) k} ∧
          ∀ x ∈ (D n).support, 4 / 5 ≤ probDecidesOrBot P A p (inst5 x s t a b) k

/-- **"`Gap-MINpKT^PH ∈ HeurBPP`"** (Def. 2.19, p.18): "for every `O ∈ PH`, there exist a polynomial
`ρ` such that `Gapρ-MINpKT^O` is easy on average with two-sided error."

**Formalization Note.** `ρ` ranges over `Polynomial ℕ`; NO shrinks as `ρ` grows, and every
polynomial `ℕ → ℕ` is dominated by one with natural coefficients, so this is the paper's range. -/
def GapPHInHeurBPP : Prop :=
  ∀ O : Set (List Bool), InPH O →
    ∃ ρ : Polynomial ℕ, EasyOnAvgTwoSided (GapMINpKT O (fun n => ρ.eval n))

/-- **"`Gap-MINpKT^PH ∈ AvgBPP`"** (Def. 2.20, p.19): "for every `O ∈ PH`, there exist a polynomial
`ρ` such that `Gapρ-MINpKT^O` is easy on average with zero error." -/
def GapPHInAvgBPP : Prop :=
  ∀ O : Set (List Bool), InPH O →
    ∃ ρ : Polynomial ℕ, EasyOnAvgZeroError (GapMINpKT O (fun n => ρ.eval n))

/-- **"`MINpKT^PH ∈ HeurBPP`"** (Theorem 5.4, p.36; the extension of Def. 2.19 to `MINpKT^PH`,
p.19): for every `O ∈ PH`, `MINpKT^O` is easy on average with two-sided error. -/
def MINpKTPHInHeurBPP : Prop :=
  ∀ O : Set (List Bool), InPH O → EasyOnAvgTwoSided (MINpKT O)

/-- **"`MINpKT^PH ∈ AvgBPP`"** (Theorem 5.1, p.35; the extension of Def. 2.20 to `MINpKT^PH`,
p.19): for every `O ∈ PH`, `MINpKT^O` is easy on average with zero error. -/
def MINpKTPHInAvgBPP : Prop :=
  ∀ O : Set (List Bool), InPH O → EasyOnAvgZeroError (MINpKT O)

end AvgWorstGap.Supplement


