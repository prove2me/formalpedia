-- Prove2me | Definitions.Def_HardCoreLocalSampling_Local_Factory
-- name    : HardCoreLocalSampling_Local_Factory
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:49:33.740574+00:00
-- url     : https://prove2.me/theorems/a47a14bc-7ee8-48e9-a42c-9fca08bedfa9
-- title:
--   Recursive signed factory and root coin algorithm
-- statement:
--   These are the recursive algorithms of §8 and §9, written as laws built from prescribed primitive choices. A sign is a Boolean, with `true` for $+1$. Every recursive call and repeated child occurrence uses a fresh independent draw.
--
--   **Factory.** At state $s$, draw from a law on multi-indices and a leftover outcome. On the leftover outcome return a fresh fair sign. On $\alpha$, draw an independent sign of the prescribed mean and multiply it by independent recursive calls, $\alpha_i$ of them at child $i$. The law also records the number of calls, including the initial one. On a finite acyclic family with a decreasing rank the recursion has finite depth.
--
--   **Root algorithm.** If $d=0$, return a coin of mean $1/(1+\lambda)$. Otherwise, with probability $2Q$ draw $\alpha\ne0$, an independent sign of mean $h_\alpha/q_\alpha$, and independent residual signs with multiplicities $\alpha_i$, multiply to get $Y$, and return $(1+Y)/2$; with the remaining probability return a coin of mean $(p_0-Q)/(1-2Q)$.
--
--   **Formalization Note** The coin of mean $p$ is truncated to $[0,1]$ to make it total. Lemma 13 and Lemma 11 state or imply that the means used lie in the right interval, so the truncation does not act in the source's domain. The fuel value at depth zero is unreachable from the entry point on an acyclic family.
--
--   The implementation predicates require actual fair-bit programs for selection and coefficient signs. A factory implementation must halt almost surely and realize the recursively defined joint law of sign and call count on the same program execution, with the count returned in a number register. Finite states are represented by injective natural-number labels.
-- source:
--   Thomas Chen, STOC 2027 submission #462 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/462.pdf, §8, Lemma 11 and eq. (21), printed p.9 (PDF p.10); §9, Lemma 13, printed p.10 (PDF p.11)

import Mathlib
import Definitions.Def_HardCoreLocalSampling_Local_Machine

namespace HardCoreLocalSampling.Local

/-! The recursive algorithms of §8 and §9 (printed pp.9–10 / PDF pp.10–11), as laws built from
the prescribed primitive choices, each call using fresh independent randomness (bind).
A sign is a `Bool`: `true` is `+1`, `false` is `-1`; a product of signs is `==`. -/

/-- The child list of a monomial: child `i` repeated `α_i` times. Each occurrence is a separate
independent call. -/
def childCalls {S : Type*} {deg : S → ℕ} (child : ∀ s, Fin (deg s) → S) (s : S)
    (α : Fin (deg s) → ℕ) : List S :=
  (List.finRange (deg s)).flatMap fun i => List.replicate (α i) (child s i)

/-- The factory of Lemma 11, with `n` the remaining recursion depth: at `s`, draw from
`select s`. On `none` (the leftover mass) return a fresh fair sign. On `some α`, draw an
independent sign of mean `mean s α`, and multiply by independent recursive calls at each entry
of `childCalls`. The second component counts recursive calls, including this one. The value at
depth `0` is never reached from `factorySign` on an acyclic family. -/
noncomputable def factoryLaw {S : Type*} {deg : S → ℕ} (child : ∀ s, Fin (deg s) → S)
    (select : ∀ s, PMF (Option (Fin (deg s) → ℕ))) (mean : ∀ s, (Fin (deg s) → ℕ) → ℝ) :
    ℕ → S → PMF (Bool × ℕ)
  | 0, _ => PMF.pure (true, 1)
  | n + 1, s => (select s).bind fun o =>
      match o with
      | none => (coin (1 / 2)).map fun b => (b, 1)
      | some α => (coin ((1 + mean s α) / 2)).bind fun σ =>
          ((childCalls child s α).foldr
              (fun u acc => (factoryLaw child select mean n u).bind fun a =>
                acc.map fun b => (a.1 == b.1, a.2 + b.2))
              (PMF.pure (true, 0))).map fun b => (σ == b.1, b.2 + 1)

/-- The factory at `s` on a family with rank function `rank` (`rank` strictly decreases along
child edges). -/
noncomputable def factorySign {S : Type*} {deg : S → ℕ} (child : ∀ s, Fin (deg s) → S)
    (select : ∀ s, PMF (Option (Fin (deg s) → ℕ))) (mean : ∀ s, (Fin (deg s) → ℕ) → ℝ)
    (rank : S → ℕ) (s : S) : PMF (Bool × ℕ) :=
  factoryLaw child select mean (rank s + 1) s

/-- An effective implementation of the selection primitive in Lemma 11. States have
finite natural-number labels `encode s`. The input is that label in `N[0]`; a selected
multiindex is written to `Nm[0],...,Nm[d-1]` with output `true`, and leftover mass returns
`false`. Both probabilities and almost-sure termination concern an actual fair-bit run. -/
def SelectionImplemented {S : Type*} {deg : S → ℕ} (encode : S → ℕ)
    (select : ∀ s, PMF (Option (Fin (deg s) → ℕ))) : Prop :=
  ∃ P : Program, ∀ s,
    let init : Config := { N := regsOf [encode s] }
    (∀ᵐ ω ∂fairMeasure, outcome P noOracle ω noExt init ≠ none) ∧
    fairMeasure {ω | outcome P noOracle ω noExt init = some false} = select s none ∧
    ∀ α : Fin (deg s) → ℕ,
      fairMeasure {ω | ∃ c, finalConfig P noOracle ω noExt init = some c ∧
        c.result = some true ∧ (fun i : Fin (deg s) => c.Nm i.val) = α} = select s (some α)

/-- Effective coefficient-sign primitives in Lemma 11, uniformly over the state and
multiindex. The latter is supplied in the first `d` number-memory cells. The selected
sign is a real program output; no biased-coin instruction is introduced. Zero-envelope
terms are never selected, so no implementation is required for those terms. -/
def MeanSignsImplemented {S : Type*} {deg : S → ℕ} (encode : S → ℕ)
    (d q : ∀ s, (Fin (deg s) → ℕ) → ℝ) : Prop :=
  ∃ P : Program, ∀ s (α : Fin (deg s) → ℕ), 0 < q s α →
    let init : Config := { N := regsOf [encode s], Nm := regsOf (List.ofFn α) }
    (∀ᵐ ω ∂fairMeasure, outcome P noOracle ω noExt init ≠ none) ∧
    fairMeasure {ω | outcome P noOracle ω noExt init = some true} =
      ENNReal.ofReal ((1 + d s α / q s α) / 2)

/-- A fair-bit program realizes the complete recursive factory's joint law of sign and
number of calls (including the initial call). The count is returned in `N[0]`. This is an
execution requirement in addition to the mathematical recursive law, not a supplied
output distribution or a freely assigned cost. Lemma 11 constructs such a program from
implementations of its two primitive choices. -/
def FactoryImplemented {S : Type*} (encode : S → ℕ)
    (law : S → PMF (Bool × ℕ)) (P : Program) : Prop :=
  ∀ s,
    let init : Config := { N := regsOf [encode s] }
    (∀ᵐ ω ∂fairMeasure, outcome P noOracle ω noExt init ≠ none) ∧
    ∀ (b : Bool) (n : ℕ),
      fairMeasure {ω | ∃ c, finalConfig P noOracle ω noExt init = some c ∧
        c.result = some b ∧ c.N 0 = n} = law s (b, n)

/-- The list `i` repeated `α_i` times. -/
def rootCalls {d : ℕ} (α : Fin d → ℕ) : List (Fin d) :=
  (List.finRange d).flatMap fun i => List.replicate (α i) i

/-- The product of independent residual signs with multiplicities `α`. -/
noncomputable def childProduct {d : ℕ} (residual : Fin d → PMF Bool) (α : Fin d → ℕ) : PMF Bool :=
  (rootCalls α).foldr
    (fun i acc => (residual i).bind fun a => acc.map fun b => a == b)
    (PMF.pure true)

/-- The algorithm of Lemma 13. If `d = 0`, a direct coin of mean `1/(1+λ)`. Otherwise, with
probability `2Q`: draw `α` from `select`, an independent sign of mean `signMean α`, multiply by
independent residual signs with multiplicities `α` to get `Y`, and return `(1+Y)/2`; with the
remaining probability return a coin of mean `(p0 - Q)/(1 - 2Q)`. -/
noncomputable def rootAlgorithm {d : ℕ} (lam Q p0 : ℝ) (select : PMF (Fin d → ℕ))
    (signMean : (Fin d → ℕ) → ℝ) (residual : Fin d → PMF Bool) : PMF Bool :=
  if d = 0 then coin (1 / (1 + lam)) else
    (coin (2 * Q)).bind fun correction =>
      if correction then
        select.bind fun α => (coin ((1 + signMean α) / 2)).bind fun σ =>
          (childProduct residual α).map fun y => σ == y
      else coin ((p0 - Q) / (1 - 2 * Q))

end HardCoreLocalSampling.Local


