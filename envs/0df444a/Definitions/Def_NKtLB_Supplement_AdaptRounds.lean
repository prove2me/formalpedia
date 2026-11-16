-- Prove2me | Definitions.Def_NKtLB_Supplement_AdaptRounds
-- name    : NKtLB_Supplement_AdaptRounds
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:22:18.083763+00:00
-- url     : https://prove2.me/theorems/ac82eb67-86f5-4f53-99e3-5e486b3181b5
-- title:
--   At most $d$ rounds (levels of adaptivity) of oracle queries
-- statement:
--   Let $M$ be a machine run with oracle $O$ on fixed tape contents. The first $t$ steps of $M$ use **at most $d$ levels of adaptivity** if they split into $d$ consecutive phases $[\tau_0,\tau_1),\dots,[\tau_{d-1},\tau_d)$ with $\tau_0=0$, no query is made after $\tau_d$, and for each phase $k$ the list of queries made during that phase stays the same whatever answers are given to the queries of phase $k$ and of later phases. The answers to earlier phases are the true answers from $O$.
--
--   In words, the queries of each round are fixed before any answer of that round is seen. With $d=1$ this is **non-adaptive** (parallel) access, written $\|O$ in the paper (p.9: "We use $\|$NP to denote parallel access to an NP-oracle").
--
--   **Formalization Note** The paper gives no formal definition of these access modes. This is the semantic definition, with "whatever answers" quantified over all oracles.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), §3.3, p.22; Appendix A, p.96–97

import Mathlib
import Definitions.Def_NKtLB_Supplement_runV

namespace NKtLB.Supplement

/-- **At most `d` levels of adaptivity** (Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), §3.3, p.22: "We can consider the case where the
oracle calls are non-adaptive. In this case, we will write `K^{t,∥O}(x)` or `Kt^{∥O}(x)`"; Appendix A,
p.96: "`Kt^{∥d O}` refers to the complexity measure `Kt` wherein the universal machine may make oracle
calls to `O` with up to `d` levels of adaptivity"; p.97: "making queries to a `A` oracle with at
most `d` levels of adaptivity").

`AdaptRounds M O inp t d`: the first `t` steps of `M` on `inp` with oracle `O` split into `d`
consecutive phases `[τ₀, τ₁), …, [τ_{d-1}, τ_d)` (with `τ₀ = 0`), no query is made in `[τ_d, t)`,
and the list of queries made in phase `k` is the same whatever answers are given to the queries of
phase `k` and later (answers to earlier phases are the true answers from `O`): the queries of a
phase are fixed before any answer of that phase is seen. `d = 1` is non-adaptive (parallel)
access.

**Formalization Note.** The paper gives no formal definition of these access modes; this is the
semantic one (queries of a round depend only on the input and on the answers of earlier rounds).
"Whatever answers" is quantified over all oracles `O'` answering the later queries. -/
def AdaptRounds (M : Machine) (O : Set (List Bool)) (inp : Inputs) (t d : ℕ) : Prop :=
  ∃ τ : ℕ → ℕ, τ 0 = 0 ∧ Monotone τ ∧ queriesIn M (fun _ => O) inp (τ d) t = [] ∧
    ∀ k < d, ∀ O' : Set (List Bool),
      queriesIn M (fun j => if j < τ k then O else O') inp (τ k) (τ (k + 1)) =
        queriesIn M (fun _ => O) inp (τ k) (τ (k + 1))

end NKtLB.Supplement


