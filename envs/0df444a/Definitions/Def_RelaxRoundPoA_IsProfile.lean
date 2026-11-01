-- Prove2me | Definitions.Def_RelaxRoundPoA_IsProfile
-- name    : RelaxRoundPoA_IsProfile
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:49:13.564013+00:00
-- url     : https://prove2.me/theorems/610257a9-ddb7-4a94-8434-66666fbdbcc0
-- title:
--   Profiles drawn from the agents' weight classes
-- statement:
--   For every agent $i$ let $\mathcal V_i$ be a class of weight functions $\Omega'\to\mathbb R_{\ge0}$ on the relaxed outcome space. A profile $b=(b_i)_{i\in N}$ is **drawn from the classes** if $b_i\in\mathcal V_i$ for every agent $i$.
--
--   Valuation profiles $v$ and bid profiles $b$ both range over such profiles: in a direct mechanism a bid is a reported valuation. An agent's valuation on the original outcome set $\Omega\subseteq\Omega'$ is the restriction of its member of $\mathcal V_i$.
--
--   **Formalization Note** The classes $\mathcal V_i$ are a parameter. The paper's "for all $w$" read over every function would make an oblivious rounding impossible as soon as $\Omega\ne\Omega'$; the applications of the paper each use a specific class (linear weights for packing integer programs, configuration-LP extensions for XOS valuations).
-- source:
--   Dütting, Kesselheim, Tardos, Algorithms as Mechanisms: The Price of Anarchy of Relax-and-Round, arXiv:1511.09208v1, §2, p.6

import Mathlib

open NNReal

namespace RelaxRoundPoA

/-- **Profiles drawn from the agents' weight classes.**
Dütting, Kesselheim, Tardos, arXiv:1511.09208v1, §2, p.6: each agent `i` has a valuation
`v_i : Ω → ℝ≥0`; in a relax-and-round algorithm the weight functions are generalized "to all
`x ∈ Ω'`". A valuation profile `v` and a bid profile `b` specify one such function per agent;
bids are reported valuations (direct mechanisms), so both come from the same class.

`IsProfile Val b` says that `b i ∈ Val i` for every agent `i`.

**Formalization Note** `Val i` is an arbitrary class of nonnegative weight functions on the relaxed
outcome space `Ω'`; an original valuation is the restriction of a member to `Ω ⊆ Ω'`. The paper's
literal "for all `w`" over every function would make an oblivious rounding impossible whenever
`Ω ≠ Ω'`, so the class is a parameter, as in each application of the paper (linear weights for
packing integer programs, configuration-LP extensions for XOS valuations). -/
def IsProfile {N : Type*} {Ω' : Type*} (Val : N → Set (Ω' → ℝ≥0)) (b : N → Ω' → ℝ≥0) : Prop :=
  ∀ i, b i ∈ Val i

end RelaxRoundPoA


