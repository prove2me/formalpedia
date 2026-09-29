-- Prove2me | Definitions.Def_ModularCurve_HeckeInputsAll
-- name    : ModularCurve_HeckeInputsAll
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/d086fd7f-c3c4-5d8b-9033-10f9f95c22a2
-- title:
--   Hecke correspondence inputs at every prime level
-- statement:
--   This module defines a single predicate, [`ModularCurve.HeckeInputsAll N`](../def/ModularCurve_HeckeInputsAll.html#L8) (for $N$ with `NeZero N`), asserting that for every prime $\ell$ — with the instance $\ell\neq 0$ installed from primality — the project's predicate `HeckeInputsAlong (AlgebraicClosure ℚ) N ℓ` holds. The latter is a (dependent) conjunction of the data needed to realise the Hecke correspondence as an endomorphism of $\mathrm{Pic}^0$ of the base-changed modular function field. Concretely, write $\bar F_M$ for `laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull M)`, the $\overline{\mathbb Q}$-subfield of $\overline{\mathbb Q}$-Laurent series generated coefficientwise by the field $\mathbb Q(q^{d}\text{-expansions } j(d\tau) : d\mid M)$; its degree-zero divisor class group is `JZero M`. The two maps are $\alpha=$ `heckeAlphaBar`, the inclusion $\bar F_N\subseteq\bar F_{N\ell}$ coming from $N\mid N\ell$, and $\beta=$ `heckeBetaBar`, induced by the substitution $q\mapsto q^{\ell}$ on Laurent series (i.e. $f(\tau)\mapsto f(\ell\tau)$). The conjuncts are: integrality of $\bar F_{N\ell}$ over $\bar F_N$ along $\alpha$ and along $\beta$; the instance `HasPrincipalDivisors` for $\bar F_{N\ell}$, i.e. each nonzero function admits a finitely supported divisor of its orders at all places, of degree $0$; module-finiteness along $\alpha$; the fundamental identity along $\beta$, $\sum_{w\mid v} e_w\deg w=[\bar F_{N\ell}:\bar F_N]\deg v$ for every place $v$; and the pushforward norm formula along $\alpha$, expressing $\alpha_*(\mathrm{div}\,g)$ at each place $v$ as $v(\mathrm{N}_{\bar F_N}g)$. These are exactly the hypotheses consumed by `heckePic0Bar`, which builds $T_\ell=\alpha_*\circ\beta^{*}$ on `JZero N`. Nothing is asserted here beyond the definition; `HeckeInputsAll` is a hypothesis to be supplied.
--
--   **Relation to Mathlib.** Mathlib has no notion of places, divisors or $\mathrm{Pic}^0$ for function fields in this form; the surrounding `AlgebraicCurve` layer (`Place`, `Divisor`, `Pic0`, `HasPrincipalDivisors`, `FundamentalIdentity`, `PushforwardNormFormula`) is the project's own, built on Mathlib's valuation subrings, `Algebra.IsIntegral`, `Module.Finite` and `Algebra.norm`.
--
--   **Where it is used.** The total Hecke operator `heckeOperatorAlong` is defined by case distinction and is $0$ when these inputs fail, so every substantive assertion about $T_\ell$ acting on $J_0(N)$ in the Frey curve–Mazur's principle–level-lowering part of the argument carries `HeckeInputsAll` (at the levels used) as a hypothesis.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_HeckeInputsAll.lean

import Mathlib
import Definitions.Def_ModularCurve_HeckeOperatorTotal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace ModularCurve

def HeckeInputsAll (N : ℕ) [NeZero N] : Prop :=
  ∀ ℓ : Nat.Primes,
    haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
    HeckeInputsAlong (AlgebraicClosure ℚ) N ℓ

end ModularCurve


