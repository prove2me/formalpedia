-- Prove2me | Definitions.Def_ForgetAlt_PathConstruction
-- name    : ForgetAlt_PathConstruction
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:23:00.651781+00:00
-- url     : https://prove2.me/theorems/1898abe8-9146-4b2b-b481-fe3207089eec
-- title:
--   Procedure PathConstruction (Algorithm 1)
-- statement:
--   For an ABT $T$ with fixed MIEs, vertices $s,t$, a parity $\theta$ and an edge $e$, the procedure is:
--
--   1. if $s=t$, return $t$;
--   2. if $\theta=\alpha(t)$, return $\textsc{PC}(T,s,p_T(t),\bar\theta,e^*_T(p_T(t)))\circ\{p_T(t),t\}$;
--   3. otherwise write $e=\{y,z\}$ with $z\in V(T(t))$, let $Y'=\textsc{PC}(T,s,y,\rho(e),e^*_T(y))$ and $Z'=\textsc{PC}(T,t,z,\rho(e),e^*_T(z))$, and return $Y'\circ e\circ\overline{Z'}$, where $\overline{Z'}$ is $Z'$ reversed.
--
--   The output is the vertex sequence of a path from $s$ to $t$.
--
--   **Formalization Note** The recursion carries a fuel counter and returns `none` when it runs out; "the call returns $L$" means it returns `some L` for all large enough fuel. The orientation $(y,z)$ of line 6 is unique for an incoming edge of $T(t)$.
-- source:
--   Izumi–Kitamura–Yamaguchi, Forgetting Alternation and Blossoms, STOC 2027 submission (manuscript sha256 b656488c…), Section 3.3.2, Algorithm 1, printed p.20 (PDF p.21)

import Mathlib
import Definitions.Def_ForgetAlt_ABT

namespace ForgetAlt

/-!
# Procedure PathConstruction (Algorithm 1)

Izumi–Kitamura–Yamaguchi, *Forgetting Alternation and Blossoms*, STOC 2027 submission
(manuscript sha256 b656488c…), Section 3.3.2, Algorithm 1, printed p.20 (PDF p.21):

```
1: procedure PathConstruction(T, s, t, θ, e)
2:   if s = t then return t
3:   if θ = α(t) then
4:     return PathConstruction(T, s, p_T(t), θ̄, e*_T(p_T(t))) ∘ {p_T(t), t}
5:   else
6:     Let e = {y, z}, where z ∈ V(T(t)).
7:     Y′ ← PathConstruction(T, s, y, ρ(e), e*_T(y))
8:     Z′ ← PathConstruction(T, t, z, ρ(e), e*_T(z))
9:     return Y′ ∘ e ∘ Z̄′
```

**Formalization Notes.**
* The output is the vertex list of the path, from `s` to `t`. Line 4 appends `t`; line 9 is
  `Y′ ++ reverse Z′` (`Z̄′` is the inversion of `Z′`, p.15: the edge `e` joins the last vertex
  `y` of `Y′` to the first vertex `z` of `Z̄′`).
* Recursion carries a fuel counter: every call consumes one unit and `none` signals that the
  fuel ran out. A result `some L` at some fuel is the result at every larger fuel, so "the call
  returns `L`" is stated as: for all large enough fuel the result is `some L`.
* Line 6 orients `e` as `(y, z)` with `y ∉ V(T(t))` and `z ∈ V(T(t))` (`splitInc`). For an
  incoming edge of `T(t)` the orientation is unique, so the choice made by `Classical.choose`
  is immaterial; on other edges it is a junk orientation.
-/

variable {V : Type}

/-- The orientation `(y, z)` of `e` with `y ∉ V(T(t))` and `z ∈ V(T(t))` (line 6 of
Algorithm 1). -/
noncomputable def splitInc (G : SimpleGraph V) (M : G.Subgraph) (par : ExtV V → ExtV V)
    (t : ExtV V) (e : Sym2 (ExtV V)) : ExtV V × ExtV V :=
  open Classical in
  if h : ∃ yz : ExtV V × ExtV V, e = s(yz.1, yz.2) ∧ ¬ InSubtree G M par t yz.1 ∧
      InSubtree G M par t yz.2 then h.choose
  else (e.out.1, e.out.2)

/-- `PathConstruction(T, s, t, θ, e)` (Algorithm 1) for the ABT `par` and the fixed MIEs `mie`,
with fuel. -/
noncomputable def pathConstruction (G : SimpleGraph V) (M : G.Subgraph)
    (par : ExtV V → ExtV V) (mie : ExtV V → Sym2 (ExtV V)) :
    ℕ → ExtV V → ExtV V → Parity → Sym2 (ExtV V) → Option (List (ExtV V))
  | 0, _, _, _, _ => none
  | fuel + 1, s, t, θ, e =>
    open Classical in
    if s = t then some [t]
    else if θ = alpha G M t then
      (pathConstruction G M par mie fuel s (par t) θ.flip (mie (par t))).map (· ++ [t])
    else
      let y := (splitInc G M par t e).1
      let z := (splitInc G M par t e).2
      match pathConstruction G M par mie fuel s y (rho G M e) (mie y),
          pathConstruction G M par mie fuel t z (rho G M e) (mie z) with
      | some Y, some Z => some (Y ++ Z.reverse)
      | _, _ => none

/-- "The call returns `L`": for every large enough fuel the procedure returns `some L`. -/
def PCReturns (G : SimpleGraph V) (M : G.Subgraph) (par : ExtV V → ExtV V)
    (mie : ExtV V → Sym2 (ExtV V)) (s t : ExtV V) (θ : Parity) (e : Sym2 (ExtV V))
    (L : List (ExtV V)) : Prop :=
  ∃ fuel₀, ∀ fuel ≥ fuel₀, pathConstruction G M par mie fuel s t θ e = some L

end ForgetAlt


