-- Prove2me | Definitions.Def_BNCovPack_Routing_Algorithm
-- name    : BNCovPack_Routing_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T19:17:16.777501+00:00
-- url     : https://prove2.me/theorems/ad039afb-4c10-4279-840e-b52fbf689e8c
-- title:
--   The integral online routing algorithm of Section 5.2
-- statement:
--   The algorithm keeps the state of the fractional scheme together with the integral edge usage $\chi(e)$ (the number of chosen paths through $e$) and the number of served requests, all zero initially. When request $r_i$ with path list $\mathcal P(r_i)$ arrives:
--
--   1. the fractional scheme raises the flows $f(r_i, \cdot)$;
--   2. let $\Phi^{\mathrm{start}}$ be the potential before this increase; the request is served (with bandwidth $1$) on the first flow path $P$ of $\mathcal P(r_i)$ (a path whose flow $f(r_i, P)$ is positive, in list order) such that serving it on $P$, i.e. adding $1$ to $\chi(e)$ for every $e \in P$ and to the number of served requests, gives a potential, computed with the new flows, at most $\Phi^{\mathrm{start}}$;
--   3. if there is no such path, the request is rejected and $\chi$ is unchanged.
--
--   With the paper's parameters, for path systems whose paths have at most $P(\max)$ edges, the fractional scheme runs with $\ell = P(\max) + 1$ and $B' = 2\ln(1+\ell) = 2\ln(P(\max)+2)$, and the potential uses the rounding scale $B = \exp(1 + \ln(2m)/u(\min)) - 1$.
--
--   **Formalization Note** The paper leaves the choice among good paths open; the formalization fixes the first good path in list order. Only flow paths are candidates, as in Lemma 5.3 ("serving the request on some flow path"); a request whose flow was not increased therefore has no candidate and is rejected. $P(\max)$ is a parameter (the paper's length of the longest path in the graph, known in advance); the theorems assume every path has at most $P(\max)$ edges. The paper overloads $B$; here $B'$ is the fractional scheme's parameter and $B$ the rounding scale.
-- source:
--   Buchbinder, Naor, Online Primal-Dual Algorithms for Covering and Packing, Math. Oper. Res. (2009), DOI 10.1287/moor.1080.0363, p. 15, Section 5.2 (the online rounding rule) and p. 5 (the scheme)

import Mathlib
import Definitions.Def_BNCovPack_Routing_Routing
import Definitions.Def_BNCovPack_Routing_FracScheme
import Definitions.Def_BNCovPack_Routing_Potential

namespace BNCovPack.Routing

/-- State of the integral online routing algorithm of §5.2 (pp. 15–16): the fractional scheme's
state, the integral edge usage `chi e = χ(e)` (number of chosen paths that use `e`) and the
number `served = ∑_{r_i} χ(r_i)` of requests served so far. -/
structure State (E : Type*) where
  frac : FracState E
  chi : E → ℕ
  served : ℕ

/-- The initial state: all-zero fractional state, no edge used, no request served. -/
def State.init (E : Type*) : State E where
  frac := FracState.init E
  chi := fun _ => 0
  served := 0

/-- Serving a request on path `P` adds one to `χ(e)` for every `e ∈ P`. -/
def addPath {E : Type*} [DecidableEq E] (chi : E → ℕ) (P : Finset E) : E → ℕ :=
  fun e => chi e + if e ∈ P then 1 else 0

open Classical in
/-- One round of the algorithm (p. 15) on arrival of request `r_i` with path list `ps = P(r_i)`:
1. the fractional scheme `fracStep` raises the flows of `r_i`; `fs` is the list of flows
   `f(r_i, P)` it gave to the paths of `ps` (the last entry of the new `flows`);
2. with `Φ^start` the potential before the flows were raised, the request is served on the
   first flow path `P` of `ps` (in list order: a path whose flow `f(r_i, P)` is positive) such
   that serving it on `P` gives potential `≤ Φ^start`, computed with the new flows;
3. if there is no such path the request is rejected (`χ` unchanged); in particular a request
   whose flow was not increased is rejected.
The total flow is `routingValue` of the flows and the loads are the fractional state's loads. -/
noncomputable def step {E : Type*} [Fintype E] [DecidableEq E] (u : E → ℝ) (ℓ : ℕ)
    (Bf B : ℝ) (st : State E) (ps : List (Finset E)) : State E :=
  let fr' := fracStep u ℓ Bf st.frac ps
  let Φstart := potential u B (routingValue st.frac.flows) st.frac.load st.chi st.served
  let fs := fr'.flows.getLastD []
  let good : Finset E × ℝ → Bool := fun Py =>
    decide (0 < Py.2) &&
      decide (potential u B (routingValue fr'.flows) fr'.load (addPath st.chi Py.1)
        (st.served + 1) ≤ Φstart)
  match (ps.zip fs).find? good with
  | some Py => { frac := fr', chi := addPath st.chi Py.1, served := st.served + 1 }
  | none => { frac := fr', chi := st.chi, served := st.served }

/-- The state of the algorithm with fractional parameters `ℓ`, `Bf` and rounding scale `B` after
the requests of `σ` have arrived, in order. -/
noncomputable def run {E : Type*} [Fintype E] [DecidableEq E] (u : E → ℝ) (ℓ : ℕ) (Bf B : ℝ)
    (σ : List (List (Finset E))) : State E :=
  σ.foldl (step u ℓ Bf B) (State.init E)

/-- The algorithm of §5.2 with the paper's parameters, for path systems whose paths have at most
`Pmax` edges: the fractional scheme with `ℓ = Pmax + 1` (a primal constraint has support `P` and
`Z(r_i)`) and `B' = 2 ln(1 + ℓ) = 2 ln(Pmax + 2)`, and the rounding scale
`B = exp(1 + ln(2m)/u(min)) − 1`. -/
noncomputable def algorithm {E : Type*} [Fintype E] [Nonempty E] [DecidableEq E] (u : E → ℝ)
    (Pmax : ℕ) (σ : List (List (Finset E))) : State E :=
  run u (Pmax + 1) (2 * Real.log ((Pmax : ℝ) + 2)) (roundingScale u) σ

end BNCovPack.Routing


