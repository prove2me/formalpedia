-- Prove2me | Definitions.Def_PCNonBool_stepAssignment
-- name    : PCNonBool_stepAssignment
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:29:07.192225+00:00
-- url     : https://prove2.me/theorems/24eafa97-95ff-435f-b6d3-e2780c0b07ac
-- title:
--   Restriction $\rho_\ell$ of one round of Algorithm 1
-- statement:
--   In round $\ell$, after splitting on $(i,j,j')$, Algorithm 1 extends its restriction by (recall $-1$ = true, $1$ = false):
--
--   1. (line 12) $x_{i,h}\leftarrow1$ for $h\in N_{G_{\ell-1}}(i)\setminus\{j,j'\}$;
--   2. (lines 13–14) $x_{i',h}\leftarrow1$ for every other remaining pigeon $i'$ and $h\in\{j,j'\}\cap N_{G_{\ell-1}}(i')$;
--   3. (line 21) the assignment induced by a matching $M_\ell$ of $S_\ell$ in $G'_\ell$: $x_{u,M(u)}\leftarrow-1$ for $u\in S_\ell$; $x_{u,h}\leftarrow1$ for the other holes $h$ of $u$ in $G'_\ell$; and $x_{i',M(u)}\leftarrow1$ for every other pigeon $i'$ adjacent to $M(u)$.
--
--   All other variables are left untouched.
--
--   **Formalization Note** "Assignment induced by matching" is read as item 3: matched pigeons fly to their matched holes, and every other edge at a matched pigeon or hole is set to false.
-- source:
--   Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, On the Power of Polynomial Calculus over Non-Boolean Domains, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), Algorithm 1, lines 12–14 and 21, p.30 (PDF p.33)

import Mathlib
import Definitions.Def_PCNonBool_BipGraph
import Definitions.Def_PCNonBool_Var

namespace PCNonBool

/-- The new assignments of round `ℓ` of Algorithm 1 (Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, *On the Power of Polynomial Calculus over Non-Boolean Domains*, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), Algorithm 1, lines 12–14 and 21,
p.30 (PDF p.33)), with `Ua = U_{ℓ-1}`, `Va = V_{ℓ-1}`, the split triple `(i, j, j')`, the set
`S = S_ℓ ⊆ U'_ℓ` and the matching `M` of `S` into `V'_ℓ = Va \ {j, j'}`. Recall `-1` = true and
`1` = false. In this order:

* line 12: `x_{i,h} ← 1` for `h ∈ N_{G_{ℓ-1}}(i) \ {j, j'}`;
* lines 13–14: `x_{i',h} ← 1` for `i' ∈ Ua \ {i}` and `h ∈ {j, j'}` adjacent to `i'`;
* line 21 (the assignment induced by the matching `M`): `x_{u,M(u)} ← -1` for `u ∈ S`,
  `x_{u,h} ← 1` for `u ∈ S` and the other holes `h ∈ V'_ℓ`, and `x_{i',M(u)} ← 1` for every other
  pigeon `i' ∈ Ua \ {i}` adjacent to `M(u)`;
* every other variable is untouched (in particular `x_{i,j}`, `x_{i,j'}`, which PigeonSplit
  removes).

**Formalization Note** Line 21 says only "assignment induced by matching M_ℓ on S_ℓ in G'_ℓ"; it
is read as above: matched pigeons fly to their matched holes, and every other edge at a matched
pigeon or a matched hole is set to false. Variables at vertices removed in earlier rounds are
already restricted and do not occur. -/
def stepAssignment {F : Type*} [Field F] {U V : Type*} [DecidableEq U] [DecidableEq V]
    (G : BipGraph U V) (Ua : Finset U) (Va : Finset V) (i : U) (j j' : V) (S : Finset U)
    (M : U → V) : Var G → Option F :=
  fun e =>
    if e.1.1 = i ∧ e.1.2 ∈ Va ∧ e.1.2 ≠ j ∧ e.1.2 ≠ j' then some 1
    else if e.1.1 ∈ Ua ∧ e.1.1 ≠ i ∧ (e.1.2 = j ∨ e.1.2 = j') then some 1
    else if e.1.1 ∈ S ∧ e.1.2 = M e.1.1 then some (-1)
    else if e.1.1 ∈ S ∧ e.1.2 ∈ Va \ {j, j'} then some 1
    else if e.1.1 ∈ Ua ∧ e.1.1 ≠ i ∧ e.1.2 ∈ S.image M then some 1
    else none

end PCNonBool


