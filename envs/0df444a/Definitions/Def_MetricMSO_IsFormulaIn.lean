-- Prove2me | Definitions.Def_MetricMSO_IsFormulaIn
-- name    : MetricMSO_IsFormulaIn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:42:17.83706+00:00
-- url     : https://prove2.me/theorems/582e7b32-2a37-44cf-aee7-410415f47750
-- title:
--   A formula $\varphi(X_1,\dots,X_r)$ whose free variables are exactly the displayed set variables
-- statement:
--   $\varphi(X_1,\dots,X_r)$ is a formula whose free variables are exactly the displayed set variables, with $r_V$ vertex-set variables and $r_E$ edge-set variables. A sentence is the case $r_V=r_E=0$.
--
--   Exactness matters: each displayed variable occurs in $\varphi$, so $r_V+r_E\le|\varphi|$, and the number of satisfying assignments of a short formula is not inflated by unused variables.
--
--   **Formalization Note** Free set variables have the levels below $r_V$ and $r_E$. Vertex-set variables are listed before edge-set variables; the paper's $X_i$ are in any order, which changes nothing.
-- source:
--   Chakraborty, Ordyniak, Siebertz, Model Checking for Metric Extensions of MSO (arXiv:2610.41974, sha256 ad3c586330b037548a2b4a977081284996698f39c1b55c17b91cb81a536d3dd9), §2.7, p.16 (PDF 18)

import Mathlib
import Definitions.Def_MetricMSO_Formula

namespace MetricMSO

namespace Formula

/-- `scopedAt φ dV dE dS dES`: every variable of `φ` refers to a variable of the context, i.e.
every vertex, edge, vertex-set and edge-set variable occurring at a position under `kV, kE, kS,
kES` quantifiers of the respective sorts has level `< dV + kV`, `< dE + kE`, `< dS + kS`,
`< dES + kES`. -/
def scopedAt : Formula → ℕ → ℕ → ℕ → ℕ → Bool
  | ff, _, _, _, _ => true
  | adj x y, dV, _, _, _ => x < dV && y < dV
  | eqV x y, dV, _, _, _ => x < dV && y < dV
  | eqE e f, _, dE, _, _ => e < dE && f < dE
  | inc e x, dV, dE, _, _ => e < dE && x < dV
  | memV x X, dV, _, dS, _ => x < dV && X < dS
  | memE e Y, _, dE, _, dES => e < dE && Y < dES
  | vpred _ x, dV, _, _, _ => x < dV
  | epred _ e, _, dE, _, _ => e < dE
  | cardV _ _ X, _, _, dS, _ => X < dS
  | cardE _ _ Y, _, _, _, dES => Y < dES
  | sp P s t, dV, _, dS, _ => P < dS && s < dV && t < dV
  | eqgc C x y u v, dV, _, dS, _ => C < dS && x < dV && y < dV && u < dV && v < dV
  | neg φ, dV, dE, dS, dES => scopedAt φ dV dE dS dES
  | and φ ψ, dV, dE, dS, dES => scopedAt φ dV dE dS dES && scopedAt ψ dV dE dS dES
  | exV φ, dV, dE, dS, dES => scopedAt φ (dV + 1) dE dS dES
  | exE φ, dV, dE, dS, dES => scopedAt φ dV (dE + 1) dS dES
  | exVS φ, dV, dE, dS, dES => scopedAt φ dV dE (dS + 1) dES
  | exES φ, dV, dE, dS, dES => scopedAt φ dV dE dS (dES + 1)

/-- `usesVS φ i`: the vertex-set variable of level `i` occurs in `φ`. -/
def usesVS (i : ℕ) : Formula → Bool
  | memV _ X => X == i
  | cardV _ _ X => X == i
  | sp P _ _ => P == i
  | eqgc C _ _ _ _ => C == i
  | neg φ => usesVS i φ
  | and φ ψ => usesVS i φ || usesVS i ψ
  | exV φ => usesVS i φ
  | exE φ => usesVS i φ
  | exVS φ => usesVS i φ
  | exES φ => usesVS i φ
  | _ => false

/-- `usesES φ i`: the edge-set variable of level `i` occurs in `φ`. -/
def usesES (i : ℕ) : Formula → Bool
  | memE _ Y => Y == i
  | cardE _ _ Y => Y == i
  | neg φ => usesES i φ
  | and φ ψ => usesES i φ || usesES i ψ
  | exV φ => usesES i φ
  | exE φ => usesES i φ
  | exVS φ => usesES i φ
  | exES φ => usesES i φ
  | _ => false

end Formula

/-- **`φ = φ(X₁, …, X_{rV}, Y₁, …, Y_{rE})`: a formula whose free variables are exactly the
displayed set variables.**

Chakraborty, Ordyniak, Siebertz (arXiv:2610.41974, sha256 prefix ad3c5863), §2.7, p.16 (PDF 18):
"Let φ(X1, . . . , Xr) be a formula whose free variables are exactly the displayed set variables."

`IsFormulaIn φ rV rE` says that the free variables of `φ` are vertex-set variables of levels
`0, …, rV − 1` and edge-set variables of levels `0, …, rE − 1` (no free vertex or edge variable),
and that each of these `rV + rE` variables occurs in `φ`. A sentence is the case `rV = rE = 0`.

**Formalization Note** Quantified set variables get the levels `≥ rV` (resp. `≥ rE`), so an
occurrence of a level `i < rV` is an occurrence of the free variable `X_{i+1}`. The vertex-set
variables are listed before the edge-set variables; the paper's `X_i` are in any order, which
changes nothing. -/
def IsFormulaIn (φ : Formula) (rV rE : ℕ) : Prop :=
  φ.scopedAt 0 0 rV rE = true ∧ (∀ i < rV, φ.usesVS i = true) ∧ (∀ i < rE, φ.usesES i = true)

end MetricMSO


