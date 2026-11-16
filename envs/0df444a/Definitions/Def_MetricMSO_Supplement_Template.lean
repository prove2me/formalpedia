-- Prove2me | Definitions.Def_MetricMSO_Supplement_Template
-- name    : MetricMSO_Supplement_Template
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:55:03.147211+00:00
-- url     : https://prove2.me/theorems/cd02429e-275a-4e31-a6cb-d4d6354b51f4
-- title:
--   Packing-covering templates, one-cover formulas and their inputs
-- statement:
--   A **packing-covering template** (Definition 6.1) is an expression
--
--   $$\Phi(\bar X;\bar\delta,\bar\rho):=\psi(\bar X)\wedge\bigwedge_{a\in A}\mathrm{Sep}_{\delta_a}(X_{i_a},X_{j_a})\wedge\bigwedge_{b\in B}\mathrm{Cover}_{\rho_b}(U_b,X_{\ell_b}),$$
--
--   where $X_1,\dots,X_p$ are vertex-set variables, the side formula $\psi$ is a $\mathrm{CMSO}_2[\mathrm{SP},\mathrm{EqGC}]$ formula, $A,B$ are finite index sets, $i_a,j_a,\ell_b\in\{1,\dots,p\}$, each target $U_b$ is $V(G)$ or an input predicate $L_j$, and $\delta_a,\rho_b$ are numerical parameter symbols whose values are given with the input.
--
--   Its **satisfying assignments** on a graph $G$ under a valuation $\eta$ are the tuples $(S_1,\dots,S_p)$ of vertex sets with $G\models\psi(S_1,\dots,S_p)$ and every separation and covering atom true under $\eta$. The **length** $|\Phi|$ is the length of its binary code (side formula, index data, symbol indices), not counting the threshold values.
--
--   A **one-cover formula** (end of Definition 6.2) is a template without separation atoms and with exactly one covering atom, $\Phi(\bar X;\rho)=\psi(\bar X)\wedge\mathrm{Cover}_\rho(U,S)$.
--
--   The module also fixes the binary input of a template task: the task, the instance code, the template code, the binary values of the symbols, and for the weighted tasks the signed binary vertex weights; its length is $N$.
--
--   **Formalization Note** The side formula's free variables are required to be among $X_1,\dots,X_p$ (a set variable may occur only in the metric atoms).
-- source:
--   Chakraborty, Ordyniak, Siebertz, Model Checking for Metric Extensions of MSO (arXiv:2610.41974, sha256 ad3c5863…), Definition 6.1, p.30 (PDF 32); §1, pp.7–8 (PDF 9–10); Definition 6.2, p.30 (PDF 32)

import Mathlib
import Definitions.Def_ExponomialAssortment_FPTAS_Machine
import Definitions.Def_MetricMSO_encodeInput
import Definitions.Def_MetricMSO_Supplement_XSat

set_option autoImplicit false

namespace MetricMSO.Supplement

open MetricMSO
open ExponomialAssortment.FPTAS (encodeNat)

/-- **A packing-covering template** (Definition 6.1, p.30 (PDF 32); §1, p.7 (PDF 9)):
"Φ(X̄; δ̄, ρ̄) := ψ(X̄) ∧ ⋀_{a∈A} Sep_{δa}(X_{ia}, X_{ja}) ∧ ⋀_{b∈B} Cover_{ρb}(U_b, X_{ℓb}). A and B
are finite index sets, and ia, ja, ℓb ∈ {1, . . . , p}. Each target set U_b is either V(G) or one
of the unary input sets L1, . . . , Lq."

* `p`: the number of selected vertex-set variables `X₁, …, X_p` (de Bruijn levels `0, …, p − 1`);
* `ψ`: the side formula, a CMSO2[SP, EqGC] formula (published `MetricMSO.Formula`);
* `seps`: the separation atoms, a triple `(δ, i, j)` standing for `Sep_δ(X_{i+1}, X_{j+1})`;
* `covers`: the covering atoms, a triple `(ρ, U, ℓ)` standing for `Cover_ρ(U, X_{ℓ+1})`, with
  `U = none` for `V(G)` and `U = some j` for `L_{j+1}`.

`δ` and `ρ` are indices of numerical parameter symbols, whose values are given with the input. -/
structure Template where
  p : ℕ
  ψ : Formula
  seps : List (ℕ × ℕ × ℕ)
  covers : List (ℕ × Option ℕ × ℕ)

namespace Template

/-- The template is well formed: the free variables of `ψ` are among `X₁, …, X_p` (vertex-set
variables; no free vertex, edge or edge-set variable) and every separation and covering atom names
selected sets among `X₁, …, X_p`. -/
def WellFormed (T : Template) : Prop :=
  T.ψ.scopedAt 0 0 T.p 0 = true ∧ (∀ s ∈ T.seps, s.2.1 < T.p ∧ s.2.2 < T.p) ∧
    ∀ c ∈ T.covers, c.2.2 < T.p

/-- **The satisfying assignments** of a template on an instance `I` under the valuation `η` of the
numerical symbols (symbol `δ` has the value `η[δ]`): the assignments `(S₁, …, S_p)` of vertex sets
with `G ⊨ ψ(S₁, …, S_p)`, every separation atom and every covering atom true.

**Formalization Note** An atom whose symbol index lies outside `η`, or whose set index is `≥ p`
(excluded by `WellFormed`), is false. -/
def Sol (T : Template) (I : Instance) (η : List ℕ) : Set (Assignment I T.p 0) :=
  {A | A ∈ MetricMSO.Sol I T.ψ T.p 0 ∧
    (∀ s ∈ T.seps, ∃ d, η[s.1]? = some d ∧ ∃ (hi : s.2.1 < T.p) (hj : s.2.2 < T.p),
      SepHolds I.G d (A.1 ⟨s.2.1, hi⟩) (A.1 ⟨s.2.2, hj⟩)) ∧
    (∀ c ∈ T.covers, ∃ r, η[c.1]? = some r ∧ ∃ hl : c.2.2 < T.p,
      CoverHolds I.G r (targetSet I c.2.1) (A.1 ⟨c.2.2, hl⟩))}

/-- Code of an optional label index: `none` (the target `V(G)`) is `[false]`, `some j` is `true`
followed by `j` in binary. -/
def encodeTarget : Option ℕ → List Bool
  | none => [false]
  | some j => true :: encodeNat j

/-- **Binary code of a template**: `p`, the code of the side formula, then the number and the
triples of the separation atoms, then the number and the triples of the covering atoms. Symbols are
written by their indices, never by their values. -/
def encode (T : Template) : List Bool :=
  encodeNat T.p ++ T.ψ.encode ++
  encodeNat T.seps.length ++
    (T.seps.map fun s => encodeNat s.1 ++ encodeNat s.2.1 ++ encodeNat s.2.2).flatten ++
  encodeNat T.covers.length ++
    (T.covers.map fun c => encodeNat c.1 ++ encodeTarget c.2.1 ++ encodeNat c.2.2).flatten

/-- **The template length `|Φ|`**: the length of its code. It counts the side formula, the index
data and the occurrences of the numerical symbols, but not the binary values of the thresholds
(Definition 2.12, p.18; Definition 6.2, p.30: "We count the numerical symbol in |Φ|, but we do not
count the binary value assigned to it"). -/
def length (T : Template) : ℕ := T.encode.length

/-- **One-cover formulas** (end of Definition 6.2, p.30 (PDF 32); §1, p.8 (PDF 10)):
"Φ(X̄; ρ) = ψ(X̄) ∧ Cover_ρ(U, S), where ψ ∈ CMSO2[SP, EqGC], the target set U is given by the
input, and S is one distinguished free set among X̄": no separation atom and exactly one covering
atom. -/
def IsOneCover (T : Template) : Prop := T.seps = [] ∧ T.covers.length = 1

end Template

/-- Binary code of a valuation of the numerical parameter symbols: the number of symbols, then
each value in binary. -/
def encodeValuation (η : List ℕ) : List Bool :=
  encodeNat η.length ++ (η.map encodeNat).flatten

open Classical in
/-- **The binary input for a template task**, of length `N` ("we write N for the total binary input
length, including the formula, numerical bounds, and any weights", p.30 (PDF 32)): the task, the
instance (graph and input predicates, published `encodeInstance`), the template, the values of the
numerical symbols, and for the four weighted tasks the signed binary vertex weights (published
`encodeWeights`). No decomposition is part of the input. -/
noncomputable def templateInput (task : Task) (I : Instance) (T : Template) (η : List ℕ)
    (w : Weights I T.p 0) : List Bool :=
  encodeNat task.index ++ encodeInstance I ++ T.encode ++ encodeValuation η ++
    (if task.weighted then encodeWeights w else [])

end MetricMSO.Supplement


