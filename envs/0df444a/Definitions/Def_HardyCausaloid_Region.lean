-- Prove2me | Definitions.Def_HardyCausaloid_Region
-- name    : HardyCausaloid_Region
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:17:45.770149+00:00
-- url     : https://prove2.me/theorems/f23f19f3-3495-409a-a0be-eb5d4201b0a0
-- title:
--   Regions, gluing with a generalised preparation, and probability tables
-- statement:
--   For a finite set $O$ of locations, the **region** $R_O$ is the union of the elementary regions $R_x$, $x\in O$ (eq. (2)), so a **label of $R_O$** is a family $\alpha=(\alpha_x)_{x\in O}$ of labels at the locations of $O$.
--
--   For a label $\alpha$ of $R_O$ and a total label $s$, the **glued** total label equals $\alpha$ on $O$ and $s$ off $O$; $s$ plays the **generalised preparation** $(Y_{R-R_O},F_{R-R_O})$ in $R-R_O$, and its values on $O$ are ignored. The **probability table** of the region is
--   $$p_\alpha(s)=\mathrm{Prob}\big(Y^{\alpha}_{R_O}\cup Y_{R-R_O}\ \big|\ F^{\alpha}_{R_O}\cup F_{R-R_O}\big)\qquad(11),$$
--   and the **elementary table** at $x$ is the same for $O=\{x\}$, with labels at $x$. For labels $\alpha_1$ of $R_{O_1}$ and $\alpha_2$ of $R_{O_2}$ the **joint label** $\alpha_1\alpha_2$ of $R_{O_1}\cup R_{O_2}$ is $\alpha_1$ on $O_1$ and $\alpha_2$ on $O_2\setminus O_1$ (eq. (18)); for a setting $F_2$ and an outcome family $\beta_2$ on $O_2$, their pairing is a label of $R_{O_2}$.
--
--   These are the probabilities $p_{\alpha_1}$ of (11) and $p_{\alpha_1\alpha_2}$ of (18) on which first and second level physical compression act.
--
--   **Formalization Note** The joint label is used only for disjoint $O_1$, $O_2$, where it is the pair $(\alpha_1,\alpha_2)$.
-- source:
--   Hardy, Towards Quantum Gravity: A Framework for Probabilistic Theories with Non-Fixed Causal Structure, arXiv:gr-qc/0608043v1, §3, eqs. (2)–(6), pp.8–9; §4.2, eqs. (10)–(11), p.11; §4.3, eq. (18), p.12

import Mathlib
import Definitions.Def_HardyCausaloid_Model

set_option autoImplicit false

namespace HardyCausaloid

universe u v w

variable {X : Type u} {Setting : X → Type v} {Outcome : (x : X) → Setting x → Type w}

/-- **Labels of a region**, Hardy, arXiv:gr-qc/0608043v1, §3, eqs. (2)–(6), pp.8–9. The region
`R_O` of a finite set `O` of locations is the union of the elementary regions `R_x`, `x ∈ O`
(eq. (2)), so a label `α` of `R_O` (a pair (outcome set, procedure) in `R_O`) is a label `α x`
at every location `x ∈ O`. -/
abbrev Lab (Setting : X → Type v) (Outcome : (x : X) → Setting x → Type w) (O : Finset X) :
    Type (max u v w) :=
  ∀ x : O, Label Setting Outcome x.1

variable [DecidableEq X]

/-- **Gluing a regional label with a generalised preparation**, Hardy, arXiv:gr-qc/0608043v1,
§4.2, eqs. (10)–(11), p.11, and §4.3, eq. (18), p.12. `glue O α s` is the total label equal to
`α` on `O` and to `s` off `O`.

**Formalization Note** The total label `s` plays the generalised preparation
`(Y_{R−R_O}, F_{R−R_O})` in `R − R_O`; its values on `O` are ignored. -/
def glue (O : Finset X) (α : Lab Setting Outcome O) (s : ∀ x, Label Setting Outcome x) :
    ∀ x, Label Setting Outcome x :=
  fun x => if h : x ∈ O then α ⟨x, h⟩ else s x

/-- **The joint label of two regions**, Hardy, arXiv:gr-qc/0608043v1, §4.3, eq. (18), p.12:
for labels `α₁` of `R_{O₁}` and `α₂` of `R_{O₂}`, `joinLab α₁ α₂` is the label `α₁α₂` of
`R_{O₁} ∪ R_{O₂} = R_{O₁ ∪ O₂}`: `α₁` on `O₁` and `α₂` on `O₂ \ O₁`.

**Formalization Note** It is used only for disjoint `O₁`, `O₂`, where it is the pair
`(α₁, α₂)`. -/
def joinLab {O₁ O₂ : Finset X} (α₁ : Lab Setting Outcome O₁) (α₂ : Lab Setting Outcome O₂) :
    Lab Setting Outcome (O₁ ∪ O₂) :=
  fun x => if h : x.1 ∈ O₁ then α₁ ⟨x.1, h⟩
    else α₂ ⟨x.1, (Finset.mem_union.1 x.2).resolve_left h⟩

/-- **The label of a setting and an outcome family on a region**, Hardy,
arXiv:gr-qc/0608043v1, §4.5, p.16 ("recall that α2 labels a particular outcome of a particular
measurement"): `labOf F β` pairs the setting `F x` with the outcome `β x` at each `x ∈ O`. -/
def labOf {O : Finset X} (F : ∀ x : O, Setting x.1) (β : ∀ x : O, Outcome x.1 (F x)) :
    Lab Setting Outcome O :=
  fun x => ⟨F x, β x⟩

/-- **The probability table of a region**, Hardy, arXiv:gr-qc/0608043v1, §4.2, eq. (11), p.11:
`regionTable M O α s = p_α = Prob(Y^α_{R_O} ∪ Y_{R−R_O} | F^α_{R_O} ∪ F_{R−R_O})`, the
probability of the label `α` in `R_O` under the generalised preparation `s` in `R − R_O`. -/
def regionTable (M : Model Setting Outcome) (O : Finset X) (α : Lab Setting Outcome O)
    (s : ∀ x, Label Setting Outcome x) : ℝ :=
  M.P (glue O α s)

/-- **The probability table of an elementary region**, Hardy, arXiv:gr-qc/0608043v1, §4.2,
eq. (11), p.11, for `R₁ = R_x`: `elemTable M x α s = Prob(Y^α_x ∪ Y_{R−R_x} | F^α_x ∪
F_{R−R_x})`, the probability of the label `α` at `x` under the generalised preparation `s`
(whose value at `x` is ignored). It is `regionTable M {x}` with labels of `{x}` identified with
labels at `x`. -/
def elemTable (M : Model Setting Outcome) (x : X) (α : Label Setting Outcome x)
    (s : ∀ x, Label Setting Outcome x) : ℝ :=
  M.P (Function.update s x α)

end HardyCausaloid


