-- Prove2me | Definitions.Def_HardyCausaloid_Fiducial
-- name    : HardyCausaloid_Fiducial
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:17:04.884084+00:00
-- url     : https://prove2.me/theorems/41f80ad2-b9c5-4202-bc9f-eb57d21357d1
-- title:
--   Sufficient and fiducial sets of labels, and the state vector $\mathbf p(R_1)$
-- statement:
--   Let $q(\alpha,s)$ be a table of probabilities indexed by labels $\alpha$ and generalised preparations $s$ (for example the table $p_\alpha(s)$ of a region). For a finite set $\Omega$ of labels the **state vector** is
--   $$\mathbf p(s)=\big(q(l,s)\big)_{l\in\Omega}\in\mathbb R^{\Omega}\qquad(14).$$
--   $\Omega$ is **sufficient** if for every label $\alpha$ there is one vector $\mathbf r_\alpha\in\mathbb R^\Omega$ with
--   $$q(\alpha,s)=\mathbf r_\alpha\cdot\mathbf p(s)\quad\text{for every }s\qquad(15),$$
--   and **fiducial** (just sufficient) if it is sufficient and no proper subset of it is sufficient.
--
--   Fiducial sets are the first level of physical compression: a short list of probabilities from which all others follow linearly.
--
--   **Formalization Note** The vector $\mathbf r_\alpha$ is chosen before $s$: one vector serves every preparation. "Just sufficient" is read as inclusion-minimal.
-- source:
--   Hardy, Towards Quantum Gravity: A Framework for Probabilistic Theories with Non-Fixed Causal Structure, arXiv:gr-qc/0608043v1, §4.2, eqs. (14)–(15), pp.11–12

import Mathlib

set_option autoImplicit false

namespace HardyCausaloid

universe u v

variable {A : Type u} {S : Type v}

/-- **The state vector of a finite list of labels**, Hardy, arXiv:gr-qc/0608043v1, §4.2,
eq. (14), p.11: for a probability table `q α s` (the probability `p_α` of the label `α` under
the generalised preparation `s`) and a finite set `Ω` of labels, `stateVec q Ω s` is the vector
`p(R₁) = (p_l)_{l ∈ Ω}` of the probabilities of the labels in `Ω` under `s`. -/
def stateVec (q : A → S → ℝ) (Ω : Finset A) (s : S) : Ω → ℝ :=
  fun l => q l.1 s

/-- **A sufficient set of labels**, Hardy, arXiv:gr-qc/0608043v1, §4.2, eqs. (14)–(15), p.11
("there exist vectors rα1(R1) such that a general probability is given by the linear equation
pα1 = rα1(R1) · p(R1)"). The finite set `Ω` is sufficient for the table `q` if for every label
`α` there is one vector `r : ℝ^Ω` with `q α s = r · p_Ω(s)` for every generalised preparation
`s`.

**Formalization Note** The vector `r` is chosen before `s`: one `r` serves every preparation. -/
def Sufficient (q : A → S → ℝ) (Ω : Finset A) : Prop :=
  ∀ α : A, ∃ r : Ω → ℝ, ∀ s : S, q α s = r ⬝ᵥ stateVec q Ω s

/-- **A fiducial set** (a *just* sufficient set), Hardy, arXiv:gr-qc/0608043v1, §4.2, eq. (14)
and p.12 ("We will call Ω1 the fiducial set in region R1"). `Ω` is sufficient for `q` and no
proper subset of `Ω` is sufficient.

**Formalization Note** "Just sufficient" is read as inclusion-minimal among sufficient finite
sets. -/
def Fiducial (q : A → S → ℝ) (Ω : Finset A) : Prop :=
  Sufficient q Ω ∧ ∀ Ω' : Finset A, Ω' ⊂ Ω → ¬ Sufficient q Ω'

end HardyCausaloid


