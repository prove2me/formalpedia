-- Prove2me | Definitions.Def_SurelyBetter_CLB_Supplement_Family
-- name    : SurelyBetter_CLB_Supplement_Family
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T00:48:19.481862+00:00
-- url     : https://prove2.me/theorems/e8160a92-cb81-45a8-92ac-f2e3ee0cd6a7
-- title:
--   Definitions 3–4, p. 7632 — the family F^{E,F,z,h}, the set H(z) and the better-than sets G(k)
-- statement:
--   The setting is the published utility-space model `SurelyBetter.CLB.Model`: $S$ is a finite set of states, $U=u(X)$, and an act is represented by its utility profile $v:S\to U$.
--
--   1. **The family $\mathcal F^{E,F,z,h}$** (Definition 3). Fix events $E,F\subseteq S$, a lottery $z$ with utility $u(z)$, and an act $h$. $\mathcal F^{E,F,z,h}$ is the set of acts $f$ that are constant on $E\setminus F$ (value $f(E\setminus F)$), constant on $F\setminus E$ (value $f(F\setminus E)$), satisfy
--   $$\tfrac12 u(f(s))+\tfrac12 u(z)=\tfrac12 u(f(E\setminus F))+\tfrac12 u(f(F\setminus E))\quad\text{for all } s\in F\cap E,$$
--   and agree with $h$ on $(E\cup F)^c$.
--   2. **The set $H(z)$** (Definition 4). $H(z)=\{(a,b)\in U\times U: a+b-u(z)\in U\}$, where the first coordinate stands for the utility on $E\setminus F$ and the second for the utility on $F\setminus E$.
--   3. **Better-than sets** (Definition 4). For a preference represented by $V$ as in (6) and an act $k$,
--   $$G(k)=\{(u(f(E\setminus F)),u(f(F\setminus E))): f\in\mathcal F^{E,F,z,h},\ f\succsim k\}.$$
--
--   These sets describe preferences restricted to a two-dimensional slice of utility space; Theorem 5 is stated in terms of them.
--
--   **Formalization Note** In utility space $\sim$ between lotteries is equality of utilities, so the indifference conditions of Definition 3 become equations between profile values, and $f\succsim k$ is $V(u\circ k)\le V(u\circ f)$. The family is written exactly as Definition 3 states it; when $E\cap F=\emptyset$ the condition on $F\cap E$ is empty. Definition 4 writes $z\in Z$ and Definitions 3 and 5 write $z\in X$; only $u(z)$ enters, so both are covered by an arbitrary $u(z)\in U$.
-- source:
--   Ghili & Klibanoff, If It Is Surely Better, Do It More? Implications for Preferences Under Ambiguity, Management Science 67(12) (2021), p. 7632, Definition 3, Definition 4 (G(k), H(z))

import Mathlib
import Definitions.Def_Supermodularity_Lattices_InducedSetOrder
import Definitions.Def_SurelyBetter_CLB_Model

namespace SurelyBetter.CLB.Supplement
open SurelyBetter.CLB

variable {S : Type*}

/-- Definition 3, p. 7632, in utility space: for events `E, F`, the utility `uz = u(z)` of the
default lottery `z`, and the utility profile `hp = u ∘ h` of an act `h`, `famF U E F uz hp` is the
set of profiles `f` of acts that are constant on `E \ F`, constant on `F \ E`, satisfy
`½ f(s) + ½ u(z) = ½ f(E \ F) + ½ f(F \ E)` for every `s ∈ F ∩ E`, and agree with `h` off `E ∪ F`. -/
def famF (U : Set ℝ) (E F : Set S) (uz : ℝ) (hp : S → ℝ) : Set (S → ℝ) :=
  {f | f ∈ Profiles U ∧
    (∀ s ∈ E \ F, ∀ t ∈ E \ F, f s = f t) ∧
    (∀ s ∈ F \ E, ∀ t ∈ F \ E, f s = f t) ∧
    (∀ s ∈ F ∩ E, ∀ t ∈ E \ F, ∀ t' ∈ F \ E, f s / 2 + uz / 2 = f t / 2 + f t' / 2) ∧
    (∀ s, s ∉ E ∪ F → f s = hp s)}

/-- Definition 4, p. 7632: `H(z) = {(a, b) ∈ u(X) × u(X) : a + b − u(z) ∈ u(X)}`; the first
coordinate is the utility on `E \ F`, the second the utility on `F \ E`. -/
def Hz (U : Set ℝ) (uz : ℝ) : Set (ℝ × ℝ) :=
  {q | q.1 ∈ U ∧ q.2 ∈ U ∧ q.1 + q.2 - uz ∈ U}

/-- Definition 4, p. 7632: the better-than set
`G(k) = {(u(f(E \ F)), u(f(F \ E))) : f ∈ F^{E,F,z,h} and f ≿ k}` of the act with profile `kp`. -/
def betterSet (U : Set ℝ) (V : (S → ℝ) → ℝ) (E F : Set S) (uz : ℝ) (hp kp : S → ℝ) :
    Set (ℝ × ℝ) :=
  {q | ∃ f ∈ famF U E F uz hp, (∀ t ∈ E \ F, f t = q.1) ∧ (∀ t ∈ F \ E, f t = q.2) ∧
    V kp ≤ V f}

end SurelyBetter.CLB.Supplement


