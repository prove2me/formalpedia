-- Prove2me | Definitions.Def_WatsonPseudodeterminism_MASeparation_Supplement_Models
-- name    : WatsonPseudodeterminism_MASeparation_Supplement_Models
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T07:28:30.04431+00:00
-- url     : https://prove2.me/theorems/f5bdd9cf-65f8-4e8c-9176-8db7a50c8008
-- title:
--   RP-type and error-parameterized psP-type protocols; complement of a partial function
-- statement:
--   Let $F:X\times Y\to\{0,1,\bot\}$ be a two-party partial function (valid inputs are those with $F(x,y)\ne\bot$) and let $d$ be a natural cost bound. All protocols below are a **single** public-coin distribution $D$ over deterministic protocol trees of depth at most $d$, with acceptance probability $D(x,y)=\Pr_{P\sim D}[P(x,y)=1]$.
--
--   1. An **RP-type protocol** of cost $d$ for $F$ satisfies, for all valid $(x,y)$,
--   $$F(x,y)=1\Rightarrow D(x,y)\ge 2/3,\qquad F(x,y)=0\Rightarrow D(x,y)=0.$$
--   2. The **complement** $\overline F$ swaps the values $0$ and $1$ on valid inputs and is $\bot$ exactly where $F$ is $\bot$.
--   3. An **$\varepsilon$-error psP-type protocol** of cost $d$ for $F$ satisfies, for **all** $(x,y)$, valid or invalid,
--   $$D(x,y)\in[0,\varepsilon]\cup[1-\varepsilon,1],$$
--   and, for valid $(x,y)$,
--   $$F(x,y)=1\Rightarrow D(x,y)\ge 1-\varepsilon,\qquad F(x,y)=0\Rightarrow D(x,y)\le \varepsilon.$$
--   A **psP-type protocol** is the case $\varepsilon=1/3$.
--
--   The pseudodeterministic gap on invalid inputs is what distinguishes psP from two-sided-error (BPP) protocols. These models are used for Theorem 1 ($\mathrm{ZPP}\not\subseteq\mathrm{psP}$) and its supporting results.
--
--   **Formalization Note** The protocol trees, the PMF of public randomness, the depth bound on the support and the acceptance probability are the base mission's published `Protocol` definition. The $\varepsilon$-error psP form is equivalent to §3's wording "a total $F'$ agreeing with $F$ has an $\varepsilon$-error randomized protocol" (take $F'(x,y)=[D(x,y)\ge1-\varepsilon]$ for $\varepsilon<1/2$), as remarked on p. 1.
-- source:
--   Thomas Watson, STOC 2027 submission #13 (October 2026), §1.1, p. 4 (RP-type and psP-type protocols); §1, p. 2 ("Recall ZPP = RP ∩ coRP") and §3, p. 8 (F̄); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/13.pdf

import Definitions.Def_WatsonPseudodeterminism_MASeparation_Protocol

namespace WatsonPseudodeterminism.MASeparation.Supplement

/-- §1.1, p. 4: an RP-type protocol of cost d is ONE distribution over depth-≤d trees with
completeness 2/3 and perfect soundness on valid inputs. -/
def RPProtocol {X Y : Type} (F : PartialFn X Y) (d : ℕ) : Prop :=
  ∃ D : RandomProtocol X Y, DepthBound D d ∧
    (∀ x y, F x y = some true → (2 / 3 : ℝ) ≤ acceptance D x y) ∧
    (∀ x y, F x y = some false → acceptance D x y = 0)

/-- The complement F̄: swaps 0 and 1 on valid inputs and keeps ⊥ (= `none`) invalid. -/
def complementFn {X Y : Type} (F : PartialFn X Y) : PartialFn X Y :=
  fun x y => (F x y).map (fun b => !b)

/-- §1.1, p. 4, with error parameter ε: ONE distribution over depth-≤d trees whose acceptance
lies in [0, ε] ∪ [1 − ε, 1] on EVERY input pair, valid or invalid, with thresholds 1 − ε and ε
on valid inputs. -/
def PsPProtocolErr {X Y : Type} (ε : ℝ) (F : PartialFn X Y) (d : ℕ) : Prop :=
  ∃ D : RandomProtocol X Y, DepthBound D d ∧
    (∀ x y,
      (0 ≤ acceptance D x y ∧ acceptance D x y ≤ ε) ∨
      (1 - ε ≤ acceptance D x y ∧ acceptance D x y ≤ 1)) ∧
    (∀ x y, F x y = some true → 1 - ε ≤ acceptance D x y) ∧
    (∀ x y, F x y = some false → acceptance D x y ≤ ε)

/-- The psP-type protocol of §1.1 has the standard error 1/3. -/
def PsPProtocol {X Y : Type} (F : PartialFn X Y) (d : ℕ) : Prop :=
  PsPProtocolErr (1 / 3) F d

end WatsonPseudodeterminism.MASeparation.Supplement


