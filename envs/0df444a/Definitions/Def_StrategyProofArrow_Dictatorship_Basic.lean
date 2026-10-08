-- Prove2me | Definitions.Def_StrategyProofArrow_Dictatorship_Basic
-- name    : StrategyProofArrow_Dictatorship_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:45:31.045827+00:00
-- url     : https://prove2.me/theorems/368f197d-021c-46e2-8fe9-030abc79673e
-- title:
--   Range, dictatorship (full and partial), Condition U, alternative-excluding procedures, agreement on the range, and sections of a strict voting procedure
-- statement:
--   This file fixes the vocabulary of §2–§3 of Satterthwaite's paper for **strict committees**, those in which every individual's preference and every ballot is a strong order (a linear order, no indifference). A committee has a finite set $I_n$ of $n$ individuals and a finite set $S_m$ of $m$ alternatives. A ballot set $B=(B_1,\dots,B_n)$ assigns each individual a strict ballot $B_i$; $x\,\bar B_i\,y$ means that $B_i$ ranks $x$ strictly above $y$. A **strict voting procedure** $v^{nm}$ maps each ballot set $B\in\rho^n_m$ to a single alternative $v^{nm}(B)\in S_m$.
--
--   1. **Range.** The range $T_p=\{v^{nm}(B): B\in\rho^n_m\}$, with $p=|T_p|$ elements.
--   2. **Top element of a set.** For a strict ballot $B_i$ and $T\subseteq S_m$, $x$ is the $B_i$-maximal element of $T$ when $x\in T$ and $x\,\bar B_i\,y$ for every $y\in T$, $y\neq x$. For a strong order this is the unique element of the paper's choice set $\Psi_T(B_i)$.
--   3. **Dictatorial.** $v^{nm}$ is dictatorial if some individual $i$ exists such that, for every $B\in\rho^n_m$, $v^{nm}(B)$ is the $B_i$-maximal element of the range $T_p$, i.e. $v^{nm}(B)=f^i_T(B)$. It is **fully dictatorial** if moreover $T_p=S_m$, and **partially dictatorial** if $T_p\subsetneq S_m$.
--   4. **Condition U.** For every $B\in\rho^n_m$ at which all individuals have the same $B_i$-maximal element $x$ of $T=T_p$, i.e. $\Psi_T(B_1)=\dots=\Psi_T(B_n)=\{x\}$, the procedure chooses $v^{nm}(B)=x$.
--   5. **Alternative-excluding.** $v^{nm}$ is **weak alternative-excluding** if some $x\in S_m$ satisfies $v^{nm}(B)\neq x$ for all $B\in\rho^n_m$ (equivalently $T_p\subsetneq S_m$), and **strong alternative-excluding** if it is weak alternative-excluding and satisfies Condition U.
--   6. **Agreement on a set.** Two strict ballots $C_i,D_i$ agree on $T$ when $x\,\bar C_i\,y\iff x\,\bar D_i\,y$ for all $x,y\in T$; this is the paper's $\theta_T(C_i)=\theta_T(D_i)$.
--   7. **Sections.** For a procedure $v^{n+1,3}$ of $n+1$ individuals and a strict ballot $b$, the section is the $n$-individual procedure $B\mapsto v^{n+1,3}(B,b)$ in which individual $n+1$ casts $b$ (display (6) of Lemma 3).
--
--   **Strategy-proofness** is not redefined here: it is `AGT.IncentiveCompatible` of the referenced definition `agt_social`, which states that no strict ballot set $B$, individual $i$ and strict ballot $B'_i$ satisfy $v^{nm}(B_1,\dots,B'_i,\dots,B_n)\,\bar B_i\,v^{nm}(B)$, the paper's definition (1) on $\rho^n_m$ (pp. 7–9).
--
--   These notions are the hypotheses and conclusions of Theorem 1 and of Lemmas 1–6.
--
--   **Formalization Note** A strict ballot is a relation `r : A → A → Prop` with `IsStrictTotalOrder A r` (the `AGT.IsPrefProfile` convention of `agt_social`); `r x y` is the paper's strict preference $x\,\bar B_i\,y$. A strong order and its strict part determine each other ($x\,B_i\,y \iff x=y \lor x\,\bar B_i\,y$), so this is the same object as $\rho_m$. A procedure is a total function on all relation profiles, but the range, dictatorship, Condition U and alternative exclusion quantify only over strict ballot sets, so values at other profiles play no role. The paper leaves the tie-breaking dictator function $f^i_T$ unspecified; for strong orders the $B_i$-maximal element of $T_p$ is unique, so "dictatorial" is stated directly as "the choice is $i$'s maximal element of $T_p$". The restriction $\theta_T$ is encoded as agreement on $T\times T$ rather than as an equality of orders on a $q$-element set. The $n+1$ individuals of Lemma 3 are `Option ι`, with `none` the individual $n+1$.
-- source:
--   Satterthwaite, Strategy-proofness and Arrow's Conditions, Northwestern Discussion Paper No. 122 (rev. Dec. 12, 1974), §2 pp. 6–9 (committee, range T_p, strategy-proofness (1), Restriction D, Ψ_W, θ_W), §3 p. 10 (dictatorial, fully/partially dictatorial), p. 13 (weak/strong alternative-excluding, Condition U), pp. 16–17 (display (6))

import Mathlib
import Definitions.Def_agt_social

namespace StrategyProofArrow.Dictatorship

open AGT

variable {ι A : Type*}

/-- The range `T_p` of a strict voting procedure (Satterthwaite, p. 6 and pp. 8–9): the set of
alternatives chosen at some strict ballot set. Ballot sets are profiles of strict total orders
(`AGT.IsPrefProfile`), the paper's `ρ^n_m`; values of `f` at other relation profiles are ignored. -/
def range (f : (ι → A → A → Prop) → A) : Set A :=
  {x | ∃ P : ι → A → A → Prop, IsPrefProfile P ∧ f P = x}

/-- `x` is the `r`-maximal element of `T` (`Ψ_T(r) = {x}` for a strong order `r`, p. 9):
`x ∈ T` and `r` ranks `x` strictly above every other element of `T`. Here `r a b` reads
"`a` strictly above `b`". -/
def IsTopIn (r : A → A → Prop) (T : Set A) (x : A) : Prop :=
  x ∈ T ∧ ∀ y ∈ T, y ≠ x → r x y

/-- A strict voting procedure is **dictatorial** (p. 10) if some individual `i` exists such that,
at every strict ballot set `P`, the chosen alternative is `i`'s most preferred element of the range
`T_p` (the paper's `v^{nm}(B) = f^i_T(B)`). -/
def Dictatorial (f : (ι → A → A → Prop) → A) : Prop :=
  ∃ i : ι, ∀ P : ι → A → A → Prop, IsPrefProfile P → IsTopIn (P i) (range f) (f P)

/-- **Fully dictatorial** (p. 10): dictatorial with range the whole alternative set,
`T_p ≡ S_m`. -/
def FullyDictatorial (f : (ι → A → A → Prop) → A) : Prop :=
  range f = Set.univ ∧ Dictatorial f

/-- **Partially dictatorial** (p. 10): dictatorial with range a proper subset of the alternative
set, `T_p ⊂⊂ S_m`. -/
def PartiallyDictatorial (f : (ι → A → A → Prop) → A) : Prop :=
  range f ≠ Set.univ ∧ Dictatorial f

/-- **Condition U** (p. 13): at every strict ballot set at which all individuals have the same
most preferred element `x` of the range `T = T_p`, the procedure chooses `x`. -/
def ConditionU (f : (ι → A → A → Prop) → A) : Prop :=
  ∀ P : ι → A → A → Prop, IsPrefProfile P →
    ∀ x : A, (∀ i, IsTopIn (P i) (range f) x) → f P = x

/-- **Weak alternative-excluding** (p. 13): some alternative is chosen at no strict ballot set. -/
def WeakAltExcluding (f : (ι → A → A → Prop) → A) : Prop :=
  ∃ x : A, ∀ P : ι → A → A → Prop, IsPrefProfile P → f P ≠ x

/-- **Strong alternative-excluding** (p. 13): weak alternative-excluding and Condition U. -/
def StrongAltExcluding (f : (ι → A → A → Prop) → A) : Prop :=
  WeakAltExcluding f ∧ ConditionU f

/-- `θ_T(r) = θ_T(s)` (p. 9): the two strict ballots order the elements of `T` alike. -/
def AgreeOn (T : Set A) (r s : A → A → Prop) : Prop :=
  ∀ x ∈ T, ∀ y ∈ T, (r x y ↔ s x y)

/-- The `n`-voter section of an `(n+1)`-voter procedure (display (6), pp. 16–17): voters are
`Option ι`, `none` is individual `n+1`, and the section for voter `n+1`'s ballot `b` is the
procedure `B ↦ v^{n+1}(B, b)` of the remaining voters. -/
def sectionAt (f : (Option ι → A → A → Prop) → A) (b : A → A → Prop) :
    (ι → A → A → Prop) → A :=
  fun Q => f (fun o => o.elim b Q)

end StrategyProofArrow.Dictatorship


