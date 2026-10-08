-- Prove2me | Definitions.Def_MFOTLMon_Monitor_Automatic
-- name    : MFOTLMon_Monitor_Automatic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T03:34:50.995771+00:00
-- url     : https://prove2.me/theorems/e752a8d3-7703-4f83-92fd-4cdf0351905f
-- title:
--   Definition 3.1 and §3.1, p. 15:8 — convolution of words, regular relations, constant domain representation of ℕ, automatic temporal structures, the order predicate ≺
-- statement:
--   This file formalizes the automata-theoretic restrictions of §3.1.
--
--   Let $\Gamma$ be a finite alphabet and $\#\notin\Gamma$ a padding symbol. The **convolution** of words $w_1,\dots,w_k\in\Gamma^*$ is the word $w_1\otimes\cdots\otimes w_k\in((\Gamma\cup\{\#\})^k)^*$ of length $\ell=\max_i|w_i|$ whose $p$-th letter is the column $(w'_{1p},\dots,w'_{kp})$, where $w'_{ip}$ is the $p$-th letter of $w_i$ if $p\le|w_i|$ and $\#$ otherwise.
--
--   A **constant domain representation** of the domain $\mathbb N$ consists of a regular language $\mathcal L\subseteq\Gamma^*$ and a function $\nu:\mathcal L\to\mathbb N$ that is surjective, such that the equality language
--   $$
--   \mathcal L_\approx=\{u\otimes v\mid u,v\in\mathcal L,\ \nu(u)=\nu(v)\}
--   $$
--   is regular. Given such a representation, a relation $A\subseteq\mathbb N^k$ is **regular** (Definition 3.1(iii)) if
--   $$
--   \{u_1\otimes\cdots\otimes u_k\mid u_1,\dots,u_k\in\mathcal L,\ (\nu(u_1),\dots,\nu(u_k))\in A\}
--   $$
--   is a regular language over the alphabet $(\Gamma\cup\{\#\})^k$.
--
--   A temporal structure is **automatic** with respect to the representation if every relation $r^{\mathcal D_i}$ ($i\in\mathbb N$, $r\in R$) is regular (Definition 3.1(i), with one function $\nu$ for all $\mathcal D_i$ as §3.1 requires). It **has the order predicate** if some binary $\prec\in R$ is interpreted as the standard order $<$ on $\mathbb N$ at every time point.
--
--   These are the hypotheses on the input of the monitor; the representation is a fixed parameter, shared by the hypothesis on the input and the regularity claims about the output.
--
--   **Formalization Note.** The padding symbol is `none` in `Option Γ`, and a $k$-tuple of words is a function `Fin k → List Γ`. Regularity is Mathlib's `Language.IsRegular` (a finite-state DFA). $\nu$ is a total function on $\Gamma^*$ whose values off $\mathcal L$ are never used. The family of words $(w_c)_{c\in C}$ of Definition 3.1(ii) exists because $\nu$ is surjective, so it is not a field.
-- source:
--   Basin, Klaedtke, Müller, Zălinescu, Monitoring metric first-order temporal properties, J. ACM 62(2), Article 15 (2015), p. 15:8, convolution, Definition 3.1 and §3.1 (constant domain representation, |D̄| = ℕ, ≺ interpreted as <)

import Mathlib
import Definitions.Def_MFOTLMon_Monitor_Syntax

namespace MFOTLMon.Monitor

variable {S : Signature} {Γ : Type}

/-- The convolution `w₁ ⊗ ⋯ ⊗ w_k` (§3.1, p. 15:8): a word over `(Γ ∪ {#})^k` of length
`ℓ = max |wᵢ|`, whose `p`-th letter has `i`-th component the `p`-th letter of `wᵢ`, or the padding
symbol `#` (here `none`) if `wᵢ` is shorter. -/
def conv {k : ℕ} (ws : Fin k → List Γ) : List (Fin k → Option Γ) :=
  List.ofFn (n := Finset.univ.sup fun i => (ws i).length) fun p i => (ws i)[(p : ℕ)]?

/-- The language `{u₁ ⊗ ⋯ ⊗ u_k | u₁, …, u_k ∈ L with (ν(u₁), …, ν(u_k)) ∈ A}` of a relation
`A ⊆ ℕ^k` (tuples as lists) under a representation `ν : L → ℕ` (Definition 3.1, p. 15:8). -/
def relLang (L : Language Γ) (ν : List Γ → ℕ) (k : ℕ) (A : Set (List ℕ)) :
    Language (Fin k → Option Γ) :=
  ({w | ∃ ws : Fin k → List Γ, (∀ i, ws i ∈ L) ∧ List.ofFn (fun i => ν (ws i)) ∈ A ∧ conv ws = w} :
    Set (List (Fin k → Option Γ)))

/-- A constant domain representation of the domain `|D̄| = ℕ` (Definition 3.1(i) and §3.1, p. 15:8):
a regular language `L ⊆ Γ*` over the finite alphabet `Γ`, a function `ν : L → ℕ` that is surjective
onto `ℕ`, and the equality language `L≈ = {u ⊗ v | u, v ∈ L, ν(u) = ν(v)}` regular. -/
structure DomainRep (Γ : Type) [Fintype Γ] where
  L : Language Γ
  L_regular : L.IsRegular
  ν : List Γ → ℕ
  ν_surj : ∀ d : ℕ, ∃ w ∈ L, ν w = d
  eq_regular : (relLang L ν 2 {l | ∃ d : ℕ, l = [d, d]}).IsRegular

/-- A relation `A ⊆ ℕ^k` is regular w.r.t. the representation `rep` (Definition 3.1(iii), p. 15:8). -/
def RegularRel [Fintype Γ] (rep : DomainRep Γ) (k : ℕ) (A : Set (List ℕ)) : Prop :=
  (relLang rep.L rep.ν k A).IsRegular

/-- Every structure `Dᵢ` is automatic with the common representation `rep` of its domain (§3.1,
pp. 15:7–15:8, Definition 3.1(i)): every relation `r^{Dᵢ}` is regular. -/
def IsAutomatic [Fintype Γ] (rep : DomainRep Γ) (D : TempStruct S) : Prop :=
  ∀ i r, RegularRel rep (S.arity r) (D.rel i r)

/-- There is a binary predicate `≺ ∈ R` interpreted as the standard ordering `<` on `ℕ` at every
time point (§3.1, p. 15:8). -/
def HasOrderPred (D : TempStruct S) : Prop :=
  ∃ lt : S.R, S.arity lt = 2 ∧ ∀ i, D.rel i lt = {l | ∃ x y : ℕ, l = [x, y] ∧ x < y}

end MFOTLMon.Monitor


