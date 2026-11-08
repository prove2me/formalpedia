-- Prove2me | Definitions.Def_ValiantModel_ConceptSequence
-- name    : ValiantModel_ConceptSequence
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:33:49.244713+00:00
-- url     : https://prove2.me/theorems/d57d505f-2165-4791-8e79-11a7d6fdca89
-- title:
--   The domain $\{0,1\}^d$, hypotheses, supports and a sequence of concept classes $(H_1,H_2,\dots)$
-- statement:
--   The domain is the Boolean cube $\{0,1\}^d$. A **hypothesis** is a Boolean function $h:\{0,1\}^d\to\{0,1\}$, and its **support** is $\mathrm{supp}(h)=\{x: h(x)=1\}$. A **sequence of concept classes** $H=(H_1,H_2,\dots)$ assigns to each dimension $d$ a set $H_d$ of hypotheses on $\{0,1\}^d$.
--
--   Nothing else is assumed about $H_d$: it may be empty, and it may contain the all-zero function, which has empty support. Every object in this mission is built on these.
--
--   **Formalization Note** The cube is `Fin d → Bool`. The sequence is a function on all of `ℕ`, so a value at $d=0$ exists but is never constrained: every statement about the sequence quantifies $1\le d$.
-- source:
--   Hanneke, Mehrotra, Velegkas, Zampetakis, What is Learnable in Valiant's Theory of the Learnable?, arXiv:2605.13840 (version held, sha256 f793f255…), §1, p.1 (PDF p.3), footnote 1

import Mathlib

namespace ValiantModel

/-- The domain `{0,1}^d` of Hanneke, Mehrotra, Velegkas, Zampetakis, *What is Learnable in
Valiant's Theory of the Learnable?*, arXiv:2605.13840 (version held, sha256 f793f255…), §1, p.1
(PDF p.3). -/
abbrev Point (d : ℕ) : Type := Fin d → Bool

/-- A Boolean function `h : {0,1}^d → {0,1}` on the domain, ibid., p.1 (PDF p.3). -/
abbrev Hypothesis (d : ℕ) : Type := Point d → Bool

/-- The support `supp(h) = {x : h(x) = 1}`, ibid., footnote 1, p.1 (PDF p.3). -/
def supp {d : ℕ} (h : Hypothesis d) : Set (Point d) := {x | h x = true}

/-- A sequence of concept classes `H = (H₁, H₂, …)`, where `H d` is any set of Boolean functions
on `{0,1}^d`, ibid., p.1 (PDF p.3).

**Formalization Note.** The paper's sequence starts at `H₁`, while `ℕ` starts at `0`: the value
`H 0` is never constrained, and every statement about the sequence quantifies `1 ≤ d`. No other
condition is imposed: `H d` may be empty and may contain the all-zero function. -/
abbrev ConceptSequence : Type := (d : ℕ) → Set (Hypothesis d)

end ValiantModel


