-- Prove2me | Definitions.Def_QMAvsQCMAH_prob
-- name    : QMAvsQCMAH_prob
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:14:40.362991+00:00
-- url     : https://prove2.me/theorems/b295edf8-a5f1-41f4-a507-0574fb17d901
-- title:
--   Finite probability distributions, events and Bernoulli weights
-- statement:
--   A **finite distribution** on a finite set $A$ is a weight function $\mu:A\to\mathbb R$ with $\mu(a)\ge0$ and $\sum_a\mu(a)=1$. The **probability** of an event $E\subseteq A$ is
--   $$\Pr_\mu[E]=\sum_{a\in E}\mu(a).$$
--   For $\beta\in[0,1]$, a $\mathrm{Bernoulli}(\beta)$ bit has weight $\beta$ at $1$ and $1-\beta$ at $0$, and a function $B:X\to\{0,1\}$ with independent $\mathrm{Bernoulli}(\beta)$ values has weight $\prod_{u\in X}\Pr[B(u)]$ (the law $\mathrm{Bernoulli}(\beta)^X$).
--
--   All random objects of the paper (oracles, hashes, random sets, shared tapes) live on finite sets, so every probability in this mission is such a finite sum.
-- source:
--   Cakan, Classical Oracle Separation of QMA from the QCMA Hierarchy and Quantum Cryptography Even When P = QCMA, STOC 2027 submission (held version, sha256 336ce016…c897), Section 3.1, p.18; Definition 21, p.35; Equation (37), p.40

import Mathlib

set_option autoImplicit false

namespace QMAvsQCMAH

open Classical

/-- A weight function `μ : α → ℝ` on a finite type is a **probability distribution** if its
weights are nonnegative and sum to `1`.

Cakan, *Classical Oracle Separation of QMA from the QCMA Hierarchy and Quantum Cryptography
Even When P = QCMA*, STOC 2027 submission (held version, sha256 336ce016…c897), Section 3.1, p.18 (PDF p.21); every random object of the paper (oracles, hashes, random
sets, shared tapes) lives on a finite set.

**Formalization Note.** Finite distributions are written as explicit weight functions, never as
integrals (paper.md decision 13). -/
def IsDist {α : Type} [Fintype α] (μ : α → ℝ) : Prop := (∀ a, 0 ≤ μ a) ∧ ∑ a, μ a = 1

/-- The **probability** `Pr_μ[E] = ∑_{a : E(a)} μ(a)` of an event `E` under a finite weight
function `μ`.

Cakan, *Classical Oracle Separation of QMA from the QCMA Hierarchy and Quantum Cryptography
Even When P = QCMA*, STOC 2027 submission (held version, sha256 336ce016…c897), Section 3.1, p.18 (PDF p.21).

**Formalization Note.** Events are arbitrary predicates (decided classically). -/
noncomputable def prob {α : Type} [Fintype α] (μ : α → ℝ) (E : α → Prop) : ℝ :=
  ∑ a, if E a then μ a else 0

/-- The weight `Pr[x] = β` if `x = 1` and `1 − β` if `x = 0` of a `Bernoulli(β)` bit. -/
noncomputable def bern (β : ℝ) (x : Bool) : ℝ := if x then β else 1 - β

/-- The weight `∏_{u} Pr_{Bernoulli(β)}[B(u)]` of a function `B : X → {0,1}` whose values are
independent `Bernoulli(β)` bits, i.e. the law `Bernoulli(β)^X`.

Cakan, *Classical Oracle Separation of QMA from the QCMA Hierarchy and Quantum Cryptography
Even When P = QCMA*, STOC 2027 submission (held version, sha256 336ce016…c897), Definition 21 (2), p.35 (PDF p.38), Equation (37), p.40 (PDF p.43):
"B(v, y) ←ind Bernoulli(2^{−⌈√λ⌉})". -/
noncomputable def bernW {X : Type} [Fintype X] (β : ℝ) (B : X → Bool) : ℝ := ∏ u, bern β (B u)

end QMAvsQCMAH


