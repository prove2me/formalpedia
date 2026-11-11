-- Prove2me | Definitions.Def_QMAvsQCMAH_unionW
-- name    : QMAvsQCMAH_unionW
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:18:56.132344+00:00
-- url     : https://prove2.me/theorems/36226cc0-5419-4e47-a31c-7793f8564bfb
-- title:
--   The law of $F\cup\mathrm{supp}(B)$
-- statement:
--   For a random set $F\subseteq\mathcal X$ and an independent $B\leftarrow\mathrm{Bernoulli}(\beta)^{\mathcal X}$, this is the law of the random set $F\cup\mathrm{supp}(B)$, where $\mathrm{supp}(B)=\{u:B(u)=1\}$.
-- source:
--   Cakan, Classical Oracle Separation of QMA from the QCMA Hierarchy and Quantum Cryptography Even When P = QCMA, STOC 2027 submission (held version, sha256 336ce016…c897), Lemma 8, p.29

import Definitions.Def_QMAvsQCMAH_prob

set_option autoImplicit false

namespace QMAvsQCMAH

/-- The law of `F ∪ supp(B)` for a random set `F` (law `μ`) and an independent
`B ← Bernoulli(β)^X`, where `supp(B) = {u : B(u) = 1}`.

Cakan, *Classical Oracle Separation of QMA from the QCMA Hierarchy and Quantum Cryptography
Even When P = QCMA*, STOC 2027 submission (held version, sha256 336ce016…c897), Lemma 8, p.29 (PDF p.32): "If Bλ ← Bernoulli(β(λ))^{Xλ} is sampled independently of Fλ
and ρ(λ) + β(λ) → 0, the same statement holds for Fλ ∪ supp(Bλ)". -/
noncomputable def unionW {X : Type} [Fintype X] [DecidableEq X] (μ : Finset X → ℝ) (β : ℝ) :
    Finset X → ℝ :=
  fun S => ∑ F : Finset X, ∑ B : X → Bool,
    μ F * bernW β B * (if F ∪ Finset.univ.filter (fun u => B u = true) = S then 1 else 0)

end QMAvsQCMAH


